#lang racket/base

;; optimization ideas:
;;
;; -- jay's idea
;;
;; -- when a list pattern has only a single repeat,
;;    don't search for matches, just count
;;
;; -- need to figure out something to do with patterns
;;    that have multiple ellipses in a sequence. Perhaps try
;;    to look for the fixed parts and then see if the others
;;    will fill in between them?
;;
;; -- when a match is unambiguous (and possibly only when
;;    there are no names underneath an ellipsis),
;;    pre-allocate the space to store the result (in a vector)
;;
;; -- change the way decomposition matching works to pass down
;;    the pattern to match at the hole and match it there, so
;;    that in situations like this: (in-hole E (+ n_1 n_2))
;;    we don't return all of the bogus matches that show up
;;    by treating the hole as 'any'. 
;;
;;    (this one turns out not to be so great because it
;;     makes caching less effective)
;;
;; -- combine the left-hand sides of a reduction relation
;;    so to avoid re-doing decompositions over and over
;;    (maybe....)
;;
;; -- parallelism? but what about the hash-table cache?
;; 
#|

Note: the patterns described in the documentation are
slightly different than the patterns processed here.
See match-a-pattern.rkt for more details

|#
(require racket/list
         racket/match
         racket/contract
         racket/promise
         racket/set
         data/union-find
         racket/performance-hint
         (for-syntax racket/base)
         "build-nt-property.rkt"
         "underscore-allowed.rkt"
         "match-a-pattern.rkt"
         "lang-struct.rkt"
         "enum.rkt"
         "binding-forms.rkt"
         "ambiguous.rkt"
         (only-in "binding-forms-definitions.rkt" bspec?))

(define-struct compiled-pattern (cp binds-names? skip-dup-check? lang-α-equal?) #:transparent)

(define caching-enabled? (make-parameter #t))

;; var = (make-var sym sexp)
;; patterns are sexps with `var's embedded
;; in them. It means to match the
;; embedded sexp and return that binding



;; repeat = (make-repeat compiled-pattern (listof rib) (or/c #f symbol?) (or/c #f symbol?))
(define-struct repeat (pat empty-bindings name mismatch) #:transparent)

(define none
  (let ()
    (define-struct none ())
    (make-none)))
(define (none? x) (eq? x none))

;; lookup-binding : bindings (union sym (cons sym sym)) [(-> any)] -> any
(begin-encourage-inline
  (define (lookup-binding bindings
                          sym
                          [fail (lambda () 
                                  (error 'lookup-binding "didn't find ~e in ~e" sym bindings))])
    (let loop ([ribs (bindings-table bindings)])
      (cond
        [(null? ribs) (fail)]
        [else
         (let ([rib (car ribs)])
           (if (and (bind? rib) (eq? (bind-name rib) sym))
               (bind-exp rib)
               (loop (cdr ribs))))]))))

;; compile-language : language-pict-info[see pict.rkt] (listof nt) (listof (uf-set/c symbol?)) 
;; (listof (list rewritten-pattern bspec)) -> compiled-lang
(define (compile-language pict-info lang nt-map binding-info)
  (let* ([clang-ht (make-hasheq)]
         [clang-list-ht (make-hasheq)]
         [across-ht (make-hasheq)]
         [across-list-ht (make-hasheq)]
         [has-hole-or-hide-hole-ht (build-has-hole-or-hide-hole-ht lang)]
         [cache (make-hash)]
         [binding-forms-absent-cache (make-hash)]
         [bind-names-cache (make-hash)]
         [literals (extract-literals lang)]
         [collapsible-nts (extract-collapsible-nts lang)]
         [clang (make-compiled-lang lang #f clang-ht clang-list-ht 
                                    across-ht across-list-ht
                                    has-hole-or-hide-hole-ht 
                                    cache binding-forms-absent-cache bind-names-cache
                                    pict-info
                                    literals
                                    nt-map
                                    collapsible-nts
                                    'uninitialized-ambiguity-info
                                    `() ;; internal patterns don't need freshening
                                    #f)]
         [binders (map (match-lambda
                        [`(,rewritten-pattern ,bspec) 
                         `(,(compile-pattern clang rewritten-pattern #t) ,bspec)])
                       binding-info)]
         [non-list-nt-table (build-non-list-nt-label lang)]
         [list-nt-table (build-list-nt-label lang)]
         [do-compilation
          (lambda (ht list-ht lang)
            (for ([nt (in-list lang)])
              (for ([rhs (in-list (nt-rhs nt))])
                (define-values (compiled-pattern-proc has-hole? has-hide-hole? names) 
                  (compile-pattern/cross? clang (rhs-pattern rhs) #f))
                (define (add-to-ht ht) 
                  (define nv (cons
                              (build-compiled-pattern compiled-pattern-proc names equal?)
                              (hash-ref ht (nt-name nt))))
                  (hash-set! ht (nt-name nt) nv))
                (define may-be-non-list? (may-be-non-list-pattern? (rhs-pattern rhs) non-list-nt-table))
                (define may-be-list? (may-be-list-pattern? (rhs-pattern rhs) list-nt-table))
                (when may-be-non-list? (add-to-ht ht))
                (when may-be-list? (add-to-ht list-ht))
                (unless (or may-be-non-list? may-be-list?)
                  (error 'compile-language 
                         "internal error: unable to determine whether pattern matches lists, non-lists, or both: ~s"
                         (rhs-pattern rhs))))))]
         
         [init-ht
          (lambda (ht)
            (for-each (lambda (nt) (hash-set! ht (nt-name nt) null))
                      lang))])
    
    (init-ht clang-ht)
    (init-ht clang-list-ht)
    
    (hash-for-each
     clang-ht
     (lambda (nt rhs)
       (when (has-underscore? nt)
         (error 'compile-language "cannot use underscore in nonterminal name, ~s" nt))))
    
    (define compatible-context-language
      (delay
        (let ([compatible-context-language
               (build-compatible-context-language clang-ht lang)])
          (for-each (lambda (nt)
                      (hash-set! across-ht (nt-name nt) null)
                      (hash-set! across-list-ht (nt-name nt) null))
                    compatible-context-language)
          (do-compilation across-ht across-list-ht compatible-context-language)
          compatible-context-language)))
    (do-compilation clang-ht clang-list-ht lang)
    (define the-ambiguity-cache (build-ambiguity-cache clang))
    (define enumerators
      (lang-enumerators lang compatible-context-language))

    (struct-copy compiled-lang clang [delayed-cclang compatible-context-language]
                                     [enum-table enumerators]
                                     [ambiguity-cache the-ambiguity-cache]
                                     [binding-table binders])))

;; mk-uf-sets : (listof (listof sym)) -> (hash[symbol -o> uf-set?])
;; in the result hash, each nt maps to a uf-set that represents
;; the set of non-terminals that are coming from the same group
(define (mk-uf-sets args)
  (for/fold ([iht (hash)]) ([same-nts (in-list args)])
    (define main-name (car same-nts))
    (define main (uf-new main-name))
    (for/fold ([iht (hash-set iht main-name main)]) 
      ([other (in-list (cdr same-nts))])
      (define next (uf-new other))
      (uf-union! main next)
      (hash-set iht other next))))

;; extract-collapsible-nts : (listof nt) -> (listof any)
(define (extract-collapsible-nts nts)
  (define nt-hash (for/hasheq ([nt nts]) 
                    (values (nt-name nt) (nt-rhs nt))))
  (for/fold ([c-nts (hasheq)])
    ([nt (in-hash-keys nt-hash)])
    (let loop ([rhss (hash-ref nt-hash nt)])
      (if (= (length rhss) 1)
          (match (rhs-pattern (car rhss))
            [`(nt ,next)
             (loop (hash-ref nt-hash next))]
            [else
             (hash-set c-nts nt (rhs-pattern (car rhss)))])
          c-nts))))


;; extract-literals : (listof nt) -> (listof symbol)
(define (extract-literals nts)
  (let ([literals-ht (make-hasheq)]
        [nt-names (map nt-name nts)])
    (for-each (λ (nt) 
                (for-each (λ (rhs) (extract-literals/pat nt-names (rhs-pattern rhs) literals-ht))
                          (nt-rhs nt)))
              nts)
    (hash-map literals-ht (λ (x y) x))))

;; extract-literals/pat : (listof sym) pattern ht -> void
;; inserts the literals mentioned in pat into ht
(define (extract-literals/pat nts pat ht)
  (let loop ([pat pat])
    (match-a-pattern pat
      [`any (void)]
      [`number (void)]
      [`string (void)]
      [`natural (void)]
      [`integer (void)]
      [`real (void)]
      [`boolean (void)]
      [`variable (void)]
      [`(variable-except ,s ...) (void)]
      [`(variable-prefix ,s) (void)]
      [`variable-not-otherwise-mentioned (void)]
      [`hole (void)]
      [`(nt ,id) (void)]
      [`(name ,name ,pat) (loop pat)]
      [`(mismatch-name ,name ,pat) (loop pat)]
      [`(in-hole ,p1 ,p2) 
       (loop p1)
       (loop p2)]
      [`(hide-hole ,p) (loop p)]
      [`(side-condition ,p ,g ,e)
       (loop p)]
      [`(cross ,s) (void)]
      [`(list ,sub-pats ...)
       (for ([sub-pat (in-list sub-pats)])
         (match sub-pat
           [`(repeat ,pat ,name ,mismatch)
            (loop pat)]
           [else
            (loop sub-pat)]))]
      [(? (compose not pair?)) 
       (when (symbol? pat)
         (unless (regexp-match #rx"_" (symbol->string pat))
           (unless (regexp-match #rx"^\\.\\.\\." (symbol->string pat))
             (unless (memq pat nts)
               (hash-set! ht pat #t)))))])))

;; prefix-nts : string pat -> pat
(define (prefix-nts prefix pat)
  (let loop ([pat pat])
    (match-a-pattern pat
      [`any pat]
      [`number pat]
      [`string pat]
      [`natural pat]
      [`integer pat]
      [`real pat]
      [`boolean pat]
      [`variable pat]
      [`(variable-except ,s ...) pat]
      [`(variable-prefix ,s) pat]
      [`variable-not-otherwise-mentioned pat]
      [`hole pat]
      [`(nt ,id) `(nt ,(string->symbol (string-append prefix (symbol->string id))))]
      [`(name ,name ,pat) `(name , name ,(loop pat))]
      [`(mismatch-name ,name ,pat) `(mismatch-name ,name ,(loop pat))]
      [`(in-hole ,p1 ,p2) `(in-hole ,(loop p1) ,(loop p2))]
      [`(hide-hole ,p) `(hide-hole ,(loop p))]
      [`(side-condition ,p ,g ,e) `(side-condition ,(loop p) ,g ,e)]
      [`(cross ,s) pat]
      [`(list ,sub-pats ...)
       `(list ,@(for/list ([sub-pat (in-list sub-pats)])
                  (match sub-pat
                    [`(repeat ,pat ,name ,mismatch)
                     `(repeat ,(loop pat) ,name ,mismatch)]
                    [else
                     (loop sub-pat)])))]
      [(? (compose not pair?)) 
       pat])))

; build-has-hole-or-hide-hole-ht : (listof nt) -> hash[symbol -o> boolean]
; produces a map of nonterminal -> whether that nonterminal could produce a hole
(define (build-has-hole-or-hide-hole-ht lang)
  (build-nt-property 
   lang
   (lambda (pattern ht)
     (let loop ([pattern pattern])
       (match-a-pattern pattern
         [`any #f]
         [`number #f]
         [`string #f]
         [`natural #f]
         [`integer #f]
         [`real #f]
         [`boolean #f]
         [`variable #f] 
         [`(variable-except ,vars ...) #f]
         [`(variable-prefix ,var) #f]
         [`variable-not-otherwise-mentioned #f]
         [`hole #t]
         [`(nt ,id) (hash-ref ht id)]
         [`(name ,name ,pat) (loop pat)]
         [`(mismatch-name ,name ,pat) (loop pat)]
         [`(in-hole ,context ,contractum) (loop contractum)]
         [`(hide-hole ,arg) #t]
         [`(side-condition ,pat ,condition ,expr) (loop pat)]
         [`(cross ,nt) #f]
         [`(list ,pats ...)
          (for/or ([pat (in-list pats)])
            (match pat
              [`(repeat ,pat ,name ,mismatch?) (loop pat)]
              [_ (loop pat)]))]
         [(? (compose not pair?)) #f])))
   #f
   (λ (x y) (or x y))))

;; build-compatible-context-language : lang -> lang
(define (build-compatible-context-language clang-ht lang)
  (remove-empty-compatible-contexts
   (apply
    append
    (map 
     (lambda (nt1)
       (map
        (lambda (nt2)
          (let ([compat-nt (build-compatible-contexts/nt clang-ht (nt-name nt1) nt2)])
            (if (eq? (nt-name nt1) (nt-name nt2))
                (make-nt (nt-name compat-nt)
                         (cons
                          (make-rhs 'hole)
                          (nt-rhs compat-nt)))
                compat-nt)))
        lang))
     lang))))

;; remove-empty-compatible-contexts : lang -> lang
;; Removes the empty compatible context non-terminals and the 
;; rhss that reference them.
(define (remove-empty-compatible-contexts lang)
  (define (has-cross? pattern crosses)
    (match pattern
      [`(cross ,(? symbol? nt)) (memq nt crosses)]
      [(list-rest p '... rest) (has-cross? rest crosses)]
      [(cons first rest) (or (has-cross? first crosses)
                             (has-cross? rest crosses))]
      [_ #f]))
  (define (delete-empty nts)
    (for/fold ([deleted null] [kept null]) ([nt nts])
      (if (null? (nt-rhs nt))
          (values (cons nt deleted) kept)
          (values deleted (cons nt kept)))))
  (define (delete-references deleted-names remaining-nts)
    (map (λ (nt) 
           (make-nt (nt-name nt)
                    (filter (λ (rhs) (not (has-cross? (rhs-pattern rhs) deleted-names))) 
                            (nt-rhs nt))))
         remaining-nts))
  
  (let loop ([nts lang])
    (let-values ([(deleted kept) (delete-empty nts)])
      (if (null? deleted)
          kept
          (loop (delete-references (map nt-name deleted) kept))))))

;; build-compatible-contexts : clang-ht prefix nt -> nt
;; constructs the compatible closure evaluation context from nt.
(define (build-compatible-contexts/nt clang-ht prefix nt)
  (make-nt
   (symbol-append prefix '- (nt-name nt))
   (apply append
          (map
           (lambda (rhs)
             (let-values ([(maker count) (build-compatible-context-maker clang-ht
                                                                         (rhs-pattern rhs)
                                                                         prefix)])
               (let loop ([i count])
                 (cond
                   [(zero? i) null]
                   [else (let ([nts (build-across-nts (nt-name nt) count (- i 1))])
                           (cons (make-rhs (maker (box nts)))
                                 (loop (- i 1))))]))))
           (nt-rhs nt)))))

(define (symbol-append . args)
  (string->symbol (apply string-append (map symbol->string args))))

;; build-across-nts : symbol number number -> (listof pattern)
(define (build-across-nts nt count i)
  (let loop ([j count])
    (cond
      [(zero? j) null]
      [else
       (cons (= i (- j 1)) 
             (loop (- j 1)))])))

;; build-compatible-context-maker : symbol pattern -> (values ((box (listof pattern)) -> pattern) number)
;; when the result function is applied, it takes each element
;; of the of the boxed list and plugs them into the places where
;; the nt corresponding from this rhs appeared in the original pattern. 
;; The number result is the number of times that the nt appeared in the pattern.
(define (build-compatible-context-maker clang-ht pattern prefix)
  (let ([count 0])
    (define maker
     (let loop ([pattern pattern])
       (define (untouched-pattern _) 
         (values pattern #f))
       (match-a-pattern pattern
         [`any untouched-pattern]
         [`number untouched-pattern]
         [`string untouched-pattern]
         [`natural untouched-pattern]
         [`integer untouched-pattern]
         [`real untouched-pattern]
         [`boolean untouched-pattern]
         [`variable untouched-pattern] 
         [`(variable-except ,vars ...) untouched-pattern]
         [`(variable-prefix ,var) untouched-pattern]
         [`variable-not-otherwise-mentioned untouched-pattern]
         [`hole untouched-pattern]
         [`(nt ,name)
          (cond
            [(hash-ref clang-ht name #f)
             (set! count (+ count 1))
             (lambda (l)
               (let ([fst (car (unbox l))])
                 (set-box! l (cdr (unbox l)))
                 (if fst
                     (values `(cross ,(symbol-append prefix '- name)) #t)
                     (values pattern #f))))]
            [else untouched-pattern])]
         [`(name ,name ,pat)
          (let ([patf (loop pat)])
            (lambda (l)
              (let-values ([(p h?) (patf l)])
                (values `(name ,name ,p) h?))))]
         [`(mismatch-name ,name ,pat)
          (let ([patf (loop pat)])
            (lambda (l)
              (let-values ([(p h?) (patf l)])
                (values `(mismatch-name ,name ,p) h?))))]
         [`(in-hole ,context ,contractum)
          (let ([match-context (loop context)]
                [match-contractum (loop contractum)])
            (lambda (l)
              (let-values ([(ctxt _) (match-context l)]
                           [(ctct h?) (match-contractum l)])
                (values `(in-hole ,ctxt ,ctct) h?))))]
         [`(hide-hole ,p)
          (let ([m (loop p)])
            (lambda (l)
              (let-values ([(p h?) (m l)])
                (if h?
                    (values p #t)
                    (values `(hide-hole ,p) #f)))))]
         [`(side-condition ,pat ,condition ,expr)
          (let ([patf (loop pat)])
            (lambda (l)
              (let-values ([(p h?) (patf l)])
                (values `(side-condition ,p ,condition ,expr) h?))))]
         [`(cross ,arg) untouched-pattern]
         [`(list ,pats ...)
          (define pre-cross
            (for/list ([sub-pat (in-list pats)])
              (match sub-pat
                [`(repeat ,pat ,name ,mismatch)
                 (list (loop pat) sub-pat)]
                [else
                 (list (loop sub-pat) #f)])))
          (λ (l)
            (define any-cross? #f)
            (define post-cross
              (map (match-lambda 
                     [(list f r?)
                      (let-values ([(p h?) (f l)])
                        (set! any-cross? (or any-cross? h?))
                        (list p h? r?))])
                   pre-cross))
            (define (hide p)
              (if any-cross?
                  (match p
                    [`(repeat ,p ,name ,mismatch?)
                     `(repeat (hide-hole ,p) ,name ,mismatch?)]
                    [_ 
                     `(hide-hole ,p)])
                  p))
            (values
             `(list ,@(foldr (λ (post tail)
                               (match post
                                 [(list p* #t (and (not #f) p))
                                  `(,(hide p) ,p* ,(hide p) . ,tail)]
                                 [(list p #f (not #f))
                                  `((repeat ,(hide p) #f #f) . ,tail)]
                                 [(list p* #t #f)
                                  `(,p* . ,tail)]
                                 [(list p #f #f)
                                  `(,(hide p) . ,tail)]))
                             '()
                             post-cross))
             any-cross?))]
         [(? (compose not pair?)) untouched-pattern])))
    (values (λ (l) (let-values ([(p _) (maker l)]) p))
            count)))

;; build-list-nt-label : lang -> hash[symbol -o> boolean]
(define (build-list-nt-label lang)
  (build-nt-property lang
                     may-be-list-pattern?
                     #f
                     (λ (x y) (or x y))))

(define (may-be-list-pattern? pattern nt-table)
  (let loop ([pattern pattern])
    (match-a-pattern pattern
      [`any #t]
      [`number #f]
      [`string #f]
      [`natural #f]
      [`integer #f]
      [`real #f]
      [`boolean #f]
      [`variable #f]
      [`(variable-except ,vars ...) #f]
      [`(variable-prefix ,var) #f]
      [`variable-not-otherwise-mentioned #f]
      [`hole #t]
      [`(nt ,id) (hash-ref nt-table id)]
      [`(name ,id ,pat) (loop pat)]
      [`(mismatch-name ,id ,pat) (loop pat)]
      [`(in-hole ,context ,contractum) 
       ;; pessimistic, assumes that context can be 'hole' directly
       (or (loop context) (loop contractum))]
      [`(hide-hole ,p) (loop p)]
      [`(side-condition ,pat ,condition ,expr) (loop pat)]
      [`(cross ,nt) #t]
      [`(list ,pats ...) #t]
      [(? (compose not pair?)) #f])))


;; build-non-list-nt-label : lang -> hash[symbol -o> boolean]
(define (build-non-list-nt-label lang)
  (build-nt-property lang
                     may-be-non-list-pattern?
                     #f
                     (λ (x y) (or x y))))

(define (may-be-non-list-pattern? pattern ht)
  (let loop ([pattern pattern])
    (match-a-pattern pattern
      [`any #t]
      [`number #t]
      [`string #t]
      [`natural #t]
      [`integer #t]
      [`real #t]
      [`boolean #t]
      [`variable #t]
      [`(variable-except ,vars ...) #t]
      [`(variable-prefix ,prefix) #t]
      [`variable-not-otherwise-mentioned #t]
      [`hole #t]
      [`(nt ,nt) (hash-ref ht nt)]
      [`(name ,name ,pat) (loop pat)]
      [`(mismatch-name ,name ,pat) (loop pat)]
      [`(in-hole ,context ,contractum) 
       ;; pessimistic, assumes that context can be 'hole' directly
       (or (loop context) (loop contractum))]
      [`(hide-hole ,p) (loop p)]
      [`(side-condition ,pat ,condition ,expr) (loop pat)]
      [`(cross ,nt) #t]
      [`(list ,pats ...) #f]
      [(? (compose not pair?)) #t])))

;; match-pattern? : compiled-pattern exp -> boolean
(define (match-pattern? compiled-pattern exp)
  (and (match-pattern compiled-pattern exp) #t))

;; match-pattern : compiled-pattern exp -> (union #f (listof bindings))
(define (match-pattern compiled-pattern exp)
  (let ([results ((compiled-pattern-cp compiled-pattern) exp #f 0)])
    (if (compiled-pattern-skip-dup-check? compiled-pattern)
        results
        (and results
             (let ([filtered (filter-multiples results (compiled-pattern-lang-α-equal?
                                                        compiled-pattern))])
               (and (not (null? filtered))
                    filtered))))))

;; filter-multiples : (listof mtch) (exp exp -> boolean) -> (listof mtch)
(define (filter-multiples matches lang-α-equal?)
  ;(printf "matches ~s\n" matches)
  (let loop ([matches matches]
             [acc null])
    (cond
      [(null? matches) 
       ;; this reverse here is to get things back
       ;; in the same order that they'd be in if the
       ;; skip-dup-check? bolean had been true
       (reverse acc)]
      [else
       (let ([merged (merge-multiples/remove (car matches) lang-α-equal?)])
         (if merged
             (loop (cdr matches) (cons merged acc))
             (loop (cdr matches) acc)))])))

;; merge-multiples/remove : bindings (exp exp -> boolean) -> (union #f bindings)
;; returns #f if all duplicate bindings don't bind the same thing
;; returns a new bindings 
(define (merge-multiples/remove match lang-α-equal?)
  (let/ec fail
    (let (
          ;; match-ht : sym -o> sexp
          [match-ht (make-hash)]
          
          ;; mismatch-ht : sym -o> hash[sexp -o> #t]
          [mismatch-ht (make-hash)]
          
          [ribs (bindings-table (mtch-bindings match))])
      (for ([rib (in-list ribs)])
        (cond
          [(bind? rib)
           (let ([name (bind-name rib)]
                 [exp (bind-exp rib)])
             (let ([previous-exp (hash-ref match-ht name uniq)])
               (cond
                 [(eq? previous-exp uniq)
                  (hash-set! match-ht name exp)]
                 [else
                  (unless (lang-α-equal? exp previous-exp)
                    (fail #f))])))]
          [(mismatch-bind? rib)
           (match-define (mismatch-bind name exp nesting-depth) rib)
           (define priors (hash-ref mismatch-ht name uniq))
           (when (eq? priors uniq)
             (define table (make-hash))
             (hash-set! mismatch-ht name table)
             (set! priors table))
           (cond
             [(equal? nesting-depth 'unknown-mismatch-depth)
              (unless (null? exp)
                (error 'matcher.rkt 
                       (string-append "invariant broken; unknown-mismatch-depth should"
                                      " appear only when the expression is an empty list: ~s")
                       exp))]
             [else
              (let loop ([depth nesting-depth]
                         [exp exp])
                (cond
                  [(= depth 0)
                   (when (hash-ref priors exp #f)
                     (fail #f))
                   (hash-set! priors exp #t)]
                  [else
                   (for ([exp-ele (in-list exp)])
                     (loop (- depth 1) exp-ele))]))])]))
      (make-mtch
       (make-bindings (hash-map match-ht make-bind))
       (mtch-context match)
       (mtch-hole match)))))

;; compile-pattern : compiled-lang pattern boolean -> compiled-pattern
(define (compile-pattern clang pattern bind-names?)
  (let-values ([(pattern has-hole? has-hide-hole? names) 
                (compile-pattern/cross? clang pattern bind-names?)])
    (build-compiled-pattern 
     (if (or has-hole? has-hide-hole? (not (null? names)))
         pattern
         (convert-matcher pattern))
     names
     (if (empty? (compiled-lang-binding-table clang))
         equal?
         (λ (lhs rhs) (α-equal? (compiled-lang-binding-table clang) match-pattern lhs rhs))))))

(define (build-compiled-pattern proc names lang-α-equal?)
  (make-compiled-pattern 
   proc
   (null? names)
                         
   ;; none of the names are duplicated
   (and (equal? names (remove-duplicates names))
        
        ;; no mismatch names
        (not (for/or ([name (in-list names)])
                     (pair? name))))
   lang-α-equal?))

(define (pattern-might-destructure? pattern)
  (match-a-pattern pattern
    [`any #f]
    [`number #f]
    [`string #f]
    [`natural #f]
    [`integer #f]
    [`real #f]
    [`boolean #f]
    [`variable #f]
    [`(variable-except ,var ...) #f]
    [`(variable-prefix ,var) #f]
    [`variable-not-otherwise-mentioned #f]
    [`hole #f]
    [`(nt ,var) #f]
    [`(name ,var ,pat) (pattern-might-destructure? pat)]
    [`(mismatch-name ,var ,pat) (pattern-might-destructure? pat)]
    [`(in-hole ,pat1 ,pat2) ;; not that there's much chance that `pat1` isn't a list
     (or (pattern-might-destructure? pat1) (pattern-might-destructure? pat2))]
    [`(hide-hole ,pat) (pattern-might-destructure? pat)]
    [`(side-condition ,pat ,_ ,_) (pattern-might-destructure? pat)]
    [`(cross ,_) #t] ;; check with Robby about this
    [`(list ,lpat ...) #t]
    [(? (compose not pair?)) #f]))

;; compile-pattern/cross? : compiled-lang pattern boolean -> (values compiled-pattern boolean)
(define (compile-pattern/cross? clang pattern bind-names?)
  (define clang-ht (compiled-lang-ht clang))
  (define clang-list-ht (compiled-lang-list-ht clang))
  (define has-hole-or-hide-hole-ht (compiled-lang-has-hole-or-hide-hole-ht clang))
  (define binding-forms (compiled-lang-binding-table clang))

  (define lang-α-equal? 
    (λ (lhs rhs) (α-equal? (compiled-lang-binding-table clang) match-pattern lhs rhs)))

  ;; Note that `bind-names?` means that identical names must match identical values, and 
  ;; binding forms specify alpha-equivalence behavior in the user-defined language.
  ;; Other than the fact that `bind-names?` being false supresses freshening (and thus allows
  ;; us to ignore the binding forms), they have nothing to do with each other!


  (define (compile-pattern/default-cache pattern)
    (compile-pattern/cache pattern 
                           (if bind-names?
                               (if (empty? binding-forms) 
                                   (compiled-lang-binding-forms-absent-cache clang)
                                   (compiled-lang-bind-names-cache clang))
                               (compiled-lang-cache clang))))
  
  (define in-name-parameter (make-parameter #f))
  
  (define (compile-pattern/cache pattern compiled-pattern-cache)
    (let ([compiled-cache (hash-ref compiled-pattern-cache pattern uniq)])
      (cond 
        [(eq? compiled-cache uniq)
         (define-values (compiled-pattern-without-freshening has-hole? has-hide-hole? names) 
           (true-compile-pattern pattern))

         ;; If necessary, freshen the value before matching it
         (define compiled-pattern
           (cond
            [(or (not bind-names?) 
                 (not (pattern-might-destructure? pattern))
                 (empty? (compiled-lang-binding-table clang)))
             compiled-pattern-without-freshening]
            [(equal? (procedure-arity compiled-pattern-without-freshening) 3)
             (lambda (exp hole-info nesting-depth)
                     (compiled-pattern-without-freshening
                      (freshen (compiled-lang-binding-table clang) match-pattern exp)
                      hole-info nesting-depth))]
            ;; only returns a boolean, no need to freshen
            [else compiled-pattern-without-freshening]))
         
         
         (unless (equal? (if (or has-hole? has-hide-hole? (not (null? names)))
                             3
                             1)
                         (procedure-arity compiled-pattern))
           (error 'compile-pattern "got procedure with wrong arity; pattern ~s ~s ~s ~s ~s\n"
                  pattern compiled-pattern has-hole? has-hide-hole? names))
         (define val (list (match pattern
                             [`(nt ,p)
                              (memoize compiled-pattern has-hole?)]
                             [_ compiled-pattern])
                           has-hole?
                           has-hide-hole?
                           names))
         (hash-set! compiled-pattern-cache pattern val)
         (apply values val)]
        [else
         (apply values compiled-cache)])))
  
  ;; invariant : if both result booleans are #f (ie, no-hole and no names), then
  ;;             the result (matching) function returns a boolean and has arity 1. 
  ;;             otherwise it is a compiled-pattern function (ie returning a list
  ;;             of assoc tables)
  (define (true-compile-pattern pattern)
    (match-a-pattern pattern
      [`any (simple-match (λ (x) #t))]
      [`number (simple-match number?)]
      [`string (simple-match string?)]
      [`natural (simple-match exact-nonnegative-integer?)]
      [`integer (simple-match exact-integer?)]
      [`real (simple-match real?)]
      [`boolean (simple-match boolean?)]
      [`variable (simple-match symbol?)]
      [`(variable-except ,vars ...)
       (simple-match
        (λ (exp)
          (and (symbol? exp)
               (not (memq exp vars)))))]
      [`(variable-prefix ,var)
       (define prefix-str (symbol->string var))
       (define prefix-len (string-length prefix-str))
       (simple-match
        (λ (exp)
          (and (symbol? exp)
               (let ([str (symbol->string exp)])
                 (and ((string-length str) . >= . prefix-len)
                      (string=? (substring str 0 prefix-len) prefix-str))))))]
      [`variable-not-otherwise-mentioned
       (let ([literals (compiled-lang-literals clang)])
         (simple-match
          (λ (exp)
            (and (symbol? exp) 
                 (not (memq exp literals))))))]
      [`hole
       (values match-hole #t #f '())]
      [`(nt ,nt)
       (define in-name? (in-name-parameter))
       (define has-hole? (hash-ref has-hole-or-hide-hole-ht nt))
       (values
        (if has-hole?
            (λ (exp hole-info nesting-depth)
              (match-nt (hash-ref clang-list-ht nt)
                        (hash-ref clang-ht nt)
                        nt exp hole-info
                        lang-α-equal?))
            (λ (exp)
              (match-nt/boolean
               (hash-ref clang-list-ht nt)
               (hash-ref clang-ht nt)
               nt exp
               lang-α-equal?)))
        has-hole?
        #f
        '())]
      [`(name ,name ,pat)
       (define-values (match-pat has-hole? has-hide-hole? names) 
         (parameterize ([in-name-parameter #t])
           (compile-pattern/default-cache pat)))
       (values (match-named-pat name (if (or has-hide-hole? has-hole? (not (null? names)))
                                         match-pat
                                         (convert-matcher match-pat))
                                #f)
               has-hole?
               has-hide-hole?
               (cons name names))]
      [`(mismatch-name ,name ,pat)
       (define-values (match-pat has-hole? has-hide-hole? names) (compile-pattern/default-cache pat))
       (values (match-named-pat name (if (or has-hide-hole? has-hole? (not (null? names)))
                                         match-pat
                                         (convert-matcher match-pat))
                                #t)
               has-hole?
               has-hide-hole?
               (cons `(mismatch-name name) names))]
      [`(in-hole ,context ,contractum) 
       (define-values (match-context ctxt-has-hole? ctxt-has-hide-hole? ctxt-names)
         (compile-pattern/default-cache context))
       (define-values (match-contractum contractum-has-hole? contractum-has-hide-hole? contractum-names)
         (compile-pattern/default-cache contractum))
       (unless ctxt-has-hole?
         (error 'compile-pattern
                "found an in-hole pattern whose context position has no hole ~s"
                pattern))
       (values
        (if (or ctxt-has-hide-hole?
                contractum-has-hole?
                contractum-has-hide-hole?
                (not (null? ctxt-names))
                (not (null? contractum-names)))
            (match-in-hole context
                           contractum
                           exp
                           match-context
                           (if (or contractum-has-hole? contractum-has-hide-hole? (not (null? contractum-names)))
                               match-contractum
                               (convert-matcher match-contractum)))
            (match-in-hole/contractum-boolean context
                                              contractum
                                              exp
                                              match-context
                                              match-contractum))
        contractum-has-hole?
        (or ctxt-has-hide-hole? contractum-has-hide-hole?)
        (append ctxt-names contractum-names))]
      [`(hide-hole ,p)
       (define-values (match-pat has-hole? has-hide-hole? names) (compile-pattern/default-cache p))
       (values
        (cond
          [(or has-hole? has-hide-hole? (not (null? names)))
           (lambda (exp hole-info nesting-depth)
             (let ([matches (match-pat exp #f nesting-depth)])
               (and matches
                    (map (λ (match) (make-mtch (mtch-bindings match) 
                                               (hole->not-hole (mtch-context match))
                                               none))
                         matches))))]
          [else
           (lambda (exp hole-info nesting-depth)
             (let ([matches (match-pat exp)])
               (and matches
                    (list (make-mtch empty-bindings
                                     (hole->not-hole exp)
                                     none)))))])
        #f
        #t
        names)]
      [`(side-condition ,pat ,condition ,expr)
       (define-values (match-pat has-hole? has-hide-hole? names) (compile-pattern/default-cache pat))
       (values
        (if (or has-hole? has-hide-hole? (not (null? names)))
            (λ (exp hole-info nesting-depth)
              (let ([matches (match-pat exp hole-info nesting-depth)])
                (and matches
                     (let ([filtered (filter (λ (m) (condition (mtch-bindings m))) 
                                             (filter-multiples matches lang-α-equal?))])
                       (if (null? filtered)
                           #f
                           filtered)))))
            (λ (exp)
              (and (match-pat exp)
                   (condition empty-bindings))))
        has-hole?
        has-hide-hole?
        names)]
      [`(cross ,(? symbol? id))
       (define across-ht (compiled-lang-across-ht clang))
       (define across-list-ht (compiled-lang-across-list-ht clang))
       (cond
         [(hash-maps? across-ht id)
          (values
           (λ (exp hole-info nesting-depth)
             (match-nt (hash-ref across-list-ht id)
                       (hash-ref across-ht id)
                       id exp hole-info
                       lang-α-equal?))
           #t
           #f
           '())]
         [else
          (error 'compile-pattern "unknown cross reference ~a" id)])]
      [`(list ,pats ...)
       (define-values (rewritten has-hole?s has-hide-hole?s namess) (rewrite-ellipses pats compile-pattern/default-cache))
       (define any-has-hole? (ormap values has-hole?s))
       (define any-has-hide-hole? (ormap values has-hide-hole?s))
       (define repeats (length (filter repeat? rewritten)))
       (define non-repeats (length (filter (λ (x) (not (repeat? x))) rewritten)))
       (define names (apply append namess))
       (define rewritten/coerced
         (for/list ([pat (in-list rewritten)]
                    [has-hole? (in-list has-hole?s)]
                    [has-hide-hole? (in-list has-hide-hole?s)]
                    [names (in-list namess)])
           (cond
             [(repeat? pat)
              ;; have to use procedure arity test here in case the
              ;; name on this pattern is in the repeat (in which case
              ;; the has-hide-hole? boolean will be true, but pat
              ;; may not need converting)
              (if (equal? (procedure-arity (repeat-pat pat))
                          3)
                  pat
                  (struct-copy repeat pat [pat (convert-matcher (repeat-pat pat))]))]
             [else
              (if (or has-hole? has-hide-hole? (not (null? names)))
                  pat
                  (convert-matcher pat))])))
       (values
        (cond
          [(not (or any-has-hole? any-has-hide-hole? (not (null? names))))
           (λ (exp)
             (cond
               [(list? exp) (match-list/boolean rewritten exp)]
               [else #f]))]
          [(= 0 repeats)
           (λ (exp hole-info nesting-depth)
             (cond
               [(list? exp)
                ;; shortcircuit: if the list isn't the right length, give up immediately.
                (if (= (length exp) non-repeats)
                    (match-list/no-repeats rewritten/coerced exp hole-info nesting-depth)
                    #f)]
               [else #f]))]
          [else
           (λ (exp hole-info nesting-depth)
             (cond
               [(list? exp)
                ;; shortcircuit: if the list doesn't have the right number of
                ;; fixed parts, give up immediately
                (if (>= (length exp) non-repeats)
                    (match-list rewritten/coerced exp hole-info nesting-depth)
                    #f)]
               [else #f]))])
        any-has-hole?
        any-has-hide-hole?
        names)]
      
      [(? (compose not pair?))
       (cond
         [(compiled-pattern? pattern) ;; can this really happen anymore?!
          (values (compiled-pattern-cp pattern)
                  ;; return #ts here as a failsafe; no way to check better.
                  #t
                  #t)]
         [(eq? pattern '....)
          ;; this should probably be checked at compile time, not here
          (error 'compile-language "the pattern .... can only be used in extend-language")]
         [else
          (simple-match
           (λ (exp) 
             (equal? pattern exp)))])]))
  
  ;; simple-match : (any -> bool) -> (values <compiled-pattern> boolean boolean)
  ;; does a match based on a predicate
  (define (simple-match pred)
    (values (lambda (exp) (pred exp))
            #f
            #f
            '()))
  
  (compile-pattern/default-cache pattern))


;; convert-matcher : (any -> boolean) -> <compiled-pattern>
(define (convert-matcher boolean-based-matcher)
  (unless (equal? (procedure-arity boolean-based-matcher) 1)
    (error 'convert-matcher 
           "not a unary proc: ~s" 
           boolean-based-matcher))
  (define (match-boolean-to-record-converter exp hole-info nesting-depth)
    (and (boolean-based-matcher exp)
         (list (make-mtch empty-bindings
                          (build-flat-context exp)
                          none))))
  match-boolean-to-record-converter)

;; match-named-pat : symbol <compiled-pattern> -> <compiled-pattern>
(define (match-named-pat name match-pat mismatch-bind?)
  (λ (exp hole-info nesting-depth)
    (let ([matches (match-pat exp hole-info nesting-depth)])
      (and matches 
           (map (lambda (match)
                  (make-mtch
                   (make-bindings (cons (if mismatch-bind?
                                            (make-mismatch-bind name 
                                                                (mtch-context match)
                                                                nesting-depth)
                                            (make-bind name (mtch-context match)))
                                        (bindings-table (mtch-bindings match))))
                   (mtch-context match)
                   (mtch-hole match)))
                matches)))))

;; has-underscore? : symbol -> boolean
(define (has-underscore? sym)
  (memq #\_ (string->list (symbol->string sym))))

(define (memoize f needs-all-args?)
  (case (procedure-arity f)
    [(1) (memoize/1 f nohole)]
    [(3) (memoize/3 f w/hole)]
    [else (error 'memoize "unknown arity for ~s" f)]))

(define cache-size 63)
(define (set-cache-size! cs) (set! cache-size cs))

;; original version, but without closure allocation in hash lookup
(define-syntax (mk-memoize-key stx)
  (syntax-case stx ()
    [(_ arity)
     (with-syntax ([(args ...) (generate-temporaries (build-list (syntax-e #'arity) (λ (x) 'x)))])
       (with-syntax ([key-exp (if (= 1 (syntax-e #'arity))
                                  (car (syntax->list #'(args ...)))
                                  #'(list args ...))])
         #'(λ (f statsbox)
             (let ([ht (make-hash)]
                   [entries 0])
               (lambda (args ...)
                 (cond
                   [(not (caching-enabled?)) (f args ...)]
                   [else
                    (let* ([key key-exp])
                      ;(record-cache-test! statsbox)
                      (unless (< entries cache-size)
                        (set! entries 0)
                        (set! ht (make-hash)))
                      (let ([ans (hash-ref ht key uniq)])
                        (cond
                          [(eq? ans uniq)
                           ;(record-cache-miss! statsbox)
                           (set! entries (+ entries 1))
                           (let ([res (f args ...)])
                             (hash-set! ht key res)
                             res)]
                          [else ans])))]))))))]))

;(define memoize/1 (mk-memoize-key 1))
;(define memoize/3 (mk-memoize-key 3))

(define-syntax (mk-memoize-vec stx)
  (syntax-case stx ()
    [(_ arity)
     (with-syntax ([(args ...) (generate-temporaries (build-list (syntax-e #'arity) (λ (x) 'x)))])
       (with-syntax ([key-exp (if (= 1 (syntax-e #'arity))
                                  (car (syntax->list #'(args ...)))
                                  #'(list args ...))])
         #'(λ (f statsbox)
             (let* ([uniq (gensym)]
                    [this-cache-size cache-size]
                    [ans-vec (make-vector this-cache-size uniq)]
                    [key-vec (make-vector this-cache-size uniq)])
               (lambda (args ...)
                 (cond
                   [(not (caching-enabled?)) (f args ...)]
                   [else
                    ;(record-cache-test! statsbox)
                    ;(when (zero? (modulo (cache-stats-hits statsbox) 1000))
                    ;  (record-cache-size! statsbox (cons ans-vec key-vec)))
                    (let* ([key key-exp]
                           [index (modulo (equal-hash-code key) this-cache-size)])
                      (cond
                        [(equal? (vector-ref key-vec index) key)
                         (vector-ref ans-vec index)]
                        [else
                         ;(record-cache-miss! statsbox)
                         (unless (eq? uniq (vector-ref key-vec index)) (record-cache-clobber! statsbox))
                         (let ([ans (f args ...)])
                           (vector-set! key-vec index key)
                           (vector-set! ans-vec index ans)
                           ans)]))]))))))]))

(define memoize/1 (mk-memoize-vec 1))
(define memoize/3 (mk-memoize-vec 3))

;; hash version, but with an extra hash that tells when to evict cache entries
#;
(define (memoize/key f key-fn statsbox)
  (let* ([cache-size 50]
         [ht (make-hash)]
         [uniq (gensym)]
         [when-to-evict-table (make-hasheq)]
         [pointer 0])
    (lambda (x y)
      (record-cache-test! statsbox)
      (let* ([key (key-fn x y)]
             [value-in-cache (hash-ref ht key uniq)])
        (cond
          [(eq? value-in-cache uniq)
           (record-cache-miss! statsbox)
           (let ([res (f x y)])
             (let ([to-remove (hash-ref when-to-evict-table pointer uniq)])
               (unless (eq? uniq to-remove)
                 (hash-remove! ht to-remove)))
             (hash-set! when-to-evict-table pointer key)
             (hash-set! ht key res)
             (set! pointer (modulo (+ pointer 1) cache-size))
             res)]
          [else
           value-in-cache])))))

;; lru cache
;; for some reason, this seems to hit *less* than the "just dump stuff out" strategy!
#;
(define (memoize/key f key-fn statsbox)
  (let* ([cache-size 50]
         [cache '()])
    (lambda (x y)
      (record-cache-test! statsbox)
      (let ([key (key-fn x y)])
        (cond
          [(null? cache)
           ;; empty cache
           (let ([ans (f x y)])
             (record-cache-miss! statsbox)
             (set! cache (cons (cons key ans) '()))
             ans)]
          [(null? (cdr cache))
           ;; one element cache
           (if (equal? (car (car cache)) key)
               (cdr (car cache))
               (let ([ans (f x y)])
                 (record-cache-miss! statsbox)
                 (set! cache (cons (cons key ans) cache))
                 ans))]
          [else
           ;; two of more element cache
           (cond
             [(equal? (car (car cache)) key)
              ;; check first element
              (cdr (car cache))]
             [(equal? (car (cadr cache)) key)
              ;; check second element
              (cdr (cadr cache))]
             [else
              ;; iterate from the 3rd element onwards
              (let loop ([previous2 cache]
                         [previous1 (cdr cache)]
                         [current (cddr cache)]
                         [i 0])
                (cond
                  [(null? current)
                   ;; found the end of the cache -- need to drop the last element if the cache is too full,
                   ;; and put the current value at the front of the cache.
                   (let ([ans (f x y)])
                     (record-cache-miss! statsbox)
                     (set! cache (cons (cons key ans) cache))
                     (unless (< i cache-size)
                       ;; drop the last element from the cache
                       (set-cdr! previous2 '()))
                     ans)]
                  [else
                   (let ([entry (car current)])
                     (cond
                       [(equal? (car entry) key)
                        ;; found a hit 
                        
                        ; remove this element from the list where it is.
                        (set-cdr! previous1 (cdr current))
                        
                        ; move it to the front of the cache
                        (set! cache (cons current cache))
                        
                        ; return the found element
                        (cdr entry)]
                       [else
                        ;; didn't hit yet, continue searching
                        (loop previous1 current (cdr current) (+ i 1))]))]))])])))))

;; hash version, but with a vector that tells when to evict cache entries
#;
(define (memoize/key f key-fn statsbox)
  (let* ([cache-size 50]
         [ht (make-hash)]
         [uniq (gensym)]
         [vector (make-vector cache-size uniq)] ;; vector is only used to evict things from the hash
         [pointer 0])
    (lambda (x y)
      (let* ([key (key-fn x y)]
             [value-in-cache (hash-ref ht key uniq)])
        (cond
          [(eq? value-in-cache uniq)
           (let ([res (f x y)])
             (let ([to-remove (vector-ref vector pointer)])
               (unless (eq? uniq to-remove)
                 (hash-remove! ht to-remove)))
             (vector-set! vector pointer key)
             (hash-set! ht key res)
             (set! pointer (modulo (+ pointer 1) cache-size))
             res)]
          [else
           value-in-cache])))))

;; vector-based version, with a cleverer replacement strategy
#;
(define (memoize/key f key-fn statsbox)
  (let* ([cache-size 20]
         ;; cache : (vector-of (union #f (cons key val)))
         ;; the #f correspond to empty spots in the cache
         [cache (make-vector cache-size #f)] 
         [pointer 0])
    (lambda (x y)
      (let ([key (key-fn x y)])
        (let loop ([i 0])
          (cond
            [(= i cache-size)
             (unless (vector-ref cache pointer)
               (vector-set! cache pointer (cons #f #f)))
             (let ([pair (vector-ref cache pointer)]
                   [ans (f x y)])
               (set-car! pair key)
               (set-cdr! pair ans)
               (set! pointer (modulo (+ 1 pointer) cache-size))
               ans)]
            [else
             (let ([entry (vector-ref cache i)])
               (if entry
                   (let ([e-key (car entry)]
                         [e-val (cdr entry)])
                     (if (equal? e-key key)
                         e-val
                         (loop (+ i 1))))
                   
                   ;; if we hit a #f, just skip ahead and store this in the cache
                   (loop cache-size)))]))))))

;; original version
#;
(define (memoize/key f key-fn statsbox)
  (let ([ht (make-hash)]
        [entries 0])
    (lambda (x y)
      (record-cache-test! statsbox)
      (let* ([key (key-fn x y)]
             [compute/cache
              (lambda ()
                (set! entries (+ entries 1))
                (record-cache-miss! statsbox)
                (let ([res (f x y)])
                  (hash-set! ht key res)
                  res))])
        (unless (< entries 200) ; 10000 was original size
          (set! entries 0)
          (set! ht (make-hash)))
        (hash-ref ht key compute/cache)))))

(define (record-cache-miss! statsbox)
  (set-cache-stats-hits! statsbox (sub1 (cache-stats-hits statsbox)))
  (set-cache-stats-misses! statsbox (add1 (cache-stats-misses statsbox))))

(define (record-cache-test! statsbox)
  (set-cache-stats-hits! statsbox (add1 (cache-stats-hits statsbox))))

(define (record-cache-clobber! statsbox)
  (set-cache-stats-clobber-hits! statsbox (add1 (cache-stats-clobber-hits statsbox))))

(define-struct cache-stats (name misses hits clobber-hits sizes) #:mutable)
(define (new-cache-stats name) (make-cache-stats name 0 0 0 '()))

(define w/hole (new-cache-stats "hole"))
(define nohole (new-cache-stats "no-hole"))

(define (record-cache-size! cache-stats cache)
  (define size 
    (let loop ([cache cache])
      (cond
        [(vector? cache)
         (for/fold ([size (vector-length cache)])
                   ([ele (in-vector cache)])
           (+ size (loop ele)))]
        [(pair? cache)
         (+ 1 (loop (car cache)) (loop (cdr cache)))]
        [else 1])))
  (set-cache-stats-sizes! cache-stats (cons size (cache-stats-sizes cache-stats))))

(define (print-stats)
  (let ((stats (list w/hole nohole)))
    (for-each 
     (lambda (s) 
       (when (> (+ (cache-stats-hits s) (cache-stats-misses s)) 0)
         (printf "~a has ~a hits, ~a misses (~a% miss rate)\n" 
                 (cache-stats-name s)
                 (cache-stats-hits s)
                 (cache-stats-misses s)
                 (floor
                  (* 100 (/ (cache-stats-misses s)
                            (+ (cache-stats-hits s) (cache-stats-misses s))))))))
     stats)
    (let ((overall-hits (apply + (map cache-stats-hits stats)))
          (overall-miss (apply + (map cache-stats-misses stats)))
          (overall-clobber-hits (apply + (map cache-stats-clobber-hits stats))))
      (printf "---\nOverall hits:   ~a\n" overall-hits)
      (printf "Overall misses: ~a\n" overall-miss)
      (when (> (+ overall-hits overall-miss) 0)
        (printf "Overall miss rate: ~a%\n" 
                (floor (* 100 (/ overall-miss (+ overall-hits overall-miss))))))
      (printf "Overall clobbering hits: ~a\n" overall-clobber-hits))
    
    (let* ([sizes (apply append (map cache-stats-sizes stats))]
           [len (length sizes)])
      (unless (zero? len)
        (let ([avg (/ (apply + 0.0 sizes) len)])
          (printf "Average cache size ~s; ~a samples\n" avg len))))))

;; match-hole : compiled-pattern
(define match-hole
  (λ (exp hole-info nesting-depth)
    (if hole-info
        (list (make-mtch empty-bindings
                         the-hole
                         exp))
        (and (hole? exp)
             (list (make-mtch empty-bindings
                              the-hole
                              none))))))

;; match-in-hole : sexp sexp sexp compiled-pattern compiled-pattern -> compiled-pattern
(define (match-in-hole context contractum exp match-context match-contractum)
   (λ (exp old-hole-info nesting-depth)
     (define mtches (match-context exp #t nesting-depth))
     (and mtches
          (let loop ([mtches mtches]
                     [acc null])
            (cond
              [(null? mtches) 
               (if (null? acc)
                   #f
                   acc)]
              [else 
               (define mtch (car mtches))
               (define bindings (mtch-bindings mtch))
               (define hole-exp (mtch-hole mtch))
               (define contractum-mtches (match-contractum hole-exp old-hole-info nesting-depth))
               (when (eq? none hole-exp)
                 (error 'matcher.rkt "found no hole when matching a decomposition"))
               (if contractum-mtches
                   (let i-loop ([contractum-mtches contractum-mtches]
                                [acc acc])
                     (cond
                       [(null? contractum-mtches) (loop (cdr mtches) acc)]
                       [else (let* ([contractum-mtch (car contractum-mtches)]
                                    [contractum-bindings (mtch-bindings contractum-mtch)])
                               (i-loop
                                (cdr contractum-mtches)
                                (cons
                                 (make-mtch (make-bindings
                                             (append (bindings-table contractum-bindings)
                                                     (bindings-table bindings)))
                                            (build-nested-context 
                                             (mtch-context mtch)
                                             (mtch-context contractum-mtch))
                                            (mtch-hole contractum-mtch))
                                 acc)))]))
                   (loop (cdr mtches) acc))])))))

(define (match-in-hole/contractum-boolean context contractum exp match-context match-contractum)
  (λ (exp)
    ;; we get here only if there are no names in the context so we can safely pass 0 as the depth
    (define mtches (match-context exp #t 0))
    (and mtches
         (let loop ([mtches mtches])
           (cond
             [(null? mtches) #f]
             [else 
              (let* ([mtch (car mtches)]
                     [hole-exp (mtch-hole mtch)]
                     [contractum-mtches (match-contractum hole-exp)])
                (when (eq? none hole-exp)
                  (error 'matcher.rkt "found no hole when matching a decomposition"))
                (or contractum-mtches
                    (loop (cdr mtches))))])))))

;; match-list/boolean : (listof (union repeat (any -> boolean)))
;;                      sexp hole-info -> boolean
(define (match-list/boolean patterns exp)
  (define has-repeats? (ormap repeat? patterns))
  (cond
    [(not (list? exp)) #f]
    [(and (not has-repeats?)
          (not (= (length patterns) (length exp))))
     #f]
    [else
     (let loop ([exp exp]
                [patterns patterns])
       (cond
         [(null? exp)
          (let loop ([patterns patterns])
            (or (null? patterns)
                (and (repeat? (car patterns))
                     (loop (cdr patterns)))))]
         [(null? patterns) #f]
         [(repeat? (car patterns)) 
          (or (loop exp (cdr patterns))
              (and ((repeat-pat (car patterns)) (car exp))
                   (loop (cdr exp) patterns)))]
         [else
          (and ((car patterns) (car exp))
               (loop (cdr exp) (cdr patterns)))]))]))

;; match-list : (listof (union repeat compiled-pattern)) sexp hole-info -> (union #f (listof bindings))
(define (match-list patterns exp hole-info nesting-depth)
  (let (;; raw-match : (listof (listof (listof mtch)))
        [raw-match (match-list/raw patterns exp hole-info nesting-depth)])
    
    (and (not (null? raw-match))
         (let loop ([raw-match raw-match])
           (cond
             [(null? raw-match) '()]
             [else (append (combine-matches (car raw-match))
                           (loop (cdr raw-match)))])))))

;; match-list/raw : (listof (union repeat compiled-pattern)) 
;;                  sexp
;;                  hole-info
;;               -> (listof (listof (listof mtch)))
;; the result is the raw accumulation of the matches for each subpattern, as follows:
;;  (listof (listof (listof mtch)))
;;  \       \       \-------------/  a match for one position in the list (failures don't show up)
;;   \       \-------------------/   one element for each position in the pattern list
;;    \-------------------------/    one element for different expansions of the ellipses
;; the failures to match are just removed from the outer list before this function finishes
;; via the `fail' argument to `loop'.
(define (match-list/raw patterns exp hole-info nesting-depth)
  (let/ec k
    (let loop ([patterns patterns]
               [exp exp]
               ;; fail : -> alpha
               ;; causes one possible expansion of ellipses to fail
               ;; initially there is only one possible expansion, so
               ;; everything fails.
               [fail (lambda () (k null))])
      (cond
        [(pair? patterns)
         (let ([fst-pat (car patterns)])
           (cond
             [(repeat? fst-pat)
              (if (or (null? exp) (pair? exp))
                  (let ([r-pat (repeat-pat fst-pat)]
                        [r-mt (make-mtch (make-bindings (repeat-empty-bindings fst-pat))
                                         (build-flat-context '())
                                         none)])
                    (apply 
                     append
                     (cons (let/ec k
                             (let ([mt-fail (lambda () (k null))])
                               (map (lambda (pat-ele) 
                                      (cons (add-ellipses-index (list r-mt)
                                                                (repeat-name fst-pat)
                                                                (repeat-mismatch fst-pat)
                                                                0
                                                                nesting-depth)
                                            pat-ele))
                                    (loop (cdr patterns) exp mt-fail))))
                           (let r-loop ([exp exp]
                                        ;; past-matches is in reverse order
                                        ;; it gets reversed before put into final list
                                        [past-matches (list r-mt)]
                                        [index 1])
                             (cond
                               [(pair? exp)
                                (let* ([fst (car exp)]
                                       [m (r-pat fst hole-info (+ nesting-depth 1))])
                                  (if m
                                      (let* ([combined-matches (collapse-single-multiples m past-matches)]
                                             [reversed 
                                              (add-ellipses-index 
                                               (reverse-multiples combined-matches)
                                               (repeat-name fst-pat)
                                               (repeat-mismatch fst-pat)
                                               index
                                               nesting-depth)])
                                        (cons 
                                         (let/ec fail-k
                                           (map (lambda (x) (cons reversed x))
                                                (loop (cdr patterns) 
                                                      (cdr exp)
                                                      (lambda () (fail-k null)))))
                                         (r-loop (cdr exp)
                                                 combined-matches
                                                 (+ index 1))))
                                      (list null)))]
                               ;; what about dotted pairs?
                               [else (list null)])))))
                  (fail))]
             [else
              (cond
                [(pair? exp)
                 (let* ([fst-exp (car exp)]
                        [match (fst-pat fst-exp hole-info nesting-depth)])
                   (if match
                       (let ([exp-match (map (λ (mtch) (make-mtch (mtch-bindings mtch)
                                                                  (build-list-context (mtch-context mtch))
                                                                  (mtch-hole mtch)))
                                             match)])
                         (map (lambda (x) (cons exp-match x))
                              (loop (cdr patterns) (cdr exp) fail)))
                       (fail)))]
                [else
                 (fail)])]))]
        [else
         (if (null? exp)
             (list null)
             (fail))]))))

(define null-match (list (make-mtch (make-bindings '()) '() none)))

(define (match-list/no-repeats patterns exp hole-info nesting-depth)
  
  (define (match-list/raw/no-repeats/no-ambiguity patterns exp hole-info)
    (let/ec k
      (define-values (bindings lst hole)
        (let loop ([patterns patterns]
                   [exp exp])
          (cond
            [(pair? patterns)
             (let ([fst-pat (car patterns)])
               (cond
                 [(pair? exp)
                  (let* ([fst-exp (car exp)]
                         [fst-mtchs (fst-pat fst-exp hole-info nesting-depth)])
                    (cond
                      [(not fst-mtchs) (k #f)]
                      [(null? (cdr fst-mtchs))
                       (define mtch1 (car fst-mtchs))
                       (define-values (bindings lst hole) (loop (cdr patterns) (cdr exp)))
                       (define new-bindings (bindings-table (mtch-bindings mtch1)))
                       (values (append new-bindings bindings)
                               (build-cons-context (mtch-context mtch1) lst)
                               (pick-hole (mtch-hole mtch1) hole))]
                      [else
                       (error 'ack)]))]
                 [else (k #f)]))]
            [else
             (if (null? exp)
                 (values '() '() none)
                 (k #f))])))
      (list (make-mtch (make-bindings bindings) lst hole))))
  
  (define (match-list/raw/no-repeats patterns exp hole-info)
    (let/ec k
      (let loop ([patterns patterns]
                 [exp exp])
        (cond
          [(pair? patterns)
           (let ([fst-pat (car patterns)])
             (cond
               [(pair? exp)
                (let* ([fst-exp (car exp)]
                       [fst-mtchs (fst-pat fst-exp hole-info nesting-depth)])
                  (cond
                    [fst-mtchs
                     (define rst-mtchs (loop (cdr patterns) (cdr exp)))
                     (cond
                       [rst-mtchs
                        (combine-pair/no-repeat fst-mtchs rst-mtchs)]
                       [else
                        (k #f)])]
                    [else (k #f)]))]
               [else (k #f)]))]
          [else
           (if (null? exp)
               null-match
               (k #f))]))))
  
  ;; combine-pair : (listof mtch) (listof mtch) -> (listof mtch)
  (define (combine-pair/no-repeat fst snd)
    (let ([mtchs null])
      (for-each 
       (lambda (mtch1)
         (for-each
          (lambda (mtch2)
            (set! mtchs (cons (make-mtch 
                               (make-bindings (append (bindings-table (mtch-bindings mtch1))
                                                      (bindings-table (mtch-bindings mtch2))))
                               (build-cons-context (mtch-context mtch1) (mtch-context mtch2))
                               (pick-hole (mtch-hole mtch1) 
                                          (mtch-hole mtch2)))
                              mtchs)))
          snd))
       fst)
      mtchs))
  
  ;(match-list/raw/no-repeats/no-ambiguity patterns exp hole-info)
  (match-list/raw/no-repeats patterns exp hole-info)
  )

;; add-ellipses-index : (listof mtch) (or/c sym #f) (or/c sym #f) number -> (listof mtch)
(define (add-ellipses-index mtchs name mismatch-name i nesting-depth)
  (let* ([ribs '()]
         [ribs (if name
                   (cons (make-bind name i) ribs)
                   ribs)]
         [ribs (if mismatch-name
                   (cons (make-mismatch-bind mismatch-name i nesting-depth) ribs)
                   ribs)])
    (map (λ (mtch) (make-mtch (make-bindings (append ribs (bindings-table (mtch-bindings mtch))))
                              (mtch-context mtch)
                              (mtch-hole mtch)))
         mtchs)))

;; collapse-single-multiples : (listof mtch) (listof mtch[to-lists]) -> (listof mtch[to-lists])
(define (collapse-single-multiples bindingss multiple-bindingss)
  (apply append 
         (map
          (lambda (multiple-match)
            (let ([multiple-bindings (mtch-bindings multiple-match)])
              (map
               (lambda (single-match)
                 (let ([single-bindings (mtch-bindings single-match)])
                   (make-mtch (make-bindings 
                               (map (match-lambda* 
                                      [`(,(struct bind (name sing-exp)) ,(struct bind (name mult-exp)))
                                       (make-bind name (cons sing-exp mult-exp))]
                                      [`(,(struct mismatch-bind (name sing-exp nesting-depth1))
                                         ,(struct mismatch-bind (name mult-exp nesting-depth2)))
                                       (make-mismatch-bind name 
                                                           (cons sing-exp mult-exp)
                                                           nesting-depth1)]
                                      [else 
                                       (error 'collapse-single-multiples
                                              "internal error: expected matches' bindings in same order; got\n  ~e\n  ~e"
                                              single-bindings
                                              multiple-bindings)])
                                    (bindings-table single-bindings)
                                    (bindings-table multiple-bindings)))
                              (build-cons-context
                               (mtch-context single-match)
                               (mtch-context multiple-match))
                              (pick-hole (mtch-hole single-match)
                                         (mtch-hole multiple-match)))))
               bindingss)))
          multiple-bindingss)))

;; pick-hole : (union none sexp) (union none sexp) -> (union none sexp)
(define (pick-hole s1 s2)
  (cond
    [(eq? none s1) s2]
    [(eq? none s2) s1]
    [(error 'matcher.rkt "found two holes")]))

;; reverse-multiples : (listof mtch[to-lists]) -> (listof mtch[to-lists])
;; reverses the rhs of each rib in the bindings and reverses the context.
(define (reverse-multiples matches)
  (map (lambda (match)
         (let ([bindings (mtch-bindings match)])
           (make-mtch
            (make-bindings
             (map (lambda (rib)
                    (cond
                      [(bind? rib)
                       (make-bind (bind-name rib)
                                  (reverse (bind-exp rib)))]
                      [(mismatch-bind? rib)
                       (make-mismatch-bind (mismatch-bind-name rib)
                                           (reverse (mismatch-bind-exp rib))
                                           (mismatch-bind-nesting-depth rib))]))
                  (bindings-table bindings)))
            (reverse-context (mtch-context match))
            (mtch-hole match))))
       matches))

;; match-nt : (listof compiled-rhs) (listof compiled-rhs) sym exp hole-info (exp exp -> boolean)
;;        -> (union #f (listof bindings))
(define (match-nt list-rhs non-list-rhs nt term hole-info lang-α-equal?)
  (if hole-info
      
      (let loop ([rhss (if (or (null? term) (pair? term))
                           list-rhs
                           non-list-rhs)]
                 [ans '()])
        (cond
          [(null? rhss) 
           (if (null? ans)
               #f
               (begin
                 (when (check-redudancy)
                   (let ([rd (remove-duplicates ans)])
                     (unless (= (length rd) (length ans))
                       (eprintf "found redundancy when matching the non-terminal ~s against:\n~s~a"
                                nt
                                term
                                (apply
                                 string-append
                                 (map (λ (x) (format "\n  ~s" x))
                                      ans))))))
                 ans))]
          [else
           (let ([mth (call-nt-proc/bindings (car rhss) term hole-info lang-α-equal?)])
             (cond
               [mth
                (loop (cdr rhss) (append mth ans))]
               [else 
                (loop (cdr rhss) ans)]))]))
      
      ;; if we're not doing a decomposition, we just need
      ;; to find the first match, not all of the matches
      (let loop ([rhss (if (or (null? term) (pair? term))
                           list-rhs
                           non-list-rhs)])
        (cond
          [(null? rhss) #f]
          [else
           (or (call-nt-proc/bindings (car rhss) term hole-info lang-α-equal?)
               (loop (cdr rhss)))]))))

(define check-redudancy (make-parameter #f))

(define (match-nt/boolean list-rhs non-list-rhs nt term lang-α-equal?)
  (let loop ([rhss (if (or (null? term) (pair? term))
                       list-rhs
                       non-list-rhs)])
    (cond
      [(null? rhss) #f]
      [else
       (or (call-nt-proc/bool (compiled-pattern-cp (car rhss)) term lang-α-equal?)
           (loop (cdr rhss)))])))

(define (call-nt-proc/bool nt-proc exp lang-α-equal?)
  (if (procedure-arity-includes? nt-proc 1)
      (nt-proc exp)
      (and (remove-bindings/filter (nt-proc exp #f 0) lang-α-equal?) #t)))

(define (call-nt-proc/bindings compiled-pattern exp hole-info lang-α-equal?)
  (define nt-proc (compiled-pattern-cp compiled-pattern))
  (define skip-dup? (compiled-pattern-skip-dup-check? compiled-pattern))
  (define has-names? (compiled-pattern-binds-names? compiled-pattern))
  (cond
    [(procedure-arity-includes? nt-proc 1)
     (and (nt-proc exp)
          (list (make-mtch empty-bindings
                           (build-flat-context exp)
                           none)))]
    [skip-dup? 
     (define res (nt-proc exp hole-info 0))
     (and res
          (not (null? res))
          (if has-names?
              (map (λ (match)
                     (make-mtch empty-bindings
                                (mtch-context match)
                                (mtch-hole match)))
                   res)
              res))]
    [else
     (remove-bindings/filter (nt-proc exp hole-info 0) lang-α-equal?)]))

;; remove-bindings/filter : (union #f (listof mtch)) (exp exp -> boolean) -> (union #f (listof mtch))
(define (remove-bindings/filter matches lang-α-equal?)
  (and matches
       (let ([filtered (filter-multiples matches equal?)])
         ;(printf ">> ~s\n=> ~s\n\n" matches filtered)
         (and (not (null? filtered))
              (map (λ (match)
                     (make-mtch empty-bindings
                                (mtch-context match)
                                (mtch-hole match)))
                   matches)))))

;; rewrite-ellipses : (listof l-pat) 
;;                    (pattern -> (values compiled-pattern boolean))
;;                 -> (values (listof (union repeat compiled-pattern)) boolean)
;; moves the ellipses out of the list and produces repeat structures
(define (rewrite-ellipses pattern compile)
  (define (maybe-cons hd tl) (if hd (cons hd tl) tl))
  (let loop ([exp-eles pattern])
    (match exp-eles
      [`() (values empty empty empty empty)]
      [(cons `(repeat ,pat ,name ,mismatch-name) rst)
       (define-values (fst-compiled fst-has-hole? fst-has-hide-hole? fst-names) (compile pat))
       (define-values (rst-compiled rst-has-hole? rst-has-hide-hole? rst-names) (loop rst))
       (values (cons (make-repeat fst-compiled
                                  (extract-empty-bindings pat)
                                  name
                                  mismatch-name)
                     rst-compiled)
               (cons fst-has-hole? rst-has-hole?)
               (cons (or fst-has-hide-hole? name mismatch-name) rst-has-hide-hole?)
               (cons (maybe-cons name (maybe-cons (and mismatch-name `(mismatch , mismatch-name))
                                                  fst-names))
                     rst-names))]
      [(cons pat rst)
       (define-values (fst-compiled fst-has-hole? fst-has-hide-hole? fst-names) (compile pat))
       (define-values (rst-compiled rst-has-hole? rst-has-hide-hole? rst-names) (loop rst))
       (values (cons fst-compiled rst-compiled)
               (cons fst-has-hole? rst-has-hole?)
               (cons fst-has-hide-hole? rst-has-hide-hole?)
               (cons fst-names rst-names))])))

(define (prefixed-with? prefix exp)
  (and (symbol? exp)
       (let* ([str (symbol->string exp)]
              [len (string-length str)])
         (and (len . >= . (string-length prefix))
              (string=? (substring str 0 (string-length prefix))
                        prefix)))))

(define dummy (box 0))

;; extract-empty-bindings : pattern -> (listof rib)
(define (extract-empty-bindings pattern)
  (let loop ([pattern pattern]
             [ribs null])
    (match-a-pattern pattern
      [`any ribs]
      [`number ribs]
      [`string ribs]
      [`natural ribs]
      [`integer ribs]
      [`real ribs]
      [`boolean ribs]
      [`variable ribs]
      [`(variable-except ,vars ...) ribs]
      [`(variable-prefix ,vars) ribs]
      [`variable-not-otherwise-mentioned ribs]
      
      [`hole ribs]
      [`(nt ,nt) ribs]
      [`(name ,name ,pat)
       (cons (make-bind name '()) (loop pat ribs))]
      [`(mismatch-name ,name ,pat) 
       (cons (make-mismatch-bind name '() 'unknown-mismatch-depth) (loop pat ribs))]
      [`(in-hole ,context ,contractum) (loop contractum (loop context ribs))]
      [`(hide-hole ,p) (loop p ribs)]
      [`(side-condition ,pat ,test ,expr) (loop pat ribs)]
      [`(cross ,id) ribs]
      [`(list ,pats ...)
       (let-values ([(rewritten has-hole? has-hide-hole? names)
                     (rewrite-ellipses pats (lambda (x) (values x #f #f '())))])
         (let i-loop ([r-exps rewritten]
                      [ribs ribs])
           (cond
             [(null? r-exps) ribs]
             [else (let ([r-exp (car r-exps)])
                     (cond
                       [(repeat? r-exp)
                        (define bindings (if (repeat-mismatch r-exp)
                                             (list (make-mismatch-bind (repeat-mismatch r-exp)
                                                                       '()
                                                                       'unknown-mismatch-depth))
                                             '()))
                        (define bindings2 (if (repeat-name r-exp)
                                              (cons (make-bind (repeat-name r-exp) '()) bindings)
                                              bindings))
                        (append bindings2
                                (repeat-empty-bindings r-exp)
                                (i-loop (cdr r-exps) ribs))]
                       [else
                        (loop (car r-exps) (i-loop (cdr r-exps) ribs))]))])))]
      [(? (compose not pair?)) ribs])))

;; combine-matches : (listof (listof mtch)) -> (listof mtch)
;; input is the list of bindings corresonding to a piecewise match
;; of a list. produces all of the combinations of complete matches
(define (combine-matches matchess)
  (let loop ([matchess matchess])
    (cond
      [(null? matchess) combine-matches-base-case]
      [else (combine-pair (car matchess) (loop (cdr matchess)))])))

;; this 'inlines' build-flat-context so that the definition can remain here, near where it is used.
(define combine-matches-base-case (list (make-mtch empty-bindings
						   '() #;(build-flat-context '()) 
						   none)))

;; combine-pair : (listof mtch) (listof mtch) -> (listof mtch)
(define (combine-pair fst snd)
  (let ([mtchs null])
    (for-each 
     (lambda (mtch1)
       (for-each
        (lambda (mtch2)
          (set! mtchs (cons (make-mtch 
                             (make-bindings (append (bindings-table (mtch-bindings mtch1))
                                                    (bindings-table (mtch-bindings mtch2))))
                             (build-append-context (mtch-context mtch1) (mtch-context mtch2))
                             (pick-hole (mtch-hole mtch1) 
                                        (mtch-hole mtch2)))
                            mtchs)))
        snd))
     fst)
    mtchs))

(define (hash-maps? ht key)
  (not (eq? (hash-ref ht key uniq) uniq)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; context adt
;;

#|
  ;; This version of the ADT isn't right yet -- 
  ;; need to figure out what to do about (name ...) patterns.

  (define-values (struct:context make-context context? context-ref context-set!)
    (make-struct-type 'context #f 1 0 #f '() #f 0))
  (define hole values)
  (define (build-flat-context exp) (make-context (lambda (x) exp)))
  (define (build-cons-context c1 c2) (make-context (lambda (x) (cons (c1 x) (c2 x)))))
  (define (build-append-context l1 l2) (make-context (lambda (x) (append (l1 x) (l2 x)))))
  (define (build-list-context l) (make-context (lambda (x) (list (l x)))))
  (define (build-nested-context c1 c2) (make-context (lambda (x) (c1 (c2 x)))))
  (define (plug exp hole-stuff) (exp hole-stuff))
  (define (reverse-context c) (make-context (lambda (x) (reverse (c x)))))

|#
(define (context? x) #t)

(define (hole->not-hole exp)
  (let loop ([exp exp])
    (cond
      [(pair? exp) 
       (define old-car (car exp))
       (define new-car (loop old-car))
       (cond
         [(eq? new-car old-car)
          (define old-cdr (cdr exp))
          (define new-cdr (loop old-cdr))
          (if (eq? new-cdr old-cdr)
              exp
              (cons new-car new-cdr))]
         [else (cons new-car (cdr exp))])]
      [(eq? exp the-hole)
       the-not-hole]
      [else exp])))

(define (build-flat-context exp) exp)
(define (build-cons-context e1 e2) (cons e1 e2))
(define (build-append-context e1 e2) (append e1 e2))
(define (build-list-context x) (list x))
(define (reverse-context x) (reverse x))
(define (build-nested-context c1 c2) 
  (plug c1 c2))

(define (plug exp hole-stuff)
  (let loop ([exp exp])
    (cond
      [(pair? exp) 
       (define old-car (car exp))
       (define new-car (loop old-car))
       (cond
         [(eq? new-car old-car)
          (define old-cdr (cdr exp))
          (define new-cdr (loop old-cdr))
          (if (eq? new-cdr old-cdr)
              exp
              (cons new-car new-cdr))]
         [else (cons new-car (cdr exp))])]
      [(eq? the-not-hole exp)
       the-not-hole]
      [(eq? the-hole exp)
       hole-stuff]
      [else exp])))

;;
;; end context adt
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; used in hash lookups to tell when something isn't in the table
(define uniq (gensym))

(provide/contract
 (match-pattern (compiled-pattern? any/c . -> . (or/c false/c (listof mtch?))))
 (match-pattern? (compiled-pattern? any/c . -> . boolean?))
 (compile-pattern (-> compiled-lang? any/c boolean?
                      compiled-pattern?))
 
 (set-cache-size! (-> (and/c integer? positive?) void?))
 (cache-size (and/c integer? positive?))
 
 (compile-language (-> any/c (listof nt?) (hash/c symbol? uf-set?) 
                       any/c #;(listof (list/c compiled-pattern? bspec?))
                       compiled-lang?)))
(provide compiled-pattern? 
         print-stats)

;; for test suite
(provide build-cons-context
         build-flat-context
         context?
         extract-empty-bindings
         (rename-out [bindings-table bindings-table-unchecked])
         (struct-out mismatch-bind)
         (struct-out compiled-pattern))

(provide lookup-binding
         
         compiled-pattern
         
         plug
         none? none
         
         make-repeat
         rewrite-ellipses
         build-compatible-context-language
         caching-enabled?
         check-redudancy
         prefix-nts
         mk-uf-sets)
