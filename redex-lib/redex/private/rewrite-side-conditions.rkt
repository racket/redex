#lang racket/base

#|

Additional (backwards-incompatible) checks to
consider adding when in some special mode:

  - metafunction names should be syntax errors (not literals)

  - keywords should be syntax errors

see also term.rkt for some restrictions/changes there

|#

  (require "underscore-allowed.rkt"
           "term-fn.rkt"
           "keyword-macros.rkt"
           racket/match
           "match-a-pattern.rkt"
           (for-template
            racket/base
            "term.rkt"
            "matcher.rkt"))
  
  (provide rewrite-side-conditions/check-errs
           break-out-underscore
           extract-names
           (rename-out [binds? id-binds?])
           raise-ellipsis-depth-error
           make-language-id
           language-id-nts
           bind-pattern-names
           check-hole-sanity)
  
  (provide (struct-out id/depth))
  
  ;; the result is a four-tuple (as a list) syntax object
  ;; - the first is an ordinary expression that evaluates
  ;;   to (void), but tells check syntax about binding information
  ;; - the second is an expression that, when prefixed with a
  ;;   quasiquote, evaluates to a pattern that can be used with
  ;;   match-a-pattern (at runtime).

  ;; if rewrite-id is not #f, then it must be a pair of
  ;; a symbol and a well-formed rewritten pattern.
  ;; Occurrences of that symbol in the `orig-stx' pattern are replaced by
  ;; the pattern. Also, uses of that identifier not in "pattern expression" positions
  ;; are signalled as syntax errors
  (define (rewrite-side-conditions/check-errs all-nts/lang-id what bind-names? orig-stx
                                              #:rewrite-as-any-id [rewrite-as-any-id #f]
                                              #:aliases [_aliases #f]
                                              #:nt-identifiers [_nt-identifiers #f])
    (unless (or (not what) (symbol? what))
      (error 'rewrite-side-conditions/check-errs
             "expected `what' argument to be a symbol or #f, got ~s"
             what))
    (define aliases
      (or _aliases
          (and (identifier? all-nts/lang-id)
               (language-id-nt-aliases
                all-nts/lang-id what))))
    (unless aliases
      (error 'rewrite-side-conditions/check-errs
             "expected either a language binding or an explicit #:aliases argument"))
    (define all-nts (if (identifier? all-nts/lang-id)
                        (language-id-nts all-nts/lang-id what)
                        all-nts/lang-id))
    (define nt->hole (and (identifier? all-nts/lang-id)
                          (language-id-nt-hole-map all-nts/lang-id #f)))
    (define nt-identifiers (or _nt-identifiers
                               (and (identifier? all-nts/lang-id)
                                    (language-id-nt-identifiers all-nts/lang-id #f))))
    (unless nt-identifiers
      (error 'rewrite-side-conditions/check-errs
             "expected either a language binding or an explicit #:nt-identifiers argument"))
    (define (expected-exact name n stx)
      (raise-syntax-error what (format "~a expected to have ~a arguments" 
                                       name
                                       n)
                          orig-stx 
                          stx))

    (define (expected-arguments name stx)
      (raise-syntax-error what (format "~a expected to have arguments" name) orig-stx stx))
    (define (expect-identifier src stx)
      (unless (identifier? stx)
        (raise-syntax-error what "expected an identifier" src stx)))
    
    ; union-find w/o balancing or path compression (at least for now)
    (define (union e f sets)
      (hash-set sets (find f sets) (find e sets)))
    (define (find e sets)
      (let recur ([chd e] [par (hash-ref sets e #f)])
        (if (and par (not (eq? chd par))) (recur par (hash-ref sets par #f)) chd)))
    
    (define void-stx #'(void))
    
    (define last-contexts (make-hasheq))
    (define last-stx (make-hasheq)) ;; used for syntax error reporting
    (define assignments #hasheq())

    ;; hash[sym -o> (listof stx)]
    (define var-locs-table (make-hash))
    
    ;; hash[sym -o> sym]
    ;; tells the original names for any given repeat to be replaced after
    ;; normalization and checking has finished
    (define original-repeat-names (make-hash))
    
    (define (record-binder pat-stx under under-mismatch-ellipsis)
      (define pat-sym (syntax->datum pat-stx))
      (hash-set! var-locs-table pat-sym (cons pat-stx (hash-ref var-locs-table pat-sym '())))
      
      (set! assignments
            (if (null? under)
                assignments
                (let ([last (hash-ref last-contexts pat-sym #f)])
                  (hash-set! last-stx pat-sym (cons pat-stx (hash-ref last-stx pat-sym '())))
                  (cond
                    [last
                     (unless (equal? (length last) (length under))
                       (define stxs (hash-ref last-stx pat-sym))
                       (raise-syntax-error
                        what
                        (format "found ~a under ~a ellips~as in one place and ~a ellips~as in another"
                                pat-sym
                                (length last)
                                (if (= 1 (length last)) "i" "e")
                                (length under)
                                (if (= 1 (length under)) "i" "e"))
                        orig-stx
                        (car stxs)
                        (cdr stxs)))
                     (foldl (λ (cur last asgns) (union cur last asgns)) assignments under last)]
                    [else
                     (hash-set! last-contexts pat-sym under)
                     assignments])))))
    
    (define (record-syncheck-use stx nt)
      (define the-uses (build-disappeared-uses nt-identifiers nt stx))
      (define old (syntax-property void-stx 'disappeared-use))
      (set! void-stx
            (syntax-property void-stx
                             'disappeared-use
                             (if old (cons old the-uses) the-uses))))

    (define ellipsis-number 0)
    
    (define-values (term names)
      (let loop ([term orig-stx]
                 [under '()]
                 [under-mismatch-ellipsis '()])
        (syntax-case term (side-condition variable-except variable-prefix
                                          hole name in-hole hide-hole unquote and)
          [(side-condition pre-pat (and))
           ;; rewriting metafunctions (and possibly other things) that have no where, etc clauses
           ;; end up with side-conditions that are empty 'and' expressions, so we just toss them here.
           (loop #'pre-pat under under-mismatch-ellipsis)]
          [(side-condition pre-pat exp)
           (let ()
             (define-values (pre-term pre-vars) (loop #'pre-pat under under-mismatch-ellipsis))
             (define names/ellipses (map build-dots pre-vars))
             (with-syntax ([pre-term pre-term]
                           [((name name/ellipses) ...)
                            (map (λ (id name/ellipses)
                                   (list (id/depth-id id)
                                         name/ellipses))
                                 pre-vars
                                 names/ellipses)]
                           [src-loc 
                            (let ([stx #'exp])
                              (define src (syntax-source stx))
                              (define line (syntax-line stx))
                              (define col (syntax-column stx))
                              (format "~a:~a" 
                                      (if (path? src)
                                          (path->presentable-string src)
                                          "?")
                                      (if (and line col)
                                          (format "~a:~a" line col)
                                          (if line
                                              (format "~a:?" line)
                                              (syntax-position stx)))))])
               (values (syntax/loc (if (syntax? term)
                                       term
                                       (datum->syntax #f 'whatever #f))
                         (side-condition
                          pre-term
                          ,(lambda (bindings)
                             (term-let
                              ([name/ellipses (lookup-binding bindings 'name)] ...)
                              exp))
                          ; For use in error messages.
                          src-loc))
                       pre-vars)))]
          [(side-condition a ...) (expected-exact 'side-condition 2 term)]
          [side-condition (expected-arguments 'side-condition term)]
          [(variable-except a ...)
           (begin
             (for ([a (in-list (syntax->list #'(a ...)))])
               (expect-identifier term a))
             (values term '()))]
          [variable-except (expected-arguments 'variable-except term)]
          [(variable-prefix a)
           (begin
             (expect-identifier term #'a)
             (values term '()))]
          [(variable-prefix a ...) (expected-exact 'variable-prefix 1 term)]
          [variable-prefix (expected-arguments 'variable-prefix term)]
          [hole (values term '())]
          [(name x y)
           (let ()
             (unless (identifier? #'x)
               (raise-syntax-error what "expected an identifier"
                                   orig-stx #'x))
             (when (equal? (syntax-e #'x) rewrite-as-any-id)
               (raise-syntax-error what
                                   "the identifier bound by a shortcut may not be used in a with"
                                   orig-stx #'x))
             (define-values (sub-term sub-vars) (loop #'y under under-mismatch-ellipsis))
             (record-binder #'x under under-mismatch-ellipsis)
             (values #`(name x #,sub-term)
                     (cons (make-id/depth #'x (length under))
                           sub-vars)))]
          [(name x ...) (expected-exact 'name 2 term)]
          [name (expected-arguments 'name term)]
          [(in-hole a b)
           (let ()
             (define-values (a-term a-vars) (loop #'a under under-mismatch-ellipsis))
             (define-values (b-term b-vars) (loop #'b under under-mismatch-ellipsis))
             (values #`(in-hole #,a-term #,b-term)
                     (append a-vars b-vars)))]
          [(in-hole a ...) (expected-exact 'in-hole 2 term)]
          [in-hole (expected-arguments 'in-hole term)]
          [(hide-hole a) 
           (let ()
             (define-values (sub-term vars) (loop #'a under under-mismatch-ellipsis))
             (values #`(hide-hole #,sub-term) vars))]
          [(hide-hole a ...) (expected-exact 'hide-hole 1 term)]
          [hide-hole (expected-arguments 'hide-hole term)]
          [(unquote . _)
           (raise-syntax-error what "unquote disallowed in patterns" orig-stx term)]
          [_
           (identifier? term)
           (let ()
             (define-values (prefix-sym suffix-sym) (break-out-underscore term))
             (define unaliased-sym (if prefix-sym
                                       (hash-ref aliases prefix-sym prefix-sym)
                                       (hash-ref aliases (syntax-e term) (syntax-e term))))
             (cond
               [suffix-sym
                (define unaliased-prefix-stx (datum->syntax term unaliased-sym))
                (define mismatch? (regexp-match? #rx"^!_" (symbol->string suffix-sym)))
                (cond
                  [(eq? (syntax-e term) '_) (values `any '())] ;; don't bind wildcard
                  [(eq? prefix-sym '...)
                   (raise-syntax-error 
                    what
                    "found an ellipsis outside of a sequence"
                    orig-stx
                    term)]
                  [(memq unaliased-sym all-nts)
                   (record-syncheck-use term prefix-sym)
                   (cond
                     [mismatch?
                      (values `(mismatch-name ,term (nt ,unaliased-prefix-stx))
                              '())]
                     [else
                      (record-binder term under under-mismatch-ellipsis)
                      (values `(name ,term (nt ,unaliased-prefix-stx))
                              (list (make-id/depth term (length under))))])]
                  [(memq unaliased-sym underscore-allowed)
                   (cond
                     [mismatch?
                      (values `(mismatch-name ,term ,unaliased-prefix-stx)
                              '())]
                     [else
                      (record-binder term under under-mismatch-ellipsis)
                      (values `(name ,term ,unaliased-prefix-stx)
                              (list (make-id/depth term (length under))))])]
                  [else
                   (raise-syntax-error
                    what
                    (format (string-append "before underscore must be either a"
                                           " non-terminal or a built-in pattern, found ~a in ~s")
                            prefix-sym (syntax-e term))
                    orig-stx 
                    term)])]
               [(eq? (syntax-e term) '...)
                (raise-syntax-error 
                 what
                 "found an ellipsis outside of a sequence"
                 orig-stx
                 term)]
               [(memq unaliased-sym all-nts)
                (record-syncheck-use term prefix-sym)
                (cond
                  [bind-names?
                   (record-binder term under under-mismatch-ellipsis)
                   (values `(name ,term (nt ,unaliased-sym))
                           (list (make-id/depth term (length under))))]
                  [else
                   (values `(nt ,unaliased-sym) '())])]
               [(memq (syntax-e term) underscore-allowed)
                (cond
                  [bind-names?
                   (record-binder term under under-mismatch-ellipsis)
                   (values `(name ,term ,term) (list (make-id/depth term (length under))))]
                  [else
                   (values term '())])]
               [(equal? (syntax-e term) rewrite-as-any-id)
                (values `(name ,rewrite-as-any-id any)
                        (list (make-id/depth term (length under))))]
               [else
                (values term '())]))]
          [(terms ...)
           (let ()
             (define terms-lst (syntax->list #'(terms ...)))
             (define (is-ellipsis? term)
               (and (identifier? term)
                    (regexp-match? #rx"^[.][.][.]" (symbol->string (syntax-e term)))))
             (when (and (pair? terms-lst) (is-ellipsis? (car terms-lst)))
               (raise-syntax-error what
                                   "ellipsis should not appear in the first position of a sequence"
                                   orig-stx 
                                   term))
             (define-values (updated-terms vars)
               (let t-loop ([terms terms-lst])
                 (cond
                   [(null? terms) (values '() '())]
                   [(null? (cdr terms))
                    (define-values (term vars) (loop (car terms) under under-mismatch-ellipsis))
                    (values (list term) vars)]
                   [(is-ellipsis? (cadr terms))
                    (when (and (pair? (cddr terms))
                               (is-ellipsis? (caddr terms)))
                      (raise-syntax-error what
                                          "two ellipses should not appear in a row"
                                          orig-stx
                                          (cadr terms)
                                          (list (caddr terms))))
                    (define ellipsis-pre-sym (syntax-e (cadr terms)))
                    (define ellipsis-pre-str (symbol->string ellipsis-pre-sym))
                    (define mismatch? (regexp-match? #rx"^[.][.][.]_!_" ellipsis-pre-str))
                    (define-values (ellipsis-str was-named-ellipsis?)
                      (cond
                        [mismatch?
                         (set! ellipsis-number (+ ellipsis-number 1))
                         (values (format "..._r~a" ellipsis-number) #f)]
                        [(regexp-match? #rx"^[.][.][.]_r" ellipsis-pre-str)
                         (values (string-append (substring ellipsis-pre-str 0 4)
                                                "r"
                                                (substring ellipsis-pre-str 
                                                           4
                                                           (string-length ellipsis-pre-str)))
                                 #t)]
                        [(regexp-match? #rx"^[.][.][.]_" ellipsis-pre-str) 
                         (values ellipsis-pre-str #t)]
                        [else 
                         (set! ellipsis-number (+ ellipsis-number 1))
                         (values (format "..._r~a" ellipsis-number) #f)]))
                    (define ellipsis-sym (string->symbol ellipsis-str))
                    (when was-named-ellipsis? 
                      (hash-set! original-repeat-names ellipsis-sym ellipsis-pre-sym))
                    (define ellipsis+name (datum->syntax
                                           (cadr terms)
                                           (string->symbol ellipsis-str)
                                           (cadr terms)))
                    (record-binder ellipsis+name under under-mismatch-ellipsis)
                    (define-values (fst-term fst-vars) 
                      (loop (car terms) 
                            (cons (syntax-e ellipsis+name) under)
                            (if mismatch?
                                (cons (syntax-e (cadr terms)) under-mismatch-ellipsis)
                                under-mismatch-ellipsis)))
                    (define-values (rst-terms rst-vars) (t-loop (cddr terms)))
                    (values (cons `(repeat ,fst-term ,ellipsis+name ,(if mismatch? (cadr terms) #f))
                                  rst-terms)
                            (append fst-vars
                                    (if was-named-ellipsis? 
                                        (list (make-id/depth (cadr terms) (length under)))
                                        '())
                                    rst-vars))]
                   [else
                    (define-values (fst-term fst-vars) 
                      (loop (car terms) under under-mismatch-ellipsis))
                    (define-values (rst-terms rst-vars) (t-loop (cdr terms)))
                    (values (cons fst-term rst-terms)
                            (append fst-vars rst-vars))])))
             (values `(list ,@updated-terms) vars))]
          [else
           (when (pair? (syntax-e term))
             (let loop ([term term])
               (cond
                 [(syntax? term) (loop (syntax-e term))]
                 [(pair? term) (loop (cdr term))]
                 [(null? term) (void)]
                 [#t
                  (raise-syntax-error what "dotted pairs not supported in patterns" orig-stx term)])))
           (values term '())])))
    
    (define closed-table
      (make-immutable-hasheq (hash-map assignments (λ (cls _) (cons cls (find cls assignments))))))
     
    (define repeat-id-counts (make-hash))

    (define ellipsis-normalized 
      (let loop ([pat term])
        (syntax-case pat (repeat)
          [(repeat sub-pat name mismatch-name)
           (let ()
             (define mapped-name (hash-ref closed-table (syntax-e #'name) #f))
             (define new-name (if mapped-name
                                  mapped-name
                                  (syntax-e #'name)))
             (hash-set! repeat-id-counts new-name (+ 1 (hash-ref repeat-id-counts new-name 0)))
             (let ([id (syntax-e #'mismatch-name)])
               (when id
                 (hash-set! repeat-id-counts id (+ 1 (hash-ref repeat-id-counts id 0)))))
             #`(repeat #,(loop #'sub-pat) #,new-name mismatch-name))]
          [(a ...)
           (let ()
             (define new (map loop (syntax->list #'(a ...))))
             (if (syntax? pat)
                 (datum->syntax pat new pat)
                 new))]
          [_ pat])))
    
    (define (raise-impossible-pattern-error pat1 pat2)
      (define (find-pat-var pat)
        (syntax-case pat (name)
          [(name id pat)
           (syntax-e #'id)]
          [_ #f]))
      (define pat-var1 (find-pat-var pat1))
      (define pat-var2 (find-pat-var pat1))
      (cond
        [(and pat-var1 pat-var2
              (not (equal? pat-var1 pat-var2)))
         (define all-ids (append (hash-ref var-locs-table pat-var1 '())
                                 (hash-ref var-locs-table pat-var2 '())))
         (raise-syntax-error 
          what 
          (format 
           (string-append "no terms match pattern;\n"
                          " ~a and ~a are together overly constrained")
           pat-var1 pat-var2)
          orig-stx
          (if (null? all-ids) #f (car all-ids))
          (if (null? all-ids) '() (cdr all-ids)))]
        [(or pat-var1 pat-var2)
         =>
         (λ (the-pat-var)
           (define all-ids (hash-ref var-locs-table the-pat-var '()))
           (raise-syntax-error 
            what 
            (format (string-append "no terms match pattern;\n"
                                   " ~a is overly constrained")
                    the-pat-var)
            orig-stx
            (if (null? all-ids) #f (car all-ids))
            (if (null? all-ids) '() (cdr all-ids))))]
        [else
         (raise-syntax-error
          what
          "no terms match pattern"
          orig-stx)]))
#|
    (printf "term\n") ((dynamic-require 'racket/pretty 'pretty-print)
                       (syntax->datum (datum->syntax #'here term)))
    (printf "norm\n") ((dynamic-require 'racket/pretty 'pretty-print)
                       (syntax->datum (datum->syntax #'here ellipsis-normalized)))
    (printf "repeat-id-counts ~s\n" repeat-id-counts)
|#
    
    ;; hash[(list symbol[match-id] symbol[mismatch-id]) -o> syntax[repeat pattern]]
    (define both-match-and-mismatch-id (make-hash))
    
    (define ellipsis-normalized/simplified 
      (let loop ([pat ellipsis-normalized])
        (syntax-case pat (repeat)
          [(repeat sub-pat name mismatch-name)
           (let ()
             (define final-match-repeat-name 
               (if (= 1 (hash-ref repeat-id-counts (syntax-e #'name)))
                   (hash-ref original-repeat-names (syntax-e #'name) #f)
                   #'name))
             (define final-mismatch-repeat-name
               (if (and (syntax-e #'mismatch-name)
                        (= 1 (hash-ref repeat-id-counts (syntax-e #'mismatch-name))))
                   #f
                   #'mismatch-name))
             (when (and (identifier? final-mismatch-repeat-name)
                        (identifier? final-match-repeat-name))
               (define key (list (syntax-e final-mismatch-repeat-name) 
                                 (syntax-e final-match-repeat-name)))
               (define already-bound (hash-ref both-match-and-mismatch-id key #f))
               (when already-bound
                 (raise-impossible-pattern-error already-bound #'sub-pat))
               (hash-set! both-match-and-mismatch-id key #'sub-pat))
             #`(repeat #,(loop #'sub-pat) 
                       #,final-match-repeat-name
                       #,final-mismatch-repeat-name))]
          [(a ...)
           (let ()
             (define new (map loop (syntax->list #'(a ...))))
             (if (syntax? pat)
                 (datum->syntax pat new pat)
                 new))]
          [_ pat])))
    
    (filter-duplicates what orig-stx names)

    (with-syntax ([(name/ellipses ...) (map build-dots names)]
                  [(name ...) (map id/depth-id names)]
                  [term ellipsis-normalized/simplified]
                  [void-stx void-stx])
      (when nt->hole
        (check-hole-sanity what #'term nt->hole orig-stx))
      #'(void-stx term (name ...) (name/ellipses ...))))

(define (break-out-underscore id)
  (define sym (syntax-e id))
  (define m (regexp-match #rx"^([^_]*)_(.*)$" (symbol->string sym)))
  (cond
    [m
     (define prefix (list-ref m 1))
     (define suffix (list-ref m 2))
     (values (string->symbol prefix) (string->symbol suffix))]
    [else
     (values sym #f)]))
                


;; check-hole-sanity : pat hash[sym -o> (or/c 0 1 'unknown)] -> (or/c 0 1 'unknown)
;; returns 'unknown if cannot figure out the answer (based on an 'unknown in the nt-map)
;; returns 0 if the pattern cannot produce a hole
;; returns 1 if the pattern produces a unique hole,
;; returns 'lots if it might produce any number of holes (0, 1, or more)
;; raises an error if there is inconsistency
  (define (check-hole-sanity who pattern nt-map stx-to-use-for-error-messages)
    (let loop ([pattern (syntax->datum pattern)]
               [local-stx pattern])
       (match-a-pattern pattern
         [`any 0]
         [`number 0]
         [`string 0]
         [`natural 0]
         [`integer 0]
         [`real 0]
         [`boolean 0]
         [`variable 0] 
         [`(variable-except ,vars ...) 0]
         [`(variable-prefix ,var) 0]
         [`variable-not-otherwise-mentioned 0]
         [`hole 1]
         [`(nt ,id) (hash-ref nt-map id)]
         [`(name ,name ,pat)
          (syntax-case local-stx ()
            [(_1 _2 sub-stx)
             (loop pat #'sub-stx)])]
         [`(mismatch-name ,name ,pat)
          (syntax-case local-stx ()
            [(_1 _2 sub-stx)
             (loop pat #'sub-stx)])]
         [`(in-hole ,context ,contractum)
          (syntax-case local-stx ()
            [(_ context-stx contractum-stx)
             (let ()
               (define ctxt (loop context #'context-stx))
               (unless (or (equal? ctxt 1) (equal? ctxt 'unknown))
                 (raise-syntax-error
                  who
                  (string-append
                   "in-hole's first argument is expected to match exactly one hole"
                   (cond
                     [(equal? ctxt 0)
                      ", but it cannot match a hole"]
                     [(equal? ctxt 'lots)
                      ", but it may match a hole many different ways"]))
                  stx-to-use-for-error-messages))
               (loop contractum #'contractum-stx))])]
         [`(hide-hole ,pat)
          (syntax-case local-stx ()
            [(_ pat-stx)
             (let ()
               (define pat-resp (loop pat #'pat-stx))
               (unless (or (equal? pat-resp 1) (equal? pat-resp 'unknown))
                 (raise-syntax-error who "hide-hole's argument is expected to have a hole"
                                     stx-to-use-for-error-messages))
               0)])]
         [`(side-condition ,pat ,condition ,expr)
          (syntax-case local-stx ()
            [(_ pat-stx _2 _3)
             (loop pat #'pat-stx)])]
         [`(cross ,nt) 1]
         [`(list ,pats ...)
          (syntax-case local-stx ()
            [(_ pat-stx ...)
             (let l-loop ([pats pats]
                          [pat-stxes (syntax->list #'(pat-stx ...))]
                          [all-zeros? #t]
                          [number-of-ones 0]
                          [all-known? #t])
               (cond
                 [(null? pats)
                  (cond
                    [all-zeros? 0]
                    [(>= number-of-ones 2) 'lots]
                    [(and (= number-of-ones 1) all-known?) 1]
                    [else 'unknown])]
                 [else
                  (match (car pats)
                    [`(repeat ,pat ,name ,mname)
                     (syntax-case (car pat-stxes) ()
                       [(repeat pat-stx _1 _2)
                        (let ()
                          (define this-one (loop pat #'pat-stx))
                          (l-loop (cdr pats) (cdr pat-stxes)
                                  (and all-zeros? (equal? this-one 0))
                                  (if (equal? this-one 1) +inf.0 number-of-ones)
                                  (and all-known? (not (equal? this-one 'unknown)))))])]
                    [pat
                     (let ()
                       (define this-one (loop pat (car pat-stxes)))
                       (l-loop (cdr pats)
                               (cdr pat-stxes)
                               (and all-zeros? (equal? this-one 0))
                               (if (equal? this-one 1) (+ number-of-ones 1) number-of-ones)
                               (and all-known? (not (equal? this-one 'unknown)))))])]))])]
         [(? (compose not pair?)) 0])))

  (define-struct id/depth (id depth))
  
  ;; extract-names : syntax syntax -> 
  ;;   (values (listof syntax)
  ;;           (listof syntax[x | (x ...) | ((x ...) ...) | ...]))
  ;; this function is obsolete and uses of it are suspect. Things should be using 
  ;; rewrite-side-conditions/check-errs instead
  (define (extract-names all-nts what bind-names? orig-stx [mode 'rhs-only])
    (let* ([dups
            (let loop ([stx orig-stx]
                       [names null]
                       [depth 0])
              (syntax-case stx (name in-hole side-condition cross nt)
                [(name sym pat)
                 (identifier? (syntax sym))
                 (loop (syntax pat) 
                       (cons (make-id/depth (syntax sym) depth) names)
                       depth)]
                [(in-hole pat1 pat2)
                 (loop (syntax pat1)
                       (loop (syntax pat2) names depth)
                       depth)]
                [(side-condition pat . rest)
                 (loop (syntax pat) names depth)]
                [(cross _) names]
                [(pat ...)
                 (let i-loop ([pats (syntax->list (syntax (pat ...)))]
                              [names names])
                   (cond
                     [(null? pats) names]
                     [else 
                      (if (or (null? (cdr pats))
                              (not (identifier? (cadr pats)))
                              (not (or (free-identifier=? (quote-syntax ...)
                                                          (cadr pats))
                                       (let ([inside (syntax-e (cadr pats))])
                                         (regexp-match #rx"^\\.\\.\\._" (symbol->string inside))))))
                          (i-loop (cdr pats)
                                  (loop (car pats) names depth))
                          (i-loop (cdr pats)
                                  (loop (car pats) names (+ depth 1))))]))]
                [x
                 (and (identifier? (syntax x))
                      ((case mode
                         [(rhs-only) binds-in-right-hand-side?]
                         [(binds-anywhere) binds?])
                       all-nts bind-names? (syntax x)))
                 (cons (make-id/depth (syntax x) depth) names)]
                [else names]))]
           [no-dups (filter-duplicates what orig-stx dups)])
      (values (map id/depth-id no-dups)
              (map build-dots no-dups))))
  
  ;; build-dots : id/depth -> syntax[x | (x ...) | ((x ...) ...) | ...]
  (define (build-dots id/depth)
    (let loop ([depth (id/depth-depth id/depth)])
      (cond
        [(zero? depth) (id/depth-id id/depth)]
        [else (with-syntax ([rest (loop (- depth 1))]
                            [dots (quote-syntax ...)])
                (syntax (rest dots)))])))
  
  (define (binds? nts bind-names? x)
    (and (not (eq? '_ (syntax-e x)))
         (or (and bind-names? (memq (syntax-e x) nts))
             (and bind-names? (memq (syntax-e x) underscore-allowed))
             (regexp-match #rx"_" (symbol->string (syntax-e x))))))
  
  (define (binds-in-right-hand-side? nts bind-names? x)
    (and (binds? nts bind-names? x)
         (let ([str (symbol->string (syntax-e x))])
           (and (not (regexp-match #rx"^\\.\\.\\._" str))
                (not (regexp-match #rx"_!_" str))))))
  
  (define (raise-ellipsis-depth-error what 
                                      one-binder 
                                      one-depth 
                                      another-binder 
                                      another-depth
                                      [orig-stx #f])
    (raise-syntax-error
     what
     (format "found the same binder, ~s, at different depths, ~a and ~a"
             (syntax->datum one-binder)
             one-depth
             another-depth)
     orig-stx
     another-binder
     (list one-binder)))
  
  (define (filter-duplicates what orig-stx dups)
    (let loop ([dups dups])
      (cond
        [(null? dups) null]
        [else 
         (cons
          (car dups)
          (filter (lambda (x) 
                    (let ([same-id? (free-identifier=? (id/depth-id x)
                                                       (id/depth-id (car dups)))])
                      (when same-id?
                        (unless (equal? (id/depth-depth x)
                                        (id/depth-depth (car dups)))
                          (raise-ellipsis-depth-error
                           what 
                           (id/depth-id x) (id/depth-depth x)
                           (id/depth-id (car dups)) (id/depth-depth (car dups))
                           orig-stx)))
                      (not same-id?)))
                  (loop (cdr dups))))])))

  (define (bind-pattern-names err-name names/ellipses vals body)
    (with-syntax ([(names/ellipsis ...) names/ellipses]
                  [(val ...) vals])
      #`(term-let/error-name
         #,err-name
         ([names/ellipsis val] ...) 
         #,body)))
