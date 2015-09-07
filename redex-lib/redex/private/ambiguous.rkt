#lang 2d racket/base

(require racket/set
         racket/match
         racket/contract
         "match-a-pattern.rkt"
         "lang-struct.rkt"
         "build-nt-property.rkt"
         2d/match)

(provide 
 (contract-out
  
  ;; expects the lang, literals, and list-ht fields of the clang to be filled in.
  [build-ambiguity-cache (-> compiled-lang? hash?)]
  
  [ambiguous-pattern? (-> any/c hash? boolean?)]))

;; provided only for the test suite
(provide build-can-match-var-ht
         overlapping-patterns? 
         build-overlapping-productions-table
         konsts
         prefixes
         build-ambiguous-ht)

(define (build-ambiguity-cache clang)
  (define can-match-var-ht (build-can-match-var-ht clang))
  (define overlapping-productions-ht (build-overlapping-productions-table clang))
  (define ambiguous-ht (build-ambiguous-ht clang overlapping-productions-ht))
  ambiguous-ht)
  
;; returns #f when they definitely do NOT overlap
;; returns #t when the might overlap 
;;    or they might not and we cannot tell
(define (overlapping-patterns? u t vari clang)
  
  ;; this match-a-pattern is here only to catch changes in the pattern
  ;; language that would affect the big 2d cond below.
  (void
   (match-a-pattern u [`any 1] [`number 1] [`string 1] [`natural 1] [`integer 1] [`real 1] 
                    [`boolean 1] [`variable 1] [`(variable-except ,vars ...) 1]
                    [`(variable-prefix ,var) 1] [`variable-not-otherwise-mentioned 1] [`hole 1]
                    [`(nt ,id) 1] [`(name ,name ,pat) 1] [`(mismatch-name ,name ,pat) 1] 
                    [`(in-hole ,context ,contractum) 1] [`(hide-hole ,pat) 1]
                    [`(side-condition ,pat ,condition ,expr) 1]
                    [`(cross ,nt) 1] [`(list ,pats ...) 1] [(? (compose not pair?)) 1]))
  
  (define (r a b) (overlapping-patterns? a b vari clang))
  (define (not-pair? x) (not (pair? x)))
  
  
  #2dmatch
  ╔═══════════════════╦═════════════════╦═════════════╦════════════════╦══════════════╦═════╦═════════╦════════════╦═══════════════╦═══════════════════╦═════════════╦══════════════════╦════════════╦═══════════════════╦═════════════╗
  ║            u      ║ `any            ║ (? num-pat?)║ (? base-pat?)  ║ (? var-pat?) ║`hole║`(nt ,id)║`(name      ║`(mismatch-name║ `(in-hole         ║ `(hide-hole ║ `(side-condition ║`(cross ,nt)║ `(list ,u-ps ...) ║(? not-pair?)║
  ║                   ║                 ║             ║                ║              ║     ║         ║  ,name     ║  ,name ,u2)   ║   ,context        ║   ,pat)     ║   ,pat ,cond     ║            ║                   ║             ║
  ║  t                ║                 ║             ║                ║              ║     ║         ║  ,u2)      ║               ║   ,contractum)    ║             ║   ,expr)         ║            ║                   ║             ║
  ╠═══════════════════╬═════════════════╩═════════════╩════════════════╩══════════════╩═════╩═════════╩════════════╩═══════════════╩═══════════════════╩═════════════╩══════════════════╩════════════╩═══════════════════╩═════════════╣
  ║`any               ║                                                                                                         #t                                                                                                     ║
  ╠═══════════════════╬═════════════════╦═════════════╦════════════════╦══════════════╦═════╦═════════╦════════════╦═══════════════╦═══════════════════╦═════════════╦══════════════════╦════════════╦═══════════════════╦═════════════╣
  ║  (? num-pat?)     ║                 ║     #t      ║      #f        ║      #f      ║ #f  ║   #t    ║ (r u2 t)   ║   (r u2 t)    ║ (r t contractum)  ║  (r t pat)  ║    (r t pat)     ║     #t     ║         #f        ║ (number? u) ║
  ╠═══════════════════╣                 ╚═════════════╬════════════════╬══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  (? base-pat?)    ║                               ║  (equal? t u)  ║      #f      ║ #f  ║   #t    ║            ║               ║                   ║             ║                  ║            ║                   ║ (bmatches?  ║
  ║                   ║                               ║                ║              ║     ║         ║            ║               ║                   ║             ║                  ║            ║         #f        ║  t u)       ║
  ║                   ║                               ║                ║              ║     ║         ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ╠═══════════════════╣                               ╚════════════════╬══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  (? var-pat?)     ║                                                ║(v-overlap? t ║ #f  ║(v-nt    ║            ║               ║                   ║             ║                  ║            ║                   ║ (symbol? u) ║
  ║                   ║                                                ║            u)║     ║ t id    ║            ║               ║                   ║             ║                  ║            ║         #f        ║             ║
  ║                   ║                                                ║              ║     ║ vari)   ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ╠═══════════════════╣                                                ╚══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║     `hole         ║                                                               ║ #t  ║    #t   ║            ║               ║                   ║             ║                  ║            ║         #t        ║    #t       ║
  ╠═══════════════════╣                                                               ╚═════╬═════════╣            ║               ╠═══════════════════╣             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  `(nt ,t-id)      ║                                                                     ║   #t    ║            ║               ║         #t        ║             ║                  ║            ║(nt-can-be-list?   ║(nmatches?   ║
  ║                   ║                                                                     ║         ║            ║               ║                   ║             ║                  ║            ║ t-id clang)       ║ t-id u vari)║
  ╠═══════════════════╣                                                                     ╚═════════╬════════════╣               ╠═══════════════════╩═════════════╩══════════════════╩════════════╩═══════════════════╩═════════════╣
  ║`(name ,t-name     ║                                                                               ║ (r u2 t2)  ║               ║                                             (r u t2)                                              ║
  ║       ,t2)        ║                                                                               ║            ║               ║                                                                                                   ║
  ╠═══════════════════╣                                                                               ╚════════════╣               ╠═══════════════════════════════════════════════════════════════════════════════════════════════════╣
  ║`(mismatch-name    ║                                                                                            ║               ║                                             (r u t2)                                              ║
  ║  ,name ,t2)       ║                                                                                            ║               ║                                                                                                   ║
  ╠═══════════════════╣                                                                                            ╚═══════════════╬═══════════════════╦═════════════╦══════════════════╦════════════╦═════════════════════════════════╣
  ║`(in-hole          ║                                                                                                            ║                   ║  (r t pat)  ║    (r t pat)     ║     #t     ║                                 ║
  ║  ,t-context       ║                                                                                                            ║         #t        ║             ║                  ║            ║                #t               ║
  ║  ,t-contractum)   ║                                                                                                            ║                   ║             ║                  ║            ║                                 ║
  ╠═══════════════════╣                                                                                                            ╚═══════════════════╣             ║                  ║            ╠═════════════════════════════════╣
  ║`(hide-hole ,t2)   ║                   (r t u)                                                                                                      ║             ║                  ║            ║             (r u t2)            ║
  ║                   ║                                                                                                                                ║             ║                  ║            ║                                 ║
  ╠═══════════════════╣                                                                                                                                ╚═════════════╣                  ║            ╠═════════════════════════════════╣
  ║`(side-condition   ║                                                                                                                                              ║                  ║            ║             (r u t2)            ║
  ║  ,t2 ,t-cond      ║                                                                                                                                              ║                  ║            ║                                 ║
  ║  ,t-expr)         ║                                                                                                                                              ║                  ║            ║                                 ║
  ╠═══════════════════╣                                                                                                                                              ╚══════════════════╣            ╠═══════════════════╦═════════════╣
  ║ `(cross ,t-nt)    ║                                                                                                                                                                 ║            ║         #t        ║     #t      ║
  ╠═══════════════════╣                                                                                                                                                                 ║            ╠═══════════════════╬═════════════╣
  ║ `(list ,t-ps ...) ║                                                                                                                                                                 ║            ║ (olist u-ps t-ps  ║             ║
  ║                   ║                                                                                                                                                                 ║            ║        vari       ║     #f      ║
  ║                   ║                                                                                                                                                                 ║            ║        clang)     ║             ║
  ╠═══════════════════╣                                                                                                                                                                 ╚════════════╩═══════════════════╬═════════════╣
  ║ (? not-pair?)     ║                                                                                                                                                                                                  ║(equal? t u) ║
  ╚═══════════════════╩══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╩═════════════╝)

(define (v-nt v-pat nt vari)
  (define nt-info (hash-ref vari nt))
  (cond
    [(equal? nt-info #t) #t]
    [(equal? nt-info #f) #f]
    [(konsts? nt-info) #t]
    [(prefixes? nt-info)
     (match v-pat
       [`(variable-prefix ,prefix)
        (define prefixes-as-lists-of-chars
          (for/list ([s (in-set (prefixes-prefixes nt-info))])
            (string->list (symbol->string s))))
        (let loop ([prefixes prefixes-as-lists-of-chars]
                   [prefix (string->list (symbol->string prefix))])
          (cond
            [(ormap null? prefixes) #t]
            [(null? prefix) #t]
            [else
             (define new-prefixes
               (for/list ([a-prefix (in-list prefixes)]
                          #:when (equal? (car a-prefix) (car prefix)))
                 (cdr a-prefix)))
             (cond
               [(null? new-prefixes) #f]
               [else (loop new-prefixes (cdr prefix))])]))]
       [_ #t])]))

;; returns #f when the nt definitely does NOT match a list
;; returns #t when the nt might match a list
(define (nt-can-be-list? nt-id clang)
  ;; if the list-ht maps the nt to the empty list,
  ;; then we know there is no way that this nt can
  ;; match any lists.
  (not (null? (hash-ref (compiled-lang-list-ht clang) nt-id))))

(define (v-overlap? t u)
  (match* (t u)
    [(`(variable-prefix ,t-prefix) `(variable-prefix ,u-prefix))
     (define t-str (symbol->string t-prefix))
     (define u-str (symbol->string u-prefix))
     (define (is-prefix? a b) (regexp-match? (format "^~a" (regexp-quote a)) b))
     (or (is-prefix? u-str t-str)
         (is-prefix? t-str u-str))]
    [(_ _) #t]))

(define (count-repeats pats)
  (for/sum ([pat (in-list pats)]
            #:when (and (pair? pat) (equal? (car pat) 'repeat)))
    1))


;; olist : (listof lpat) (listof lpat) var-info-hash clang -> boolean
;; result is #t if the patterns might overlap when in a `(list ...)
;; and #f if they will definitely not overlap
(define (olist u-pats t-pats vari clang)
  (define u-repeats (count-repeats u-pats))
  (define t-repeats (count-repeats t-pats))
  (cond
    [(and (= 0 u-repeats)
          (= 0 t-repeats))
     (olist-0-repeats u-pats t-pats vari clang)]
    [(and (= 1 u-repeats)
          (= 0 t-repeats))
     (olist-1-repeat u-pats t-pats vari clang)]
    [(and (= 0 u-repeats)
          (= 1 t-repeats))
     (olist-1-repeat t-pats u-pats vari clang)]
    [else #t]))

;; neither u-pats nor t-pats contains a repeat
(define (olist-0-repeats u-pats t-pats vari clang)
  (define u-len (length u-pats))
  (define t-len (length t-pats))
  (cond
    [(= u-len t-len)
     (for/and ([u-pat (in-list u-pats)]
               [t-pat (in-list t-pats)])
       (overlapping-patterns? u-pat t-pat vari clang))]
    [else #f]))

;; u-pats contains a repeat and t-pats does not.
(define (olist-1-repeat u-pats t-pats vari clang)
  (define u-len (length u-pats))
  (define t-len (length t-pats))
  (define u-min (- u-len 1)) ;; length of the shortest list that u can match
  (cond
    [(<= u-min t-len)
     (olist-0-repeats (expand-repeat u-pats t-len)
                      t-pats vari clang)]
    [else #f]))

(define (expand-repeat lpats i)
  (let loop ([lpats lpats])
    (cond
      [(null? lpats) (error 'expand-repeat "no repeat")]
      [else
       (match (car lpats)
         [`(repeat ,lpat ,name ,mname)
          (append (build-list i (λ (_) lpat))
                  (cdr lpats))]
         [_ (cons (car lpats) (loop (cdr lpats)))])])))

(define (num-pat? t)
  (match-a-pattern
   t
   [`any #f] [`number #t] [`string #f] [`natural #t] [`integer #t] [`real #t] 
   [`boolean #f] [`variable #f] [`(variable-except ,vars ...) #f]
   [`(variable-prefix ,var) #f] [`variable-not-otherwise-mentioned #f] [`hole #f]
   [`(nt ,id) #f] [`(name ,name ,pat) #f] [`(mismatch-name ,name ,pat) #f] 
   [`(in-hole ,context ,contractum) #f] [`(hide-hole ,pat) #f]
   [`(side-condition ,pat ,condition ,expr) #f]
   [`(cross ,nt) #f] [`(list ,pats ...) #f] [(? (compose not pair?)) #f]))

(define (var-pat? t)
  (match-a-pattern
   t
   [`any #f] [`number #f] [`string #f] [`natural #f] [`integer #f] [`real #f] 
   [`boolean #f] [`variable #t] [`(variable-except ,vars ...) #t]
   [`(variable-prefix ,var) #t] [`variable-not-otherwise-mentioned #t] [`hole #f]
   [`(nt ,id) #f] [`(name ,name ,pat) #f] [`(mismatch-name ,name ,pat) #f] 
   [`(in-hole ,context ,contractum) #f] [`(hide-hole ,pat) #f]
   [`(side-condition ,pat ,condition ,expr) #f]
   [`(cross ,nt) #f] [`(list ,pats ...) #f] [(? (compose not pair?)) #f]))

(define (base-pat? t)
  ;; patterns for base type that aren't numbers
  ;; they are expected to all be disjoint and 
  ;; not overlap with numbers or symbols at all.
  (match-a-pattern
   t
   [`any #f] [`number #f] [`string #t] [`natural #f] [`integer #f] [`real #f] 
   [`boolean #t] [`variable #f] [`(variable-except ,vars ...) #f]
   [`(variable-prefix ,var) #f] [`variable-not-otherwise-mentioned #f] [`hole #f]
   [`(nt ,id) #f] [`(name ,name ,pat) #f] [`(mismatch-name ,name ,pat) #f] 
   [`(in-hole ,context ,contractum) #f] [`(hide-hole ,pat) #f]
   [`(side-condition ,pat ,condition ,expr) #f]
   [`(cross ,nt) #f] [`(list ,pats ...) #f] [(? (compose not pair?)) #f]))

(define (bmatches? b v)
  (match b
    [`string (string? v)]
    [`boolean (boolean? b)]))

;; nmatches : symbol constant -> vari
;; returns #f when the non-terminal is known NOT to
;; match the non-terminal
;; return #t when the non-terminal might match the constant
(define (nmatches? nt v vari)
  (cond
    [(symbol? v)
     (define nt-info (hash-ref vari nt))
     (cond
       [(equal? nt-info #t) #t]
       [(equal? nt-info #f) #f]
       [(konsts? nt-info)
        (not (set-member? (konsts-syms nt-info) v))]
       [(prefixes? nt-info)
        (for/or ([prefix (in-set (prefixes-prefixes nt-info))])
          (regexp-match? (format "^~a" (regexp-quote (symbol->string prefix)))
                         (symbol->string v)))])]
    [else #t]))

(define (build-overlapping-productions-table clang)
  (define overlapping-nt-table (make-hash))
  (define vari (build-can-match-var-ht clang))
  (for ([nt (in-list (compiled-lang-lang clang))])
    (define has-overlap?
      (let loop ([rhses (nt-rhs nt)])
        (cond
          [(null? rhses) #f]
          [else 
           (define first-rhs-pat (rhs-pattern (car rhses)))
           (or (for/or ([second-rhs (in-list (cdr rhses))])
                 (overlapping-patterns? first-rhs-pat
                                        (rhs-pattern second-rhs)
                                        vari clang))
               (loop (cdr rhses)))])))
    (hash-set! overlapping-nt-table (nt-name nt) has-overlap?))
  overlapping-nt-table)
  
(struct konsts (syms) #:prefab)
(struct prefixes (prefixes) #:prefab)
(define (build-can-match-var-ht clang)
  #|


lattice:

      #t   -- all variables
     /  \
    /    \
 konsts  prefixes
    \    /
     \  /
      #f  -- no variables

The middle piece of the lattice describes two different
states. If it is a konsts, then the non-terminal can match
any symbol except the ones listed. If it is a prefixes,
then the non-terminal can match any variable with one
of the prefixes.

konsts and prefixes must not have empty sets in them.

|#
  (define nothing #f)
  (build-nt-property 
   (compiled-lang-lang clang)
   (lambda (pattern ht)
     (let loop ([pattern pattern])
       (match-a-pattern pattern
         [`any #t]
         [`number nothing]
         [`string nothing]
         [`natural nothing]
         [`integer nothing]
         [`real nothing]
         [`boolean nothing]
         [`variable #t] 
         [`(variable-except ,vars ...) (konsts (apply set vars))]
         [`(variable-prefix ,var) (prefixes (set var))]
         [`variable-not-otherwise-mentioned 
          (konsts (apply set (compiled-lang-literals clang)))]
         [`hole #f]
         [`(nt ,id) (hash-ref ht id)]
         [`(name ,name ,pat) (loop pat)]
         [`(mismatch-name ,name ,pat) (loop pat)]
         [`(in-hole ,context ,contractum) (loop contractum)]
         [`(hide-hole ,pat) (loop pat)]
         [`(side-condition ,pat ,condition ,expr) (loop pat)]
         [`(cross ,nt) #t]
         [`(list ,pats ...) nothing]
         [(? (compose not pair?))
          (cond
            [(symbol? pattern)
             ;; it can match only that one symbol,
             ;; but our nearest approximation is top
             #t]
            [else nothing])])))
   nothing
   (λ (x y) 
     (match* (x y)
       [((konsts k1) (konsts k2))
        (define i (set-intersect k1 k2))
        (if (set-empty? i)
            #t
            (konsts i))]
       [((prefixes p1) (prefixes p2))
        (prefixes (set-union p1 p2))]
       [(#f x) x]
       [(x #f) x]
       [(_ _) #t]))))

(define (ambiguous-pattern? pattern non-terminal-ambiguous-ht)
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
       [`hole #f]
       [`(nt ,id) (hash-ref non-terminal-ambiguous-ht id)]
       [`(name ,name ,pat) (loop pat)]
       [`(mismatch-name ,name ,pat) (loop pat)]
       [`(in-hole ,context ,contractum) #t]
       [`(hide-hole ,pat) (loop pat)]
       [`(side-condition ,pat ,condition ,expr) (loop pat)]
       [`(cross ,nt) #t]
       [`(list ,pats ...) 
        (define number-of-repeats 0)
        (or (for/or ([lpat (in-list pats)])
              (match lpat
                [`(repeat ,pat ,name ,mname) 
                 (set! number-of-repeats (+ number-of-repeats 1))
                 (loop pat)]
                [pat (loop pat)]))
            (number-of-repeats . >= . 2))]
       [(? (compose not pair?)) #f])))

(define (build-ambiguous-ht clang overlapping-productions-ht)
  (build-nt-property 
   (compiled-lang-lang clang)
   ambiguous-pattern?
   (λ (nt)
     (cond
       [nt (hash-ref overlapping-productions-ht nt)]
       [else #f]))
   (λ (x y) (or x y))))

