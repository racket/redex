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
  [build-ambiguity-cache (-> compiled-lang? ambiguity-cache?)]
  
  [ambiguous-pattern? (-> any/c ambiguity-cache? boolean?)]
  [ambiguity-cache? (-> any/c boolean?)]))

(struct ambiguity-cache (ht))

(define (build-ambiguity-cache clang)
  (define overlapping-productions-ht (build-overlapping-productions-table clang))
  (define ambiguous-ht (build-ambiguous-ht clang overlapping-productions-ht))
  (ambiguity-cache ambiguous-ht))
  
;; returns #f when they definitely do NOT overlap
;; returns #t when the might overlap 
;;    or they might not and we cannot tell
(define (overlapping-patterns? u t info clang)
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
  
  (define (r a b) (overlapping-patterns? a b info clang))
  (define (not-pair? x) (not (pair? x)))
  
  #2dmatch
  ╔═══════════════════╦═════════════════╦═════════════╦════════════════╦══════════════╦═════╦═════════╦════════════╦═══════════════╦═══════════════════╦═════════════╦══════════════════╦════════════╦═══════════════════╦═════════════╗
  ║            u      ║ `any            ║ (? num-pat?)║ (? base-pat?)  ║ (? var-pat?) ║`hole║`(nt ,id)║`(name      ║`(mismatch-name║ `(in-hole         ║ `(hide-hole ║ `(side-condition ║`(cross ,nt)║ `(list ,u-ps ...) ║(? not-pair?)║
  ║                   ║                 ║             ║                ║              ║     ║         ║  ,name     ║  ,name ,u2)   ║   ,context        ║   ,pat)     ║   ,pat ,cond     ║            ║                   ║             ║
  ║  t                ║                 ║             ║                ║              ║     ║         ║  ,u2)      ║               ║   ,contractum)    ║             ║   ,expr)         ║            ║                   ║             ║
  ╠═══════════════════╬═════════════════╩═════════════╩════════════════╩══════════════╩═════╩═════════╩════════════╩═══════════════╩═══════════════════╩═════════════╩══════════════════╩════════════╩═══════════════════╩═════════════╣
  ║`any               ║                                                                                                         #t                                                                                                     ║
  ╠═══════════════════╬═════════════════╦═════════════╦════════════════╦══════════════╦═════╦═════════╦════════════╦═══════════════╦═══════════════════╦═════════════╦══════════════════╦════════════╦═══════════════════╦═════════════╣
  ║  (? num-pat?)     ║                 ║     #t      ║      #f        ║      #f      ║ #f  ║(n-nt    ║ (r u2 t)   ║   (r u2 t)    ║ (r t contractum)  ║  (r t pat)  ║    (r t pat)     ║     #t     ║         #f        ║ (number? u) ║
  ║                   ║                 ║             ║                ║              ║     ║ t id    ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ║                   ║                 ║             ║                ║              ║     ║ info)   ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ╠═══════════════════╣                 ╚═════════════╬════════════════╬══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  (? base-pat?)    ║                               ║  (equal? t u)  ║      #f      ║ #f  ║   #t    ║            ║               ║                   ║             ║                  ║            ║                   ║ (bmatches?  ║
  ║                   ║                               ║                ║              ║     ║         ║            ║               ║                   ║             ║                  ║            ║         #f        ║  t u)       ║
  ║                   ║                               ║                ║              ║     ║         ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ╠═══════════════════╣                               ╚════════════════╬══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  (? var-pat?)     ║                                                ║(v-overlap? t ║ #f  ║(v-nt    ║            ║               ║                   ║             ║                  ║            ║                   ║ (vmatches?  ║
  ║                   ║                                                ║            u)║     ║ t id    ║            ║               ║                   ║             ║                  ║            ║         #f        ║  t u clang) ║
  ║                   ║                                                ║              ║     ║ info)   ║            ║               ║                   ║             ║                  ║            ║                   ║             ║
  ╠═══════════════════╣                                                ╚══════════════╬═════╬═════════╣            ║               ║                   ║             ║                  ║            ╠═══════════════════╬═════════════╣
  ║     `hole         ║                                                               ║ #t  ║   #t    ║            ║               ║                   ║             ║                  ║            ║         #t        ║    #t       ║
  ╠═══════════════════╣                                                               ╚═════╬═════════╣            ║               ╠═══════════════════╣             ║                  ║            ╠═══════════════════╬═════════════╣
  ║  `(nt ,t-id)      ║                                                                     ║(nt-nt   ║            ║               ║         #t        ║             ║                  ║            ║(nt-matches-list?  ║(nmatches?   ║
  ║                   ║                                                                     ║ t-id id ║            ║               ║                   ║             ║                  ║            ║ t-id clang        ║ t-id u info)║
  ║                   ║                                                                     ║ info)   ║            ║               ║                   ║             ║                  ║            ║ u-ps info)        ║             ║
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
  ╠═══════════════════╣                                                                                                                                                                 ╚════════════╬═══════════════════╬═════════════╣
  ║ `(list ,t-ps ...) ║                                                                                                                                                                              ║ (olist u-ps t-ps  ║             ║
  ║                   ║                                                                                                                                                                              ║        info       ║     #f      ║
  ║                   ║                                                                                                                                                                              ║        clang)     ║             ║
  ╠═══════════════════╣                                                                                                                                                                              ╚═══════════════════╬═════════════╣
  ║ (? not-pair?)     ║                                                                                                                                                                                                  ║(equal? t u) ║
  ╚═══════════════════╩══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╩═════════════╝)

(define (nt-nt nt1 nt2 info)
  (match* ((hash-ref info nt1) (hash-ref info nt2))
    [((lp sym1 num1 bool1 str1 list1 hole?1)
      (lp sym2 num2 bool2 str2 list2 hole?2))
     (not (and (disjoint-sym sym1 sym2)
               (disjoint-num num1 num2)
               (disjoint-bool bool1 bool2)
               (disjoint-list list1 list2)
               (disjoint-hole hole?1 hole?2)))]
    [(_ _) #t]))
 
(define (n-nt n-pat nt info)
  (match (hash-ref info nt)
    [`any #t]
    [`bot #f]
    [(lp sym num bool str list hole?)
     (not (equal? num (num-konsts (set))))]))
  
(define (v-nt v-pat nt info)
  (match (hash-ref info nt)
    [`any #t]
    [`bot #f]
    [(lp sym num bool str list hole?)
     (match sym
       [`symbol #t]
       [`bot #f]
       [(var-konsts _) #t]
       [(prefixes+literals the-prefixes-set the-literal-set)
        (match v-pat
          [`(variable-prefix ,prefix)
           (define prefixes-as-lists-of-chars
             (for/list ([s (in-set the-prefixes-set)])
               (string->list (symbol->string s))))
           (or (for/or ([literal (in-set the-literal-set)])
                 (is-prefix? (symbol->string prefix) (symbol->string literal)))
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
                      [else (loop new-prefixes (cdr prefix))])])))]
          [_ #t])])]))

;; returns #t when the nt might match the list whose patterns are given by u-ps
(define (nt-matches-list? nt-id clang u-ps info)
  (match (hash-ref info nt-id)
    [`any #t]
    [`bot #f]
    [(lp sym num bool str list hole?)
     (match list
       [`list #t]
       [(list-lp fixed-sizes at-least-size)
        (define repeat?
          (for/or ([u-p (in-list u-ps)])
            (match u-p
              [`(repeat ,_ ...) #t]
              [_ #f])))
        (cond
          [repeat? #t]
          [else (set-member? fixed-sizes (length u-ps))])]
       [`bot #f])]))

(define (v-overlap? t u)
  (match* (t u)
    [(`(variable-prefix ,t-prefix) `(variable-prefix ,u-prefix))
     (define t-str (symbol->string t-prefix))
     (define u-str (symbol->string u-prefix))
     (or (is-prefix? u-str t-str)
         (is-prefix? t-str u-str))]
    [(_ _) #t]))

(define (is-prefix? a b) (regexp-match? (format "^~a" (regexp-quote a)) b))

(define (vmatches? t u clang)
  (and (symbol? u)
       (match t
         [`variable #t]
         [`(variable-except ,vars ...) (not (member u vars))]
         [`(variable-prefix ,var)
          (is-prefix? (symbol->string var) (symbol->string u))]
         [`variable-not-otherwise-mentioned
          (not (member u (compiled-lang-literals clang)))])))

(define (count-repeats pats)
  (for/sum ([pat (in-list pats)]
            #:when (and (pair? pat) (equal? (car pat) 'repeat)))
    1))


;; olist : (listof lpat) (listof lpat) info clang -> boolean
;; result is #t if the patterns might overlap when in a `(list ...)
;; and #f if they will definitely not overlap
(define (olist u-pats t-pats info clang)
  (define u-repeats (count-repeats u-pats))
  (define t-repeats (count-repeats t-pats))
  (cond
    [(and (= 0 u-repeats)
          (= 0 t-repeats))
     (olist-0-repeats u-pats t-pats info clang)]
    [(and (= 1 u-repeats)
          (= 0 t-repeats))
     (olist-1-repeat u-pats t-pats info clang)]
    [(and (= 0 u-repeats)
          (= 1 t-repeats))
     (olist-1-repeat t-pats u-pats info clang)]
    [else #t]))

;; neither u-pats nor t-pats contains a repeat
(define (olist-0-repeats u-pats t-pats info clang)
  (define u-len (length u-pats))
  (define t-len (length t-pats))
  (cond
    [(= u-len t-len)
     (for/and ([u-pat (in-list u-pats)]
               [t-pat (in-list t-pats)])
       (overlapping-patterns? u-pat t-pat info clang))]
    [else #f]))

;; u-pats contains a repeat and t-pats does not.
(define (olist-1-repeat u-pats t-pats info clang)
  (define u-len (length u-pats))
  (define t-len (length t-pats))
  (define u-min (- u-len 1)) ;; length of the shortest list that u can match
  (cond
    [(<= u-min t-len)
     (olist-0-repeats (expand-repeat u-pats t-len)
                      t-pats info clang)]
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
;; match the constant
;; return #t when the non-terminal might match the constant
(define (nmatches? nt v info)
  (match (hash-ref info nt)
    [`any #t]
    [`bot #f]
    [(lp sym num bool str list hole?)
     (cond
       [(symbol? v)
        (match sym
          ['variable #t]
          ['bot #f]
          [(var-konsts syms)
           (not (set-member? syms v))]
          [(prefixes+literals the-prefixes the-literals)
           (define v-str (symbol->string v))
           (or (set-member? the-literals v)
               (for/or ([prefix (in-set the-prefixes)])
                 (is-prefix? (symbol->string prefix) v-str)))])]
       [(exact-nonnegative-integer? v)
        (cond
          [(num-konsts? num)
           (set-member? (num-konsts-nums num) v)]
          [else #t])]
       [(boolean? v)
        (match bool
          [`bool #t]
          [#f (equal? v #f)]
          [#t (equal? v #t)]
          [`bot #f])]
       [(string? v)
        (match str
          [`string #t]
          [(? set?) (set-member? str v)]
          [`bot #f])]
       [else #t])]))

(define (build-overlapping-productions-table clang)
  (define overlapping-nt-table (make-hash))
  (define info (build-amb-info clang))
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
                                        info clang))
               (loop (cdr rhses)))])))
    (hash-set! overlapping-nt-table (nt-name nt) has-overlap?))
  overlapping-nt-table)
  
;; a point in the overall lattice
(struct lp (sym num bool str list hole) #:prefab)

;; fixed-sizes : (setof natural)
;; at-least-size : (or/c natural #f)
(struct list-lp (fixed-sizes at-least-size) #:prefab)

;; nums : (set/c exact-nonnegative-integer?)
(struct num-konsts (nums) #:prefab)

;; used for the variable portion of the lattice (see below)
(struct var-konsts (syms) #:prefab)
(struct prefixes+literals (prefixes literals) #:prefab)


(define (build-amb-info clang)
  #|


main-lattice:
  this is a cross product-like
  lattice. As long as we dont encounter
  any "any"s, then we can move the pieces
  independently.
 

       any
        |
  (lp <variable-lattice>
      <number-lattice>
      <boolean-lattice>
      <string-lattice>
      <list-lattice>
      boolean?) --- hole or not
        |
       bot

variable-lattice:

   variable   -- all variables
     /  \
    /    \
 konsts  prefixes+literals
    \    /
     \  /
      bot  -- no variables

The middle piece of the lattice describes two different
states. If it is a konsts, then the non-terminal can match
any symbol except the ones listed. If it is a prefixes+literals,
then the non-terminal can match any variable with one
of the prefixes or when the it is exactly that symbol

konsts and prefixes must not have empty sets in them.



number-lattice:

   number
     |
    real
     |
   integer
     |
   natural
     |
   (num-konsts (set/c nat))


boolean lattice:

    bool
    /  \
   #f   #t
    \  /
     bot


string lattice:

        string
        / | \
.... sets of constant strings ....
        \ | /
         bot

list lattice:

       list
        |
    (list-lp ...)
        |
       bot

|#

  (define (join x y)
    (cond
      [(or (equal? x 'any) (equal? y 'any)) 'any]
      [(equal? x 'bot) y]
      [(equal? y 'bot) x]
      [else
       (lp (join-sym (lp-sym x) (lp-sym y))
           (join-num (lp-num x) (lp-num y))
           (join-bool (lp-bool x) (lp-bool y))
           (join-string (lp-str x) (lp-str y))
           (join-list (lp-list x) (lp-list y))
           (or (lp-hole x) (lp-hole y)))]))

  (define (join-list x y)
    (cond
      [(equal? x 'bot) y]
      [(equal? y 'bot) x]
      [(or (equal? x 'string) (equal? y 'string)) 'string]
      [else
       (match-define (list-lp x-fixed-sizes x-at-least-size) x)
       (match-define (list-lp y-fixed-sizes y-at-least-size) y)
       (define at-least-size
         (cond
           [(and x-at-least-size y-at-least-size)
            (min x-at-least-size y-at-least-size)]
           [else
            (or x-at-least-size y-at-least-size)]))
       (define fixed-sizes
         (if at-least-size
             (for/set ([ele (in-set (set-union x-fixed-sizes y-fixed-sizes))]
                       #:when (< ele at-least-size))
               ele)
             (set-union x-fixed-sizes y-fixed-sizes)))
       (list-lp fixed-sizes at-least-size)]))
  
  (define (join-sym x y)
    (match* (x y)
      [((var-konsts k1) (var-konsts k2))
       (define i (set-intersect k1 k2))
       (if (set-empty? i)
           'variable
           (var-konsts i))]
      [((prefixes+literals p1 l1) (prefixes+literals p2 l2))
       (prefixes+literals (set-union p1 p2) (set-union l1 l2))]
      [('bot x) x]
      [(x 'bot) x]
      [(_ _)    'variable]))
  
  (define (join-num x y)
    (define (both k1 k2) (num-konsts (set-union k1 k2)))
    #2dmatch
    ╔═════════════════╦═════════════════╦══════════╦══════════╦═══════╦═════════╗
    ║         x       ║ (num-konsts k1) ║ `natural ║ `integer ║ `real ║ `number ║
    ║   y             ║                 ║          ║          ║       ║         ║
    ╠═════════════════╬═════════════════╬══════════╬══════════╬═══════╬═════════╣
    ║ (num-konsts k2) ║  (both k1 k2)   ║          ║          ║       ║         ║
    ╠═════════════════╬═════════════════╝          ║          ║       ║         ║
    ║ `natural        ║                   `natural ║          ║       ║         ║
    ╠═════════════════╬════════════════════════════╝          ║       ║         ║
    ║ `integer        ║                              `integer ║       ║         ║
    ╠═════════════════╬═══════════════════════════════════════╝       ║         ║
    ║ `real           ║                                        `real  ║         ║
    ╠═════════════════╬═══════════════════════════════════════════════╝         ║
    ║ `number         ║                                                 `number ║
    ╚═════════════════╩═════════════════════════════════════════════════════════╝)

  (define (join-bool x y)
    #2dmatch
    ╔═════════════╦═══════╦═══════╦═══════╦═══════╗
    ║         x   ║ 'bot  ║  #t   ║  #f   ║ 'bool ║
    ║   y         ║       ║       ║       ║       ║
    ╠═════════════╬═══════╬═══════╬═══════╬═══════╣
    ║ 'bot        ║ 'bot  ║  #t   ║  #f   ║       ║
    ╠═════════════╬═══════╬═══════╬═══════╣       ║
    ║ #t          ║  #t   ║  #t   ║ 'bool ║       ║
    ╠═════════════╬═══════╬═══════╬═══════╣       ║
    ║ #f          ║  #f   ║ 'bool ║  #f   ║       ║
    ╠═════════════╬═══════╩═══════╩═══════╝       ║ 
    ║ 'bool       ║                         'bool ║
    ╚═════════════╩═══════════════════════════════╝)

  (define (join-string x y)
    (match* (x y)
      [('string y) 'string]
      [(x 'string) 'string]
      [('bot y) y]
      [(x 'bot) x]
      [(s1 s2) (set-union s1 s2)]))

  (define num-bot (num-konsts (set)))

  (build-nt-property 
   (compiled-lang-lang clang)
   (lambda (pattern ht)
     (let loop ([pattern pattern])
       (match-a-pattern pattern
         [`any `any]
         [`number (lp 'bot `number 'bot 'bot 'bot #f)]
         [`string (lp 'bot num-bot 'bot `string 'bot #f)]
         [`natural (lp 'bot `natural 'bot 'bot 'bot #f)]
         [`integer (lp 'bot `integer 'bot 'bot 'bot #f)]
         [`real (lp 'bot `real 'bot 'bot 'bot #f)]
         [`boolean (lp 'bot num-bot `bool 'bot 'bot #f)]
         [`variable (lp 'variable num-bot 'bot 'bot 'bot #f)]
         [`(variable-except ,vars ...) (lp (var-konsts (apply set vars)) num-bot 'bot 'bot 'bot #f)]
         [`(variable-prefix ,var) (lp (prefixes+literals (set var) (set)) num-bot 'bot 'bot 'bot #f)]
         [`variable-not-otherwise-mentioned
          (lp (var-konsts (apply set (compiled-lang-literals clang)))
              num-bot 'bot 'bot 'bot #f)]
         [`hole (lp 'bot num-bot 'bot 'bot 'bot #t)]
         [`(nt ,id) (hash-ref ht id)]
         [`(name ,name ,pat) (loop pat)]
         [`(mismatch-name ,name ,pat) (loop pat)]
         [`(in-hole ,context ,contractum) (join (loop context) (loop contractum))]
         [`(hide-hole ,pat) (loop pat)]
         [`(side-condition ,pat ,condition ,expr) (loop pat)]
         [`(cross ,nt) `any]
         [`(list ,pats ...)
          (let loop ([pats pats]
                     [non-repeat 0]
                     [repeat? #f])
            (cond
              [(null? pats)
               (lp 'bot num-bot 'bot 'bot
                   (list-lp (set non-repeat)
                            (if repeat?
                                non-repeat
                                #f))
                   #f)]
              [else
               (match (car pats)
                 [`(repeat . ,whatever)
                  (loop (cdr pats) non-repeat #t)]
                 [_
                  (loop (cdr pats) (+ non-repeat 1) repeat?)])]))]
         [(? (compose not pair?))
          (cond
            [(exact-nonnegative-integer? pattern)
             (lp 'bot (num-konsts (set pattern)) 'bot 'bot 'bot #f)]
            [(number? pattern)
             (lp 'bot 'number 'bot 'bot 'bot #f)]
            [(string? pattern)
             (lp 'bot num-bot 'bot (set pattern) 'bot #f)]
            [(boolean? pattern)
             (lp 'bot num-bot pattern 'bot 'bot #f)]
            [(symbol? pattern)
             (lp (prefixes+literals (set) (set pattern)) num-bot 'bot 'bot 'bot #f)]
            [else 'any])])))
   'bot
   join))

(define (disjoint-sym sym1 sym2)
  (match* (sym1 sym2)
    [('bot _) #t]
    [(_ 'bot) #t]
    [((prefixes+literals ps1 ls1) (prefixes+literals ps2 ls2))
     (and (set-empty? (set-intersect ls1 ls2))
          (for/and ([l (in-set ls1)]
                    [p (in-set ps2)])
            (not (is-prefix? (symbol->string p) (symbol->string l))))
          (for/and ([l (in-set ls2)]
                    [p (in-set ps1)])
            (not (is-prefix? (symbol->string p) (symbol->string l))))
          (for*/and ([p1 (in-set ps1)]
                     [p2 (in-set ps2)])
            (and (not (is-prefix? (symbol->string p1) (symbol->string p2)))
                 (not (is-prefix? (symbol->string p2) (symbol->string p1))))))]
    ;; simplification of the the real knowledge
    [(_ _) #f]))
(define (disjoint-num num1 num2)
  (match* (num1 num2)
    [('bot _) #t]
    [(_ 'bot) #t]
    [((num-konsts s1) (num-konsts s2))
     (disjoint-set? s1 s2)]
    [(_ _) #f]))
(define (disjoint-bool bool1 bool2)
  (match* (bool1 bool2)
    [('bot _) #t]
    [(_ 'bot) #t]
    [(#f #t) #t]
    [(#t #f) #t]
    [(_ _) #f]))

(define (disjoint-list list1 list2)
  #2dmatch
  ╔════════════════════╦══════╦══════════════════╦══════════════════════╦═══════╗
  ║              list2 ║ 'bot ║ (list-lp fs1 #f) ║ (list-lp fs1 n1)     ║ 'list ║
  ║ list1              ║      ║                  ║                      ║       ║
  ╠════════════════════╬══════╩══════════════════╩══════════════════════╩═══════╣
  ║ 'bot               ║  #t                                                    ║
  ╠════════════════════╣      ╔══════════════════╦══════════════════════╦═══════╣
  ║ (list-lp fs2 #f)   ║      ║ (disjoint-set?   ║ (and                 ║       ║
  ║                    ║      ║  fs1 fs2)        ║  (disjoint-set?      ║       ║
  ║                    ║      ║                  ║   fs1 fs2)           ║       ║
  ║                    ║      ║                  ║  (bigger-than-all?   ║       ║
  ║                    ║      ║                  ║   n1 fs2))           ║       ║
  ╠════════════════════╣      ╠══════════════════╬══════════════════════╣       ║
  ║ (list-lp fs2 n2)   ║      ║ (disjoint-list   ║  #f                  ║       ║
  ║                    ║      ║  list2 list1)    ║                      ║       ║
  ║                    ║      ║                  ║                      ║       ║
  ╠════════════════════╣      ╠══════════════════╩══════════════════════╝       ║
  ║ 'list              ║      ║                                            #f   ║
  ╚════════════════════╩══════╩═════════════════════════════════════════════════╝)

(define (disjoint-set? s1 s2)
  (set-empty? (set-intersect s1 s2)))
(define (bigger-than-all? n1 fs2)
  (for/and ([e (in-set fs2)])
    (< e n1)))
    
(define (disjoint-hole hole?1 hole?2) (not (and hole?1 hole?2)))

(define (ambiguous-pattern? pattern the-ambiguity-cache)
  (define non-terminal-ambiguous-ht (ambiguity-cache-ht the-ambiguity-cache))
  (ambiguous-pattern?/ht pattern non-terminal-ambiguous-ht))

(define (ambiguous-pattern?/ht pattern non-terminal-ambiguous-ht)
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
   ambiguous-pattern?/ht
   (λ (nt)
     (cond
       [nt (hash-ref overlapping-productions-ht nt)]
       [else #f]))
   (λ (x y) (or x y))))

;; provided only for the test suite
(module+ for-tests 
  (provide ambiguity-cache
           ambiguity-cache-ht
           overlapping-patterns? 
           build-overlapping-productions-table
           var-konsts
           prefixes+literals
           build-ambiguous-ht
           build-amb-info
           (struct-out lp)
           (struct-out list-lp)
           (struct-out num-konsts)
           (struct-out var-konsts)
           (struct-out prefixes+literals)))
