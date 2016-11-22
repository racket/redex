#lang racket/base
(require racket/bool
         racket/contract
         racket/function
         racket/list
         racket/math
         racket/match
         racket/promise
         racket/set
         data/enumerate/lib/unsafe
         
         
         "env.rkt"
         "error.rkt"
         "lang-struct.rkt"
         "match-a-pattern.rkt"
         "preprocess-pat.rkt"
         "preprocess-lang.rkt"
         "ambiguous.rkt")

(provide 
 enum-count
 finite-enum?
 (contract-out
  [lang-enumerators (-> (listof nt?)
                        (hash/c symbol? (listof any/c)) ;; any/c is compiled-pattern
                        (promise/c (listof nt?))
                        procedure? ;; this works around a circularity at the module level
                        lang-enum?)]
  [pat-enumerator (-> lang-enum?
                      any/c ;; pattern
                      ambiguity-cache?
                      flat-contract?
                      (or/c #f enum?))]
  [term-index (-> lang-enum?
                  any/c ;; pattern
                  any/c ;; term
                  (or/c exact-nonnegative-integer? #f))]
  [enum-ith (-> enum? exact-nonnegative-integer? any/c)]
  [lang-enum? (-> any/c boolean?)]
  [enum? (-> any/c boolean?)]))

;; nt-enums : hash[sym -o> (or/c #f enum)]
;; cc-enums : promise/c (hash[sym -o> (or/c #f enum)])
;; unused-var/e : enum
(struct lang-enum (nt-enums delayed-cc-enums unused-var/e unparse-term+pat-nt-ht))
(struct production (n term) #:transparent)
(struct repeat (n terms) #:transparent)
(struct name-ref (name) #:transparent)
(struct misname-ref (name tag) #:transparent)
(struct nrep-ref (name subpat) #:transparent)
(struct decomp (ctx term) #:transparent)
(struct hide-hole (term) #:transparent)

;; Top level exports
(define (enum-ith e x) (from-nat e x))

(define (lang-enumerators lang orig-clang-all-ht cc-lang call-nt-proc/bool)
  (define clang-all-ht (hash-copy orig-clang-all-ht))
  (define nt-enums (make-hash))
  (define cc-enums (make-hash))
  (define unused-var/e
    (apply except/e
           symbol/e
           (used-vars lang)))
  
  (define filled-cc-enums
    (delay (let-values ([(fin-cc-lang rec-cc-lang cant-enumerate-cc-table)
                         (sep-lang (force cc-lang) #f)])
             (make-lang-table! l-enum cc-enums fin-cc-lang rec-cc-lang cant-enumerate-cc-table)
             cc-enums)))

  (define-values (fin-lang rec-lang cant-enumerate-table) (sep-lang lang clang-all-ht))
  (define unparse-term+pat-nt-ht
    (build-nt-unparse-term+pat (append fin-lang rec-lang)
                               ;; recombine the productions to make sure they are in
                               ;; the same order as they are in the forwards enumeration
                               clang-all-ht
                               call-nt-proc/bool))
  (define l-enum
    (lang-enum nt-enums filled-cc-enums unused-var/e unparse-term+pat-nt-ht))
  (make-lang-table! l-enum nt-enums fin-lang rec-lang cant-enumerate-table)
  l-enum)

(define (make-lang-table! l-enum ht fin-lang rec-lang cant-enumerate-table)
  (define (enumerate-lang! cur-lang enum-f)
    (for ([nt (in-list cur-lang)])
      (hash-set! ht
                 (nt-name nt)
                 (if (hash-ref cant-enumerate-table (nt-name nt))
                     #f
                     (enum-f (nt-rhs nt) ht)))))
  (enumerate-lang! fin-lang
                   (λ (rhs enums)
                     (enumerate-rhss rhs l-enum)))
  (define rec-lang-base-i (length fin-lang))
  (enumerate-lang! rec-lang
                   (λ (rhs enums)
                     (delay/e (enumerate-rhss rhs l-enum)
                              #:count +inf.f))))

(define (build-nt-unparse-term+pat lang clang-all-ht call-nt-proc/bool)
  
  (define init-unparse-term+pat (make-hash))
  (define unparse-term+pat-nt-ht (make-hash))
  (for ([nt (in-list lang)])
    (define name (nt-name nt))
    (hash-set! unparse-term+pat-nt-ht name
               (λ (term)
                 (error 'lang-enumerators "knot for ~s not tied" nt)))
    (hash-set! init-unparse-term+pat
               name
               (λ (term)
                 ((hash-ref unparse-term+pat-nt-ht name) term))))

  (define empty-t-env (t-env #hash() #hash() #hash()))
  (for ([nt (in-list lang)])
    (define name (nt-name nt))
    (define prod-procs
      (for/list ([rhs (in-list (nt-rhs nt))])
        (unparse-term+pat (rhs-pattern rhs) init-unparse-term+pat)))
    (cond
      [(andmap values prod-procs)
       (define (unparse-nt-term+pat term)
         (let/ec k
           (for ([rhs (in-list (hash-ref clang-all-ht name))]
                 [prod-proc (in-list prod-procs)]
                 [i (in-naturals)])
             (when (call-nt-proc/bool (compiled-pattern-cp rhs)
                                      term
                                      ;; is it okay to use equal? here
                                      ;; and not the language's α-equal function?
                                      equal?)
               (k (production i (ann-pat empty-t-env (prod-proc term))))))
           (error 'unparse-term+pat "ack: failure ~s ~s" nt term)))
       (hash-set! unparse-term+pat-nt-ht name unparse-nt-term+pat)]
      [else (hash-set! unparse-term+pat-nt-ht name #f)]))

  unparse-term+pat-nt-ht)

(define (pat-enumerator l-enum pat the-ambiguity-cache pat-matches/c)
  (cond
    [(can-enumerate? pat (lang-enum-nt-enums l-enum) (lang-enum-delayed-cc-enums l-enum))
     (define from-term (and (not (ambiguous-pattern? pat the-ambiguity-cache))
                            (top-level-unparse-term+pat pat l-enum)))
     (define raw-enumerator (pat/e pat l-enum))
     (cond
       [from-term
        (map/e to-term from-term raw-enumerator #:contract pat-matches/c)]
       [else
        (pam/e to-term raw-enumerator #:contract pat-matches/c)])]
    [else #f]))

(define (term-index l-enum pat term)
  (define raw-enumerator (pat/e pat l-enum))
  (cond
    [raw-enumerator
     (define from-term (top-level-unparse-term+pat pat l-enum))
     (to-nat raw-enumerator (from-term term))]
    [else #f]))

(define (enumerate-rhss rhss l-enum)
  (define (with-index i e)
    (map/e (λ (x) (production i x))
           production-term
           e
           #:contract
           (struct/c production i any/c)))
  (apply or/e
         (for/list ([i (in-naturals)]
                    [production (in-list rhss)])
           (with-index i
                       (pat/e (rhs-pattern production) l-enum)))))

(define (pat/e pat l-enum)
  (match-define (ann-pat nv pp-pat) (preprocess pat))
  (map/e
   (λ (l) (apply ann-pat l))
   (λ (ap)
      (list (ann-pat-ann ap)
            (ann-pat-pat ap)))
   (list/e (env/e nv l-enum)
           (pat-refs/e pp-pat l-enum))
   #:contract any/c))

;; (: pat-refs/e : Pat (HashTable Symbol (Enum Pat)) (Enum Symbol) -> Enum RefPat)
(define (pat-refs/e pat l-enum)
  (define (loop pat)
    (match-a-pattern
     pat
     [`any any/e]
     [`number two-way-number/e]
     [`string string/e]
     [`natural natural/e]
     [`integer integer/e]
     [`real two-way-real/e]
     [`boolean bool/e]
     [`variable symbol/e]
     [`(variable-except ,s ...)
      (apply except/e symbol/e s)]
     [`(variable-prefix ,s)
      (var-prefix/e s)]
     [`variable-not-otherwise-mentioned
      (lang-enum-unused-var/e l-enum)]
     
     ;; not sure this is the right equality function, 
     ;; but it matches the plug-hole function (above)
     [`hole (single/e the-hole #:equal? eq?)]
     
     [`(nt ,id)
      (lang-enum-get-nt-enum l-enum id)]
     [`(name ,n ,pat)
      (single/e (name-ref n))]
     [`(mismatch-name ,n ,tag)
      (single/e (misname-ref n tag))]
     [`(in-hole ,p1 ,p2)
      (define p1/e (loop p1))
      (define p2/e (loop p2))
      (map/e (λ (l) (apply decomp l))
             (λ (d)
               (match d
                 [(decomp ctx term)
                  (list ctx term)]))
             (list/e p1/e p2/e)
             #:contract
             (struct/c decomp
                       (enum-contract p1/e)
                       (enum-contract p2/e)))]
     [`(hide-hole ,p)
      (define p/e (loop p))
      (map/e hide-hole
             hide-hole-term
             p/e
             #:contract 
             (struct/c hide-hole
                       (enum-contract p/e)))]
                                  
     [`(side-condition ,p ,g ,e)
      (unsupported pat)]
     [`(cross ,s)
      (lang-enum-get-cross-enum l-enum s)]
     [`(list ,sub-pats ...)
      (apply list/e
       (for/list ([sub-pat (in-list sub-pats)])
         (match sub-pat
           [`(repeat ,pat #f #f)
            (define pats/e (listof/e (loop pat)))
            (map/e
             (λ (ts) (repeat (length ts) ts))
             (λ (rep) (repeat-terms rep))
             pats/e
             #:contract (struct/c repeat
                                  exact-nonnegative-integer?
                                  (enum-contract pats/e)))]
           [`(repeat ,tag ,n #f)
            (single/e (nrep-ref n tag))]
           [`(repeat ,pat ,n ,m)
            (unimplemented "mismatch repeats (..._!_)")]
           [else (loop sub-pat)])))]
     [(? (compose not pair?)) 
      (single/e pat)]))
  (loop pat))

(define/match (env/e nv l-enum)
  [((env names misnames nreps) _)
   (define (val/e p)
     (pat-refs/e p l-enum))

   (define/match (misvals/e p-ts)
     [((cons p ts))
      (define p/e (val/e p))
      (fold-enum (λ (ts-excepts tag)
                    (define excepts
                      (map cdr ts-excepts))
                    (cons/e (fin/e tag)
                            (apply except/e p/e excepts
                                   #:contract any/c)))
                 (set->list ts)
                 #:f-range-finite? (finite-enum? p/e))])
   
   (define/match (reprec/e nv-t)
     [((cons nv tpats))
      (define tpats/e
        (hash-traverse/e val/e tpats #:contract any/c))
      (listof/e
       (cons/e (env/e nv l-enum)
               tpats/e))])
   (define names-env
     (hash-traverse/e val/e names #:contract any/c))

   (define misnames-env
     (hash-traverse/e misvals/e misnames #:contract any/c))
   
   (define nreps-env
     (hash-traverse/e reprec/e nreps #:contract any/c))
   (map/e
    (λ (v) (apply t-env v))
    (λ (t-e)
      (match t-e
        [(t-env  names misnames nreps)
         (list names misnames nreps)]))
    (list/e names-env
            misnames-env
            nreps-env)
    #:contract t-env?)])

;; to-term : (ann-pat t-env pat-with-refs) -> redex term
(define/match (to-term ap)
  [((ann-pat nv term))
   (strip-hide-holes ((refs-to-fn term) nv))])

;; refs-to-fn : RefPat -> (TEnv -> Term)
(define (refs-to-fn refpat)
  (match refpat
    [(ann-pat nv term)
     (λ (_)
        ((refs-to-fn term) nv))]
    [(production _ term)
     (refs-to-fn term)]
    [(decomp ctx-refs termpat-refs)
     (define ctx-fn (refs-to-fn ctx-refs))
     (define term-fn (refs-to-fn termpat-refs))
     (λ (nv)
        (define ctx (ctx-fn nv))
        (define term (term-fn nv))
        (plug-hole ctx term))]
    [(hide-hole p)
     (define p-fn (refs-to-fn p))
     (λ (nv)
        (hide-hole (p-fn nv)))]
    [(name-ref n)
     (λ (nv)
        (t-env-name-ref nv n))]
    [(misname-ref n tag)
     (λ (nv)
        ((refs-to-fn (t-env-misname-ref nv n tag)) nv))]
    [(list subrefpats ...)
     (compose
      append*
      (sequence-fn
       (for/list ([subrefpat (in-list subrefpats)])
         (match subrefpat
           [(repeat _ subs)
            (sequence-fn (map refs-to-fn subs))]
           [(nrep-ref n tag)
            (λ (nv)
               (define env-ts (t-env-nrep-ref nv n))
               (for/list ([nv-t (in-list env-ts)])
                 (match nv-t
                   [(cons nv tterms)
                    ((refs-to-fn (hash-ref tterms tag)) nv)])))]
           [_ (sequence-fn (list (refs-to-fn subrefpat)))]))))]
    [else (λ (_) refpat)]))

(define (strip-hide-holes term)
  (match term
    [(hide-hole t) (strip-hide-holes t)]
    [(list ts ...) (map strip-hide-holes ts)]
    [_ term]))

(define (plug-hole ctx term)
  (define (plug ctx)
    (match ctx
      [(? (curry eq? the-hole)) term]
      [(list ctxs ...) (map plug ctxs)]
      [_ ctx]))
  (define (unhide term)
    (match term
      [(list ctxs ...) (map unhide ctxs)]
      [(hide-hole term) (unhide term)]
      [_ term]))
  (unhide (plug ctx)))

;; (: sequence-fn : (All (a b) (Listof (a -> b)) -> (a -> (Listof b))))
(define (sequence-fn fs)
  (λ (x)
     (for/list ([f (in-list fs)])
       (f x))))

;; lang-enum-get-nt-enum : lang-enum Symbol -> (or/c Enum #f)
(define (lang-enum-get-nt-enum l-enum s)
  (hash-ref (lang-enum-nt-enums l-enum) s))

;; lang-enum-get-cross-enum : lang-enum Symbol -> (or/c Enum #f)
(define (lang-enum-get-cross-enum l-enum s)
  (hash-ref (force (lang-enum-delayed-cc-enums l-enum)) s))

(define (var-prefix/e s)
  (define as-str (symbol->string s))
  (define ((flip f) x y) (f y x))
  (map/e (compose string->symbol
                  (curry string-append as-str)
                  symbol->string)
         (compose string->symbol
                  list->string
                  (curry (flip drop) (string-length as-str))
                  string->list
                  symbol->string)
         symbol/e
         #:contract (and/c symbol?
                           (let ([reg (regexp (format "^~a" (regexp-quote as-str)))])
                             (λ (x) 
                               (regexp-match? reg (symbol->string x)))))))

(define base/e
  (or/e (fin/e '())
        (cons two-way-number/e number?)
        string/e
        bool/e
        symbol/e))

(define any/e
  (delay/e
   (or/e (cons base/e (negate pair?))
         (cons (cons/e any/e any/e) pair?))
   #:count +inf.0))

;; this function turns a term back into a parsed
;; term to be used with an enumerator produced by pat-refs/e
;; also: the pat should be unambiguous ...?
;; (if so, we can invert; if not, we can maybe just get the first one?)
;; PRE: term matches pat.
;;
;; this variant can be used with non-terminals in a language; the function
;; top-level-unparse-term+pat is used with raw patterns that appear
;; outside of a language
(define (unparse-term+pat pat unparse-nt-hash)
  (define names-encountered (make-hash))
  (let/ec k
    (define (fail) (k #f))
    (let loop ([pat pat])
      (match-a-pattern
       pat
       [`any values]
       [`number values]
       [`string values]
       [`natural values]
       [`integer values]
       [`real values]
       [`boolean values]
       [`variable values]
       [`(variable-except ,s ...) values]
       [`(variable-prefix ,s) values]
       [`variable-not-otherwise-mentioned values]
       [`hole values]
       [`(nt ,id) (or (hash-ref unparse-nt-hash id) (fail))]
       [`(name ,n ,pat)
        (when (hash-ref names-encountered n #f) (fail))
        (hash-set! names-encountered n #t)
        (loop pat)]
       [`(mismatch-name ,n ,tag) (fail)]
       [`(in-hole ,p1 ,p2) (fail)]
       [`(hide-hole ,p) (fail)]
       [`(side-condition ,p ,g ,e) (fail)]
       [`(cross ,s) (fail)]
       [`(list ,sub-pats ...)
        (define repeat-count 0)
        (define to-terms
          ;; (listof (cons/c boolean?[repeat] term-parser))
          (for/list ([sub-pat (in-list sub-pats)])
            (match sub-pat
              [`(repeat ,pat #f #f)
               (cond
                 [(zero? repeat-count)
                  (set! repeat-count 1)
                  (cons #t (loop pat))]
                 [else
                  (fail)])]
              [`(repeat ,pat ,_1 ,_2) (fail)]
              [pat (cons #f (loop pat))])))
        (λ (term)
          (define times-to-repeat (- (length term) (- (length sub-pats) 1)))
          (for/list ([bool+to-term (in-list to-terms)])
            (match bool+to-term
              [(cons #t to-term) ;; repeat
               (repeat
                times-to-repeat
                (for/list ([i (in-range times-to-repeat)])
                  (define this-term (car term))
                  (set! term (cdr term))
                  (to-term this-term)))]
              [(cons #f to-term) ;; not a repeat
               (define this-term (car term))
               (set! term (cdr term))
               (to-term this-term)])))]
       [(? (compose not pair?)) values]))))

(define (top-level-unparse-term+pat pat l-enum)
  (define unparse-nt-hash (lang-enum-unparse-term+pat-nt-ht l-enum))
  (define unparser (unparse-term+pat pat (lang-enum-unparse-term+pat-nt-ht l-enum)))
  (and unparser
       (λ (term)
         (ann-pat (t-env #hash() #hash() #hash()) (unparser term)))))
