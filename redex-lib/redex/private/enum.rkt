#lang racket/base
(require racket/bool
         racket/contract
         racket/function
         racket/list
         racket/math
         racket/match
         racket/promise
         racket/set

         "enumerator.rkt"
         "env.rkt"
         "error.rkt"
         "lang-struct.rkt"
         "match-a-pattern.rkt"
         "preprocess-pat.rkt"
         "preprocess-lang.rkt")

(provide 
 enum-size
 finite-enum?
 (contract-out
  [lang-enumerators (-> (listof nt?) (promise/c (listof nt?)) lang-enum?)]
  [pat-enumerator (-> lang-enum?
                      any/c ;; pattern
                      (or/c #f enum?))]
  [enum-ith (-> enum? exact-nonnegative-integer? any/c)]
  [lang-enum? (-> any/c boolean?)]
  [enum? (-> any/c boolean?)]))

;; nt-enums : hash[sym -o> (or/c #f enum)]
;; cc-enums : promise/c (hash[sym -o> (or/c #f enum)])
;; unused-var/e : enum
(struct lang-enum (nt-enums delayed-cc-enums unused-var/e))
(struct production (n term) #:transparent)
(struct repeat (n terms) #:transparent)
(struct name-ref (name) #:transparent)
(struct misname-ref (name tag) #:transparent)
(struct nrep-ref (name subpat) #:transparent)
(struct decomp (ctx term) #:transparent)
(struct hide-hole (term) #:transparent)

;; Top level exports
(define enum-ith decode)

(define (lang-enumerators lang cc-lang)
  (define (make-lang-table! ht lang)
    (define-values (fin-lang rec-lang cant-enumerate-table) (sep-lang lang))
    (define (enumerate-lang! cur-lang enum-f)
      (for ([nt (in-list cur-lang)])
        (hash-set! ht
                   (nt-name nt)
                   (if (hash-ref cant-enumerate-table (nt-name nt))
                       #f
                       (enum-f (nt-rhs nt) nt-enums)))))
    (enumerate-lang! fin-lang
                     (λ (rhs enums)
                        (enumerate-rhss rhs l-enum)))
    (enumerate-lang! rec-lang
                     (λ (rhs enums)
                        (thunk/e #:size +inf.f
                                 (λ ()
                                    (enumerate-rhss rhs l-enum)))))
    ht)
  (define nt-enums (make-hash))
  (define cc-enums (delay (make-hash)))
  (define unused-var/e
    (apply except/e
           var/e
           (used-vars lang)))
  (define l-enum
    (lang-enum nt-enums cc-enums unused-var/e))
  
  (make-lang-table! nt-enums lang)
  (define filled-cc-enums
    (delay (make-lang-table! (force cc-enums) (force cc-lang))))

  (struct-copy lang-enum l-enum [delayed-cc-enums filled-cc-enums]))

(define (pat-enumerator l-enum pat)
  (cond
    [(can-enumerate? pat (lang-enum-nt-enums l-enum) (lang-enum-delayed-cc-enums l-enum))
     (map/e
      to-term
      (λ (_)
        (redex-error 'pat-enum "Enumerator is not a  bijection"))
      (pat/e pat l-enum)
      #:contract any/c)]
    [else #f]))

(define (enumerate-rhss rhss l-enum)
  (define (with-index i e)
    (cons (map/e (λ (x) (production i x))
                 production-term
                 e
                 #:contract any/c)
          (λ (nd-x) (= i (production-n nd-x)))))
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
     [`natural nat/e]
     [`integer integer/e]
     [`real two-way-real/e]
     [`boolean bool/e]
     [`variable var/e]
     [`(variable-except ,s ...)
      (apply except/e var/e s)]
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
      (map/e (λ (l) (apply decomp l))
             (λ (d)
               (match d
                 [(decomp ctx term)
                  (list ctx term)]))
             (list/e (loop p1)
                     (loop p2))
             #:contract any/c)]
     [`(hide-hole ,p)
      (map/e hide-hole
             hide-hole-term
             (loop p)
             #:contract any/c)]
     [`(side-condition ,p ,g ,e)
      (unsupported pat)]
     [`(cross ,s)
      (lang-enum-get-cross-enum l-enum s)]
     [`(list ,sub-pats ...)
      (apply list/e
       (for/list ([sub-pat (in-list sub-pats)])
         (match sub-pat
           [`(repeat ,pat #f #f)
            (map/e
             (λ (ts)
                (repeat (length ts)
                        ts))
             (λ (rep)
                (repeat-terms rep))
             (list/e (loop pat))
             #:contract any/c)]
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
        (hash-traverse/e val/e tpats #:get-contract (λ (x) any/c)))
      (list/e
       (cons/e (env/e nv l-enum)
               tpats/e))])
   (define names-env
     (hash-traverse/e val/e names #:get-contract (λ (x) any/c)))

   (define misnames-env
     (hash-traverse/e misvals/e misnames #:get-contract (λ (x) any/c)))
   
   (define nreps-env
     (hash-traverse/e reprec/e nreps #:get-contract (λ (x) any/c)))
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
