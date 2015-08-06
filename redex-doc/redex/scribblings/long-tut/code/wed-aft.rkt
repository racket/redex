#lang racket

;; turn standard reduction into a 3-register machine in three stages: 
;; -- separate evaluation contexts from in-focus expresssion (CC) 
;; -- use a stack data structure instead of a context data structure (CK)
;; -- delay substitution and use environment instead

;; -------------------------------------------------------
(require redex "common.rkt" "close.rkt")

(define-extended-language Lambda/v Lambda
  (e ::= .... n +)
  (n ::= integer)
  (v ::= n + (lambda (x ...) e)))

(define vv? (redex-match? Lambda/v e))

(define e0 (term ((lambda (x) x) 0)))

(define e1 (term ((lambda (x y) x) 1 2)))

(module+ test
  (test-equal (vv? e1) #true)
  (test-equal (vv? e0) #true))

;; -------------------------------------------------------
;; the CC machine: separate contexts from expression-in-focus

(define-extended-language CC Lambda/v
  (E ::= hole (e ... E v ...)))

(module+ test
  (test-->> -->cc (term [,e0 hole]) (term [0 hole]))
  (test-->> -->cc (term [,e1 hole]) (term [1 hole])))

(define -->cc
  (reduction-relation
   CC
   #:domain (e E)
   (--> [(lambda (x ..._n) e)
         (in-hole E (hole v ..._n))]
        [(subst ([v x] ...) e) E]
        CC-β_v)
   (--> [+
         (in-hole E (hole n_1 n_2))]
        [,(+ (term n_1) (term n_2)) E]
        CC-+)
   (--> [(e_1 ...) E]
        [e_last (in-hole E (e_1others ... hole))]
        (where (e_1others ... e_last) (e_1 ...))
        CC-push)
   (--> [v      (in-hole E (e ... hole v_1 ...))]
        [e_last (in-hole E (e_prefix ... hole v v_1 ...))]
        (where (e_prefix ... e_last) (e ...))
        CC-switch)))

(module+ test
  (test-equal (term (eval-cc ,e0)) 0)
  (test-equal (term (eval-cc ,e1)) 1))

(define-metafunction Lambda/v
  eval-cc : e -> v or closure or stuck
  [(eval-cc e) (run-cc [e hole])])

(define-metafunction CC
  run-cc : (e E) -> v or closure or stuck
  [(run-cc (n hole)) n]
  [(run-cc (v hole)) closure]
  [(run-cc any_1)
   (run-cc any_again)
   (where (any_again)
          ,(apply-reduction-relation -->cc (term any_1)))]
  [(run-cc any) stuck])

;; =======================================================
;; the CK machine: encode context as stack (left is top)

(define-extended-language CK Lambda/v
  (k ::= ((app [v ...] [e ...]) ...)))

(module+ test
  (test-->> -->ck (term [,e0 ()]) (term [0 ()]))
  (test-->> -->ck (term [,e1 ()]) (term [1 ()])))

(define -->ck
  (reduction-relation
   CK
   #:domain (e k)
   (--> [(lambda (x ..._n) e)
         ((app [v ..._n] []) (app any_v any_e) ...)]
        [(subst ([v x] ...) e)
         ((app any_v any_e) ...)]
        CK-β_v)
   (--> [+ ((app [n_1 n_2] []) (app any_v any_e) ...)]
        [,(+ (term n_1) (term n_2)) ((app any_v any_e) ...)]
        CK-+)
   (--> [(e_1 ...) (any_k ...)]
        [e_last ((app () (e_1others ...)) any_k ...)]
        (where (e_1others ... e_last) (e_1 ...))
        CK-push)
   (--> [v ((app (v_1 ...) (e ...)) any_k ...)]
        [e_last ((app (v v_1 ...) (e_prefix ...)) any_k ...)]
        (where (e_prefix ... e_last) (e ...))
        CK-switch)))

(module+ test
  (test-equal (term (eval-ck ,e0)) 0)
  (test-equal (term (eval-ck ,e1)) 1))

(define-metafunction Lambda/v
  eval-ck : e -> v or closure or stuck
  [(eval-ck e) (run-ck [e ()])])

(define-metafunction CK
  run-ck : (e k) -> v or closure or stuck
  [(run-ck (n ())) n]
  [(run-ck (v ())) closure]
  [(run-ck any_1)
   (run-ck any_again)
   (where (any_again)
          ,(apply-reduction-relation -->ck (term any_1)))]
  [(run-ck any) stuck])

(module+ test
  ;; theorem:eval-ck=eval-cc
  (test-equal (term (theorem:eval-ck=eval-cc ,e0)) #true)
  (test-equal (term (theorem:eval-ck=eval-cc ,e1)) #true)
  
  ;; NEXT: CEK vs CK 
  (redex-check Lambda e (term (theorem:eval-ck=eval-cc e))
               #:attempts 24
               #:prepare (close-over-fv-with vv?)))

(define-metafunction Lambda/v
  theorem:eval-ck=eval-cc : e -> boolean
  [(theorem:eval-ck=eval-cc e)
   ,(equal? (term (eval-cc e)) (term (eval-ck e)))])


;; =============================================================================
;; the CEK machine: delay substitution via environment 

(define-extended-language CEK Lambda/v
  (ρ ::= ((x c) ...))
  (c ::= (v ρ))
  (k ::= ((app [c ...] ρ [e ...]) ...)))

(module+ test
  (test-->> -->cek (term [,e0 () ()]) (term [0 () ()]))
  (test-->> -->cek (term [,e1 () ()]) (term [1 () ()])))

(define -->cek
  (reduction-relation
   CEK
   #:domain (e ρ k)
   (--> [x
         ((x_1 c_1) ... (x (v ρ)) (x_2 c_2) ...)
         ((app any_v any_r any_e) ...)]
        [v
         ρ
         ((app any_v any_r any_e) ...)]
        CEK-lookup)
   (--> [(lambda (x ..._n) e)
         (any_c ...)
         ((app [c ..._n] ρ []) (app any_v any_r any_e) ...)]
        [e
         ([x c] ... any_c ...)
         ((app any_v any_r any_e) ...)]
        CEK-β_v)
   (--> [+
         ρ
         ((app [n_1 n_2] []) (app any_v any_r any_e) ...)]
        [,(+ (term n_1) (term n_2))
         ()
         ((app any_v any_r any_e) ...)]
        CEK-+)
   (--> [(e_1 ...)
         ρ
         (any_k ...)]
        [e_last
         ρ
         ((app () ρ (e_1others ...)) any_k ...)]
        (where (e_1others ... e_last) (e_1 ...))
        CEK-push)
   (--> [v
         ρ
         ((app (c_1 ...) ρ_stack (e ...)) any_k ...)]
        [e_last
         ρ_stack
         ((app ((v ρ) c_1 ...) ρ_stack (e_prefix ...)) any_k ...)]
        (where (e_prefix ... e_last) (e ...))
        CEK-switch)))

(module+ test
  (test-equal (term (eval-cek ,e0)) 0)
  (test-equal (term (eval-cek ,e1)) 1))

(define-metafunction Lambda/v
  eval-cek : e -> v or closure or stuck
  [(eval-cek e) (run-cek [e () ()])])

(define-metafunction CEK
  run-cek : (e ρ k) -> v or closure or stuck
  [(run-cek (n ρ ())) n]
  [(run-cek (v ρ ())) closure]
  [(run-cek any_1)
   (run-cek any_again)
   (where (any_again)
          ,(apply-reduction-relation -->cek (term any_1)))]
  [(run-cek any) stuck])

(module+ test
  ;; theorem:eval-ck=eval-cc
  (test-equal (term (theorem:eval-cek=eval-ck ,e0)) #true)
  (test-equal (term (theorem:eval-cek=eval-ck ,e1)) #true)
  
  ;; NEXT: CEK vs CK 
  (redex-check Lambda e (term (theorem:eval-cek=eval-ck e))
               #:attempts 24
               #:prepare (close-over-fv-with vv?)))

(define-metafunction Lambda/v
  theorem:eval-cek=eval-ck : e -> boolean
  [(theorem:eval-cek=eval-ck e)
   ,(equal? (term (eval-cek e)) (term (eval-ck e)))])

;; -------------------------------------------------------
(module+ test
  (test-results))
