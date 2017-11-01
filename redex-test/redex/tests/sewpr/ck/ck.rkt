#lang racket/base
(require redex/reduction-semantics racket/list "../iswim/iswim.rkt")
(provide ck ck-fix same-ck-stdred? same-fixed-answer?)

;; START lang
(define-extended-language iswim-mach
  iswim
  (κ mt (fn V κ) (ar N κ) (op (V ... o) (N ...) κ)))
;; STOP lang

;; START red
(define ck
  (reduction-relation
   iswim-mach
   (--> ((M N) κ) (M (ar N κ)))
   (--> ((o M N ...) κ) (M (op (o) (N ...) κ)))
   (--> (V (fn (λ X M) κ)) ((subst M X V) κ))
   (--> (V (ar N κ)) (N (fn V κ)))
   (--> (b_m (op (b_1 ... o) () κ)) ((δ (o b_m b_1 ...)) κ))
   (--> (V (op (U ... o) (N M ...) κ)) 
        (N (op (V U ... o) (M ...) κ)))))
;; STOP red

;; START fix
(define ck-fix
  (reduction-relation
   iswim-mach
   (--> ((M N) κ) (M (ar N κ)))
   (--> ((o M N ...) κ) (M (op (o) (N ...) κ)))
   (--> (V (fn (λ X M) κ)) ((subst M X V) κ))
   (--> (V (ar N κ)) (N (fn V κ)))
   (--> (b_m (op (b_m-1 ... o) () κ))
        ((δ ,(reverse (term (b_m b_m-1 ... o)))) κ))
   (--> (V (op (U ... o) (N M ...) κ)) 
        (N (op (V U ... o) (M ...) κ)))))
;; STOP fix

(define (get-answers exp)
  (values (apply-reduction-relation* ck (term (,exp mt)))
          (apply-reduction-relation* iswim-red exp)))

;; START phi
(define-metafunction iswim-mach
  [(φ (V mt)) V])
;; STOP phi

;; START pred
(define (same-ck-stdred? exp)
  (define stdred-answers
    (apply-reduction-relation* iswim-red exp))
  (define machine-answers
    (apply-reduction-relation* ck (term (,exp mt))))
  (and (equal? (length stdred-answers) 1)
       (equal? (length machine-answers) 1)
       (equal? (first stdred-answers)
               (term (φ ,(first machine-answers))))))
;; STOP pred

(define (same-fixed-answer? exp)
  (let ([machine-answers
         (apply-reduction-relation* ck-fix (term (,exp mt)))]
        [stdred-answers
         (apply-reduction-relation* iswim-red exp)])
    (and (= (length machine-answers)
            (length stdred-answers)
            1)
         (equal? (list-ref (first machine-answers) 1)
                 (term mt))
         (equal? (list-ref (first machine-answers) 0) 
                 (first stdred-answers)))))

