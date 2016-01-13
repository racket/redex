#lang racket

#|

BUG: letrec & let are not handled properly by substitution

|#

(require redex "subst.rkt")

(reduction-steps-cutoff 20)

(define-language lang
  (p ((store (x v) ...) e))
  (e (set! x e)
     (let ((x e)) e)
     (letrec ((x e)) e)
     (if e e e)
     (begin e e ...)
     (e e)
     x
     v)
  (v (lambda (x) e)
     binop (binop v)
     unop
     number)
  (binop + - *)
  (unop zero?)
  (x variable)
  (pc ((store (x v) ...) ec))
  (ec (ec e)
      (v ec)
      (set! variable ec)
      (let ((x ec)) e)
      (if ec e e)
      (begin ec e e ...)
      hole))

;; collect : term -> term
;; performs a garbage collection on the term `p'
(define (collect p)
  (define (substitute var exp body)
    (term-let ((var var) 
               (exp exp)
               (body body))
      (term (subst (var exp body)))))
  
  (define (find-unused vars p)
    (filter (λ (var) (unused? var p))
            vars))
  
  (define (unused? var p)
    (let ([rhss (map cadr (cdar p))]
          [body (cadr p)])
      (and (not (free-in? var body))
           (andmap (λ (rhs) (not (free-in? var rhs)))
                   rhss))))
  
  (define (free-in? var body)
    (not (equal? (substitute var (gensym) body)
                 body)))
  
  (define (remove-unused vars p)
    `((store ,@(filter (λ (binding) (not (memq (car binding) vars)))
                       (cdar p)))
      ,(cadr p)))
  
  (let* ([vars (map car (cdar p))]
         [unused (find-unused vars p)])
    (cond
      [(null? unused) p]
      [else
       (collect (remove-unused unused p))])))

(define reductions
  (reduction-relation
   lang
   (==> (in-hole pc_1 (begin v e_1 e_2 ...))
        (in-hole pc_1 (begin e_1 e_2 ...))
        begin\ many)
   
   (==> (in-hole pc_1 (begin e_1))
        (in-hole pc_1 e_1)
        begin\ one)
   
   (==> ((store (x_before v_before) ...
           (x_i v_i)
           (x_after v_after) ...)
         (in-hole ec_1 x_i))
        ((store 
             (x_before v_before) ... 
           (x_i v_i)
           (x_after v_after) ...)
         (in-hole ec_1 v_i))
        deref)
   
   (==> ((store (x_before v_before) ...
           (x_i v)
           (x_after v_after) ...)
         (in-hole ec_1 (set! x_i v_new)))
        ((store (x_before v_before) ... 
           (x_i v_new)
           (x_after v_after) ...)
         (in-hole ec_1 v_new))
        set!)     
   
   (==> (in-hole pc_1 ((lambda (x_1) e_1) v_1))
        (in-hole pc_1 (subst (x_1 v_1 e_1)))
        βv)

   (==> (in-hole pc_1 ((binop v_1) v_2))
        (in-hole pc_1
                 ,((match (term binop) ['+ +] ['- -]['* *])
                   (term v_1) (term v_2)))
        δ-binop)

   (==> (in-hole pc_1 (unop v_1))
        (in-hole pc_1
                 ,((match (term unop) ['zero? zero?])
                   (term v_1)))
        δ-unop)

   (==> (in-hole pc_1 (if v_test e_then e_else))
        (in-hole pc_1 ,(if (not (zero? (term v_test)))
                           (term e_then)
                           (term e_else)))
        if)
   
   (==> ((store (name the-store any) ...)
         (in-hole ec_1 (let ((x_1 v_1)) e_1)))
        ,(let ((new-x (variable-not-in (term (the-store ...)) (term x_1))))
           (term
            ((store the-store ... (,new-x v_1))
             (in-hole ec_1 (subst (x_1 ,new-x e_1))))))
        let)
   
   (==> (in-hole pc_1 (letrec ((x_1 e_1)) e_2))
        (in-hole pc_1 (let ((x_1 0)) (begin (set! x_1 e_1) e_2)))
        letrec)
   
   with
   [(--> a ,(collect (term b))) (==> a b)]))



(define (run e) (traces reductions `((store) ,e)))

(define (show-some-reductions)
  (run '(letrec ((f (lambda (x)
                      (letrec ((y (f 1)))
                        2))))
          (f 3)))

  (run '(letrec ((f (lambda (x)
                      (letrec ((y 1))
                        (f 1)))))
          (f 3))))

(define (result-of prog)
  (match (apply-reduction-relation* reductions `((store) ,prog))
    [`(((store . ,_) ,res)) res]))


(time
 (test-equal
  (result-of `(let ((x 5))
                (begin
                  (set! x 6)
                  x)))
  6)

 (test-equal
  (result-of
   `(letrec ((f (lambda (x) (begin (set! f x) f))))
      (begin (f 8)
             f)))
  8)

 ;; changing `xx` to `x` produces an error, but it shouldn't

 (test-equal
  (result-of
   `(let ((x 9999))
      (let ((x 5))
        (let ((double (lambda (x) (let ((xx x))
                                    (begin (set! xx ((+ xx) xx)) xx)))))
          ((+ (double ((+ (double (double x))) x))) (double x))))))
  60)

 (test-equal
  (result-of
   `(letrec ((fact
              (lambda (x)
                (if x
                    ((* x) (fact ((- x) 1)))
                    1))))
      (fact 5)))
  120)

 (test-equal
  (result-of
   `(let ((even? 0))
      (let ((odd? 0))
        (begin
          (set! even?
                (lambda (x)
                  (if x
                      (odd? ((- x) 1))
                      1)))
          (set! odd?
                (lambda (x)
                  (if x
                      (even? ((- x) 1))
                      0)))
          ((+
            ((+ (odd? 17))
             ((* (odd? 18)) 10)))
           ((* (odd? 19)) 100))))))
  101)

 (test-equal
  (result-of
   `(let ((n 5))
      (let ((acc 1))
        (letrec ((imperative-fact (lambda (ignored)
                                    (if n
                                        (begin
                                          (set! acc ((* acc) n))
                                          (set! n ((- n) 1))
                                          (imperative-fact 9999))
                                        acc))))
          (imperative-fact 9999)))))
  120))



(test-results)
