#lang racket
(require redex)

#|

A model of Racket's letrec

|#

(provide lang
         surface-lang
         result-of
         run)

(define-language surface-lang
  (e (set! x e)
     (let ((x_!_ e) ...) e)
     (letrec ((x_!_ e) ...) e)
     (if e e e)
     (begin e e ...)
     (e e ...)
     x
     v)
  (v (λ (x_!_ ...) e)
     + - * =
     number
     (void)
     #t
     #f)
  (x variable-not-otherwise-mentioned)

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))

(define-extended-language lang surface-lang
  (p ((store (x_!_ v-or-undefined) ...) e))
  (e ::= ....
     undefined
     (lset! x e))
  
  (P ((store (x v-or-undefined) ...) E))
  (E (v ... E e ...)
     (set! x E)
     (lset! x E)
     (let ((x v-or-undefined) ... (x E) (x e) ...) e)
     (if E e e)
     (begin E e e ...)
     hole)
  
  (v-or-undefined v undefined))


;; collect : term -> term
;; performs a garbage collection on the term `p'
(define (collect p)

  (define (find-unused vars p)
    (filter (λ (var) (unused? var p))
            vars))

  (define (unused? var p)
    (let ([rhss (map cadr (cdar p))]
          [body (cadr p)])
      (and (not (in? var body))
           (andmap (λ (rhs) (not (in? var rhs)))
                   rhss))))

  (define (in? var body)
    (let loop ([body body])
      (match body
        [(cons a b) (or (loop a) (loop b))]
        [(? symbol?) (equal? body var)]
        [else #f])))

  (define (remove-unused vars p)
    (term ((store ,@(filter (λ (binding) (not (memq (car binding) vars)))
                            (cdar p)))
           ,(cadr p))))

  (define vars
    (match p
      [`((store (,xs ,vs) ...) ,e) xs]))
  (define unused (find-unused vars p))
  (cond
    [(null? unused) p]
    [else
     (collect (remove-unused unused p))]))

(module+ test
  (test-equal (collect (term ((store) 1))) (term ((store) 1)))
  (test-equal (collect (term ((store (x 1)) 1))) (term ((store) 1)))
  (test-equal (collect (term ((store (x 1)) x))) (term ((store (x 1)) x)))
  (test-equal (collect (term ((store (x 1) (y x)) 1))) (term ((store) 1)))
  (test-equal (collect (term ((store (x 1) (y x)) y))) (term ((store (x 1) (y x)) y)))
  ;; doesn't really do actually gc, so improving the collect
  ;; function might break this test (which would be great)
  (test-equal (collect (term ((store (x y) (y x)) 1))) (term ((store (x y) (y x)) 1))))

(define reductions
  (reduction-relation
   lang #:domain p
   (==> (in-hole P_1 (begin v e_1 e_2 ...))
        (in-hole P_1 (begin e_1 e_2 ...))
        "begin many")

   (==> (in-hole P_1 (begin e_1))
        (in-hole P_1 e_1)
        "begin one")

   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v_i)
                (x_after v-or-undefined_after) ...)
         (in-hole E_1 x_i))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_i)
                (x_after v-or-undefined_after) ...)
         (in-hole E_1 v_i))
        "get")

   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v_old)
                (x_after v-or-undefined_after) ...)
         (in-hole E (set! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (in-hole E (void)))
        "set!")
   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v-or-undefined)
                (x_after v-or-undefined_after) ...)
         (in-hole E (lset! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (in-hole E (void)))
        "lset!")

   (==> (in-hole P ((λ (x ..._1) e) v ..._1))
        (in-hole P (let ([x v] ...) e))
        "βv")

   (==> (in-hole P (= number_1 number_2 number_3 ...))
        (in-hole P ,(apply = (term (number_1 number_2 number_3 ...))))
        "=")
   (==> (in-hole P (- number_1 number_2 ...))
        (in-hole P ,(apply - (term (number_1 number_2 ...))))
        "-")
   (==> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (==> (in-hole P (* number ...))
        (in-hole P ,(apply * (term (number ...))))
        "*")
   (==> (in-hole P (zero? number))
        (in-hole P (δ zero? number))
        "zero")

   (==> (in-hole P (if #f e_then e_else))
        (in-hole P e_else)
        "iff")
   (==> (in-hole P (if v e_then e_else))
        (in-hole P e_then)
        (side-condition (not (equal? (term v) #f)))
        "ift")

   (==> ((store (x_old v-or-undefined_old) ...)
         (in-hole E (let ([x_1 v-or-undefined_1] [x_2 v-or-undefined_2] ...) e)))
        ((store (x_old v-or-undefined_old) ... (x_new v-or-undefined_1))
         (in-hole E (let ([x_2 v-or-undefined_2] ...) (substitute e x_1 x_new))))
        (fresh x_new)
        "let1")
   (==> (in-hole P (let () e))
        (in-hole P e)
        "let0")

   (==> (in-hole P (letrec ((x e_1) ...) e_2))
        (in-hole P (let ((x undefined) ...) (begin (lset! x e_1) ... e_2)))
        "letrec")

   with
   [(--> a ,(collect (term b))) (==> a b)]))

(define (run e) (traces reductions (term ((store) ,e))))

(define (result-of prog)
  (match (apply-reduction-relation* reductions (term ((store) ,prog)))
    [`(((store . ,_) ,res)) res]))

(module+ test
  (test-equal
   (result-of (term (let ((x 5))
                      (begin
                        (set! x 6)
                        x))))
   6)

  (test-equal
   (result-of
    (term (letrec ((f (λ (x) (begin (set! f x) f))))
            (begin (f 8)
                   f))))
   8)

  (test-equal (result-of (term (+ 1 2 3 4))) 10)
  (test-equal (result-of (term (- 1 2 3 4))) -8)
  (test-equal (result-of (term (* 1 2 3 4))) 24)
  (test-equal (result-of (term (if (= 0 0) 1 2))) 1)
  (test-equal (result-of (term (if (= 0 2) 1 2))) 2)
  (test-equal (result-of (term (letrec ([x 1][y 2]) (+ x y)))) 3)
  (test-equal (result-of (term (letrec ([x 1][y x][z 3]) y))) 1)

  ;; test it gets stuck
  (test-equal (redex-match lang
                           v
                           (result-of (term (letrec ((B (set! B #t))) 1))))
              #f)

  (test-equal
   (result-of
    (term (let ((x 9999))
            (let ((x 5))
              (let ((double (λ (x) (let ((xx x))
                                     (begin (set! xx (+ xx xx)) xx)))))
                (+ (double x)
                   (+ (double (double x))
                      x)
                   (double x)))))))
   45)

  (test-equal
   (result-of
    (term (letrec ((fact
                    (λ (x)
                      (if (= x 0)
                          1
                          (* x (fact (- x 1)))))))
            (fact 5))))
   120)

  (test-equal
   (result-of
    (term (let ((even? 0))
            (let ((odd? 0))
              (begin
                (set! even?
                      (λ (x)
                        (if (= x 0)
                            1
                            (odd? (- x 1)))))
                (set! odd?
                      (λ (x)
                        (if (= x 0)
                            0
                            (even? (- x 1)))))
                (+ (+ (odd? 1)
                      (* (odd? 2) 10))
                   (* (odd? 3) 100)))))))
   101)

  (test-equal
   (result-of
    (term (let ([n 5]
                [acc 1])
            (letrec ([imperative-fact
                      (λ ()
                        (if (= n 0)
                            acc
                            (begin
                              (set! acc (* acc n))
                              (set! n (- n 1))
                              (imperative-fact))))])
              (imperative-fact)))))
   120))
