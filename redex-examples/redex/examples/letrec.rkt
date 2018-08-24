#lang racket
(require redex)

#|

A model of Racket's letrec

|#

(provide lang
         surface-lang
         result-and-output-of
         result-of
         run)

(define-language surface-lang
  (e (set! x e)
     (let ((x_!_ e) ...) e)
     (letrec ((x_!_ e) ...) e)
     (if e e e)
     (begin e e ...)
     (e e ...)
     (writeln e)
     x
     v)
  (v fv sv)
  (fv (λ (x_!_ ...) e) + - * =)
  (sv number
      (void)
      #t
      #f)
  (x variable-not-otherwise-mentioned)

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))

(define-extended-language lang surface-lang
  (p ((store (x_!_ v-or-undefined) ...)
      (output o ...)
      e))
  (e ::= ....
     undefined
     (lset! x e))
  (o ::= procedure sv)
  (P ((store (x v-or-undefined) ...) (output o ...) E))
  (E (v ... E e ...)
     (set! x E)
     (lset! x E)
     (let ((x v-or-undefined) ... (x E) (x e) ...) e)
     (if E e e)
     (begin E e e ...)
     (writeln E)
     hole)
  (v-or-undefined v undefined))

(define v? (redex-match? lang v))

;; collect : term -> term
;; performs a garbage collection on the term `p'
(define (collect p)
  (match p
    [`((store (,vars ,vs) ...) ,o ,e)

     (define (unused-var? var)
       (and (not (in? var e))
            (andmap (λ (rhs) (not (in? var rhs)))
                    vs)))

     (define unused
       (for/list ([var (in-list vars)]
                  #:when (unused-var? var))
         var))

     (cond
       [(null? unused) p]
       [else
        (collect
         (term ((store ,@(filter (λ (binding) (not (memq (car binding) unused)))
                                 (cdar p)))
                ,o
                ,e)))])]))

(define (in? var body)
  (let loop ([body body])
    (match body
      [(cons a b) (or (loop a) (loop b))]
      [(? symbol?) (equal? body var)]
      [else #f])))

(module+ test
  (test-equal (collect (term ((store) (output) 1))) (term ((store) (output) 1)))
  (test-equal (collect (term ((store (x 1)) (output) 1))) (term ((store) (output) 1)))
  (test-equal (collect (term ((store (x 1)) (output) x))) (term ((store (x 1)) (output) x)))
  (test-equal (collect (term ((store (x 1) (y x)) (output) 1))) (term ((store) (output) 1)))
  (test-equal (collect (term ((store (x 1) (y x)) (output) y)))
              (term ((store (x 1) (y x)) (output) y)))
  ;; doesn't really do actually gc, so improving the collect
  ;; function might break this test (which would be great)
  (test-equal (collect (term ((store (x y) (y x)) (output) 1)))
              (term ((store (x y) (y x)) (output) 1))))

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
         (output o ...)
         (in-hole E_1 x_i))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_i)
                (x_after v-or-undefined_after) ...)
         (output o ...)
         (in-hole E_1 v_i))
        "get")

   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v_old)
                (x_after v-or-undefined_after) ...)
         (output o ...)
         (in-hole E (set! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (output o ...)
         (in-hole E (void)))
        "set!")
   (==> ((store (x_before v-or-undefined_before) ...
                (x_i v-or-undefined)
                (x_after v-or-undefined_after) ...)
         (output o ...)
         (in-hole E (lset! x_i v_new)))
        ((store (x_before v-or-undefined_before) ...
                (x_i v_new)
                (x_after v-or-undefined_after) ...)
         (output o ...)
         (in-hole E (void)))
        "lset!")

   (==> (in-hole P ((λ (x ..._1) e) v ..._1))
        (in-hole P (let ([x v] ...) e))
        "βv")

   (==> (in-hole P (= number_1 number_2 ...))
        (in-hole P ,(apply = (term (number_1 number_2 ...))))
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
         (output o ...)
         (in-hole E (let ([x_1 v-or-undefined_1] [x_2 v-or-undefined_2] ...) e)))
        ((store (x_old v-or-undefined_old) ... (x_new v-or-undefined_1))
         (output o ...)
         (in-hole E (let ([x_2 v-or-undefined_2] ...) (substitute e x_1 x_new))))
        (fresh x_new)
        "let1")
   (==> (in-hole P (let () e))
        (in-hole P e)
        "let0")

   (==> (in-hole P (letrec ((x e_1) ...) e_2))
        (in-hole P (let ((x undefined) ...) (begin (lset! x e_1) ... e_2)))
        "letrec")

   (==> ((store (x v-or-undefined) ...)
         (output o ...)
         (in-hole E (writeln sv)))
        ((store (x v-or-undefined) ...)
         (output o ... sv)
         (in-hole E (void)))
        "write flat")
   (==> ((store (x v-or-undefined) ...)
         (output o ...)
         (in-hole E (writeln fv)))
        ((store (x v-or-undefined) ...)
         (output o ... procedure)
         (in-hole E (void)))
        "write proc")

   with
   [(--> a ,(collect (term b))) (==> a b)]))

(define (run e) (traces reductions (term ((store) (output) ,e))))

(define (result-of prog #:steps [steps #f])
  (define-values (result io) (result-and-output-of prog #:steps steps))
  result)

(define (io-of prog #:steps [steps #f])
  (define-values (result io) (result-and-output-of prog #:steps steps))
  io)

(define (result-and-output-of e #:steps [steps #f])
  (define cache (make-binding-hash lang))
  (let loop ([prog (term ((store) (output) ,e))]
             [steps-so-far 0])
    (define cycle? (dict-ref cache prog #f))
    (dict-set! cache prog #t)
    (cond
      [cycle?
       (values 'infinite-loop '())]
      [(or (not steps) (< steps-so-far steps))
       (define nexts (apply-reduction-relation reductions prog))
       (cond
         [(null? nexts)
          (match prog
            [`((store . ,_) (output ,o ...) ,res)
             (values res o)])]
         [(null? (cdr nexts))
          (loop (car nexts) (+ steps-so-far 1))]
         [else
          (error 'result-and-output-of
                 (string-append
                  "term reduced to multiple things\n"
                  "  e: ~s\n"
                  "  reduced to: ~s\n"
                  "  which reduced to multiple things\n"
                  "  ~s")
                 e
                 prog
                 nexts)])]
      [else (values 'ran-out-of-steps '())])))

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
  (test-equal (result-of (term (= 1))) #t)
  (test-equal (result-of (term (if (= 0 0) 1 2))) 1)
  (test-equal (result-of (term (if (= 0 2) 1 2))) 2)
  (test-equal (result-of (term (letrec ([x 1][y 2]) (+ x y)))) 3)
  (test-equal (result-of (term (letrec ([x 1][y x][z 3]) y))) 1)

  (test-equal (io-of (term (writeln (+ 1 2)))) (list 3))
  (test-equal (io-of (term (writeln (writeln (+ 1 2))))) (term (3 (void))))

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
   120)

  (test-equal
   (result-of
    (term (letrec ([loop (λ () (loop))])
            (loop))))
   'infinite-loop)

  (test-equal
   (result-of
    (term (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 2)))))))
    #:steps 2)
   'ran-out-of-steps))
