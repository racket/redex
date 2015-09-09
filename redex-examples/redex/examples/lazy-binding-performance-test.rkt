#lang racket
(require redex)

(require "lazy.rkt")

(require (prefix-in binding: "lazy-with-binding.rkt"))

(define add-5-through-1 (term
      (let ([Y (λ (f) 
                  (let ([g (λ (x) 
                              (let ([xx (x x)])
                                (f xx)))])
                    (g g)))]
            [tri
             (λ (me)
                (λ (x)
                   (if0 x
                        0
                        (let ([x1 (+ x -1)])
                          (+ (me x1) x)))))]
            [five 5])
        ((Y tri) five))))

(define 5-noop (term (let ([tri
                            (λ (x)
                               (let ([x1 (+ x -1)])
                                 x))]
                           [five 5])
                       (tri five))))

(define awkward-add (term
                     (let ([o 1]
                           [t 2]
                           [r 3]
                           [f 4])
                       (((((λ (x)
                              (λ (y)
                                 (λ (z)
                                    (λ (w)
                                       (+ (+ x y)
                                          (+ w z))))))
                           o)
                          t)
                         r)
                        f))))

(define (do-subst in old new)
  (term (subst ,in ,old ,new)))
(define (binding:do-subst in old new)
  (substitute binding:L in old new))

(define-syntax-rule (perf-test runner t repeat-count)
  (begin
    (collect-garbage)
    (printf "~a ~a: ~n  " (symbol->string 'runner) 't)
    (time (let loop ([rpts repeat-count])
            (when (> rpts 0)
                  (apply runner t)
                  (loop (- rpts 1)))))))


(perf-test run (list add-5-through-1) 20)
(perf-test binding:run (list add-5-through-1) 20)

(perf-test run (list 5-noop) 5000)
(perf-test binding:run (list 5-noop) 5000)

(perf-test run (list awkward-add) 5000)
(perf-test binding:run (list awkward-add) 5000)



(perf-test do-subst `((λ (x) ((λ (y) x) y)) y z) 30000)
(perf-test binding:do-subst `((λ (x) ((λ (y) x) y)) y z) 30000)

(perf-test do-subst `((λ (x) ((λ (q) y) y)) y z) 30000)
(perf-test binding:do-subst `((λ (x) ((λ (q) y) y)) y z) 30000)

(perf-test do-subst `((let ([x 1][y 2][z 3]) (+ x y)) x q) 30000)
(perf-test binding:do-subst `((let ([x 1][y 2][z 3]) (+ x y)) x q) 30000)
