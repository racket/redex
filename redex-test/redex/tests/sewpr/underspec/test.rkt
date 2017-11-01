#lang racket/base
(require redex/reduction-semantics "oo.rkt")

(define (3ply red)
  (let loop ([n 2]
             [t main-example])
    (cond
      [(zero? n) (list t)]
      [else 
       (apply append (map (λ (x) (loop (- n 1) x))
                          (apply-reduction-relation red t)))])))

(define ((results-match . x) y)
  (define (⊆ s1 s2) (andmap (λ (x) (member x s2)) s1))
  (and (⊆ x y) (⊆ y x)))

(test-predicate (results-match 
                 '(0 (+ (set 1) (set (- (get) 1)))))
                (3ply red!))
(test-predicate (results-match
                 '(0 (+ (set 1) (set (- (get) 1))))
                 '(0 (+ (set (+ (get) 1)) (set -1)))
                 '(0 (+ (set (+ 0 1)) (set (- 0 1)))))
                (3ply C-red))
(test-predicate (results-match
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set ((λ X1 (- (get) X1)) 1))))
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set ((λ X1 (+ (get) X1)) 1))))
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set ((λ X1 (+ X1 1)) (get)))))
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set ((λ X1 (- X1 1)) (get)))))
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set (+ 0 1))))
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set (- 0 1)))))
                (3ply sch1-red))
(test-predicate (results-match
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set ((λ X1 (+ X1 1)) (get)))))
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set ((λ X1 (- X1 1)) (get)))))
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set (+ 0 1))))
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set (- 0 1)))))
                (3ply sch2-red))
(test-predicate (results-match 
                 '(0 ((λ X (+ (set (+ (get) 1)) X)) (set (- 0 1))))
                 '(0 ((λ X (+ X (set (- (get) 1)))) (set (+ 0 1)))))
                (3ply sch3-red))

(test-->> red!
          (term (0 ((set 1)
                    (set 2))))
          (term (2 (1 2))))
(test-->> C-red 
          (term (0 ((set 1)
                    (set 2))))
          (term (2 (1 2))))
(test-->> sch1-red
          (term (0 ((set 1)
                    (set 2))))
          (term (2 (1 2))))
(test-->> sch2-red
          (term (0 ((set 1)
                    (set 2))))
          (term (2 (1 2))))
(test-->> sch3-red
          (term (0 ((set 1)
                    (set 2))))
          (term (2 (1 2))))

(test-results)
