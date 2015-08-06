#lang racket

;; a model of hardware addition of bit sequences

(require redex)

(define-language L
  (e ::= 
     (or e e)
     (and e e)
     (not e)
     (append e ...)
     (add e e)
     v)
  (v ::= (b ...))
  (n ::= natural)
  (b ::= 0 1))

(define red
  (compatible-closure
   (reduction-relation 
    L
    
    (--> (or (b) (1)) (1) "or-1b")
    (--> (or (1) (b)) (1) "or-b1")
    (--> (or (0) (0)) (0) "or-00")
    
    (--> (or () ()) () "or-0")
    (--> (or (b_1 b_2 b_3 ...)
             (b_4 b_5 b_6 ...))
         (append (or (b_1) (b_4))
                 (or (b_2) (b_5))
                 (or (b_3) (b_6)) ...)
         "or-n")

    
    (--> (not (0)) (1) "not-1")
    (--> (not (1)) (0) "not-0")
    
    (--> (not (b_1 b_2 b_3 ...))
         (append (not (b_1))
                 (not (b_2))
                 (not (b_3)) ...)
         "not-n")
    (--> (not ()) () "not0")
    
    (--> (append (b ...)) (b ...) "append1")
    (--> (append (b_1 ...) (b_2 ...) (b_3 ...) ...)
         (append (b_1 ... b_2 ...) (b_3 ...) ...)
         "append2")
    
    (--> (and (b_1 ...) (b_2 ...))
         (not (or (not (b_1 ...)) 
                  (not (b_2 ...))))
         "and")

    (--> (add () (b ...)) (b ...))
    (--> (add (b ...) ()) (b ...))
    (--> (add (b ... 0) (b_2 ... b_1))
         (append (add (b ...) (b_2 ...)) (b_1)))
    (--> (add (b_2 ... b_1) (b ... 0))
         (append (add (b ...) (b_2 ...)) (b_1)))
    (--> (add (b_1 ... 1) (b_2 ... 1))
         (append (add (add (b_1 ...) (b_2 ...)) (1)) (0))))
   L e))

(module+ test
  (test-->> red (term (or (1 1 0 0) (0 1 0 1))) (term (1 1 0 1)))
  (test-->> red (term (not (0 1))) (term (1 0)))
  (test-->> red (term (append (1 0) (0 1))) (term (1 0 0 1)))
  
  (test-->> red (term (or (1 1 0 0) (0 1 0 1))) (term (1 1 0 1)))
  (test-->> red (term (and (1 1) (0 1))) (term (0 1)))
  (test-->> red (term (and (0 0) (0 1))) (term (0 0))))

;; rewrite-and-compare : (b ...) (b ...) -> boolean
(define (rewrite-and-compare b1s b2s)
  (define rewrite-answer 
    (car
     (apply-reduction-relation*
      red
      (term (add ,b1s ,b2s)))))
  (if (redex-match? L (b ...) rewrite-answer)
      (equal? (+ (to-nat b1s) (to-nat b2s))
              (to-nat rewrite-answer))
      #f))

(define (to-nat bs)
  (for/sum ([b (in-list (reverse bs))]
            [i (in-naturals)])
    (* b (expt 2 i))))

(module+ test
  (test-equal (to-nat (term ())) 0)
  (test-equal (to-nat (term (0))) 0)
  (test-equal (to-nat (term (1))) 1)
  (test-equal (to-nat (term (0 1))) 1)
  (test-equal (to-nat (term (1 0))) 2)
  (test-equal (to-nat (term (1 1))) 3)
  (test-equal (to-nat (term (1 1 1))) 7)
  (test-equal (to-nat (term (0 1 1 1))) 7)
  (test-equal (to-nat (term (0 1 1 0))) 6))


(module+ test
  (test-equal (term (2nat ())) 0)
  (test-equal (term (2nat (0))) 0)
  (test-equal (term (2nat (1))) 1)
  (test-equal (term (2nat (0 1))) 1)
  (test-equal (term (2nat (1 0))) 2)
  (test-equal (term (2nat (1 1))) 3)
  (test-equal (term (2nat (1 1 1))) 7)
  (test-equal (term (2nat (0 1 1 1))) 7)
  (test-equal (term (2nat (0 1 1 0))) 6))

(define-metafunction L
  2nat : (b ...) -> natural
  [(2nat ()) 0]
  [(2nat (b_0 b_1 ...))
   ,(+ (term n_0) (term n_1))
   (where n_1 (2nat (b_1 ...)))
   (where n_0 ,(* (term b_0) (expt 2 (length (term (b_1 ...))))))])
   

;(traces red (term (and (1 1 0 0) (1 0 1 0)))) 

(module+ test
  (test-equal
   (for*/and ([b1 (in-list '(0 1))]
              [b2 (in-list '(0 1))]
              [b3 (in-list '(0 1))]
              [b4 (in-list '(0 1))]
              [b5 (in-list '(0 1))]
              [b6 (in-list '(0 1))])
     (rewrite-and-compare (list b1 b2 b3)
                          (list b4 b5 b6)))
   #t))

(module+ test (test-results))
