#lang racket

;; solving the missionaries-and-cannibals problem with Redex

(require redex)

;; -----------------------------------------------------------------------------
;; the problem space syntax

(define-language MC
  (configuration ::= (population boat population))
  (population ::= (mc ...))
  (boat ::= L R)
  (mc ::= c m))

;; -----------------------------------------------------------------------------
;; constraints 

(define-metafunction MC
  ok : population -> boolean
  [(ok (mc ...))
   ,(let ((m (for/sum ((mc (term (mc ...))) #:when (eq? 'm mc)) 1))
          (c (for/sum ((mc (term (mc ...))) #:when (eq? 'c mc)) 1)))
      (or (zero? m) (>= m c)))])

;; a subject reduction test (which sadly failed for the first draft)
(define-metafunction MC
  ok-state : configuration -> boolean
  [(ok-state ((mc_l ...) any (mc_r ...)))
   ,(and (term (ok (mc_l ...))) (term (ok (mc_r ...))))])

;; -----------------------------------------------------------------------------
;; a reduction relation that searches the state space

(define mc-->
  (reduction-relation
   MC
   (--> [(mc_l1 ... mc_* mc_l2 ... mc_+ mc_l3 ...) L (mc_r ...)]
        ;; move two people from left to right 
        [(mc_l1 ... mc_l2 ... mc_l3 ...) R (mc_* mc_+ mc_r ...)]
        (where population_left (mc_l1 ... mc_l2 ... mc_l3 ...))
        (where population_right (mc_* mc_+ mc_r ...))
        (where #true (ok population_left))
        (where #true (ok population_right))
        move-2-left-to-right)
   (--> [(mc mc_1 ...) R (mc_r1 ... mc_* mc_r2 ...)]
        ;; move one person from right to left 
        [(mc_* mc mc_1 ...) L (mc_r1 ... mc_r2 ...)]
        (where population_left (mc_* mc mc_1 ...))
        (where population_right (mc_r1 ... mc_r2 ...))
        (where #true (ok population_left))
        (where #true (ok population_right))
        move-1-right-to-left)
   (--> [(mc mc_1 ...) R (mc_r1 ... mc_* mc_r2 ... mc_+ mc_r3 ...)]
        ;; move two people from right to left 
        [(mc_* mc_+ mc mc_1 ...) L (mc_r1 ... mc_r2 ... mc_r3 ...)]
        (where population_left (mc_* mc_+ mc mc_1 ...))
        (where population_right (mc_r1 ... mc_r2 ... mc_r3 ...))
        (where #true (ok population_left))
        (where #true (ok population_right))
        move-2-right-to-left)))
   
;; -----------------------------------------------------------------------------
(module+ main
  (traces mc--> (term ((m m m c c c) L ()))
          #:pred (lambda (e) (term (ok-state ,e)))))
