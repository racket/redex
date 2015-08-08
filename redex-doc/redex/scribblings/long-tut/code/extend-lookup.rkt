#lang racket

(provide
 ;; (extend σ (x ...) (v ...)) adds (x v) ... to σ
 extend

 ;; (lookup σ x) retrieves x's value from σ
 lookup)


;; ------------------------------------------------------------------
(require redex "common.rkt")

(define-metafunction Lambda
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction Lambda
  lookup : ((x any) ...) x -> any or #f
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   #f])
