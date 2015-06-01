#lang racket/base

(require racket/runtime-path
         "../util/info-util.rkt")

(provide (all-defined-out))

(define name "poly-stlc")
(define fname (make-path-root 'poly-stlc))

(define-runtime-path here ".")

(define (all-mods)
  (append
   (all-mods/type 'typed here name fname)
   (all-mods/type 'typed+rr here name fname)))
