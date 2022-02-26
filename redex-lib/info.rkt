#lang info

;; racket -l redex/tests/run-tests

(define collection 'multi)

(define deps '(("data-enumerate-lib" #:version "1.3")
               "scheme-lib"
               ("base" #:version "6.2.900.6")
               "data-lib"
               "math-lib"
               "tex-table"
               "profile-lib"
               "typed-racket-lib"
               "testing-util-lib"
               "2d-lib"))
(define build-deps '("rackunit-lib"))

(define pkg-desc "implementation (no documentation) part of \"redex\"")

(define pkg-authors '(robby bfetscher))

(define version "1.18")

(define license
  '(Apache-2.0 OR MIT))
