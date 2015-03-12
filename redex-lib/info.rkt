#lang info

;; racket -l redex/tests/run-tests

(define collection 'multi)

(define deps '(("data-enumerate-lib" #:version "1.2")
               "scheme-lib"
               "base"
               "data-lib"
               "math-lib"
               "tex-table"
               "profile-lib"
               "typed-racket-lib"
               "unstable-2d"
               "unstable-list-lib"))
(define build-deps '("rackunit-lib"))

(define pkg-desc "implementation (no documentation) part of \"redex\"")

(define pkg-authors '(robby bfetscher))

(define version "1.6")
