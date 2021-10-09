#lang info

(define collection 'multi)

(define deps '("base"
               "compiler-lib"
               "rackunit-lib"
               "redex-gui-lib"
               "slideshow-lib"
               "math-lib"
               "plot-lib"))

(define build-deps '())

(define pkg-desc "PLT Redex examples")

(define pkg-authors '(robby bfetscher))

(define license
  '(Apache-2.0 OR MIT))
