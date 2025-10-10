#lang info

(define collection 'multi)

(define deps '("base" "racket-doc"))
(define build-deps '("draw-doc"
                     "gui-doc"
                     "htdp-doc"
                     "pict-doc"
                     "at-exp-lib"
                     "data-doc"
                     "data-enumerate-lib"
                     ["scribble-lib" #:version "1.16"]
                     "gui-lib"
                     "htdp-lib"
                     "pict-lib"
                     "redex-gui-lib"
                     "redex-benchmark"
                     "rackunit-lib"
                     "sandbox-lib"))

(define pkg-desc "documentation part of \"redex\"")

(define pkg-authors '(robby bfetscher))

(define license
  '(Apache-2.0 OR MIT))
