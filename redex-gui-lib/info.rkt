#lang info

(define collection 'multi)

(define deps '("scheme-lib"
               "base"
               "draw-lib"
               "gui-lib"
               "data-lib"
               "profile-lib"
               "redex-lib"
               "redex-pict-lib"))
(define build-deps '("rackunit-lib"))
(define implies '("redex-lib" "redex-pict-lib"))

(define pkg-desc "implementation (no documentation) part of \"redex\" gui")

(define pkg-authors '(robby bfetscher))

(define version "1.1")

(define license
  '(Apache-2.0 OR MIT))
