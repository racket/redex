#lang scribble/manual

@(require racket/runtime-path)

@(require (for-label redex/reduction-semantics))

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "redex2015"]{Long Tutorial}

This tutorial is derived from a week-long Redex summer school,
run July 27–31, 2015 at the University of Utah.

@include-section{mon-mor.scrbl}
@include-section{mon-aft.scrbl}
@include-section{lab-mon-aft.scrbl}

@include-section{tue-mor.scrbl}
@include-section{lab-tue-mor.scrbl}

@include-section{tue-aft.scrbl}
@include-section{lab-tue-aft.scrbl}

@include-section{wed-mor.scrbl}
@include-section{lab-wed-mor.scrbl}

@include-section{wed-aft.scrbl}
@include-section{lab-wed-aft.scrbl}

@include-section{thu.scrbl}

@(define (load-it file)
   (apply
    typeset-code
    (call-with-input-file file
      (λ (port)
        (for/list ([l (in-lines port)])
          (string-append l "\n"))))))

@(define-runtime-path common.rkt "code/common.rkt")
@section[#:tag "common.rkt"]{@filepath{common.rkt}}
@(load-it common.rkt)


@(define-runtime-path close.rkt "code/close.rkt")
@section[#:tag "close.rkt"]{@filepath{close.rkt}}
@(load-it close.rkt)

@(define-runtime-path tc-common.rkt "code/tc-common.rkt")
@section[#:tag "tc-common.rkt"]{@filepath{tc-common.rkt}}
@(load-it tc-common.rkt)

@(define-runtime-path extend-lookup.rkt "code/extend-lookup.rkt")
@section[#:tag "extend-lookup.rkt"]{@filepath{extend-lookup.rkt}}
@(load-it extend-lookup.rkt)
