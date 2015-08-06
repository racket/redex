#lang scribble/doc
@(require scribble/manual
          scribble/bnf
          scribble/struct
          scribble/eval
          "scribblings/cite.rkt")

@title{Redex: Practical Semantics Engineering}

@author["Robert Bruce Findler" "Casey Klein" "Burke Fetscher" "Matthias Felleisen"]

PLT Redex consists of a domain-specific language for specifying
reduction semantics, plus a suite of tools for working with the
semantics. 

This manual consists of four parts: a short tutorial introduction,
a long tutorial introduction, a reference manual for Redex, and a
description of the Redex automated testing benchmark suite.
Also see
@link["http://redex.racket-lang.org/"]{@tt{http://redex.racket-lang.org/}}
and the @tt{examples} subdirectory in the @tt{redex} collection.

@table-of-contents[]

@include-section["scribblings/tut.scrbl"]
@include-section["scribblings/long-tut/long-tut.scrbl"]
@include-section["scribblings/extended-exercises/extended-exercises.scrbl"]
@include-section["scribblings/ref.scrbl"]
@include-section["scribblings/benchmark.scrbl"]

@generate-bibliography[]
@index-section[]


@; Needs a timeout for testing:
@(module* test racket/base
   (require (submod ".."))
   (module config info
     (define timeout 300)))
