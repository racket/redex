#lang scribble/doc
@(require scribble/manual)
@title{The Redex Reference}

@defmodule*/no-declare[(redex)]

The @racketmodname[redex] library provides all of
the names documented here.

Alternatively, use the @racketmodname[redex/reduction-semantics] and 
@racketmodname[redex/pict] libraries, which provide only non-GUI 
functionality (i.e., everything except @racketmodname[redex/gui]), 
making them suitable for programs that should not depend on 
@racketmodname[racket/gui/base].

@include-section["ref/patterns.scrbl"]
@include-section["ref/terms.scrbl"]
@include-section["ref/languages.scrbl"]
@include-section["ref/reduction-relations.scrbl"]
@include-section["ref/other-relations.scrbl"]
@include-section["ref/testing.scrbl"]
@include-section["ref/gui.scrbl"]
@include-section["ref/typesetting.scrbl"]
