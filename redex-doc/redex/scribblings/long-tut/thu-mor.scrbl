#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "thu-mor"]{Abstracting Abstract Machines I} 

@goals[
 @item{another perspective and more machines}
 @item{advanced Redex features and extensions}
 @item{static analysis via abstracting abstract machines}
 @item{soundness theorems (in place of equivalence theorems)}
]

We'll work through some existing notes on introducing Redex using an
idea called ``abstracting abstract machines,'' a process for turning
abstract machines in to static analyzers.

The beginning of these notes will largely be review, but it won't hurt
to go through the material again.  During the lecture, I'll skim
through those parts that have been covered to make sure we're all on
the same page.

Please see @url{https://dvanhorn.github.io/redex-aam-tutorial/}.