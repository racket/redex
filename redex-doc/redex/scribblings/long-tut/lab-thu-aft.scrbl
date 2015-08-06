#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-thu-aft"]{@bold{Lab} Abstracting Abstract Machines II}

@goals[
@item{go further with AAM}
@item{a glimpse of pragmatic concerns}
]

@common[]

@; -----------------------------------------------------------------------------
@section[#:tag "ltha" #:style 'unnumbered]{Exercises}

@exercise["ex:dvh4"]{Add exceptions to the model and carry it through to an
analyzer that handles control effects.}

@exercise["ex:dvh5"]{A very common, pragmatic further approximation to
perform is to consider a ``global'' store, i.e. analysis is not done
by collecting a set of states, each of which includes a store, but
instead a pair consisting of a set of term, environment, stack tuples
and a single store.  Construct another reduction relation which
performs this approximation.}

@exercise["ex:dvh6"]{Pick a language feature you think would be
interesting to model and add it.}

