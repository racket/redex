#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-thu-mor"]{@bold{Lab} Abstracting Abstract Machines I}

@goals[
@item{develop the world's smallest static analysis}
@item{define approximation on stores}
@item{import semantic ideas into analysis}
]

@;common[]

Start with 
and edit @tt{tutorial.rkt} to complete the exercises.

@; -----------------------------------------------------------------------------
@section[#:tag "lthm" #:style 'unnumbered]{Exercises}

@exercise["ex:dvh1"]{Design the approximation relation for stores,
named @tt{⊑Σ}.  (Marked with @tt{FIXME} in @tt{tutorial.rkt}.)}

@exercise["ex:dvh2"]{Add @tt{set!} and @tt{void} to the model starting
with @tt{-->vσ} and carry it through to @tt{-->vσ^}.  Can you design a 
more precise, yet sound, way of approximating store updates?}

@exercise["ex:dvh3"]{Implement a garbage collector for @tt{-->vσ}
and carry it through to @tt{-->vσ^}.  What do you notice about the precision
of the resulting analyzer?}




