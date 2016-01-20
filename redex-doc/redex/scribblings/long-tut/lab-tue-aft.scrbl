#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-tue-aft"]{@bold{Lab} Type Checking}

@goals[
@item{subject reduction testing with @racket[trace]}
@item{typing judgments}
]

@common[]

In addition to @seclink["common.rkt"], you also want to @racket[require]
@seclink["tc-common.rkt"] for this lab. Furthermore, if you
copy code from @secref{tue-aft}, make sure to copy the tests and to adapt
the tests as you develop the machines.
		  
@; -----------------------------------------------------------------------------
@section[#:tag "lta" #:style 'unnumbered]{Exercises}

@exercise["ex:typing-trace"]{Develop a reduction system for which the
@racket[trace] expression from the lecture preserves types

@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (traces ->
          (term (((lambda ((x (int -> int))) x) (lambda ((x int)) x)) 1))
          #:pred (lambda (e)
                   (judgment-holds (⊢ () ,e int)))))
))
@;%
}

@exercise["ex:typing"]{Extend @racket[TLambda] with syntax for the
following:
@;
@itemlist[

@item{additional numeric operators, say, multiplication, subtraction, and
division;} 

@item{@racket[let] expressions;}

@item{Boolean constants plus strict and and or operators as well as a
branching construct;}

@item{lists, specifically constructors and selectors (de-constructors);}

@item{explicitly recursive function definitions.}
]
Completing the above list is an ambitious undertaking, but do try to
complete at least two or three of these tasks.}
