#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-wed-mor"]{@bold{Lab} Contexts and Stores}

@goals[
@item{develop a general reduction system for Lambda with assignments}
@item{develop a standard reduction system for Lambda with exceptions}
]

@common[]

Also require @seclink["extend-lookup.rkt"]. Feel free to
copy code from @secref{wed-mor} but make sure to add tests. 

@; -----------------------------------------------------------------------------
@section[#:tag "lwm" #:style 'unnumbered]{Exercises}

The exercises this morning are puzzles. Try your hands on them, but when
you feel stuck, don't hesitate to request help. 

@exercise["ex:calculus-assignments"]{Develop a reduction relation for
assignment statements. Add a @racket[letrec] syntax to the language like
this: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language ImperativeCalculus Assignments
  (e ::= .... (letrec ((x v) ...) e)))
))
@;%
 A @racket[letrec] mutually recursively binds the variables @racket[x ...]
 to the values @racket[v ...] and in @racket[e]. The addition of
 @racket[letrec] internalizes the store into the language. Adapt the
 existing relations. 

Develop terms that one-step reduce in several different directions via
reductions that model assignment and/or variable derefences. Use
@racket[trace] graphs to demonstrate the idea.

@bold{Note} This calculus has naturally separated mini-heaps, but your
system must extrude the scope of these heaps on occasion (when values are
returned) and merge them.}

@exercise["ex:exn-semantics"]{Develop a standard reduction system and a
semantics for exceptions.

@bold{Note} You need to use evaluation contexts for two distinct purposes.}

@exercise["ex:callcc"]{Develop a semantics of for a control operator such as
@racket[callcc]. 

@bold{Request} Check with one of us before you embark on this project. We
want to make sure that (1) the operator isn't too difficult and (2) not to
easy to implement. We are also available for hints.} 

