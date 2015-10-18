#lang scribble/manual

@(require racket/runtime-path
          scribble/core
          (for-syntax racket/base))

@(define-syntax (sol stx)
   (syntax-case stx ()
     [(_ filename)
      (with-syntax ([filename-str (symbol->string (syntax-e #'filename))])
        #'(begin
            (define-runtime-path filename filename-str)
            (fetch-solution filename)))]))

@(define-runtime-path common.rkt "common.rkt")
@(define (fetch-solution filename)
   (define common-needed? #f)
   (define (get-lines filename)
     (call-with-input-file filename
       (λ (port)
         (for/list ([l (in-lines port)])
           (string-append l "\n")))))
   (define main-lines (get-lines filename))
   (cond
     [(ormap (λ (l) (regexp-match #rx"common.rkt" l)) main-lines)
      (nested-flow
       (style #f '())
       (list (apply typeset-code main-lines)
             (apply
              typeset-code
              (append
               '("\n"
                 ";;; ------------------------------------------------------------\n"
                 ";;; common.rkt starts here\n"
                 "\n")
               (get-lines common.rkt)))))]
     [else (apply typeset-code main-lines)]))

@; -----------------------------------------------------------------------------
@title[#:tag "fri-mor" #:style 'toc]{Extended Exercises}

This section offers some Redex challenges of varying complexity. They are broken
up into separate sections, alternating between problems and sample solutions.

@table-of-contents[]

@; -----------------------------------------------------------------------------
@section{Objects: Problem}
Design a small model of untyped objects: a language,
scoping, an adapted substitution function, and a (standard or regular)
reduction system. 

Start with the simplification of objects as multi-entry functions: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-language Object
  (e ::= 
     n
     y
     (object (m (x) e) ...)
     (send e m e))
  (y ::=
     x
     this)
  (n ::= number)
  (m ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned))
))
@;%
 Sometimes we wish to treat @racket[this] like a variable and at other
 times, we want to exclude it from this world. To support this two-faced
 treatment, the grammar includes the syntactic category of @racket[_y],
 which consists of the set @racket[_x] of variables and @racket[this]. 

@section{Objects: Solution}

This solution shows how numbers are interpreted as objects and messages to
these numbers might include symbols such as @racket[+]. Consider extending
this solution with some of the following: 
@itemlist[
@item{recognize stuck states for expressions such as 
@racket[(send _n + (object ...))], 
@racket[(send (object ...) + _n)], 
or 
@racket[(send o m v)] where @racket[_o] does not have an entry point
labeled @racket[_m].}

@item{a @racket[clone] operation for objects}

@item{an @racket[update] operation for objects that adds a new method}

@item{and the inclusion of fields.}
]

@(sol obj.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Types}
Design a reduction system that models type checking by
reducing terms to their types. Formulate a metafunction that maps terms to
types or @racket[#false]:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-metafunction TLambda-tc
  tc : e -> t or #false
  ;; more here 
  ..... 
  )
))
@;%
It produces @racket[#false] when type checking fails. 

You start with the normal term language: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-language TLambda
  (e ::= n x (lambda (x t) e) (e e) (+ e e))
  (n ::= number)
  (t ::= int (t -> t))
  (x ::= variable-not-otherwise-mentioned))
))
@;%
The reduction systems gradually reduces terms to types, like this: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define type-checking 
  (reduction-relation 
    (--> (in-hole C n) (in-hole C int))
    (--> (in-hole C (+ int int)) (in-hole C int))
    ;; you need more here
    .....
    ))
))
@;%

@bold{Hint} The key is to design a language of contexts that extends the
given expression language so the reduction system can find all possible
terms. 

Consider adding @racket[if] and @racket[let] expressions to the
language once you have the core model working. 

@section{Solution: Types}

Also consult chapter III.23 in the Redex book for ideas.

@(sol tc.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Missionaries and Cannibals}

Here is a old puzzle from the 1800s: 
@;
@nested[#:style 'inset]{``Once upon a time, three cannibals were guiding
 three missionaries through a jungle. They were on their way to the nearest
 mission station. After some time, they arrived at a wide river, filled
 with deadly snakes and fish. There was no way to cross the river without a
 boat. Fortunately, they found a rowing boat with two oars after a short
 search. Unfortunately, the boat was too small to carry all of them. It
 could barely carry two people at a time.  Worse, because of the river's
 width someone had to row the boat back.

``Since the missionaries could not trust the cannibals, they had to figure out
 a plan to get all six of them safely across the river. The problem was
 that these cannibals would kill and eat missionaries as soon as there were
 more cannibals than missionaries at some place. Thus our
 missionaries had to devise a plan that guaranteed that there were
 never any missionaries in the minority at either side of the river.  The
 cannibals, however, could be trusted to cooperate otherwise. Specifically,
 they wouldn't abandon any potential food, just as the missionaries
 wouldn't abandon any potential converts.''
}

Formulate a reduction system that solves this puzzle. Use @racket[traces]
 to visualize the solution space. You want to impose a side condition on
 the rules so that no boat is sent back to the other side of the river when
 a configuration represents a solutions. The other side conditions just
 ensure that no missionary will be eaten.

Consider running @racket[traces] with a subject-reduction test. The
 predicate you want to check is that the parties on both sides of the river
 are safe.

@section{Solution: Missionaries and Cannibals}

@(sol mc.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Towers of Hanoi}

Implement a solver for
@hyperlink["https://en.wikipedia.org/wiki/Tower_of_Hanoi"]{Tower of Hanoi}
as a reduction relation, where a step by the reduction corresponds to a
move in the game. You can implement the solver as an exploration of all
possible game moves via the reduction relation, checking whether a solution
state is reachable.

@bold{Hints} While you can implement the game using just
@racket[define-language] and @racket[reduction-relation], a metafunction
that checks whether a stack of ties will ``accept'' a given additional tile
makes the reduction easier to write. Among the possible choices for
representing a tile, a list of @tt{•}s works well and looks nice.

@section{Solution: Towers of Hanoi}

@(sol hanoi.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: GC}

Consider the language of stored binary trees: 
@;
@racketblock[
(define-language L
 [V number
    (cons σ σ)]
 [Σ ([σ V] ...)]
 [σ variable-not-otherwise-mentioned])
]
@;
Design the @racket[-->gc] reduction relation, which implements garbage
collection. The @racket[-->gc] reduction relation operates on a
configuration that combines the store @racket[Σ], a set of ``gray''
addresses, i.e., @racket[σ]s) to be explored (the addresses of the
initially reachable objects, also called roots, plus a set of ``black''
addresses (initially empty).  Each step operates on one gray address,
adjusting the gray and black sets based on the address's value in the
store. No more steps are possible when the set of gray addresses goes
empty, at which point every address not in the black list can be pruned
from the store.

@section{Solution: GC}
@(sol gc.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Finite State Machines}

Implement a reduction relation that executes a given
finite-state machine with a given initial state on a given input
sequence. Your representation for finite-state machine should accommodate a
non-deterministic set of transition rules.

@bold{Challenge} Implement a metafunction that converts a non-deterministic
machine to a deterministic one.

@section{Solution: Finite State Machines}

@(sol fsm.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Threads}

Add process forking and channel-based communication to a
call-by-value functional language. Here is the proposed grammar: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-language Lambda
  (e ::=
     x (lambda (x_!_ ...) e) (e e ...)
     n (+ e e)
     (if0 e e e)
     (spawn e)
     (put c e)
     (get c)
     (void))
  (n ::= number)
  (c ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned))
))
@;%
@;
 A @racket[(spawn _e)] expression creates a new thread from the given
 sub-expression, while @racket[put] and @racket[get] expressions allow
 these threads to communicate. Specifically, when one thread evaluates
 @racket[(put _c _v)] and another evaluates @racket[(get _c)] for the same
 @racket[_c], the @racket[get] thread receives value @racket[_v] while the
 @racket[put] thread's expression evaluates to @racket[(void)]. 

@bold{Hints} Instead of a single expression, your reductions must deal with
 a set of expressions, one per thread.  Reducing @racket[(spawn _e)] in one
 of these expressions thus adds an @racket[_e] to that set; use
 @racket[(void)] as the result of this action. When any one thread has
 @racket[(get _c)] as its redex and another has @racket[(put _c _v)], the
 two redexes are simultaneously replaced with their contractions. 

In Redex, sets are currently realized with sequences. The key difference is
 that sets are @emph{unordered} and sequences are @emph{ordered}. Keep this
 in mind when you formulate reduction relations for
 @racket[put]-@racket[get] communications. 

@section{Solution: Threads}

@(sol channels.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Contracts}

Design a reduction semantics (standard or regular) for a
Lambda language with contracts. Here is the syntax: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-language Lambda
  (e ::=
     x (lambda (x) e) (e e)
     n (+ e e)
     (if0 e e e)
     (c · e x x)
     (blame x))
  (n ::= number)
  (c ::= num? even? odd? pos? (c -> c))
  (x ::= variable-not-otherwise-mentioned))
))
@;%
The contract primitives are interpreted as follows: 
@itemlist[
@item{@racket[(num? x)] checks whether @racket[x] is a number, not a function}
@item{@racket[(pos? x)] checks whether @racket[x] is a positive number}
@item{@racket[(even? x)] checks whether @racket[x] is an even number}
@item{@racket[(odd? x)] checks whether @racket[x] is an even number}
]
The contract form @racket[(c · e x_s x_c)] checks contract @racket[_c] on
@racket[_e]. If @racket[_e] breaks the contract, the semantics signals a
@racket[(blame x_s)] error; other contract violations signal a
@racket[(blame x_c)] error. 

Consider these three examples where the same contracted function works
well, is blamed, or blames its context depending on the argument: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define a-module (term {(even? -> pos?) · (lambda (x) (+ x 1)) server client}))
(define p-good (term [,a-module 2]))
(define p-bad-server (term [,a-module -2]))
(define p-bad-client (term [,a-module 1]))
))
@;%
Work through the examples by hand to find out why the three programs work
fine, blame the server, and blame the client for contract violations,
respectively. 

@section{Solution: Contracts}
@(sol contract.rkt)

@; -----------------------------------------------------------------------------
@section{Problem: Binary Addition}

Redex can also model hardware scenarios. 

Here is a language of @italic{bit} expressions: 
@racketblock[
(define-language L
  (e ::=
     (or e e)
     (and e e)
     (not e)
     (append e ...)
     (add e e)
     v)
  (v ::= (b ...))
  (b ::= 0 1)
  (n ::= natural))
]
Your task is to design a standard reduction system that mimics addition on
sequences of bits (binary digits).
 
@bold{Hints} Raw values are sequences of booleans, not just one.  For
@racket[or], you can reduce sequences that have more than one element into
@racket[append]s of @racket[or]s that each have a single element, and then
actually handle @racket[or]'s logic for arrays that have just one
element. This also works for @racket[and] and @racket[not]. This idea
doesn't work for @racket[add].

Here are some test cases to get you started:
@racketblock[(module+ test
              (test-->> red (term (or (1 1 0 0) (0 1 0 1))) (term (1 1 0 1)))
              (test-->> red (term (not (0 1))) (term (1 0)))
              (test-->> red (term (append (1 0) (0 1))) (term (1 0 0 1)))

              (test-->> red (term (or (1 1 0 0) (0 1 0 1))) (term (1 1 0 1)))
              (test-->> red (term (and (1 1) (0 1))) (term (0 1)))
              (test-->> red (term (and (0 0) (0 1))) (term (0 0))))]

For testing @racket[add], we suggest comparing it to Racket's @racket[+]
operation using this helper function:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; v -> n (in @racket[L])
;; convert a sequence of bits to a natural number 

(module+ test
  (test-equal (to-nat (term ())) 0)
  (test-equal (to-nat (term (0))) 0)
  (test-equal (to-nat (term (1))) 1)
  (test-equal (to-nat (term (0 1))) 1)
  (test-equal (to-nat (term (1 0))) 2)
  (test-equal (to-nat (term (1 1))) 3)
  (test-equal (to-nat (term (1 1 1))) 7)
  (test-equal (to-nat (term (0 1 1 1))) 7)
  (test-equal (to-nat (term (0 1 1 0))) 6))

(define (to-nat bs)
  (for/sum ([b (in-list (reverse bs))]
	    [i (in-naturals)])
    (* b (expt 2 i))))
))
@;%

@section{Solution: Binary Addition}
@(sol bit-strings.rkt)
