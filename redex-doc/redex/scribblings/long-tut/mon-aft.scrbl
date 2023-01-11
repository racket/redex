#lang scribble/manual

@(require "shared.rkt")
@(define redex-eval (let ([e (make-base-eval)]) (e '(require redex/reduction-semantics)) e))

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "mon-aft"]{Syntax and Metafunctions}

@goals[
@item{Redex versus Racket}

@item{define languages}

@item{develop metafunctions, includes basic testing, submodules}

@item{extend languages}

@item{generalizing with @racket[any]}
]

@; -----------------------------------------------------------------------------
@section{Developing a Language}

To start a program with Redex, start your file with
@codeblock{#lang racket
           (require redex)}

The @racket[define-language] from specifies syntax trees via tree grammars:

@code-from-file["code/mon-aft.rkt" #rx"define-language Lambda" #:eval redex-eval]

The trees are somewhat concrete, which makes it easy to work with them, but
it is confusing on those incredibly rare occasions when we want truly
abstract syntax. 

We can include literal numbers (all of Racket's numbers, including complex)
or integers (all of Racket's integers) or naturals (all of Racket's natural
numbers)---and many other things. 

After you have a syntax, use the grammar to generate instances and check
them (typos do sneak in). Instances are generated with @racket[term]:
@code-from-file["code/mon-aft.rkt"
                #rx"define e1 [(]term"
                #:eval redex-eval
                #:exp-count 4
                #:extra-code ("e4")]

Mouse over @racket[define]. It is @emph{not} a Redex form, it comes from
Racket. Take a close look at the last definition. Comma anyone? 

Define yourself a predicate that tests membership: 
@code-from-file["code/mon-aft.rkt" #rx"define in-Lambda[?]" #:eval redex-eval]

Now you can formulate language tests:
@code-from-file["code/mon-aft.rkt" #rx"test-equal [(]in-Lambda[?] e1"
                #:eval redex-eval #:exp-count 4]
@code-from-file["code/mon-aft.rkt" #rx"define eb1"
                #:eval redex-eval #:exp-count 2]
@code-from-file["code/mon-aft.rkt" #rx"test-equal [(]in-Lambda[?] eb1"
                #:eval redex-eval #:exp-count 2
                #:extra-code ("(test-results)")]

Make sure your language contains the terms that you want and does
@emph{not} contain those you want to exclude. Why should @racket[eb1] and
@racket[eb2] not be in @racket[Lambda]'s set of expressions? 

@; -----------------------------------------------------------------------------
@section{Developing Metafunctions}

To make basic statements about (parts of) your language, define
metafunctions. Roughly, a metafunction is a function on the terms of a
specific language. 

A first meta-function might determine whether or not some sequence
of variables has any duplicates. The second line is a Redex contract, not a type. It says
 @racket[unique-vars] consumes a sequence of @racket[x]s and produces a
 @racket[boolean]. 

The remaining lines say that we don't want repeated variables with patterns.
@code-from-file["code/mon-aft.rkt"
                #rx";; unique-vars metafunction start"
                #:eval redex-eval
                #:skip-lines 1]
Patterns are powerful. More later. 

But, don't just define metafunctions, develop them properly: state what
they are about, work through examples, write down the latter as tests,
@emph{then} define the function. 


Wrap the tests in a @racket[module+] with the name @racketidfont{test}
to delegate the tests to a submodule where they belong, allowing us to
document functions by example without introducing tests into client modules
that require the module for the definitions:
@;
@code-from-file["code/mon-aft.rkt"
                #rx";; unique-vars metafunction start"
                #:eval redex-eval
                #:skip-lines 1]


Here are two more metafunctions that use patterns in interesting ways:

@code-from-file["code/mon-aft.rkt"
                #rx"[(]subtract [(]x [.][.][.][)] x_1 [.][.][.][)] removes"
                #:exp-count 4
                #:skip-lines 2]

@; -----------------------------------------------------------------------------
@section{Developing a Language 2}

One of the first things a language designer ought to specify is
@deftech{scope}. People often do so with a free-variables function that
specifies which language constructs bind and which ones don't.

@racket[(fv e)] computes the sequence of free variables of e
a variable occurrence of @racket[x] is free in @racket[e] 
if no @racket[(lambda (x) ...)] @emph{dominates} its occurrence 


@code-from-file["code/mon-aft.rkt"
                #rx"[(]fv e[)] computes the sequence of free variables of e"
                #:skip-lines 1]

@code-from-file["code/mon-aft.rkt"
                #rx";; fv metafunction start"
                #:eval redex-eval
                #:skip-lines 1]

@margin-note{You may know it as the de Bruijn index representation.}
@;
The best approach is to specify an α equivalence relation, that is, the
relation that virtually eliminates variables from phrases and replaces them
with arrows to their declarations. In the world of lambda calculus-based
languages, this transformation is often a part of the compiler, the
so-called static-distance phase. The function is a good example of
accumulator-functions in Redex.

  We have to add a means to the language to say ``arrow back to the variable
  declaration.'' We do @emph{not} edit the language definition but
  @emph{extend} the language definition instead. 

@code-from-file["code/mon-aft.rkt"
                #rx"define-extended-language SD Lambda"
                #:eval redex-eval
                #:exp-count 3]
@code-from-file["code/mon-aft.rkt"
                #rx";; SD[?] test case"
                #:skip-lines 1]

@;%

@code-from-file["code/mon-aft.rkt"
                #rx";; SD metafunction"
                #:exp-count 3]

Now α equivalence is straightforward: 


@code-from-file["code/mon-aft.rkt"
                #rx"determines whether e_1 and e_2 are α equivalent"
                #:exp-count 3]


@; -----------------------------------------------------------------------------
@section{Extending a Language: @racket[any]}

Suppose we wish to extend @racket[Lambda] with @racket[if] and Booleans,
like this: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language SD Lambda
  (e ::= .... 
     true
     false
     (if e e e)))
))
@;%
 Guess what? @racket[(term (fv (lambda (x y) (if x y false))))] doesn't
 work because @racket[false] and @racket[if] are not covered. 

We want metafunctions that are as generic as possible for computing such
notions as free variable sequences, static distance, and alpha
equivalences. 

Redex contracts come with @racket[any] and Redex patterns really are over
Racket's S-expressions. This definition now works for extensions that don't
add binders: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (test-equal (SD? sd1) #true))

(define-metafunction SD
  sd : e -> e
  [(sd e) (sd/a e ())])

(module+ test
  (test-equal (term (sd/a x ())) (term x))
  (test-equal (term (sd/a x (y z x))) (term (K 2)))
  (test-equal (term (sd/a ((lambda (x) x) (lambda (y) y)) ()))
              (term ((lambda (K 0)) (lambda (K 0)))))
  (test-equal (term (sd/a (lambda (x) (x (lambda (y) y))) ()))
              (term (lambda ((K 0) (lambda (K 0))))))
  (test-equal (term (sd/a (lambda (z) (lambda (x) (x (lambda (y) z)))) ()))
              (term (lambda (lambda ((K 0) (lambda (K 2))))))))

(define-metafunction SD
  sd/a : e (x ...) -> e
  [(sd/a x (x_1 ... x x_2 ...))
   ;; bound variable 
   (K n)
   (where n ,(length (term (x_1 ...))))
   (where #false (in x (x_1 ...)))]
  [(sd/a (lambda (x) e) (x_rest ...))
   (lambda (sd/a e (x x_rest ...)))
   (where n ,(length (term (x_rest ...))))]
  [(sd/a (e_fun e_arg) (x_rib ...))
   ((sd/a e_fun (x_rib ...)) (sd/a e_arg (x_rib ...)))]
  [(sd/a any_1 (x ...))
   ;; free variable or constant
   any_1])
))
@;%

@; -----------------------------------------------------------------------------
@section{Substitution}

The last thing we need is substitution, because it @emph{is} the syntactic
equivalent of function application. We define it with @emph{any} having
future extensions in mind.  

@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; (subst ([e x] ...) e_*) substitutes e ... for x ... in e_* (hygienically)

(module+ test
  (test-equal (term (subst ([1 x][2 y]) x)) 1)
  (test-equal (term (subst ([1 x][2 y]) y)) 2)
  (test-equal (term (subst ([1 x][2 y]) z)) (term z))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z) (lambda (w) (x y)))))
              (term (lambda (z) (lambda (w) (1 2)))))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z) (lambda (w) (lambda (x) (x y))))))
              (term (lambda (z) (lambda (w) (lambda (x) (x 2)))))
              #:equiv =α/racket)
  (test-equal (term (subst ((2 x)) ((lambda (x) (1 x)) x)))
              (term ((lambda (x) (1 x)) 2))
              #:equiv =α/racket))

(define-metafunction Lambda
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x) any_body))
   (lambda (x_new)
     (subst ((any_1 x_1) ...)
            (subst-raw (x_new x) any_body)))
   (where  x_new ,(variable-not-in (term any_body) (term x)))]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])

(define-metafunction Lambda
  subst-raw : (x x) any -> any
  [(subst-raw (x_new x_) x_) x_new]
  [(subst-raw (x_new x_) x) x]
  [(subst-raw (x_new x_) (lambda (x) any))
   (lambda (x) (subst-raw (x_new x_) any))]
  [(subst-raw (x_new x_) (any ...))
   ((subst-raw (x_new x_) any) ...)]
  [(subst-raw (x_new x_) any_*) any_*])

))
@;%


}
