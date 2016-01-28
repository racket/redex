#lang scribble/manual

@(require "common.rkt" scribble/example
          (for-label racket/base
                     (except-in racket/gui make-color)
                     racket/pretty
                     racket/contract
                     mrlib/graph
                     (except-in 2htdp/image make-pen text)
                     (only-in pict pict? text dc-for-text-size text-style/c
                              vc-append hbl-append vl-append)
                     redex))

@(define redex-eval (make-base-eval '(require redex/reduction-semantics)))

@title[#:tag "sec:binding"]{Binding}

@declare-exporting[redex/reduction-semantics redex]

Typical languages provide a mechanism for the programmer to introduce new names
and give them meaning. The language forms used for this (such as Racket's @racket[let]
and @racket[lambda]) are called @deftech{binding forms}.

Binding forms require special treatment from the language implementor. In Redex, this treatment
consists of declaring the binding forms at the time of language definition. Explicitly declaring
binding forms makes safely manipulating terms containing binding simpler and easier, as opposed to
manually writing operations that respect the binding structure of the language.

@(racketgrammar*
   #:literals (binding:nothing binding:shadow pat:symbol)
   [binding-declaration-list (code:line) (code:line #:binding-forms binding-declaration ...)]
   [binding-declaration binding-pattern
                 (code:line binding-pattern #:exports beta)]
   [beta nothing
         pat:symbol
         (shadow beta-sequence ...)]
   [beta-sequence beta
                  (code:line ... (code:comment "literal ellipsis"))])

A @deftech{binding pattern} is like a @pattern, except that inside it, any @tech{binding pattern}
may be followed by @racket[#:refers-to beta]. A @deftech{beta} is a tree of references to
names bound by the @tech{binding pattern}. (Note that the ``binding'' of pattern variables by Redex
patterns is otherwise unrelated to the ``binding'' of symbols inside Redex terms that we discuss
here.)  Furthermore, in a @tech{binding pattern}, it is also possible to use @racket[#:...bind
(symbol beta beta)] wherever a literal @racket[...] is allowed, creating a @tech{binding
repetition}.

In a given language, a @tech{term} is determined to be a binding form if it matches one of the
@tech{binding patterns} defined in that language (@racket[#:refers-to] and @racket[#:exports] do not
affect matching). 

A common problem is for the binding patterns to be over-specific and not match values that the user
intended to be binding forms. In particular, the binding patterns are different from the patterns
that define the grammar of a language in that multiple references to the name are constrained to
match (alpha-)equivalent values.

@section{The structure of binding forms}

When a term is matched against a @tech{binding pattern}, some of its variables are binders,
and some of them are references to those binders. The rules for binding are already largely
ingrained in programmers minds, but they are as follows: a reference references a binder if they
are both the same symbol, and the reference is inside the scope of that binder, according to
a binding form. When multiple binding forms put the same name in the scope of a term, the innermost
binding form shadows the others.

Scope is defined by @racket[#:refers-to] and @racket[#:exports]. Consider the definition of the
untyped lambda calculus:

@examples[#:label #f #:eval redex-eval
          (define-language lc
            (e (e e)
               x
               (λ (x) e))
            (x variable-not-otherwise-mentioned)
            #:binding-forms
            (λ (x_param) e_body #:refers-to x_param))
          ]

In this simple case, in a @racket[λ] term, the @racket[e_body] subterm has the name from
the @racket[x_param] subterm in scope. The symbols inside a beta must be names bound by the
@tech{binding pattern}

It is possible for a single subterm to refer to multiple other sources of names. In such a case, the
shadowing direction must be specified by the @tech{beta} with a @racket[shadow] clause.

@examples[#:label #f #:eval redex-eval
          (define-extended-language lc-more-1 lc
            (e ....
               (let2 ((x e) (x e)) e))
            #:binding-forms
            (let2 ((x_1 e_1) (x_2 e_2)) e_body #:refers-to (shadow x_1 x_2)))
          ]

Ellipses are also permitted inside @tech{betas}:

@examples[#:label #f #:eval redex-eval
          (define-extended-language lc-more-2 lc
            (e ....
               (let ((x e) ...) e))
            #:binding-forms
            (let ((x_val e_val) ...) e_body #:refers-to (shadow x_val ...)))
          ]

If a pattern symbol is matched underneath ellipses, it may only be mentioned in a @tech{beta}
underneath the same number of ellipses.

So far, the nonterminals mentioned in @racket[#:refers-to] have always represented
individual atoms. If a non-atom is mentioned, and it does not have a binding specification,
or that specification lacks an @racket[#:exports] clause, no names are brought into scope.

The @racket[#:exports] clause can be used to create more complex binding structures. When a
binding form with such a clause is mentioned, the names brought into scope
are determined by recursively examining everything mentioned by that @racket[#:exports] clause.

@examples[#:label #f #:eval redex-eval
          (define-extended-language lc-more-3 lc-more-2
            (e ....
               (let* let*-clauses e))
            (let*-clauses (let*-clause x e let*-clauses)
                          ())
            #:binding-forms
            (let* let*-clauses e #:refers-to let*-clauses)
            (let*-clause x_bnd e_val let*-clauses #:refers-to x_bnd)
            #:exports (shadow x_bnd let*-clauses))]

(Note that, in this example, we have departed from standard Racket syntax: A term representing
a @racket[let*] might look like @racket[(let* (let*-clause x 1 (let*-clause y (* x x) ()))
(+ x y))]. The expected syntax can be recovered with the use of a @tech{binding repetition}.)

Just like @racket[#:refers-to], the beta in an an @racket[#:exports] clause may refer to any
named subterm in its binding declaration.

@section{Behavior of binding forms}

Informally speaking, the fundamental problem in handling binding forms is that, depending on
the context (i.e., the values that they are embedded in), two equal atoms may or may not have
different meanings (i.e., may refer to binders in different positions). Redex solves this
problem by detecting when a binding form is destructured, and @deftech{freshening} all the
names that thereby become free.

This enables Redex to provide a conditional guarantee: if the only tools used to examine a
term are @racket[symbol=?] and built-in Redex operations (for example, metafunctions and
@racket[redex-match]), terms that are alpha-equivalent (according to their binding
specifications) will behave indistinguishably.

One important consequence of this guarantee is that it is not necessary to write
complex capture-avoiding substitution metafunctions in languages with correct binding
specifications. In such languages, any substitution metafunction is inherently
capture-avoiding and inherently avoids replacing bound names.

Similarly, a Redex translation between two languages with binding specifications is
inherently hygienic: it is never affected by the choice of bound names in the program
to be translated.

Furthermore, the notion of equality used by the pattern-matcher is alpha-equivalence,
not naive equivalence. For example:

@examples[#:eval
          redex-eval
          (redex-match lc (any any) (term ((λ (x) x) (λ (y) y))))]

@section{Binding repetitions}

The @racket[let*] construct requires each clause to be a separate binding form in order to
represent the correct behavior. But @racket[let*] clauses (as normally represented) are not
distinguishable from other syntax by pattern-matching. Furthermore, the normal representation of
@racket[let*] clauses does not nest them in a way that corresponds to their binding structure.

Both of these problems can be solved with @tech{binding repetition}. Declaring a subpattern of a
binding form to have @deftech{binding repetition} makes each repetition of the subpattern act as a
separate binding form.

For example:

@examples[#:label #f #:eval redex-eval
          (define-language lc-with-let*
            (e (e e)
               x
               (λ (x) e)
               (let* ((x e) ...) e))
            (x variable-not-otherwise-mentioned)
            #:binding-forms
            (λ (x_param) e_body #:refers-to x_param)
            (let* ((x_v e_v) #:...bind (clauses x_v (shadow clauses x_v)))
              e_body #:refers-to clauses))]

A @tech{binding repetition} can be declared anywhere @racket[...] is legal by instead writing
@racket[#:...bind(subform-name tail-refers-to-beta subform-export-beta)]. The subform exports
@racket[subform-export-beta] (here, @racket[(shadow clauses x_v)]) to the preceding
repetition or the outer binding form, both of which can refer to it by @racket[subform-name] (here,
@racket[clauses]). All subsequent repetitions of the subform will have @racket[tail-refers-to-beta]
(here, @racket[x_v]) in scope.

@examples[#:label #f #:eval redex-eval
          (term (let* ([a 1]
                       [b (+ 1 a)]
                       [c (+ 1 a b)])
                  (+ a b c)))]

In the term above, each @racket[x_v] (i.e. @racket[a], @racket[b], and @racket[c]) is in scope in
all subsequent clauses (though there are no subsequent clauses for @racket[c] to be in scope
for). Furthermore, since each clause exports @racket[(shadow clauses x_v)], the last clause
exports @racket[c], the second-to-last clause exports @racket[c] and @racket[b], and the first one
exports all three, which are then referred-to by the body of the @racket[let*].

Note that because the subpattern under a @racket[#:...bind] creates distinct binding forms, it is
not possible to use @racket[#:refers-to] underneath a @racket[#:...bind] to reference a subform
outside of it, or vice versa. For example, @racket[e_body #:refers-to (shadow x_v ...)]
would have been illegal in the above example.

@defidform[shadow]{Recognized specially within a @tech{beta}. A @racket[shadow] is an error elsewhere.}

@defidform[nothing]{Recognized specially within a @tech{beta}. A @racket[nothing] is an error elsewhere.}

@(close-eval redex-eval)
