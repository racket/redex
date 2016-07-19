#lang scribble/manual
@(require "common.rkt"
	  scribble/example
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

@title{Languages}

@declare-exporting[redex/reduction-semantics redex]

@defform/subs[#:literals (::= shadow nothing symbol)
              (define-language lang-name 
                non-terminal-def ...
                maybe-binding-spec)
              ([non-terminal-def (non-terminal-name ...+ ::= @#,ttpattern ...+)
                                 (non-terminal-name @#,ttpattern ...+)
                                 ((non-terminal-name ...+) @#,ttpattern ...+)]
               [maybe-binding-spec (code:line)
                                   (code:line #:binding-forms binding-declaration ...)]
	       [binding-declaration binding-pattern
	                            (code:line binding-pattern #:exports beta)]
	       [beta nothing
	             symbol
		     (shadow beta-seqence ...)]
	       [beta-sequence beta
	                      (code:line ... (code:comment "literal ellipsis"))])]{

Defines the grammar of a language. The @racket[define-language] form supports the
definition of recursive @|pattern|s, much like a BNF, but for
regular-tree grammars. It goes beyond their expressive
power, however, because repeated @racket[name] @|pattern|s and
side-conditions can restrict matches in a context-sensitive
way.

A @racket[non-terminal-def] comprises one or more non-terminal names
(considered aliases) followed by one or more productions.

For example, the following defines @deftech{@racket[_lc-lang]} as the
grammar of the λ-calculus:
@examples[#:label #f #:eval redex-eval #:no-prompt #:no-result
(define-language lc-lang
  (e ::= (e e ...)
         x
         v)
  (c ::= (v ... c e ...)
         hole)
  (v ::= (λ (x ...) e))
  (x ::= variable-not-otherwise-mentioned))]

with non-terminals @racket[e] for the expression language, @racket[x] for
variables, @racket[c] for the evaluation contexts, and @racket[v] for values.


Non-terminals used in @racket[define-language] are not bound in
@pattech[side-condition] patterns and duplicates are not constrained
to be the same unless they have underscores in them.

Typical languages provide a mechanism for the programmer to introduce new names
and give them meaning. The language forms used for this (such as Racket's @racket[let]
and @racket[lambda]) are called @tech{binding forms}.

Binding forms require special treatment from the language implementor. In Redex, this treatment
consists of declaring the binding forms at the time of language definition. Explicitly declaring
binding forms makes safely manipulating terms containing binding simpler and easier, as opposed to
manually writing operations that respect the binding structure of the language.

When @racket[maybe-binding-spec] is provided, it declares binding specifications
for certain forms in the language. The language, @tech{@racket[_lc-lang]}, above does not
declare any binding specifications.

To understand the consequences of not specifying any binding forms, consider
the behavior of substitution on terms of @tech{@racket[_lc-lang]}.

@margin-note{
Passing the @racket[#:lang] argument to @racket[term]
allows the @racket[substitute] metafunction to determine
the language of its arguments.}

@examples[#:label #f #:eval redex-eval
 (term (substitute (x (λ (x) (λ (y) x))) x (y y)) #:lang lc-lang)]

Because @tech{@racket[_lc-lang]} does not specify any binding forms, @racket[substitute]
naively replaces all instances of @racket[x] with @racket[(y y)] in the term
@racket[(x (λ (x) (λ (y) x)))], note that even the @racket[x] that appears in what
is normally a binding position has been replaced, resulting in an ill-formed lambda
expression.

In order to have @racket[substitute] behave correctly when substituting over terms
that contain bound variables, the language @tech{@racket[_lc-lang]} must declare its
binding specification. To better understand the use of binding forms in Redex, consider
the following definition of the lambda calculus with binding forms.


@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind
  (e ::= x
         number
         (λ (x) e)
         (e e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))]

In this example the language @deftech{@racket[_lc-bind]} explicitly declares the lambda form as a binding form.
Just like Racket's @racket[lambda], in @tech{@racket[_lc-bind]} all instances of the argument variable in the body
of the lambda should refer to the argument. In a binding declaration, this is specified using the
@racket[#:refers-to] keyword.

@examples[#:label #f #:eval redex-eval
    (term (substitute (x (λ (x) x)) x y) #:lang lc-bind)]

In the example of @racket[#:refers-to] above, in a @racket[λ] term, the @racket[e] subterm has the name from
the @racket[x] subterm in scope. Each symbol mentioned in a beta must also appear in the binding pattern outside
any beta; otherwise it wouldn't mean anything.

It is often useful for a single subterm to refer to multiple sources of names, for example in Racket's @racket[let]
form. This feature is easily expressible with @tech{binding forms} in Redex.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+let
  (e ::= x
         number
         (λ (x) e)
         (e e)
         (let ([x e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))]

The @racket[shadow] form is used to refer to a list of patterns as binders. The subterm
@racket[e_body] will refer to all of the names @racket[x] in the preceding pattern.

@examples[#:label #f #:eval redex-eval
    (term (substitute (let ([x 5] [y x]) (y x)) x z) #:lang lc-bind+let)]

The intuition behind the name of the @racket[shadow] form can be seen in the following example:

@examples[#:label #f #:eval redex-eval
   (term (substitute (let ([x 1] [y x] [x 3]) x) x z) #:lang lc-bind+let)]

Because the language, @deftech{@racket[_lc-bind+let]}, does not require that all binders in its @racket[let] form
be distinct from one another, the @tech{binding forms} specification must declare what happens when there is a conflict.
The @racket[shadow] form specifies that duplicate binders will be shadowed by earlier binders in its list of
arguments.

It is possible to have multiple uses of @racket[#:refers-to] in a single binding specification. For example,
consider a language with a @racket[letrec] form.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+letrec
  (e ::= x
         number
         (λ (x) e)
         (e e)
         (let ([x e] ...) e)
         (letrec ([x e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))]

In this binding specification the subterms corresponding to both @racket[([x e_x] ...)] and @racket[e_body]
may refer to the bound variables in the beta @racket[(shadow x ...)].

@examples[#:label #f #:eval redex-eval
  (term (substitute (letrec ([x x]) x) x y) #:lang lc-bind+letrec)]
@examples[#:label #f #:eval redex-eval
  (term
   (substitute
    (letrec ([x (λ (a) (y a))]
             [y (λ (b) (z b))]
             [z a])
      (x 7))
    a
    (λ (x) 5))
   #:lang lc-bind+letrec)]

Some care must be taken when writing binding specifications that match patterns with ellipses.
If a pattern symbol is matched underneath ellipses, it may only be mentioned in a beta underneath the same number of ellipses.
Consider, for example, a language with Racket's @racket[let-values] binding form.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+values
  (e ::= x
         number
         (λ (x) e)
         (e e)
         (values e ...)
         (let-values ([(x ...) e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x)
  (let-values ([(x ...) e_x0] ...)
    e_body #:refers-to (shadow (shadow x ...) ...)))]

In the binding specification for the @racket[let-values] form, the bound variable, @racket[x],
occurs only under a single ellipsis, thus when it is mentioned in a @racket[#:refers-to] clause it
is restricted to be mentioned only underneath a single ellipsis. Therefore the body of the @racket[let-values]
form must refer to @racket[(shadow (shadow x ...) ...)] rather than @racket[(shadow x ... ...)].

So far, the nonterminals mentioned in @racket[#:refers-to] have always represented
individual atoms. If a non-atom is mentioned, and it does not have a binding specification,
or that specification lacks an @racket[#:exports] clause, no names are brought into scope.

The @racket[#:exports] clause can be used to create more complex binding structures. When a
binding form with such a clause is mentioned, the names brought into scope
are determined by recursively examining everything mentioned by that @racket[#:exports] clause.
Consider the following version of the @racket[_lc-bind] language with lists that allows for pattern matching
in binding positions.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+patterns
    (e ::= x
           number
           (λ (p) e)
           (e e)
           (list e ...))
    (x ::= variable-not-otherwise-mentioned)
    (p ::= (listp p ...) x)
    #:binding-forms
    (λ (p) e #:refers-to p)
    (listp p ...) #:exports (shadow p ...))]

In this language functions accept patterns as arguments, therefore all variables mentioned in a pattern in
binding position should be bound in the body of the function. A call to the @racket[substitute] metafunction
shows this behavior.

@examples[#:label #f #:eval redex-eval
(term
 (substitute (x (λ ((listp w (listp x y) z)) (list z y x w)))
             x
             u)
 #:lang lc-bind+patterns)]

The use of the @racket[#:exports] clause in the binding specification for @racket[_lc-bind+patterns]
allows the use of nested binding patterns seen in the example. More precisely, each @racket[p] may itself
be a pattern that mentions any number of bound variables.

For completeness, consider the following version of @racket[_lc-lang] with contexts, which has
been extended with binding forms.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+hole
  (e ::= (e e ...)
         x
         v)
  (v ::= (λ (x ...) e))
  (c ::= (v ... c e ...)
         hole)
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...)))]

It is important to note in this example, that @racket[(λ (x) e)] is the only binding form.
In general, terms that may contain holes should never be binding forms. In the above language,
if the term @racket[((λ (x) (x x)) (λ (y) y))] were decomposed into
@racket[(in-hole ((λ (x) (x hole)) (λ (y) y)) x)] then instances of @racket[x] must be considered
free so that they maintain their relationship to one another.
}

@defidform[::=]{
A non-terminal's names and productions may be separated by the keyword @racket[::=].
Use of the @racket[::=] keyword outside a language definition is a syntax error.
}

@defform/subs[#:literals (::=)
              (define-extended-language extended-lang base-lang 
                non-terminal-def ...
                maybe-binding-spec)
              ([non-terminal-def (non-terminal-name ...+ ::= @#,ttpattern ...+)
                                 (non-terminal-name @#,ttpattern ...+)
                                 ((non-terminal-name ...+) @#,ttpattern ...+)]
               [maybe-binding-spec (code:line)
                                   (code:line #:binding-forms binding-declaration ...)])]{

Extends a language with some new, replaced, or
extended non-terminals. For example, this language:

@racketblock[
  (define-extended-language lc-num-lang
    lc-lang
    (v ....     (code:comment "extend the previous `v' non-terminal")
       number
       +)
    (x (variable-except λ +)))
]

extends @racket[_lc-lang] with two new alternatives (@racket[+] and @racket[number])
for the @racket[v] non-terminal, carries forward the @racket[e] 
and @racket[c] non-terminals, and replaces the @racket[x] non-terminal 
with a new one (which happens to be equivalent to the one that would 
have been inherited).

The four-period ellipses indicates that the new language's
non-terminal has all of the alternatives from the original
language's non-terminal, as well as any new ones. If a
non-terminal occurs in both the base language and the
extension, the extension's non-terminal replaces the
originals. If a non-terminal only occurs in either the base
language, then it is carried forward into the
extension. And, of course, extend-language lets you add new
non-terminals to the language.

If a language is has a group of multiple non-terminals
defined together, extending any one of those non-terminals
extends all of them.

When @racket[maybe-binding-spec] is provided, it declares binding specifications
for the new forms in the extended language. For a detailed explanation of how to declare
and use binding specifications, see @secref["sec:binding"].
}

@defform/subs[(define-union-language L base/prefix-lang ...)
              ([base/prefix-lang lang-id
                                 (prefix lang-id)])]{
  Constructs a language that is the union of all of the
  languages listed in the @racket[base/prefix-lang].
  
  If the two languages have non-terminals in common, then 
  @racket[define-union-language] will combine all of the productions
  of the common non-terminals. For example, this definition of @racket[L]:
  @racketblock[(define-language L1
                 (e ::=
                    (+ e e) 
                    number))
               (define-language L2
                 (e ::=
                    (if e e e)
                    true 
                    false))
               (define-union-language L1-plus-L2 L1 L2)]
  is equivalent to this one:
  @racketblock[(define-language L1-plus-L2
                 (e ::=
                    (+ e e) 
                    number
                    (if e e e)
                    true 
                    false))]
  
  If a language has a prefix, then all of the non-terminals
  from that language have the corresponding prefix in 
  the union language. The prefix helps avoid unintended collisions
  between the constituent language's non-terminals.
  
  For example, with two these two languages:
  @racketblock[(define-language UT
                 (e (e e)
                    (λ (x) e)
                    x))
               
               (define-language WT
                 (e (e e)
                    (λ (x t) e)
                    x)
                 (t (→ t t)
                    num))]
  then this declaration:
  @racketblock[(define-union-language B (ut. UT) (wt. WT))]
  will create a language named @racket[B] containing the non-terminals
  @racket[ut.e], @racket[wt.e], and @racket[wt.t] consisting
  of the productions listed in the original languages.
}
                                                                                
@defproc[(language-nts [lang compiled-lang?]) (listof symbol?)]{

Returns the list of non-terminals (as symbols) that are
defined by this language.
}

@defproc[(compiled-lang? [l any/c]) boolean?]{

Returns @racket[#t] if its argument was produced by @racket[language], @racket[#f]
otherwise.
}

@defparam[default-language lang (or/c false/c compiled-lang?)]{
The value of this parameter is used by the default value of @racket[(default-equiv)]
to determine what language to calculate alpha-equivalence in. By default,
it is @racket[#f], which acts as if it were a language with no binding forms.
In that case, alpha-equivalence is the same thing as @racket[equal?].

The @racket[default-language] parameter is set to the appropriate language inside judgment forms and
metafunctions, and by @racket[apply-reduction-relation].
}

@defproc[(alpha-equivalent? [lang compiled-lang?] [lhs any/c] [rhs any/c]) boolean?]{
Returns @racket[#t] if (according to the binding specification in @racket[lang])
the bound names in @racket[lhs] and @racket[rhs] have the same structure and,
in everything but bound names, they are @racket[equal?]. If @racket[lang]
has no binding forms, terms have no bound names and therefore
@racket[alpha-equivalent?] is the same as @racket[equal?].
}

@defform[#:kind "metafunction"
         (substitute val old-var new-val)]{
A metafunction that returns a value like @racket[val], except that any free occurences of
@racket[old-var] have been replaced with @racket[new-val], in a capture-avoiding fashion. The bound
names of @racket[val] may be freshened in order to accomplish this, based on the binding information
in @racket[(default-language)] (this is unlike normal metafunctions, which are defined in a
particular language).

Note that @racket[substitute] is merely a convenience metafunction. Any manually-written
substitution in the correct language will also be capture-avoiding, provided that the language's
binding forms are correctly defined.  However, @racket[substitute] may be significantly faster.}
