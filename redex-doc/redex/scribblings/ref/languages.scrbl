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
@(define (mini-heading . whatever) (apply section whatever))

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
                                   (code:line #:binding-forms binding-pattern ...)]
               [binding-pattern
                #,pattern
                (code:line binding-pattern #:exports beta)
                (code:line binding-pattern #:refers-to beta)
                (code:line binding-pattern #:...bind (id beta beta))]
	       [beta nothing
	             symbol
		     (shadow beta-sequence ...)]
	       [beta-sequence beta
	                      (code:line ... (code:comment "literal ellipsis"))])]{

Defines the grammar of a language. The @racket[define-language] form supports the
definition of recursive @|pattern|s, much like a BNF, but for
regular-tree grammars. It goes beyond their expressive
power, however, because repeated @racket[name], @racket[in-hole], and
side-condition @|pattern|s can restrict matches in complex ways.

A @racket[non-terminal-def] comprises one or more non-terminal names
(considered aliases) followed by one or more productions.

@; this language is copied to other-relations.scrbl to be used in examples there, too
 For example, the following defines @deftech{@racket[_lc-lang]} as the
grammar of the λ-calculus:
@examples[#:label #f #:eval redex-eval #:no-prompt #:no-result
(define-language lc-lang
  (e ::= (e e ...)
         x
         (λ (x ...) e))
  (v ::= (λ (x ...) e))
  (E ::= (v ... E e ...)
         hole)
  (x y ::= variable-not-otherwise-mentioned))]

 It has non-terminals: @racket[e] for the expression language, @racket[x]
 and @racket[y] for variables,
 @racket[v] for values, and
 @racket[E] for the evaluation contexts.

Non-terminals used in @racket[define-language] are not bound in
@pattech[side-condition] patterns. Duplicate non-terminals
that appear outside of the binding-forms section are not constrained
to be the same unless they have underscores in them.

@mini-heading{Binding Forms}

Typical languages provide a mechanism for the programmer to introduce new names
and give them meaning. The language forms used for this (such as Racket's @racket[let]
and @racket[λ]) are called @deftech{binding forms}.

Binding forms require special treatment from the language implementer. In Redex, this treatment
consists of declaring the binding forms at the time of language definition. Explicitly declaring
binding forms makes safely manipulating terms containing binding simpler and easier, eliminating the
need to write operations that (explicitly) respect the binding structure of the language.

When @racket[maybe-binding-spec] is provided, it declares binding specifications
for certain forms in the language. The @racket[binding-pattern] specification is an
extension of Redex's @|pattern| language, allowing the keywords @indexed-racket[#:refers-to],
@indexed-racket[#:exports], and @indexed-racket[#:...bind]s to appear nested inside a binding pattern.

The language, @racket[_lc-lang], above does not
declare any binding specifications, despite the clear intention of @racket[λ] as
a binding form. To understand the consequences of not specifying any binding forms, consider
the behavior of substitution on terms of @racket[_lc-lang].

@margin-note{
Passing the @racket[#:lang] argument to @racket[term]
allows the @racket[substitute] metafunction to determine
the language of its arguments.}

@examples[#:label #f #:eval redex-eval
 (term (substitute (x (λ (x) (λ (y) x)))
                   x
                   (y y)) #:lang lc-lang)]

This call is intended to replace all free occurrences of @racket[x] with @racket[(y y)]
in the first argument to @racket[substitute]. But, 
because @racket[_lc-lang] is missing a binding forms declaration, @racket[substitute]
replaces all instances of @racket[x] with @racket[(y y)] in the term
@racket[(x (λ (x) (λ (y) x)))]. Note that even the @racket[x] that appears in what
is normally a binding position has been replaced, resulting in an ill-formed lambda
expression.

In order to have @racket[substitute] behave correctly when substituting over terms
that contain bound variables, the language @racket[_lc-lang] must declare its
binding specification. Consider the following simplification of the @racket[_lc-lang]
definition, this time with a binding form declaration for @racket[λ].

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind
  (e ::= (e e)
         x
         (λ (x) e))
  (v ::= (λ (x) e))
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))
]

Just like Racket's @racket[λ], in @racket[_lc-bind] all instances of the argument variable in the body
of the lambda refer to the argument. In a binding declaration, this is specified using the
@racket[#:refers-to] keyword. Now the previous example has the right behavior.

@examples[#:label #f #:eval redex-eval
 (term (substitute (x (λ (x) (λ (y) x)))
                   x
                   (y y)) #:lang lc-bind)]

Note that sometimes substitute changes the names of the bound identifiers, in this case
replacing the @racket[x] and @racket[y] with identifiers that have @racket[«] and @racket[»]
in their names.

The @racket[#:refers-to] declaration says that, in a @racket[λ] term, the @racket[e] subterm has the name from
the @racket[x] subterm in scope.

@mini-heading{Multiple Variables in a Single Scope}

To generalize to the version of @racket[λ] in @racket[_lc-lang], we need to cope with multiple
variables at once. And in order to do that, we must handle the situation where some of the
names are the same. Redex's binding support offers only one option for this, namely taking
the variables in order. The is captured by the keyword @racket[_shadow]. It also allows
us to specify the binding structure for @racket[let]:

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+let
  (e ::= x
         number
         (λ (x ...) e)
         (e e)
         (let ([x e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))]

This @racket[#:binding-forms] declaration says that the subterm
@racket[e] of the @racket[λ] expression refers to all of the binders
in @racket[λ]. Similarly, the @racket[e_body] refers to all of the
binders in the @racket[let] expression.

@examples[#:label #f #:eval redex-eval
          (term (substitute (let ([x 5] [y x]) (y x))
                            x
                            z) #:lang lc-bind+let)]

The intuition behind the name of the @racket[shadow] form can be seen in the following example:

@examples[#:label #f #:eval redex-eval
   (term (substitute (let ([x 1] [y x] [x 3]) x)
                     x
                     z) #:lang lc-bind+let)]

Because the @racket[_lc-bind+let]  language does not require that all binders in its @racket[let] form
be distinct from one another, the @tech{binding forms} specification must declare what happens when there is a conflict.
The @racket[shadow] form specifies that duplicate binders will be shadowed by earlier binders in its list of
arguments. (Of course, if we were interested in modelling Racket's @racket[let] form, we'd
want that term to be malformed syntax.)

It is possible to have multiple uses of @racket[#:refers-to] in a single binding specification. For example,
consider a language with a @racket[letrec] form.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+letrec
  (e ::= x
         number
         (λ (x ...) e)
         (e e)
         (let ([x e] ...) e)
         (letrec ([x e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec ([x e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...)))]

In this binding specification the subterms corresponding to both @racket[([x e_x] ...)] and @racket[e_body]
refer to the bound variables @racket[(shadow x ...)].

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

@mini-heading{Ellipses in Binding Forms}

Some care must be taken when writing binding specifications that match patterns with ellipses.
If a pattern symbol is matched underneath ellipses, it may only be mentioned under the same number of ellipses.
Consider, for example, a language with Racket's @racket[let-values] binding form.

@examples[#:label #f #:eval redex-eval #:no-result
(define-language lc-bind+values
  (e ::= x
         number
         (λ (x ...) e)
         (e e)
         (values e ...)
         (let-values ([(x ...) e] ...) e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let-values ([(x ...) e_x0] ...)
    e_body #:refers-to (shadow (shadow x ...) ...)))]

In the binding specification for the @racket[let-values] form, the bound variable, @racket[x],
occurs only under a single ellipsis, thus when it is mentioned in a @racket[#:refers-to] clause it
is restricted to be mentioned only underneath a single ellipsis. Therefore the body of the @racket[let-values]
form must refer to @racket[(shadow (shadow x ...) ...)] rather than @racket[(shadow x ... ...)].

@mini-heading{Compound Forms with Binders}

 So far, the nonterminals mentioned in @racket[#:refers-to]
 have always stood directly for variables that appear in the
 terms. But sometimes the variables are down inside some
 piece of the term, or only some of the variables are
 relevant. The @racket[#:exports] clause can be used to
 handle such situations.

 When a binding form with an @racket[#:exports] clause is
 mentioned, the names brought into scope are determined by
 recursively examining everything mentioned by that
 @racket[#:exports] clause. Consider the following version of
 the @racket[_lc-bind] language with lists that allows for
 pattern matching in binding positions.

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

@mini-heading{Binding Repetitions}

 In some situations, the @racket[#:exports] and
 @racket[#:refers-to] keywords are not sufficiently
 expressive to be able to describe the binding structure of
 different parts of a repeated sequence relate to each other.
 For example, consider the @racket[let*] form. Its shape is
 the same as @racket[let], namely
 @racket[(let* ([x e] ...) e)], but the binding structure is
 different.

 In a @racket[let*] form, each variable is accessible to
 each of the @racket[e]s that follow it, with all of the
 variables available in the body (the final @racket[e]). With
 @racket[#:exports], we can build an expression form that has
 a structure like that, but we must write syntax that nests
 differently than @racket[let*].

@examples[#:label #f #:eval redex-eval #:no-result
          (define-language lc-bind+awkward-let*
            (e ::= (let*-awk c e) natural x (+ e ...))
            (x ::= variable-not-otherwise-mentioned)
            (c ::= (clause x e c) ())
            #:binding-forms
            (let*-awk c e #:refers-to c)
            (clause x e c #:refers-to x) #:exports (shadow x c))]

The @racket[let*-awk] form binds like Racket's @racket[let*], with
each clause's variable being active for the subsequent ones, but
the syntax is different with extra nesting inside the clauses:

@examples[#:label #f #:eval redex-eval
          (term (substitute (let*-awk (clause x y (clause y x ()))
                                      (+ x y z))
                            x
                            1)
                #:lang lc-bind+awkward-let*)
          (term (substitute (let*-awk (clause x y (clause y x ()))
                                      (+ x y z))
                            y
                            2)
                #:lang lc-bind+awkward-let*)]

 In order to get the same syntax as Racket's @racket[let*],
 we need to use the @racket[#:...bind] binding pattern
 annotation. A @racket[#:...bind] can appear wherever a
 @racket[_...] might appear, and it has the same function,
 namely indicating a repetition of the preceding pattern. In
 addition, however it comes with three extra pieces that
 follow the @racket[#:...bind] form that describe how the
 binding structure inside the repetition is handled. The
 first part is a name that can be used by a
 @racket[#:refers-to] outside of the repetition to indicate
 all of the exported variables of the sequence. The middle
 piece indicates the variables from a specific repetition of
 the ellipsis are exported to all subsequent repetitions of
 the ellipsis. The last piece is a @racket[beta] that moves
 backwards through the sequence, indicating what is exported
 from the last repetition of the sequence to the one before,
 from the one before to the one before that, and then finally
 from the first one to the export of the entire sequence (as
 named by the identifier in the first position).

 So, in this example, we use @racket[#:...bind] to express the
 scope of @racket[let*].

@examples[#:label #f #:eval redex-eval #:no-result
          (define-language lc-bind+let*
            (e ::= (let* ([x e] ...) e) natural x (+ e ...))
            (x ::= variable-not-otherwise-mentioned)
            #:binding-forms
            (let* ([x e] #:...bind (clauses x (shadow clauses x)))
              e_body #:refers-to clauses))]

It says that the name of the exported variables from the entire sequence
is @racket[clauses], which means that all of the variable exported
from the sequence in the second position of the @racket[let*] bind
variables in the body (thanks to the last @racket[#:refers-to] in the
example). The @racket[x] in the second position following the @racket[#:...bind]
says that @racket[x] is in scope for each of the subsequent @racket[[x e]] elements of
the sequence. The final @racket[(shadow clauses x)] says that the variables
in a subsequent @racket[clauses] are exported by the current one, as well as @racket[x],
which then is exported by the entire sequence.

@examples[#:label #f #:eval redex-eval
          (term (substitute (let* ([x y] [y x])
                              (+ x y z))
                            x
                            1)
                #:lang lc-bind+let*)
          (term (substitute (let* ([x y] [y x])
                              (+ x y z))
                            y
                            2)
                #:lang lc-bind+let*)]
}

@defidform[::=]{
A non-terminal's names and productions may be separated by the keyword @racket[::=].
Use of the @racket[::=] keyword outside a language definition is a syntax error.
}

@defidform[shadow]{Recognized specially within a @racket[define-language]. A @racket[shadow] is an error elsewhere.}

@defidform[nothing]{Recognized specially within a @racket[define-language]. A @racket[nothing] is an error elsewhere.}


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
    (e ::= ....     (code:comment "extend the previous `e' non-terminal")
       number
       +)
    (v ::= ....     (code:comment "extend the previous `v' non-terminal")
       number
       +))
]

extends @racket[_lc-lang] with two new alternatives (@racket[+] and @racket[number])
for the @racket[v] non-terminal, carries forward the @racket[e],
@racket[E], @racket[x], and @racket[y] non-terminals. Note that
the meaning of @racket[variable-not-otherwise-mentioned] adapts to the
language where it is used, so in this case it is equivalent to
@racket[(variable-except λ +)] because @racket[λ] and @racket[+] are
used as literals in this language.

The four-period ellipses indicates that the new language's
non-terminal has all of the alternatives from the original
language's non-terminal, as well as any new ones. If a
non-terminal occurs in both the base language and the
extension, the extension's non-terminal replaces the
originals. If a non-terminal only occurs in the base
language, then it is carried forward into the
extension. And, of course, @racket[define-extended-language] lets you add new
non-terminals to the language.

If a language has a group of multiple non-terminals
defined together, extending any one of those non-terminals
extends all of them.
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
it is @racket[#f], which acts as if it were a language with no @tech{binding forms}.
In that case, alpha-equivalence is the same thing as @racket[equal?].

The @racket[default-language] parameter is set to the appropriate language inside judgment forms and
metafunctions, and by @racket[apply-reduction-relation].
}

@defproc*[([(alpha-equivalent? [lang compiled-lang?] [lhs any/c] [rhs any/c]) boolean?]
           [(alpha-equivalent? [lhs any/c] [rhs any/c]) boolean?])]{
Returns @racket[#t] if (according to the binding specification in @racket[lang])
the bound names in @racket[lhs] and @racket[rhs] have the same structure and,
in everything but bound names, they are @racket[equal?]. If @racket[lang]
has no @tech{binding forms}, terms have no bound names and therefore
@racket[alpha-equivalent?] is the same as @racket[equal?].

If the @racket[lang] argument is not supplied, it
defaults to the value of @racket[(default-language)], which must not @racket[#f].
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
@tech{binding forms} are correctly defined.  However, @racket[substitute] may be significantly faster.}
