#lang scribble/manual
@(require "common.rkt"
          (for-label racket/base
                     (except-in racket/gui make-color)
                     racket/pretty
                     racket/contract
                     mrlib/graph
                     (except-in 2htdp/image make-pen text)
                     (only-in pict pict? text dc-for-text-size text-style/c
                              vc-append hbl-append vl-append)
                     redex))

@title{Languages}

@declare-exporting[redex/reduction-semantics redex]

@defform/subs[#:literals (::=)
              (define-language lang-name 
                non-terminal-def ...
                maybe-binding-spec)
              ([non-terminal-def (non-terminal-name ...+ ::= @#,ttpattern ...+)
                                 (non-terminal-name @#,ttpattern ...+)
                                 ((non-terminal-name ...+) @#,ttpattern ...+)]
               [maybe-binding-spec (code:line)
                                   (code:line #:binding-forms binding-declaration ...)])]{

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

@racketblock[
  (define-language lc-lang
    (e (e e ...)
       x
       v)
    (c (v ... c e ...)
       hole)
    (v (λ (x ...) e))
    (x variable-not-otherwise-mentioned))
]

with non-terminals @racket[e] for the expression language, @racket[x] for
variables, @racket[c] for the evaluation contexts and @racket[v] for values.

Non-terminals used in @racket[define-language] are not bound in
@pattech[side-condition] patterns and duplicates are not constrained
to be the same unless they have underscores in them.

When @racket[maybe-binding-spec] is provided, it declares binding specifications
for certain forms in the language. For a detailed explanation of how to declare
and use binding specifications, see @secref["sec:binding"].
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
