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

@title{Terms}

@declare-exporting[redex/reduction-semantics redex]

Object language expressions in Redex are written using
@racket[term]. It is similar to Racket's @racket[quote] (in
many cases it is identical) in that it constructs lists as
the visible representation of terms. 

The grammar of @deftech{term}s is (note that an ellipsis
stands for repetition unless otherwise indicated):

@(racketgrammar* #:literals (in-hole hole unquote unquote-splicing) 
   [term identifier
         (term-sequence ...)
         ,expr
         (in-hole term term)
         hole
         #t #f
         string]
   [term-sequence 
     term
     ,@expr
     (code:line ... (code:comment "literal ellipsis"))])

@itemize[

@item{A term written @racket[_identifier] is equivalent to the
corresponding symbol, unless the identifier is bound by
@racket[term-let], @racket[define-term], or a @|pattern| variable or
the identifier is @tt{hole} (as below).}

@item{A term written @racket[(_term-sequence ...)] constructs a list of
the terms constructed by the sequence elements.}

@item{A term written @racket[,_expr] evaluates
@racket[_expr] and substitutes its value into the term at
that point.}

@item{A term written @racket[,@_expr] evaluates the
@racket[_expr], which must produce a list. It then splices
the contents of the list into the expression at that point in the sequence.}

@item{A term written @racket[(in-hole #,tttterm #,tttterm)]
 is the dual to the @pattern @racket[in-hole] -- it accepts
 a context and an expression and uses @racket[plug] to combine
them.}

@item{A term written @racket[hole] produces a hole.}

@item{A term written as a literal boolean or a string
produces the boolean or the string.}
]

@defform*[[(term @#,tttterm) (term @#,tttterm #:lang lang-id)]]{

Used for construction of a term.

The @racket[term] form behaves similarly to @racket[quasiquote], except for a few special
forms that are recognized (listed below) and that names bound by
@racket[term-let] are implicitly substituted with the values that
those names were bound to, expanding ellipses as in-place sublists (in
the same manner as syntax-case patterns).

The optional @racket[#:lang] keyword must supply an identifier bound
by @racket[define-language], and adds a check that any symbol containing
an underscore in @tttterm could have been bound by a pattern in the
language referenced by @racket[lang-id].  In practice, this means that the
underscore must be preceded by a non-terminal in that language or a
built-in @ttpattern such as @racket[number].  This form of @racket[term]
is used internally by default, so this check is applied to terms 
that are constructed by Redex forms such as @racket[reduction-relation] 
and @racket[define-metafunction].

For example,

@racketblock[
(term-let ([body '(+ x 1)]
           [(expr ...) '(+ - (values * /))]
           [((id ...) ...) '((a) (b) (c d))])
  (term (let-values ([(id ...) expr] ...) body)))
]

evaluates to

@racketblock[
'(let-values ([(a) +] 
              [(b) -] 
              [(c d) (values * /)]) 
   (+ x 1))
]

It is an error for a term variable to appear in an
expression with an ellipsis-depth different from the depth
with which it was bound by @racket[term-let]. It is also an error
for two @racket[term-let]-bound identifiers bound to lists of
different lengths to appear together inside an ellipsis.
}

@defidform[hole]{ Recognized specially within
  @racket[term]. A @racket[hole] form is an
  error elsewhere.  }

@defidform[in-hole]{ Recognized specially within
  @racket[reduction-relation]. An @racket[in-hole] form is an
  error elsewhere.  }

@defform/subs[(term-let ([tl-pat expr] ...) body)
              ([tl-pat identifier (tl-pat-ele ...)]
               [tl-pat-ele tl-pat (code:line tl-pat ... (code:comment "a literal ellipsis"))])]{

Matches each given id pattern to the value yielded by
evaluating the corresponding expression and binds each variable in
the id pattern to the appropriate value (described
below). These bindings are then accessible to the @|tttterm|
syntactic form.

Note that each ellipsis should be the literal symbol consisting of
three dots (and the ... elsewhere indicates repetition as usual). If
@racket[tl-pat] is an identifier, it matches any value and binds it to
the identifier, for use inside @racket[term]. If it is a list, it
matches only if the value being matched is a list value and only if
every subpattern recursively matches the corresponding list
element. There may be a single ellipsis in any list pattern; if one is
present, the pattern before the ellipses may match multiple adjacent
elements in the list value (possibly none).

This form is a lower-level form in Redex, and not really designed to
be used directly. For @racket[let]-like forms that use
Redex's full pattern matching facilities, see @racket[redex-let],
@racket[redex-let*], @racket[term-match], @racket[term-match/single].
}

@defform[(redex-let language ([@#,ttpattern expression] ...) body ...+)]{
Like @racket[term-let] but the left-hand sides are Redex patterns, 
interpreted according to the specified language. It is a syntax
error for two left-hand sides to bind the same pattern variable.

This form raises an exception recognized by @racket[exn:fail:redex?] 
if any right-hand side does not match its left-hand side in exactly one 
way. 

In some contexts, it may be more efficient to use @racket[term-match/single]
(lifted out of the context).
}

@defform[(redex-let* language ([@#,ttpattern expression] ...) body ...+)]{
The @racket[let*] analog of @racket[redex-let].
}

@defform[(define-term identifier @#,tttterm)]{
Defines @racket[identifier] for use in @|tterm| templates.}

@defform[(term-match language [@#,ttpattern expression] ...)]{

Produces a procedure that accepts term (or quoted)
expressions and checks them against each pattern. The
function returns a list of the values of the expression
where the pattern matches. If one of the patterns matches
multiple times, the expression is evaluated multiple times,
once with the bindings in the pattern for each match.

When evaluating a @racket[term-match] expression, the patterns are
compiled in an effort to speed up matching. Using the procedural
result multiple times to avoid compiling the patterns multiple times.
}

@defform[(term-match/single language [@#,ttpattern expression] ...)]{

Produces a procedure that accepts term (or quoted)
expressions and checks them against each pattern. The
function returns the expression behind the first successful
match. If that pattern produces multiple matches, an error
is signaled. If no patterns match, an error is signaled.

The @racket[term-match/single] form raises an exception recognized by @racket[exn:fail:redex?] if
no clauses match or if one of the clauses matches multiple ways.

When evaluating a @racket[term-match/single] expression, the patterns
are compiled in an effort to speed up matching. Using the procedural
result multiple times to avoid compiling the patterns multiple times.
}

@defproc[(plug [context any/c] [expression any/c]) any]{

The first argument to this function is an term to
plug into. The second argument is the term to replace
in the first argument. It returns the replaced term. This is
also used when a @racket[term] sub-expression contains @tt{in-hole}.
}

@defproc[(variable-not-in [t any/c] [prefix symbol?]) symbol?]{

A helper function that accepts a term and a
variable. It returns a symbol that not in the term, where the
variable has @racket[prefix] as a prefix.

}

@defproc[(variables-not-in [t any/c] [vars (listof symbol?)]) (listof symbol?)]{

Like @racket[variable-not-in], create variables that do
no occur in @racket[t]---but returning a list of
such variables, one for each variable in its second
argument. 

The @racket[variables-not-in] function does not expect the symbols in
@racket[vars] to be distinct, but it does produce a list of distinct
symbols.
}

@defproc[(exn:fail:redex? [v any/c]) boolean?]{
  Returns @racket[#t] if its argument is a Redex exception record, and
  @racket[#f] otherwise.
}
