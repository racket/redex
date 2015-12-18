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

@title{Reduction Relations}

@declare-exporting[redex/reduction-semantics redex]

@defform/subs[#:literals (--> fresh side-condition side-condition/hidden
                          where where/hidden judgment-holds with)
              (reduction-relation language domain base-arrow
                                  reduction-case ...
                                  shortcuts)
              ([domain (code:line) (code:line #:domain @#,ttpattern)]
               [base-arrow (code:line) (code:line #:arrow base-arrow-name)]
               [reduction-case (arrow-name @#,ttpattern @#,tttterm red-extras ...)]
               [red-extras rule-name
                           (fresh fresh-clause ...)
                           (side-condition racket-expression)
                           (where @#,ttpattern @#,tttterm)
                           (judgment-holds (judgment-form-id pat/term ...))
                           (side-condition/hidden racket-expression)
                           (where/hidden @#,ttpattern @#,tttterm)]
               [shortcuts (code:line)
                          (code:line with shortcut ...)]
               [shortcut [(old-arrow-name @#,ttpattern @#,tttterm)
                          (new-arrow-name identifier identifier)]]
               [rule-name identifier
                          string 
                          (computed-name racket-expression)]
               [fresh-clause var ((var1 ...) (var2 ...))]
               [pat/term @#,ttpattern
                         @#,tttterm])]{

Defines a reduction relation case-wise, one case for each of the
@racket[reduction-case] clauses. 

The optional @racket[domain] clause provides a contract for the
relation, in the form of a pattern that defines the relation's 
domain and codomain.

The @racket[arrow-name] in each @racket[reduction-case] clause is either 
@racket[base-arrow-name] (default @racket[-->]) or an arrow name
defined by @racket[shortcuts] (described below). In either case, 
the @|pattern| refers to @racket[language] and binds variables in
the corresponding @|tterm|. Following the @|pattern| and @|tterm|
can be the name of the reduction rule and declarations of fresh
variables and side-conditions.

For example, the expression

@racketblock[
  (reduction-relation
   lc-lang
   (--> (in-hole c_1 ((λ (variable_i ...) e_body) v_i ...))
        (in-hole c_1 ,(foldl lc-subst 
                             (term e_body) 
                             (term (v_i ...)) 
                             (term (variable_i ...))))
        beta-v))
]

defines a reduction relation for the @tech{@racket[_lc-lang]} grammar.

A rule's name (used in @seclink["Typesetting" "typesetting"],
the @racket[stepper], @racket[traces], and 
@racket[apply-reduction-relation/tag-with-names]) can be given
as a literal (an identifier or a string) or as an expression
that computes a name using the values of the bound pattern
variables (much like the rule's right-hand side). Some operations
require literal names, so a rule definition may provide both
a literal name and a computed name. In particular, only rules that include
a literal name may be replaced using @racket[extend-reduction-relation],
used as breakpoints in the @racket[stepper], and selected using
@racket[render-reduction-relation-rules]. The output of 
@racket[apply-reduction-relation/tag-with-names], @racket[traces], and
the @racket[stepper] prefers the computed name, if it exists. Typesetting
a rule with a computed name shows the expression that computes the name
only when the rule has no literal name or when it would not typeset in 
pink due to @racket[with-unquote-rewriter]s in the context; otherwise,
the literal name (or nothing) is shown.

Fresh variable clauses generate variables that do not
occur in the term being reduced. If the @racket[fresh-clause] is a
variable, that variable is used both as a binding in the
@|tterm| and as the prefix for the freshly generated
variable. (The variable does not have to be
a non-terminal in the language of the reduction relation.)

The second form of @racket[fresh-clause]s generates 
a sequence of variables. In that case, the ellipses
are literal ellipses; that is, you must actually write
ellipses in your rule. The variable @racket[var1] is like the
variable in first case of a @racket[fresh-clause]; namely it is
used to determine the prefix of the generated variables and
it is bound in the right-hand side of the reduction rule,
but unlike the single-variable fresh clause, it is bound to
a sequence of variables. The variable @racket[var2] is used to
determine the number of variables generated and @racket[var2] must be
bound by the left-hand side of the rule.

The expressions within @as-index{@racket[side-condition] clause}s
and @as-index{@racket[side-condition/hidden] clause}s are collected with @racket[and] and
used as guards on the case being matched. The argument to each
side-condition should be a Racket expression, and the pattern
variables in the @|ttpattern| are bound in that expression. A
@racket[side-condition/hidden] clause is the same as
a @racket[side-condition] clause, except that the condition is not
rendered when typesetting via @racketmodname[redex/pict].

Each @deftech{@racket[where] clause} acts as a side condition requiring a
successful pattern match, and it can bind pattern variables in the
side-conditions (and @racket[where] clauses) that follow and in the
metafunction result. The bindings are the same as bindings in a
@racket[term-let] expression. A @as-index{@racket[where/hidden] clause} is the
same as a @racket[where] clause, but the clause is not
rendered when typesetting via @racketmodname[redex/pict].

Each @racket[judgment-holds] clause acts like a @racket[where] clause, where
the left-hand side pattern incorporates each of the patterns used in the 
judgment form's output positions.

Each @racket[shortcut] clause defines arrow names in terms of 
@racket[base-arrow-name] and earlier @racket[shortcut] definitions.
The left- and right-hand sides of a @racket[shortcut] definition 
are identifiers, not @|pattern|s and @|tterm|s. These identifiers
need not correspond to non-terminals in @racket[language] and if
they do, that correspondence is ignored (more precisely, the
shortcut is @emph{not} restricted only to terms matching the non-terminal).

For example, this expression

@racketblock[
  (reduction-relation
   lc-num-lang
   (==> ((λ (variable_i ...) e_body) v_i ...)
        ,(foldl lc-subst 
                (term e_body) 
                (term (v_i ...)) 
                (term (variable_i ...))))
   (==> (+ number_1 ...)
        ,(apply + (term (number_1 ...))))
   
   with
   [(--> (in-hole c_1 a) (in-hole c_1 b))
    (==> a b)])
]
  
defines reductions for the λ-calculus with numbers,
where the @tt{==>} shortcut is defined by reducing in the context
@tt{c}.

A @racket[fresh] clause in @racket[reduction-case] defined by shortcut
refers to the entire term, not just the portion matched by the left-hand
side of shortcut's use.
}

@defform[(extend-reduction-relation reduction-relation language more ...)]{

This form extends the reduction relation in its first
argument with the rules specified in @racket[more]. They should
have the same shape as the rules (including the @racket[with]
clause) in an ordinary @racket[reduction-relation].

If the original reduction-relation has a rule with the same
name as one of the rules specified in the extension, the old
rule is removed.

In addition to adding the rules specified to the existing
relation, this form also reinterprets the rules in the
original reduction, using the new language.
}
@defproc[(union-reduction-relations [r reduction-relation?] ...) 
         reduction-relation?]{

Combines all of the argument reduction relations into a
single reduction relation that steps when any of the
arguments would have stepped.
}

@defproc[(reduction-relation->rule-names [r reduction-relation?])
         (listof symbol?)]{

Returns the names of the reduction relation's named clauses.
}

@defform[(compatible-closure reduction-relation lang non-terminal)]{

This accepts a reduction, a language, the name of a
non-terminal in the language and returns the compatible
closure of the reduction for the specified non-terminal.
}

@defform[(context-closure reduction-relation lang pattern)]{

This accepts a reduction, a language, a pattern representing
a context (i.e., that can be used as the first argument to
@racket[in-hole]; often just a non-terminal) in the language and
returns the closure of the reduction in that context.
}

@defproc[(reduction-relation? [v any/c]) boolean?]{
  Returns @racket[#t] if its argument is a reduction-relation, and
  @racket[#f] otherwise.
}

@defproc[(apply-reduction-relation [r (or/c reduction-relation? IO-judgment-form?)]
                                   [t any/c])
         (listof any/c)]{

This accepts reduction relation, a term, and returns a
list of terms that the term reduces to.
}

@defproc[(apply-reduction-relation/tag-with-names
          [r (or/c reduction-relation? IO-judgment-form?)]
          [t any/c])
         (listof (list/c (or/c #f string?) any/c))]{

Like @racket[apply-reduction-relation], but the result indicates the
names of the reductions that were used.
}

@defproc[(apply-reduction-relation*
          [r (or/c reduction-relation? IO-judgment-form?)]
          [t any/c]
          [#:all? all boolean? #f]
          [#:cache-all? cache-all? boolean? (or all? (current-cache-all?))]
          [#:stop-when stop-when (-> any/c any) (λ (x) #f)])
         (listof any/c)]{

Accepts a reduction relation and a
term. Starting from @racket[t], it follows every reduction
path and returns either all of the terms that do not reduce further
or all of the terms, if @racket[all?] is @racket[#t].
If there are infinite reduction
sequences that do not repeat, this function will not
terminate (it does terminate if the only infinite reduction paths are cyclic).

If the @racket[cache-all?] argument is @racket[#t], then @racket[apply-reduction-relation*]
keeps a cache of all visited terms when traversing the graph and does not revisit
any of them. This cache can, in some cases, use a lot of memory, so it is off by
default and the cycle checking happens by keeping track only of the current path
it is traversing through the reduction graph.

The @racket[stop-when] argument controls the stopping criterion. Specifically, it is
called with each term that @racket[apply-reduction-relation*] encounters. If it
ever returns a true value (anything except @racket[#f]), then @racket[apply-reduction-relation*]
considers the term to be irreducible (and so returns it and does not try to
reduce it further).

}

@defparam[current-cache-all? cache-all? boolean?]{
  Controls the behavior of @racket[apply-reduction-relation*]
  and @racket[test-->>]'s cycle checking. See @racket[apply-reduction-relation*]
  for more details.
}

@examples[
#:eval redex-eval
       (define-language empty-lang)
       (define R
         (reduction-relation
          empty-lang
          (--> 0 1)
          (--> 0 2)
          (--> 2 3)
          (--> 3 3)))
       (apply-reduction-relation R 0)
       (apply-reduction-relation* R 0)]

@defidform[-->]{ Recognized specially within
  @racket[reduction-relation]. A @racket[-->] form is an
  error elsewhere.  }

@defidform[fresh]{ Recognized specially within
  @racket[reduction-relation]. A @racket[fresh] form is an
  error elsewhere.  }

@defidform[with]{ Recognized specially within
  @racket[reduction-relation]. A @racket[with] form is an
  error elsewhere.  }

@(close-eval redex-eval)
