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

@title{Patterns}

@defmodule*/no-declare[(redex/reduction-semantics)]
@declare-exporting[redex/reduction-semantics redex]

This section covers Redex's @deftech{pattern} language, which is used
in many of Redex's forms. Patterns are matched against @tech{terms},
which are represented as S-expressions.

Pattern matching uses a cache---including caching the results of
side-conditions---so after a pattern has matched a given term, Redex
assumes that the pattern will always match the term.

In the following grammar, literal identifiers (such as
@racket[pat:any]) are matched symbolically, as opposed to using the
identifier's lexical binding:

@(racketgrammar*
   #:literals (pat:any pat:_ pat:number pat:natural pat:integer
               pat:real pat:string pat:boolean pat:variable
               pat:variable-except pat:variable-prefix
               pat:variable-not-otherwise-mentioned
               pat:hole pat:symbol pat:name pat:in-hole pat:hide-hole
               pat:side-condition pat:cross
               pat:pattern-sequence pat:other-literal)
   [pattern pat:any
            pat:_
            pat:number 
            pat:natural
            pat:integer
            pat:real
            pat:string 
            pat:boolean
            pat:variable 
            (pat:variable-except id ...)
            (pat:variable-prefix id)
            pat:variable-not-otherwise-mentioned
            pat:hole
            pat:symbol
            (pat:name id pattern)
            (pat:in-hole pattern pattern)
            (pat:hide-hole pattern)
            (pat:side-condition pattern guard-expr)
            (pat:cross id)
            (pat:pattern-sequence ...)
            pat:other-literal]
   [pattern-sequence 
     pattern
     (code:line ... (code:comment "literal ellipsis"))
     ..._id])

@(define can-underscore
   @list{Like @racket[pat:number], this @pattern can be suffixed with an underscore
         and additional characters to create a binding.})

@itemize[

@item{The @defpattech[any] @pattern matches any term.
This @pattern may also be suffixed with an underscore and another
identifier, in which case a match binds the full name (as if it
were an implicit @pattech[name] @pattern) and match the portion
before the underscore.
}

@item{The @defpattech[_] @pattern matches any term,
but does not bind @pattech[_] as a name, nor can it be suffixed to bind a name.
}

@item{The @defpattech[number] @pattern matches any number.

      The @racket[pat:number] identifier can be suffixed with an underscore and additional
         characters, in which case the @pattern binds the full name (as if it
         were an implicit @pattech[name] @pattern) when matching the portion
         before the underscore. For example, the pattern

          @racketblock[number_1]

         matches the same as @racket[pat:number], but it also binds the
         identifier @racket[number_1] to the matching portion of a term.

         When the same underscore suffix is used for multiple
         instances if @racket[pat:number] within a larger pattern, then the
         overall pattern matches only when all of the instances match the
         same number.
}

@item{The @defpattech[natural] @pattern matches any exact 
non-negative integer.
      @can-underscore
}

@item{The @defpattech[integer] @pattern matches any exact integer.
      @can-underscore
}

@item{The @defpattech[real] @pattern matches any real number.
      @can-underscore
}

@item{The @defpattech[string] @pattern matches any string. 
      @can-underscore
}

@item{The @defpattech[boolean] @pattern matches @racket[#true] and @racket[#false]
(which are the same as @racket[#t] and @racket[#f], respectively).
@can-underscore
}

@item{The @defpattech[variable] @pattern matches any symbol.
      @can-underscore
}

@item{The @defpattech[variable-except] @pattern matches any symbol except those
listed in its argument. This @pattern is useful for ensuring that
reserved words in the language are not accidentally captured by
variables. 
}

@item{ The @defpattech[variable-prefix] @pattern matches any symbol
that begins with the given prefix. }

@item{The @defpattech[variable-not-otherwise-mentioned] @pattern matches any
symbol except those that are used as literals elsewhere in
the language.
}

@item{The @defpattech[hole] @pattern matches anything when inside
the first argument to an @pattech[in-hole] @|pattern|. Otherwise, 
it matches only a hole.
}

@item{The @defpattech[symbol] @pattern stands for a literal symbol that must
match exactly, unless it is the name of a non-terminal in a
relevant language or contains an underscore. 

If @racket[pat:symbol] is a non-terminal, it matches any of the right-hand
sides of the non-terminal. If the non-terminal appears
twice in a single pattern, then the match is constrained
to expressions that are the same, unless the pattern is part
of a @racket[define-language] definition or a contract (e.g., in
@racket[define-metafunction], @racket[define-judment-form], or
@racket[define-relation])
in which case there is no constraint. Also, the
non-terminal will be bound in the expression in any
surrounding @pattech[side-condition] patterns unless there the
pattern is in a @racket[define-language] definition.

If @racket[pat:symbol] is a non-terminal followed by an underscore,
for example @tt{e_1}, it is implicitly the same as a name @pattern
that matches only the non-terminal, @tt{(@pattech[name] e_1 e)} for the
example. Accordingly, repeated uses of the same name are
constrained to match the same expression.

If the symbol is a non-terminal followed by @tt{_!_}, for example
@tt{e_!_1}, it is also treated as a @|pattern|, but repeated uses of
the same @pattern are constrained to be different. For
example, this @|pattern|:

@racketblock[(e_!_1 e_!_1 e_!_1)]

matches lists of three @tt{e}s, but where all three of them are
distinct.

If the @tt{_!_} is used under the ellipsis then the ellipsis is effectively
ignored while checking to see if the @tt{e}s are different. For example,
the @pattern @racket[(e_!_1 ...)] matches any sequence of @tt{e}s, as long
as they are all distinct. Also, unlike @tt{e_1} patterns, the nesting depth
of @tt{_!_} patterns do not have to be the same. For example, this pattern:

@racketblock[(e_!_1 ... e_!_1)]

matches all sequences of @racket[e]s that have at least one element, as long
as they are all distinct.

Unlike a @tt{_} @|pattern|, the @tt{_!_} @|pattern|s do not bind names.

If @tt{_} names and @tt{_!_} are mixed, they are treated as
separate. That is, this @pattern @tt{(e_1 e_!_1)} matches just the
same things as @tt{(e e)}, but the second doesn't bind any
variables.

If the symbol otherwise has an underscore, it is an error.
}

@item{The @pattern @tt{(@defpattech[name] _id @ttpattern)}
matches @ttpattern and binds using it to the name @racket[_id]. 
}

@item{The @tt{(@defpattech[in-hole] @ttpattern @ttpattern)} @pattern
matches the first @|ttpattern|, looking for a way to decompose the
term such that the second @ttpattern matches at some sub-expression
where the @racket[hole] appears while matching the first @|ttpattern|.

The first @ttpattern must be a pattern that matches with exactly one hole.
}

@item{The @tt{(@defpattech[hide-hole] @ttpattern)} @pattern matches what
the embedded @ttpattern matches but if the @pattern matcher is
looking for a decomposition, it ignores any holes found in
that @|ttpattern|.
}

@item{The @tt{(@defpattech[side-condition] @ttpattern _guard-expr)} @pattern
matches what the embedded @ttpattern matches, and then @racket[_guard-expr]
is evaluated. If @racket[_guard-expr] produces @racket[#f], the @pattern fails
to match, otherwise the @pattern matches. Any
occurrences of @racket[pat:name] in the @pattern (including those implicitly
present via @tt{_} patterns) are bound using @racket[term-let] in
@racket[_guard-expr]. 
}

@item{The @tt{(@defpattech[cross] _id)} @pattern is used for the compatible
closure functions. If the language contains a non-terminal with the
same name as @racket[_id], the @pattern @racket[(cross _id)] matches the
context that corresponds to the compatible closure of that
non-terminal.
}

@item{The @tt{(@defpattech[pattern-sequence] ...)}
@pattern matches a term
list, where each pattern-sequence element matches an element
of the list. In addition, if a list @pattern contains an
ellipsis, the ellipsis is not treated as a literal, instead
it matches any number of duplicates of the @pattern that
came before the ellipses (including 0). Furthermore, each
@tt{(@pattech[name] symbol @ttpattern)} in the duplicated @pattern binds a
list of matches to @tt{symbol}, instead of a single match.  (A
nested duplicated @pattern creates a list of list matches,
etc.) Ellipses may be placed anywhere inside the row of
@|pattern|s, except in the first position or immediately after
another ellipses.

Multiple ellipses are allowed. For example, this @|pattern|:

@racketblock[((name x a) ... (name y a) ...)]

matches this term:

@racketblock[(term (a a))]

three different ways. One where the first @tt{a} in the @pattern
matches nothing, and the second matches both of the
occurrences of @tt{a}, one where each named @pattern matches a
single @tt{a} and one where the first matches both and the
second matches nothing.

If the ellipses is named (i.e., has an underscore and a name
following it, like a variable may), the @pattern matcher
records the length of the list and ensures that any other
occurrences of the same named ellipses must have the same
length. 

As an example, this @|pattern|:

@racketblock[((name x a) ..._1 (name y a) ..._1)]

only matches this term:

@racketblock[(term (a a))]

one way, with each named @pattern matching a single a. Unlike
the above, the two @|pattern|s with mismatched lengths is ruled
out, due to the underscores following the ellipses.

Also, like underscore @|pattern|s above, if an underscore
@pattern begins with @tt{..._!_}, then the lengths must be
different.

Thus, with the @|pattern|:

@racketblock[((name x a) ..._!_1 (name y a) ..._!_1)]

and the expression

@racketblock[(@#,tttterm (a a))]

two matches occur, one where @tt{x} is bound to @racket['()] and
@tt{y} is bound to @racket['(a a)] and one where @tt{x} is bound to
@racket['(a a)] and @tt{y} is
bound to @racket['()].

}

@item{The @defpattech[other-literal] @pattern stands for a literal
      value---such as a number, boolean, or string---that must match
      exactly.}
]

@history[#:changed "1.8" @list{
          Non-terminals are syntactically classified
          as either always producing exactly one hole or may
          produce some other number of holes,
          and the first argument to @racket[in-hole] is allowed
          to accept only patterns that produce exactly one hole.}]

@defform*[[(redex-match lang @#,ttpattern term-expr)
           (redex-match lang @#,ttpattern)]]{
          
If @racket[redex-match] is given a @racket[term-expr], it
matches the pattern (in the language) against the result of
@racket[term-expr]. The result is @racket[#f] or a list of match
structures describing the matches (see @racket[match?] and 
@racket[match-bindings]).

If @racket[redex-match] has only a @racket[lang] and @ttpattern,
the result is a procedure for efficiently testing whether terms
match the pattern with respect to the language @racket[lang]. The
procedure accepts a single term and returns @racket[#f] or
a list of match structures describing the matches.

@examples[#:eval 
          redex-eval
          (define-language nums
            (AE number
                (+ AE AE)))
          (redex-match nums
                       (+ AE_1 AE_2)
                       (term (+ (+ 1 2) 3)))
          (redex-match nums
                       (+ AE_1 (+ AE_2 AE_3))
                       (term (+ (+ 1 2) 3)))
          (redex-match nums
                       (+ AE_1 AE_1)
                       (term (+ (+ 1 2) 3)))]

}

@defform*[[(redex-match? lang @#,ttpattern any)
           (redex-match? lang @#,ttpattern)]]{
          
Like @racket[redex-match], but returns only a boolean
indicating whether the match was successful.

@examples[#:eval 
          redex-eval
          (define-language nums
            (AE number
                (+ AE AE)))
          (redex-match? nums
                        (+ AE_1 AE_2)
                        (term (+ (+ 1 2) 3)))
          (redex-match? nums
                        (+ AE_1 AE_1)
                        (term (+ (+ 1 2) 3)))]

}

@defproc[(match? [val any/c]) boolean?]{

Determines whether a value is a @tt{match} structure.
}

@defproc[(match-bindings [m match?]) (listof bind?)]{

Returns a list of @racket[bind] structs that
binds the pattern variables in this match.
}

@defstruct[bind ([name symbol?] [exp any/c])]{

Instances of this struct are returned by @racket[redex-match].
Each @racket[bind] associates a name with an s-expression from the
language, or a list of such s-expressions if the corresponding @pattech[name]
clause is followed by an ellipsis.  Nested ellipses produce
nested lists.
}

@defparam[caching-enabled? on? boolean?]{
  When this parameter is @racket[#t] (the default), Redex caches the results of 
  pattern matching, metafunction, and judgment-form evaluation. There is a separate cache for
  each pattern, metafunction, and judgment-form; when one fills (see @racket[set-cache-size!]),
  Redex evicts all of the entries in that cache.

  Caching should be disabled when matching a pattern that depends on values
  other than the in-scope pattern variables or evaluating a metafunction or
  judgment-form that reads or writes mutable external state.
  
  @history[#:changed "1.6" @list{Extended caching to cover judgment forms.}]
}

@defproc[(set-cache-size! [size positive-integer?]) void?]{
Changes the size of the per-pattern and per-metafunction caches.

The default size is @racket[63].
}

@defparam[check-redundancy check? boolean?]{
  Ambiguous patterns can slow down
  Redex's pattern matching implementation significantly. To help debug
  such performance issues, set the @racket[check-redundancy]
  parameter to @racket[#t]. A true value causes Redex to, at runtime,
  report any redundant matches that it encounters.

  @history[#:changed "1.9" @list{Corrected spelling error, from
             @racket[check-redudancy] to @racket[check-redundancy]}]
}


@(close-eval redex-eval)
