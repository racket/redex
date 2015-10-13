#lang scribble/manual
@(require "common.rkt"
          scribble/eval
          (for-label racket/base
                     (except-in racket/gui make-color)
                     racket/pretty
                     racket/contract
                     mrlib/graph
                     (except-in 2htdp/image make-pen text)
                     (only-in pict pict? text dc-for-text-size text-style/c
                              vc-append hbl-append vl-append)
                     redex))

@(define redex-eval (make-base-eval))
@(interaction-eval #:eval redex-eval (require redex/reduction-semantics))

@(define (examples-link relative-path dir? text)
   (link (format "http://git.racket-lang.org/plt/~a/HEAD:/collects/redex/examples/~a"
                 (if dir? "tree" "blob")
                 relative-path)
         (filepath text)))

@title{Other Relations}

@declare-exporting[redex/reduction-semantics redex]

@defform/subs[#:literals (: -> 
                          where side-condition 
                          side-condition/hidden where/hidden 
                          judgment-holds)
             (define-metafunction language
               metafunction-contract
               [(name @#,ttpattern ...) @#,tttterm metafunction-extras ...] 
               ...)
             ([metafunction-contract (code:line) 
                                     (code:line id : @#,ttpattern-sequence ... -> range
                                                maybe-pre-condition
                                                maybe-post-condition)]
              [maybe-pre-condition (code:line #:pre @#,tttterm)
                                   (code:line)]
              [maybe-post-condition (code:line #:post @#,tttterm)
                                    (code:line)]
              [range @#,ttpattern
                     (code:line @#,ttpattern or range)
                     (code:line @#,ttpattern ∨ range)
                     (code:line @#,ttpattern ∪ range)]
              [metafunction-extras (side-condition racket-expression)
                                   (side-condition/hidden racket-expression)
                                   (where pat @#,tttterm)
                                   (where/hidden pat @#,tttterm)
                                   (judgment-holds 
                                    (judgment-form-id pat/term ...))
                                   (clause-name name)
                                   (code:line or @#,tttterm)])]{

The @racket[define-metafunction] form builds a function on
terms according to the pattern and right-hand-side
expressions. The first argument indicates the language used
to resolve non-terminals in the pattern expressions. Each of
the rhs-expressions is implicitly wrapped in @|tttterm|. 

The contract, if present, is matched against every input to
the metafunction and, if the match fails, an exception is raised.
If present, the term inside the @racket[maybe-pre-condition] is evaluated
after a successful match to the input pattern in the contract (with
any variables from the input contract bound). If
it returns @racket[#f], then the input contract is considered to not
have matched and an error is also raised. When a metafunction
returns, the expression in the @racket[maybe-post-condition] is
evaluated (if present), with any variables from the input or output 
contract bound.

The @racket[side-condition], @racket[hidden-side-condition],
@racket[where], and @racket[where/hidden] clauses behave as
in the @racket[reduction-relation] form.

The resulting metafunction raises an exception recognized by @racket[exn:fail:redex?] if
no clauses match or if one of the clauses matches multiple ways
(and that leads to different results for the different matches).

The @racket[side-condition] extra is evaluated after a successful match
to the corresponding argument pattern. If it returns @racket[#f],
the clause is considered not to have matched, and the next one is tried.
The @racket[side-condition/hidden] extra behaves the same, but is
not typeset.

The @racket[where] and @racket[where/hidden] extra are like
@racket[side-condition] and @racket[side-condition/hidden],
except the match guards the clause.

The @racket[judgment-holds] clause is like @racket[side-condition]
and @racket[where], except the given judgment must hold for the
clause to be taken.

The @racket[clause-name] is used only when typesetting. See
@racket[metafunction-cases].

The @racket[or] clause is used to define a form of conditional
right-hand side of a metafunction. In particular, if any of the
@racket[where] or @racket[side-condition] clauses fail, then
evaluation continues after an @racket[or] clause, treating the
term that follows as the result (subject to any subsequent
@racket[where] clauses or @racket[side-condition]s. This construction
is equivalent to simply duplicating the left-hand side of the
clause, once for each @racket[or] expression, but signals to
the typesetting library to use a large left curly brace to group
the conditions in the @racket[or].

Note that metafunctions are assumed to always return the same results
for the same inputs, and their results are cached, unless
@racket[caching-enabled?] is set to @racket[#f]. Accordingly, if a
metafunction is called with the same inputs twice, then its body is
only evaluated a single time.

As an example, these metafunctions finds the free variables in
an expression in the @racket[_lc-lang] above:

@racketblock[
    (define-metafunction lc-lang
      free-vars : e -> (x ...)
      [(free-vars (e_1 e_2 ...))
       (∪ (free-vars e_1) (free-vars e_2) ...)]
      [(free-vars x) (x)]
      [(free-vars (λ (x ...) e))
       (- (free-vars e) (x ...))])
]

The first argument to define-metafunction is the grammar
(defined above). Following that are three cases, one for
each variation of expressions (e in @racket[_lc-lang]). The free variables of an
application are the free variables of each of the subterms;
the free variables of a variable is just the variable
itself, and the free variables of a λ expression are
the free variables of the body, minus the bound parameters.

Here are the helper metafunctions used above.

@racketblock[
    (define-metafunction lc-lang
      ∪ : (x ...) ... -> (x ...)
      [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
       (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
      [(∪ (x_1 ...))
       (x_1 ...)]
      [(∪) ()])
    
    (define-metafunction lc-lang
      - : (x ...) (x ...) -> (x ...)
      [(- (x ...) ()) (x ...)]
      [(- (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
       (- (x_1 ... x_3 ...) (x_2 x_4 ...))
       (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
      [(- (x_1 ...) (x_2 x_3 ...))
       (- (x_1 ...) (x_3 ...))])
]

Note the side-condition in the second case of @racket[-]. It
ensures that there is a unique match for that case. Without
it, @racket[(term (- (x x) x))] would lead to an ambiguous
match.

@history[#:changed "1.4" @list{Added @racket[#:post] conditions.}
         #:changed "1.5" @list{Added @racket[or] clauses.}]
}

@defform[(define-metafunction/extension f language 
           metafunction-contract
           [(g @#,ttpattern ...) @#,tttterm metafunction-extras ...] 
           ...)]{

Defines a metafunction @racket[g] as an extension of an existing
metafunction @racket[f]. The metafunction @racket[g] behaves as 
if @racket[f]'s clauses were appended to its definition (with 
occurrences of @racket[f] changed to @racket[g] in the inherited
clauses).
}

For example, @racket[define-metafunction/extension] may be used to extend
the free-vars function above to the forms introduced by the language
@racket[_lc-num-lang].
                
@racketblock[
(define-metafunction/extension free-vars lc-num-lang
  free-vars-num : e -> (x ...)
  [(free-vars-num number) 
   ()]
  [(free-vars-num (+ e_1 e_2))
   (∪ (free-vars-num e_1)
      (free-vars-num e_2))])
]
                
@defform[(in-domain? (metafunction-name @#,tttterm ...))]{
Returns @racket[#t] if the inputs specified to @racket[metafunction-name] are
legitimate inputs according to @racket[metafunction-name]'s contract,
and @racket[#f] otherwise.
}

@defform/subs[#:literals (I O where where/hidden side-condition side-condition/hidden etc.)
             (define-judgment-form language
               mode-spec
               contract-spec
               invariant-spec
               rule rule ...)
             ([mode-spec (code:line #:mode (form-id pos-use ...))]
              [contract-spec (code:line) 
                             (code:line #:contract (form-id @#,ttpattern-sequence ...))]
              [invariant-spec (code:line #:inv @#,tttterm)
                                   (code:line)]
              [pos-use I
                       O]
              [rule [premise
                     ... 
                     dashes rule-name
                     conclusion]
                    [conclusion 
                     premise 
                     ...
                     rule-name]]
              [conclusion (form-id pat/term ...)]
              [premise (code:line (judgment-form-id pat/term ...) maybe-ellipsis)
                       (where @#,ttpattern @#,tttterm)
                       (where/hidden @#,ttpattern @#,tttterm)
                       (side-condition @#,tttterm)
                       (side-condition/hidden @#,tttterm)]
              [rule-name (code:line)
                         string
                         non-ellipsis-non-hypens-var]
              [pat/term @#,ttpattern
                        @#,tttterm]
              [maybe-ellipsis (code:line)
                              ...]
              [dashes ---
                      ----
                      -----
                      etc.])]{
Defines @racket[form-id] as a relation on terms via a set of inference rules.
Each rule must be such that its premises can be evaluated left-to-right
without ``guessing'' values for any of their pattern variables. Redex checks this
property using the mandatory @racket[mode-spec] declaration, which partitions positions
into inputs @racket[I] and outputs @racket[O]. Output positions in conclusions
and input positions in premises must be @|tttterm|s; input positions in conclusions and 
output positions in premises must be @|ttpattern|s. When the optional @racket[contract-spec] 
declaration is present, Redex dynamically checks that the terms flowing through
these positions match the provided patterns, raising an exception recognized by 
@racket[exn:fail:redex] if not. The term in the optional @racket[invariant-spec] is
evaluated after the output positions have been computed and the contract has matched
successfully, with variables from the contract bound; a result of @racket[#f] is
considered to be a contract violation and an exception is raised.

For example, the following defines addition on natural numbers:
@interaction[
#:eval redex-eval
       (define-language nats
         (n ::= z (s n)))
       (define-judgment-form nats
         #:mode (sum I I O)
         #:contract (sum n n n)
         [-----------  "zero"
          (sum z n n)]
         
         [(sum n_1 n_2 n_3)
          ------------------------- "add1"
          (sum (s n_1) n_2 (s n_3))])]

The @racket[judgment-holds] form checks whether a relation holds for any 
assignment of pattern variables in output positions.
@examples[
#:eval redex-eval
       (judgment-holds (sum (s (s z)) (s z) (s (s (s z)))))
       (judgment-holds (sum (s (s z)) (s z) (s (s (s n)))))
       (judgment-holds (sum (s (s z)) (s z) (s (s (s (s n))))))]
Alternatively, this form constructs a list of terms based on the satisfying
pattern variable assignments.
@examples[
#:eval redex-eval
       (judgment-holds (sum (s (s z)) (s z) (s (s (s n)))) n)
       (judgment-holds (sum (s (s z)) (s z) (s (s (s (s n))))) n)
       (judgment-holds (sum (s (s z)) (s z) (s (s (s n)))) (s n))]

Declaring different modes for the same inference rules enables different forms
of computation. For example, the following mode allows @racket[judgment-holds]
to compute all pairs with a given sum.
@interaction[
#:eval redex-eval
       (define-judgment-form nats
         #:mode (sumr O O I)
         #:contract (sumr n n n)
         [------------
          (sumr z n n)]
         
         [(sumr n_1 n_2 n_3)
          --------------------------
          (sumr (s n_1) n_2 (s n_3))])
       (judgment-holds (sumr n_1 n_2 (s (s z))) (n_1 n_2))]

A rule's @racket[where] and @racket[where/hidden] premises behave as in 
@racket[reduction-relation] and @racket[define-metafunction].
@examples[
#:eval redex-eval
       (define-judgment-form nats
         #:mode (le I I)
         #:contract (le n n)
         [--------
          (le z n)]
         
         [(le n_1 n_2)
          --------------------
          (le (s n_1) (s n_2))])
       (define-metafunction nats
         pred : n -> n or #f
         [(pred z) #f]
         [(pred (s n)) n])
       (define-judgment-form nats
         #:mode (gt I I)
         #:contract (gt n n)
         [(where n_3 (pred n_1))
          (le n_2 n_3)
          ----------------------
          (gt n_1 n_2)])
       (judgment-holds (gt (s (s z)) (s z)))
       (judgment-holds (gt (s z) (s z)))]

A rule's @racket[side-condition] and @racket[side-condition/hidden] premises are similar
to those in @racket[reduction-relation] and @racket[define-metafunction], except that
they do not implicitly unquote their right-hand sides. In other words, a premise 
of the form @racket[(side-condition term)] is equivalent to the premise 
@racket[(where #t term)], except it does not typeset with the ``#t = '', as that would.

Judgments with exclusively @racket[I] mode positions may also be used in @|tttterm|s
in a manner similar to metafunctions, and evaluate to a boolean.
@examples[
#:eval redex-eval
       (term (le (s z) (s (s z))))
       (term (le (s z) z))]

A literal ellipsis may follow a judgment premise when a template in one of the
judgment's input positions contains a pattern variable bound at ellipsis-depth
one.
@examples[
#:eval redex-eval
       (define-judgment-form nats
         #:mode (even I)
         #:contract (even n)
         
         [-------- "evenz"
          (even z)]
         
         [(even n)
          ---------------- "even2"
          (even (s (s n)))])
       
       (define-judgment-form nats
         #:mode (all-even I)
         #:contract (all-even (n ...))
         [(even n) ...
          ------------------
          (all-even (n ...))])
       (judgment-holds (all-even (z (s (s z)) z)))
       (judgment-holds (all-even (z (s (s z)) (s z))))]

Redex evaluates premises depth-first, even when it doing so leads to 
non-termination. For example, consider the following definitions:
@interaction[
#:eval redex-eval
       (define-language vertices
         (v a b c))
       (define-judgment-form vertices
         #:mode (edge I O)
         #:contract (edge v v)
         [(edge a b)]
         [(edge b c)])
       (define-judgment-form vertices
         #:mode (path I I)
         #:contract (path v v)
         [----------
          (path v v)]
         
         [(path v_2 v_1)
          --------------
          (path v_1 v_2)]
         
         [(edge v_1 v_2)
          (path v_2 v_3)
          --------------
          (path v_1 v_3)])]
Due to the second @racket[path] rule, the follow query fails to terminate:
@racketinput[(judgment-holds (path a c))]

The @(examples-link "" #t "examples") directory demonstrates three use cases:
@itemlist[
@item{@(examples-link "define-judgment-form/typing-rules.rkt" #f "typing-rules.rkt") ---
      defines a type system in a way that supports mechanized typesetting.
      When a typing judgment form can be given a mode, it can also be encoded as
      a metafunction using @tech{@racket[where] clauses} as premises, but Redex
      cannot typeset that encoding as inference rules.}
@item{@(examples-link "define-judgment-form/sos.rkt" #f "sos.rkt") ---
      defines an SOS-style semantics in a way that supports mechanized typesetting.}
@item{@(examples-link "define-judgment-form/multi-val.rkt" #f "multi-val.rkt") ---
      defines a judgment form that serves as a multi-valued metafunction.}]}

@defform[(define-extended-judgment-form language judgment-form-id
           mode-spec
           contract-spec
           invariant-spec
           rule ...)]{
 Defines a new judgment form that extends @racket[judgment-form-id] 
 with additional rules. The @racket[mode-spec], @racket[contract-spec],
 @racket[invariant-spec], and @racket[rule]s
 are as in @racket[define-judgment-form].
 
 The mode specification in this judgment form and the original
 must be the same.
}
                             
@defform*/subs[((judgment-holds judgment)
                (judgment-holds judgment @#,tttterm))
               ([judgment (judgment-form-id pat/term ...)])]{
In its first form, checks whether @racket[judgment] holds for any assignment of
the pattern variables in @racket[judgment-id]'s output positions. In its second
form, produces a list of terms by instantiating the supplied term template with
each satisfying assignment of pattern variables.

@interaction[#:eval 
             redex-eval
             (judgment-holds (sum (s (s z)) (s z) n))
             (judgment-holds (sum (s (s z)) (s z) n) n)]
See @racket[define-judgment-form] for more examples.
}

@defform[(build-derivations judgment)]{
  Constructs all of the @racket[derivation] trees
  for @racket[judgment]. 
  
@examples[
#:eval redex-eval
       (build-derivations (even (s (s z))))]
}

@defstruct[derivation ([term any/c] [name (or/c string? #f)] [subs (listof derivation?)])]{
  Represents a derivation from a judgment form. 

  The @racket[term] field holds an s-expression based rendering of the
  conclusion of the derivation, the @racket[name] field holds the name
  of the clause with @racket[term] as the conclusion, and
  @racket[subs] contains the sub-derivations.

  See also @racket[build-derivations].
}
                                                            
@defidform[I]{
Recognized specially within @racket[define-judgment-form], the @racket[I] keyword
is an error elsewhere.
} 
@defidform[O]{
Recognized specially within @racket[define-judgment-form], the @racket[O] keyword
is an error elsewhere.
}

@defform/subs[#:literals (⊂ ⊆ × x)
              (define-relation language
                relation-contract
                [(name @#,ttpattern ...) 
                 @#,tttterm ...
                 metafunction-extras ...] ...)
              ([relation-contract (code:line)
                                  (code:line form-id ⊂ @#,ttpattern x ... x @#,ttpattern)
                                  (code:line form-id ⊆ @#,ttpattern × ... × @#,ttpattern)])]{
Similar to @racket[define-judgment-form] but suitable only when every position
is an input. There is no associated form corresponding to 
@racket[judgment-holds]; querying the result uses the same syntax as 
metafunction application.

The contract specification for a relation restricts the patterns that can
be used as input to a relation. For each argument to the relation, there
should be a single pattern, using @racket[x] or @racket[×] to separate
the argument contracts.

@examples[
#:eval redex-eval
       (define-language types
         ((τ σ) int
                num
                (τ → τ)))

       (define-relation types
         subtype ⊆ τ × τ
         [(subtype int num)]
         [(subtype (τ_1 → τ_2) (σ_1 → σ_2))
          (subtype σ_1 τ_1)
          (subtype τ_2 σ_2)]
         [(subtype τ τ)])

       (term (subtype int num))
       (term (subtype (int → int) (num → num)))
       (term (subtype (num → int) (num → num)))]
}

@defproc[(judgment-form? [v any/c]) boolean?]{
 Identifies values bound to identifiers introduced by
 @racket[define-judgment-form] and @racket[define-relation].
}

@defproc[(IO-judgment-form? [v any/c]) boolean?]{
 Identifies values bound to identifiers introduced by
 @racket[define-judgment-form] when the mode is
 @racket[(I O)] or @racket[(O I)].
}

@defparam[current-traced-metafunctions traced-metafunctions (or/c 'all (listof symbol?))]{

Controls which metafunctions are currently being traced. If it is
@racket['all], all of them are. Otherwise, the elements of the list
name the metafunctions to trace. 

The tracing looks just like the tracing done by the @racketmodname[racket/trace]
library, except that the first column printed by each traced call indicate
if this call to the metafunction is cached. Specifically, a @tt{c} is printed
in the first column if the result is just returned from the cache and a
space is printed if the metafunction call is actually performed.

Defaults to @racket['()].
}

@(close-eval redex-eval)
