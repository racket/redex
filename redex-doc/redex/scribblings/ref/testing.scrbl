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

@title{Testing}

@declare-exporting[redex/reduction-semantics redex]

@defform/subs[(test-equal e1 e2 option)
              ([option (code:line #:equiv pred-expr)
                       (code:line)])
	      #:contracts ([pred-expr (-> any/c any/c any/c)])]{

Tests to see if @racket[e1] is equal to @racket[e2], using @racket[pred-expr] as
the comparison. It defaults to @racket[(default-equiv)].

@examples[#:eval redex-eval
                 
                 (define-language L
                   (bt ::= 
                       empty
                       (node any bt bt))
                   (lt ::=
                       empty
                       (node any lt empty)))
                 
                 (define-metafunction L
                   linearize/a : bt lt -> lt
                   [(linearize/a empty lt) lt]
                   [(linearize/a (node any_val bt_left bt_right) lt)
                    (node any_val (linearize/a bt_left (linearize/a bt_right lt)) empty)])
                 
                 (define-metafunction L
                   linearize : bt -> lt
                   [(linearize bt) (linearize/a bt empty)])
                 
                 (test-equal (term (linearize empty))
                             (term empty))
                 (test-equal (term (linearize (node 1
                                                    (node 2 empty empty)
                                                    (node 3 empty empty))))
                             (term (node 1 (node 2 (node 3 empty empty) empty) empty)))
                 (test-results)
]}

@defform/subs[(test-->> rel-expr option ... e1-expr e2-expr ...)
              ([option (code:line #:cycles-ok)
                       (code:line #:equiv pred-expr)
                       (code:line #:pred pred-expr)])
              #:contracts ([rel-expr reduction-relation?]
                           [pred-expr (--> any/c any)]
                           [e1-expr any/c]
                           [e2-expr any/c])]{

Tests to see if the term @racket[e1-expr],
reduces to the terms @racket[e2-expr] under @racket[rel-expr],
using @racket[pred-expr] to determine equivalence. 

If @racket[#:pred] is specified, it is applied to each reachable term
until one of the terms fails to satisfy the predicate (i.e., the
predicate returns @racket[#f]). If that happens, then the test fails
and a message is printed with the term that failed to satisfy the
predicate.

This test uses
@racket[apply-reduction-relation*], so it does not terminate
when the resulting reduction graph is infinite, although it 
does terminate if there are cycles in the (finite) graph.

If @racket[#:cycles-ok] is not supplied then any cycles detected
are treated as a test failure. If a @racket[pred-expr] is supplied,
then it is used to compare the expected and actual results. If it 
isn't supplied, then @racket[(default-equiv)] is used.
}

@defform/subs[(test--> rel-expr option ... e1-expr e2-expr ...)
              ([option (code:line #:equiv pred-expr)])
              #:contracts ([rel-expr reduction-relation?]
                           [pred-expr (--> any/c any/c any/c)]
                           [e1-expr any/c]
                           [e2-expr any/c])]{

Tests to see if the term @racket[e1-expr],
reduces to the terms @racket[e2-expr] in a single @racket[rel-expr]
step, using @racket[pred-expr] to determine equivalence (or
@racket[(default-equiv)] if @racket[pred-expr] isn't specified).
}

@examples[
#:eval redex-eval
       (define-language L
         (i integer))

       (define R
         (reduction-relation
          L
          (--> i i)
          (--> i ,(add1 (term i)))))

       (define (mod2=? i j)
         (= (modulo i 2) (modulo j 2)))

       (test--> R #:equiv mod2=? 7 1)

       (test--> R #:equiv mod2=? 7 1 0)
       
       (test-results)]

@defform/subs[(test-->>∃ option ... rel-expr start-expr goal-expr)
              ([option (code:line #:steps steps-expr)])
              #:contracts ([rel-expr reduction-relation?]
                           [start-expr any/c]
                           [goal-expr (or/c (-> any/c any/c)
                                            (not/c procedure?))]
                           [steps-expr (or/c natural-number/c +inf.0)])]{
Tests to see if the term @racket[start-expr] reduces according to the reduction 
relation @racket[rel-expr] to a term specified by @racket[goal-expr] in 
@racket[steps-expr] or fewer steps (default 1,000). The specification 
@racket[goal-expr] may be either a predicate on terms or a term itself.
}
@defidform[test-->>E]{An alias for @racket[test-->>∃].}

@examples[
#:eval redex-eval
       (define-language L
         (n natural))

       (define succ-mod8
         (reduction-relation
          L
          (--> n ,(modulo (add1 (term n)) 8))))

       (test-->>∃ succ-mod8 6 2)
       (test-->>∃ succ-mod8 6 even?)
       (test-->>∃ succ-mod8 6 8)
       (test-->>∃ #:steps 6 succ-mod8 6 5)
       
       (test-results)]

@defform[(test-predicate p? e)]{
Tests to see if the value of @racket[e] matches the predicate @racket[p?].
}

@defproc[(test-results) void?]{
Prints out how many tests passed and failed, and resets the
counters so that next time this function is called, it
prints the test results for the next round of tests.
}

@defparam[default-equiv equiv (-> any/c any/c any/c)]{
  The value of this parameter is used as the default value
  of the equivalence predicates
  for @racket[test-equal], @racket[test-->], and @racket[test-->>].
  
  It defaults to @racket[(lambda (lhs rhs) (alpha-equivalent? (default-language) lhs rhs))].
}

@defform/subs[(make-coverage subject)
              ([subject (code:line metafunction)
                        (code:line relation-expr)])]{
Constructs a structure (recognized by @racket[coverage?])
to contain per-case test coverage of the supplied metafunction
or reduction relation. Use with @racket[relation-coverage] and 
@racket[covered-cases].
}

@defproc[(coverage? [v any/c]) boolean?]{
Returns @racket[#t] for a value produced by @racket[make-coverage]
and @racket[#f] for any other.}

@defparam[relation-coverage tracked (listof coverage?)]{
Redex populates the coverage records in @racket[tracked] (default @racket[null]),
counting the times that tests exercise each case of the associated metafunction
and relations.}

@defproc[(covered-cases 
          [c coverage?])
         (listof (cons/c string? natural-number/c))]{
Extracts the coverage information recorded in @racket[c], producing
an association list mapping names (or source locations, in the case of
metafunctions or unnamed reduction-relation cases) to application counts.}

@examples[
#:eval redex-eval
       (define-language empty-lang)
       
       (define-metafunction empty-lang
         [(plus number_1 number_2)
          ,(+ (term number_1) (term number_2))])
       
       (define equals
         (reduction-relation 
          empty-lang
          (--> (+) 0 "zero")
          (--> (+ number) number)
          (--> (+ number_1 number_2 number ...)
               (+ (plus number_1 number_2)
                  number ...)
               "add")))
       (let ([equals-coverage (make-coverage equals)]
             [plus-coverage (make-coverage plus)])
         (parameterize ([relation-coverage (list equals-coverage 
                                                 plus-coverage)])
           (apply-reduction-relation* equals (term (+ 1 2 3)))
           (values (covered-cases equals-coverage)
                   (covered-cases plus-coverage))))]

@defform*/subs[((generate-term from-pattern)
                (generate-term from-judgment-form)
                (generate-term from-metafunction)
                (generate-term from-reduction-relation))
               ([from-pattern
                 (code:line language @#,ttpattern size-expr kw-args ...)
                 (code:line language @#,ttpattern)
                 (code:line language @#,ttpattern #:i-th index-expr)
                 (code:line language @#,ttpattern #:i-th)]
                [from-judgment-form
                 (code:line language #:satisfying
                            (judgment-form-id @#,ttpattern ...))
                 (code:line language #:satisfying
                            (judgment-form-id @#,ttpattern ...)
                            size-expr)]
                [from-metafunction
                 (code:line language #:satisfying 
                            (metafunction-id @#,ttpattern ...) = @#,ttpattern)
                 (code:line language #:satisfying 
                            (metafunction-id @#,ttpattern ...) = @#,ttpattern
                            size-expr)
                 (code:line #:source metafunction size-expr kw-args)
                 (code:line #:source metafunction)]
                [from-reduction-relation
                 (code:line #:source reduction-relation-expr
                            size-expr kw-args ...)
                 (code:line #:source reduction-relation-expr)]
                [kw-args (code:line #:attempt-num attempts-expr)
                         (code:line #:retries retries-expr)])
              #:contracts ([size-expr natural-number/c]
                           [attempt-num-expr natural-number/c]
                           [retries-expr natural-number/c])]{

Generates terms in a number of different ways:
@itemlist[@item{@racket[from-pattern]:
                 In the first case, randomly makes an expression matching the given pattern
                 whose size is bounded by @racket[size-expr]; the second returns a function
                 that accepts a size bound and returns a random term. Calling this function 
                 (even with the same size bound) may be more efficient than using the first case.
                 
                 
                 @examples[#:eval
                           redex-eval
                           (define-language L
                             (e ::=
                                (e e)
                                (λ (x) e)
                                x)
                             (x ::= a b c))
                           
                           (for/list ([i (in-range 10)])
                             (generate-term L e 3))]
                 
                 The @racket[#:i-th] option uses an enumeration of the non-terminals in a language. 
                 If @racket[index-expr] is supplied, @racket[generate-term] returns the corresponding
                 term and if it isn't, @racket[generate-term] returns a function from indices
                 to terms.
                 @examples[#:eval
                           redex-eval
                           (for/list ([i (in-range 9)])
                             (generate-term L e #:i-th i))]

                 Base type enumerations such as @racket[boolean], 
                 @racket[natural] and @racket[integer] are what you might expect:
                 
                 @examples[#:eval
                           redex-eval
                           (for/list ([i (in-range 10)])
                             (generate-term L boolean #:i-th i))
                           (for/list ([i (in-range 10)])
                             (generate-term L natural #:i-th i))
                           (for/list ([i (in-range 10)])
                             (generate-term L integer #:i-th i))]
                 
                 The @racket[real] base type enumeration consists of all integers and flonums, and the
                 @racket[number] pattern consists of complex numbers with real and imaginary parts 
                 taken from the @racket[real] enumeration.
                 
                 @examples[#:eval
                           redex-eval
                           (for/list ([i (in-range 20)])
                             (generate-term L real #:i-th i))
                           (for/list ([i (in-range 20)])
                             (generate-term L number #:i-th i))]
                 
                 The @racket[string] enumeration produces all single character strings before
                 going on to strings with multiple characters. For each character it starts
                 the lowercase Latin characters, then uppercase Latin, and then every remaining
                 Unicode character. The @racket[variable] enumeration is the same, except it 
                 produces symbols instead of strings.
                 
                 @examples[#:eval
                           redex-eval
                           (generate-term L string #:i-th 0)
                           (generate-term L string #:i-th 1)
                           (generate-term L string #:i-th 26)
                           (generate-term L string #:i-th 27)
                           (generate-term L string #:i-th 52)
                           (generate-term L string #:i-th 53)
                           (generate-term L string #:i-th 956)
                           (generate-term L variable #:i-th 1)
                           (generate-term L variable #:i-th 27)]
                 
                 The @racket[variable-prefix], @racket[variable-except], and
                 @racket[variable-not-otherwise-mentioned] are defined
                 similarly, as you expect.
                 
                 @examples[#:eval
                           redex-eval
                           (define-language L
                             (used ::= a b c)
                             (except ::= (variable-except a))
                             (unused ::= variable-not-otherwise-mentioned))
                           (for/list ([i (in-range 10)])
                             (generate-term L (variable-prefix a:) #:i-th i))
                           (for/list ([i (in-range 10)])
                             (generate-term L except #:i-th i))
                           (for/list ([i (in-range 10)])
                             (generate-term L unused #:i-th i))]

                 Finally, the @racket[any] pattern enumerates terms of the above base types.
                 @examples[#:eval
                           redex-eval
                           (for/list ([i (in-range 20)])
                             (generate-term L any #:i-th i))]
                 
                 In addition, all other pattern types are supported
                 except for mismatch repeat @racket[..._!_] patterns
                 and @racket[side-condition] patterns.
                 
                 The enumerators do not repeat terms unless the given pattern is ambiguous.
                 Roughly speaking, the enumerator generates all possible ways that a pattern
                 might be parsed and since ambiguous patterns have multiple ways they might
                 be parsed, those multiple parsings turn into repeated elements in the enumeration.
                 
                 @examples[#:eval
                           redex-eval
                           (for/list ([i (in-range 9)])
                             (generate-term L (boolean_1 ... boolean_2 ...) #:i-th i))]
                 
                 Other sources of ambiguity are @racket[in-hole] and overlapping non-terminals.
                 @examples[#:eval
                           redex-eval
                           (define-language L
                             (e ::= (e e) (λ (x) e) x)
                             (E ::= hole (e E) (E e))
                             (x ::= a b c))

                           (for/list ([i (in-range 9)])
                             (generate-term L (in-hole E e) #:i-th i))
                           
                           (define-language L
                             (overlap ::= natural integer))
                           (for/list ([i (in-range 10)])
                             (generate-term L overlap #:i-th i))]

                 For similar reasons, enumerations for mismatch
                 patterns (using @racketvarfont{_!_}) do not work properly when given 
                 ambiguous patterns; they may repeat elements of the enumeration.
                 @examples[#:eval
                           redex-eval
                           (define-language Bad
                             (ambig ::= (x ... x ...)))
                           (generate-term Bad (ambig_!_1 ambig_!_1) #:i-th 4)]
                 In this case, the elements of the resulting list are the same,
                 even though they should not be, according to the pattern. Internally,
                 the enumerator has discovered two different ways to generate @racket[ambig]
                 (one where the @racket[x] comes from the first ellipses and one from the second)
                 but those two different ways produce the same term and so the enumerator
                 incorrectly produces @racket[(x x)].
                 
                 }
           @item{@racket[from-judgment-form]: Randomly picks a term that satisfies
                  the given use of the judgment form.
                  
                  @examples[#:eval
                            redex-eval
                            (define-language L
                              (nat ::= Z (S nat)))
                            (define-judgment-form L
                              #:mode (sum I I O)
                              [---------------
                               (sum Z nat nat)]
                              [(sum nat_1 nat_2 nat_3)
                               -------------------------------
                               (sum (S nat_1) nat_2 (S nat_3))])
                            
                            (for/list ([i (in-range 10)])
                              (generate-term L #:satisfying 
                                             (sum nat_1 nat_2 nat_3)
                                             3))]}
           @item{@racket[from-metafunction]: The first form randomly picks a term
                  that satisfies the given invocation of the metafunction, using
                  techniques similar to how the @racket[from-judgment-form] case works.
                  The second form uses a more naive approach; it simply generates terms
                  that match the patterns of the cases of the metafunction; it does not
                  consider the results of the metafunctions, nor does it consider
                  patterns from earlier cases when generating terms based on a particular case.
                  The third case is like the second, except it returns a function that accepts
                  the size and keywords arguments that may be more efficient if multiple 
                  random terms are generated.
                  @examples[#:eval
                            redex-eval
                            (define-language L
                             (n number))
                            (define-metafunction L
                              [(F one-clause n) ()]
                              [(F another-clause n) ()])
                            
                            (for/list ([i (in-range 10)])
                              (generate-term #:source F 5))]}
           @item{@racket[from-reduction-relation]: In the first case, @racket[generate-term]
                  randomly picks a rule from the reduction relation and tries to pick a term
                  that satisfies its domain pattern, returning that. The second case returns
                  a function that accepts the size and keyword arguments that may be more
                  efficient if multiple random terms are generated.
                  
                  @examples[#:eval
                            redex-eval
                            (define-language L
                             (n number))
                            (for/list ([i (in-range 10)])
                              (generate-term
                               #:source
                               (reduction-relation
                                L
                                (--> (one-clause n) ())
                                (--> (another-clause n) ()))
                               5))]}]

The argument @racket[size-expr] bounds the height of the generated term
(measured as the height of its parse tree). 

The optional keyword argument @racket[attempt-num-expr] 
(default @racket[1]) provides coarse grained control over the random
decisions made during generation; increasing @racket[attempt-num-expr]
tends to increase the complexity of the result. For example, the absolute
values of numbers chosen for @pattech[integer] patterns increase with
@racket[attempt-num-expr].

The random generation process does not actively consider the constraints
imposed by @pattech[side-condition] or @tt{_!_} @|pattern|s; instead, 
it uses a ``guess and check'' strategy in which it freely generates 
candidate terms then tests whether they happen to satisfy the constraints,
repeating as necessary. The optional keyword argument @racket[retries-expr]
(default @racket[100]) bounds the number of times that 
@racket[generate-term] retries the generation of any pattern. If 
@racket[generate-term] is unable to produce a satisfying term after 
@racket[retries-expr] attempts, it raises an exception recognized by
@racket[exn:fail:redex:generation-failure?].
}

@defform/subs[(redex-check template property-expr kw-arg ...)
              ([template (code:line language @#,ttpattern)
                         (code:line language @#,ttpattern #:ad-hoc)
                         (code:line language @#,ttpattern #:in-order)
                         (code:line language @#,ttpattern #:uniform-at-random p-value)
                         (code:line language @#,ttpattern #:enum bound)
                         (code:line language #:satisfying
                            (judgment-form-id @#,ttpattern ...))
                         (code:line language #:satisfying 
                            (metafunction-id @#,ttpattern ...) = @#,ttpattern)]
              [kw-arg (code:line #:attempts attempts-expr)
                       (code:line #:source metafunction)
                       (code:line #:source relation-expr)
                       (code:line #:retries retries-expr)
                       (code:line #:print? print?-expr)
                       (code:line #:attempt-size attempt-size-expr)
                       (code:line #:prepare prepare-expr)
                       (code:line #:keep-going? keep-going?-expr)])
              #:contracts ([property-expr any/c]
                           [attempts-expr natural-number/c]
                           [relation-expr reduction-relation?]
                           [retries-expr natural-number/c]
                           [print?-expr any/c]
                           [attempt-size-expr (-> natural-number/c natural-number/c)]
                           [prepare-expr (-> any/c any/c)])]{
Searches for a counterexample to @racket[property-expr], interpreted
as a predicate universally quantified over the pattern variables
bound by the @racket[pattern](s) in @racket[template].
@racket[redex-check] constructs and tests 
a candidate counterexample by choosing a random term @math{t} based 
on @racket[template] and then evaluating @racket[property-expr]
using the @racket[match-bindings] produced by @racket[match]ing
@math{t} against @racket[pattern]. The form of @racket[template] controls
how @math{t} is generated:
@itemlist[@item{@racket[language @#,ttpattern]:
                 In this case, @racket[redex-check] uses an ad hoc strategy for 
                 generating @racket[_pattern]. For the first 10 seconds, it uses 
                 in-order enumeration to pick terms. After that, it
                 alternates back and forth between in-order enumeration
                 and the ad hoc random generator. After the 10 minute mark,
                 it switches over to using just the ad hoc random generator.}
          @item{@racket[language @#,ttpattern #:ad-hoc]:
                 In this case, @racket[redex-check] uses an ad hoc random generator
                 to generate terms that match @racket[_pattern].}
          @item{@racket[language @#,ttpattern #:in-order]:
                 In this case, @racket[redex-check] uses an enumeration
                 of @racket[_pattern], checking each @math{t} one at a time}
          @item{@racket[language @#,ttpattern #:uniform-at-random p-value]:
                 that to index into an enumeration of @racket[_pattern].
                 If the enumeration is finite, @racket[redex-check] picks a natural number
                 uniformly at random; if it isn't, @racket[redex-check] uses a geometric
                 distribution with @racket[p-value] as its probability of zero 
                 to pick the number of bits in the index and then picks a
                 number uniformly at random with that number of bits.}
          @item{@racket[language @#,ttpattern #:enum bound]:
                 This is similar to @racket[#:uniform-at-random], except
                 that Redex always picks a random natural number less than @racket[bound]
                 to index into the enumeration}
          @item{@racket[language #:satisfying (judgment-form-id @#,ttpattern ...)]:
                  Generates terms that match @racket[pattern] and satisfy 
                  the judgment form.}
          @item{@racket[language #:satisfying (metafunction-id @#,ttpattern ...) = @#,ttpattern]:
                  Generates terms matching the two @racket[pattern]s, such that
                  if the first is the argument to the metafunction, the
                  second will be the result.}]

@racket[redex-check] generates at most @racket[attempts-expr] 
(default @racket[(default-check-attempts)])
random terms in its search. The size and complexity of these terms tend to increase 
with each failed attempt. The @racket[#:attempt-size] keyword determines the rate at which
terms grow by supplying a function that bounds term size based on the number of failed
attempts (see @racket[generate-term]'s @racket[size-expr] argument). By default, the bound
grows according to the @racket[default-attempt-size] function.

When @racket[print?-expr] produces any non-@racket[#f] value (the default), 
@racket[redex-check] prints the test outcome on @racket[current-output-port].
When @racket[print?-expr] produces @racket[#f], @racket[redex-check] prints
nothing, instead 
@itemlist[
  @item{returning a @racket[counterexample] structure when the test reveals a counterexample,}
  @item{returning @racket[#t] when all tests pass, or}
  @item{raising a @racket[exn:fail:redex:test] when checking the property raises an exception.}
]

The optional @racket[#:prepare] keyword supplies a function that transforms each
generated example before @racket[redex-check] checks @racket[property-expr].
This keyword may be useful when @racket[property-expr] takes the form
of a conditional, and a term chosen freely from the grammar is unlikely to
satisfy the conditional's hypothesis. In some such cases, the @racket[prepare] 
keyword  can be used to increase the probability that an example satisfies the
hypothesis.

The @racket[#:retries] keyword behaves identically as in @racket[generate-term],
controlling the number of times the generation of any pattern will be
reattempted. It can't be used together with @racket[#:satisfying].

If @racket[keep-going?-expr] produces any non-@racket[#f] value,
@racket[redex-check] will stop only when it hits the limit on the number of attempts 
showing all of the errors it finds. This argument is allowed only when 
@racket[print?-expr] is not @racket[#f].

When passed a metafunction or reduction relation via the optional @racket[#:source]
argument, @racket[redex-check] distributes its attempts across the left-hand sides
of that metafunction/relation by using those patterns, rather than @racket[pattern],
as the basis of its generation. If any left-hand side generates a
term that does not match @racket[pattern], then the test input is discarded.
@racket[#:source] cannot be used with @racket[#:satisfying].
See also @racket[check-reduction-relation] and @racket[check-metafunction].

@examples[
#:eval redex-eval
       (define-language empty-lang)
       
       (random-seed 0)

       (redex-check 
        empty-lang
        ((number_1 ...)
         (number_2 ...))
        (equal? (reverse (append (term (number_1 ...))
                                 (term (number_2 ...))))
                (append (reverse (term (number_1 ...)))
                        (reverse (term (number_2 ...))))))

       (redex-check 
        empty-lang
        ((number_1 ...)
         (number_2 ...))
        (equal? (reverse (append (term (number_1 ...))
                                 (term (number_2 ...))))
                (append (reverse (term (number_2 ...)))
                        (reverse (term (number_1 ...)))))
        #:attempts 200)
       
       (let ([R (reduction-relation 
                 empty-lang
                 (--> (Σ) 0)
                 (--> (Σ number) number)
                 (--> (Σ number_1 number_2 number_3 ...)
                      (Σ ,(+ (term number_1) (term number_2)) 
                         number_3 ...)))])
         (redex-check
          empty-lang
          (Σ number ...)
          (printf "~s\n" (term (number ...)))
          #:attempts 3
          #:source R))

       (redex-check
        empty-lang
        number
        (begin
          (printf "checking ~s\n" (term number))
          (positive? (term number)))
        #:prepare (λ (n)
                    (printf "preparing ~s; " n)
                    (add1 (abs (real-part n))))
        #:attempts 3)
                     
       (define-language L
         (nat ::= Z (S nat)))
       (define-judgment-form L
         #:mode (sum I I O)
         [---------------
          (sum Z nat nat)]
         [(sum nat_1 nat_2 nat_3)
          -------------------------------
          (sum (S nat_1) nat_2 (S nat_3))])
       (redex-check L
                    #:satisfying
                    (sum nat_1 nat_2 nat_3)
                    (equal? (judgment-holds
                             (sum nat_1 nat_2 nat_4) nat_4)
                            (term (nat_3)))
                    #:attempts 100)
       (redex-check L
                    #:satisfying
                    (sum nat_1 nat_2 nat_3)
                    (equal? (term nat_1) (term nat_2)))]

@history[#:changed "1.10" @list{Instead of raising an error, @racket[redex-check] now discards
           test cases that don't match the given pattern when using @racket[#:source].}]

}

@defparam[depth-dependent-order? depth-dependent (or/c boolean? 'random)
                                 #:value 'random]{

Toggles whether or not Redex will dynamically adjust the
chance that more recursive clauses of judgment forms or metafunctions 
are chosen earlier when attempting to generate terms 
with forms that use @racket[#:satisfying]. If it is @racket[#t],
Redex favors more recursive clauses at
lower depths and less recursive clauses at depths closer to the
limit, in an attempt to generate larger terms. 
When it is @racket[#f], all clause orderings have equal probability
above the bound.
By default, it is @racket['random], which causes Redex to
choose between the two above alternatives with equal probability.
}

@defform/subs[(redex-generator language-id satisfying size-expr)
              ([satisfying (judgment-form-id @#,ttpattern ...)
                           (code:line (metafunction-id @#,ttpattern ...) = @#,ttpattern)])
              #:contracts ([size-expr natural-number/c])]{
  
  @italic{WARNING: @racket[redex-generator] is a new, experimental form, 
          and its API may change.}
                                                     
  Returns a thunk that, each time it is called, either generates a random
  s-expression based on @racket[satisfying] or fails to (and returns @racket[#f]). 
  The terms returned by a particular thunk are guaranteed to be distinct.
  
  @examples[#:eval
            redex-eval
            (define-language L
              (nat ::= Z (S nat)))
            (define-judgment-form L
              #:mode (sum I I O)
              [---------------
               (sum Z nat nat)]
              [(sum nat_1 nat_2 nat_3)
               -------------------------------
               (sum (S nat_1) nat_2 (S nat_3))])
            (define gen-sum (redex-generator L (sum nat_1 nat_2 nat_3) 3))
            (for/list ([_ (in-range 5)])
              (gen-sum))]
}

@defstruct[counterexample ([term any/c]) #:inspector #f]{
Produced by @racket[redex-check], @racket[check-reduction-relation], and 
@racket[check-metafunction] when testing falsifies a property.}

@defstruct[(exn:fail:redex:test exn:fail:redex) ([source exn:fail?] [term any/c])]{
Raised by @racket[redex-check], @racket[check-reduction-relation], and 
@racket[check-metafunction] when testing a property raises an exception.
The @racket[exn:fail:redex:test-source] component contains the exception raised by the property,
and the @racket[exn:fail:redex:test-term] component contains the term that induced the exception.}

                                                         
@defform/subs[(check-reduction-relation relation property kw-args ...)
              ([kw-arg (code:line #:attempts attempts-expr)
                       (code:line #:retries retries-expr)
                       (code:line #:print? print?-expr)
                       (code:line #:attempt-size attempt-size-expr)
                       (code:line #:prepare prepare-expr)])
              #:contracts ([property (-> any/c any/c)]
                           [attempts-expr natural-number/c]
                           [retries-expr natural-number/c]
                           [print?-expr any/c]
                           [attempt-size-expr (-> natural-number/c natural-number/c)]
                           [prepare-expr (-> any/c any/c)])]{
Tests @racket[relation] as follows: for each case of @racket[relation],
@racket[check-reduction-relation] generates @racket[attempts] random
terms that match that case's left-hand side and applies @racket[property] 
to each random term.

Only the primary pattern of each case's left-hand side is considered. If there
are @racket[where] clauses or @racket[side-condition]s (or anything else from the
@racket[_red-extras] portion of the grammar), they are ignored.

This form provides a more convenient notation for
@racketblock[(redex-check L any (property (term any)) 
                          #:attempts (* n attempts)
                          #:source relation)]
when @racket[relation] is a relation on @racket[L] with @racket[n] rules.}

@defform/subs[(check-metafunction metafunction property kw-args ...)
              ([kw-arg (code:line #:attempts attempts-expr)
                       (code:line #:retries retries-expr)
                       (code:line #:print? print?-expr)
                       (code:line #:attempt-size attempt-size-expr)
                       (code:line #:prepare prepare-expr)])
              #:contracts ([property (-> (listof any/c) any/c)]
                           [attempts-expr natural-number/c]
                           [retries-expr natural-number/c]
                           [print?-expr any/c]
                           [attempt-size-expr (-> natural-number/c natural-number/c)]
                           [prepare-expr (-> (listof any/c) (listof any/c))])]{
Like @racket[check-reduction-relation] but for metafunctions. 
@racket[check-metafunction] calls @racket[property] with lists
containing arguments to the metafunction. Similarly, @racket[prepare-expr]
produces and consumes argument lists.}

Only the primary pattern of each case's left-hand side is considered. If there
are @racket[where] clauses or @racket[side-condition]s (or anything else from the
@racket[_metafunction-extras] portion of the grammar), they are ignored.

@(redex-eval '(random-seed 0))
@examples[
#:eval redex-eval
       (define-language empty-lang)

       (define-metafunction empty-lang
         Σ : number ... -> number
         [(Σ) 0]
         [(Σ number) number]
         [(Σ number_1 number_2) ,(+ (term number_1) (term number_2))]
         [(Σ number_1 number_2 ...) (Σ number_1 (Σ number_2 ...))])
       
       (check-metafunction Σ (λ (args) 
                               (printf "trying ~s\n" args)
                               (equal? (apply + args)
                                       (term (Σ ,@args))))
                           #:attempts 2)]

@defproc[(default-attempt-size [n natural-number/c]) natural-number/c]{
The default value of the @racket[#:attempt-size] argument to 
@racket[redex-check] and the other randomized testing forms, this 
procedure computes an upper bound on the size of the next
test case from the number of previously attempted tests @racket[n]. 
Currently, this procedure computes the base 5 logarithm, but 
that behavior may change in future versions.
}

@defparam[default-check-attempts attempts natural-number/c]{Determines the default
value for @racket[redex-check]'s optional @racket[#:attempts] argument. By default,
@racket[attempts] is 1,000.}

@defparam[redex-pseudo-random-generator generator pseudo-random-generator?]{
@racket[generate-term] and the randomized testing forms (e.g., @racket[redex-check])
use the parameter @racket[generator] to construct random terms. The parameter's
initial value is @racket[(current-pseudo-random-generator)].}

@defproc[(exn:fail:redex:generation-failure? [v any/c]) boolean?]{
  Recognizes the exceptions raised by @racket[generate-term], 
  @racket[redex-check], etc. when those forms are unable to produce
  a term matching some pattern.
}

@deftech{Debugging PLT Redex Programs}

It is easy to write grammars and reduction rules that are
subtly wrong. Typically such mistakes result in examples
that get stuck when viewed in a @racket[traces] window.

The best way to debug such programs is to find an expression
that looks like it should reduce, but doesn't, then try to find
out which pattern is failing to match. To do so, use the
@racket[redex-match] form.

In particular, first check if the term in question matches the
your system's main non-terminal (typically the expression
or program non-terminal). If it does not match, simplify the term
piece by piece to determine whether the problem is in the
term or the grammar. 

If the term does match your system's main
non-terminal, determine by inspection which reduction rules
should apply. For each such rule, repeat the above term-pattern 
debugging procedure, this time using the rule's left-hand side 
pattern instead of the system's main non-terminal. In addition
to simplifying the term, also consider simplifying the pattern.

If the term matches the left-hand side, but the rule does not 
apply, then one of the rule's @racket[side-condition] or 
@racket[where] clauses is not satisfied. Using the bindings
reported by @racket[redex-match], check each @racket[side-condition]
expression and each @racket[where] pattern-match to discover which
clause is preventing the rule's application.

@(close-eval redex-eval)
