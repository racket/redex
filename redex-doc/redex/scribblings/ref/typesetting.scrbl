#lang scribble/manual
@(require scribble/struct
          (for-label racket/base
                     (except-in racket/gui make-color)
                     racket/pretty
                     racket/contract
                     mrlib/graph
                     (except-in 2htdp/image make-pen text)
                     (only-in pict pict? text dc-for-text-size text-style/c
                              vc-append hbl-append vl-append)
                     redex))

@(define-syntax-rule (arrows a0 a ...)
   (make-blockquote
    #f 
    (list (make-paragraph 
           (list (racketidfont (make-element #f (list (symbol->string 'a0))))
                 (make-element #f (list " " (hspace 1) " " (racketidfont (symbol->string 'a))))
                 ...)))))


@title{Typesetting}

@defmodule*/no-declare[(redex/pict)]
@declare-exporting[redex/pict redex]

The @racketmodname[redex/pict] library provides functions
designed to typeset grammars, reduction relations, and
metafunctions.

Each grammar, reduction relation, and metafunction can be
saved in a @filepath{.ps} file (as encapsulated PostScript),
or can be turned into a pict for viewing in the REPL or
using with Slideshow (see the @racketmodname[pict]
library).

For producing papers with Scribble, just include the
picts inline in the paper and pass the the @DFlag{dvipdf} 
flag generate the @filepath{.pdf} file. For producing
papers with LaTeX, create @filepath{.ps} files from Redex and use
@tt{latex} and @tt{dvipdf} to create @filepath{.pdf} files
(using @tt{pdflatex} with @filepath{.pdf} files will 
work but the results will not look as good onscreen).

@section{Picts, PDF, & PostScript}

This section documents two classes of operations, one for
direct use of creating postscript figures for use in papers
and for use in DrRacket to easily adjust the typesetting:
@racket[render-term],
@racket[render-language],
@racket[render-reduction-relation], 
@racket[render-relation],
@racket[render-judgment-form],
@racket[render-metafunctions], and
@racket[render-lw], 
and one for use in combination with other libraries
that operate on @racketmodname[pict]s
@racket[term->pict],
@racket[language->pict],
@racket[reduction-relation->pict],
@racket[relation->pict],
@racket[judgment-form->pict],
@racket[metafunction->pict], and
@racket[lw->pict].
The primary difference between these functions is that the former list
sets @racket[dc-for-text-size] and the latter does not.


@defform*[[(render-term lang term)
           (render-term lang term file)]]{
  Renders the term @racket[term]. If @racket[file] is @racket[#f] or not present,
  @racket[render-term] produces a pict; if @racket[file] is a path, it saves
  Encapsulated PostScript in the provided filename, unless the filename
  ends with @filepath{.pdf}, in which case it saves PDF.
  
  The @racket[term] argument must be a literal; it is not an 
  evaluated position. For example, this:
  @racketblock[(define-language L)
               (define x (term (+ 1 2)))
               (render-term L x)]
  will render the term @racket[x], not the term @racket[(+ 1 2)].
  
  See @racket[render-language] for more details on the construction of the pict.
}


@defform[(term->pict lang term)]{
 Produces a pict like @racket[render-term], but without
 adjusting @racket[dc-for-text-size].

 The first argument is expected to be a @racket[compiled-language?] and
 the second argument is expected to be a term (without the
 @racket[term] wrapper). The formatting in the @racket[term] argument
 is used to determine how the resulting pict will look.
 
 This function is primarily designed to be used with
 Slideshow or with other tools that combine @racketmodname[pict]s
 together.
}

@defproc[(render-term/pretty-write [lang compiled-lang?]
                                   [term any/c]
                                   [filename path-string?]
                                   [#:width width #f])
         void?]{
  Like @racket[render-term], except that the @racket[term] argument is evaluated,
  and expected to return a term. Then, @racket[pretty-write] is used
  to determine where the line breaks go, using the @racket[width] argument
  as a maximum width (via @racket[pretty-print-columns]).
}

@defproc[(term->pict/pretty-write [lang compiled-lang?] 
                                  [term any/c]
                                  [filename (or/c path-string? #f)]
                                  [#:width width #f])
         pict?]{
  Like @racket[term->pict], but with the same change that
  @racket[render-term/pretty-write] has from @racket[render-term].
}

@defproc[(render-language [lang compiled-lang?]
                          [file (or/c false/c path-string?) #f]
                          [#:nts nts (or/c false/c (listof (or/c string? symbol?)))
                           (render-language-nts)])
         (if file void? pict?)]{

Renders a language. If @racket[file] is @racket[#f],
it produces a pict; if @racket[file] is a path, it saves
Encapsulated PostScript in the provided filename, unless the filename
ends with @filepath{.pdf}, in which case it saves PDF.
See
@racket[render-language-nts] for information on the
@racket[nts] argument.

This function parameterizes @racket[dc-for-text-size] to install a
relevant dc: a @racket[bitmap-dc%] or a @racket[post-script-dc%], depending on
whether @racket[file] is a path.

See @racket[language->pict] if you are using Slideshow or
are otherwise setting @racket[dc-for-text-size].  }

@defproc[(language->pict (lang compiled-lang?)
                         [#:nts nts (or/c false/c (listof (or/c string? symbol?)))
                          (render-language-nts)])
         pict?]{

Produce a pict like @racket[render-language], but without
adjusting @racket[dc-for-text-size].

This function is primarily designed to be used with
Slideshow or with other tools that combine @racketmodname[pict]s
together.
}

@defproc[(render-reduction-relation [rel reduction-relation?]
                                    [file (or/c false/c path-string?) #f]
                                    [#:style style reduction-rule-style/c (rule-pict-style)])
         (if file void? pict?)]{

Renders a reduction relation. If @racket[file] is @racket[#f],
it produces a pict; if @racket[file] is a path, it saves
Encapsulated PostScript in the provided filename, unless the filename
ends with @filepath{.pdf}, in which case it saves PDF.
See @racket[rule-pict-style] for information on the
@racket[style] argument.

This function parameterizes @racket[dc-for-text-size] to install a
relevant dc: a @racket[bitmap-dc%] or a @racket[post-script-dc%], depending on
whether @racket[file] is a path. See also
@racket[reduction-relation->pict].

The following forms of arrows can be typeset: 

@arrows[--> -+> ==> -> => ..> >-> ~~> ~> :-> :--> c->
        -->> >-- --< >>-- --<<]

}

@defproc[(reduction-relation->pict (r reduction-relation?)
                                   [#:style style reduction-rule-style/c (rule-pict-style)])
         pict?]{

  Produces a pict like @racket[render-reduction-relation], but 
  without setting @racket[dc-for-text-size].

This function is
primarily designed to be used with Slideshow or with
other tools that combine @racketmodname[pict]s together.
}

@deftogether[[
@defform[(render-metafunction metafunction-name maybe-contract)]{}
@defform/none[#:literals (render-metafunction)
              (render-metafunction metafunction-name filename maybe-contract)]{}
@defform[(render-metafunctions metafunction-name ... 
                               maybe-filename maybe-contract)
          #:grammar ([maybe-filename (code:line)
                      (code:line #:file filename)
                      (code:line #:filename filename)]
                     [maybe-contract? (code:line) (code:line #:contract? bool-expr)])]{}]]{
Like @racket[render-reduction-relation] but for metafunctions.

Similarly, @racket[render-metafunctions] accepts multiple 
metafunctions and renders them together, lining up all of the
clauses together.

If the metafunctions have contracts, they are typeset as the first
lines of the output unless the expression following @racket[#:contract?]
evaluates to @racket[#f] (which is the default).

This function sets @racket[dc-for-text-size]. See also
@racket[metafunction->pict] and
@racket[metafunctions->pict].

@history[#:changed "1.3" @list{Added @racket[#:contract?] keyword argument.}]
}

@defform[(metafunction->pict metafunction-name maybe-contract?)]{
  Produces a pict like @racket[render-metafunction], but without setting @racket[dc-for-text-size].
  It is suitable for use in Slideshow or other libraries that combine
  @racketmodname[pict]s.
  @history[#:changed "1.3" @list{Added @racket[#:contract?] keyword argument.}]
}

@defform[(metafunctions->pict metafunction-name ...)]{
  Like @racket[metafunction->pict], 
  this produces a @racketmodname[pict], but without setting @racket[dc-for-text-size]
  and is suitable for use in Slideshow or other libraries that combine
  @racketmodname[pict]s. Like
  @racket[render-metafunctions], it accepts multiple metafunctions
  and renders them together.
}

@deftogether[(@defform[(render-relation relation-name)]{}
              @defform/none[#:literals (render-relation)
                                       (render-relation relation-name filename)]{})]{
Like @racket[render-metafunction] but for relations.

This function sets @racket[dc-for-text-size]. See also
@racket[relation->pict].
}

@deftogether[(@defform[(render-judgment-form judgment-form-name)]{}
              @defform/none[#:literals (render-judgment-form)
                                       (render-judgment-form judgment-form-name filename)]{})]{
Like @racket[render-metafunction] but for judgment forms.

This function sets @racket[dc-for-text-size]. See also
@racket[judgment-form->pict].
}

@defform[(relation->pict relation-name)]{
  This produces a pict, but without setting @racket[dc-for-text-size].
  It is suitable for use in Slideshow or other libraries that combine
  @racketmodname[pict]s.
}

@defform[(judgment-form->pict judgment-form-name)]{
  This produces a pict, but without setting @racket[dc-for-text-size].
  It is suitable for use in Slideshow or other libraries that combine
  @racketmodname[pict]s.
}

@section{Customization}

@defparam[render-language-nts nts (or/c false/c (listof symbol?))]{
  The value of this parameter controls which non-terminals
  @racket[render-language] and @racket[language->pict] render by default. If it
  is @racket[#f] (the default), all non-terminals are rendered.
  If it is a list of symbols, only the listed symbols are rendered.

  See also @racket[language-nts].
}

@defparam[non-terminal-gap-space gap-space real?]{
  Controls the amount of vertical space between non-terminals
  in a typeset language.
  
  Defaults to @racket[0].
  
  @history[#:added "1.1"]
}

@defparam[extend-language-show-union show? boolean?]{

A parameter that controls the rendering of extended languages.
If the parameter value is @racket[#t], then a language constructed with
extend-language is shown as if the language had been
constructed directly with @racket[language]. If it is @racket[#f], then only
the last extension to the language is shown (with
four-period ellipses, just like in the concrete syntax).

Defaults to @racket[#f].

Note that the @racket[#t] variant can look a little bit strange if
@racket[....] are used and the original version of the language has
multi-line right-hand sides.
}

@defparam[extend-language-show-extended-order ext-order? boolean?]{

A parameter that controls the rendering of extended languages when
@racket[extend-language-show-union] has a true value.  If this
parameter's value is @racket[#t], then productions are shown as
ordered in the language extension instead of the order of the
original, unextended language.

Defaults to @racket[#f].

@history[#:added "1.2"]}

@defparam[render-reduction-relation-rules 
          rules 
          (or/c false/c 
                (listof (or/c symbol? 
                              string?
                              exact-nonnegative-integer?)))]{
  This parameter controls which rules in a reduction relation
  will be rendered. The strings and symbols match the names of
  the rules and the integers match the position of the rule in
  the original definition.
}

@defparam[rule-pict-style style reduction-rule-style/c]{

This parameter controls the style used by default for the reduction
relation. It can be @racket['horizontal], where the left and
right-hand sides of the reduction rule are beside each other or
@racket['vertical], where the left and right-hand sides of the
reduction rule are above each other.  The @racket['compact-vertical]
style moves the reduction arrow to the second line and uses less space
between lines.  The @racket['vertical-overlapping-side-conditions]
variant, the side-conditions don't contribute to the width of the
pict, but are just overlaid on the second line of each rule.  The
@racket['horizontal-left-align] style is like the @racket['horizontal]
style, but the left-hand sides of the rules are aligned on the left,
instead of on the right. The @racket[''horizontal-side-conditions-same-line]
is like @racket['horizontal], except that side-conditions
are on the same lines as the rule, instead of on their own line below.

}

@defthing[reduction-rule-style/c contract?]{

A contract equivalent to

@racketblock[(or/c 'vertical 
                   'compact-vertical
                   'vertical-overlapping-side-conditions
                   'horizontal
                   'horizontal-left-align
                   'horizontal-side-conditions-same-line
                   (-> (listof rule-pict-info?) pict?))]

The symbols indicate various pre-defined styles. The procedure
implements new styles; it is give the @racket[rule-pict-info?]
values, one for each clause in the reduction relation,
and is expected to combine them into a single @racket[pict?]
}

@defproc[(rule-pict-info? [x any/c]) boolean?]{
  A predicate that recognizes information about a rule for use 
  in rendering the rule as a @racket[pict?].
}
@defproc[(rule-pict-info-arrow [rule-pict-info rule-pict-info?]) symbol?]{
  Extracts the arrow used for this rule. See also @racket[arrow->pict].
}
@defproc[(rule-pict-info-lhs [rule-pict-info rule-pict-info?]) pict?]{
  Extracts a pict for the left-hand side of this rule.
}
@defproc[(rule-pict-info-rhs [rule-pict-info rule-pict-info?]) pict?]{
 Extracts a pict for the right-hand side of this rule.
}
@defproc[(rule-pict-info-label [rule-pict-info rule-pict-info?]) (or/c symbol? #f)]{
 Returns the label used for this rule, unless there is no label
 for the rule or @racket[_computed-label] was used,
 in which case this returns @racket[#f].
}
@defproc[(rule-pict-info-computed-label [rule-pict-info rule-pict-info?]) (or/c pict? #f)]{
  Returns a pict for the typeset version of the label of this rule, when
  @racket[_computed-label] was used. Otherwise, returns @racket[#f].
}
@defproc[(rule-pict-info->side-condition-pict [rule-pict-info rule-pict-info?] 
                                              [max-width real? +inf.0])
         pict?]{
  Builds a pict for the @racket[_side-condition]s and @racket[_where] clauses
  for @racket[rule-pict-info], attempting to keep the width under @racket[max-width].
}


@defparam[arrow-space space natural-number/c]{

This parameter controls the amount of extra horizontal space
around the reduction relation arrow. Defaults to 0.
}

@defparam[label-space space natural-number/c]{

This parameter controls the amount of extra space before the
label on each rule, except in the @racket['vertical] and 
@racket['vertical-overlapping-side-conditions] modes, where
it has no effect. Defaults to 0.
}

@defparam[metafunction-pict-style style 
                                  (or/c 'left-right
                                        'up-down
                                        'left-right/vertical-side-conditions
                                        'up-down/vertical-side-conditions
                                        'left-right/compact-side-conditions
                                        'up-down/compact-side-conditions
                                        'left-right/beside-side-conditions)]{

This parameter controls the style used for typesetting
metafunctions. The @racket['left-right] style means that the
results of calling the metafunction are displayed to the 
right of the arguments and the @racket['up-down] style means that
the results are displayed below the arguments.

The @racket['left-right/vertical-side-conditions] and
@racket['up-down/vertical-side-conditions] variants format side
conditions each on a separate line, instead of all on the same line.

The @racket['left-right/compact-side-conditions] and
@racket['up-down/compact-side-conditions] variants move side
conditions to separate lines to avoid making the rendered form wider
than it would be otherwise.

The @racket['left-right/beside-side-conditions] variant is like
@racket['left-right], except it puts the side-conditions on the 
same line, instead of on a new line below the case.}

@defparam[metafunction-up/down-indent indent (>=/c 0)]{
  Controls the indentation of the right-hand side clauses
  when typesetting metafunctions in one of the up/down
  styles (see @racket[metafunction-pict-style]). 
  
  The value is the amount to indent and it defaults to @racket[0].
 
  @history[#:added "1.2"]
}

@defparam[delimit-ellipsis-arguments? delimit? any/c]{
This parameter controls the typesetting of metafunction definitions
and applications. When it is non-@racket[#f] (the default), commas
precede ellipses that represent argument sequences; when it is 
@racket[#f] no commas appear in those positions.
}

@defparam[white-square-bracket make-white-square-bracket (-> boolean? pict?)]{
This parameter controls the typesetting of the brackets in metafunction
definitions and applications. It is called to supply the two white bracket
picts. If @racket[#t] is supplied, the function should return the open 
white bracket (to be used at the left-hand side of an application) and if
@racket[#f] is supplied, the function should return the close white bracket.

It's default value is @racket[default-white-square-bracket]. See also
@racket[homemade-white-square-bracket].

@history[#:added "1.1"]
}

@defproc[(homemade-white-square-bracket [open? boolean?]) pict?]{
 This function implements the default way that older versions
 of Redex typeset whitebrackets. It uses two overlapping
 @litchar{[} and  @litchar{]} chars with a little whitespace between them.

 @history[#:added "1.1"]
}

@defproc[(default-white-square-bracket [open? boolean?]) pict?]{
 This function returns picts built using
 @litchar{〚} and  @litchar{〛}
 in the style @racket[default-style], using
 @racket[current-text] and @racket[default-font-size].

 If these result in picts that are more than 1/2 whitespace,
 then 1/3 of the whitespace is trimmed from sides (trimmed
 only from the left of the open and the right of the close).
 
 @history[#:added "1.1"]
}

@defparam[linebreaks breaks (or/c #f (listof boolean?))]{
  This parameter controls which cases in the metafunction 
  are rendered on two lines and which are rendered on one.
  
  If its value is a list, the length of the list must match
  the number of cases plus one if there is a contract. 
  Each boolean indicates if that case has a linebreak or not.
  
  This parameter's value influences the @racket['left/right] styles only.
}

@defparam[metafunction-cases 
          cases
          (or/c #f (and/c (listof (or/c exact-nonnegative-integer? 
                                        string?))
                          pair?))]{

Controls which cases in a metafunction are rendered. If it is @racket[#f]
(the default), then all of the cases appear. If it is a list, then only 
the selected cases appear. The numbers indicate the cases counting from
@racket[0] and the strings indicate cases named with @racket[clause-name].

This parameter also controls how which clauses in judgment forms are rendered, but
only in the case that @racket[judgment-form-cases] is @racket[#f] (and in that
case, only the numbers are used).
}
                                  
@defparam[judgment-form-cases 
          cases
          (or/c #f
                (and/c (listof (or/c exact-nonnegative-integer?
                                     string?))
                       pair?))]{
   Controls which clauses in a judgment form are rendered. If it is 
   @racket[#f] (the default), then all of them are rendered. If
   it is a list, then only the selected clauses appear (numbers
   count from @racket[0], and strings correspond to the labels
   in a judgment form).
}

@deftogether[[
@defparam[label-style style text-style/c]{}
@defparam[grammar-style style text-style/c]{}
@defparam[paren-style style text-style/c]{}
@defparam[literal-style style text-style/c]{}
@defparam[metafunction-style style text-style/c]{}
@defparam[non-terminal-style style text-style/c]{}
@defparam[non-terminal-subscript-style style text-style/c]{}
@defparam[non-terminal-superscript-style style text-style/c]{}
@defparam[default-style style text-style/c]{}]]{

These parameters determine the font used for various text in
the picts. See @racket[text] in the texpict collection for
documentation explaining @racket[text-style/c]. One of the more
useful things a style can be is the symbol @racket['roman],
@racket['swiss], or @racket['modern], which corresponds to serif, sans-serif, and
monospaced font, respectively. (A style can encode additional
information, too, such as boldface or italic configuration.)

The @racket[label-style] parameter is used for reduction-rule labels.
The @racket[literal-style] parameter is used for names that aren't
non-terminals that appear in patterns. The
@racket[metafunction-style] parameter is used for the names of
metafunctions. 
The @racket[paren-style] parameter is used for parentheses 
(including ``['', ``]'', ``@"{"'', and ``@"}"'',
as well as ``('' and ``)'') and for keywords, but it is not used for the square brackets of
in-hole decompositions, which use the @racket[default-style] parameter.
The @racket[grammar-style] parameter is used for the ``::='' and ``|''
in grammars.

The @racket[non-terminal-style] parameter is used for the names of non-terminals.
Two parameters style the text in the (optional) ``underscore'' component
of a non-terminal reference. The first, @racket[non-terminal-subscript-style],
applies to the segment between the underscore and the first caret (@racket[^]) 
to follow it; the second, @racket[non-terminal-superscript-style], applies
to the segment following that caret. For example, in the non-terminal 
reference @racket[x_y^z], @racket[x] has style @racket[non-terminal-style],
@racket[y] has style @racket[non-terminal-subscript-style], and @racket[z]
has style @racket[non-terminal-superscript-style].

The @racket[default-style] parameter is used for parenthesis, the dot in dotted
lists, spaces, the
``where'' and ``fresh'' in side-conditions, and other places
where the other parameters aren't used.

@history[#:changed "1.4" @elem{Use @racket[paren-style] for keywords.}]
}

@deftogether[[
@defparam[label-font-size size (and/c (between/c 1 255) integer?)]{}
@defparam[metafunction-font-size size (and/c (between/c 1 255)
                                             integer?)]{}
@defparam[default-font-size size (and/c (between/c 1 255) integer?)]{}]]{

Parameters that control the various font sizes. The
default-font-size is used for all of the font sizes except
labels and metafunctions.
}

@defparam[reduction-relation-rule-separation sep (parameter/c real?)]{  

Controls the amount of space between rule in a reduction
relation. Defaults to 4.

Horizontal and compact-vertical renderings add this parameter's amount to
@racket[(reduction-relation-rule-extra-separation)] to compute
the full separation.
}

@defparam[reduction-relation-rule-extra-separation sep (parameter/c real?)]{  

Controls the amount of space between rule in a reduction
relation for a horizontal or compact-vertical rendering,
in addition to @racket[(reduction-relation-rule-separation)].
Defaults to 4.

@history[#:added "1.7"]}

@defparam[reduction-relation-rule-line-separation sep (parameter/c real?)]{  

Controls the amount of space between lines within a reduction-relation rule.
Defaults to 2.

@history[#:added "1.7"]}

@defparam[curly-quotes-for-strings on? boolean?]{

Controls if the open and close quotes for strings are turned
into @litchar{“} and @litchar{”} or are left as merely @litchar{"}.

Defaults to @racket[#t].
}

@defparam[current-text proc (-> string? text-style/c number? pict?)]{

A parameter whose value is a function to be called whenever Redex typesets
some part of a grammar, reduction relation, or
metafunction. It defaults to the @racketmodname[pict] 
library's @racket[text] function.
}

@defproc[(arrow->pict [arrow symbol?]) pict?]{
  Returns the pict corresponding to @racket[arrow].
}

@defproc[(set-arrow-pict! [arrow symbol?] [proc  (-> pict?)]) void?]{

Sets the pict for a given reduction-relation
symbol. When typesetting a reduction relation that uses the
symbol, the thunk will be invoked to get a pict to render
it. The thunk may be invoked multiple times when rendering a
single reduction relation.
}

@defparam[white-bracket-sizing proc (-> string? number? (values number? number? number? number?))]{

  A parameter whose value is a function to be used when typesetting metafunctions to
  determine how to create the @"\u27e6\u27e7"
  characters with @racket[homemade-white-square-bracket], which
  combines two @litchar{[} characters
  or two @litchar{]} characters together.
  
  The procedure accepts a string that is either @racket["["]
  or @racket["]"], and it returns four numbers. The first two
  numbers determine the offset (from the left and from the
  right respectively) for the second square bracket, and the
  second two two numbers determine the extra space added (to
  the left and to the right respectively).

  The default value of the parameter is: @racketblock[
     (λ (str size)
       (let ([inset-amt (floor/even (max 4 (* size 1/2)))])
         (cond
           [(equal? str "[")
            (values inset-amt
                    0
                    0
                    (/ inset-amt 2))]
           [else
            (values 0
                    inset-amt
                    (/ inset-amt 2)
                    0)])))]

 where @racket[floor/even] returns the nearest even number
 below its argument.  This means that for sizes 9, 10, and
 11, @racket[inset-amt] will be 4, and for 12, 13, 14, and
 15, @racket[inset-amt] will be 6.

}

@defparam[horizontal-bar-spacing space (parameter/c exact-nonnegative-integer?)]{
  Controls the amount of space around the horizontal bar when rendering
  a relation (that was created by @racket[define-relation]). Defaults
  to @racket[4].
}

@defparam[metafunction-gap-space gap-space real?]{
  Controls the amount of vertical space between different metafunctions
  rendered together with @racket[render-metafunctions].
  
  Defaults to @racket[2].
  
  @history[#:added "1.7"]
}

@defparam[metafunction-rule-gap-space gap-space real?]{
  Controls the amount of vertical space between different rules
  within a metafunction as rendered with @racket[render-metafunction]
  or @racket[render-metafunctions].
  
  Defaults to @racket[2].
  
  @history[#:added "1.7"]
}

@defparam[metafunction-line-gap-space gap-space real?]{
  Controls the amount of vertical space between different lines
  within a metafunction rule as rendered with @racket[render-metafunction]
  or @racket[render-metafunctions].
  
  Defaults to @racket[2].
  
  @history[#:added "1.7"]
}

@defparam[metafunction-combine-contract-and-rules combine (pict? pict? . -> . pict?)]{
  Controls the combination of a contract with the rules of a metafunction
  when contract rendering is enabled. The first argument to the combining function
  is a pict for the contract, and the second argument is a pict for the rules.

  The default combining function uses @racket[vl-append] with a separation
  of @racket[(metafunction-rule-gap-space)].

 @history[#:added "1.7"]
}

@defparam[relation-clauses-combine combine 
                                   (parameter/c (-> (listof pict?) pict?))]{
  The @racket[combine] function is called with the list of picts that are obtained by rendering
  a relation; it should put them together into a single pict. It defaults to
  @racket[(λ (l) (apply vc-append 20 l))]
}

@defparam[where-make-prefix-pict make-prefix (parameter/c (-> pict?))]{
  The @racket[make-prefix] function is called with no arguments to generate a pict
  that prefixes @tech{@racket[where] clauses}. It defaults to a function that
  produces a pict for ``where'' surrounded by spaces using the default style.
}

@defparam[where-combine combine (parameter/c (-> pict? pict? pict?))]{
  The @racket[combine] function is called with picts for the left and right
  side of a where clause, and it should put them together into a single pict. It defaults to
  @racket[(λ (l r) (hbl-append l _=-pict r))], where @racket[_=-pict] is an equal
  sign surrounded by spaces using the default style.
}

@defparam[current-render-pict-adjust adjust (pict? symbol? . -> . pict?)]{
 A parameter whose value is a function to adjusts picts generated as
 various parts of a rendering. The symbol that is provided to the function
 indicates the role of the pict. A pict-adjusting function might be installed
 to ensure consistent spacing among multiple lines in a metafunction's
 rendering, for example, or to adjust the color of side-condition terms.

 The set of roles is meant to be extensible, and the currently
 provided role symbols are as follows:

 @itemlist[ 

   @item{@racket['lw-line] --- a line with a render term (including
         any term that fits on a single line)}

   @item{@racket['language-line] --- a line on the right-hand side of
         a production in a language grammar.}

   @item{@racket['language-production] --- a production (possibly
         multiple lines) within a language grammar.}

   @item{@racket['side-condition-line] --- a line within a side condition
         for a reduction-relation rule or metafunction rule}

   @item{@racket['side-condition] --- a single side condition with a
         group of side conditions for a reduction-relation rule or 
         a metafunction rule}

   @item{@racket['side-conditions] --- a group of side conditions
         for a reduction-relation rule or a metafunction rule
         including the ``where'' prefix added by
         @racket[(where-make-prefix-pict)]}

   @item{@racket['reduction-relation-line] --- a single line within a
         reduction-relation rule}

   @item{@racket['reduction-relation-rule] --- a single rule within a
         reduction relation}

   @item{@racket['metafunction-contract] --- a contract for a metafunction}

   @item{@racket['metafunction-line] --- a line within a metafunction rule}

   @item{@racket['metafunction-rule] --- a single rule within a metafunction}

   @item{@racket['metafunctions-metafunction] --- a single
        metafunction within a group of metafunctions that are rendered
        together}

 ]

  @history[#:added "1.7"]
}



@section[#:tag "pink"]{Removing the Pink Background}

@declare-exporting[redex/pict redex]

When reduction rules, a metafunction, or a grammar contains
unquoted Racket code or side-conditions, they are rendered
with a pink background as a guide to help find them and
provide an alternative typesetting for them. In general, a
good goal for a PLT Redex program that you intend to typeset
is to only include such things when they correspond to
standard mathematical operations, and the Racket code is an
implementation of those operations.

To replace the pink code, use:

@defform[(with-unquote-rewriter proc expression)]{

Installs @racket[proc] as the current unquote rewriter and
evaluates @racket[expression]. If that expression computes any picts,
the unquote rewriter specified is used to remap them.

The @racket[proc] must match the contract @racket[(-> lw? lw?)].
Its result should be the rewritten version version of the input.
}

@defform[(with-atomic-rewriter name-symbol
                               string-or-thunk-returning-pict
                               expression)]{

Extends the current set of atomic-rewriters with one
new one that rewrites the value of name-symbol to
@racket[string-or-pict-returning-thunk] (applied, in the case of a
thunk), during the evaluation of expression.

@racket[name-symbol] is expected to evaluate to a symbol. The value
of @racket[string-or-thunk-returning-pict] is used whenever the symbol
appears in a pattern.
}

@defform[(with-compound-rewriter name-symbol
                                 proc
                                 expression)]{

Extends the current set of compound-rewriters with one
new one that rewrites the value of name-symbol via proc,
during the evaluation of expression.

@racket[name-symbol] is expected to evaluate to a symbol. The value
of proc is called with a @racket[(listof lw)], and is expected to
return a new @racket[(listof (or/c lw? string? pict?))],
rewritten appropriately. 

The list passed to the rewriter corresponds to the
@racket[lw] for the sequence that has name-symbol's value at
its head.

The result list is constrained to have at most 2 adjacent
non-@racket[lw]s. That list is then transformed by adding
@racket[lw] structs for each of the non-@racket[lw]s in the
list (see the text just below the description of @racket[lw] for a
explanation of logical space):

@itemize[
@item{
    If there are two adjacent @racket[lw]s, then the logical
    space between them is filled with whitespace.}

@item{
    If there is a pair of @racket[lw]s with just a single
    non-@racket[lw] between them, a @racket[lw] will be
    created (containing the non-@racket[lw]) that uses all
    of the available logical space between the @racket[lw]s.
}

@item{
    If there are two adjacent non-@racket[lw]s between two
    @racket[lw]s, the first non-@racket[lw] is rendered
    right after the first @racket[lw] with a logical space
    of zero, and the second is rendered right before the
    last @racket[lw] also with a logical space of zero, and
    the logical space between the two @racket[lw]s is
    absorbed by a new @racket[lw] that renders using no
    actual space in the typeset version.
}]

One useful way to take advantage of @racket[with-compound-rewriters]
is to return a list that begins and ends with @racket[""] (the
empty string). In that situation, any extra logical space that
would have been just outside the sequence is replaced with an 
@racket[lw] that does not draw anything at all.

}

@defform[(with-compound-rewriters ([name-symbol proc] ...)
                                  expression)]{
Shorthand for nested @racket[with-compound-rewriter] expressions.}

@section{LWs}
                                              
@defstruct[lw ([e (or/c string?
                        symbol?
                        pict? 
                        (listof (or/c (symbols 'spring) lw?)))]
               [line exact-positive-integer?]
               [line-span exact-positive-integer?]
               [column exact-positive-integer?]
               [column-span exact-positive-integer?]
               [unq? boolean?]
               [metafunction? boolean?])
              #:mutable]{
The @racket[lw] data structure corresponds represents a pattern or a Racket
expression that is to be typeset.  The functions listed above
construct @racket[lw] structs, select fields out of them, and
recognize them. The @racket[lw] binding can be used with
@racket[copy-struct].

The values of the @racket[unq?] and @racket[metafunction?] fields, respectively,
indicate whether the @racket[lw] represents an unquoted expression or a 
metafunction application. See @racket[to-lw] for the meanings of the other fields.
}

@defproc[(build-lw [e (or/c string?
                            symbol?
                            pict? 
                            (listof (or/c (symbols 'spring) lw?)))]
                   [line exact-positive-integer?]
                   [line-span exact-positive-integer?]
                   [column exact-positive-integer?]
                   [column-span exact-positive-integer?]) 
         lw?]{
Like @racket[make-lw] but specialized for constructing @racket[lw]s that
do not represent unquoted expressions or metafunction applications.
}

@defform[(to-lw arg)]{

Turns @racket[arg] into @racket[lw] structs that
contain all of the spacing information just as it would appear
when being used to typeset.

Each sub-expression corresponds to its own lw, and
the element indicates what kind of sub-expression it is. If
the element is a list, then the lw corresponds to a
parenthesized sequence, and the list contains a lw
for the open paren, one lw for each component of the
sequence and then a lw for the close
parenthesis. In the case of a dotted list, there will also
be a lw in the third-to-last position for the dot.

For example, this expression:

@racketblock[(a)]

becomes this lw (assuming the above expression
appears as the first thing in the file):

@racketblock[
     (build-lw (list (build-lw "(" 0 0 0 1)
                     (build-lw 'a 0 0 1 1)
                     (build-lw ")" 0 0 2 1))
               0 0 0 3)
]

If there is some whitespace in the sequence, like this one:

@racketblock[
  (a b)
]

then there is no lw that corresponds to that
whitespace; instead there is a logical gap between the
lws.

@racketblock[
     (build-lw (list (build-lw "(" 0 0 0 1)
                     (build-lw 'a 0 0 1 1)
                     (build-lw 'b 0 0 3 1)
                     (build-lw ")" 0 0 4 1))
               0 0 0 5)
]

In general, identifiers are represented with symbols and
parenthesis are represented with strings and @racket[pict]s can be
inserted to render arbitrary pictures.

The line, line-span, column, and column-span correspond to
the logical spacing for the redex program, not the actual
spacing that will be used when they are rendered. The
logical spacing is only used when determining where to place
typeset portions of the program. In the absence of any
rewriters, these numbers correspond to the line and column
numbers in the original program.

The line and column are absolute numbers from the beginning
of the file containing the expression. The column number is
not necessarily the column of the open parenthesis in a
sequence -- it is the leftmost column that is occupied by
anything in the sequence. The line-span is the number of
lines, and the column span is the number of columns on the
last line (not the total width).

When there are multiple lines, lines are aligned based on
the logical space (i.e., the line/column &
line-span/column-span) fields of the lws. As an
example, if this is the original pattern:

@racketblock[
   (all good boys
        deserve fudge)
]

then the leftmost edges of the words "good" and "deserve"
will be lined up underneath each other, but the relative
positions of "boys" and "fudge" will be determined by the
natural size of the words as they rendered in the
appropriate font.

When @racket['spring] appears in the list in the @racket[e]
field of a @racket[lw] struct, then it absorbs all of the
space around it. It is also used by @racket[to-lw] when
constructing the picts for unquoted strings. For example, this expression

@racketblock[,x]

corresponds to these structs:

@racketblock[(build-lw (list (build-lw "" 1 0 9 0)
                             'spring
                             (build-lw x 1 0 10 1))
                       1 0 9 2)]

and the @racket['spring] causes there to be no space between
the empty string and the @racket[x] in the typeset output.

}

@defproc[(to-lw/stx [stx syntax?]) lw?]{
  A procedure variant of @racket[to-lw]; it accepts a 
  syntax object and returns the corresponding @racket[lw] structs.
  It only uses the location information in the syntax object,
  so metafunctions will not be rendered properly.
}

@defproc[(render-lw (language/nts (or/c (listof symbol?) compiled-lang?))
                    (lw lw?)) pict?]{

  Produces a pict that corresponds to the @racket[lw] object
  argument, using @racket[language/nts] to determine which
  of the identifiers in the @racket[lw] argument are
  non-terminals.

  This function sets @racket[dc-for-text-size]. See also
  @racket[lw->pict].
}

@defproc[(lw->pict (language/ntw (or/c (listof symbol?) compiled-lang?))
                   (lw lw?)) pict?]{

  Produces a pict that corresponds to the @racket[lw] object
  argument, using @racket[language/nts] to determine which
  of the identifiers in the @racket[lw] argument are
  non-terminals.

  This function does not set the @racket[dc-for-text-size] parameter. See also
  @racket[render-lw].
}

@deftogether[[
@defproc[(just-before [stuff (or/c pict? string? symbol?)]
                      [lw lw?])
                     lw?]{}
@defproc[(just-after [stuff (or/c pict? string? symbol?)]
                     [lw lw?])
                    lw?]{}]]{
These two helper functions build new lws whose contents are
the first argument, and whose line and column are based on
the second argument, making the new loc wrapper be either
just before or just after that argument. The line-span and
column-span of the new lw is always zero.
}

@include-section["dynamic-typesetting-and-macros.scrbl"]
