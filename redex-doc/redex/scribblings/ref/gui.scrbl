#lang scribble/manual
@(require (for-label racket/base
                     (except-in racket/gui make-color)
                     racket/pretty
                     racket/contract
                     mrlib/graph
                     (except-in 2htdp/image make-pen text)
                     (only-in pict pict? text dc-for-text-size text-style/c
                              vc-append hbl-append vl-append)
                     redex))

@title{GUI}

@defmodule*/no-declare[(redex/gui)]
@declare-exporting[redex/gui redex]

This section describes the GUI tools that Redex provides for
exploring reduction sequences.

@defproc[(traces [reductions (or/c reduction-relation? IO-judgment-form?)] 
                 [expr (or/c any/c (listof any/c))]
                 [#:multiple? multiple? boolean? #f]
                 [#:reduce reduce (-> reduction-relation? any/c
                                      (listof (list/c (union false/c string?) any/c)))
                           apply-reduction-relation/tag-with-names]
                 [#:pred pred
                         (or/c (-> sexp any)
                               (-> sexp term-node? any))
                         (λ (x) #t)]
                 [#:pp pp
                       (or/c (any -> string)
                             (any output-port number (is-a?/c text%) -> void))
                       default-pretty-printer]
                 [#:colors colors 
                  (listof 
                   (cons/c string? 
                           (and/c (listof (or/c string? (is-a?/c color%)))
                                  (λ (x) (<= 0 (length x) 6)))))
                  '()]
                 [#:racket-colors? racket-colors? boolean? #t]
                 [#:scheme-colors? scheme-colors? boolean? racket-colors?]
                 [#:filter term-filter (-> any/c (or/c #f string?) any/c) (λ (x y) #t)]
                 [#:x-spacing x-spacing real? 15]
                 [#:y-spacing y-spacing real? 15]
                 [#:layout layout (-> (listof term-node?) void?) void]
                 [#:edge-labels? edge-labels? boolean? #t]
                 [#:edge-label-font edge-label-font (or/c #f (is-a?/c font%)) #f]
                 [#:graph-pasteboard-mixin graph-pasteboard-mixin 
                                           (make-mixin-contract graph-pasteboard<%>)
                                           values])
         void?]{

This function opens a new window and inserts each expression
in @racket[expr] (if @racket[multiple?] is @racket[#t] -- if
@racket[multiple?] is @racket[#f], then @racket[expr] is treated as a single
expression). Then, it reduces the terms until at least
@racket[reduction-steps-cutoff] (see below) different terms are
found, or no more reductions can occur. It inserts each new
term into the gui. Clicking the @onscreen{reduce} button reduces
until @racket[reduction-steps-cutoff] more terms are found.

The @racket[reduce] function applies the reduction relation to the terms.
By default, it is @racket[apply-reduction-relation/tag-with-names];
it may be changed to only return a subset of the possible reductions,
for example, but it must satisfy the same contract as
@racket[apply-reduction-relation/tag-with-names].

If @racket[reductions] is an @racket[IO-judgment-form?], then the judgment
form is treated as a reduction relation. The initial input position is
the given @racket[expr] and the output position becomes the next input.

The @racket[pred] function indicates if a term has a particular
property. If it returns @racket[#f], the term is displayed with a
pink background. If it returns a string or a @racket[color%] object,
the term is displayed with a background of that color (using
@racket[the-color-database] to map the string to a color). If it
returns any other value, the term is displayed normally. If
the @racket[pred] function accepts two arguments, a term-node
corresponding to the term is passed to the predicate. This
lets the predicate function explore the (names of the)
reductions that led to this term, using @racket[term-node-children],
@racket[term-node-parents], and @racket[term-node-labels].

The @racket[pred] function may be called more than once per node. In
particular, it is called each time an edge is added to a
node. The latest value returned determines the color.

The @racket[pp] function is used to specially print expressions. It
must either accept one or four arguments. If it accepts one
argument, it will be passed each term and is expected to
return a string to display the term.

If the @racket[pp] function takes four arguments, it should render
its first argument into the port (its second argument) with
width at most given by the number (its third argument). The
final argument is the text where the port is connected --
characters written to the port go to the end of the editor.
Use @racket[write-special] to send @racket[snip%] objects or 
@racketmodname[2htdp/image] images 
(or other things that subscribe to @racketmodname[file/convertible]
or @racketmodname[pict/convert])
directly to the editor.

The @racket[colors] argument, if provided, specifies a list of
reduction-name/color-list pairs. The traces gui will color arrows
drawn because of the given reduction name with the given color instead
of using the default color.

The @racket[cdr] of each of the elements of @racket[colors] is a list
of colors, organized in pairs. The first two colors cover the colors
of the line and the border around the arrow head, the first when the
mouse is over a graph node that is connected to that arrow, and the
second for when the mouse is not over that arrow. Similarly, the next
colors are for the text drawn on the arrow and the last two are for
the color that fills the arrow head.  If fewer than six colors are
specified, the specified colors are used and then defaults are
filled in for the remaining colors.

The @racket[racket-colors?] argument (along with @racket[scheme-colors?],
retained for backward compatibility), controls the coloring of 
each window. When @racket[racket-colors?] is @racket[#t] (and
@racket[scheme-colors?] is @racket[#t] too), @racket[traces] colors the 
contents according to DrRacket's Racket-mode color scheme; otherwise,
@racket[traces] uses a black color scheme.

The @racket[term-filter] function is called each time a new node is
about to be inserted into the graph. If the filter returns false, the
node is not inserted into the graph.

The @racket[x-spacing] and @racket[y-spacing] arguments control the amount of
space put between the snips in the default layout.

The @racket[layout] argument is called (with all of the terms) when
new terms are inserted into the window. In general, it is called
after new terms are inserted in response to the user clicking on the
reduce button, and after the initial set of terms is inserted.
See also @racket[term-node-set-position!].

If @racket[edge-labels?] is @racket[#t] (the default), then edge labels
are drawn; otherwise not.

The @racket[edge-label-font] argument is used as the font on the edge
labels. If @racket[#f] is supplied, the @racket[dc<%>] object's default
font is used.

The traces library uses an instance of the @racketmodname[mrlib/graph]
library's @racket[graph-pasteboard<%>] interface to layout
the graphs.  Sometimes, overriding one of its methods can
help give finer-grained control over the layout, so the
@racket[graph-pasteboard-mixin] is applied to the class
before it is instantiated. Also note that all of the snips
inserted into the editor by this library have a
@tt{get-term-node} method which returns the snip's
@racket[term-node].

For a more serious example of @racket[traces], please see @secref["tutorial"],
but for a silly one that demonstrates how the @racket[pp] argument
lets us use images, we can take the pairing functions discussed in
Matthew Szudzik's @italic{An Elegant Pairing Function} presentation:
@racketblock[(define/contract (unpair z)
               (-> exact-nonnegative-integer? 
                   (list/c exact-nonnegative-integer? exact-nonnegative-integer?))
               (define i (integer-sqrt z))
               (define i2 (* i i))
               (cond
                 [(< (- z i2) i)
                  (list (- z i2) i)]
                 [else 
                  (list i (- z i2 i))]))
             
             (define/contract (pair x y)
               (-> exact-nonnegative-integer? exact-nonnegative-integer?
                   exact-nonnegative-integer?)
               (if (= x (max x y))
                   (+ (* x x) x y)
                   (+ (* y y) x)))]
and build a reduction relation out of them:
@racketblock[(define-language L (n ::= natural))
             (define red
               (reduction-relation
                L
                (--> (n_1 n_2)
                     ,(unpair (+ 1 (pair (term n_1) 
                                         (term n_2)))))))
             (traces red (term (0 0)))]
We can then turn those two numbers into two stars, where the
number indicates the number of points in the star:
@racketblock[(require 2htdp/image)
             (define/contract (two-stars point-count1 point-count2)
               (-> (>=/c 2) (>=/c 2) image?)
               (overlay
                (radial-star (+ 2 point-count1)
                             10 60
                             "solid"
                             (make-color 255 0 255 150))
                (radial-star (+ 2 point-count2)
                             10 60
                             "solid"
                             "cornflowerblue")))]
and then use the @racket[pp] function to show those in the
traces window instead of just the numbers.
@racketblock[(traces red 
                     (term (0 0))
                     #:pp
                     (λ (term port w txt)
                       (write-special 
                        (two-stars (+ 2 (list-ref term 0))
                                   (+ 2 (list-ref term 1)))
                        port)))]

}

@defproc[(traces/ps [reductions (or/c reduction-relation? IO-judgment-form?)] 
                    [expr (or/c any/c (listof any/c))]
                    [file (or/c path-string? path?)]
                    [#:multiple? multiple? boolean? #f]
                    [#:reduce reduce (-> reduction-relation? any/c
                                         (listof (list/c (union false/c string?) any/c)))
                              apply-reduction-relation/tag-with-names]
                    [#:pred pred
                            (or/c (-> sexp any)
                                  (-> sexp term-node? any))
                            (λ (x) #t)]
                    [#:pp pp
                          (or/c (any -> string)
                                (any output-port number (is-a?/c text%) -> void))
                          default-pretty-printer]
                    [#:colors colors 
                              (listof 
                               (cons/c string?
                                       (and/c (listof (or/c string? (is-a?/c color%)))
                                              (λ (x) (<= 0 (length x) 6)))))
                              '()]
                    [#:filter term-filter (-> any/c (or/c #f string?) any/c) (λ (x y) #t)]
                    [#:layout layout (-> (listof term-node?) void?) void]
                    [#:x-spacing x-spacing number? 15]
                    [#:y-spacing y-spacing number? 15]
                    [#:edge-labels? edge-labels? boolean? #t]
                    [#:edge-label-font edge-label-font (or/c #f (is-a?/c font%)) #f]
                    [#:graph-pasteboard-mixin graph-pasteboard-mixin 
                                              (make-mixin-contract graph-pasteboard<%>)
                                              values]
                    [#:post-process post-process (-> (is-a?/c graph-pasteboard<%>) any/c)])
         void?]{

This function  behaves just like the function @racket[traces], but
instead of opening a window to show the reduction graph, it just saves
the reduction graph to the specified @racket[file].

All of the arguments behave like the arguments to @racket[traces],
with the exception of the @racket[post-process] argument. It is called
just before the PostScript is created with the graph pasteboard.
}

@defproc[(stepper [reductions (or/c reduction-relation? IO-judgment-form?)] 
                  [t any/c] 
                  [pp (or/c (any -> string)
                            (any output-port number (is-a?/c text%) -> void))
                      default-pretty-printer])
          void?]{

This function opens a stepper window for exploring the
behavior of the term @racket[t] in the reduction system given by
@racket[reductions].

The @racket[pp] argument is the same as to the
@racket[traces] function but is here for
backwards compatibility only and
should not be changed for most uses, but instead adjusted with
@racket[pretty-print-parameters]. Specifically, the 
highlighting shown in the stepper window can be wrong if
@racket[default-pretty-printer] does not print sufficiently similarly
to how @racket[pretty-print] prints (when adjusted by
@racket[pretty-print-parameters]'s behavior, of course).
}

@defproc[(stepper/seed [reductions (or/c reduction-relation? IO-judgment-form?)]
                       [seed (cons/c any/c (listof any/c))]
                       [pp (or/c (any -> string)
                                 (any output-port number (is-a?/c text%) -> void))
                           default-pretty-printer])
         void?]{

Like @racket[stepper], this function opens a stepper window, but it
seeds it with the reduction-sequence supplied in @racket[seed].
}

@defproc[(show-derivations [derivations (cons/c derivation? (listof derivation?))]
                           [#:pp pp
                                 (or/c (any -> string)
                                       (any output-port number (is-a?/c text%) -> void))
                                 default-pretty-printer]
                           [#:racket-colors? racket-colors? boolean? #f]
                           [#:init-derivation init-derivation exact-nonnegative-integer? 0])
         any]{
  Opens a window to show @racket[derivations]. 
                         
  The @racket[pp] and @racket[racket-colors?] arguments are like those to @racket[traces].
  
  The initial derivation shown in the window is chosen by @racket[init-derivation], used
  as an index into @racket[derivations].
}

@defproc[(derivation/ps [derivation derivation?]
                        [filename path-string?]
                        [#:pp pp
                              (or/c (any -> string)
                                    (any output-port number (is-a?/c text%) -> void))
                              default-pretty-printer]
                        [#:racket-colors? racket-colors? boolean? #f]
                        [#:post-process post-process (-> (is-a?/c pasteboard%) any)])
         void?]{
                
  Like @racket[show-derivations], except it prints a single
  derivation in PostScript to @racket[filename].
}

@defproc[(term-node-children [tn term-node?]) (listof term-node?)]{

Returns a list of the children (i.e., terms that this term
reduces to) of the given node.

Note that this function does not return all terms that this
term reduces to -- only those that are currently in the
graph.
}

               
@defproc[(term-node-parents [tn term-node?]) (listof term-node?)]{

Returns a list of the parents (i.e., terms that reduced to the
current term) of the given node.

Note that this function does not return all terms that
reduce to this one -- only those that are currently in the
graph.
}
@defproc[(term-node-labels [tn term-node?]) (listof (or/c false/c string?))]{

Returns a list of the names of the reductions that led to
the given node, in the same order as the result of
term-node-parents. If the list contains @racket[#f], that means that
the corresponding step does not have a label.
}

@defproc[(term-node-set-color! [tn term-node?] [color (or/c string? (is-a?/c color%) false/c)])
         void?]{

Changes the highlighting of the node; if its second argument
is @racket[#f], the coloring is removed, otherwise the color is set
to the specified @racket[color%] object or the color named by the
string. The @racket[color-database<%>] is used to convert the string
to a @racket[color%] object.
}

@defproc[(term-node-color [tn term-node?]) (or/c string? (is-a?/c color%) false/c)]{

Returns the current highlighting of the node. See also @racket[term-node-set-color!].
}


@defproc[(term-node-set-red! [tn term-node?] [red? boolean?]) void?]{

Changes the highlighting of the node; if its second argument
is @racket[#t], the term is colored pink, if it is @racket[#f], the term is
not colored specially.

}

@defproc[(term-node-expr [tn term-node?]) any]{

Returns the expression in this node.
}

@defproc[(term-node-set-position! [tn term-node?] 
                                  [x (and/c real? positive?)]
                                  [y (and/c real? positive?)])
         void?]{

Sets the position of @racket[tn] in the graph to (@racket[x],@racket[y]). 
}

@defproc[(term-node-x [tn term-node?]) real?]{
Returns the @tt{x} coordinate of @racket[tn] in the window.
}
@defproc[(term-node-y [tn term-node?]) real?]{
Returns the @tt{y} coordinate of @racket[tn] in the window.
}
@defproc[(term-node-width [tn term-node?]) real?]{
Returns the width of @racket[tn] in the window.
}
@defproc[(term-node-height [tn term-node?]) real?]{
Returns the height of @racket[tn] in the window.
}

@defproc[(term-node? [v any/c]) boolean?]{

Recognizes term nodes.
}

@defparam[reduction-steps-cutoff cutoff number?]{

A parameter that controls how many steps the @racket[traces] function
takes before stopping.
}

@defparam[initial-font-size size number?]{

A parameter that controls the initial font size for the terms shown
in the GUI window.
}

@defparam[initial-char-width width (or/c number? (-> any/c number?))]{

A parameter that determines the initial width of the boxes
where terms are displayed (measured in characters) for both
the stepper and traces.

If its value is a number, then the number is used as the width for 
every term. If its value is a function, then the function is called
with each term and the resulting number is used as the width.
}

@deftogether[[
@defparam[dark-pen-color color (or/c string? (is-a?/c color<%>))]{}
@defparam[dark-brush-color color (or/c string? (is-a?/c color<%>))]{}
@defparam[light-pen-color color (or/c string? (is-a?/c color<%>))]{}
@defparam[light-brush-color color (or/c string? (is-a?/c color<%>))]{}
@defparam[dark-text-color color (or/c string? (is-a?/c color<%>))]{}
@defparam[light-text-color color (or/c string? (is-a?/c color<%>))]{}]]{

These six parameters control the color of the edges in the graph.

The dark colors are used when the mouse is over one of the nodes that
is connected to this edge. The light colors are used when it isn't.

The pen colors control the color of the line. The brush colors control
the color used to fill the arrowhead and the text colors control the
color used to draw the label on the edge.
}

@defparam[pretty-print-parameters f (-> (-> any/c) any/c)]{
  A parameter that is used to set other @racket[pretty-print]
  parameters. 
  
  Specifically, whenever @racket[default-pretty-printer] prints
  something it calls @racket[f] with a thunk that does the actual
  printing. Thus, @racket[f] can adjust @racket[pretty-print]'s
  parameters to adjust how printing happens.

}

@defproc[(default-pretty-printer 
           [v any/c] 
           [port output-port?]
           [width exact-nonnegative-integer?]
           [text (is-a?/c text%)])
         void?]{

This is the default value of @racket[pp] used by @racket[traces] and
@racket[stepper] and it uses
@racket[pretty-print]. 

This function uses the value of @racket[pretty-print-parameters] to adjust how it prints.

It sets the @racket[pretty-print-columns] parameter to
@racket[width], and it sets @racket[pretty-print-size-hook]
and @racket[pretty-print-print-hook] to print holes and the
symbol @racket['hole] to match the way they are input in a
@racket[term] expression.

}
