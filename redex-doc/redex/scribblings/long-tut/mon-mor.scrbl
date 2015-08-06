#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "mon-mor"]{The Theoretical Framework}

@goals[

@item{abstract syntax}
@item{notions of reduction, substitution}
@item{reductions and calculations}
@item{semantics}
@item{standard reduction}
@item{abstract register machines}
@item{types}

]

The lambda calculus:

@ntt{e = x | (\x.e) | (e e)}

Terms vs trees, abstract over concrete syntax

Encode some forms of primitives: numbers, booleans -- good for theory of
computation; mostly irrelevant for PL. extensions with primitive data

@ntt{e = x | (\x.e) | (e e) | tt | ff | (if e e e)}

What we want: develop LC as a @emph{model} of a PL. Because of history,
this means two things: a simple logic for calculating with the terms of the
language @tt{e == e'} and a system for determining the value of a
program. The former is the @deftech{calculus}, the latter is the
@deftech{semantics}. 

Both start with basic notions of reduction (axioms). They are just relation
on terms:

@ntt{ ((\x.e) e') beta e[x=e'] } pronounced: e with x replaced by e'
@ntt{ ((\x.e) e') beta [e'/x]e} pronounced substitute e' for x in e 

@bold{Think} substitution via tree surgery, preserving bindings 

Here are two more, often done via external interpretation functions (δ)

@ntt{(if tt e e') if-tt e} 
@ntt{(if ff e e') if-ff e'}

If this is supposed to be a theory of functions (and if expressions) we
need to be able to use this relations @emph{in context}

@verbatim[#:indent 4]{
      e xyz e'    
  --------------
      e  =  e'  

      e = e'                 e = e'                 e = e'    
  --------------         --------------	        --------------
  e e'' = e' e''         e'' e = e'' e'	         \x.e  = \x.e'

  plus reflexivity, symmetry, and transitivity 
}
for any relation @tt{xyz}

Now you have an equational system. what's it good for? you can prove such
facts as 

@ntt{e (Y e) = (Y e)}

meaning @emph{every single term has a fixpoint}

All of the above is mathematics but it is just that,
mathematics. It might be considered theory of computation,
but it is not theory of programming languages. But we can
use these ideas to create a theory of programming languages.
Plotkin's 1974 TCS paper on call-by-name versus
call-by-value shows how to create a theory of programming
languages.

In addition, Plotkin's paper also sketches several research programs,
mostly on scaling up his ideas to the full spectrum of languages but also
on the precise connection between by-value and by-name their relationship,
both at the proof-theoretical level as well as at the model-theoretic
level.

Here is Plotkin's idea as a quasi-algorithm: 
@itemlist[#:style 'ordered

@item{Start from an abstract syntax, plus notions of scope and
scope-preserving substitution. Consider closed terms @deftech{Program}s.}

@item{Identify a subset of expressions as @deftech{Value}s. Use @tt{v} to
range over @tech{Value}s.

@bold{Note} The complement of this set was (later) dubbed
@deftech{computations}, due to Moggi's work under Plotkin.}

@item{Define basic notions of reduction (axioms). Examples: 

@ntt{((\x.e) e') beta-name e[x=e']}
@ntt{((\x.e) v) beta-value e[x=v]}

}

@item{Inductively generate an equational theory from the basic notions of
reduction.}

@item{This theory defines a semantics, that is, a relation @italic{eval}
from programs to values:

@ntt{eval : Program x Value}
@ntt{@bold{def} e eval v iff e = v}
}

@item{Prove that @italic{eval} is a function, and you have got yourself a
@emph{specification} of an interpreter.

@ntt{eval : Program -> Value}
@ntt{eval(e) = v}

@bold{Note} This step often reuses a variant of the Church-Rosser theorem
of the mathematical theory of lambda calculus.}

@item{Prove that the calculus satisfies a Curry-Feys standard reduction
property. This gives you a second semantics: 

@ntt{eval-standard : Program -> Value}
@ntt{@bold{def} eval-standard(e) = v iff e standard reduces to v}

The new semantics is correct:
@ntt{@bold{Theorem} eval-standard = eval}

@deftech{Standard reduction} is a strategy for the lambda calculus, that
is, a function that picks the next reducible expression (called
@deftech{redex}) to reduce. Plotkin specifically uses the
leftmost-outermost strategy but others may work, too.}

]
Plotkin also shows---on an ad hoc basis---that this evaluator function is
equivalent to Landin's evaluator based on the SECD machine, an abstract
register machine.

Plotkin (following Morris, 1968) uses step 6 from above to add two ideas: 
@itemlist[

@item{The interpreter of a programming language (non-constructively)
 generates a theory of equivalence on phrases. 

@ntt{@bold{def} e ~ e' iff placing e and e' into any context yields
programs that produce the same observable behavior according to eval}

@bold{Theorem} @tt{~} is the coarsest equivalence theory and thus unique.

Let's call @tt{~} the @deftech{Truth}.}

@item{@bold{Theorem} e = e' implies e ~ e'. Naturally the reverse doesn't hold.}
]

Matthias's (post)dissertation research extends Plotkin's work in two
directions: 
@;
@itemlist[#:style 'ordered

@item{Plotkin's ``algorithm'' applies to imperative programming language,
 especially those extending the lambda calculus syntax with (variable)
 assignment and non-local control operators.

@Secref{wed-mor} explains how two of these work.}

@item{It is possible to derive useful abstract register machines from the
standard reduction semantics of the programming language

Each machine @tt{M} defines a new semantics: 
@ntt{@bold{def} eval-M(e) = v iff load M with e, run, unload, yields v}

For each of these functions, we can prove an equivalence theorem.

@ntt{@bold{Theorem} eval-M = eval-standard = eval}}

]
@;
His work also shows how this approach greatly simplifies proofs of
consistency for the semantics of programming languages and especially
so-called type soundness theorems. 
