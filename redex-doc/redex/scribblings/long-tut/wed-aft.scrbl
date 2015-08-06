#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "wed-aft"]{Abstract Machines} 

@goals[

@item{why these three machines: CC machine, CK machine, CEK machine}
@item{theorems connecting the machines, theorems for debugging}

@item{equivalence theorems}
]

@; -----------------------------------------------------------------------------
@section{CC Machine}

@bold{Observation} β and β_v redexes often take place repeatedly in the
same evaluation context. On occasion they just add more layers (inside the
hole) to the evaluation context. Let's separate the in-focus expression
from the evaluation context. Historically the two have been called
@italic{control string} (C) and @italic{control context} (C). 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Lambda/v Lambda
  (e ::= .... n +)
  (n ::= integer)
  (v ::= n + (lambda (x ...) e)))

(define vv? (redex-match? Lambda/v e))

(define e0
  (term ((lambda (x) x) 0)))

(define e1
  (term ((lambda (x y) x) 1 2)))

(module+ test
  (test-equal (vv? e1) #true)
  (test-equal (vv? e0) #true))

;; -----------------------------------------------------------------------------
;; the CC machine: keep contexts and expression-in-focus apart

(define-extended-language CC Lambda/v
  (E ::=
     hole
     ;; @bold{Note} right to left evaluation of application 
     (e ... E v ...)))

(module+ test
  (test-->> -->cc (term [,e0 hole]) (term [0 hole]))
  (test-->> -->cc (term [,e1 hole]) (term [1 hole])))

(define -->cc
  (reduction-relation
   CC
   #:domain (e E)
   (--> [(lambda (x ..._n) e)
         (in-hole E (hole v ..._n))]
        [(subst ([v x] ...) e) E]
        CC-β_v)
   (--> [+
         (in-hole E (hole n_1 n_2))]
        [,(+ (term n_1) (term n_2)) E]
        CC-+)
   (--> [(e_1 ...) E]
        [e_last (in-hole E (e_1others ... hole))]
        (where (e_1others ... e_last) (e_1 ...))
        CC-push)
   (--> [v      (in-hole E (e ... hole v_1 ...))]
        [e_last (in-hole E (e_prefix ... hole v v_1 ...))]
        (where (e_prefix ... e_last) (e ...))
        CC-switch)))

(module+ test
  (test-equal (term (eval-cc ,e0)) 0)
  (test-equal (term (eval-cc ,e1)) 1))

(define-metafunction Lambda/v
  eval-cc : e -> v or closure or stuck
  [(eval-cc e) (run-cc [e hole])])

(define-metafunction CC
  run-cc : (e E) -> v or closure or stuck
  [(run-cc (n hole)) n]
  [(run-cc (v hole)) closure]
  [(run-cc any_1)
   (run-cc (e_again E_again))
   (where ((e_again E_again)) ,(apply-reduction-relation -->cc (term any_1)))]
  [(run-cc any) stuck])
))
@;%

@; -----------------------------------------------------------------------------
@section{The CK Machine}

@bold{Observation} The evaluation context of the CC machine behaves exactly
like a control stack. Let's represent it as such. 

@bold{General Idea} The general idea is to show how valuable it is to
reconsider data representations in PL, and how easy it is to do so in
Redex. 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language CK Lambda/v
  ;; @bold{Note} encode context as stack (left is top)
  (k ::= ((app [v ...] [e ...]) ...)))

(module+ test
  (test-->> -->ck (term [,e0 ()]) (term [0 ()]))
  (test-->> -->ck (term [,e1 ()]) (term [1 ()])))

(define -->ck
  (reduction-relation
   CK
   #:domain (e k)
   (--> [(lambda (x ..._n) e)
         ((app [v ..._n] []) (app any_v any_e) ...)]
        [(subst ([v x] ...) e)
         ((app any_v any_e) ...)]
        CK-β_v)
   (--> [+ ((app [n_1 n_2] []) (app any_v any_e) ...)]
        [,(+ (term n_1) (term n_2)) ((app any_v any_e) ...)]
        CK-+)
   (--> [(e_1 ...) (any_k ...)]
        [e_last ((app () (e_1others ...)) any_k ...)]
        (where (e_1others ... e_last) (e_1 ...))
        CK-push)
   (--> [v ((app (v_1 ...) (e ...)) any_k ...)]
        [e_last ((app (v v_1 ...) (e_prefix ...)) any_k ...)]
        (where (e_prefix ... e_last) (e ...))
        CK-switch)))

(module+ test
  (test-equal (term (eval-ck ,e0)) 0)
  (test-equal (term (eval-ck ,e1)) 1))

(define-metafunction Lambda/v
  eval-ck : e -> v or closure or stuck
  [(eval-ck e) (run-ck [e ()])])

(define-metafunction CK
  run-ck : (e k) -> v or closure or stuck
  [(run-ck (n ())) n]
  [(run-ck (v ())) closure]
  [(run-ck any_1)
   (run-ck (e_again k_again))
   (where ((e_again k_again)) ,(apply-reduction-relation -->ck (term any_1)))]
  [(run-ck any) stuck])
))
@;%

@; -----------------------------------------------------------------------------
@section{The CC-CK Theorem}

The two machines define the same evaluation function. Let's formulate this
as a theorem and @racket[redex-check] it. 

@bold{Note} When I prepared these notes, I found two mistakes in my
machines. 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  ;; theorem:eval-ck=eval-cc
  (test-equal (term (theorem:eval-ck=eval-cc ,e0)) #true)
  (test-equal (term (theorem:eval-ck=eval-cc ,e1)) #true)
  
  ;; NEXT: CEK vs CK 
  (redex-check Lambda e (term (theorem:eval-ck=eval-cc e))
               #:attempts 24
               #:prepare (close-all-fv vv?)))

(define-metafunction Lambda/v
  theorem:eval-ck=eval-cc : e -> boolean
  [(theorem:eval-ck=eval-cc e)
   ,(equal? (term (eval-cc e)) (term (eval-ck e)))])
))
@;%

@; -----------------------------------------------------------------------------
@section{The CEK machine}

@bold{Observation} Substitution is an eager operation. It traverses the
term kind of like machine does anyway when it searches for a redex. Why not
combine the two by delaying substitution until needed? That's called an
@tech{environment} (E) in the contexts of machines (also see above). 

@bold{General Idea} Universal laziness is @emph{not} a good idea. But
the selective delay of operations---especially when operations can be
merged---is a good thing. 

@;%
@(begin
#reader scribble/comment-reader
(racketblock

(define-extended-language CEK Lambda/v
  (ρ ::= ((x c) ...))
  (c ::= (v ρ))
  (k ::= ((app [c ...] ρ [e ...]) ...)))

(module+ test
  (test-->> -->cek (term [,e0 () ()]) (term [0 () ()]))
  (test-->> -->cek (term [,e1 () ()]) (term [1 () ()])))

(define -->cek
  (reduction-relation
   CEK
   #:domain (e ρ k)
   (--> [x
         ((x_1 c_1) ... (x (v ρ)) (x_2 c_2) ...)
         ((app any_v any_r any_e) ...)]
        [v
         ρ
         ((app any_v any_r any_e) ...)]
        CEK-lookup)
   (--> [(lambda (x ..._n) e)
         (any_c ...)
         ((app [c ..._n] ρ []) (app any_v any_r any_e) ...)]
        [e
         ([x c] ... any_c ...)
         ((app any_v any_r any_e) ...)]
        CEK-β_v)
   (--> [+
         ρ
         ((app [n_1 n_2] []) (app any_v any_r any_e) ...)]
        [,(+ (term n_1) (term n_2))
         ()
         ((app any_v any_r any_e) ...)]
        CEK-+)
   (--> [(e_1 ...)
         ρ
         (any_k ...)]
        [e_last
         ρ
         ((app () ρ (e_1others ...)) any_k ...)]
        (where (e_1others ... e_last) (e_1 ...))
        CEK-push)
   (--> [v
         ρ
         ((app (c_1 ...) ρ_stack (e ...)) any_k ...)]
        [e_last
         ρ_stack
         ((app ((v ρ) c_1 ...) ρ_stack (e_prefix ...)) any_k ...)]
        (where (e_prefix ... e_last) (e ...))
        CEK-switch)))

(module+ test
  (test-equal (term (eval-cek ,e0)) 0)
  (test-equal (term (eval-cek ,e1)) 1))

(define-metafunction Lambda/v
  eval-cek : e -> v or closure or stuck
  [(eval-cek e) (run-cek [e () ()])])

(define-metafunction CEK
  run-cek : (e ρ k) -> v or closure or stuck
  [(run-cek (n ρ ())) n]
  [(run-cek (v ρ ())) closure]
  [(run-cek any_1)
   (run-cek (e_again ρ_again k_again))
   (where ((e_again ρ_again k_again))
          ,(apply-reduction-relation -->cek (term any_1)))]
  [(run-cek any) stuck])
))
@;%


@; -----------------------------------------------------------------------------
@section{The CEK-CK Theorem}

Again, the two machines define the @emph{same semantics}. Here is the
theorem. 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  ;; theorem:eval-ck=eval-cc
  (test-equal (term (theorem:eval-cek=eval-ck ,e0)) #true)
  (test-equal (term (theorem:eval-cek=eval-ck ,e1)) #true)
  
  ;; NEXT: CEK vs CK 
  (redex-check Lambda e (term (theorem:eval-cek=eval-ck e))
               #:attempts 24
               #:prepare (close-all-fv vv?)))

(define-metafunction Lambda/v
  theorem:eval-cek=eval-ck : e -> boolean
  [(theorem:eval-cek=eval-ck e)
   ,(equal? (term (eval-cek e)) (term (eval-ck e)))])
))
@;%
