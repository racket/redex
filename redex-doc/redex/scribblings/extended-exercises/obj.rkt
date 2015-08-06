#lang racket

;; a model of simple object programming (no updater, no prototype, no clone)

(require redex (only-in "common.rkt" in))

;; -----------------------------------------------------------------------------
;; syntax

(define-language Object
  (e ::= n y (object (m (x) e) ...) (send e m e))
  (y ::= x this)
  (n ::= natural)
  (m ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned))

;; -----------------------------------------------------------------------------
;; examples

(define help
  (term (object [help (x) x])))

(define p-good
  (term
   (send
    (object [get(x) this]
            [set(x) x])
    set
    ,help)))

(define p-8
  (term
   (send (object [get(x) this] [set(x) (send x + 3)]) set 5)))

(module+ test
  (test-equal (redex-match? Object e help) #true)
  (test-equal (redex-match? Object e p-good) #true))

;; -----------------------------------------------------------------------------
;; scope

;; (=α e_1 e_2) determines whether e_1 and e_2 are α equivalent
(module+ test
  (test-equal (term (=α (object (help (x) x)) (object (help (y) y)) )) #true)
  (test-equal (term (=α (object (help (x) x)) (object (main (y) y)) )) #false))

(define-metafunction Object
  =α : any any -> boolean
  [(=α any_1 any_2) ,(equal? (term (sd any_1)) (term (sd any_2)))])

;; a Racket definition for use in Racket positions 
(define (=α/racket x y) (term (=α ,x ,y)))

;; (sd e) computes the static distance version of e
(define-extended-language SD Object
  (e ::= .... (K n))
  (n ::= natural))

(define SD? (redex-match? SD e))

(module+ test
  (define sd1 (term (K 1)))
  (define sd2 (term 1))
  
  (test-equal (SD? sd1) #true))

(define-metafunction SD
  sd : any -> any
  [(sd any_1) (sd/a any_1 ())])

(module+ test
  (define help-sd
    (term (object [help () (K 0)])))
  (define p-good-sd
    (term
     (send
      (object [get(x) this]
              [set(x) (K 0)])
      set
      ,help-sd)))
  (test-equal (term (sd/a x ())) (term x))
  (test-equal (term (sd/a x (y z x))) (term (K 2)))
  (test-equal (term (sd ,help)) help-sd))

(define-metafunction SD
  sd/a : any (x ...) -> any
  ;; bound variable 
  [(sd/a x (x_1 ... x x_2 ...))
   (K n_rib)
   (where n_rib ,(length (term (x_1 ...))))
   (where #false (in x (x_1 ...)))]
  ;; free variable 
  [(sd/a x (x_1 ...)) x]
  [(sd/a (object (m (x) any_1) ...) (any_rest ...))
   (object (m () (sd/a any_1 (x any_rest ...))) ...)]
  [(sd/a (send any_fun m any_arg) (any_rib ...))
   (send (sd/a any_fun (any_rib ...)) m (sd/a any_arg (any_rib ...)))]
  [(sd/a any (x_1 ...)) any])

;; -----------------------------------------------------------------------------
;; substitution

;; (subst ([e x] ...) e_*) substitutes e ... for x ... in e_* (hygienically)
(module+ test
  (test-equal (term (subst ([1 x][2 y]) x)) 1)
  (test-equal (term (subst ([1 x][2 y]) y)) 2)
  (test-equal (term (subst ([1 x][2 y]) z)) (term z))
  (test-equal
   (term (subst ([1 x][2 y]) (object (m (z) x))))
   (term (object (m (z) 1)))
   #:equiv =α/racket)
  (test-equal
   (term (subst ([1 x][2 y]) (object (m (z) (object (n (x) x))))))
   (term (object (m (z) (object (n (x) x)))))
   #:equiv =α/racket)
  (test-equal
   (term (subst ([1 x][2 y]) (object (m (z) (object (n (y) x))))))
   (term (object (m (z) (object (n (y) 1)))))
   #:equiv =α/racket)
  (test-equal
   (term (subst ([(object (x) y) x][2 y]) (object (m (z) (object (n (y) x))))))
   (term (object (m (z) (object (n (y1) (object (x) y))))))
   #:equiv =α/racket)
  
  (test-equal
   (term
    (subst ([(object (help (x) x)) x]
            [(object (get (x) this) (set (x) x)) this])
           x))
   help
   #:equiv =α/racket))

(define-metafunction Object
  subst : ((any y) ...) any -> any
  [(subst [(any_1 y_1) ... (any_x x) (any_2 y_2) ...] x) any_x]
  [(subst [(any_1 y_1) ... ] x) x]
  [(subst [(any_1 y_1) ... ] (object (m (x) any_m) ...))
   (object
    (m (y_new) (subst ((any_1 y_1) ...) (subst-raw ((y_new x) ...) any_m))) ...)
   (where (y_new ...) (fresh-in any_m ... any_1 ... (x ...)))]
  [(subst [(any_1 y_1) ... ] (any ...)) ((subst [(any_1 y_1) ... ] any) ...)]
  [(subst [(any_1 y_1) ... ] any_*) any_*])

(define-metafunction Object
  subst-raw : ((y y) ...) any -> any
  [(subst-raw ((y_n1 y_o1) ... (y_new x) (y_n2 y_o2) ...) x) y_new]
  [(subst-raw ((y_n1 y_o1) ... ) x) x]
  [(subst-raw ((y_n1 y_o1) ... ) (object (m (x) any_m) ...))
   (object (m (x) (subst-raw ((y_n1 y_o1) ... ) any_m)) ...)]
  [(subst-raw [(any_1 y_1) ... ] (any ...))
   ((subst-raw [(any_1 y_1) ... ] any) ...)]
  [(subst-raw [(any_1 y_1) ... ] any_*) any_*])

;; (fresh-in any ... (x ...)) generates a sequence of variables
;; like x ... not in any ...
(define-metafunction Object
  fresh-in : any ... (x ...) -> (x ...)
  [(fresh-in any ... (x ...))
   ,(variables-not-in (term (any ...)) (term (x ...)))])

;; -----------------------------------------------------------------------------
;; the object calculus (standard reduction)

(define-extended-language Object-calculus Object
  (v ::= n (object (m (x) e) ...))
  (E ::= hole (send E m e) (send v m E)))

(module+ test
  #;
  (traces -->obj p-good)
  (test-->> -->obj #:equiv =α/racket p-good help)
  (test-->> -->obj #:equiv =α/racket p-8 8))

(define -->obj 
  (reduction-relation
   Object-calculus
   (--> (in-hole E (send (name THIS
                               (object (m_left (x_left) e_left) ...
                                       (m (x) e)
                                       (m_right (x_right) e_right) ...))
                         m
                         v))
        (in-hole E (subst ([v x][THIS this]) e))
        send)
   (--> (in-hole E (send n_1 + n_2))
        (in-hole E ,(+ (term n_1) (term n_2)))
        add)))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))

