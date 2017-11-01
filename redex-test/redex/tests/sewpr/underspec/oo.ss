#lang scheme
(require redex "../iswim/iswim.ss")
(provide main-example red! C-red sch sch1-red sch2-red sch3-red)

;; START bang
(define-extended-language iswim!
  iswim
  (P (V M))
  (M .... (get) (set M))
  (E .... (set E)))
;; STOP bang

;; START bang-red
(define red!
  (reduction-relation
   iswim!
   (--> (V_s (in-hole E ((λ X M) V)))
        (V_s (in-hole E (subst M X V)))
        βv)
   (--> (V_s (in-hole E (o b ...)))
        (V_s (in-hole E (δ (o b ...))))
        δ)
   (--> (V_s (in-hole E (get)))
        (V_s (in-hole E V_s))
        get)
   (--> (V_s (in-hole E (set V_n)))
        (V_n (in-hole E V_n))
        set)))
;; STOP bang-red


;; START all
(define-extended-language C-lang
  iswim!
  (E hole (V E) (E M) (o M ... E M ...) (set E)))
;; STOP all

;; START all-red
(define C-red
  (extend-reduction-relation red! C-lang))
;; STOP all-red

;; START sch
(define-extended-language sch
  iswim!
  (E hole (V E) (E M) (o V ... E V ...) (set E)))
;; STOP sch

;; START sch1-red
(define sch1-red
  (extend-reduction-relation
   red!
   sch
   (--> (in-hole E (o M_1 ... M_2 M_3 ...))
        (in-hole E ((λ X (o M_1 ... X M_3 ...))
                    M_2))
        lift
        (fresh X))))
;; STOP sch1-red

;; START schnv
(define-extended-language sch/nv
  sch
  (NV (side-condition M_1 (not (V? (term M_1))))))

(define V? (redex-match sch V))
;; STOP schnv

;; START sch2-red
(define sch2-red
  (extend-reduction-relation
   red!
   sch/nv
   (--> (in-hole E (o M_1 ... NV M_3 ...))
        (in-hole E ((λ X (o M_1 ... X M_3 ...))
                    NV))
        lift
        (fresh X))))
;; STOP sch2-red

;; START sch3-red
(define sch3-red
  (extend-reduction-relation
   red!
   sch/nv
   (--> (in-hole E (o M_1 ... NV_1 M_2 ... NV_2 M_3 ...))
        (in-hole E ((λ X (o M_1 ... X M_2 ... NV_2 M_3 ...))
                    NV_1))
        left-lift
        (fresh X))
   
   (--> (in-hole E (o M_1 ... NV_1 M_2 ... NV_2 M_3 ...))
        (in-hole E ((λ X (o M_1 ... NV_1 M_2 ... X M_3 ...))
                    NV_2))
        right-lift
        (fresh X))))
;; STOP sch3-red
   
;; START main-example
(define main-example
  (term (0 (+ (set (+ (get) 1))
              (set (- (get) 1))))))
;; STOP main-example
