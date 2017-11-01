#lang scheme/gui
(require "../iswim/iswim.rkt")
(require redex)

;; ENDDEFS

;; EXAMPLE lang
(render-language iswim)
;; STOP lang

;; EXAMPLE lang2
(render-language 
 iswim
 #:nts
 (remove* '(X Y Z) (language-nts iswim)))
;; STOP lang2

;; EXAMPLE lang2-b
(render-language iswim #:nts '(U V W E))
;; STOP lang2-b

;; EXAMPLE lang2-a
(render-language
 iswim
 #:nts
 (remove* '(X Y Z V U W E) (language-nts iswim)))
;; STOP lang2-a

;; EXAMPLE mf
(render-metafunction δ)
;; STOP mf

;; EXAMPLE red
(render-reduction-relation iswim-red)
;; STOP red

;; EXAMPLE red2
(render-reduction-relation iswim-red
                           #:style 'compact-vertical)
;; STOP red2

;; EXAMPLE red3
(render-reduction-relation iswim-red
                           #:style 'horizontal)
;; STOP red3

;; EXAMPLE red-spacing
(render-reduction-relation
 (reduction-relation
  iswim
  (--> (* b_1 (+ b_2 b_3))
       (+ (* b_1 b_2) 
          (* b_1 b_3)))))
;; BESIDE red-spacing
(render-reduction-relation
 (reduction-relation
  iswim
  (--> (* b_1 
          (+ b_2
             b_3))
       (+ (* b_1
             b_2) 
          (* b_1
             b_3)))))
;; STOP red-spacing
