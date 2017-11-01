#lang scheme 

(require redex)
(provide mod3 mod-lang)

#|
+ 0 1 2 
0 0 1 2 
1 1 2 0
2 2 0 1 
|#

;; START mod-lang
(define-language mod-lang
  (A 0 1 2 (+ A A))
  (C hole (+ C A) (+ A C)))
;; STOP mod-lang

;; START mod-red
(define mod3
  (reduction-relation mod-lang 
    (--> (in-hole C (+ 0 A)) (in-hole C A) 0left)
    (--> (in-hole C (+ A 0)) (in-hole C A) 0right)
    (--> (in-hole C (+ 1 1)) (in-hole C 2) 1-1)
    (--> (in-hole C (+ 1 2)) (in-hole C 0) 1-2)
    (--> (in-hole C (+ 2 1)) (in-hole C 3) 2-1)
    (--> (in-hole C (+ 2 2)) (in-hole C 1) 2-2)))
;; STOP mod-red

