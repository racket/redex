#lang scheme

(require redex "../iswim/iswim.ss")
(provide c-iswim-red ☺-iswim-red ☠-iswim-red ☠-iswim)

;; START lang
(define-extended-language c-iswim
  iswim
  (M ....
     (call/cc M)
     (abort M))
  (E ....
     (call/cc E)))
;; STOP lang

;; START red
(define c-iswim-red
  (extend-reduction-relation
   iswim-red
   c-iswim
   (--> (in-hole E (call/cc V))
        (in-hole E (V (λ X (abort (in-hole E X)))))
        (fresh X)        
        call/cc)
   (--> (in-hole E (abort M))
        M
        throw)))
;; STOP red
#;        (where X ,(variable-not-in (term (in-hole E V)) (term X)))
;; START lang-wrong
(define-extended-language ☠-iswim
  iswim
  (M ....
     (call/cc M)
     (cont E))
  (V ....
     (cont E))
  (E ....
     (call/cc E)))
;; STOP lang-wrong

;; START red-wrong
(define ☠-iswim-red
  (extend-reduction-relation
   iswim-red
   ☠-iswim
   (--> (in-hole E (call/cc V))
        (in-hole E (V (cont E)))
        call/cc)
   (--> (in-hole E_1 ((cont E_2) V))
        (in-hole E_2 V)
        throw)))
;; STOP red-wrong

;; START lang-ok
(define-extended-language ☺-iswim
  iswim
  (M ....
     (call/cc M)
     (cont (hide-hole E)))
  (V ....
     (cont (hide-hole E)))
  (E ....
     (call/cc E)))
;; STOP lang-ok

;; START red-ok
(define ☺-iswim-red
  (extend-reduction-relation
   iswim-red
   ☺-iswim
   (--> (in-hole E (call/cc V))
        (in-hole E (V (cont E)))
        call/cc)
   (--> (in-hole E_1 ((cont E_2) V))
        (in-hole E_2 V)
        throw)))
;; STOP red-ok


;; ENDDEFS

; (+ 42 (call/cc (λ k (k 1))))
; E = (+ 42 [])
; (+ 42 ((\ k (k 1)) (+ 42 [])))
; (apply-reduction-relation* ☠-iswim-red (term (+ 42 ((λ k (k 1)) (cont (+ 42 hole))))))
