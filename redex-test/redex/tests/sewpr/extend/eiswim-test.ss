#lang scheme

(require redex "../iswim/iswim.ss" "eiswim.ss")

;; ENDDEFS

(require redex)
;; START ex0
(traces e-iswim-red-first-try
        (term
         (/ ((λ x (/ 1 x)) 7)
            2)))
;; STOP ex0

;; EXAMPLE ex1
(redex-match e-iswim 
             V
             (term 
              (λ x
                (/ 1 x))))
;; BESIDE ex1
(redex-match iswim
             V
             (term
              (λ x
                (/ 1 x))))
;; STOP ex1


;; EXAMPLE ex2
(redex-match
 e-iswim
 M (term (λ err err)))
;; BESIDE ex2
(redex-match 
 iswim
 M (term (λ err err)))
;; STOP ex2




#;
(begin
  (require redex)
  (traces e-iswim-red-first-try
          (term
           (/ ((λ x (+ (/ 1 x) (err 2)))
               7)
              2))))

#;
(begin
  (require redex)
  )

