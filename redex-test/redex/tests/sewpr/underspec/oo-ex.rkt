#lang racket/base
(require redex/reduction-semantics "oo.rkt")


;; ENDDEFS

;; EXAMPLE sch1
(redex-match sch
             (o M_1 ... M_2 M_3 ...)
             (term (+ (* 1 2) (↑ 3 4))))
;; STOP sch1

;; EXAMPLE sch2
(redex-match sch
             (o M_1 ... M_2 M_3 ...)
             (term (+ (set (+ (get) 1))
                      (set (- (get) 1)))))
;; STOP sch2

#;
(begin
  (require redex)
  (initial-font-size 10)
  
  #;
  (parameterize ((initial-char-width 20) [reduction-steps-cutoff 100]) (traces all-red main-example))
  #;
  (parameterize ([reduction-steps-cutoff 10]) (traces sch1-red main-example))
  (parameterize ([reduction-steps-cutoff 20]) (traces sch2-red main-example))
  #;
  (parameterize ((initial-char-width 20) [reduction-steps-cutoff 100]) (traces sch3-red main-example)))
