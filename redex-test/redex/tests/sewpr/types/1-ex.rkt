#lang scheme
(require redex "1.rkt")

;; ENDDEFS 

;; EXAMPLE mod-test
(test-->> mod3 (term (+ (+ 0 (+ 1 2)) 2)) (term 2))
;; CONTINUE mod-test
(test-->> mod3 (term (+ (+ 1 1) (+ 1 1))) (term 1))
;; CONTINUE mod-test
(test-->> mod3 (term (+ 0 (+ 0 (+ 0 1)))) (term 1))
;; CONTINUE mod-test
(test-->> mod3 (term (+ (+ (+ (+ 0 1) 0) 1) 0)) (term 2))
;; CONTINUE mod-test
(test-->> mod3 (term (+ (+ 1 1) (+ 2 1))) (term 2))
;; CONTINUE mod-test
(test-results)
;; STOP mod-test


(module+ main
;; START mod-traces
(traces mod3 (term (+ (+ 1 1) (+ 2 1))) 
        #:pred (redex-match mod-lang A))
;; STOP mod-traces
)
