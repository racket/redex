#lang racket/base



;                                                                       
;                                                                       
;                                                                       
;                                                                       
;  ;;;  ;;;  ;;; ;;;;;   ;;;;;;   ;;    ;;  ;;;  ;;    ;;    ;;;;;      
;  ;;;  ;;;  ;;; ;;;;;   ;;;;;;;  ;;;   ;;  ;;;  ;;;   ;;   ;;;;;;; ;;; 
;   ;;  ;;;  ;; ;;;;;;;  ;;; ;;;  ;;;;  ;;  ;;;  ;;;;  ;;  ;;;  ;;; ;;; 
;   ;; ;; ;; ;; ;;; ;;;  ;;;;;;;  ;;;;  ;;  ;;;  ;;;;  ;;  ;;;      ;;; 
;   ;; ;; ;; ;; ;;; ;;;  ;;;;;;   ;; ;; ;;  ;;;  ;; ;; ;;  ;;; ;;;;     
;   ;;;;; ;;;;; ;;; ;;;  ;;; ;;;  ;;  ;;;;  ;;;  ;;  ;;;;  ;;; ;;;;     
;    ;;;; ;;;;; ;;;;;;;  ;;; ;;;  ;;  ;;;;  ;;;  ;;  ;;;;  ;;;  ;;; ;;; 
;    ;;;   ;;; ;;;;;;;;; ;;; ;;;; ;;   ;;;  ;;;  ;;   ;;;   ;;;;;;; ;;; 
;    ;;;   ;;; ;;;   ;;; ;;;  ;;; ;;    ;;  ;;;  ;;    ;;    ;;;;   ;;; 
;                                                                       
;                                                                       
;                                                                       
;                                                                       
;                                                                                                      
;                                                                                                      
;                                                                                                      
;                                                                                                      
;   ;;;;;                                 ;                   ;;;             ;;;                   ;  
;   ;;;;;;                              ;;;                                   ;;;                 ;;;  
;   ;;; ;;;   ;;;       ;;; ;;    ;;;  ;;;;;     ;;; ;; ;;;;  ;;; ;;; ;;   ;; ;;;   ;;;;  ;;; ;; ;;;;; 
;   ;;; ;;;  ;;;;;      ;;;;;;;  ;;;;; ;;;;;     ;;;;; ;; ;;; ;;; ;;;;;;; ;;;;;;;  ;; ;;; ;;;;;;;;;;;; 
;   ;;; ;;; ;;; ;;;     ;;; ;;; ;;; ;;; ;;;      ;;;  ;;; ;;; ;;; ;;; ;;; ;;; ;;; ;;; ;;; ;;; ;;; ;;;  
;   ;;; ;;; ;;; ;;;     ;;; ;;; ;;; ;;; ;;;      ;;;  ;;;;;;; ;;; ;;; ;;; ;;; ;;; ;;;;;;; ;;; ;;; ;;;  
;   ;;; ;;; ;;; ;;;     ;;; ;;; ;;; ;;; ;;;      ;;;  ;;;     ;;; ;;; ;;; ;;; ;;; ;;;     ;;; ;;; ;;;  
;   ;;;;;;   ;;;;;      ;;; ;;;  ;;;;;  ;;;;     ;;;   ;;;;;; ;;; ;;; ;;; ;;;;;;;  ;;;;;; ;;; ;;; ;;;; 
;   ;;;;;     ;;;       ;;; ;;;   ;;;    ;;;     ;;;    ;;;;  ;;; ;;; ;;;  ;; ;;;   ;;;;  ;;; ;;;  ;;; 
;                                                                                                      
;                                                                                                      
;                                                                                                      
;                                                                                                      
;                                                       
;                                                       
;                                                       
;                                                       
;    ;  ;;;     ;;;             ;;;;;;; ;;;         ;;; 
;  ;;;  ;;;                    ;;;      ;;;         ;;; 
;  ;;;; ;;; ;;  ;;;  ;;;;     ;;;;; ;;; ;;;   ;;;;  ;;; 
;  ;;;; ;;;;;;; ;;; ;;; ;;    ;;;;; ;;; ;;;  ;; ;;; ;;; 
;  ;;;  ;;; ;;; ;;; ;;;        ;;;  ;;; ;;; ;;; ;;; ;;; 
;  ;;;  ;;; ;;; ;;;  ;;;;      ;;;  ;;; ;;; ;;;;;;;     
;  ;;;  ;;; ;;; ;;;    ;;;     ;;;  ;;; ;;; ;;;     ;;; 
;  ;;;; ;;; ;;; ;;; ;; ;;;     ;;;  ;;; ;;;  ;;;;;; ;;; 
;   ;;; ;;; ;;; ;;;  ;;;;      ;;;  ;;; ;;;   ;;;;  ;;; 
;                                                       
;                                                       
;                                                       
;                                                       


#|

WARNING: Do not reindent this file!

There are some examples whose indentation does not match
the standard indentation that DrRacket provides, in order
to illustrate various points. If you reindent the file, this
will break those examples.

|#

(require "../iswim/iswim.rkt"
         "../types/types.rkt")
(require redex)
(require texpict/mrpict racket/class)

;; ENDDEFS

(require racket/gui/base)
(dc-for-text-size (make-object bitmap-dc% (make-object bitmap% 1 1)))

;; EXAMPLE 1 "5.2cm"
(to-lw X)
;; BESIDE 1 #f "5.4cm"
(render-lw iswim (to-lw X))
;; STOP 1

;; EXAMPLE 1b "5.2cm"
(to-lw x)
;; BESIDE 1b #f "5.4cm"
(render-lw iswim (to-lw x))
;; STOP 1b


;; EXAMPLE 2 "5.4cm"
(to-lw 2)
;; BESIDE 2 150 "5.5cm"
(render-lw iswim (to-lw 2))
;; STOP 2

;; EXAMPLE 3
(to-lw (f x))
;; BESIDE 3 40
(render-lw
 iswim
 (to-lw (f x)))
;; STOP 3

;; EXAMPLE 3b
(to-lw [f x])
;; BESIDE 3b 40
(render-lw
 iswim
 (to-lw [f x]))
;; STOP 3b


;; EXAMPLE 3c
(to-lw (f 
        x))
;; BESIDE 3c 100
(render-lw
 iswim
 (to-lw (f
         x)))
;; STOP 3c

;; INDENTATION ALERT: 'wax' should be under 'big'
;; EXAMPLE 3c2
(to-lw (sit stand
        wax wane))
;; BESIDE 3c2 60
(render-lw
 iswim
 (to-lw (sit stand
         wax wane)))
;; STOP 3c2


;; EXAMPLE 3c3
(render-lw
 iswim
 (make-lw
  (list
   (make-lw "(" 1 0 9 1 #f #f)
   (make-lw 'big-f 1 0 10 1 #f #f)
   (make-lw 'x 1 0 12 1 #f #f)
   (make-lw 'y 2 0 12 1 #f #f)
   (make-lw ")" 2 0 13 1 #f #f))
  1 1 9 5 #f #f))
;; STOP 3c3

;; INDENTATION ALERT: the 'f' should be out past the last close
;; paren in the first section and matched with the last close paren
;; on the second section
;; EXAMPLE 3d
(to-lw    (f 
        x))
;; BESIDE 3d
(render-lw
 iswim
 (to-lw    (f 
         x)))
;; STOP 3d


;; EXAMPLE 3e
(to-lw (f 
        x
        ))
;; BESIDE 3e 100
(render-lw
 iswim
 (to-lw (f 
         x
         )))
;; STOP 3e

;; EXAMPLE mf
(to-lw (δ (add1 2)))
;; BESIDE mf 40
(render-lw
 iswim
 (to-lw (δ (add1 2))))
;; STOP mf

;; EXAMPLE mf2
(to-lw (TC Γ (λ X num X)))
;; BESIDE mf2 40
(render-lw
 t-iswim
 (to-lw
  (TC Γ (λ X num X))))
;; STOP mf2


;; EXAMPLE uq1
(to-lw (f ,a))
;; BESIDE uq1 40
(render-lw
 iswim
 (to-lw (f ,a)))
;; STOP uq1

;; EXAMPLE uq2
(to-lw (f ,(g 2)))
;; BESIDE uq2 40
(render-lw
 iswim
 (to-lw (f ,(g 2))))
;; STOP uq2

;; EXAMPLE uq3
(to-lw ,(add1 (term b)))
;; BESIDE uq3 40
(render-lw
 iswim
 (to-lw
  ,(add1 (term b))))
;; STOP uq3

;; EXAMPLE subst
(to-lw (subst M X V))
;; BESIDE subst 35
(render-lw
 iswim
 (to-lw (subst M X V)))
;; STOP subst

;; EXAMPLE uq
(to-lw ,(add1 (term b)))
;; STOP uq

;; COMMENT BESIDE uq 40
;; (render-lw
;;  iswim
;; (to-lw (context ,(+ (term b_1) (term b_2)))))
