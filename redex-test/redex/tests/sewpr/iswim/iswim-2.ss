#lang scheme

(require redex)

;                                     
;                                     
;     ;                    ;          
;                                     
;   ;;;     ;;;; ;;; ;;; ;;;   ;;; ;  
;     ;    ;   ;  ;   ;    ;    ; ; ; 
;     ;     ;;;   ; ; ;    ;    ; ; ; 
;     ;        ;  ; ; ;    ;    ; ; ; 
;     ;    ;   ;  ; ; ;    ;    ; ; ; 
;   ;;;;;  ;;;;    ; ;   ;;;;; ;;;;;;;
;                                     
;                                     
;                                     
;                                     

(define-language iswim
  (M X (λ X M) (M M) b (o2 M M) (o1 M))
  (o o1 o2)
  (o1 add1 sub1 iszero)
  (o2 + - * ↑)
  (b number)
  (V b X (λ X M))
  (E hole (V E) (E M) (o V ... E M ...))
  (X variable-not-otherwise-mentioned))

(define-metafunction iswim
  [(δ (iszero 0)) (λ x (λ y x))]
  [(δ (iszero b)) (λ x (λ y y))]
  [(δ (add1 b)) ,(add1 (term b))]
  [(δ (sub1 b)) ,(sub1 (term b))]
  [(δ (+ b_1 b_2)) ,(+ (term b_1) (term b_2))]
  [(δ (- b_1 b_2)) ,(- (term b_1) (term b_2))]
  [(δ (* b_1 b_2)) ,(* (term b_1) (term b_2))]
  [(δ (↑ b_1 b_2)) ,(expt (term b_1) (term b_2))])

;; START red
(define iswim-standard
  (reduction-relation
   iswim
   (v ((λ X M) V) (subst M X V) βv)
   (v (o b ...) (δ (o b ...)) δ)
   with 
   [(--> (in-hole E M) (in-hole E N)) (v M N)]))
;; STOP red

(define iswim-standard0
  (reduction-relation
   iswim
   (--> (in-hole E ((λ X M) V)) (in-hole E (subst M X V)) βv)
   (--> (in-hole E (o b ...))   (in-hole E (δ (o b ...))) δ)))

(define-metafunction iswim
  
  ;; 1. X_1 bound, so don't continue in λ body
  [(subst (λ X_1 any_2) X_1 any_1)
   (λ X_1 any_2)]
  
  ;; 2. do capture avoiding substitution
  ;;    by generating a fresh name
  [(subst (λ X_2 any_2) X_1 any_1)
   (λ X_new
     (subst (subst-var any_2 X_2 X_new) X_1 any_1))
   (where X_new ,(variable-not-in (term (X_1 any_1 any_2)) 
                                  (term X_2)))]
  ;; 3. replace X_1 with any_1
  [(subst X_1 X_1 any_1) any_1]
  
  ;; the last two cases just recur on 
  ;; the tree structure of the term
  [(subst (any_2 ...) X_1 any_1)
   ((subst any_2 X_1 any_1) ...)]
  [(subst any_2 X_1 any_1) any_2])

(define-metafunction iswim
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])

(define Yv
  (term (λ f
          (λ x
            (((λ g (f (λ x ((g g) x))))
              (λ g (f (λ x ((g g) x)))))
             x)))))

(define big-example
  (term ((,Yv
          (λ f
            (λ x
              ((((iszero x)
                 (λ d 1))
                (λ d (+ x (f (+ x -1)))))
               0))))
         10)))

;; ENDDEFS

(provide iswim-standard
         iswim-standard0
         subst)
