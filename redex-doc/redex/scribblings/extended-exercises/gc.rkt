#lang racket

;; a model of garbage collection for binary trees in a store

(require redex)

;; -----------------------------------------------------------------------------
;; syntax 
(define-language L
  [V number
     (cons σ σ)]
  [σ variable-not-otherwise-mentioned]
  [Σ ([σ V] ...)]
  [σs (σ ...)])

;; -----------------------------------------------------------------------------
;; set constraints 
(define-judgment-form L
  #:mode (∈ I I)
  #:contract (∈ any (any ...))
  [-----------------
   (∈ any_1 (_ ... any_1 _ ...))])

(define-judgment-form L
  #:mode (∉ I I)
  #:contract (∉ any (any ...))
  [-----------------
   (∉ any_!_ (any_!_ ...))])

;; -----------------------------------------------------------------------------
;; the reduction system 

(module+ test
  (test-->> -->gc
            (term [([a 1] [b (cons a b)] [c (cons c c)]) (a) ()])
            (term [([a 1] [b (cons a b)] [c (cons c c)]) () (a)]))
  (test-->> -->gc
            (term [([a 1] [b (cons a b)] [c (cons c c)]) (b) ()])
            (term [([a 1] [b (cons a b)] [c (cons c c)]) () (b a)]))
  (test-->> -->gc
            (term [([a 1] [b (cons a b)] [c (cons c c)]) (c) ()])
            (term [([a 1] [b (cons a b)] [c (cons c c)]) () (c)])))

(define -->gc
  (reduction-relation
   L
   #:domain [Σ σs σs]
   (--> [Σ (σ_g σ_g2 ...) σs_b]
        [Σ (σ_g2 ...) σs_b]
        (judgment-holds (∈ σ_g σs_b))
        "already black")
   
   (--> [Σ (σ_g σ_g2 ...) (name σs_b (σ_b ...))]
        [Σ (σ_g2 ...) (σ_b ... σ_g)]
        (where (_ ... [σ_g number_g] _ ...) Σ)
        (judgment-holds (∉ σ_g σs_b))
        "number cell")
   
   (--> [Σ (σ_g σ_g2 ...) (name σs_b (σ_b ...))]
        [Σ (σ_ga σ_gd σ_g2 ...) (σ_b ... σ_g)]
        (where (_ ... [σ_g (cons σ_ga σ_gd)] _ ...) Σ)
        (judgment-holds (∉ σ_g σs_b))
        "pair cell")))


(module+ test
  (test-results))