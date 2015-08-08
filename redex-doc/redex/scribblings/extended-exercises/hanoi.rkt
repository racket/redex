#lang racket

;; solving towers of Hanoi by searching the solution space 

(require redex)

;; -----------------------------------------------------------------------------
;; the state space of configurations 
(define-language L
  [chunk *]
  [tile (chunk ...)]
  [stack (side-condition [tile_1 ...]
                         (term (stacked [tile_1 ...])))]
  [state (stack ...)])

;; -----------------------------------------------------------------------------
;; checking the stacks

(define-metafunction L
  stacked : [tile ...] -> any
  [(stacked []) #t]
  [(stacked [tile_0 tile_1 ...])
   (stacked [tile_1 ...])
   (judgment-holds (accepts [tile_1 ...] tile_0 ))])

(define-judgment-form L
  #:mode (accepts I I)
  #:contract (accepts stack tile)
  [-----------------
   (accepts [] tile)]
  [-----------------
   (accepts [(chunk_0 ... chunk_1 ..._1) tile ...]
            (chunk_1 ..._1))])

;; -----------------------------------------------------------------------------
;; the redution system

(module+ test
  (test-->>∃ -->hanoi
             (term ([(*) (* *) (* * *)] [] []))
             (term ([]                  [] [(*) (* *) (* * *)]))))

(define -->hanoi
  (reduction-relation
   L
   [--> (stack_0 ... [tile_0 tile_1 ...]
         stack_1 ... [tile_2 ...]
         stack_3 ...)
        (stack_0 ... [tile_1 ...]
         stack_1 ... [tile_0 tile_2 ...]
         stack_3 ...)
        (judgment-holds (accepts [tile_2 ...] tile_0))]
   [--> (stack_0 ... [tile_1 ...]
         stack_1 ... [tile_0 tile_2 ...]
         stack_3 ...)
        (stack_0 ... [tile_0 tile_1 ...]
         stack_1 ... [tile_2 ...]
         stack_3 ...)
        (judgment-holds (accepts [tile_1 ...] tile_0))]))

(module+ test
  (test-results))

;; rendering the search 
(module+ main
  (traces -->hanoi (term ([(*) (* *) (* * *)] [] []))))
