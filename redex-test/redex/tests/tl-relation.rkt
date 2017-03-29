#lang racket
(require "private/test-util.rkt"
         redex/reduction-semantics)

(module test racket/base)
(reset-count)

(define-language empty-language)

(let ()
  (define-relation empty-language
    [(<: any any) #t])
  
  (test (term (<: 1 1)) #t)
  (test (term (<: 1 2)) #f))

(let ()
  (define-relation empty-language
    [(<: number_1 number_2) ,(< (term number_1) (term number_2))]
    [(<: number_1 number_1) #t])
  
  (test (term (<: 1 2)) #t)
  (test (term (<: 1 1)) #t)
  (test (term (<: 2 1)) #f))

(let ()
  (define-relation empty-language
    [(<: number_1 ... number_2 number_3 ... number_2 number_4 ...) #t])
  
  (test (term (<: 1 2 3 4)) #f)
  (test (term (<: 1 1 2 3 4)) #t)
  (test (term (<: 1 2 1 3 4)) #t)
  (test (term (<: 1 2 3 1 4)) #t)
  (test (term (<: 1 2 3 4 1)) #t))

(let ()
  (define-relation empty-language
    [(<: number_1 number_1)])
  (test (term (<: 1 1)) #t)
  (test (term (<: 1 2)) #f))

(let ()
  (define-relation empty-language
    [(<: number_1 number_2 number_3)
     ,(= (term number_1) (term number_2))
     ,(= (term number_2) (term number_3))])
  (test (term (<: 1 2 3)) #f)
  (test (term (<: 1 1 2)) #f)
  (test (term (<: 1 2 2)) #f)
  (test (term (<: 1 1 1)) #t))

(let ()
  (define-relation empty-language
    d ⊆ any × any
    [(d (any) (any)) (d any any)]
    [(d () ())])
  
  (test (term (d ((())) ((())))) #t)
  (test (term (d ((())) ())) #f))

(let ()
  (define-relation empty-language
    d ⊂ any x any
    [(d (any) (any)) (d any any)]
    [(d () ())])
  
  (test (term (d ((())) ((())))) #t)
  (test (term (d ((())) ())) #f))

(let ()
  (define-relation empty-language
    d ⊂ (any)
    [(d (1))])
  
  (test (term (d (1))) #t)
  (test (term (d (2))) #f)
  (test (with-handlers ((exn:fail? (λ (x) 'passed)))
          (term (d 1))
          'failed)
        'passed))

(let ()
  (define-language types
    ((τ σ) int
           num
           (τ ... → τ)))
  
  (define-relation types
    subtype ⊆ τ × τ
    [(subtype int num)]
    [(subtype (τ_1 ..._1 → τ_2) (σ_1 ..._1 → σ_2))
     (subtype σ_1 τ_1) ...
     (subtype τ_2 σ_2)]
    [(subtype τ τ)])
  
  (test (term (subtype int int)) #t)
  (test (term (subtype int num)) #t)
  (test (term (subtype (int int int → int) (int int → int))) #f)
  (test (term (subtype (int int → int) (int num → int))) #f)
  (test (term (subtype (int num → int) (int int → int))) #t)
  (test (term (subtype (int int → int) (int int → num))) #t))

(let ()
  (define-relation empty-language
    [(R () ())]
    [(R (any_a) (any_b)) 
     (R any_c any_d) 
     (where any_c any_a)
     (where any_d any_b)])
  
  (test (term (R () ())) #t)
  (test (term (R (()) (()))) #t)
  (test (term (R (()) ())) #f))

(let ()
  (define-relation empty-language
    [(R () ())]
    [(R (any_a) (any_b)) 
     (R any_c any_d) 
     (where/hidden any_c any_a)
     (where/hidden any_d any_b)])
  
  (test (term (R () ())) #t)
  (test (term (R (()) (()))) #t)
  (test (term (R (()) ())) #f))

(let ()
  (define-relation empty-language
    [(R any_a any_b)
     (side-condition (equal? (term any_a)
                             (term any_b)))])
  
  (test (term (R (xx) (xx))) #t)
  (test (term (R (()) ())) #f))

(let ()
  (define-relation empty-language
    [(R any_a any_b)
     (side-condition/hidden
      (equal? (term any_a)
              (term any_b)))])
  
  (test (term (R (xx) (xx))) #t)
  (test (term (R (()) ())) #f))

(let ()
  
  (define-relation empty-language
    [(a number_1)
     (b number_1)]
    [(a 2)])
  
  (define-relation empty-language
    [(b 1)]
    [(b 2)])
  
  (test (term (a 1)) #t)
  (test (term (a 2)) #t)
  (test (term (a 3)) #f)
  (test (term (b 1)) #t)
  (test (term (b 2)) #t)
  (test (term (b 3)) #f))

(let ()
  (define-relation empty-language
    [(a any)])
  (define-relation empty-language
    [(b any)])
  (define-relation empty-language
    [(c any) (a (b any))])
  
  (define-metafunction empty-language
    [(f any)
     (c any)])
  
  (define-judgment-form empty-language
    #:mode (J I O)
    [(J any_1 (a any_1))])
  
  (test (term (a 1)) #t)
  (test (term (b 2)) #t)
  (test (term (c 3)) #t)
  (test (term (c (b (a x)))) #t)
  (test (term (f q)) #t)
  (test (judgment-holds (J Z #t)) #t)
  (test (judgment-holds (J Z Z)) #f)
  )

(let ()
  (define-language L)

  (define-relation L
    R ⊂ any
    [(R any)])

  (define tried-body? #f)
  (parameterize ([current-output-port (open-output-nowhere)])
    (redex-check
     L
     #:satisfying (R any)
     (set! tried-body? #t)
     #:attempts 1))
  (test tried-body? #t))

(print-tests-passed 'tl-relation.rkt)
