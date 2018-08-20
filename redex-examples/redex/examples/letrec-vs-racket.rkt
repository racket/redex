#lang racket
(require "letrec.rkt" redex/reduction-semantics)

#|

Tests to see if the model in letrec.rkt
produces the same results as racket itself

|#

(require racket/runtime-path)
(define ns (make-base-empty-namespace))
(module all-the-stuff racket/base
  (provide + - * set! = #%top
           let letrec if begin
           #%app λ void #%datum))
(define-runtime-path letrec-vs-racket.rkt "letrec-vs-racket.rkt")
(require (only-in (submod "." all-the-stuff))) ;; bind nothing
(namespace-attach-module (current-namespace)
                         `(submod (file ,(path->string letrec-vs-racket.rkt)) all-the-stuff)
                         ns)
(parameterize ([current-namespace ns])
  (namespace-require `(submod (file ,(path->string letrec-vs-racket.rkt)) all-the-stuff)))

(define (same-as-racket? t)
  (define cleaned-up (clean-up t))
  (define redex-result (redex-eval cleaned-up))
  (define racket-result (racket-eval cleaned-up))
  (define ans (equal? redex-result racket-result))
  (unless ans
    (printf "cleaned up:\n")
    (pretty-write cleaned-up)
    (printf "from redex:\n")
    (pretty-write redex-result)
    (printf "from racket:\n")
    (pretty-write racket-result))
  ans)

(define v? (redex-match? lang v))
(define lam? (redex-match? lang (λ (x ...) e)))
(define (redex-eval prog)
  (define result (result-of prog))
  (cond
    [(or (lam? result) (member result '(* - + =))) 'proc]
    [(v? result) result]
    [else 'error]))

(define (racket-eval prog)
  (with-handlers ([exn:fail? (λ (x) 'error)])
    (define result (eval prog ns))
    (match result
      [(? procedure?) 'proc]
      [(? void?) '(void)]
      [_ result])))

;; clean-up : any -> any
;; removes forms that shouldn't be in the original program
;; removes (most of) the free variables
(define (clean-up s)
  (define primitives '(+ = * -))
  (let loop ([s s]
             [bound '()])
    (define (pick-a-var x prim-ok?)
      (cond
        [(member x bound) x]
        [(or (null? bound) (zero? (random 10))) x]
        [else
         (when prim-ok? (set! bound (append primitives bound)))
         (list-ref bound (random (length bound)))]))
    (match s
      [`(letrec ([,xs ,es] ...) ,e)
       (define new-vars (append xs bound))
       `(letrec (,@(for/list ([x (in-list xs)]
                              [e (in-list es)])
                     `[,x ,(loop e new-vars)]))
          ,(loop e new-vars))]
      [`(let ([,xs ,es] ...) ,e)
       (define new-vars (append xs bound))
       `(let (,@(for/list ([x (in-list xs)]
                           [e (in-list es)])
                  `[,x ,(loop e bound)]))
          ,(loop e new-vars))]
      [`(λ (,xs ...) ,e)
       (define new-vars (append xs bound))
       `(λ (,@xs) ,(loop e new-vars))]
      [`(set! ,x ,e)  `(set! ,(pick-a-var x #f) ,(loop e bound))]
      [`(if ,e1 ,e2 ,e3)  `(if ,(loop e1 bound) ,(loop e2 bound) ,(loop e3 bound))]
      [`(begin ,es ...) `(begin ,@(for/list ([e (in-list es)])
                                    (loop e bound)))]
      [`(void) `(void)]
      [`(,ef ,eas ...)  `(,(loop ef bound) ,@(for/list ([ea (in-list eas)])
                                               (loop ea bound)))]
      [(? symbol?) (pick-a-var s #t)]
      [(? boolean?) s]
      [(? number?) s])))
  
(module+ test
  (redex-check surface-lang e
               (same-as-racket? (term e))))
