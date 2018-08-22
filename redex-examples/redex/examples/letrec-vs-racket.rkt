#lang racket
(require "letrec.rkt" redex/reduction-semantics
         racket/linklet racket/runtime-path)

#|

Tests to see if the model in letrec.rkt
produces the same results as racket itself

|#

(define (namespace-mapped-symbols.2 ns)
  (for/list ([x (in-list (namespace-mapped-symbols ns))]
             #:when (with-handlers ([exn:fail? (λ (x) #f)])
                      (eval x ns)))
    x))

(define ns (make-base-empty-namespace))
(module all-the-stuff racket/base
  (provide + - * set! = #%top
           let letrec if begin
           #%app λ void #%datum
           writeln))
(module all-the-stuff-lang racket/base
  (require (submod ".." all-the-stuff)
           (for-syntax racket/base))
  (provide (except-out (all-from-out (submod ".." all-the-stuff))
                       #%top
                       set!)
           (rename-out [module-begin #%module-begin]
                       [top #%top]
                       [-set! set!]))
  (define-syntax (-set! stx)
    (syntax-case stx ()
      [(_ id e) #'(#%expression (real-set! id e))]))
  (define-syntax (real-set! stx)
    (syntax-case stx ()
      [(_ id e)
       (if (identifier-binding #'id)
           #'(set! id e)
           #'(error 'set! "free variable ~s" 'id))]))
  (define-syntax (module-begin stx)
    (syntax-case stx ()
      [(_ e) #'(#%plain-module-begin
                (define the-answer e)
                (provide the-answer))]))
  (define-syntax (top stx)
    (syntax-case stx ()
      [(_ . x) #'(error 'free-variable "~s" 'x)])))

(define-runtime-path letrec-vs-racket.rkt "letrec-vs-racket.rkt")
(require (only-in (submod "." all-the-stuff))  ;; bind nothing
         (only-in (submod "." all-the-stuff-lang)))
(namespace-attach-module (current-namespace)
                         `(submod (file ,(path->string letrec-vs-racket.rkt)) all-the-stuff)
                         ns)
(parameterize ([current-namespace ns])
  (namespace-require `(submod (file ,(path->string letrec-vs-racket.rkt)) all-the-stuff)))
(define originally-mapped-symbols (namespace-mapped-symbols.2 ns))

(define (same-as-racket? t)
  (define cleaned-up (clean-up t))
  (define redex-result (redex-eval cleaned-up))
  (cond
    [(equal? redex-result 'infinite-loop) #t]
    [else
     (define racket-result (racket-eval cleaned-up))
     (define racket-module-result (racket-module-eval cleaned-up))
     (define newly-mapped-symbols (namespace-mapped-symbols.2 ns))
     (cond
       [(not (equal? newly-mapped-symbols originally-mapped-symbols))
        (printf "set of symbols mapped in the namespace changed to:\n")
        (pretty-write newly-mapped-symbols)
        (printf "cleaned up:\n")
        (pretty-write cleaned-up)
        #f]
       [(not (equal? redex-result racket-result))
        (printf "cleaned up:\n")
        (pretty-write cleaned-up)
        (printf "from redex:\n")
        (pretty-write redex-result)
        (printf "from racket at the top-level:\n")
        (pretty-write racket-result)
        #f]
       [(not (equal? redex-result racket-module-result))
        (printf "cleaned up:\n")
        (pretty-write cleaned-up)
        (printf "from redex:\n")
        (pretty-write redex-result)
        (printf "from racket in a module:\n")
        (pretty-write racket-module-result)
        #f]
       [else #t])]))

(define v? (redex-match? lang v))
(define lam? (redex-match? lang (λ (x ...) e)))
(define (redex-eval prog)
  (define-values (result io) (result-and-output-of prog))
  (define normalized-result
    (cond
      [(or (lam? result) (member result '(* - + =))) 'procedure]
      [(equal? result 'infinite-loop) result]
      [(v? result) result]
      [else 'error]))
  (list normalized-result io))

;; e -> (list/c (or/c 'error value) (listof value))
(define (racket-eval prog)
  (define sp (open-output-string))
  (define result
    (with-handlers ([exn:fail? (λ (x) 'error)])
      (parameterize ([current-output-port sp])
        (eval prog ns))))
  (close-output-port sp)
  (list (normalize-result result) (normalize-io sp)))

;; e -> (list/c (or/c 'error value) (listof value))
(define racket-module-eval-name-counter 0)
(define (racket-module-eval prog)
  (define sp (open-output-string))
  (define modname
    (string->symbol (~a "racket-module-eval-module-name-" racket-module-eval-name-counter)))
  (set! racket-module-eval-name-counter (+ racket-module-eval-name-counter 1))
  (define result
    (with-handlers ([exn:fail? (λ (x) 'error)])
      (parameterize ([current-output-port sp])
        (eval `(,#'module ,modname
                          (submod (file ,(path->string letrec-vs-racket.rkt)) all-the-stuff-lang)
                          ,prog))
        (dynamic-require `',modname 'the-answer))))
  (close-output-port sp)
  (list (normalize-result result) (normalize-io sp)))

(define (normalize-io sp)
  (for/list ([l (in-lines (open-input-string (get-output-string sp)))])
    (cond
      [(regexp-match #rx"#<proc" l) 'procedure]
      [(regexp-match #rx"#<void" l) '(void)]
      [else (read (open-input-string l))])))

(define (normalize-result result)
  (match result
    [(? procedure?) 'procedure]
    [(? void?) '(void)]
    [_ result]))

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
