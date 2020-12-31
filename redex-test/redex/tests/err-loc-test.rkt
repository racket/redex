#lang racket/base

(module util racket/base
  (require setup/path-to-relative
           racket/runtime-path
           "private/test-util.rkt"
           syntax/strip-context
           racket/set)
  (provide exec-syntax-error-tests
           exec-runtime-error-tests
           syn-err-test-namespace
           check-syntax/runtime-test-complete)
  
  (define-runtime-path run-err-tests "run-err-tests")
  (define-runtime-path syn-err-tests "syn-err-tests")
  
  (define syn-err-test-namespace (make-base-namespace))
  (parameterize ([current-namespace syn-err-test-namespace])
    (eval '(require (for-syntax racket/base)))
    (eval '(require redex/reduction-semantics)))
  
  (define (syntax-error-test-setup thunk)
    (parameterize ([current-namespace syn-err-test-namespace])
      (with-handlers ([exn:fail:syntax? 
                       (λ (exn) 
                         (values (exn-message exn)
                                 (map source-location (exn:fail:syntax-exprs exn))))])
        (thunk))))
  (define ((runtime-error-test-setup depth-in-stack) thunk)
    (define errortrace-key (dynamic-require 'errortrace/errortrace-key 'errortrace-key))
    (parameterize ([current-compile ((dynamic-require 'errortrace/errortrace-lib
                                                      'make-errortrace-compile-handler))])
      (with-handlers ([exn:fail? 
                       (λ (exn)
                         (define marks
                           (continuation-mark-set->list
                            (exn-continuation-marks exn)
                            errortrace-key))
                         (define mark
                           (if (< (length marks) depth-in-stack)
                               '()
                               (list (cdr (list-ref marks depth-in-stack)))))
                         (values (exn-message exn)
                                 (let loop ([ans mark])
                                   (cond
                                     [(pair? ans) (cons (loop (car ans)) (loop (cdr ans)))]
                                     [(path? ans) (path->relative-string/library ans)]
                                     [else ans]))))])
        (thunk))))

  (define syntax-error-tests-box (box '()))
  (define (exec-syntax-error-tests path)
    (exec-error-tests syn-err-tests syntax-error-test-setup
                      expand syntax-error-tests-box path))

  (define runtime-error-tests-box (box '()))
  (define (exec-runtime-error-tests path  #:depth-in-stack [depth-in-stack 0])
    (exec-error-tests run-err-tests (runtime-error-test-setup depth-in-stack)
                      eval runtime-error-tests-box path))
  
  (define (exec-error-tests base-path setup exec b path)
    (set-box! b (cons path (unbox b)))
    (for ([test (in-list (read-tests (build-path base-path path)))])
      (exec-error-test test exec setup)))
  
  (define (exec-error-test spec exec setup)
    (define-values (file line expected-message expected-sources test)
      (make-error-test spec))
    (let-values ([(actual-message actual-sources)
                  (setup (λ () (begin (exec (strip-context test)) (values "" '()))))])
      (test/proc (λ () actual-message) expected-message line file)
      (test/proc (λ () actual-sources) expected-sources line file)))
  
  (define (make-error-test spec)
    (syntax-case spec ()
      [(message named-pieces body)
       (make-error-test (syntax/loc spec (message named-pieces () body)))]
      [(message ([loc-name loc-piece] ...) ([non-loc-name non-loc-piece] ...) body)
       (values (and (path? (syntax-source spec))
                    (path->relative-string/library (syntax-source spec)))
               (syntax-line spec)
               (syntax-e #'message)
               (map source-location (syntax->list #'(loc-piece ...)))
               #'(let-syntax ([subst 
                               (λ (stx)
                                 (syntax-case (syntax-local-introduce stx) ()
                                   [(_ loc-name ... non-loc-name ...)
                                    #'body]))])
                   (subst loc-piece ... non-loc-piece ...)
                   (void)))]))
  
  (define (source-location stx)
    (list (and (path? (syntax-source stx))
               (path->relative-string/library (syntax-source stx))) 
          (syntax-line stx) 
          (syntax-column stx) 
          (syntax-position stx)
          (syntax-span stx)))
  
  (define (read-tests path)
    (call-with-input-file path
      (λ (port)
        (port-count-lines! port)
        (let loop ()
          (define test (read-syntax path port))
          (if (eof-object? test)
              '()
              (cons test (loop)))))))

  (define (check-syntax/runtime-test-complete)
    (check-test-complete syntax-error-tests-box syn-err-tests)
    (check-test-complete runtime-error-tests-box run-err-tests))

  (define (check-test-complete tested-files base-path)
    (define all-tested-files (apply set (unbox tested-files)))
    (for ([file (in-list (directory-list base-path))]
          #:unless (regexp-match #rx"~$" (path->bytes file)))
      (unless (set-member? all-tested-files (path->string file))
        (define-values (base-base base1 dir?) (split-path base-path))
        (eprintf "err-lock-test.rkt: test not run: ~a\n" (build-path base1 file))))))

(require "private/test-util.rkt"
         redex/reduction-semantics
         (for-syntax racket/base)
         'util)

(reset-count)

(parameterize ([current-namespace syn-err-test-namespace])
  (eval '(define-language syn-err-lang
           (M (M M)
              number)
           (E hole
              (E M)
              (number E))
           (X (number any)
              (any number))
           (Q (Q ...)
              variable)
           (UN (add1 UN)
               zero))))

(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require (for-syntax racket/base)))
  (eval '(require redex/reduction-semantics redex/pict))
  (eval '(define-language L
           (s a b c)))
  (exec-runtime-error-tests "define-union-language.rktd"))

(exec-syntax-error-tests "language-definition.rktd")

;; term with #:lang tests
(exec-syntax-error-tests "term-lang.rktd")

(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require redex/reduction-semantics))
  (eval '(require (for-syntax racket/base)))
  (exec-runtime-error-tests "metafunction-undefined.rktd")
  (exec-runtime-error-tests "judgment-form-undefined.rktd"))

(exec-syntax-error-tests "metafunction-definition.rktd")

(exec-syntax-error-tests "relation-definition.rktd")

(exec-syntax-error-tests "reduction-relation-definition.rktd")

(exec-syntax-error-tests "redex-let.rktd")

(exec-syntax-error-tests "judgment-form-definition.rktd")
(exec-syntax-error-tests "judgment-holds.rktd")

(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require (for-syntax racket/base)))
  (eval '(require redex/reduction-semantics))
  (eval '(define-language L
           (s a b c)))
  (eval '(define-judgment-form L
           #:mode (ctc-fail I O)
           #:contract (ctc-fail s s)
           [(ctc-fail a q)]
           [(ctc-fail b s)
            (ctc-fail q s)]
           [(ctc-fail c s)
            (ctc-fail a s)]))
  (eval '(define-judgment-form L
           #:mode (inv-fail I O)
           #:contract (inv-fail s_1 s_2)
           #:inv ,(not (eq? (term s_1) (term s_2)))
           [(inv-fail s a)]))
  (exec-runtime-error-tests "judgment-form-contracts.rktd")
  (exec-runtime-error-tests "judgment-form-undefined.rktd")
  (exec-runtime-error-tests "judgment-form-ellipses.rktd")
  (exec-runtime-error-tests "judgment-form-where-error.rktd")
  (exec-runtime-error-tests "test-judgment-holds.rktd"))

(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require (for-syntax racket/base)))
  (eval '(require redex/reduction-semantics))
  (eval '(define-language L))
  (eval '(define-metafunction L
           ∨ : boolean boolean -> boolean
           [(∨ #f #f) #f]
           [(∨ boolean boolean) #t]))
  (exec-runtime-error-tests "metafunction-no-match.rktd"))

(require redex/private/term
         redex/private/lang-struct)
(define-namespace-anchor here)
(define ns (namespace-anchor->namespace here))
(parameterize ([current-namespace ns])
  (exec-runtime-error-tests "term.rktd"))
  
(exec-syntax-error-tests "term.rktd")

(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require (for-syntax racket/base racket/syntax)
                  redex/reduction-semantics))
  (exec-runtime-error-tests "test-equal.rktd" #:depth-in-stack 1)
  (exec-runtime-error-tests "test-predicate.rktd" #:depth-in-stack 1)
  (exec-runtime-error-tests "test-reduction-relation.rktd"))

(check-syntax/runtime-test-complete)
(print-tests-passed 'err-loc-test.rkt)

