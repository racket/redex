#lang racket/base

;; Test the `mf-apply` keyword:
;; - `mf-apply` is a syntax error outside terms
;; - `(mf-apply f e ...)` errors if `f` is not a metafunction,
;;   otherwise is the same as `(f e ...)`
;; - typesetting should not show `mf-apply` (in judgments or metafunctions)

;; -----------------------------------------------------------------------------

(require pict
         rackunit
         (only-in racket/class send)
         redex/reduction-semantics
         redex/pict
         syntax/macro-testing
         (for-syntax racket/base))

(define expected-mf #rx"expected a previously defined metafunction")

(define-language nats
  [nat Z (S nat)])

(define-syntax (fake-mf stx)
  #'Z)

(define-metafunction nats real-mf : nat -> nat
  [(real-mf nat)
   Z])

(define-metafunction nats mf2 : nat -> nat
  [(mf2 nat_0)
   (S nat_1)
   (where nat_1 (mf-apply real-mf nat_0))])

(define-judgment-form nats
  #:mode (jf I)
  #:contract (jf nat)
  [(where Z (mf-apply real-mf nat_0))
   ---
   (jf nat_0)])

;; -----------------------------------------------------------------------------
;; behavioral tests

(check-exn #rx"mf-apply: used outside of term"
  (λ () (convert-compile-time-error mf-apply))
  "mf-apply should error when used outside `term`")

(check-exn #rx"malformed mf-apply"
  (λ () (convert-compile-time-error (term (mf-apply))))
  "mf-apply should error when given 0 arguments")

(check-exn expected-mf
  (λ () (convert-compile-time-error (term (mf-apply yo (S Z)))))
  "mf-apply should error when given a number")

(check-exn expected-mf
  (λ () (convert-compile-time-error (term (mf-apply 8 (S Z)))))
  "mf-apply should error when given an unbound identifier")

(check-exn expected-mf
  (λ () (convert-compile-time-error (term (mf-apply fake-mf (S Z)))))
  "mf-apply should error when given a syntax transformer")

(check-exn expected-mf
  (λ () (convert-compile-time-error (let ()
          (define-metafunction nats mf2 : nat -> nat
            [(mf2 nat_0)
             (S nat_1)
             (where nat_1 (mf-apply fake-mf nat_0))])
          (void))))
  "mf-apply should error when given a syntax transformer in a where clause")

(check-exn expected-mf
  (λ () (convert-compile-time-error (let ()
          (define-judgment-form nats
            #:mode (jf I)
            #:contract (jf nat)
            [(where Z (mf-apply fake-mf nat_0))
             ---
             (jf nat_0)])
          (void))))
  "mf-apply should error when given a syntax transformer in a judgment form premise")

(check-equal?
  (term (mf-apply real-mf (S Z)))
  (term Z)
  "mf-apply should apply a given metafunction")

(check-equal?
  (term (mf2 (S Z)))
  (term (S Z)))

(check-true
  (judgment-holds (jf (S (S Z)))))

;; -----------------------------------------------------------------------------
;; typesetting tests

(define (pict->pixels p)
  (define b (pict->bitmap p))
  (define w (send b get-width))
  (define h (send b get-height))
  (define pixbuf (make-bytes (* 4 (inexact->exact (ceiling (* w h))))))
  (send b get-argb-pixels 0 0 w h pixbuf)
  pixbuf)

(define (pixels=? p1 p2)
  (equal? (pict->pixels p1) (pict->pixels p2)))

(check pixels=?
  (term->pict nats (term (mf-apply real-mf Z)))
  (term->pict nats (term (real-mf Z))))

(check pixels=?
  (term->pict/pretty-write nats (term (mf-apply real-mf Z)))
  (term->pict/pretty-write nats (term (real-mf Z))))

(check pixels=?
  (metafunction->pict mf2)
  (let () ;; mf2, without mf-apply
    (define-metafunction nats mf2 : nat -> nat
      [(mf2 nat_0)
       (S nat_1)
       (where nat_1 (real-mf nat_0))])
    (metafunction->pict mf2)))

(check pixels=?
  (judgment-form->pict jf)
  (let () ;; jf, without mf-apply
    (define-judgment-form nats
      #:mode (jf I)
      #:contract (jf nat)
      [(where Z (mf-apply real-mf nat_0))
       ---
       (jf nat_0)])
    (judgment-form->pict jf)))

;; -----------------------------------------------------------------------------
;; lw tests

;; Two lw structs that are similar --- but for occurrence of `mf-apply` ---
;;  currently look similar, but the one with the mf-apply will have a wider
;;  column span.

(define len-mf-apply (string-length "mf-apply "))

(define ((lw=? num-mf-apply) lw1 lw2)
  (define col-span-offset (* num-mf-apply len-mf-apply))
  (and (equal? (lw-column-span lw1) (+ (lw-column-span lw2) col-span-offset))
       (equal? (lw-e* lw1) (lw-e* lw2))))

;; lw-e* : lw -> (sexp (or/c string symbol))
(define (lw-e* lw)
  (define e (lw-e lw))
  (cond
   [(or (symbol? e) (string? e))
    e]
   [(list? e)
    (for/list ([lw (in-list e)])
      (lw-e* lw))]
   [else
    (raise-user-error 'mf-apply-test "expected symbol, string, or list inside lw ~a" lw)]))

(check (lw=? 1)
  (to-lw (term (mf-apply real-mf Z)))
  (to-lw (term (real-mf Z))))

(check (lw=? 2)
  (to-lw (term (mf-apply real-mf (mf-apply real-mf (S Z)))))
  (to-lw (term (real-mf (real-mf (S Z))))))

;; -----------------------------------------------------------------------------
;; typesetting, with-compound-rewriter test, from Ryan Culpepper

(let ()
  (define-language Arith
    [e number
       (plus e e)])

  (define-metafunction Arith
    [(invisible-id e) e])

  (define-metafunction Arith
    [(times e 1) e]
    [(times e natural_k)
     (plus e (times e ,(sub1 (term natural_k))))])

  (define (call/rewrites proc)
    (with-compound-rewriter
     'plus
     ;; (plus e1 e2) =render=> e1 + e2
     (lambda (lws) ;; wrapped "(" 'plus" <e1> <e2> ")"
       (list "" (caddr lws) " + " (cadddr lws) ""))
     (with-compound-rewriter
      'times
      ;; (times e1 n) =render=> e1 × e2
      (lambda (lws) ;; wrapped "(" 'times <e1> <e2> ")"
        (list "(" (caddr lws) ") × " (cadddr lws) ""))
      (with-compound-rewriter
       'invisible-id
       ;; (invisible-id e) =render=> e
       (lambda (lws)
         (list "" (caddr lws) ""))
       (proc)))))

  (test-case "mtwt:without-rewrites"
    (check pixels=?
      (term->pict Arith (times (plus 1 2) 3))
      (term->pict Arith (mf-apply times (plus 1 2) 3)))

    (check pixels=?
      (term->pict Arith (invisible-id (times (plus 1 2) 3)))
      (term->pict Arith (invisible-id (mf-apply times (plus 1 2) 3)))))

  (test-case "mtwt:with-rewrites"
    (check pixels=?
      (call/rewrites (lambda () (term->pict Arith (times (plus 1 2) 3))))
      (call/rewrites (lambda () (term->pict Arith (mf-apply times (plus 1 2) 3)))))

    (check pixels=?
      (call/rewrites (lambda () (term->pict Arith (invisible-id (times (plus 1 2) 3)))))
      (call/rewrites (lambda () (term->pict Arith (invisible-id (mf-apply times (plus 1 2) 3)))))))
)
