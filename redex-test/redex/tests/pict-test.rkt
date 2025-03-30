#lang racket/base
(require racket/file)
;; these tests just make sure that errors don't happen.

(module test racket/base)

(require redex/reduction-semantics
         redex/pict
         pict 
         racket/gui/base
         racket/class
         rackunit)

(define-language empty-language)

(define-language var-ab
  [var (a 
        b)])
(void (render-language var-ab))

(define-language var-not-ab
  [var (variable-except x
                        y)])
(void (render-language var-not-ab))

(let ()
  (define-language L2
    [e ::= 0
       (1
        2)])

  (void (render-language L2)))

(let ()
  (define-language L2
    [e ::= any
       (let ([x e]
             ...
             [x e]
             [x e] ...)
         e)])

  (void (render-language L2)))

(let ()
  (define-metafunction empty-language [(zero any_in) 0])
  (void (render-metafunction zero)))

(void
 (render-reduction-relation
  (reduction-relation
   empty-language
   (--> number_const
        ,(term
          (+ number_const 0))))))

(void
 (render-reduction-relation 
  (reduction-relation
   empty-language
   (--> a b
        (fresh x)
        (fresh y)))))


(define-language x1-9 
  (x 1 2 3 4 5 6 7 8 9))

(define-extended-language x0-10 x1-9
  (x 0 .... 10))

(void (render-language x0-10))

(let ([tmp (make-temporary-file "redex-pict-test~a.pdf")])
  (render-language x0-10 tmp)
  (delete-file tmp))

(define-metafunction empty-language
  id : any -> any
  [(id any) any])

(check-equal?
 (pict-width
  (parameterize ([metafunction-cases '()])
    (render-metafunction id)))
 0)

(check-equal?
 (pict-height
  (parameterize ([metafunction-cases '()])
    (render-metafunction id)))
 0)

(void
 (parameterize ([metafunction-cases '()])
   (render-metafunction id #:contract? #t)))

(define-judgment-form empty-language
  #:mode (deep-empty I)
  #:contract (deep-empty any)
  [-----
   (deep-empty ())]
  [(deep-empty any)
   ----
   (deep-empty (any))])

(check-equal?
 (pict-width
  (parameterize ([metafunction-cases '()])
    (render-judgment-form deep-empty)))
 0)

(check-equal?
 (pict-height
  (parameterize ([metafunction-cases '()])
    (render-judgment-form deep-empty)))
 0)

;; make sure fresh variables in judgment forms don't crash
(let ()
  (define-language L
    (x ::= variable-not-otherwise-mentioned))

  (define-judgment-form L
    #:mode (J I)
    #:contract (J any)

    [(where x_2 ,(variable-not-in (term e) 'x))
     ------------------------------------------
     (J any)])

  (void (render-judgment-form J)))

;; check the contracts for the various rule-pict functions
(void
 (parameterize ([rule-pict-style
                 (λ (rule-pict-infos)
                   (for ([r (in-list rule-pict-infos)])
                     (rule-pict-info-arrow r)
                     (rule-pict-info-lhs r)
                     (rule-pict-info-rhs r)
                     (rule-pict-info-label r)
                     (rule-pict-info-computed-label r)
                     (rule-pict-info->side-condition-pict r))
                   (blank))])
   (render-reduction-relation
    (reduction-relation
     empty-language
     (--> (a any) 1 "a")
     (--> (b any) 2 b)
     (--> (c any) 3 (computed-name (format "c: ~a" (term any))))
     (--> (d any) 4)
     (--> (e any) 5 (where (1) any))))))

(void
 (render-term/pretty-write empty-language (term (1 2 3))))

(void
 (render-term/pretty-write empty-language (term (any_1 any_2 any_1))))

(void
 (render-term/pretty-write empty-language (term hole)))
(void
 (render-term/pretty-write empty-language (term (1 2 (((hole))) 3 4))))

(let ()
  (define-language L1)
  (check-exn
   (λ (x)
     (and (exn:fail? x)
          (regexp-match? #rx"expected some non-terminals to render"
                         (exn-message x))))
   (λ () (render-language L1)))
  (define-union-language L2 L1)
  (check-exn
   (λ (x)
     (and (exn:fail? x)
          (regexp-match? #rx"cannot render the result of define-union-language"
                         (exn-message x))))
   (λ () (render-language L2)))
  (define-extended-language L3 L2
    (e ::= a b))
  (check-true (pict? (render-language L3)))

  (check-exn
   (λ (x)
     (and (exn:fail? x)
          (regexp-match? #rx"expected some non-terminals to render"
                         (exn-message x))))
   (λ () (render-language L3 #:nts '())))

  (define-extended-language L4 L2
    (e ::= 1 2))
  (check-true (pict? (render-language L4))))

(printf "pict-test.rkt done\n")
