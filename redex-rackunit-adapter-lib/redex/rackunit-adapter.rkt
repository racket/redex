#lang racket
(provide
 (rename-out
  [in:test-->* test-->]
  [in:test-->>* test-->>]
  [in:test-judgment-holds test-judgment-holds]
  [in:test-equal test-equal])
 test-judgment-does-not-hold
 test-->>∃
 test--/>
 test--?>
 test-->>P
 test-->>P*)
(require redex/reduction-semantics
         rackunit
         (for-syntax syntax/parse)
         syntax/parse/define
         (for-syntax rackunit-abbrevs/error-reporting))

(define-syntax in:test-->*
  (syntax-parser
    [(_ R term results ...)
     (syntax/loc this-syntax
       (test--> R term (list results ...)))]))

(define-syntax in:test-->>*
  (syntax-parser
    [(_ R term results ...)
     (syntax/loc this-syntax
       (test-->> R term (list results ...)))]))

(define-check (test--> R term expected)
  (define res (apply-reduction-relation R term))
  (unless (equal? (list->set res)
                  (list->set expected))
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "Did not match reductions in one step"))))

(define-check (test-->> R term results ...)
  (define res (apply-reduction-relation* R term))
  (define expected (list results ...))
  (unless (equal? (list->set res)
                  (list->set expected))
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "Did not match reductions in many"))))

(define-check (test-->>∃ R term expected)
  (define res (apply-reduction-relation* R term #:all? #t))
  (unless (memf (curry (default-equiv) expected) res)
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "could not find term not match reductions in many steps"))))

(define-check (test--/> R term)
  (define res (apply-reduction-relation R term))
  (unless (empty? res)
    (with-check-info
     (['results res])
     (fail-check "could not find term not match reductions in many steps"))))

(define-check (test--?> R term t)
  (define res (apply-reduction-relation R term))
  (if t
      (when (empty? res)
        (fail-check "had no reductions when it should have"))
      (unless (empty? res)
        (with-check-info
         (['results res])
         (fail-check "could not find term not match reductions in many steps")))))

(define-check (test-->>P R term P)
  (define res (apply-reduction-relation* R term))
  (define failed
    (for/list ([r (in-list res)]
               #:unless (P r))
      r))
  (unless (empty? failed)
    (with-check-info
     (['all-results res]
      ['failed failed])
     (fail-check "Some terminal reductions failed property"))))

(define-check (test-->>P* R term P)
  (define res (apply-reduction-relation* R term))
  (define failed (P res))
  (unless failed
    (with-check-info
     (['all-results res])
     (fail-check "Some terminal reductions failed property"))))

(define-syntax in:test-equal
  (syntax-parser
    [(test-equal a b)
     (syntax/loc this-syntax
       (test-equal a b #:equiv (default-equiv)))]
    [(test-equal a b #:equiv eq)
     #`(with-default-check-info*
        (list (make-check-name 'test-equial)
              (make-check-location '#,(syntax->location this-syntax))
              (make-check-expression
               '(test-equal a b #:equiv eq)))
        (lambda ()
          ((current-check-around)
           (lambda ()
             (define a* a)
             (define b* b)
             (unless (eq a* b*)
               (with-check-info
                (['expected a*]
                 ['actual b*])
                (fail-check)))))))]))

(define-syntax test-judgment-does-not-hold
  (syntax-parser
    [(test-judgment-does-not-hold (judgment body ...))
     #`(with-default-check-info*
        (list (make-check-name 'test-judgment-does-not-hold)
              (make-check-location '#,(syntax->location this-syntax))
              (make-check-expression
               '(test-judgment-doesnt-hold (judgment body ...))))
        (lambda ()
          ((current-check-around)
           (lambda ()
             (define r (judgment-holds (judgment body ...) (body ...)))
             (with-check-info
              (['|held at| (map (lambda (x) (cons 'judgment x)) r)])
              (unless (empty? r)
                (fail-check "judgment, in fact, held")))))))]))

(define-syntax in:test-judgment-holds
  (syntax-parser
    [(test-judgment-doesnt-hold (judgment body ...))
     #`(with-default-check-info*
        (list (make-check-name 'test-judgment-doesnt-hold)
              (make-check-location '#,(syntax->location this-syntax))
              (make-check-expression
               '(test-judgment-doesnt-hold (judgment body ...))))
        (lambda ()
          ((current-check-around)
           (lambda ()
             (define r (judgment-holds (judgment body ...)))
             (when (not r)
               (fail-check "judgment didn't hold"))))))]))

