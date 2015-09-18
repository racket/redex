#lang racket

(provide (for-syntax compile-binding-forms))


(begin-for-syntax
 (require racket)

 (require "error.rkt")
 (require "binding-forms-definitions.rkt")
 (require (for-template "binding-forms-definitions.rkt"))
 (require "rewrite-side-conditions.rkt")


 ;; Intended for use in "reduction-semantics.rkt".
 ;; 
 ;; Takes the syntax that comes after a `#:binding-forms` and returns 
 ;; syntax<(listof (list pattern bspec))>
 (define (compile-binding-forms binding-forms-stx all-nts form-name)
   (syntax-case binding-forms-stx ()
     [((bf-name . bf-body) . rest-plus-exports)
      (begin
        ;; pull the #:exports off (it can only occur at the end of a binding form
        ;; declaration), along with all subsequent binding forms
        (define-values (rest-of-bfs exports)
          (syntax-case #'rest-plus-exports ()
            [(#:exports exports-beta . rest-of-bfs) (values #'rest-of-bfs #'exports-beta)]
            [(#:exports) (raise-syntax-error (syntax-e form-name)
                                             "#:exports requires an argument"
                                             #'rest-plus-exports)]
            [(rest-of-bfs ...)
             (values #'(rest-of-bfs ...) #'nothing)]
            [_ (raise-syntax-error (syntax-e form-name) "internal error")]))
        
        (define-values (pat bspec) 
          (surface-bspec->pat&bspec #`((bf-name . bf-body) #:exports #,exports) form-name))

        (with-syntax ([(syncheck-expr rewritten-pat _ _)
                       (rewrite-side-conditions/check-errs all-nts (syntax-e form-name) #t pat)])
          #`(cons (begin syncheck-expr `(rewritten-pat , `#,bspec))
                  #,(compile-binding-forms rest-of-bfs all-nts form-name)))
        )]
     [() #`'()]
     [anything (raise-syntax-error (syntax-e form-name) "expected a parenthesized binding form." #`anything)]))



 ;; === Name utilities ===
 
 (define (names-mentioned-in-beta/rec beta)
   (match beta
     [(rib/internal betas)
      (append* (map (λ (b) (names-mentioned-in-beta/rec b)) betas))]
     [(shadow/internal betas)
      (append* (map (λ (b) (names-mentioned-in-beta/rec b)) betas))]
     ;; PS: can we just return `names` here?
     [(.../internal beta names) (names-mentioned-in-beta/rec beta)]
     [name `(,name)]))

 ;; names-mentioned-in-beta : beta -> (listof symbol)
 (define (names-mentioned-in-beta beta)
   (remove-duplicates (names-mentioned-in-beta/rec beta)))


 (define (names-imported-in/rec body)
   (match body
     [(import/internal sub-body beta) (append (names-imported-in/rec sub-body)
                                              (names-mentioned-in-beta/rec beta))]
     [(.../internal sub-body _) (names-imported-in/rec sub-body)]
     [(...bind/internal _ _ _) '()] 
     [`(,car-body . ,cdr-body) (append (names-imported-in/rec car-body)
                                       (names-imported-in/rec cdr-body))]
     [anything-else `()]))

 (define (names-imported-in body)
   (remove-duplicates (names-imported-in/rec body)))

 (define (dedupe-names-and-depths lst form-name stx-for-error)
  (remove-duplicates
   lst
   (match-lambda*
    [`((,id-a ,depth-a) (,id-b ,depth-b))
     (if (symbol=? id-a id-b)
         (if (= depth-a depth-b)
             #t
             (raise-syntax-error
              (syntax-e form-name)
              (format "Same name used at two different ... depths: ~s (depth ~s) vs. ~s (depth ~s)"
                      id-a depth-a id-b depth-b)
              stx-for-error))
         #f)])))

 ;; this returns both the names and the `...` depth at which they were transcribed
 (define (names-transcribed-in-body/rec body depth)
   (match body
     [(import/internal sub-body beta)
      (names-transcribed-in-body/rec sub-body depth)]
     [(.../internal sub-body _)
      (names-transcribed-in-body/rec sub-body (+ depth 1))]
     [(...bind/internal export-name _ _) `((,export-name ,depth))]
     [`(,car-body . ,cdr-body)
      (append (names-transcribed-in-body/rec car-body depth)
              (names-transcribed-in-body/rec cdr-body depth))]
     [anything-else (if (symbol? anything-else)
                        `((,anything-else ,depth))
                        `())]))

 (define (names-transcribed-in-body body form-name stx-for-error)
   (dedupe-names-and-depths (names-transcribed-in-body/rec body 0) form-name stx-for-error))

 (module+ test
   (require rackunit)
   
   (check-equal? (names-mentioned-in-beta `a) `(a))
   (check-equal? (names-mentioned-in-beta 
                  (shadow/internal 
                   `(,(rib/internal `(a b c)) ,(shadow/internal `(b c d e))
                     ,(rib/internal `(f g h a a a))
                     b ,(shadow/internal `()) ,(shadow/internal `()))))
                 `(a b c d e f g h))
   
   (check-equal? (names-imported-in `((x) ,(import/internal `e `x))) `(x))
   (check-equal? (names-imported-in `((x) e)) `())
   (check-equal? (names-imported-in
                  `(,(import/internal `e_1 (shadow/internal `(x_2 x_444)))
                    (x_22 ,(import/internal `x_33 (rib/internal `(x_1 x_2)))
                          ,(import/internal `(e_2 ,(import/internal `e_3 (rib/internal `(x_9))))
                                            `x_3))))
                 `(x_2 x_444 x_1 x_9 x_3))
   (check-equal? (names-imported-in
                  `(,(import/internal `e_1 `x_1) ,(...bind/internal `tail `(x_2 x_3) `clause_2)))
                  `(x_1))
   )



 ;; === Surface syntax parsing ===

 (define (surface-beta->beta surface-beta form-name)
   (define (surface-betas->betas surface-betas)
     (syntax-case surface-betas (...)
       [(sub-s-beta (... ...) . rest)
        (let ((beta (surface-beta->beta #'sub-s-beta form-name)))
          `(,(.../internal beta (names-mentioned-in-beta beta))
            . ,(surface-betas->betas #'rest)))]
       [(sub-s-beta . rest)
        `(,(surface-beta->beta #'sub-s-beta form-name) . ,(surface-betas->betas #`rest))]
       [() `()]))
   
   (syntax-case surface-beta (shadow rib nothing)
     [(shadow . sub-s-betas)
      (shadow/internal (surface-betas->betas #'sub-s-betas))]
     [(rib . sub-s-betas)
      (rib/internal (surface-betas->betas #'sub-s-betas))]
     [nothing (shadow/internal '())]
     [nt-ref (if (identifier? #'nt-ref)
                 (syntax-e #'nt-ref)
                 (raise-syntax-error
                  (syntax-e form-name)
                  "expected a shadow, rib, nothing, or nonterminal" #'nt-ref))]))

 (module+ test
   (check-equal? (surface-beta->beta #'(rib (shadow nothing a b) c d) #'irrelevant)
                 (rib/internal `(,(shadow/internal `(,(shadow/internal `()) a b)) c d)))
   
   (check-equal? (surface-beta->beta #'(rib x (... ...)) #'irrelevant)
                 (rib/internal `(,(.../internal `x `(x)))))
   )



 ;; surface-bspec->pat&bspec : syntax syntax<ident> -> syntax<Redex pattern> bspec 
 (define (surface-bspec->pat&bspec surface-bspec form-name)
   (define-values (s-body export-beta)
     (syntax-case surface-bspec ()
       [(b #:exports e) (values #'b (surface-beta->beta #'e form-name))]
       [_ (raise-syntax-error (syntax-e form-name) "expected `(body #:exports beta)`"
                              surface-bspec)]))
   
   (define-values (bspec-body pat-body)
     (let loop [(s-body s-body) (bspec '()) (pat #'())]
       (define (rse str)
         (raise-syntax-error (syntax-e form-name) str s-body))
       

       (syntax-case s-body (...)
         [() (values bspec pat)]
         [(#:refers-to . rest-of-body) (rse "#:refers-to requires an expression to its left")]
         [((... ...) . rest-of-body) (rse "... requires an expression to its left")]
         [(sbspec-sub #:refers-to) (rse "#:refers-to requires an argument")]
         [(sbspec-sub #:...bind) (rse "#:...bind requires an argument")]
         [(sbspec-sub . rest)
          (begin ;; after getting the hard-to-parse syntax out of the way, do this:
            (define (process-under rest-of-body imports-beta dotdotdoting)
              (define (maybe-ddd sub dotdotdoting)
                (if dotdotdoting
                    (syntax-case dotdotdoting (nothing)
                      [(nothing nothing) ;; it was a plain `...`
                       (.../internal
                        sub
                        ;; n-t-i-b ignores the beta, anyways
                        (map first (names-transcribed-in-body sub form-name #'sbspec-sub)))]
                      
                      [(export-name imports exports)
                       ;; make a spec for separate binding object that `...bind` creates
                       (let-values 
                           ([(_ sub-bspec) 
                             (surface-bspec->pat&bspec 
                              #`((#,sub export-name #:refers-to imports) #:exports exports)
                              form-name)])
                       
                         (...bind/internal (syntax-e #'export-name)
                                           (map first (names-transcribed-in-body 
                                                       sub form-name #'sbspec-sub))
                                           sub-bspec))])
                    sub))

              (define (maybe-import sub imports-beta)
                (if imports-beta
                    (import/internal 
                     sub
                     (surface-beta->beta imports-beta form-name))
                    sub))

              (begin
                (define-values (bspec-sub pat-sub) (loop #'sbspec-sub '() #'()))
                (loop rest-of-body
                      `(,@bspec 
                        ,(maybe-ddd (maybe-import bspec-sub imports-beta) dotdotdoting))
                      #`(#,@pat #,pat-sub #,@(if dotdotdoting #`((... ...)) #`())))))


            (syntax-case #'rest (...) ;; is it followed by a postfix/infix operator?
              [(#:refers-to imports-beta (... ...) . rest-of-body)
               (process-under #'rest-of-body #'imports-beta #'(nothing nothing))]
              [(#:refers-to imports-beta #:...bind (name tail-imports tail-exports) . rest-of-body)
               (process-under #'rest-of-body #'imports-beta #'(name tail-imports tail-exports))]
              [(#:refers-to imports-beta #:...bind . anything-else)
               (rse "#...bind must be followed by `(name tail-imports tail-exports)`")]
              [(#:refers-to imports-beta . rest-of-body)
               (process-under #'rest-of-body #'imports-beta #f)]
              [((... ...) . rest-of-body)
               (process-under #'rest-of-body #f #'(nothing nothing))]
              [(#:...bind (name tail-imports tail-exports) . rest-of-body)
               (process-under #'rest-of-body #f #'(name tail-imports tail-exports))]
              [(#:...bind . anything-else)
               (rse "#...bind must be followed by `(name tail-imports tail-exports)`")]
              [rest-of-body ;; no imports or ...s
               (process-under #'rest-of-body #f #f)]))]

         [atomic-pattern (values (syntax-e #'atomic-pattern) #'atomic-pattern)])))
   
   (define import-names (names-imported-in bspec-body))
   (define export-names (names-mentioned-in-beta export-beta))

   (values
    pat-body
    (bspec bspec-body export-beta import-names export-names
           (remove-duplicates (append import-names export-names))
           (names-transcribed-in-body bspec-body form-name s-body))))


 (module+ test
   (define-syntax-rule (surface-bspec->bspec sb)
     (let ()
       (define-values (p b) (surface-bspec->pat&bspec sb #'irrelevant))
       b))
   
   (define lambda-bspec
     (surface-bspec->bspec #'((lambda (x) expr #:refers-to x) #:exports nothing)))

   (check-equal?
    lambda-bspec
    (bspec `(lambda (x) ,(import/internal 'expr 'x))
           (shadow/internal `()) '(x) '() '(x) `((lambda 0) (x 0) (expr 0))))
   
   (check-equal?
    (surface-bspec->bspec
     #'((form a b (c d #:refers-to h e) #:refers-to (shadow e b (rib nothing)) e f g h)
        #:exports (rib e f)))
    (bspec `(form a b ,(import/internal
                        `(c ,(import/internal `d `h) e)
                        (shadow/internal `(e b ,(rib/internal `(,(shadow/internal `())))))) e f g h)
           (rib/internal `(e f)) `(h e b) `(e f) `(h e b f)
           `((form 0) (a 0) (b 0) (c 0) (d 0) (e 0) (f 0) (g 0) (h 0))))
   
   (check-equal?
    (surface-bspec->bspec #'((form x_11
                                   e_1 #:refers-to (shadow x_2 x_444)
                                   (x_22 x_33 #:refers-to (rib x_1 x_2)
                                         (e_2 e_3 #:refers-to (rib x_9))
                                         #:refers-to x_3)) #:exports nothing))
    (bspec `(form x_11 ,(import/internal `e_1 (shadow/internal `(x_2 x_444)))
                  (x_22 ,(import/internal `x_33 (rib/internal `(x_1 x_2)))
                        ,(import/internal `(e_2 ,(import/internal `e_3 (rib/internal `(x_9))))
                                          `x_3)))
           (shadow/internal '()) `(x_2 x_444 x_1 x_9 x_3) `() 
           `(x_2 x_444 x_1 x_9 x_3)
           `((form 0) (x_11 0) (e_1 0) (x_22 0) (x_33 0) (e_2 0) (e_3 0))))



   (define va-lambda-bspec
     (surface-bspec->bspec #`((va-lambda (x (... ...)) expr #:refers-to (rib x (... ...)))
                              #:exports nothing)))

   (check-equal?
    va-lambda-bspec
    (bspec `(va-lambda (,(.../internal `x `(x))) 
                       ,(import/internal `expr (rib/internal `(,(.../internal `x `(x))))))
           (shadow/internal `()) `(x) `() `(x)
           `((va-lambda 0) (x 1) (expr 0))))


   ;; imported, exported, imported and exported
   (define ieie-bspec
     (surface-bspec->bspec
      #`((ieie i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
         #:exports (shadow e ie))))
   )
 )


