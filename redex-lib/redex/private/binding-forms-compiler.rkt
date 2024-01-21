#lang racket/base

(provide compile-binding-forms)

 (require racket/match
          racket/list
          "error.rkt"
          "binding-forms-definitions.rkt"
          "rewrite-side-conditions.rkt"
          (for-template racket/base "binding-forms-definitions.rkt"))


 ;; Intended for use in "reduction-semantics.rkt".
 ;;
 ;; Takes the syntax that comes after a `#:binding-forms` and returns
 ;; syntax<(listof (list pattern bspec))>
 (define (compile-binding-forms binding-forms-stx all-nts form-name aliases nt-identifiers)
   (syntax-case binding-forms-stx ()
     [(bf-name+bf-body . rest-plus-exports)
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

        (define-values (pat bspec betas+ellipses)
          (surface-bspec->pat&bspec
           (quasisyntax/loc #'bf-name+bf-body (bf-name+bf-body #:exports #,exports))
           form-name))
        
        (with-syntax ([(syncheck-expr rewritten-pat-with-betas _ _)
                       (rewrite-side-conditions/check-errs all-nts (syntax-e form-name) #t
                                                           `(,pat ,betas+ellipses)
                                                           #:aliases aliases
                                                           #:nt-identifiers nt-identifiers)])
          (syntax-case #'rewritten-pat-with-betas (list)
            [(list rewritten-pat rewritten-betas)
             #`(cons (begin syncheck-expr `(rewritten-pat , `#,bspec))
                     #,(compile-binding-forms rest-of-bfs all-nts form-name aliases nt-identifiers))]))
        )]
     [() #`'()]
     [(#:refers-to . rest)
      (raise-syntax-error (syntax-e form-name)
                          "#:refers-to must appear nested inside a binding-form"
                          (car (syntax-e binding-forms-stx)))]
     [(x . y)
      (raise-syntax-error (syntax-e form-name) "expected a parenthesized binding form" #`x)]
     [anything
      (raise-syntax-error (syntax-e form-name) "expected a parenthesized binding form" #`anything)]))



 ;; === Name utilities ===

 (define (names-mentioned-in-beta/rec beta depth)
   (match beta
     [(shadow/internal betas)
      (append* (map (λ (b) (names-mentioned-in-beta/rec b depth)) betas))]
     ;; PS: can we just return `names` here?
     [(.../internal beta names) (names-mentioned-in-beta/rec beta (+ depth 1))]
     [name `((,name ,depth))]))

 ;; names-mentioned-in-beta : beta -> (listof symbol)
 (define (names-mentioned-in-beta beta)
   (remove-duplicates (map first (names-mentioned-in-beta/rec beta 0))))

 (define (names-mentioned-in-beta-with-depths beta form-name stx-for-error)
   (names-mentioned-in-beta/rec beta 0))

 (define (names-imported-in/rec body depth)
   (match body
     [(import/internal sub-body beta) (append (names-imported-in/rec sub-body depth)
                                              (names-mentioned-in-beta/rec beta depth))]
     [(.../internal sub-body _) (names-imported-in/rec sub-body (+ depth 1))]
     [(...bind/internal _ _ _) '()]
     [`(,car-body . ,cdr-body) (append (names-imported-in/rec car-body depth)
                                       (names-imported-in/rec cdr-body depth))]
     [anything-else `()]))

 ;; names-imported-in : body -> (listof symbol)
 (define (names-imported-in body)
   (remove-duplicates (map first (names-imported-in/rec body 0))))

 ;; names-imported-in-with-depths : body -> (listof (list symbol number))
 (define (names-imported-in-with-depths body form-name stx-for-error)
   (names-imported-in/rec body 0))

 ;; this returns both the names and the `...` depth at which they were transcribed
 (define (names-transcribed-in-body body form-name stx-for-error)
   (define names-to-depths (make-hash))
   (let loop ([body body] [depth 0])
     (define (add-name s) (hash-set! names-to-depths s depth))
     (match body
       [(import/internal sub-body beta)
        (loop sub-body depth)]
       [(.../internal sub-body _)
        (loop sub-body (+ depth 1))]
       [(...bind/internal export-name _ _)
        (add-name export-name)]
       [(cons car-body cdr-body)
        (loop car-body depth)
        (loop cdr-body depth)]
       [(? symbol? s)
        (add-name s)]
       [_ (void)]))
   (sort (hash-map names-to-depths list) symbol<? #:key car))

 (module+ test
   (require rackunit)

   (check-equal? (names-mentioned-in-beta `a) `(a))
   (check-equal? (names-mentioned-in-beta
                  (shadow/internal
                   `(,(shadow/internal `(a b c)) ,(shadow/internal `(b c d e))
                     ,(shadow/internal `(f g h a a a))
                     b ,(shadow/internal `()) ,(shadow/internal `()))))
                 `(a b c d e f g h))

   (check-equal? (names-imported-in `((x) ,(import/internal `e `x))) `(x))
   (check-equal? (names-imported-in `((x) e)) `())
   (check-equal? (names-imported-in
                  `(,(import/internal `e_1 (shadow/internal `(x_2 x_444)))
                    (x_22 ,(import/internal `x_33 (shadow/internal `(x_1 x_2)))
                          ,(import/internal `(e_2 ,(import/internal `e_3 (shadow/internal `(x_9))))
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

   (syntax-case surface-beta (shadow nothing)
     [(shadow . sub-s-betas)
      (shadow/internal (surface-betas->betas #'sub-s-betas))]
     [nothing (shadow/internal '())]
     [nt-ref (if (identifier? #'nt-ref)
                 (syntax-e #'nt-ref)
                 (raise-syntax-error
                  (syntax-e form-name)
                  "expected a shadow, nothing, or nonterminal" #'nt-ref))]))

 (module+ test
   (check-equal? (surface-beta->beta #'(shadow (shadow nothing a b) c d) #'irrelevant)
                 (shadow/internal `(,(shadow/internal `(,(shadow/internal `()) a b)) c d)))

   (check-equal? (surface-beta->beta #'(shadow x (... ...)) #'irrelevant)
                 (shadow/internal `(,(.../internal `x `(x)))))
   )



 ;; surface-bspec->pat&bspec : syntax syntax<ident> ->
 ;;     syntax<Redex pattern> bspec syntax<redex pattern>
 ;; the third result is a redex pattern synthesized out of the `beta`s
 ;; that appear in the input; it is intended to be used only for
 ;; checking that the syntax is well-formed
 (define (surface-bspec->pat&bspec surface-bspec form-name)
   (define-values (s-body export-beta)
     (syntax-case surface-bspec ()
       [(b #:exports e) (values #'b (surface-beta->beta #'e form-name))]
       [_ (raise-syntax-error (syntax-e form-name) "expected `(body #:exports beta)`"
                              surface-bspec)]))

   ;; : (listof syntax)
   ;; these are all of the betas, in redex pattern form for error checking
   (define betas+ellipses '())
   (define (save-a-beta beta ellipsis-depth)
     (set! betas+ellipses
           (cons (for/fold ([beta beta])
                           ([i (in-range ellipsis-depth)])
                   `(,beta ...))
                 betas+ellipses)))
   
   (define-values (bspec-body pat-body)
     (let loop ([s-body s-body]
                [bspec '()]
                [pat #'()]
                [ellipsis-depth 0]
                [ellipses-as-this-level '()])
       (define (rse str)
         (raise-syntax-error (syntax-e form-name) str s-body))

       (syntax-case s-body (...)
         [()
          (begin
            (when (>= (length ellipses-as-this-level) 2)
              (define frontwards (reverse ellipses-as-this-level))
              (raise-syntax-error (syntax-e form-name)
                                  "at most one ellipsis is allowed in any sequence in a binding form"
                                  #f
                                  (car frontwards)
                                  (cdr frontwards)))
            (values bspec pat))]
         [(#:refers-to . rest-of-body) (rse "#:refers-to requires an expression to its left")]
         [((... ...) . rest-of-body) (rse "... requires an expression to its left")]
         [(sbspec-sub #:refers-to) (rse "#:refers-to requires an argument")]
         [(sbspec-sub #:...bind) (rse "#:...bind requires an argument")]
         [(sbspec-sub . rest)
          (begin ;; after getting the hard-to-parse syntax out of the way, do this:
            (define (process-under rest-of-body imports-beta dotdotdoting previous-ellipsis)
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
                           ([(_ sub-bspec betas+ellipses)
                             (surface-bspec->pat&bspec
                              (quasisyntax/loc #'sbspec-sub ((#,sub export-name #:refers-to imports) #:exports exports))
                              form-name)])
                         (for ([beta+ellipsis (in-list betas+ellipses)])
                           ;; add `ellipsis-depth` ellipses around the ones that
                           ;; we got from the previous call
                           (save-a-beta beta+ellipsis (+ ellipsis-depth 1)))
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
                (define-values (bspec-sub pat-sub) (loop #'sbspec-sub '() #'()
                                                         (if dotdotdoting
                                                             (+ ellipsis-depth 1)
                                                             ellipsis-depth)
                                                         '()))
                (loop rest-of-body
                      `(,@bspec
                        ,(maybe-ddd (maybe-import bspec-sub imports-beta) dotdotdoting))
                      #`(#,@pat #,pat-sub #,@(if dotdotdoting #`((... ...)) #`()))
                      ellipsis-depth
                     (if previous-ellipsis
                         (cons previous-ellipsis ellipses-as-this-level)
                         ellipses-as-this-level))))

            (define (bind-must-be-followed-by)
              (rse "#...bind must be followed by `(id beta beta)`"))

            ;; save only the betas that appear in a #:refers-to;
            ;; the ones in #:...bind will show up in those positions, thanks
            ;; to the recursive call to surface-bspec->pat&bspec above.
            ;; (and the ones in #:export appear to be checked more carefully elsewhere?)
            (syntax-case #'rest (...) ;; is it followed by a postfix/infix operator?
              [(#:refers-to imports-beta (... ...) . rest-of-body)
               (begin
                 (save-a-beta #'imports-beta ellipsis-depth)
                 (process-under #'rest-of-body #'imports-beta #'(nothing nothing) #f))]
              [(#:refers-to imports-beta #:...bind (name tail-imports tail-exports) . rest-of-body)
               (begin
                 (save-a-beta #'imports-beta ellipsis-depth)
                 (process-under #'rest-of-body #'imports-beta #'(name tail-imports tail-exports) #f))]
              [(#:refers-to imports-beta #:...bind . anything-else)
               (bind-must-be-followed-by)]
              [(#:refers-to imports-beta . rest-of-body)
               (begin
                 (save-a-beta #'imports-beta ellipsis-depth)
                 (process-under #'rest-of-body #'imports-beta #f #f))]
              [((... ...) . rest-of-body)
               (process-under #'rest-of-body #f #'(nothing nothing) (car (syntax-e #'rest)))]
              [(#:...bind (name tail-imports tail-exports) . rest-of-body)
               (process-under #'rest-of-body #f #'(name tail-imports tail-exports) #f)]
              [(#:...bind . anythinge-else)
               (bind-must-be-followed-by)]
              [rest-of-body ;; no imports or ...s
               (process-under #'rest-of-body #f #f #f)]))]

         [atomic-pattern
          (begin
            (when (equal? (syntax-e #'atomic-pattern) 'in-hole)
              (raise-syntax-error 'define-language
                                  "`in-hole` is illegal in a binding specification"
                                  #'atomic-pattern))
            (values (syntax-e #'atomic-pattern) #'atomic-pattern))])))

   (define import-names (names-imported-in-with-depths bspec-body form-name s-body))
   (define export-names (names-mentioned-in-beta-with-depths export-beta form-name s-body))

   (define pattern-names (names-transcribed-in-body bspec-body form-name s-body))

   (define nonexistent-names (append 
                              (remove* pattern-names import-names
                                       (lambda (lhs rhs) (equal? (first lhs) (first rhs))))
                              (remove* pattern-names export-names
                                       (lambda (lhs rhs) (equal? (first lhs) (first rhs))))))

   (define (check-referrents names-and-depths)
     (for ([name-and-depth (in-list names-and-depths)])
       (unless (assoc (first name-and-depth) pattern-names)
         (raise-syntax-error 
          (syntax-e form-name)
          (format "unknown name imported or exported: ~a" (first name-and-depth))
          surface-bspec))))
   
   (check-referrents import-names)
   (check-referrents export-names)

   (values
    pat-body
    (bspec bspec-body export-beta
           (remove-duplicates (map first import-names))
           (remove-duplicates (map first export-names))
           (remove-duplicates (map first (append import-names export-names)))
           pattern-names)
    betas+ellipses))


 (module+ test
   (define-syntax-rule (surface-bspec->bspec sb)
     (let ()
       (define-values (p b _) (surface-bspec->pat&bspec sb #'irrelevant))
       b))

   (define lambda-bspec
     (surface-bspec->bspec #'((lambda (x) expr #:refers-to x) #:exports nothing)))

   (check-equal?
    lambda-bspec
    (bspec `(lambda (x) ,(import/internal 'expr 'x))
           (shadow/internal `()) '(x) '() '(x) `((expr 0) (lambda 0) (x 0))))

   (check-equal?
    (surface-bspec->bspec
     #'((form a b (c d #:refers-to h e) #:refers-to (shadow e b (shadow nothing)) e f g h)
        #:exports (shadow e f)))
    (bspec `(form a b ,(import/internal
                        `(c ,(import/internal `d `h) e)
                        (shadow/internal `(e b ,(shadow/internal `(,(shadow/internal `())))))) e f g h)
           (shadow/internal `(e f)) `(h e b) `(e f) `(h e b f)
           `((a 0) (b 0) (c 0) (d 0) (e 0) (f 0) (form 0) (g 0) (h 0))))

   (check-equal?
    (surface-bspec->bspec #'((form x_11
                                   x_1 x_2 x_444 x_9 x_3
                                   e_1 #:refers-to (shadow x_2 x_444)
                                   (x_22 x_33 #:refers-to (shadow x_1 x_2)
                                         (e_2 e_3 #:refers-to (shadow x_9))
                                         #:refers-to x_3)) #:exports nothing))
    (bspec `(form x_11 x_1 x_2 x_444 x_9 x_3 ,(import/internal `e_1 (shadow/internal `(x_2 x_444)))
                  (x_22 ,(import/internal `x_33 (shadow/internal `(x_1 x_2)))
                        ,(import/internal `(e_2 ,(import/internal `e_3 (shadow/internal `(x_9))))
                                          `x_3)))
           (shadow/internal '())
           `(x_2 x_444 x_1 x_9 x_3)
           `()
           `(x_2 x_444 x_1 x_9 x_3)
           (map (λ (nm) `(,nm 0)) `(e_1 e_2 e_3 form x_1 x_11 x_2 x_22 x_3 x_33 x_444 x_9))))



   (define va-lambda-bspec
     (surface-bspec->bspec #`((va-lambda (x (... ...)) expr #:refers-to (shadow x (... ...)))
                              #:exports nothing)))

   (check-equal?
    va-lambda-bspec
    (bspec `(va-lambda (,(.../internal `x `(x)))
                       ,(import/internal `expr (shadow/internal `(,(.../internal `x `(x))))))
           (shadow/internal `()) `(x) `() `(x)
           `((expr 0) (va-lambda 0) (x 1))))


   ;; imported, exported, imported and exported
   (define ieie-bspec
     (surface-bspec->bspec
      #`((ieie i e ie expr_1 #:refers-to (shadow ie i) expr_2 #:refers-to (shadow i ie))
         #:exports (shadow e ie))))
   )
