#lang racket

(require (for-syntax
          syntax/parse
          "term-fn.rkt"
          "rewrite-side-conditions.rkt")
         "matcher.rkt"
         "lang-struct.rkt"
         "term.rkt")

(provide (for-syntax do-compile-modeless-judgment-form-proc)
         call-modeless-judgment-form)

(define-for-syntax (do-compile-modeless-judgment-form-proc
                    name mode clauses rule-names
                    nts orig lang syn-error-name
                    ;; bind-withs arg is here only
                    ;; to break a dependency cycle
                    bind-withs)
  (define (compile-clause clause clause-name)
    (syntax-parse clause
      [((_ . conc-pats) . prems)

       (define largest-used-prefix
         (let loop ([prems #'prems])
           (cond
             [(pair? prems)
              (max (loop (car prems))
                   (loop (cdr prems)))]
             [(syntax? prems) (loop (syntax-e prems))]
             [(symbol? prems)
              (define m (regexp-match #rx"^any_([0-9]*)$"
                                      (symbol->string prems)))
              (cond
                [m (string->number (list-ref m 1))]
                [else 0])]
             [else 0])))

       (define (get-name)
         (define n (+ largest-used-prefix 1))
         (set! largest-used-prefix n)
         (string->symbol (format "any_~a" n)))

       (define-values (modeless-prems
                       modeless-jf-name-only-prems
                       modeless-prem-jf-ids
                       premise-repeat-names
                       normal-prems)
         (let loop ([prems #'prems]
                    [modeless-prems '()]
                    [modeless-jf-name-only-prems '()]
                    [modeless-prem-jf-ids '()]
                    [premise-repeat-names '()]
                    [normal-prems '()])
           (syntax-parse prems
             [() (values (reverse modeless-prems)
                         (reverse modeless-jf-name-only-prems)
                         (reverse modeless-prem-jf-ids)
                         (reverse premise-repeat-names)
                         (reverse normal-prems))]
             [((form-name . rest-of-form) ellipsis . more)
              #:when (and (is-ellipsis? #'ellipsis)
                          (judgment-form-id? #'form-name)
                          (number?
                           (judgment-form-mode
                            (lookup-judgment-form-id #'form-name))))
              (define name (get-name))
              (loop #'more
                    (list* #'ellipsis
                           #`(name #,name
                                   (#,(symbol->string (syntax-e #'form-name)) . rest-of-form))
                           modeless-prems)
                    (list* #'ellipsis
                           #`(name #,name
                                   (#,(symbol->string (syntax-e #'form-name)) any (... ...)))
                           modeless-jf-name-only-prems)
                    (cons #'form-name modeless-prem-jf-ids)
                    (cons name premise-repeat-names)
                    normal-prems)]
             [(other-stuff ellipsis . more)
              #:when (is-ellipsis? #'ellipsis)
              (loop #'more
                    modeless-prems
                    modeless-jf-name-only-prems
                    modeless-prem-jf-ids
                    premise-repeat-names
                    (list* #'ellipsis #'other-stuff normal-prems))]
             [((form-name . rest-of-form) . more)
              #:when (and (judgment-form-id? #'form-name)
                          (number?
                           (judgment-form-mode
                            (lookup-judgment-form-id #'form-name))))
              (loop #'more
                    (cons #`(#,(symbol->string (syntax-e #'form-name)) . rest-of-form)
                           modeless-prems)
                    (cons #`(#,(symbol->string (syntax-e #'form-name)) any (... ...))
                          modeless-jf-name-only-prems)
                    (cons #'form-name modeless-prem-jf-ids)
                    (cons #f premise-repeat-names)
                    normal-prems)]
             [(ellipsis . more)
              #:when (is-ellipsis? #'ellipsis)
              (raise-syntax-error syn-error-name
                                  "unexpected ellipsis"
                                  #'ellipsis)]
             [(thing . more)
              (loop #'more
                    modeless-prems
                    modeless-jf-name-only-prems
                    modeless-prem-jf-ids
                    premise-repeat-names
                    (cons #'thing normal-prems))])))

       (define/syntax-parse (modeless-prems-syncheck-exp
                             modeless-prem
                             (modeless-prem-names ...)
                             (modeless-prem-names/ellipses ...))
         (rewrite-side-conditions/check-errs lang syn-error-name #t #`(#,@modeless-prems)))

       (define/syntax-parse (modeless-jf-name-only-prems-syncheck-exp
                             modeless-jf-name-only-prem
                             (modeless-jf-name-only-prem-names ...)
                             (modeless-jf-name-only-prem-names/ellipses ...))
         (rewrite-side-conditions/check-errs lang syn-error-name #t
                                             #`(#,@modeless-jf-name-only-prems)))

       (define/syntax-parse ((modeless-prem-jf-id modeless-prem-proc modeless-prem-contract-id) ...)
         (for/list ([modeless-prem-jf-id (in-list modeless-prem-jf-ids)])
           (define jf-record (lookup-judgment-form-id modeless-prem-jf-id))
           #`(#,modeless-prem-jf-id
              #,(judgment-form-proc jf-record)
              #,(judgment-form-compiled-input-contract-pat-id jf-record))))

       (define/syntax-parse (conc-syncheck-exp
                             conc
                             (conc-names ...)
                             (conc-names/ellipses ...))
         (rewrite-side-conditions/check-errs lang syn-error-name #t #'conc-pats))

       (define-values (body compiled-pattern-identifiers patterns-to-compile)
         (parameterize ([judgment-form-pending-expansion
                         (cons name
                               (struct-copy judgment-form (lookup-judgment-form-id name)
                                            [proc #'recur]
                                            [cache #'recur-cache]
                                            [original-contract-expression-id
                                             #'original-contract-expression]
                                            [compiled-input-contract-pat-id
                                             #'compiled-input-contract-pat]
                                            [compiled-output-contract-pat-id
                                             #'compiled-output-contract-pat]))])
           (bind-withs syn-error-name '() lang nts lang
                       normal-prems
                       #`'(#t) ;; body
                       (syntax->list #'(conc-names ... modeless-prem-names ...))
                       (syntax->list #'(conc-names/ellipses ... modeless-prem-names/ellipses ...))
                       #f
                       #f)))
       (define other-conditions
         (with-syntax ([(compiled-pattern-identifier ...) compiled-pattern-identifiers]
                       [(pattern-to-compile ...) patterns-to-compile])
           #`(let ([compiled-pattern-identifier (compile-pattern lang pattern-to-compile #t)] ...)
               (λ (bnds)
                 #,(bind-pattern-names
                    'judgment-form
                    #'(conc-names/ellipses ...
                       modeless-prem-names/ellipses ...)
                    #'((lookup-binding bnds 'conc-names) ...
                       (lookup-binding bnds 'modeless-prem-names) ...)
                    body)))))

       (define (get-id-depths ids)
         (define ht (make-hash))
         (for ([id (in-list (syntax->list ids))])
           (define-values (sym depth) (get-id-depth id))
           (hash-set! ht sym depth))
         ht)
       (define (get-id-depth stx)
         (let loop ([stx stx]
                    [n 0])
           (syntax-case stx ()
             [(more ell)
              (is-ellipsis? #'ell)
              (loop #'more (+ n 1))]
             [_ (values (syntax-e stx) n)])))
       (define premise-id-depths (get-id-depths #'(modeless-prem-names/ellipses ...)))
       (define conc-id-depths (get-id-depths #'(conc-names/ellipses ...)))
       (define (get-ids-to-dup our-id-depths others-id-depths)
         (for/list ([(id depth) (in-hash our-id-depths)]
                    #:when (< depth
                              (hash-ref others-id-depths id -inf.0)))
           id))

       #`(begin
           conc-syncheck-exp
           modeless-jf-name-only-prems-syncheck-exp
           modeless-prems-syncheck-exp
           (build-modeless-jf-clause
            lang
            `conc
            '(#,@(get-ids-to-dup conc-id-depths premise-id-depths))
            `modeless-prem
            '(#,@(get-ids-to-dup premise-id-depths conc-id-depths))
            `modeless-jf-name-only-prem
            '(#,@premise-repeat-names)
            #,other-conditions
            (list (λ (deriv only-check-contracts?)
                    (call-modeless-judgment-form lang
                                                 'modeless-prem-jf-id
                                                 modeless-prem-proc
                                                 modeless-prem-contract-id
                                                 deriv
                                                 only-check-contracts?)) ...)))]))

  (define noname-clauses '())
  (define named-clauses '())
  (for ([clause (in-list clauses)]
        [rule-name (in-list rule-names)])
    (define compiled (compile-clause clause rule-name))
    (cond
      [rule-name (set! named-clauses
                       (cons #`(cons #,rule-name (list #,compiled))
                             named-clauses))]
      [else (set! noname-clauses (cons compiled noname-clauses))]))

  #`(λ (lang)
      (make-hash (list #,@named-clauses
                       #,@(if (null? noname-clauses)
                              (list)
                              (list #`(cons #f (list #,@noname-clauses))))))))

(define (build-modeless-jf-clause lang conc conc-ids-to-duplicate
                                  modeless-prem modeless-prem-ids-to-duplicate
                                  modeless-jf-name-only-prem
                                  premise-repeat-names other-conditions funcs)
  (modeless-jf-clause (compile-pattern lang conc #f)
                      conc-ids-to-duplicate
                      (compile-pattern lang modeless-prem #f)
                      modeless-prem-ids-to-duplicate
                      (compile-pattern lang modeless-jf-name-only-prem #f)
                      premise-repeat-names other-conditions funcs))

;; call-modeless-judgment-form: lang
;;                              symbol
;;                              hash[rulename -o> (listof modeless-jf-clause?)]
;;                              compiled-pattern
;;                              derivation
;;                              boolean
;;                              fail: (list/c derivation?) -> any/c
;;                           -> #t or any/c
;; a list of derivations indicates the list of sub-derivations that did not match.
(define (call-modeless-judgment-form lang jf-name modeless-jf-clause-table contract-cp deriv
                                     only-check-contracts?
                                     [fail (λ _ #f)])
  (match deriv
    [(derivation (cons deriv-jf-name jf-args) rule-name sub-derivations)
     (cond
       [(equal? jf-name deriv-jf-name)
        (modeless-judgment-form-check-contract jf-name contract-cp jf-args)
        (unless only-check-contracts?
          (define rules (hash-ref modeless-jf-clause-table rule-name #f))
          (cond
            [rules
             (modeless-jf-process-rule-candidates
              lang
              rules
              jf-args
              sub-derivations
              fail)]
            [else
             (define known-rules (sort (hash-keys modeless-jf-clause-table) string<?))
             (error jf-name "unknown rule in derivation\n  rule: ~.s\n  known rules:~a"
                    rule-name
                    (apply string-append
                           (for/list ([rule (in-list known-rules)])
                             (format "\n   ~s" rule))))]))]
       [else (fail (list deriv))])]
    [_ (fail (list deriv))]))

(define (modeless-judgment-form-check-contract jf-name contract-cp jf-args)
  (when contract-cp
    (unless (match-pattern contract-cp jf-args)
      ;; actually it will show 9 if there are 9
      ;; arguments, and at most 8 otherwise
      (define max-args-shown 8)
      (define first-set-of-args
        (apply
         string-append
         (for/list ([i (in-range (if (= (+ max-args-shown 1)
                                        (length jf-args))
                                     (+ max-args-shown 1)
                                     max-args-shown))]
                    [jf-arg (in-list jf-args)])
           (format "\n  arg ~a: ~.s" (+ i 1) jf-arg))))
      (define maybe-more-args
        (if (> (length jf-args) (+ 1 max-args-shown))
            (format "\n  args ~a - ~a elided"
                    (+ max-args-shown 1)
                    (length jf-args))
            ""))
      (error jf-name
             "derivation's term field does not match contract~a"
             (string-append
              first-set-of-args
              maybe-more-args)))))

(define (modeless-jf-process-rule-candidates lang candidates jf-args sub-derivations fail [bad-derivs '()])
  (match candidates
    [`() (fail bad-derivs)]
    [(cons (modeless-jf-clause conclusion-compiled-pattern
                               conclusion-ids-to-duplicate
                               premises-compiled-pattern
                               premise-ids-to-duplicate
                               premises-jf-name-only-compiled-pattern
                               premises-repeat-names
                               other-conditions
                               premise-jf-procs)
           more-candidates)
     (define conc-mtch (match-pattern conclusion-compiled-pattern jf-args))
     (define (fail-to-next-candidate bad-subderivs)
       (modeless-jf-process-rule-candidates lang
                                            more-candidates
                                            jf-args
                                            sub-derivations
                                            fail
                                            (append bad-subderivs bad-derivs)))
     (cond
       [conc-mtch
        (define sub-derivations-arguments-term-list
          (for/list ([sub-derivation (in-list sub-derivations)])
            (define t (derivation-term sub-derivation))
            (cons (symbol->string (car t)) (cdr t))))
        (define sub-derivations-mtch (match-pattern premises-compiled-pattern
                                                    sub-derivations-arguments-term-list))
        (define sub-derivation-bindings (and sub-derivations-mtch
                                             (map mtch-bindings sub-derivations-mtch)))
        (define conc-bindings (map mtch-bindings conc-mtch))
        (define conc+sub-bindings
          (and sub-derivations-mtch
               (combine-bindings-lists sub-derivation-bindings
                                       premise-ids-to-duplicate
                                       conc-bindings
                                       conclusion-ids-to-duplicate
                                       (λ (a b) (alpha-equivalent? lang a b)))))
        (cond
          [conc+sub-bindings
           (modeless-jf-process-other-conditions
            lang
            sub-derivations
            conc+sub-bindings
            premises-repeat-names
            other-conditions
            premise-jf-procs
            fail-to-next-candidate)]
          [else
           ;; here we failed to match sub-derivation patterns, but that might
           ;; mean we have a contract violation and not just a wrong rule, so
           ;; lets check the contract before we move on to the next candidate
           ;; NB: there will be some contract violations that we cannot catch
           ;; if the jf names are messed up or ellipses are involved somehow
           (define sub-derivations-mtchs
             (match-pattern premises-jf-name-only-compiled-pattern
                            sub-derivations-arguments-term-list))
           (when sub-derivations-mtchs
             (for ([sub-derivations-mtch (in-list sub-derivations-mtchs)])
               (modeless-jf-check-sub-derivations lang
                                                  sub-derivations
                                                  (mtch-bindings sub-derivations-mtch)
                                                  premises-repeat-names
                                                  premise-jf-procs
                                                  #t
                                                  (λ _ #f))))
           (fail-to-next-candidate sub-derivations)])]
       [else (fail-to-next-candidate '())])]))


(define (modeless-jf-process-other-conditions lang
                                              sub-derivations
                                              conc+sub-bindings
                                              premises-repeat-names
                                              other-conditions
                                              premise-jf-procs
                                              fail)
  (match conc+sub-bindings
    [`() (fail sub-derivations)]
    [(cons conc+sub-binding conc+sub-bindings)
     (cond
       [(and (not-failure-value? (other-conditions conc+sub-binding))
             ; BLEH
             (equal? #t
                     (modeless-jf-check-sub-derivations lang
                                                        sub-derivations
                                                        conc+sub-binding
                                                        premises-repeat-names
                                                        premise-jf-procs
                                                        #f
                                                        fail)))
        #t]
       [else
        (modeless-jf-process-other-conditions lang
                                              sub-derivations
                                              conc+sub-bindings
                                              premises-repeat-names
                                              other-conditions
                                              premise-jf-procs
                                              fail)])]))

;; this might come back as an empty list or as #f
;; when failure; not clear to me why there are two failure values
(define (not-failure-value? x) (pair? x))

;; ... -> boolean (no fail continuation)
(define (modeless-jf-check-sub-derivations lang
                                           sub-derivations
                                           conc+sub-binding
                                           premises-repeat-names
                                           premise-jf-procs
                                           contract-checking-only?
                                           fail)
  (let loop ([premise-jf-procs premise-jf-procs]
             [premises-repeat-names premises-repeat-names]
             [sub-derivations sub-derivations])
    (match* (premise-jf-procs premises-repeat-names)
      [(`() `()) #t]
      [((cons premise-jf-proc premise-jf-procs)
        (cons premises-repeat-name premises-repeat-names))
       (define n (if premises-repeat-name
                     (length (lookup-binding conc+sub-binding premises-repeat-name))
                     1))
       (let n-loop ([n n]
                    [sub-derivations sub-derivations])
         (cond
           [(zero? n)
            (loop premise-jf-procs
                  premises-repeat-names
                  sub-derivations)]
           [else
            (match sub-derivations
              [(cons sub-derivation sub-derivations)
               (cond
                 [(premise-jf-proc sub-derivation contract-checking-only?)
                  (n-loop (- n 1) sub-derivations)]
                 [else (fail (list sub-derivation))])]
              [_ (fail (list sub-derivations))])]))])))

(struct modeless-jf-clause (conclusion-compiled-pattern
                            conclusion-ids-to-duplicate

                            ;; pattern with all of the premises
                            ;; strung together in a list, but where
                            ;; the names of the judgment forms are
                            ;; strings instead of symbols (so that they
                            ;; don't accidentally run into non-terminals, etc)
                            premises-compiled-pattern
                            premises-ids-to-duplicate

                            ;; pattern with all of the premises jf-names strung
                            ;; together, but with `any` for all of the arguments
                            ;; this is used to try to do some contract checking
                            premises-jf-name-only-compiled-pattern

                            ;; any premise with an ellipsis gets a name attached
                            ;; to it, these are the names (and #fs when there
                            ;; is not name (because the premise didn't have
                            ;; an ellipsis)
                            premises-repeat-names

                            other-conditions
                            premise-jf-procs))
