#lang racket/base

(require "matcher.rkt"
         "term.rkt"
         "fresh.rkt"
         "error.rkt"
         "search.rkt"
         "lang-struct.rkt"
         "binding-forms.rkt"
         "struct.rkt"
         "modeless-jf.rkt"
         racket/trace
         racket/list
         racket/stxparam
         racket/dict
         racket/match
         (only-in "pat-unify.rkt"
                  unsupported-pat-err-name
                  unsupported-pat-err))

(require
 (for-syntax "rewrite-side-conditions.rkt"
             "term-fn.rkt"
             "loc-wrapper-ct.rkt"
             racket/stxparam-exptime
             racket/base
             racket/syntax
             syntax/id-table
             racket/list
             syntax/parse
             syntax/stx))

;; structs that hold intermediate results when building a derivation
(struct derivation-subs-acc (subs-so-far rulename this-output) #:transparent)
(struct derivation-with-output-only (output name subs) #:transparent)

;; Intermediate structures recording clause "extras" for typesetting.
(define-struct metafunc-extra-side-cond (expr))
(define-struct metafunc-extra-where (lhs rhs))
(define-struct metafunc-extra-fresh (vars))

(define-struct runtime-judgment-form (name proc mode cache lang
                                           original-contract-expression
                                           compiled-input-contract-pat
                                           compiled-output-contract-pat
                                           input-contract-pat
                                           output-contract-pat
                                           rule-names
                                           lws
                                           relation?)
  #:methods gen:custom-write
  [(define (write-proc rjf port _mode)
     (if (runtime-judgment-form-mode rjf)
         (display "#<judgment-form: " port)
         (display "#<relation: " port))
     (define name+ctc
       (if (runtime-judgment-form-original-contract-expression rjf)
           (format "~s" (cons (runtime-judgment-form-name rjf)
                              (runtime-judgment-form-original-contract-expression rjf)))
           (format "~s" (runtime-judgment-form-name rjf))))
     (define length-limit 30)
     (cond
       [(< (string-length name+ctc) length-limit) (display name+ctc port)]
       [else
        (display (substring name+ctc 0 length-limit) port)
        (display "..." port)])
     (display ">" port))])
(define (build-runtime-judgment-form parent-judgment-form
                                     name proc mode lang
                                     original-contract-expression ;; (or/c #f (listof s-exp))
                                     input-contract-pat
                                     output-contract-pat
                                     rule-names
                                     lws
                                     relation?)
  (define cache (cons (box (make-hash)) (box (make-hash))))
  (make-runtime-judgment-form
   name proc mode cache lang
   (cond
     [original-contract-expression
      original-contract-expression]
     [parent-judgment-form
      (runtime-judgment-form-original-contract-expression
       parent-judgment-form)]
     [else #f])
   (cond
     [original-contract-expression
      (compile-pattern lang input-contract-pat #f)]
     [(and parent-judgment-form
           (runtime-judgment-form-input-contract-pat parent-judgment-form))
      =>
      (λ (pat) (compile-pattern lang pat #f))]
     [else #f])
   (cond
     [original-contract-expression
      (compile-pattern lang output-contract-pat #f)]
     [(and parent-judgment-form
           (runtime-judgment-form-output-contract-pat parent-judgment-form))
      =>
      (λ (pat) (compile-pattern lang pat #f))]
     [else #f])
   (or input-contract-pat
       (and parent-judgment-form
            (runtime-judgment-form-input-contract-pat parent-judgment-form)))
   (or output-contract-pat
       (and parent-judgment-form
            (runtime-judgment-form-output-contract-pat parent-judgment-form)))
   (map (lambda (raw-name)
          (cond
            [raw-name => (lambda (x)
                           (if (symbol? x)
                               x
                               (string->symbol x)))]
            [else raw-name]))
        rule-names)
   lws
   relation?))

(define-for-syntax (prune-syntax stx)
  (datum->syntax
   (identifier-prune-lexical-context #'whatever '(#%app #%datum))
   (let loop ([stx stx])
     (syntax-case stx ()
       [(a . b)
        (datum->syntax (identifier-prune-lexical-context #'whatever '(#%app))
                       (cons (loop #'a) (loop #'b))
                       stx
                       stx)]
       [x 
        (identifier? #'x)
        (identifier-prune-lexical-context #'x (list (syntax-e #'x) '#%top))]
       [() (datum->syntax #f '() stx stx)]
       [_ (datum->syntax (identifier-prune-lexical-context #'whatever '(#%datum))
                         (syntax->datum stx)
                         stx
                         stx)]))
   stx
   stx))

(define-syntax (--> stx) (raise-syntax-error '--> "used outside of reduction-relation"))
(define-syntax (fresh stx) (raise-syntax-error 'fresh "used outside of reduction-relation"))
(define-syntax (with stx) (raise-syntax-error 'with "used outside of reduction-relation"))

(module mode-utils racket/base
  
  (require racket/list)
  
  (provide split-by-mode
           assemble
           mode->arity)

  (define (mode->arity mode)
    (cond
      [(not mode)
       (error 'mode->arity.internal-error "no arity when mode is #f")]
      [(number? mode) mode]
      [else (length mode)]))
  
  (define (split-by-mode xs mode)
    (cond
      [(number? mode)
       (error 'split-by-mode
              "internal error: do not call this function for modeless judgment forms")]
      [mode
       (for/fold ([ins '()] [outs '()])
                 ([x (in-list (reverse xs))]
                  [m (in-list (reverse mode))])
         (case m
           [(I) (values (cons x ins) outs)]
           [(O) (values ins (cons x outs))]
           [else (error 'split-by-mode "ack ~s" m)]))]
      [else
       (values xs '())]))
  
  (define (assemble mode inputs outputs)
    (cond
      [(number? mode) inputs]
      [mode
       (let loop ([ms mode] [is inputs] [os outputs])
         (if (null? ms)
             '()
             (case (car ms)
               [(I) (cons (car is) (loop (cdr ms) (cdr is) os))]
               [(O) (cons (car os) (loop (cdr ms) is (cdr os)))])))]
      [else inputs])))

(require 'mode-utils
         (for-syntax 'mode-utils))

(define-for-syntax (generate-binding-constraints lang names names/ellipses bindings syn-err-name)
  (define (id/depth stx)
    (syntax-case stx ()
      [(s (... ...))
       (let ([r (id/depth #'s)])
         (make-id/depth (id/depth-id r) (add1 (id/depth-depth r))))]
      [s (make-id/depth #'s 0)]))
  (define temporaries (generate-temporaries names))
  (values
   (for/fold ([cs '()])
             ([n (in-list names)]
              [w/e (in-list names/ellipses)]
              [x (in-list temporaries)])
     (cond [(hash-ref bindings (syntax-e n) #f)
            => (λ (b) 
                 (let ([b-id/depth (id/depth b)]
                       [n-id/depth (id/depth w/e)])
                   (if (= (id/depth-depth b-id/depth) (id/depth-depth n-id/depth))
                       (cons #`(alpha-equivalent? #,lang #,x (term #,b)) cs)
                       (raise-ellipsis-depth-error
                        syn-err-name
                        (id/depth-id n-id/depth) (id/depth-depth n-id/depth)
                        (id/depth-id b-id/depth) (id/depth-depth b-id/depth)))))]
           [else cs]))
   temporaries
   (for/fold ([extended bindings])
             ([name (in-list names)]
              [w/ellipses (in-list names/ellipses)])
     (hash-set extended (syntax-e name) w/ellipses))))

;; the withs, freshs, and side-conditions come in backwards order
;; rt-lang is an identifier that will be bound to a (runtime) language,
;;   not necc bound via define-language. 
;; ct-lang is an identifier  guaranteed to be bound by define-language
;;   that can be used to call rewrite-side-conditions/check-errs, but
;;   some extension of that language may end up being bound to rt-lang
(define-for-syntax (bind-withs orig-name main rt-lang lang-nts ct-lang stx
                               body names w/ellipses
                               side-condition-unquoted?
                               jf-results-id)
  (define compiled-pattern-identifiers '())
  (define patterns-to-compile '())
  (define body-stx
    (with-disappeared-uses
     (let loop ([stx stx]
                [to-not-be-in main]
                [env (make-immutable-hash
                      (map (λ (x e) (cons (syntax-e x) e))
                           names w/ellipses))])
       (syntax-case stx (fresh judgment-holds)
         [() body]
         [((-where pat-stx e) y ...)
          (where-keyword? #'-where)
          (let ()
            (with-syntax ([(syncheck-exp side-conditions-rewritten (names ...) (names/ellipses ...))
                           (rewrite-side-conditions/check-errs
                            ct-lang
                            orig-name
                            #t
                            #'pat-stx)]
                          [lang-stx rt-lang])
              (define-values (binding-constraints temporaries env+)
                (generate-binding-constraints rt-lang
                                              (syntax->list #'(names ...))
                                              (syntax->list #'(names/ellipses ...))
                                              env
                                              orig-name))
              (with-syntax ([(binding-constraints ...) binding-constraints]
                            [(x ...) temporaries]
                            [(pat-id) (generate-temporaries '(bind-withs-pat_1))])
                (define rest-body (loop #'(y ...) #`(list x ... #,to-not-be-in) env+))
                (set! patterns-to-compile (cons #'`side-conditions-rewritten patterns-to-compile))
                (set! compiled-pattern-identifiers (cons #'pat-id compiled-pattern-identifiers))
                (define proc-stx
                  #`(λ (bindings)
                      (let ([x (lookup-binding bindings 'names)] ...)
                        (and binding-constraints ...
                             (λ ()
                               #,(bind-pattern-names orig-name
                                                     #'(names/ellipses ...)
                                                     #'(x ...)
                                                     rest-body))))))
                #`(begin
                    syncheck-exp
                    #,(if (where/error? #'-where)
                          (forward-errortrace-prop
                           #'pat-stx
                           (quasisyntax/loc #'pat-stx
                             (combine-where/error-results
                              pat-id
                              (term e #:lang #,ct-lang)
                              '#,orig-name #,rt-lang
                              #,proc-stx)))
                          #`(combine-where-results/flatten
                             pat-id
                             (term e #:lang #,ct-lang)
                             #,proc-stx))))))]
         [((-side-condition s ...) y ...)
          (side-condition-keyword? #'-side-condition)
          (if side-condition-unquoted?
              #`(and s ... #,(loop #'(y ...) to-not-be-in env))
              #`(and (term s) ... #,(loop #'(y ...) to-not-be-in env)))]
         [((fresh x) y ...)
          (identifier? #'x)
          #`(term-let ([x (variable-not-in #,to-not-be-in 'x)])
                      #,(loop #'(y ...) #`(list (term x) #,to-not-be-in) env))]
         [((fresh x name) y ...)
          (identifier? #'x)
          #`(term-let ([x (let ([the-name (term name)])
                            (verify-name-ok '#,orig-name the-name)
                            (variable-not-in #,to-not-be-in the-name))])
                      #,(loop #'(y ...) #`(list (term x) #,to-not-be-in) env))]
         [((fresh (y) (x ...)) z ...)
          #`(term-let ([(y #,'...)
                        (variables-not-in #,to-not-be-in
                                          (map (λ (_ignore_) 'y)
                                               (term (x ...))))])
                      #,(loop #'(z ...) #`(list (term (y #,'...)) #,to-not-be-in) env))]
         [((fresh (y) (x ...) names) z ...)
          #`(term-let ([(y #,'...)
                        (let ([the-names (term names)]
                              [len-counter (term (x ...))])
                          (verify-names-ok '#,orig-name the-names len-counter)
                          (variables-not-in #,to-not-be-in the-names))])
                      #,(loop #'(z ...) #`(list (term (y #,'...)) #,to-not-be-in) env))]
         [((judgment-holds j) . after)
          (loop (cons #'j #'after) to-not-be-in env)]
         [((form-name pats ...) . after)
          (judgment-form-id? #'form-name)
          (let ()
            (define premise (syntax-case stx () [(p . _) #'p]))
            (define-values (rest-clauses under-ellipsis?)
              (syntax-case #'after ()
                [(maybe-ellipsis . more)
                 (ellipsis? #'maybe-ellipsis)
                 (values #'more #t)]
                [_ (values #'after #f)]))
            (define judgment-form (lookup-judgment-form-id #'form-name))
            (check-judgment-arity stx premise)
            (define mode (judgment-form-mode judgment-form))
            (when (number? mode)
              ;; the compilation of modeless judgment forms pulls out all premises before
              ;; calling `bind-withs` and supplies only the ones that aren't modeless
              (raise-syntax-error
               orig-name
               "cannot use a modeless judgment-form except from another modeless judgment form"
               premise))
            (define runtime-judgment-form-id (judgment-form-runtime-judgment-form-id judgment-form))
            (define-values (input-template output-pre-pattern)
              (let-values ([(in out) (split-by-mode (syntax->list #'(pats ...)) mode)])
                (if under-ellipsis?
                    (let ([ellipsis (forward-errortrace-prop premise (syntax/loc premise (... ...)))])
                      (values #`(#,in #,ellipsis) #`(#,out #,ellipsis)))
                    (values in out))))
            (define-values (syncheck-exp output-pattern output-names output-names/ellipses)
              (with-syntax ([(syncheck-exp output names names/ellipses)
                             (rewrite-side-conditions/check-errs ct-lang orig-name #t
                                                                 output-pre-pattern)])
                (values #'syncheck-exp
                        #'output
                        (syntax->list #'names)
                        (syntax->list #'names/ellipses))))
            (define-values (binding-constraints temporaries env+)
              (generate-binding-constraints rt-lang output-names output-names/ellipses env orig-name))
            (define rest-body
              (loop rest-clauses #`(list (term #,output-pattern) #,to-not-be-in) env+))
            (define call
              (let ([input (forward-errortrace-prop
                            premise
                            (quasisyntax/loc premise (term #,input-template #:lang #,ct-lang)))])
                (define (make-traced input)
                  (forward-errortrace-prop
                   premise
                   (quasisyntax/loc premise
                     (call-judgment-form 'form-name
                                         #,(judgment-form-proc judgment-form)
                                         '#,mode #,input
                                         #,(if jf-results-id #''() #f)
                                         #,(judgment-form-cache judgment-form)
                                         #,ct-lang
                                         #,(judgment-form-original-contract-expression-id
                                            judgment-form)
                                         #,(judgment-form-compiled-input-contract-pat-id
                                            judgment-form)
                                         #,(judgment-form-compiled-output-contract-pat-id
                                            judgment-form)))))
                (if under-ellipsis?
                    #`(repeated-premise-outputs #,input (λ (x) #,(make-traced #'x)))
                    (make-traced input))))
            (record-disappeared-uses (list #'form-name))
            (with-syntax ([(output-name ...) output-names]
                          [(output-name/ellipsis ...) output-names/ellipses]
                          [(temp ...) temporaries]
                          [(binding-constraint ...) binding-constraints]
                          [(pat-id) (generate-temporaries '(bind-withs-pat_2))]) 
              (set! patterns-to-compile (cons #``#,output-pattern patterns-to-compile))
              (set! compiled-pattern-identifiers (cons #'pat-id compiled-pattern-identifiers))
              #`(begin
                  #,syncheck-exp
                  (void #,(defined-check runtime-judgment-form-id "judgment form" #:external #'form-name))
                  (judgment-form-bind-withs/proc
                   #,rt-lang
                   pat-id
                   #,call
                   #,under-ellipsis?
                   #,jf-results-id
                   (λ (bindings #,(if jf-results-id jf-results-id '_ignored))
                     (let ([temp (lookup-binding bindings 'output-name)] ...)
                       (and binding-constraint ...
                            #,(bind-pattern-names orig-name
                                                  #'(output-name/ellipsis ...)
                                                  #'(temp ...)
                                                  rest-body))))))))]))))
  (values body-stx
          compiled-pattern-identifiers
          patterns-to-compile))

(define (judgment-form-bind-withs/proc lang compiled-pattern output under-ellipsis? old-maps do-something)
  (for/fold ([outputs '()]) ([sub-output (in-list output)])
    (define sub-tree (if under-ellipsis?
                         (map derivation-subs-acc-subs-so-far sub-output)
                         (derivation-subs-acc-subs-so-far sub-output)))
    (define term (if under-ellipsis?
                     (map derivation-subs-acc-this-output sub-output)
                     (derivation-subs-acc-this-output sub-output)))
    (define mtchs (match-pattern compiled-pattern term))
    (cond
      [mtchs
       (for/fold ([outputs outputs]) ([mtch (in-list mtchs)])
         (define mtch-outputs (do-something (mtch-bindings mtch)
                                            (and old-maps
                                                 (if under-ellipsis?
                                                     (append (reverse sub-tree) old-maps)
                                                     (cons sub-tree old-maps)))))
         (if mtch-outputs
             (append mtch-outputs outputs)
             outputs))]
      [else outputs])))

(define (combine-where-results/flatten pat term result)
  (define mtchs (match-pattern pat term))
  (and mtchs
       (for/fold ([r '()]) ([m (in-list mtchs)])
         (let ([proc/f (result (mtch-bindings m))])
           (define s (and proc/f (proc/f)))
           (if s (append s r) r)))))

(define (combine-where/error-results pat term who lang result)
  (define (fail)
    (error who "where/error did not match\n  term: ~a"
           (term->string/error-message term)))
  (define mtchs (match-pattern pat term))
  (unless mtchs (fail))
  (define all-results
    (for/list ([mtch (in-list mtchs)])
      (result (mtch-bindings mtch))))
  (define all-results/no-f (filter values all-results))
  (when (null? all-results/no-f) (fail))
  (define fst ((car all-results/no-f)))
  (for ([nxt-proc (in-list all-results/no-f)])
    (define nxt (nxt-proc))
    (unless (alpha-equivalent? lang fst nxt)
      (error who
             "where/error matched multiple ways, but did not return alpha-equivalent? results\n  ~a\n  ~a"
             (term->string/error-message fst)
             (term->string/error-message nxt))))
  fst)

(define (repeated-premise-outputs inputs premise)
  (if (null? inputs)
      '(())
      (let ([output (premise (car inputs))])
        (if (null? output)
            '()
            (for*/list ([o (in-list output)]
                        [os (in-list (repeated-premise-outputs (cdr inputs) premise))])
              (cons o os))))))

(define (IO-judgment-form? jf)
  (and (runtime-judgment-form? jf)
       (or (equal? (runtime-judgment-form-mode jf) '(I O))
           (equal? (runtime-judgment-form-mode jf) '(O I)))))

(define not-in-cache (gensym))
(define (call-runtime-judgment-form a-runtime-judgment-form inputs derivation-init)
  (call-judgment-form (runtime-judgment-form-name a-runtime-judgment-form)
                      (runtime-judgment-form-proc a-runtime-judgment-form)
                      (runtime-judgment-form-mode a-runtime-judgment-form)
                      inputs
                      derivation-init
                      (runtime-judgment-form-cache a-runtime-judgment-form)
                      (runtime-judgment-form-lang a-runtime-judgment-form)
                      (runtime-judgment-form-original-contract-expression a-runtime-judgment-form)
                      (runtime-judgment-form-compiled-input-contract-pat a-runtime-judgment-form)
                      (runtime-judgment-form-compiled-output-contract-pat a-runtime-judgment-form)))

(define (call-judgment-form form-name form-proc mode input derivation-init
                            pair-of-boxed-caches ct-lang
                            original-contract-expression
                            compiled-input-contract-pat
                            compiled-output-contract-pat)

  (define boxed-cache (if (include-entire-derivation)
                          (car pair-of-boxed-caches)
                          (cdr pair-of-boxed-caches)))
  (when (caching-enabled?)
    (when (>= (hash-count (unbox boxed-cache)) cache-size)
      (set-box! boxed-cache (make-hash))))
  (define traced (current-traced-metafunctions))
  (define cache (unbox boxed-cache))
  (define in-cache? (and (caching-enabled?)
                         (let ([cache-value (hash-ref cache input not-in-cache)])
                           (not (eq? cache-value not-in-cache)))))
  (define p-a-e (print-as-expression))
  (define (form-proc/cache recur input derivation-init pair-of-boxed-caches
                           original-contract-expression
                           compiled-input-contract-pat
                           compiled-output-contract)

    (define (check-input-contract input)
      (when compiled-input-contract-pat
        (check-judgment-form-contract form-name input #f
                                      compiled-input-contract-pat
                                      original-contract-expression
                                      'I
                                      mode)))

    (define (check-output-contract input outputs)
      (when compiled-output-contract-pat
        (for ([output (in-list outputs)])
          (check-judgment-form-contract form-name input output
                                        compiled-output-contract-pat
                                        original-contract-expression
                                        'O
                                        mode))))

    (parameterize ([default-language ct-lang]
                   [print-as-expression p-a-e]
                   [binding-forms-opened? (if (caching-enabled?) (box #f) #f)])
      (check-input-contract input)
      (cond
        [(caching-enabled?)
         (define candidate (hash-ref cache input not-in-cache))
         (cond
           [(equal? candidate not-in-cache)
            (define output (form-proc recur input derivation-init pair-of-boxed-caches
                                      original-contract-expression
                                      compiled-input-contract-pat
                                      compiled-output-contract))
            (check-output-contract input output)
            (unless (unbox (binding-forms-opened?))
              (hash-set! cache input output))
            output]
           [else
            candidate])]
        [(not compiled-output-contract-pat)
         (form-proc recur input derivation-init pair-of-boxed-caches
                    original-contract-expression
                    compiled-input-contract-pat
                    compiled-output-contract)]
        [else
         (define output (form-proc recur input derivation-init pair-of-boxed-caches
                                   original-contract-expression
                                   compiled-input-contract-pat
                                   compiled-output-contract))
         (check-output-contract input output)
         output])))
  (define dwoos
    (if (or (eq? 'all traced) (memq form-name traced))
        (let ([outputs #f])
          (define spacers
            (cond
              [mode
               (for/fold ([s '()]) ([m mode])
                 (case m [(I) s] [(O) (cons '_ s)]))]
              [else
               '()]))
          (define (wrapped . _)
            (set! outputs (form-proc/cache form-proc/cache
                                           input
                                           derivation-init
                                           pair-of-boxed-caches
                                           original-contract-expression
                                           compiled-input-contract-pat
                                           compiled-output-contract-pat))
            (for/list ([output (in-list outputs)])
              (cons form-name (assemble mode input (derivation-with-output-only-output output)))))
          (define otr (current-trace-print-results))
          (define ot (current-trace-print-args))
          (if in-cache?
              (display "c")
              (display " "))
          (define (result-tracer name results level)
            (display " ")
            (otr name results level))
          (parameterize ([print-as-expression #f]
                         [current-trace-print-results
                          ;; this 'if' condition is a strange hack 
                          ;; that I don't understand the need for
                          (if (equal? (object-name otr) 'result-tracer)
                              otr
                              result-tracer)])
            (apply trace-call form-name wrapped (assemble mode input spacers)))
          outputs)
        (form-proc/cache form-proc/cache
                         input
                         derivation-init
                         pair-of-boxed-caches
                         original-contract-expression
                         compiled-input-contract-pat
                         compiled-output-contract-pat)))
  
  (define without-exact-duplicates-vec (apply vector (remove-duplicates dwoos)))
  (define ht (make-α-hash (compiled-lang-binding-table ct-lang)
                          (compiled-lang-literals ct-lang)
                          match-pattern))
  (for ([d (in-vector without-exact-duplicates-vec)]
        [i (in-naturals)])
    (define t (derivation-with-output-only-output d))
    (dict-set! ht t (cons i (dict-ref ht t '()))))

  (for ([(k v) (in-dict ht)])
    (define main (vector-ref without-exact-duplicates-vec (car v)))
    (for ([dup-i (in-list (cdr v))])
      (define dup-candidate (vector-ref without-exact-duplicates-vec dup-i))
      (when (or (not (include-entire-derivation))
                (and (equal? (derivation-with-output-only-name main)
                             (derivation-with-output-only-name dup-candidate))
                     (equal? (derivation-with-output-only-subs main)
                             (derivation-with-output-only-subs dup-candidate))))
        (vector-set! without-exact-duplicates-vec dup-i #f))))
  
  (for/list ([v (in-vector without-exact-duplicates-vec)]
             #:when v)
    (define subs (derivation-with-output-only-subs v))
    (define rulename (derivation-with-output-only-name v))
    (define this-output (derivation-with-output-only-output v))
    (derivation-subs-acc
     (and subs (derivation (cons form-name (assemble mode input this-output))
                           
                           ;; just drop the subderivations
                           ;; and the name when we know we
                           ;; won't be using them.
                           ;; this lets the remove-duplicates
                           ;; call just above do something
                           ;; and possibly avoid exponential blowup
                           
                           (if (include-entire-derivation)
                               rulename
                               "")
                           (if (include-entire-derivation)
                               (reverse subs)
                               '())))
     (and (include-jf-rulename) rulename)
     this-output)))

(define (verify-name-ok orig-name the-name)
  (unless (symbol? the-name)
    (error orig-name "expected a single name, got ~s" the-name)))

(define (verify-names-ok orig-name the-names len-counter)
  (unless (and (list? the-names)
               (andmap symbol? the-names))
    (error orig-name
           "expected a sequence of names, got ~s"
           the-names))
  (unless (= (length len-counter)
             (length the-names))
    (error orig-name
           "expected the length of the sequence of names to be ~a, got ~s"
           (length len-counter)
           the-names)))

(define current-traced-metafunctions (make-parameter '()))

(define-for-syntax (mode-keyword stx)
  (raise-syntax-error #f "keyword invalid outside of mode specification" stx))
(define-syntax I mode-keyword)
(define-syntax O mode-keyword)

(define-for-syntax (check-judgment-arity stx judgment)
  (syntax-case judgment ()
    [(form-name pat ...)
     (judgment-form-id? #'form-name)
     (unless (jf-is-relation? #'form-name)
       (let ([expected (mode->arity (judgment-form-mode (lookup-judgment-form-id #'form-name)))]
             [actual (length (syntax->list #'(pat ...)))])
         (unless (= actual expected)
           (raise-syntax-error 
            #f 
            (format "mode specifies a ~a relation but use supplied ~a term~a"
                    (case expected
                      [(0) "nullary"]
                      [(1) "unary"]
                      [(2) "binary"]
                      [else (format "~a-ary" expected)])
                    actual
                    (if (= actual 1) "" "s"))
            judgment))))]
    [(form-name pat ...)
     (raise-syntax-error #f "expected a judgment form name" stx #'form-name)]))

(define (substitute from to pat)
  (let recur ([p pat])
    (syntax-case p (side-condition)
      [(side-condition p c)
       #`(side-condition #,(recur #'p) c)]
      [(p ...)
       #`(#,@(map recur (syntax->list #'(p ...))))]
      [else
       (if (and (identifier? p) (bound-identifier=? p from))
           to
           p)])))

(define-for-syntax (definition-nts lang orig-stx syn-error-name)
  (unless (identifier? lang)
    (raise-syntax-error #f "expected an identifier in the language position" orig-stx lang))
  (language-id-nts lang syn-error-name))

(define-for-syntax (lhs-lws clauses)
  (with-syntax ([((lhs-for-lw _ ...) ...) clauses])
    (map (λ (x) (to-lw/proc (datum->syntax #f (cdr (syntax-e x)) x x)))
         (syntax->list #'(lhs-for-lw ...)))))

(define-syntax (define-judgment-form stx)
  (not-expression-context stx)
  (syntax-case stx ()
    [(def-form-id lang . body)
     (do-extended-judgment-form #'lang (syntax-e #'def-form-id) #'body #f stx #f #f)]))

(define-syntax (define-extended-judgment-form stx)
  (not-expression-context stx)
  (syntax-case stx ()
    [(def-form-id lang original-id . body)
     (begin
       (unless (judgment-form-id? #'original-id)
         (raise-syntax-error 'define-extended-judgment-form 
                             "expected a judgment form"
                             stx
                             #'original-id))
       (do-extended-judgment-form #'lang 'define-extended-judgment-form #'body #'original-id stx #f #f))]))

(define-syntax (define-overriding-judgment-form stx)
  (not-expression-context stx)
  (syntax-case stx ()
    [(def-form-id lang original-id . body)
     (begin
       (unless (judgment-form-id? #'original-id)
         (raise-syntax-error 'define-overriding-judgment-form
                             "expected a judgment form"
                             stx
                             #'original-id))
       (do-extended-judgment-form #'lang 'define-overriding-judgment-form #'body #'original-id stx #f #t))]))

(define-syntax (define-relation stx)
  (not-expression-context stx)
  (syntax-case stx ()
    [(def-form-id lang . body)
     (begin
       (unless (identifier? #'lang)
         (raise-syntax-error #f "expected an identifier in the language position" stx #'lang))
       (define-values (contract-name dom-ctcs pre-condition 
                                     codom-contracts codom-seps post-condition
                                     pats)
         (split-out-contract stx (syntax-e #'def-form-id) #'body #t))
       (with-syntax* ([((name trms ...) rest ...) (car pats)]
                      [(ctc-stx ...) (if dom-ctcs
                                         #`(#:contract (#,contract-name #,@dom-ctcs))
                                         #'())]
                      [(clauses ...) pats]
                      [new-body #`(ctc-stx ... clauses ...)])
         (do-extended-judgment-form #'lang (syntax-e #'def-form-id) #'new-body #f stx #t #f)))]))

;; if relation? is true, then the contract is a list of redex patterns
;; if relation? is false, then the contract is a single redex pattern
;;   (meant to match the actual argument as a sequence)
(define-for-syntax (split-out-contract stx syn-error-name rest relation?)
  ;; initial test determines if a contract is specified or not
  (cond
    [(pair? (syntax-e (car (syntax->list rest))))
     (values #f #f #f (list #'any) '() #f 
             (check-clauses stx syn-error-name (syntax->list rest) relation?))]
    [else
     (syntax-case rest ()
       [(id separator more ...)
        (identifier? #'id)
        (cond
          [relation?
           (let-values ([(contract clauses) 
                         (parse-relation-contract #'(separator more ...) syn-error-name stx)])
             (when (null? clauses)
               (raise-syntax-error syn-error-name 
                                   "expected clause definitions to follow domain contract"
                                   stx))
             (values #'id contract #f (list #'any) '() #f
                     (check-clauses stx syn-error-name clauses #t)))]
          [else
           (unless (eq? ': (syntax-e #'separator))
             (raise-syntax-error syn-error-name "expected a colon to follow the meta-function's name" stx #'separator))
           (let loop ([more (syntax->list #'(more ...))]
                      [dom-pats '()])
             (cond
               [(null? more)
                (raise-syntax-error syn-error-name "expected an ->" stx)]
               [(eq? (syntax-e (car more)) '->)
                (define-values (raw-clauses rev-codomains rev-codomain-separators
                                            pre-condition post-condition)
                  (let loop ([prev (car more)]
                             [more (cdr more)]
                             [codomains '()]
                             [codomain-separators '()])
                    (cond
                      [(null? more)
                       (raise-syntax-error syn-error-name
                                           "expected a range contract to follow" stx prev)]
                      [else
                       (define after-this-one (cdr more))
                       (cond
                         [(null? after-this-one)
                          (values null (cons (car more) codomains) codomain-separators #t #t)]
                         [else
                          (define kwd (cadr more))
                          (cond
                            [(member (syntax-e kwd) '(or ∨ ∪))
                             (loop kwd 
                                   (cddr more)
                                   (cons (car more) codomains)
                                   (cons (syntax-e kwd) codomain-separators))]
                            [(and (not relation?) 
                                  (or (equal? (syntax-e kwd) '#:pre)
                                      (equal? (syntax-e kwd) '#:post)))
                             (when (null? (cddr more)) 
                               (raise-syntax-error 
                                'define-metafunction 
                                (format "expected an expression to follow ~a keyword"
                                        (syntax-e kwd))
                                kwd))
                             (define pre #t)
                             (define post #t)
                             (define remainder (cdddr more))
                             (cond
                               [(equal? (syntax-e kwd) '#:pre)
                                (set! pre (caddr more))
                                (define without-pre (cdddr more))
                                (when (and (pair? without-pre)
                                           (equal? (syntax-e (car without-pre)) '#:post))
                                  (when (null? (cddr without-pre)) 
                                    (raise-syntax-error 
                                     'define-metafunction 
                                     "expected an expression to follow #:post keyword"
                                     kwd))
                                  (set! remainder (cddr without-pre))
                                  (set! post (cadr without-pre)))]
                               [(equal? (syntax-e kwd) '#:post)
                                (set! post (caddr more))])
                             (values remainder
                                     (cons (car more) codomains)
                                     codomain-separators
                                     pre 
                                     post)]
                            [else
                             (values (cdr more)
                                     (cons (car more) codomains)
                                     codomain-separators
                                     #t
                                     #t)])])])))
                (let ([doms (reverse dom-pats)]
                      [clauses (check-clauses stx syn-error-name raw-clauses relation?)])
                  (values #'id
                          doms
                          (if relation? #f pre-condition)
                          (reverse rev-codomains)
                          (reverse rev-codomain-separators)
                          (if relation? #f post-condition)
                          clauses))]
               [else
                (loop (cdr more) (cons (car more) dom-pats))]))])]
       [_
        (raise-syntax-error
         syn-error-name
         (format "expected the name of the ~a, followed by its contract (or no name and no contract)"
                 (if relation? "relation" "meta-function"))
         stx
         rest)])]))

(define-for-syntax (parse-relation-contract after-name syn-error-name orig-stx)
  (syntax-case after-name ()
    [(subset . rest-pieces)
     (unless (memq (syntax-e #'subset) '(⊂ ⊆))
       (raise-syntax-error syn-error-name
                           "expected ⊂ or ⊆ to follow the relation's name"
                           orig-stx #'subset))
     (let ([more (syntax->list #'rest-pieces)])
       (when (null? more)
         (raise-syntax-error syn-error-name 
                             (format "expected a sequence of patterns separated by x or × to follow ~a" 
                                     (syntax-e #'subset))
                             orig-stx
                             #'subset))
       (let loop ([more (cdr more)]
                  [arg-pats (list (car more))])
         (cond
           [(and (not (null? more)) (memq (syntax-e (car more)) '(x ×)))
            (when (null? (cdr more))
              (raise-syntax-error syn-error-name 
                                  (format "expected a pattern to follow ~a" (syntax-e (car more)))
                                  orig-stx (car more)))
            (loop (cddr more)
                  (cons (cadr more) arg-pats))]
           [else (values (reverse arg-pats) more)])))]))

(define-for-syntax (expand-to-id id stx)
  (syntax-case stx ()
    [(_ args ...)
     (with-syntax ([app (datum->syntax stx '#%app stx stx)])
       #`(app #,id args ...))]
    [x
     (identifier? #'x)
     id]))

(define-for-syntax (do-extended-judgment-form lang syn-err-name body orig stx is-relation? overriding-extension?)
  (define nts (definition-nts lang stx syn-err-name))
  (define orig-mode (and orig
                         (judgment-form-id? #'orig) ;; if this fails, there will be a syntax error later
                         (judgment-form-mode (lookup-judgment-form-id #'orig))))
  (define-values (judgment-form-name
                  dup-form-names
                  mode-stx mode
                  position-contracts invariant clauses rule-names)
    (parse-judgment-form-body body syn-err-name stx (identifier? orig) orig-mode is-relation?))
  (when (and (identifier? orig)
             (free-identifier=? judgment-form-name orig))
    (raise-syntax-error syn-err-name
                        "judgment form extension must extend a different judgment form, not itself"
                        stx
                        orig
                        (list judgment-form-name)))
  (define definitions
    (with-syntax ([judgment-form-runtime-proc
                   (syntax-property (forward-errortrace-prop
                                     judgment-form-name
                                     (syntax/loc judgment-form-name judgment-form-runtime-proc))
                                    'undefined-error-name
                                    (syntax-e judgment-form-name))])
      #`(begin
          #,@(if (identifier? orig) (list #`(void (λ () #,orig))) (list)) ;; for check syntax
          (define-syntax #,judgment-form-name 
            (judgment-form '#,judgment-form-name '#,mode #'judgment-form-runtime-proc
                           #'mk-judgment-form-procs #'#,lang #'jf-lws
                           '#,rule-names #'judgment-runtime-gen-clauses #'mk-judgment-gen-clauses #'jf-term-proc #,is-relation?
                           #'jf-cache #'the-runtime-judgment-form
                           #'original-contract-expression-id
                           #'compiled-input-contract-pat-id
                           #'compiled-output-contract-pat-id
                           (λ (stx) (expand-to-id #'the-runtime-judgment-form stx))))
          (define-values (mk-judgment-form-procs
                          mk-judgment-gen-clauses
                          original-contract-expression
                          judgment-form-input-contract
                          judgment-form-output-contract)
            (compile-judgment-form #,judgment-form-name #,mode #,lang #,clauses #,rule-names #,position-contracts #,invariant
                                   #,overriding-extension? #,is-relation?
                                   #,orig #,stx #,syn-err-name judgment-runtime-gen-clauses))
          (define judgment-form-runtime-proc (assemble-judgment-form-procs '#,mode (mk-judgment-form-procs #,lang)))
          (define jf-lws (compiled-judgment-form-lws #,clauses #,judgment-form-name #,stx))
          (define judgment-runtime-gen-clauses (mk-judgment-gen-clauses #,lang (λ () (judgment-runtime-gen-clauses))))
          (define jf-term-proc (make-jf-term-proc #,judgment-form-name #,syn-err-name #,lang #,nts #,mode))
          (define the-runtime-judgment-form
            (build-runtime-judgment-form #,orig
                                         '#,judgment-form-name
                                         judgment-form-runtime-proc
                                         '#,mode
                                         #,lang
                                         original-contract-expression
                                         judgment-form-input-contract
                                         judgment-form-output-contract
                                         '#,rule-names
                                         jf-lws
                                         #,is-relation?))
          (define jf-cache (runtime-judgment-form-cache the-runtime-judgment-form))
          (define original-contract-expression-id
            (runtime-judgment-form-original-contract-expression the-runtime-judgment-form))
          (define compiled-input-contract-pat-id
            (runtime-judgment-form-compiled-input-contract-pat the-runtime-judgment-form))
          (define compiled-output-contract-pat-id
            (runtime-judgment-form-compiled-output-contract-pat the-runtime-judgment-form)))))
  (syntax-property
   (values ;prune-syntax
    (if (eq? 'top-level (syntax-local-context))
        ; Introduce the names before using them, to allow
        ; judgment form definition at the top-level.
        #`(begin 
            (define-syntaxes (judgment-form-runtime-proc 
                              judgment-runtime-gen-clauses 
                              jf-term-proc jf-lws jf-cache
                              original-contract-expression-id
                              compiled-input-contract-pat-id
                              compiled-output-contract-pat-id
                              the-runtime-judgment-form)
              (values))
            #,definitions)
        definitions))
   'disappeared-use
   (map syntax-local-introduce dup-form-names)))

(define (assemble-judgment-form-procs mode form-procs)
  (cond
    [(number? mode)
     ;; modeless judgment-forms have a hash here not a proc
     ;; that gets called, so we don't need to do any
     ;; assembly
     form-procs]
    [else
     (define (judgment-form-proc recur input derivation-init pair-of-boxed-caches
                                 original-contract-expression
                                 compiled-input-contract-pat
                                 compiled-output-contract)
       (for/fold ([result '()])
                 ([form-proc-pair (in-list form-procs)])
         (append ((cdr form-proc-pair) recur input derivation-init pair-of-boxed-caches
                                       original-contract-expression
                                       compiled-input-contract-pat
                                       compiled-output-contract)
                 result)))
     judgment-form-proc]))

(define-for-syntax (jf-is-relation? jf-id)
  (judgment-form-relation? (lookup-judgment-form-id jf-id)))

(define-for-syntax (parse-judgment-form-body body syn-err-name full-stx extension?
                                             orig-mode is-relation?)
  (define-syntax-class pos-mode
    #:literals (I O)
    (pattern I)
    (pattern O))
  (define-syntax-class mode-spec
    #:description "mode specification"
    (pattern (_:id _:pos-mode ...)))
  (define-syntax-class contract-spec
    #:description "contract specification"
    (pattern (_:id _:expr ...)))
  (define (horizontal-line? id)
    (regexp-match? #rx"^-+$" (symbol->string (syntax-e id))))
  (define-syntax-class horizontal-line
    (pattern x:id #:when (horizontal-line? #'x)))
  (define-syntax-class name
    (pattern x #:when (and (not is-relation?)
                           (or (and (symbol? (syntax-e #'x))
                                    (not (horizontal-line? #'x))
                                    (not (eq? '... (syntax-e #'x))))
                               (string? (syntax-e #'x))))))

  (define (conc->arity-count conc)
    (syntax-parse conc
      [(jf . args)
       (define l (syntax->list #'args))
       (and l (length l))]
      [_ #f]))

  (define (parse-rules rules)
    (define-values (backward-rules backward-names length-of-first-conc)
      (for/fold ([parsed-rules '()]
                 [names '()]
                 [length-of-first-conc #f])
                ([rule (in-list rules)])
        (syntax-parse rule
          [(prem ... _:horizontal-line n:name conc)
           (values (cons #'(conc prem ...) parsed-rules)
                   (cons #'n names)
                   (or length-of-first-conc (conc->arity-count #'conc)))]
          [(prem ... _:horizontal-line conc)
           (values (cons #'(conc prem ...) parsed-rules)
                   (cons #f names)
                   (or length-of-first-conc (conc->arity-count #'conc)))]
          [(conc prem ... n:name)
           (values (cons #'(conc prem ...) parsed-rules)
                   (cons #'n names)
                   (or length-of-first-conc (conc->arity-count #'conc)))]
          [(conc prem ...)
           (values (cons rule parsed-rules)
                   (cons #f names)
                   (or length-of-first-conc (conc->arity-count #'conc)))])))
    (values (reverse backward-rules)
            (reverse backward-names)
            length-of-first-conc))

  (define-values (name/mode mode-stx name/contract contract invariant rules rule-names
                            length-of-first-conc)
    (syntax-parse body #:context full-stx
      [((~or (~seq #:mode ~! mode:mode-spec)
             (~seq #:contract ~! contract:contract-spec)
             (~seq #:inv ~! inv:expr))
        ...
        rule:expr ...)
       (let-values ([(name/mode mode)
                     (syntax-parse #'(mode ...)
                       [() (values #f #f)]
                       [((name the-mode ...)) (values #'name (car (syntax->list #'(mode ...))))]
                       [_ 
                        (raise-syntax-error 
                         #f
                         "expected definition to include at most one mode specification"
                         full-stx)])]
                    [(name/ctc ctc)
                     (syntax-parse #'(contract ...)
                       [() (values #f #f)]
                       [((name . contract)) (values #'name (syntax->list #'contract))]
                       [(_ . dups)
                        (raise-syntax-error 
                         syn-err-name "expected at most one contract specification"
                         #f #f (syntax->list #'dups))])]
                    [(invt)
                     (syntax-parse #'(inv ...)
                       [() #f]
                       [(invar) #'invar]
                       [(_ . dups)
                        (raise-syntax-error
                         syn-err-name "expected at most one invariant specification"
                         #f #f (syntax->list #'dups))])])
         (define-values (parsed-rules rule-names length-of-first-conc)
           (parse-rules (syntax->list #'(rule ...))))
         (values name/mode mode name/ctc ctc invt parsed-rules rule-names
                 length-of-first-conc))]))

  (define mode
    (cond
      [is-relation? #f]
      [mode-stx
       (cdr (syntax->datum mode-stx))]
      [orig-mode orig-mode]
      [else length-of-first-conc]))

  (unless is-relation?
    (unless mode
      (raise-syntax-error syn-err-name
                          (format "internal error: could not find mode: ~s ~s ~s"
                                  mode-stx
                                  orig-mode
                                  length-of-first-conc)
                          full-stx)))
  (check-clauses full-stx syn-err-name rules #t)
  (check-dup-rule-names full-stx syn-err-name rule-names)
  (unless is-relation? (check-arity-consistency syn-err-name mode contract full-stx))
  (define-values (form-name dup-names)
    (syntax-case rules ()
      [() 
       (not extension?)
       (raise-syntax-error #f "expected at least one rule" full-stx)]
      [_ (defined-name (list name/mode name/contract) rules full-stx)]))
  (define string-rule-names
    (for/list ([name (in-list rule-names)])
      (cond
        [(not name) name]
        [(symbol? (syntax-e name))
         (symbol->string (syntax-e name))]
        [else (syntax-e name)])))
  (values form-name dup-names mode-stx mode contract invariant rules string-rule-names))

;; names : (listof (or/c #f syntax[string]))
(define-for-syntax (check-dup-rule-names full-stx syn-err-name names)
  (define tab (make-hash))
  (for ([name (in-list names)])
    (when (syntax? name)
      (define k (if (symbol? (syntax-e name))
                    (symbol->string (syntax-e name))
                    (syntax-e name)))
      (hash-set! tab k (cons name (hash-ref tab k '())))))
  (for ([(k names) (in-hash tab)])
    (unless (= 1 (length names))
      (raise-syntax-error syn-err-name
                          "duplicate rule names"
                          (car names) #f (cdr names)))))
                          
(define-for-syntax (check-arity-consistency syn-err-name mode contracts full-def)
  (when mode
    (define arity (mode->arity mode))
    (when contracts
      (unless (= arity (length contracts))
        (raise-syntax-error
         syn-err-name
         "mode and contract specify different numbers of positions" full-def)))))

(define-for-syntax (defined-name declared-names clauses orig-stx)
  (with-syntax ([(((used-names _ ...) _ ...) ...) clauses])
    (define-values (the-name other-names)
      (let ([present (filter values declared-names)])
        (if (null? present)
            (values (car (syntax->list #'(used-names ...)))
                    (cdr (syntax->list #'(used-names ...))))
            (values (car present) 
                    (append (cdr present) (syntax->list #'(used-names ...)))))))
    (let loop ([others other-names])
      (cond
        [(null? others) (values the-name other-names)]
        [else
         (unless (eq? (syntax-e the-name) (syntax-e (car others)))
           (raise-syntax-error 
            #f
            "expected the same name in both positions"
            orig-stx
            the-name (list (car others))))
         (loop (cdr others))]))))

(define-syntax (make-jf-term-proc stx)
  (syntax-parse stx
    [(_  jdg-name syn-err-name lang nts _mode)
     (define mode (syntax->datum #'_mode))
     (cond
       [(number? mode)
        #'(λ (_)
            (error 'syn-err-name
                   "modeless judgment forms cannot be used in term"))]
       [(and mode (member 'O mode))
        #'(λ (_)
            (error 'syn-err-name
                   "judgment forms with output mode positions cannot be used in term"))]
       [else
        (with-syntax* ([(binding ...) (if mode (generate-temporaries mode) '())]
                       [(input) (generate-temporaries (list #'input))])
          (define-values (body-stx compiled-pattern-identifiers patterns-to-compile)
            (bind-withs (syntax-e #'syn-err-name) '() #'lang (syntax->datum #'nts) #'lang
                        (if (jf-is-relation? #'jdg-name)
                            (list #'(jdg-name (unquote-splicing input)))
                            (list #'(jdg-name (unquote binding) ...)))
                        #`(list #t)
                        '()
                        '()
                        #f
                        #'null))
          (with-syntax ([(compiled-pattern-identifier ...) compiled-pattern-identifiers]
                        [(pattern-to-compile ...) patterns-to-compile])
            #`(let ([compiled-pattern-identifier (compile-pattern lang pattern-to-compile #t)] ...)
                #,(if (jf-is-relation? #'jdg-name)
                      #`(λ (input)
                          (not (null? #,body-stx)))
                      #`(λ (input)
                          (check-length input 'jdg-name #,(length mode))
                          (let-values ([(binding ...) (apply values input)])
                            (not (null? #,body-stx))))))))])]))

(define (check-length input name input-size)
  (unless (= (length input) input-size)
    (error name "judgment form expects ~a inputs, got ~a"
           input-size (length input))))

(define-syntax (judgment-holds/derivation stx)
  (syntax-case stx ()
    [(_ stx-name jf-id expr)
     (identifier? #'jf-id)
     (let ()
       (unless (judgment-form-id? #'jf-id)
         (raise-syntax-error (syntax-e #'stx-name)
                             "expected a modeless judgment form when the name is used alone"
                             #'jf-id))
       (define judgment-form-record (lookup-judgment-form-id #'jf-id))
       (unless (number? (judgment-form-mode judgment-form-record))
         (raise-syntax-error (syntax-e #'stx-name)
                             "expected a modeless judgment form when the name is used alone"
                             #'jf-id))
       #`(call-modeless-judgment-form #,(judgment-form-lang judgment-form-record)
                                      'jf-id
                                      #,(judgment-form-proc judgment-form-record)
                                      #,(judgment-form-compiled-input-contract-pat-id
                                         judgment-form-record)
                                      expr
                                      #f))]
    [(_ stx-name derivation? judgment)
     (forward-errortrace-prop
      stx
      (quasisyntax/loc stx
        (not (null? #,(forward-errortrace-prop
                       stx
                       (syntax/loc stx (judgment-holds/derivation stx-name derivation? judgment #t)))))))]
         
    [(_ stx-name derivation? (form-name . pats) tmpl)
     (judgment-form-id? #'form-name)
     (let* ([syn-err-name (syntax-e #'stx-name)]
            [judgment-form-record (lookup-judgment-form-id #'form-name)]
            [lang (judgment-form-lang judgment-form-record)]
            [nts (definition-nts lang stx syn-err-name)]
            [judgment (syntax-case stx () [(_ _ _ judgment _) #'judgment])]
            [derivation? (syntax-e #'derivation?)]
            [id-or-not (if derivation?
                           (car (generate-temporaries '(jf-derivation-lst)))
                           #f)])
       (when (number? (judgment-form-mode judgment-form-record))
         (raise-syntax-error (syntax-e #'stx-name)
                             "modeless judgment forms must supply only the name of the judgment form"
                             (list-ref (syntax->list stx) 3)))
       (define-values (main-stx compiled-pattern-identifiers patterns-to-compile)
         (bind-withs syn-err-name '() lang nts lang
                     (list judgment)
                     (if derivation?
                         id-or-not
                         #`(list (term #,#'tmpl #:lang #,lang)))
                     '()
                     '()
                     #f
                     id-or-not))
       
       (check-judgment-arity stx judgment)
       (with-syntax ([(compiled-pattern-identifier ...) compiled-pattern-identifiers]
                     [(pattern-to-compile ...) patterns-to-compile])
         (syntax-property
          #`(parameterize ([include-entire-derivation #,derivation?])

              ;; make sure we get the right undefined error (if there is one)
              #,(let ([s (judgment-form-proc judgment-form-record)])
                  (datum->syntax s (syntax-e s) #'form-name #'form-name))
              
              (let ([compiled-pattern-identifier (compile-pattern #,lang pattern-to-compile #t)] ...)
                #,(if id-or-not
                      #`(let ([#,id-or-not '()])
                          #,main-stx)
                      #`(sort-as-strings #,main-stx))))
          'disappeared-use
          (syntax-local-introduce #'form-name))))]
    [(_ stx-name derivation? (not-form-name . _) . _)
     (not (judgment-form-id? #'form-name))
     (raise-syntax-error (syntax-e #'stx-name) "expected a judgment form name" #'not-form-name)]
    [(_ stx-name . whatever)
     (raise-syntax-error (syntax-e #'stx-name)
                         "bad syntax"
                         stx)]))

(define (sort-as-strings l) (sort l string<? #:key (λ (x) (format "~s" x))))

(define-syntax (judgment-holds stx)
  (syntax-parse stx
    [(_ jf-id e:expr)
     #:when (identifier? #'jf-id)
     (define arg (stx-car (stx-cdr stx)))
     #`(#%expression
        #,(forward-errortrace-prop
           arg
           (quasisyntax/loc arg (judgment-holds/derivation judgment-holds #,arg e))))]
    [(_ (jf-id . args))
     (define arg (stx-car (stx-cdr stx)))
     #`(#%expression
        #,(forward-errortrace-prop
           arg
           (quasisyntax/loc arg (judgment-holds/derivation judgment-holds #f #,arg))))]
    [(_ (jf-id . args) trm)
     (define arg (stx-car (stx-cdr stx)))
     #`(#%expression
        #,(forward-errortrace-prop
           arg
           (quasisyntax/loc arg (judgment-holds/derivation judgment-holds #f #,arg trm))))]))

(define-syntax (build-derivations stx)
  (syntax-case stx ()
    [(_  jf-expr)
     #'(#%expression (judgment-holds/derivation build-derivations #t jf-expr any))]))

(define-for-syntax (ensure-valid-extension stx orig name mode syn-error-name)
  (when (identifier? orig)
    (define orig-mode (judgment-form-mode (lookup-judgment-form-id orig)))
    (unless (equal? mode orig-mode)
      (cond
        [(and orig-mode (not mode))
         (raise-syntax-error syn-error-name
                             "cannot extend a judgment-form with a relation"
                             stx
                             orig)]
        [(and mode (not orig-mode))
         (raise-syntax-error syn-error-name
                             "cannot extend a relation with a judgment-form"
                             stx
                             orig)]
        [(and (number? orig-mode)
              (not (number? mode)))
         (raise-syntax-error
          syn-error-name
          "cannot extend a judgment-form with no mode with a judgment-form that has a mode"
          stx
          orig)]
        [(and (not (number? orig-mode))
              (number? mode))
         (raise-syntax-error
          syn-error-name
          "cannot extend a judgment-form with a mode with a judgment-form that has no mode"
          stx
          orig)]
        [(and orig-mode mode)
         (raise-syntax-error syn-error-name
                             (format
                              (string-append
                               "mode for extended judgment form does not match original mode;\n"
                               "  original  mode: ~s\n"
                               "  extension mode: ~s")
                              `(,(syntax-e orig) ,@orig-mode)
                              `(,(syntax-e name) ,@mode))
                             stx
                             orig)]
        [else (error syn-error-name "should not happen")]))))

(define-for-syntax (do-compile-judgment-form-proc name mode clauses rule-names
                                                  nts orig
                                                  overriding-extension? is-relation?
                                                  lang syn-error-name)
  
  (with-syntax ([(init-jf-derivation-id) (generate-temporaries '(init-jf-derivation-id))])
    
    (define (compile-clause clause clause-name)
      (syntax-case clause ()
        [((_ . conc-pats) . prems)
         (let-values ([(input-pats output-pats) (split-by-mode (syntax->list #'conc-pats) mode)])
           (with-syntax ([(lhs-syncheck-exp lhs (names ...) (names/ellipses ...))
                          (if is-relation?
                              (rewrite-side-conditions/check-errs
                               lang syn-error-name #t
                               (if (syntax? input-pats)
                                   (syntax->list input-pats)
                                   input-pats))
                              (rewrite-side-conditions/check-errs/list
                               lang syn-error-name #t
                               (if (syntax? input-pats)
                                   (syntax->list input-pats)
                                   input-pats)))]
                         [(jf-derivation-id) (generate-temporaries '(jf-derivation-id))])
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
                             (syntax->list #'prems) 
                             #`(list (derivation-with-output-only
                                      (term (#,@output-pats) #:lang #,lang)
                                      #,clause-name
                                      jf-derivation-id))
                             (syntax->list #'(names ...))
                             (syntax->list #'(names/ellipses ...))
                             #f
                             #'jf-derivation-id)))
             (with-syntax ([(compiled-lhs) (generate-temporaries '(compiled-lhs))]
                           [(compiled-pattern-identifier ...) compiled-pattern-identifiers]
                           [(pattern-to-compile ...) patterns-to-compile])
               
               #`(;; pieces of a 'let' expression to be combined: first some bindings
                  ([compiled-pattern-identifier (compile-pattern lang pattern-to-compile #t)] ...
                   [compiled-lhs (compile-pattern lang `lhs #t)])
                  ;; and then the body of the let, but expected to be behind a (λ (input) ...).
                  (let ([jf-derivation-id init-jf-derivation-id])
                    (begin
                      lhs-syncheck-exp
                      (combine-judgment-rhses
                       compiled-lhs
                       input
                       (λ (bnds)
                         #,(bind-pattern-names 'judgment-form
                                               #'(names/ellipses ...)
                                               #'((lookup-binding bnds 'names) ...)
                                               body)))))))))]))
    
    (with-syntax ([(((clause-proc-binding ...) clause-proc-body) ...) (map compile-clause clauses rule-names)]
                  [(rule-names ...) rule-names])
      (with-syntax ([(new-rules-code ...)
                     #'((cons rule-names
                              (λ (recur input init-jf-derivation-id recur-cache
                                   original-contract-expression
                                   compiled-input-contract-pat
                                   compiled-output-contract-pat)
                                clause-proc-body)) ...)])
      (if (identifier? orig)
          (with-syntax ([orig-mks (judgment-form-mk-procs (lookup-judgment-form-id orig))])
            #`(λ (lang)
                (let (clause-proc-binding ... ...)
                  (let ([prev (orig-mks lang)])
                    #,(if overriding-extension?
                          #'(add/override-clauses (list new-rules-code ...) prev)
                          #'(list* new-rules-code ... prev))))))
          #`(λ (lang)
              (let (clause-proc-binding ... ...)
                (list new-rules-code ...))))))))

(define (add/override-clauses new-clauses old-clauses)
  (define replacements
    (for/hash ([clause (in-list new-clauses)]
               #:when (car clause))
      (values (car clause) #t)))
  (append new-clauses
          (for/list ([old-clause (in-list old-clauses)]
                     #:unless (hash-ref replacements (car old-clause) #f))
            old-clause)))

(define (combine-judgment-rhses compiled-lhs input rhs)
  (define mtchs (match-pattern compiled-lhs input))
  (cond
    [mtchs
     (define output-table (make-hash))
     (for ([m (in-list mtchs)])
       (define os (rhs (mtch-bindings m)))
       (when os
         (for ([x (in-list os)])
           (hash-set! output-table x #t))))
     (hash-map output-table (λ (k v) k))]
    [else '()]))

(define-for-syntax (do-compile-judgment-form-lws clauses jf-name-stx full-def)
  (syntax-case clauses ()
    [(((_ . conc-body) prems ...) ...)
     (with-syntax ([((rhss ...) (sc/ws ...)) (if (jf-is-relation? jf-name-stx)
                                                 (with-syntax ([(((rhses ...) (where/sc ...)) ...)
                                                                (relation-split-out-rhs #'((prems ...) ...) full-def)])
                                                   #'(((rhses ...) ...) ((where/sc ...) ...)))
                                                 (let ([rev-premss
                                                        ; for consistency with metafunction extras
                                                        (for/list ([prems (syntax->list #'((prems ...) ...))])
                                                          (reverse (syntax->list prems)))]
                                                       [no-rhss (map (λ (_) '()) clauses)])
                                                   (list no-rhss rev-premss)))])
       #`(generate-lws #t (conc-body ...) #,(lhs-lws clauses) (sc/ws ...) (rhss ...) #f))]))

(define-for-syntax (relation-split-out-rhs raw-rhsss orig-stx)
  (for/list ([rhss (in-list (syntax->list raw-rhsss))])
    (define rhses '())
    (define sc/wheres '())
    (for ([rhs (in-list (syntax->list rhss))])
      (define (found-one) 
        (set! sc/wheres (cons rhs sc/wheres)))
      (syntax-case rhs (side-condition side-condition/hidden where where/hidden judgment-holds)
        [(side-condition . stuff) (found-one)]
        [(side-condition/hidden . stuff) (found-one)]
        [(where . stuff) (found-one)]
        [(where/hidden . stuff) (found-one)]
        [(judgment-holds . stuff) (found-one)]
        [_ 
         (cond
           [(null? sc/wheres)
            (set! rhses (cons rhs rhses))]
           [else
            (raise-syntax-error 'define-relation
                                (format "found a '~a' clause not at the end; followed by a normal, right-hand side clause"
                                        (syntax-e (car (syntax-e (car sc/wheres)))))
                                (last sc/wheres)
                                #f
                                (list  rhs))])]))
    (list (reverse rhses)
          (reverse sc/wheres))))

(define (check-judgment-form-contract form-name input-term output-term+trees
                                      contracts orig-ctcs input-or-output-contract modes)
  (define o-term (and (equal? input-or-output-contract 'O)
                      (derivation-with-output-only-output output-term+trees)))
  (define description
    (case input-or-output-contract
      [(I) "input"]
      [(O) "output"]))
  (when contracts
    (case input-or-output-contract
      [(I)
       (cond
         [modes
          (unless (match-pattern contracts input-term)
            (redex-error form-name
                         (string-append "judgment input values do not match its contract;\n"
                                        " (unknown output values indicated by _)\n"
                                        "  contract: ~s\n"
                                        "  values:   ~s")
                         (cons form-name orig-ctcs)
                         (cons form-name (assemble modes input-term (build-list (length modes)
                                                                                (λ (_) '_))))))]
         [else
          (unless (match-pattern contracts input-term)
            (redex-error form-name
                         (string-append "relation values do not match the contract;\n"
                                        "  contract: ~s\n"
                                        "  values:   ~s")
                         (cons form-name orig-ctcs)
                         (cons form-name input-term)))])]
      [(O)
       (define io-term (assemble modes input-term o-term))
       (unless (match-pattern contracts io-term)
         (redex-error form-name
                      (string-append
                       "judgment values do not match its contract (or invariant);\n"
                       "  contract: ~s\n"
                       "  values:   ~s")
                      (cons form-name orig-ctcs) (cons form-name io-term)))])))

(define-for-syntax (mode-check this-judgment-form this-mode clauses nts syn-err-name orig-stx)
  (define ((check-template bound-anywhere) temp bound)
    (let check ([t temp])
      (syntax-case t (unquote)
        [x
         (identifier? #'x)
         (unless (cond [(free-id-table-ref bound-anywhere #'x #f)
                        (free-id-table-ref bound #'x #f)]
                       [(id-binds? nts #t #'x)
                        (term-fn? (syntax-local-value #'x (λ () #f)))]
                       [else #t])
           (raise-syntax-error syn-err-name "unbound pattern variable" #'x))]
        [(unquote e) (void)]
        [(u ...)
         (for-each check (syntax->list #'(u ...)))]
        [_ (void)])))
  (define ((bind kind) pat bound)
    (define-values (ids _)
      (extract-names nts syn-err-name #t pat kind))
    (for/fold ([b bound]) ([x ids])
      (free-id-table-set b x #t)))
  (define (split-body conc? judgment)
    (syntax-parse judgment
      [(form-name . body)
       (define their-mode
         (judgment-form-mode
          (lookup-judgment-form-id #'form-name)))
       (when (list? this-mode)
         (unless (or (not their-mode) (list? their-mode))
           (raise-syntax-error
            syn-err-name
            (format (string-append
                     "judgment forms with a mode cannot use judgment forms"
                     " without a mode\n  with mode: ~a\n  without mode: ~a")
                    this-judgment-form
                    (syntax-e #'form-name))
            judgment)))
       (if (number? their-mode)
           (if conc?
               (values (syntax->list #'body) '())
               (values '() (syntax->list #'body)))
           (split-by-mode (syntax->list #'body) their-mode))]))
  (define (drop-ellipses prems)
    (syntax-case prems ()
      [() '()]
      [(prem maybe-ellipsis . remaining)
       (ellipsis? #'maybe-ellipsis)
       (syntax-case #'prem ()
         [(form-name . _)
          (judgment-form-id? #'form-name)
          (cons #'prem (drop-ellipses #'remaining))]
         [_ (raise-syntax-error syn-err-name "ellipses must follow judgment form uses" #'maybe-ellipsis)])]
      [(prem . remaining)
       (cons #'prem (drop-ellipses #'remaining))]))
  (define (fold-clause pat-pos tmpl-pos acc-init clause)
    (define (raise-length-error name source expected actual)
      (raise-syntax-error syn-err-name
                          (format "~a expected ~a part(s), but got ~a"
                                  (syntax-e name)
                                  expected
                                  (length (syntax->list actual)))
                          source))
    (syntax-case clause ()
      [(conc . prems)
       (let-values ([(conc-in conc-out) (split-body #t #'conc)])
         (check-judgment-arity orig-stx #'conc)
         (define acc-out
           (for/fold ([acc (foldl pat-pos acc-init conc-in)])
                     ([prem (in-list (drop-ellipses #'prems))])
             (syntax-case prem ()
               [(-where pat tmpl)
                (where-keyword? #'-where)
                (begin
                  (tmpl-pos #'tmpl acc)
                  (pat-pos #'pat acc))]
               [(-where e ...)
                (where-keyword? #'-where)
                (raise-length-error #'-where prem 2 #'(e ...))]
               [(-side-condition tmpl)
                (side-condition-keyword? #'-side-condition)
                (begin (tmpl-pos #'tmpl acc)
                       acc)]
               [(-side-condition e ...)
                (side-condition-keyword? #'-side-condition)
                (raise-length-error #'-side-condition prem 1 #'(e ...))]
               [(form-name . _)
                (if (judgment-form-id? #'form-name)
                    (let-values ([(prem-in prem-out) (split-body #f prem)])
                      (check-judgment-arity orig-stx prem)
                      (for ([pos (in-list prem-in)]) (tmpl-pos pos acc))
                      (foldl pat-pos acc prem-out))
                    (raise-syntax-error syn-err-name "expected judgment form name" #'form-name))]
               [_ (raise-syntax-error syn-err-name "malformed premise" prem)])))
         (for ([pos (in-list conc-out)]) (tmpl-pos pos acc-out))
         acc-out)]))
  (for ([clause (in-list clauses)])
    (define do-tmpl
      (check-template
       (fold-clause (bind 'rhs-only) void (make-immutable-free-id-table) clause)))
    (fold-clause (bind 'rhs-only) do-tmpl (make-immutable-free-id-table) clause)))

(define-syntax (generate-lws stx)
  (syntax-case stx ()
    [(_ relation? seq-of-lhs seq-of-lhs-for-lw seq-of-tl-side-cond/binds seq-of-rhs 
        side-condition-unquoted?)
     (with-syntax
         ([(rhs/lw ...) 
           (syntax-case #'relation? ()
             [#t (map (λ (x) #`(list #,@(map to-lw/proc (syntax->list x))))
                      (syntax->list #'seq-of-rhs))]
             [#f (map to-lw/proc (syntax->list #'seq-of-rhs))])]
          [(((bind-id/lw . bind-pat/lw) ...) ...)
           ;; Also for pict, extract pattern bindings
           (map name-pattern-lws (syntax->list #'seq-of-lhs))]
          [((where/sc/lw ...) ...)
           ;; Also for pict, extract where bindings
           (for/list ([hm (in-list (syntax->list #'seq-of-tl-side-cond/binds))])
             (define the-extras (visible-extras hm))
             (for/list ([lst (in-list the-extras)]
                        [next (if (null? the-extras)
                                  '()
                                  (append (cdr the-extras) (list #f)))])
               (syntax-case next (or)
                 [or (to-lw/proc lst)]
                 [else
                  (syntax-case lst (unquote side-condition or)
                    [(form-name . _)
                     (judgment-form-id? #'form-name)
                     #`(make-metafunc-extra-side-cond #,(to-lw/proc lst))]
                    [(form-name . _)
                     (judgment-form-id? #'form-name)
                     #`(make-metafunc-extra-side-cond #,(to-lw/proc lst))]
                    [(where pat (unquote (f _ _)))
                     (and (or (identifier? #'pat)
                              (let ([l (syntax->list #'pat)])
                                (and l (andmap identifier? (syntax->list #'pat)))))
                          (and (identifier? #'f)
                               (or (free-identifier=? #'f #'variable-not-in)
                                   (free-identifier=? #'f #'variables-not-in))))
                     (with-syntax ([(ids ...)
                                    (map to-lw/proc
                                         (if (identifier? #'pat)
                                             (list #'pat)
                                             (syntax->list #'pat)))])
                       #`(make-metafunc-extra-fresh
                          (list ids ...)))]
                    [(-where pat exp)
                     (where-keyword? #'-where)
                     #`(make-metafunc-extra-where
                        #,(to-lw/proc #'pat) #,(to-lw/proc #'exp))]
                    [(side-condition x)
                     #`(make-metafunc-extra-side-cond
                        #,(if (syntax-e #'side-condition-unquoted?)
                              (to-lw/uq/proc #'x)
                              (to-lw/proc #'x)))]
                    [or ''or]
                    [(clause-name name)
                     #''(clause-name name)]
                    [maybe-ellipsis
                     (ellipsis? #'maybe-ellipsis)
                     (to-lw/proc #'maybe-ellipsis)])])))]
          [(((where-bind-id/lw . where-bind-pat/lw) ...) ...)
           (for/list ([clauses (in-list (syntax->list #'seq-of-tl-side-cond/binds))])
             (for/fold ([binds '()]) ([clause (visible-extras clauses)])
               (syntax-parse clause #:datum-literals (where)
                 [(form-name . pieces)
                  #:when (judgment-form-id? #'form-name)
                  (define mode (judgment-form-mode (lookup-judgment-form-id #'form-name)))
                  (define-values (_ outs)
                    (if (number? mode)
                        (values #f (syntax->list #'pieces))
                        (split-by-mode (syntax->list #'pieces) mode)))
                  (for/fold ([binds binds]) ([out (in-list outs)])
                    (append (name-pattern-lws out) binds))]
                 [(where lhs rhs) (append (name-pattern-lws #'lhs) binds)]
                 [_ binds])))]
          [(((rhs-bind-id/lw . rhs-bind-pat/lw/uq) ...) ...)
           ;; Also for pict, extract pattern bindings
           (map (λ (x) (map (λ (x) (cons (to-lw/proc (car x)) (to-lw/uq/proc (cdr x))))
                            (extract-term-let-binds x)))
                (syntax->list #'seq-of-rhs))]
          
          [(x-lhs-for-lw ...) #'seq-of-lhs-for-lw])
       #'(list (list x-lhs-for-lw
                     (list (make-metafunc-extra-where bind-id/lw bind-pat/lw) ...
                           (make-metafunc-extra-where where-bind-id/lw where-bind-pat/lw) ...
                           (make-metafunc-extra-where rhs-bind-id/lw rhs-bind-pat/lw/uq) ...
                           where/sc/lw ...)
                     rhs/lw)
               ...))]))

(define-for-syntax (visible-extras extras)
  (for/fold ([visible empty]) ([extra (syntax->list extras)])
    (syntax-case extra (where/hidden
                        side-condition/hidden
                        judgment-holds)
      [(where/hidden pat exp) visible]
      [(side-condition/hidden x) visible]
      [(judgment-holds judgment)
       (cons #'judgment visible)]
      [_ (cons extra visible)])))

(define-syntax (compile-judgment-form stx)
  (syntax-case stx ()
    [(_ judgment-form-name mode-arg lang raw-clauses rule-names ctcs invt
        overriding-extension? is-relation? orig full-def syn-err-name judgment-form-runtime-gen-clauses)
     (let ([nts (definition-nts #'lang #'full-def (syntax-e #'syn-err-name))]
           [rule-names (syntax->datum #'rule-names)]
           [syn-err-name (syntax-e #'syn-err-name)]
           [clauses (if (jf-is-relation? #'judgment-form-name)
                        (fix-relation-clauses (syntax-e #'judgment-form-name) (syntax->list #'raw-clauses))
                        (syntax->list #'raw-clauses))]
           [overriding-extension? (syntax-e #'overriding-extension?)]
           [is-relation? (syntax-e #'is-relation?)]
           [mode (syntax->datum #'mode-arg)])
       (unless (jf-is-relation? #'judgment-form-name)
         (mode-check (syntax-e #'judgment-form-name) mode clauses nts syn-err-name stx))
       (define-values (i-ctc-syncheck-expr i-ctc contract-original-expr)
         (syntax-parse #'ctcs
           [#f (values #'(void) #f #f)]
           [(p ...)
            (define-values (i-ctcs _ignore)
              (if (number? mode)
                  (values (syntax->list #'(p ...)) '())
                  (split-by-mode (syntax->list #'(p ...)) mode)))
            (with-syntax* ([(i-ctcs ...) i-ctcs]
                           [(syncheck i-ctc-pat (names ...) (names/ellipses ...))
                            (rewrite-side-conditions/check-errs
                             #'lang syn-err-name #f #'(i-ctcs ...))])
              (values #'syncheck
                      #'i-ctc-pat
                      #'(p ...)))]))
       (define-values (ctc-syncheck-expr ctc)
         (cond 
           [(not (or (syntax-e #'ctcs) 
                     (syntax-e #'invt)))
            (values #'(void) #f)]
           [else
            (define ctc-stx ((if (syntax-e #'invt)
                                 (λ (ctc-stx)
                                   #`(side-condition #,ctc-stx (term invt)))
                                 values)
                             (if (syntax-e #'ctcs)
                                 #'ctcs
                                 #'any)))
            (with-syntax ([(syncheck ctc-pat (names ...) (names/ellipses ...))
                           (rewrite-side-conditions/check-errs #'lang syn-err-name #f ctc-stx)])
              (values #'syncheck #'ctc-pat))]))

       (ensure-valid-extension #'full-def #'orig  #'judgment-form-name mode syn-err-name)

       (define proc-stx
         (cond
           [(number? mode)
            (do-compile-modeless-judgment-form-proc #'judgment-form-name
                                                    mode
                                                    clauses
                                                    rule-names
                                                    nts
                                                    #'orig
                                                    #'lang
                                                    syn-err-name
                                                    bind-withs)]
           [else
            (do-compile-judgment-form-proc #'judgment-form-name
                                           mode
                                           clauses
                                           rule-names
                                           nts
                                           #'orig
                                           overriding-extension?
                                           is-relation?
                                           #'lang
                                           syn-err-name)]))
       (define gen-stx (with-syntax* ([(comp-clauses ...) 
                                       (map (λ (c) (compile-gen-clause c mode syn-err-name 
                                                                       #'judgment-form-name #'lang)) 
                                            clauses)])
                                     (if (identifier? #'orig)
                                         (with-syntax ([prev-mk (judgment-form-mk-gen-clauses (lookup-judgment-form-id #'orig))])
                                           #`(λ (effective-lang judgment-form-runtime-gen-clauses)
                                               (define mk-prev-clauses (prev-mk effective-lang judgment-form-runtime-gen-clauses))
                                               (λ ()
                                                 (append
                                                  (mk-prev-clauses)
                                                  #,(check-pats
                                                     #'(list comp-clauses ...))))))
                                         #`(λ (effective-lang judgment-form-runtime-gen-clauses)
                                             (λ ()
                                               #,(check-pats
                                                  #'(list comp-clauses ...)))))))
       #`(begin #,i-ctc-syncheck-expr #,ctc-syncheck-expr
                (values #,proc-stx
                        #,gen-stx
                        #,(if i-ctc
                              #``#,contract-original-expr
                              #`#f)
                        #,(and i-ctc #``#,i-ctc)
                        #,(and ctc #``#,ctc))))]))

(define-for-syntax (fix-relation-clauses name raw-clauses)
  (map (λ (clause-stx)
         (define (fix-rule rule-stx)
           (syntax-case rule-stx (judgment-holds)
             [(rule-name rest ...)
              (and (identifier? #'rule-name)
                   (judgment-form-id? #'rule-name))
              rule-stx]
             [(judgment-holds (rule-name rest ...))
              (and (identifier? #'rule-name)
                   (judgment-form-id? #'rule-name))
              (stx-car (stx-cdr rule-stx))]
             [rule
              #'(side-condition rule)]))
         (let loop ([c-stx clause-stx]
                    [new-c-stx '()]
                    [extra-stx '()])
           (syntax-case c-stx ()
             [()
              (let ([c-rev (reverse new-c-stx)])
                (with-syntax ([(cls ...)
                               (cons (car c-rev)
                                     (append (reverse extra-stx)
                                             (cdr c-rev)))])
                  #'(cls ...)))]
             [((where ext-rest ...) rest ...)
              (where-keyword? #'where)
              (loop #'(rest ...)
                    new-c-stx
                    (cons #'(where ext-rest ...) extra-stx))]
             [((side-con ext-rest ...) rest ...)
              (side-condition-keyword? #'side-con)
              (loop #'(rest ...)
                    new-c-stx
                    (cons #'(side-con (unquote ext-rest ...)) extra-stx))]
             [(rule ellipsis rest ...)
              (ellipsis? #'ellipsis)
              (loop #'(rest ...)
                    (cons #'ellipsis (cons (fix-rule #'rule) new-c-stx))
                    extra-stx)]
             [(rule rest ...)
              (loop #'(rest ...)
                    (cons (fix-rule #'rule) new-c-stx)
                    extra-stx)])))
       raw-clauses))

(define-syntax (compiled-judgment-form-lws stx)
  (syntax-case stx ()
    [(_ clauses name def-stx)
     (do-compile-judgment-form-lws (syntax->list #'clauses) #'name #'def-stx)]))

(define-for-syntax (extract-term-let-binds lhs)
  (let loop ([lhs lhs])
    (syntax-case* lhs (term-let) (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
      [(term-let ((x e1) ...) e2 ...)
       (append (map cons
                    (syntax->list #'(x ...))
                    (syntax->list #'(e1 ...)))
               (loop #'(e2 ...)))]
      ;; FIXME: should follow the grammar of patterns!
      [(a . b)
       (append (loop #'a) (loop #'b))]
      [_else null])))



(define-for-syntax (name-pattern-lws pat)
  (map (λ (x) (cons (to-lw/proc (car x)) (to-lw/proc (cdr x))))
       (extract-pattern-binds pat)))

(define-for-syntax (extract-pattern-binds lhs)
  (let loop ([lhs lhs])
    (syntax-case* lhs (name) (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
      [(name id expr)
       (identifier? #'id)
       (cons (cons #'id #'expr) (loop #'expr))]
      ;; FIXME: should follow the grammar of patterns!
      [(a . b)
       (append (loop #'a) (loop #'b))]
      [_else null])))

(define-for-syntax (check-clauses stx syn-error-name rest relation?)
  (syntax-parse rest
    [([(lhs ...) roc1 roc2 ...] ...)
     rest]
    [([(lhs ...) rhs ...] ...)
     (if relation?
         rest
         (begin
           (for ([clause (in-list rest)])
             (syntax-case clause ()
               [(a b c ...) (void)]
               [x (raise-syntax-error
                   syn-error-name
                   "expected a pattern and a right-hand side" stx clause)]))
           (raise-syntax-error syn-error-name "error checking failed.3" stx)))]
    [([x roc ...] ...)
     (begin
       (for-each 
        (λ (x)
          (syntax-case x ()
            [(lhs ...) (void)]
            [x (raise-syntax-error syn-error-name "expected a function prototype" stx #'x)]))
        (syntax->list #'(x ...)))
       (raise-syntax-error syn-error-name "error checking failed.1" stx))]
    [(x ...)
     (begin
       (for-each 
        (λ (x)
          (syntax-case x ()
            [(stuff stuff2 ...) (void)]
            [x (raise-syntax-error syn-error-name "expected a clause" stx #'x)]))
        (syntax->list #'(x ...)))
       (raise-syntax-error syn-error-name "error checking failed.2" stx))]))

(define-for-syntax (ellipsis? stx)
  (and (identifier? stx)
       (free-identifier=? stx (quote-syntax ...))))

(define-for-syntax (where-keyword? id)
  (and (identifier? id)
       (or (free-identifier=? id #'where)
           (free-identifier=? id #'where/hidden)
           (where/error? id))))
(define-for-syntax (where/error? id)
  (and (identifier? id)
       (free-identifier=? id #'where/error)))
(define-for-syntax (side-condition-keyword? id)
  (and (identifier? id)
       (or (free-identifier=? id #'side-condition)
           (free-identifier=? id #'side-condition/hidden))))
;                                                                        
;                                                                        
;                                                      ;                 
;                                              ;                         
;    ;; ;;  ;;;  ;; ;;    ;;;   ;; ;;   ;;;   ;;;;;  ;;;     ;;;  ;; ;;  
;   ;  ;;  ;   ;  ;;  ;  ;   ;   ;;    ;   ;   ;       ;    ;   ;  ;;  ; 
;   ;   ;  ;;;;;  ;   ;  ;;;;;   ;      ;;;;   ;       ;    ;   ;  ;   ; 
;   ;   ;  ;      ;   ;  ;       ;     ;   ;   ;       ;    ;   ;  ;   ; 
;   ;   ;  ;      ;   ;  ;       ;     ;   ;   ;   ;   ;    ;   ;  ;   ; 
;    ;;;;   ;;;; ;;; ;;;  ;;;;  ;;;;;   ;;;;;   ;;;  ;;;;;   ;;;  ;;; ;;;
;       ;                                                                
;    ;;;                                                                 
;                                                                        
;                                                                        




(define-for-syntax (compile-gen-clause clause-stx mode syn-error-name jdg-name lang)
  (syntax-parse clause-stx
    [((conc-name . conc-body-raw) prems ...)
     (cond
       [(number? mode)
        #`"modeless judgment-forms are not currently handled by generation"]
       [else
        (define what (if mode 'define-judgment-form 'define-relation))
        (define-values (conc/+ conc/-) (split-by-mode (syntax->list #'conc-body-raw) mode))
        (define-values (syncheck-exps conc/+rw names)
          ;; in a relation, we just stick everything into a single sequence so ellipses
          ;; are handled properly at this stage (there will be an error later about them, tho)
          (if mode
              (rewrite-pats conc/+ lang what)
              (rewrite-pats (list conc/+) lang what)))
        (define-values (ps-rw eqs p-names)
          (rewrite-prems #t (syntax->list #'(prems ...)) names lang what))
        (define-values (conc/-rw conc-mfs) (rewrite-terms conc/- p-names))
        (define conc (if mode
                         `(list ,@(assemble mode conc/+rw conc/-rw))
                         `(list ,(car conc/+rw))))
        (with-syntax ([(c-mf ...) conc-mfs]
                      [(eq ...) eqs]
                      [(prem-bod ...) (reverse ps-rw)])
          #`(begin #,@syncheck-exps
                   (clause `#,conc
                           (list eq ...)
                           (list c-mf ... prem-bod ...)
                           effective-lang
                           '#,jdg-name)))])]))


(define-for-syntax (rewrite-prems in-judgment-form? prems names lang what)
  (define (rewrite-jf prem-name prem-body ns ps-rw eqs)
    (define p-form (lookup-judgment-form-id prem-name))
    (define p-mode (judgment-form-mode p-form))
    (define p-clauses (judgment-form-gen-clauses p-form))
    (define-values (p/-s p/+s) (split-by-mode (syntax->list prem-body) p-mode))
    (define-values (p/-rws mf-apps)
      (if p-mode
          (rewrite-terms p/-s ns in-judgment-form?)
          (rewrite-terms (list (datum->syntax #f p/-s)) ns in-judgment-form?)))
    (define-values (syncheck-exps p/+rws new-names) (rewrite-pats p/+s lang what))
    (define p-rw (assemble p-mode p/-rws p/+rws))
    (with-syntax ([(p ...) p-rw])
      (values (cons #`(begin
                        #,@syncheck-exps
                        (prem #,p-clauses '(list p ...)))
                    (append mf-apps ps-rw))
              eqs
              (append ns new-names))))
  (define-values (prems-rev new-eqs new-names)
    (for/fold ([ps-rw '()] 
               [eqs '()]
               [ns names])
      ([prem prems])
      (syntax-case prem ()
        [(-where pat term)
         (where-keyword? #'-where)
         (let-values ([(term-rws mf-cs) (rewrite-terms (list #'term) ns in-judgment-form?)])
           (with-syntax ([(syncheck-exp pat-rw new-names) (rewrite/pat #'pat lang what)])
             (values (append mf-cs ps-rw)
                     (cons #`(begin syncheck-exp (eqn 'pat-rw '#,(car term-rws))) eqs)
                     (append (syntax->datum #'new-names) ns))))]
        [(side-cond rest)
         (side-condition-keyword? #'side-cond)
         (if in-judgment-form?
             (let-values ([(term-rws mf-cs) (rewrite-terms (list #'rest) ns in-judgment-form?)])
               (values (append mf-cs ps-rw)
                       (cons #`(dqn '() #f '#,(car term-rws)) eqs)
                       ns))
             (values ps-rw eqs ns))]
        [(prem-name . prem-body)
         (and (judgment-form-id? #'prem-name) in-judgment-form?)
         (rewrite-jf #'prem-name #'prem-body ns ps-rw eqs)]
        [(judgment-holds (prem-name . prem-body))
         (and (judgment-form-id? #'prem-name) (not in-judgment-form?))
         (rewrite-jf #'prem-name #'prem-body ns ps-rw eqs)]
        [var
         (eq? '... (syntax-e #'var))
         ;; TODO - fix when implementing ellipses
         (values ps-rw eqs ns)]
        [else (raise-syntax-error what "malformed premise" prem)])))
  (values prems-rev new-eqs new-names))

(define-for-syntax (rewrite-pats pats lang what)
  (with-syntax ([((syncheck-exp pat-rw (names ...)) ...) 
                 (for/list ([p (in-list pats)])
                   (rewrite/pat p lang what))])
    (values #'(syncheck-exp ...)
            (syntax->list #'(pat-rw ...))
            (remove-duplicates (syntax->datum #'(names ... ...))))))

(define-for-syntax (rewrite/pat pat lang what)
  (with-syntax ([(syncheck-exp body (names ...) (names/ellipses ...))
                 (rewrite-side-conditions/check-errs lang what #t pat)])
    #'(syncheck-exp body (names ...))))

(define-for-syntax (rewrite-terms terms names [reverse-mfs? #f])
  (with-syntax* ([((term-pattern ((res-pat ((metafunc f) args-pat)) ...) body-pat) ...)
                  (map (λ (t) (term-rewrite t names)) terms)]
                 [((mf-clauses ...) ...)
                  (for/list ([fs (in-list (syntax->list #'((f ...) ...)))])
                    (for/list ([f-id (in-list (syntax->list fs))])
                      (if (judgment-form-id? f-id)
                          #`(error 'generate-term
                                   "generation disabled for relations in term positions: ~a"
                                   '#,f-id)
                          #`(metafunc-proc-gen-clauses #,f-id))))])
    (define to-maybe-be-revd
      (syntax->list #'((prem mf-clauses '(list args-pat res-pat)) ... ...)))
    (values (syntax->list #'(body-pat ...))
            (if reverse-mfs? (reverse to-maybe-be-revd) to-maybe-be-revd))))

(define-for-syntax (check-pats stx)
  (cond
    [(has-unsupported-pat? stx) 
     =>
     (λ (bad-stx)
       #`(unsupported-pat-err #,bad-stx))]
    [else
     stx]))

(define-for-syntax (has-unsupported-pat? stx)
  (syntax-case stx ()
    [(repeat . rest)
     (and (identifier? #'repeat)
          (eq? (syntax-e #'repeat) 'repeat))
     #''(repeat . rest)]
    [(side-condition . rest)
     (and (identifier? #'side-condition)
          (eq? (syntax-e #'side-condition) 'side-condition))
     #''(side-condition . rest)]
    [(in-hole . rest)
     (and (identifier? #'in-hole)
          (eq? (syntax-e #'in-hole) 'in-hole))
     #''(in-hole . rest)]
    [(undatum (variable-not-in (term . tr) (q/t s)))
     (and (identifier? #'undatum)
          (eq? (syntax-e #'undatum) 'undatum)
          (identifier? #'variable-not-in)
          (eq? (syntax-e #'variable-not-in) 'variable-not-in)
          (identifier? #'q/t)
          (or (eq? (syntax-e #'q/t) 'term)
              (eq? (syntax-e #'q/t) 'quote)
              (eq? (syntax-e #'q/t) 'quasiquote)))
     #f]
    [(undatum . rest)
     (and (identifier? #'undatum)
          (eq? (syntax-e #'undatum) 'undatum))
     #''(undatum . rest)]
    [(undatum-splicing .rest)
     (and (identifier? #'undatum-splicing)
          (eq? (syntax-e #'undatum-splicing) 'undatum-splicing))
     #''(undatum-splicing .rest)]
    [(elems ...)
     (for/or ([e (in-list (syntax->list #'(elems ...)))])
       (has-unsupported-pat? e))]
    [_
     #f]))

(define (term->string/error-message t)
  (define candidate (format "~s" t))
  (define limit 1000)
  (cond
    [(< (string-length candidate) limit) t]
    [else (string-append (substring candidate 0 (- limit 3)) "...")]))

(provide define-judgment-form 
         define-relation
         define-extended-judgment-form
         define-overriding-judgment-form
         judgment-holds
         build-derivations
         generate-lws
         IO-judgment-form?
         call-runtime-judgment-form
         include-jf-rulename
         term->string/error-message
         (struct-out derivation-subs-acc)
         (struct-out runtime-judgment-form)
         (for-syntax extract-term-let-binds
                     name-pattern-lws
                     extract-pattern-binds
                     check-clauses
                     split-by-mode
                     where-keyword?
                     side-condition-keyword?
                     ellipsis?
                     visible-extras
                     judgment-form-id?
                     lookup-judgment-form-id
                     split-out-contract
                     jf-is-relation?))


(provide --> fresh with I O ;; macro keywords
         (for-syntax prune-syntax
                     side-condition-keyword?
                     bind-withs
                     split-by-mode)
         current-traced-metafunctions
         
         (struct-out metafunc-extra-side-cond)
         (struct-out metafunc-extra-where)
         (struct-out metafunc-extra-fresh))

(provide unsupported-pat-err-name
         (for-syntax rewrite-terms
                     currently-expanding-term-fn
                     rewrite-prems
                     with-syntax*
                     definition-nts
                     check-pats
                     relation-split-out-rhs))
