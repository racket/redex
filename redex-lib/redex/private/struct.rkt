#lang racket/base

(require racket/list "matcher.rkt")

;; don't provide reduction-relation directly, so that we can use that for the macro's name.
(provide reduction-relation-lang
         reduction-relation-make-procs
         reduction-relation-rule-names
         reduction-relation-lws
         reduction-relation-procs
         reduction-relation-domain-pat
         reduction-relation-codomain-pat
         reduction-relation-compiled-domain-pat
         build-reduction-relation make-reduction-relation
         no-codomain-pattern no-codomain-pattern?
         reduction-relation?
         empty-reduction-relation
         make-rewrite-proc rewrite-proc? rewrite-proc-name 
         rewrite-proc-side-conditions-rewritten rewrite-proc-lhs-src rewrite-proc-id
         (struct-out rule-pict-info)

         metafunc-proc-clause-names
         metafunc-proc-pict-info
         metafunc-proc-lang
         metafunc-proc-multi-arg?
         metafunc-proc-name
         metafunc-proc-in-dom?
         metafunc-proc-dom-pat
         metafunc-proc-cases
         metafunc-proc-gen-clauses
         metafunc-proc?
         make-metafunc-proc)

(define-struct rule-pict-info (arrow
                               lhs rhs
                               label computed-label
                               side-conditions/pattern-binds fresh-vars))

;; type proc = (exp exp (any -> any) (listof any) -> (listof any)))
;;   a proc is a `cached' version of a make-proc, specialized to a particular language
;;   since that first application does all the work of compiling a pattern (wrt to a language),
;;   we want to avoid doing it multiple times, so it is cached in a reduction-relation struct


(define-values (make-rewrite-proc 
                rewrite-proc? 
                rewrite-proc-name
                rewrite-proc-side-conditions-rewritten
                rewrite-proc-lhs-src
                rewrite-proc-id)
  (let ()
    (define-values (type constructor predicate accessor mutator) 
      (make-struct-type 'rewrite-proc #f 5 0 #f '() #f 0))
    (values constructor 
            predicate 
            (make-struct-field-accessor accessor 1 'name)
            (make-struct-field-accessor accessor 2 'lhs)
            (make-struct-field-accessor accessor 3 'lhs-src)
            (make-struct-field-accessor accessor 4 'id))))

;; lang : compiled-language
;; make-procs = (listof (compiled-lang -> proc))
;; rule-names : (listof sym)
;; procs : (listof proc)
;; codomain-pat : (or/c #f pattern[uncompiled])
(define-struct reduction-relation (lang make-procs rule-names lws procs
                                        domain-pat

                                        ;; (or/c no-codomain-pattern? <pat>)
                                        codomain-pat
                                        
                                        ;; (or/c #f compiled-pat)
                                        ;; -- this is #f when there is no codomain pattern,
                                        ;;    and the compiled version of the domain-pattern
                                        ;;    when there is a codomain pattern
                                        compiled-domain-pat))

(define-values (no-codomain-pattern no-codomain-pattern?)
  (let ()
    (define-struct no-codomain-pattern ())
    (values (no-codomain-pattern) no-codomain-pattern?)))

(define empty-reduction-relation (make-reduction-relation 'empty-reduction-relations-language
                                                          '()
                                                          '()
                                                          '()
                                                          '()
                                                          #f
                                                          no-codomain-pattern
                                                          #f))

(define (build-reduction-relation original language rules rule-names lws domain-pat codomain-pat)
  (define combined-rules
    (if original
        (append 
         (filter (λ (rule)
                   (or (not (rewrite-proc-name rule))
                       (not (member (string->symbol (rewrite-proc-name rule)) rule-names))))
                 (reduction-relation-make-procs original))
         rules)
        rules))
  (define combined-rule-names
    (if original
        (remove-duplicates (append rule-names (reduction-relation-rule-names original)))
        rule-names))
  (define compiled-domain (compile-pattern language domain-pat #f))
  (define compiled-input-check
    (if (no-codomain-pattern? codomain-pat)
        compiled-domain
        (compile-pattern language codomain-pat #f)))
  (make-reduction-relation
   language combined-rules combined-rule-names lws
   (for/list ([rule (in-list combined-rules)])
     (define specialized (rule language))
     (define (checked-rewrite t)
       (unless (match-pattern compiled-input-check t)
         (error 'reduction-relation
                "relation reduced to ~s via ~a, which is outside its ~a"
                t
                (let ([name (rewrite-proc-name rule)])
                  (if name
                      (format "the rule named ~a" name)
                      "an unnamed rule"))
                (if (no-codomain-pattern? codomain-pat)
                    "domain"
                    "codomain")))
       t)
     (λ (exp acc)
       (unless (match-pattern compiled-domain exp)
         (error 'reduction-relation "relation not defined for ~s" exp))
       (specialized exp exp checked-rewrite acc)))
   domain-pat
   codomain-pat
   (if (no-codomain-pattern? codomain-pat)
       #f
       compiled-domain)))

(define-values (struct:metafunc-proc
                make-metafunc-proc
                metafunc-proc?
                metafunc-proc-ref
                metafunc-proc-set!)
  (make-struct-type 'metafunc-proc #f 10 0 #f null (current-inspector) 0))
(define metafunc-proc-clause-names (make-struct-field-accessor metafunc-proc-ref 1))
(define metafunc-proc-pict-info (make-struct-field-accessor metafunc-proc-ref 2))
(define metafunc-proc-lang (make-struct-field-accessor metafunc-proc-ref 3))
(define metafunc-proc-multi-arg? (make-struct-field-accessor metafunc-proc-ref 4))
(define metafunc-proc-name (make-struct-field-accessor metafunc-proc-ref 5))
(define metafunc-proc-in-dom? (make-struct-field-accessor metafunc-proc-ref 6))
(define metafunc-proc-dom-pat (make-struct-field-accessor metafunc-proc-ref 7))
(define metafunc-proc-cases (make-struct-field-accessor metafunc-proc-ref 8))
(define metafunc-proc-gen-clauses (make-struct-field-accessor metafunc-proc-ref 9))
