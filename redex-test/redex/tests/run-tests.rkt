#lang racket/base
(require racket/port)

;; require this file to run all of the test suites for redex.

(require racket/runtime-path
         racket/cmdline
         racket/match
         pkg/lib
         "private/test-util.rkt"
         "private/bitmap-test-util.rkt")

(define test-examples? #f)
(define set-exit-status-on-stderr? #f)
(define skip-bitmap-tests? #f)

(command-line
 #:once-each
 [("--no-bitmap-gui") "skips the GUI for bitmap-test.rkt" (show-bitmap-test-gui? #f)]
 [("--no-bitmap-tests") "skips the bitmap tests" (set! skip-bitmap-tests? #t)]
 [("--examples") "executes the tests in the examples directory" (set! test-examples? #t)]
 [("--set-exit-status-on-stderr") "executes the tests in the examples directory" (set! set-exit-status-on-stderr? #t)])

(define watching-stderr-and-printed-to-stderr?
  (cond
    [set-exit-status-on-stderr?
     (define printed-to-stderr? #f)
     (define-values (in out) (make-pipe 1))
     (define err (current-error-port))
     (current-error-port out)
     (define copy-thread
       (thread
        (λ ()
          (define b (read-byte in))
          (unless (eof-object? b)
            (set! printed-to-stderr? #t)
            (write-byte b err)
            (copy-port in err)
            (close-input-port in)))))
     (λ ()
       (current-error-port err)
       (close-output-port out)
       (thread-wait copy-thread)
       (flush-output err)
       printed-to-stderr?)]
    [else (λ () #f)]))

(define test-files
  (append
   '("lw-test.rkt"
     "matcher-test.rkt"
     "rewrite-side-condition-test.rkt"
     "unify-tests.rkt"
     "dq-test.rkt"

     "tl-language.rkt"
     "tl-metafunctions.rkt"
     "tl-relation.rkt"
     "tl-reduction-relation.rkt"
     "tl-judgment-form.rkt"
     "tl-test.rkt"

     "err-loc-test.rkt"
     "term-test.rkt"
     "binding-forms-test.rkt"
     "rg-test.rkt"
     "gen-test.rkt"
     "keyword-macros-test.rkt"
     "core-layout-test.rkt"
     "pict-test.rkt"
     "hole-test.rkt"
     "mf-apply-test.rkt"
     "stepper-test.rkt"
     "check-syntax-test.rkt"
     "test-docs-complete.rkt"
     "tut-subst-test.rkt"
     "ambiguous-test.rkt"
     "enum-test.rkt"
     "convert-test.rkt"
     "bitmap-test.rkt")
   (if test-examples?
       '("<redex-examples>/redex/examples/cbn-letrec.rkt"
         "<redex-examples>/redex/examples/stlc.rkt"
         "<redex-examples>/redex/examples/pi-calculus.rkt"
         "<redex-examples>/redex/examples/list-machine/test.rkt"
         ("<redex-examples>/redex/examples/beginner.rkt" main)
         "<redex-examples>/redex/examples/racket-machine/reduction-test.rkt"
         "<redex-examples>/redex/examples/racket-machine/verification-test.rkt"
         "<redex-examples>/redex/examples/delim-cont/test.rkt"
         "<redex-examples>/redex/examples/cont-mark-transform/all-test.rkt"
         ("<redex-examples>/redex/examples/r6rs/r6rs-tests.rkt" main))
       '())))

(define-runtime-path here ".")
(define examples-path (pkg-directory "redex-examples"))

(define (flush)
  ;; these flushes are here for running under cygwin, 
  ;; which somehow makes racket think it isn't using
  ;; an interative port
  (flush-output (current-error-port))
  (flush-output (current-output-port)))

(define exempted-tests
  '("color-test.rkt"
    "ryr-test.rkt"
    "binding-performance-test.rkt"))

;; check to make sure all the files in this directory
;; are actually known by this testing file
(for ([file (in-list (directory-list here))])
  (when (file-exists? (build-path here file))
    (define str (path->string file))
    (unless (or (member str test-files)
                (regexp-match? #rx"~$" str)
                (regexp-match? #rx"[.]bak$" str)
                (equal? str "run-tests.rkt")
                (member str exempted-tests))
      (eprintf "WARNING: unknown file ~a\n" file))))

(for ([test-file (in-list test-files)])
  (define-values (file provided action)
    (match test-file
      [(list (? string? file) id)
       (values file id (λ (x) (x)))]
      [(? string?) 
       (values test-file #f values)]))
  (flush)
  (printf "running ~a\n" file)
  (flush)
  (define path
    (if (regexp-match #rx"<redex-examples>" file)
        (build-path examples-path (cadr (regexp-match #rx"^<redex-examples>/(.*)$" file)))
        (build-path here file)))
  (cond
    [(and (equal? file "bitmap-test.rkt")
          skip-bitmap-tests?)
     (printf "skipping the bitmap tests\n")]
    [else
     (action (dynamic-require path provided))])
  (flush))

(printf "\nWARNING: didn't run ~s\n" exempted-tests)
(flush)
(when (watching-stderr-and-printed-to-stderr?)
  (exit 1))

;; Test mode:
(module test racket/base
  (module config info
    (define timeout 300))
  (require syntax/location)
  (parameterize ([current-command-line-arguments
                  (vector "--examples" "--no-bitmap-gui")])
    (dynamic-require (quote-module-path "..") #f)))
