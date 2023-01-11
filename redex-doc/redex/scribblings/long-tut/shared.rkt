#lang at-exp racket/base
(module+ test (require rackunit))

#; #;
(this is to facilitate
      some testing code
      that appears below)
(it helps test
    codeblock-from-file)

(provide
  goals  ;; bulletize goals 
  ntt    ;; nested tt 
  common ;; where are the common definitions? 
  (for-label (all-from-out redex/reduction-semantics racket/base))
  (all-from-out
    "exercise/ex.rkt"
    scribble/example
    racket/sandbox
    scribble/core
    scriblib/figure)
  code-from-file)

;; -----------------------------------------------------------------------------
(require
  "exercise/ex.rkt"
  (for-label racket/base redex/reduction-semantics)
  (for-syntax racket/base racket/match racket/list racket/port
              syntax/parse syntax/strip-context)
  scribble/manual
  scribble/core
  scribble/example
  racket/sandbox
  racket/runtime-path
  racket/list
  scriblib/figure)


(define-syntax-rule
   (goals (item x ...) ...)
   @list{
     @tabular[#:style 'boxed
       @list[
         @list[@bold{Goals}]
	 @list[(t " --- " x ...)] ... ]]})
;; @list[@itemlist[ x ... ]]]]})

(define-syntax-rule
  (ntt x ...)
  (nested #:style 'inset (tt x ...)))

(define (common)
@list{
The following exercises refer to several definitions found in, and exported
from, @seclink["common.rkt"]. You may either copy these
definitions into your file or add the following @racket[require] statement
to the top of your file: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(require "common.rkt")
))
@;%
 }
)

;; codeblock-from-file pulls a specific hunk of lines from
;; one of the files in code/ and generates a use of `examples`
;; with that code in it.
;;
;; Supply:
;; - the name of the file as a relative path to the source
;;   location of the use of codeblock-from-file,
;; - a regular expression that the first line to include must match
;; - the evaluator to evaluate the program, with #:eval; if #:eval
;;   is not present, the code is not evaluated and instead of `examples`
;;   being used, `codeblock` is used.
;; - the number of expressions that should follow (according to the
;;   rules of read) with #:exp-count, which defaults to 1
;; - the number of lines to skip, counting the matching line
;;   (useful to add comments to give the regexp something to grab onto)
;;   with #:skip-lines
;; - and a sequence of strings to tack onto the end of the expression
;;   these are treated as if they are extra lines in the file with
;;   #:extra-code
;;
;; if the expression begins with define, define-language or a few
;; other keywords (see the match expression below), then the code
;; is wrapped with eval:no-prompt (see examples for docs)
;; the highlighting and linking is based on the for-label bindings
;; that are at the use of codeblock-from-file
(define-syntax (code-from-file stx)
  (syntax-parse stx
    [(_ file:string rx-start:regexp 
        (~optional (~seq #:eval eval))
        (~optional (~seq #:exp-count number-of-expressions:integer))
        (~optional (~seq #:skip-lines number-of-lines-to-skip:integer))
        (~optional (~seq #:extra-code (extra-code:string ...))))
     (define doing-eval? (attribute eval))
     (define code
       (get-code (syntax-e #'file)
                 (syntax-e #'rx-start)
                 (if (attribute number-of-expressions)
                     (syntax-e #'number-of-expressions)
                     1)
                 (if (attribute number-of-lines-to-skip)
                     (syntax-e #'number-of-lines-to-skip)
                     0)
                 (if (attribute extra-code)
                     (map
                      syntax-e
                      (syntax->list #'(extra-code ...)))
                     '())
                 doing-eval?
                 stx))
     (if doing-eval?
         #`(examples #:label #f
                     #:eval eval
                     #,@code)
         #`(codeblock #:context #'#,stx
                      #,@code))]))

(begin-for-syntax
  (define (get-code file rx:start number-of-expressions number-of-lines-to-skip extra-code doing-eval? stx)
    (define src (syntax-source stx))
    (define-values (src-dir _1 _2) (split-path src))
    (define-values (in out) (make-pipe))
    (define-values (start-pos start-line end-line no-prompt?s)
      (get-start-and-end-lines file rx:start
                               number-of-expressions
                               stx
                               src-dir))
    (set! start-line (+ start-line number-of-lines-to-skip))
    (call-with-input-file (build-path src-dir file)
      (λ (port)
        (for/list ([l (in-lines port)]
                   [i (in-range end-line)]
                   #:unless (< i start-line))
          (displayln l out))))
    (for ([extra-code-item (in-list extra-code)])
      (displayln extra-code-item out))
    (close-output-port out)
    (port-count-lines! in)
    (set-port-next-location! in start-line 0 start-pos)
    (cond
      [doing-eval?
       (for/list ([no-prompt? (in-list (append no-prompt?s
                                               (make-list (length extra-code)
                                                          #f)))])
         (define e (replace-context stx (read-syntax (build-path src-dir file) in)))
         (if no-prompt?
             `(eval:no-prompt ,e)
             e))]
      [else
       (define sp (open-output-string))
       (copy-port in sp)
       (list (get-output-string sp))]))

  (define (get-start-and-end-lines file rx:start number-of-expressions stx src-dir)
    (define-values (start-line start-pos)
      (call-with-input-file (build-path src-dir file)
        (λ (port)
          (define count 0)
          (let/ec escape
            (for ([l (in-lines port)])
              (when (regexp-match? rx:start l)
                (escape))
              (set! count (+ count 1)))
            (raise-syntax-error 'codeblock-from-file
                                (format "didn't find a line matching ~s" rx:start)
                                stx))
          (define-values (line col pos) (port-next-location port))
          (values count pos))))
    (define-values (no-prompt?s end-line)
      (call-with-input-file (build-path src-dir file)
        (λ (port)
          (port-count-lines! port)
          (for ([i (in-range start-line)])
            (read-line port))
          (define no-prompt?s
            (for/list ([i (in-range number-of-expressions)])
              (define exp (read port))
              (when (eof-object? exp) (error 'codeblock-from-file "expression #~a not present in file" i))
              (match exp
                [`(define . ,stuff) #t]
                [`(define-language . ,stuff) #t]
                [`(define-extended-language . ,stuff) #t]
                [`(define-metafunction . ,stuff) #t]
                [`(test-equal . ,stuff) #t]
                [_ #f])))
          (define-values (line col pos) (port-next-location port))
          (values no-prompt?s line))))
    (values start-pos start-line end-line no-prompt?s)))
