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
  codeblock-from-file)

;; -----------------------------------------------------------------------------
(require
  "exercise/ex.rkt"
  (for-label racket/base redex/reduction-semantics)
  (for-syntax racket/base racket/match racket/list
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
;; - the evaluator to evaluate the program, with #:eval
;; - the number of expressions that should follow (according to the
;;   rules of read) with #:exp-count, which defaults to 1
;; - and a sequence of strings to tack onto the end of the expression
;;   these are treated as if they are extra lines in the file with
;;   #:extra-code
;;
;; if the expression begins with define, define-language or a few
;; other keywords (see the match expression below), then the code
;; is wrapped with eval:no-prompt (see examples for docs)
;; the highlighting and linking is based on the for-label bindings
;; that are at the use of codeblock-from-file
(define-syntax (codeblock-from-file stx)
  (syntax-parse stx
    [(_ file:string rx-start:regexp #:eval eval
        (~optional (~seq #:exp-count number-of-expressions:integer))
        (~optional (~seq #:extra-code (extra-code:string ...))))

     #`(examples #:label #f
                 #:eval eval
                 #,@(get-code (syntax-e #'file)
                              (syntax-e #'rx-start)
                              (if (attribute number-of-expressions)
                                  (syntax-e #'number-of-expressions)
                                  1)
                              (if (attribute extra-code)
                                  (map
                                   syntax-e
                                   (syntax->list #'(extra-code ...)))
                                  '())
                              stx))]))

(begin-for-syntax
  (define (get-code file rx:start number-of-expressions extra-code stx)
    (define src (syntax-source stx))
    (define-values (src-dir _1 _2) (split-path src))
    (define-values (in out) (make-pipe))
    (define-values (start-line end-line no-prompt?s)
      (get-start-and-end-lines file rx:start
                               number-of-expressions
                               stx
                               src-dir))
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
    (for/list ([no-prompt? (in-list (append no-prompt?s
                                            (make-list (length extra-code)
                                                       #f)))])
      (define e (replace-context stx (read-syntax src in)))
      (if no-prompt?
          `(eval:no-prompt ,e)
          e)))

  (define (get-start-and-end-lines file rx:start number-of-expressions stx src-dir)
    (define start-line
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
          count)))
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
                [`(test-equal . ,stuff) #t]
                [_ #f])))
          (define-values (line col pos) (port-next-location port))
          (values no-prompt?s line))))
    (values start-line end-line no-prompt?s)))
