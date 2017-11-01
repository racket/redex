#lang racket/base
(require racket/system
         racket/cmdline)

(define (rewrite/copy orig tmp-file)
  (fprintf (current-error-port) "chopping out fonts from ~a\n" orig)
  (call-with-output-file tmp-file
    (λ (out-port)
      (call-with-input-file orig
        (λ (in-port)
          (let loop ([copying? #t])
            (let ([line (read-line in-port)])
              (cond
                [(eof-object? line) (void)]
                [(regexp-match #rx"^%%BeginFont(.*)$" line)
                 =>
                 (λ (m)
                   (let ([fnt (list-ref m 1)])
                     (cond
                       [(and (regexp-match #rx"Charter" fnt)
                             (not (regexp-match #rx"Bold" fnt)))
                        (fprintf (current-error-port) "  chopping ~a\n" fnt)
                        (loop #f)]
                       [else
                        (fprintf (current-error-port) "  keeping ~a\n" fnt)
                        (display line out-port)
                        (newline out-port)
                        (loop #t)])))]
                [(regexp-match #rx"^%%EndFont" line)
                 (loop #t)]
                [else
                 (when copying?
                   (display line out-port)
                   (newline out-port))
                 (loop copying?)]))))))
    #:exists 'truncate)
  (system (format "mv ~a ~a" tmp-file orig))
  (void))

(command-line
 #:args (ps-file tmp-file)
 (rewrite/copy ps-file tmp-file))
