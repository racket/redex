#lang scheme/gui

#|

Special symbols that are parsed out of the other scheme files in this directory:

  ;; START <name>
  ;; END <name>

The text between the start and end is saved in a file whose name is constructed
from the name of the filename being processed, say "file.ss" and the name specified
above, eg: .file-<name>-GEN.tex

  ;; EXAMPLE <name> <string sizing>
  ;; END <name>

As with START, the text between the start and end is saved in a file, with the same
naming conventions. In additon, a prompt is added before the first line in the file,
and the code is evaluated and the result placed afterwards.

If <string sizing> is present, an additional minipage is added to the first part of the 
example (anticipating a following BESIDE) and the string is used as the argument for
a size, eg in: \begin{minipage}{_____} where the underscores are replaced by the contents
of the string.

  ;; ENDDEFS

Text up to this point is included as a preamble in each example being evaluated.
Include definitions of the grammar & reduction relation before that, but do not
include any expressions that have non-void values before that, or they will appear
in each EXAMPLE file.

  ;; CONTINUE <name>
  ;; BESIDE <name> <width> <sizing string>

If a continue or beside line appears inside an EXAMPLE, then the text before that line 
is collected, evaluated and its output is shown, right at that point and 
then the process continues. This is useful for putting multiple examples into a single
\dbox{}.

Continue shows the output one above the other, and beside shows them side-by-side
with a vertical bar.

The <width> in a beside is optional (and may also be present, but be #f). 
If present (and not #f), it controls the width of the column
just before the BESIDE. Specifically, it sets the pretty-printer's maximum width when 
printing out the results of the evaluation. If it isn't present, then 1/2 of the total
width is used.

The <sizing string> is also optional. If present, it works just like the <sizing string>
in EXAMPLE, creating a minipage.

|#

(require scheme/port
         scheme/runtime-path
         scheme/system
         "../redex-latex-config/pict-config-setup.ss"
         mzlib/pconvert)


;; these requires are here in order to attach them later
(require texpict/mrpict
         redex)

(send (current-ps-setup) set-file "junk.ps")
(dc-for-text-size (new post-script-dc% [interactive #f]))
(pict-config-setup)

;; prefix : format string
;; the ~a is filled with an open minipage declaration or with just an empty string
(define prefix "~~\\par\\noindent\\begin{schemeregion}\n\\dbox{~a\\begin{schemetopbox}\n")

;; middle: format string
;; the first ~a is filled with an open minipage declaration or with a spacer, and
;; the second ~a is filled with a close minipage declaration or with a spacer
(define middle "\\end{schemetopbox}~a\\vline{}~a\\begin{schemetopbox}\n")

;; suffix: format string
;; the ~a is filled with a close minipage declaration or with just an empty string
(define suffix "\\end{schemetopbox}~a}\n\\end{schemeregion}\n")

(define scratch-example-file 'scratch-example-tmp)

;(define default-pp-columns 60)
(define default-pp-columns 52)

(define (show-FAILED-schema? filename tag)
  (and (equal? (path->string filename) "iswim-test.ss")
       (equal? tag "fail")))

(define mps 
  (map (λ (x) ((current-module-name-resolver) x #f #f))
       (list 'redex
             'scheme/gui
             'texpict/mrpict)))

(define (extract-file filename)
  (let-values ([(filename-base-dir _1 _2) (split-path filename)])
    (let/ec date-escape
      (let ([found-one? #f])
        (call-with-input-file filename
          (λ (in-port)
            (let loop ([first-one? #t])
              (let ([l (read-line in-port)])
                (cond
                  [(eof-object? l) (void)]
                  [(regexp-match #rx"^ *;; (START|EXAMPLEN?) +(.*)$" l)
                   =>
                   (λ (m)
                     (unless found-one? 
                       (printf "~a:" (clean-up-for-display filename))
                       (flush-output)
                       (set! found-one? #t))
                     (let* ([example? (regexp-match #rx"EXAMPLE" (list-ref m 1))]
                            [stuff (open-input-string (list-ref m 2))]
                            [key (with-handlers ((exn:fail:read? (λ (x) 
                                                                   (error 'extract.ss
                                                                          "could not parse name on line ~s, orig error: ~a"
                                                                          l
                                                                          (exn-message x)))))
                                   (read stuff))]
                            [width (extract-width stuff l)]
                            [of 
                             (let-values ([(base name dir) (split-path filename)])
                               (build-path
                                main-dir
                                (string-append
                                 "."
                                 (path->string (path-replace-suffix name #""))
                                 (format "-~a-GEN.tex" key))))]
                            [ep #f]
                            [init-ep
                             (λ ()
                               (let-values ([(base name dir) (split-path filename)])
                                 (when example?
                                   (set! ep (open-output-file (build-path filename-base-dir (format "~a.ss" scratch-example-file))
                                                              #:exists 'truncate)))))])
                       
                       (when (and first-one?
                                  (file-exists? of)
                                  (>= (file-or-directory-modify-seconds of)
                                      (file-or-directory-modify-seconds filename))
                                  (>= (file-or-directory-modify-seconds of)
                                      (file-or-directory-modify-seconds "extract.ss")))
                         (printf " <<file unchanged>>\n")
                         (date-escape (void)))
                       
                       (init-ep)
                       (call-with-output-file of
                         (λ (out-port)
                           (printf " ~a" key) (flush-output)
                           (fprintf out-port "% WARNING: do not edit this file. it was\n")
                           (fprintf out-port "% automatically generated from\n% ~a\n\n" filename)
                           (when ep
                             (fprintf out-port "% ALSO: the results below were generated automatically\n")
                             (fprintf out-port "%         by evaluting the term after the prompt in mzscheme\n\n"))
                           (display (format prefix (if width 
                                                       (format "\\begin{minipage}{~a}" width)
                                                       ""))
                                    out-port)
                           (let ([index-entry #f]
                                 [had-beside? #f])
                             (let loop ([spaces-to-remove #f]
                                        [first-line? #t]
                                        [close-minipage? width])
                               (let ([l (read-line in-port 'any)])
                                 (cond
                                   [(eof-object? l)
                                    (error 'extract.ss "did not find end for key ~a" key)]
                                   [(regexp-match (format "^ *;; CONTINUE ~a *$" key)
                                                  l)
                                    (unless ep
                                      (error 'extract.ss "found a CONTINUE not inside an EXAMPLE in ~s" filename))
                                    (close-output-port ep)
                                    (fetch-and-show-output out-port filename key default-pp-columns)
                                    (display "$\\relax$\n" out-port)
                                    (init-ep)
                                    (loop spaces-to-remove #t #f)]
                                   [(regexp-match (format "^ *;; BESIDE ~a *([#f0-9]*)(.*)$" key)
                                                  l)
                                    =>
                                    (λ (m)
                                      (let ([pp-columns (or (string->number (list-ref m 1))
                                                            (/ default-pp-columns 2))]
                                            [minipage (extract-width (open-input-string (list-ref m 2)) l)])
                                        (unless ep
                                          (error 'extract.ss "found a BESIDE not inside an EXAMPLE in ~s" filename))
                                        (set! had-beside? #t)
                                        (close-output-port ep)
                                        (fetch-and-show-output out-port filename key pp-columns)
                                        (display (format middle 
                                                         (if close-minipage? 
                                                             "\\end{minipage}"
                                                             "~~~")
                                                         (if minipage
                                                             (format "~~~~\\begin{minipage}{~a}" minipage)
                                                             "~~"))
                                                 out-port)
                                        (init-ep)
                                        (loop spaces-to-remove #t minipage)))]
                                   [(regexp-match (format "^ *;; STOP ~a *$" key)
                                                  l)
                                    (when ep
                                      (close-output-port ep)
                                      (fetch-and-show-output out-port filename key (if had-beside?
                                                                                       (/ default-pp-columns 2)
                                                                                       default-pp-columns))
                                      (delete-file (build-path filename-base-dir (format "~a.ss" scratch-example-file))))
                                    (display (format suffix (if close-minipage?
                                                                "\\end{minipage}"
                                                                ""))
                                             out-port)
                                    (void)]
                                   [else
                                    (let ([spaces-to-remove
                                           (or spaces-to-remove
                                               (if (regexp-match #rx"^( *)[^ ]" l)
                                                   (string-length (cadr (regexp-match #rx"^( *)[^ ]" l)))
                                                   0))])
                                      
                                      (cond
                                        [(not index-entry)
                                         (let ([m (regexp-match #rx" *.(define[^ ]*) ([^ ]+)" l)])
                                           (when m
                                             (cond
                                               [(regexp-match #rx"define-metafunction" l)
                                                (set! index-entry 'metafunction)]
                                               [else
                                                (set! index-entry (list (list-ref m 1)
                                                                        (list-ref m 2)))])))]
                                        [(eq? index-entry 'metafunction)
                                         (cond
                                           [(regexp-match #rx"^ *$" l)
                                            (void)]
                                           [(regexp-match #rx"^ *;" l)
                                            (void)]
                                           [else
                                            (let ([m (regexp-match #rx"^ *[[(][[(]([^ ]*)" l)])
                                              (unless m 
                                                (error 'extract.ss "could not parse metafunction name in line ~s" l))
                                              (set! index-entry (list "define-metafunction"
                                                                      (list-ref m 1))))])])
                                      
                                      (let ([transformed
                                             (transform (substring l 
                                                                   (min (string-length l) spaces-to-remove)
                                                                   (string-length l)))])
                                        (when ep
                                          (if first-line?
                                              (display "> " out-port)
                                              (display "  " out-port)))
                                        (display transformed out-port)
                                        (newline out-port)
                                        (when ep
                                          (display (rewrite-renders l) ep)
                                          (newline ep)))
                                      (loop spaces-to-remove #f close-minipage?))])))
                             (when index-entry
                               (print-index-entry out-port index-entry))))
                         #:exists 'truncate))
                     (loop #f))]
                  [else (loop first-one?)])))))
        (when found-one?
          (printf "\n"))))))

(define (extract-width stuff l)
  (with-handlers ((exn:fail:read? (λ (x) #f)))
    (let ([width (read stuff)])
      (cond
        [(eof-object? width) #f]
        [(string? width) width]
        [else (error 'extract.ss "could not parse width on line ~s, got ~s, expected a string" l width)]))))

(define (print-index-entry out-port index-entry)
  (unless (pair? index-entry)
    (error 'print-index-entry "could not find metafunction name"))
  (let* ([raw-name (list-ref index-entry 1)]
         [unicode-name (regexp-replace #rx"[)]$"
                                       (regexp-replace #rx"^[(]" 
                                                       raw-name 
                                                       "")
                                       "")]
         [latex-name (rewrite-unicode unicode-name #t)])
    (let-values ([(index-key bang) (build-index-key/bang unicode-name)])
      (let* ([atsign 
              (if (andmap (λ (x) (> (char->integer x) 255)) (string->list unicode-name))
                  latex-name
                  (format "\\texttt{~a}" latex-name))]
             [index-ent
              (format "\\index{~a@~a~a}\n" 
                      (regexp-replace* #rx"!" index-key "\"!")
                      (regexp-replace* #rx"!" atsign "\"!")
                      (regexp-replace* #rx"!" bang "\"!"))])
        #;
        (fprintf (current-error-port) "\nuicode-name ~s latex-name ~s index-key ~s\n" 
                 unicode-name
                 latex-name
                 index-key)
        (fprintf out-port index-ent)))))

(define (build-index-key/bang str)
  (let ([gets-period? 
         (ormap (λ (x) (> (char->integer x) 255))
                (string->list str))])
    (let loop ([syms syms]
               [str str])
      (cond
        [(null? syms) 
         (if gets-period?
             (values (string-append "." str)
                     "!in part II")
             (values str ""))]
        [else
         (let* ([this-one (car syms)]
                [reg (list-ref this-one 0)]
                [key (list-ref this-one 2)]
                [m (regexp-match-positions reg str)])
           (if m
               (let* ([where (car m)]
                      [start (car where)]
                      [end (cdr where)])
                 (loop (cdr syms)
                       (string-append (substring str 0 start)
                                      key
                                      (substring str end (string-length str)))))
               (loop (cdr syms) str)))]))))

(define (clean-up-for-display filename)
  (let-values ([(base1 name1 dir1) (split-path filename)])
    (let-values ([(base2 name2 dir2) (split-path base1)])
      (path->string (build-path name2 name1)))))

(define (fetch-and-show-output out-port filename key pp-columns)
  (let ([sp (open-output-string)]
        [vals '()]
        [original-output-port (current-error-port)])
    (let/ec k
      
      ;; limit exceptions (error output will be in the file).
      (parameterize ([error-escape-handler (λ () (k (void)))])
        (parameterize ([error-display-handler
                        (let ([edh (error-display-handler)])
                          (λ (msg exn)
                            (set! error-happened? #t)
                            (let-values ([(in out) (make-pipe)])
                              (let ([t (thread
                                        (λ ()
                                          (copy-port in sp original-output-port)
                                          (close-input-port in)))])
                                (fprintf original-output-port "\n")
                                (parameterize ([current-output-port out]
                                               [current-error-port out])
                                  (edh msg exn))
                                (close-output-port out)
                                (thread-wait t)))))])
        (let ([orig-namespace (current-namespace)]
              [orig-err (current-error-port)]
              [prefix-lines (prefix-line-count filename)])
          (let-values ([(base-dir _1 _2) (split-path filename)])
            (parameterize ([current-print (λ (v) (set! vals (append vals (list v))))]
                           [current-namespace (make-gui-namespace)]
                           [current-output-port sp]
                           [current-error-port sp]
                           [current-load-relative-directory base-dir]
                           [current-directory base-dir]
                           [read-accept-reader #t])
              (for-each (λ (mp) (namespace-attach-module orig-namespace mp)) mps)
              (let-values ([(in out) (make-pipe)])
                (thread (λ ()
                          (fetch-prefix filename out)
                          (close-output-port out)))
                (letrec ([fp (open-input-file (format "~a.ss" scratch-example-file))]
                         [ap (input-port-append #t in fp)]
                         [c-port (transplant-input-port ap
                                                        (λ ()
                                                          (let-values ([(line col pos) (port-next-location ap)])
                                                            (values (max 1 (- line prefix-lines)) col pos)))
                                                        1)])
                  (port-count-lines! ap)
                  (port-count-lines! c-port)
                  (let ([exp
                         (read-syntax
                          (format "~a.ss" scratch-example-file)
                          c-port)])
                    (eval exp))
                  (close-input-port fp)))
              (dynamic-require `'anonymous-module #f)
              #;(dynamic-require (format "~a.ss" scratch-example-file) #f)))))))
    (show-output (get-output-string sp)
                 out-port 
                 (show-FAILED-schema? filename key))
    (for-each (λ (v) (transform-and-write-value filename v out-port pp-columns))
              vals)))

(define (prefix-line-count filename)
  (let-values ([(in out) (make-pipe)])
    (thread (λ ()
              (fetch-prefix filename out)
              (close-output-port out)))
    (let loop ([n 0])
      (let ([line (read-line in)])
        (if (eof-object? line)
            n
            (loop (+ n 1)))))))

(define (fetch-prefix filename ep)
  (call-with-input-file filename
    (λ (port)
      (let loop ()
        (let ([line (read-line port)])
          (when (eof-object? line)
            (error 'extract.ss "expected ';; ENDDEFS' line in ~a, but didn't find it" filename))
          (unless (regexp-match #rx"^ *;; ENDDEFS" line)
            (display line ep)
            (newline ep)
            (loop)))))))

(define (install-special-pretty-print-lw-handling thunk)
  (let ([inset 0])
    (parameterize ([pretty-print-print-line
                    (λ (line-number op len dest)
                      (cond
                        [(and (equal? 0 line-number)
                              (equal? 0 len))
                         0]
                        [(not line-number)
                         0]
                        [else
                         (newline op)
                         (display (build-string 
                                   (cond
                                     [#t inset]
                                     [(= 1 inset) 1]
                                     [else (+ inset 1)])
                                   (λ (i) #\space))
                                  op)
                         inset]))])
      (parameterize ([pretty-print-size-hook
                      (λ (val display? op)
                        (and (pair? val)
                             (eq? (car val) 'make-lw)
                             (pair? (cdr val))
                             (let ([arg1 (cadr val)])
                               (and (pair? arg1)
                                    (not (eq? 'quote (car arg1)))
                                    (inexact->exact (pretty-print-columns))))))]
                     [pretty-print-print-hook
                      (λ (val display? op)
                        (display "(make-lw" op)
                        (set! inset (+ inset 1))
                        (pretty-print-newline op (pretty-print-columns))
                        (set! inset (+ inset 1))
                        (pretty-print (cadr val) op)
                        (set! inset (- inset 1))
                        (pretty-print-newline op (pretty-print-columns))
                        (set! inset (- inset 1))
                        (let loop ([rst (cddr val)])
                          (write (car rst) op)
                          (cond
                            [(null? (cdr rst))
                             (display ")" op)]
                            [else
                             (display " " op)
                             (loop (cdr rst))])))])
        (thunk)))))

(define pict-value-counter 0)
(define (transform-and-write-value filename v out-port pp-columns)
  (cond
    [(void? v) (void)]
    [(pict? v) 
     (set! pict-value-counter (+ 1 pict-value-counter))
     (let-values ([(base name dir) (split-path filename)])
       (let ([fn (format ".pictval-~a~a" (path->string name) pict-value-counter)])
         (render-pict v fn)
         (fprintf out-port "$\\mbox{\\includegraphics{~a.ps}}$\n" fn)))]
    [else
     (let ([sp (open-output-string)])
       (parameterize ([constructor-style-printing #t]
                      [show-sharing #f]
                      [booleans-as-true/false #f]
                      [pretty-print-columns pp-columns])
         (install-special-pretty-print-lw-handling 
          (λ ()
            (pretty-print (print-convert v) sp))))
       (display (transform (get-output-string sp)) out-port))
     (newline out-port)]))

(define (render-pict p fn)
  (send (current-ps-setup) set-file (format "~a.ps" fn))
  (let ([dc (new post-script-dc% [interactive #f])]
        [y-off 0])
    (send dc start-doc "")
    (send dc start-page)
    (draw-pict p dc 0 0) 
    ;; (draw-pict p dc 0 (+ y-off 1)) ;; used to build extra space into the top of the pict
    ; (send dc set-pen "white" 1 'transparent)
    ; (send dc set-brush "white" 'solid)
    ;(send dc draw-rectangle 0 0 2 y-off) ;; used to build extra space into the top of the pict
    (send dc end-page)
    (send dc end-doc)))
		 
(define (transform str)
  (let ([str (fixup-comment-leading-space str)])
    (cond
      [(regexp-match #rx"^([^;]*)(;+)([^;].*)$" str)
       =>
       (λ (m)
         (let ([before (list-ref m 1)]
               [semis (list-ref m 2)]
               [after (list-ref m 3)])
           (format "~a~a$\\mbox{\\texttt{\\textsl{~a}}}$" 
                   before 
                   semis
                   (quote-latex-syms (local-transform after #f)))))]
      [else
       (local-transform str #t)])))

(define (show-output s out-port show-failed-schema?)
  (unless (equal? s "")
    (let* ([no-failed (regexp-replace* #rx"(^|\n)FAILED[^\n]*\n"
                                       s
                                       (if show-failed-schema?
                                           "\\1FAILED \\\\textsf{filename.ss}:\\\\textsf{line}:\\\\textsf{column}\n"
                                           "\\1FAILED\n"))]
           [lines (regexp-split #rx"\n" (regexp-replace #rx"\n$" no-failed ""))])
      (for-each
       (λ (line)
         (fprintf out-port "$\\texttt{\\textsl{~a}}$\n" (regexp-replace* #rx" " 
                                                                         (quote-latex-syms (rewrite-unicode line #f))
                                                                         "~")))
       lines))))

(define (rewrite-unicode str in-scheme?)
  (let loop ([syms syms]
             [str str])
    (cond
      [(null? syms) str]
      [else 
       (let ([sym (car syms)])
         (loop (cdr syms)
               (regexp-replace*
                (list-ref sym 0)
                str
                (format "~a\\\\~a~a" 
                        (if in-scheme? "$" "\\\\ensuremath{")
                        (list-ref sym 1)
                        (if in-scheme? "$" "}")))))])))

;; syms : (listof (list regexp string string))
;; the first string is the latex command (without the initial backslash)
;; the second string is how it should be written for sorting in the index.
(define syms
  '((#rx"β" "beta" "beta")
    (#rx"λ" "lambda" "lambda")
    (#rx"δ" "delta" "delta")
    (#rx"κ" "kappa" "kappa")
    (#rx"φ" "phi" "phi")
    (#rx"ξ" "xi" "xi")
    (#rx"Γ" "Gamma" "gamma")
    (#rx"Ω" "Omega" "omega")
    (#rx"∆" "Dt" "delta")
    (#rx"∧" "wedge" "wedge")
    (#rx"∨" "vee" "vee")
    (#rx"⇒" "Rightarrow" "rightarrow")
    (#rx"↑" "uparrow" "uparrow")
    (#rx"☠" "skull" "skull")
    (#rx"☺" "smiley" "smiley")
    (#rx"ℬ" "Bt" "b")
    (#rx"ĥ" "hat{\\\\mbox{\\\\texttt{h}}}" "h^")
    (#rx"ḣ" "dot{\\\\mbox{\\\\texttt{h}}}" "h.")
    (#rx"ē" "bar{\\\\mbox{\\\\texttt{e}}}" "e-")))

(define (local-transform str in-scheme?)
  (cond
    [(regexp-match #rx"^[\t ]*$" str)
     "$\\relax$"]
    [else
     (regexp-replace*
      #rx"–|—|–|–"
      (rewrite-unicode str in-scheme?)
      "-")]))

;; rewrite-renders : string -> string
;; rewrites calls to the render-* functions into *->pict.
;; NOTE: this can fail if one of the render- functions is
;; used with two arguments.
(define (rewrite-renders str)
  (cond
    [(let ([m (regexp-match #rx"(.*)\\(render-([^ \t\n]*)(.*)$" str)])
       (and m
            (let ([what (list-ref m 2)])
              (and (member what '("language" "metafunction" "reduction-relation" "lw"))
                   m))))
     =>
     (λ (m) 
       (let ([before-render (list-ref m 1)]
             [what (list-ref m 2)]
             [after (list-ref m 3)])
         (format "~a(~a->pict~a" before-render what after)))]
    [else
     (when (and (regexp-match #rx"render-" str)
                (not (regexp-match #rx"render-language-nts" str)))
       (error 'rewrite-renders "could not rewrite ~s" str))
     str]))

(define (quote-latex-syms s)
  (regexp-replace* 
   #rx"_" 
   (regexp-replace*
    #rx"&"
    (regexp-replace*
     #rx"#"
     (regexp-replace*
      #rx"%"
      s
      "\\\\%")
     "\\\\#")
    "\\\\&")
   "\\\\_"))

(define (fixup-comment-leading-space str)
  (cond
    [(regexp-match #rx"^([^;]*;+)( +)([^ ].*)$" str)
     =>
     (λ (m)
       (string-append (list-ref m 1)
                      ;"$"
                      (regexp-replace* #rx" " 
                                       (list-ref m 2)
                                       "~")
                      ;"$"
                      (list-ref m 3)))]
    [else str]))

(provide main)
(define-runtime-path main-dir ".")

(define error-happened? #f)
(define (main) 
  (for-each 
   (λ (f/d)
     (when (directory-exists? f/d)
       (unless (or (regexp-match #rx"svn" (path->string f/d))
                   (regexp-match #rx"compiled" (path->string f/d)))
         (for-each (λ (x) (process-file (normalize-path (build-path f/d x))))
                   (directory-list f/d)))))
   (directory-list main-dir))
  (when error-happened?
    (error 'extract.ss "there was an error")))

(define (process-file x)
  (when (and (regexp-match #rx"\\.ss$" (path->bytes x))
             (not (equal? (path->string x) "extract.ss"))
             (not (equal? (path->string x) (format "~a.ss" scratch-example-file))))
    (extract-file x)))
