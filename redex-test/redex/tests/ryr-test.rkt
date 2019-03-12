#lang racket/base
(require net/url 
         racket/port 
         racket/file
         file/gunzip
         file/untar)

(define tmp-dir (make-temporary-file "ryr-test-~a" 'directory))
(current-directory tmp-dir)
(define models-url "http://www.eecs.northwestern.edu/~robby/lightweight-metatheory/models.tar.gz")
(printf "downloading ~a\n   to ~a\n" models-url tmp-dir)
(call-with-output-file "models.tar.gz"
  (λ (out-port)
    (call/input-url
     (string->url models-url)
     get-pure-port
     (λ (in-port)
       (copy-port in-port out-port)))))
(with-handlers ([exn:fail?
                 (λ (exn)
                   (printf "an exception was raised while gunzipping. File's prefix:\n=======\n")
                   (call-with-input-file "models.tar.gz"
                     (λ (port)
                       (for ([i (in-range 1000)])
                         (define b (read-byte port))
                         (unless (eof-object? b)
                           (write-byte b)))
                       (printf "\n=======\n")))
                   (raise exn))])
  (gunzip "models.tar.gz"))
(untar "models.tar")

(define racket-files
  (sort (for/list ([file (in-directory "models")]
                   #:when (regexp-match #rx"rkt$" (path->string file))
                   #:unless (regexp-match #rx"/[.]_" (path->string file)))
          file)
        string<=?
        #:key path->string))

(for ([file (in-list racket-files)])
  (printf "running ~a\n" file)
  (flush-output)
  (let/ec k
    (parameterize ([error-escape-handler (λ args (k (void)))])
      (dynamic-require file #f)))
  (flush-output (current-error-port))
  (flush-output))

(delete-directory/files tmp-dir)

(module+ test
  (module config info
    (define timeout 200)
    (define random? #t)))
