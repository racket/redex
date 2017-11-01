#lang scheme

(require scheme/runtime-path)

(define test-files
  '("basics/test.ss"
    "iswim/test.ss"
    "iswim/test-2.ss"
    "extend/test.ss"
    "ck/test.ss"
    "ck/iswim-test.ss"
    "types/test.ss"
    "underspec/test.ss"
    "cont/test.ss"))

(define-runtime-path here ".")

(define (run-tests x)
  (parameterize ([current-print void])
    (printf "running ~s\n" x)
    (dynamic-require (build-path here x) #f)
    (printf "done\n")))

(for-each run-tests test-files)
