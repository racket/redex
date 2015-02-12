#lang racket/base
(require data/enumerate/lib
         racket/function
         racket/list
         racket/contract/base)
(provide enum?
         enum-size
         finite-enum?
         (contract-out
          (rename to-nat encode (-> enum? any/c exact-nonnegative-integer?))
          (rename from-nat decode (-> enum? exact-nonnegative-integer? any/c)))
         empty/e
         fin/e
         single/e
         or/e
         append/e
         cons/e
         map/e
         except/e 
         thunk/e
         list/e
         listof/e
         hash-traverse/e
         
         enum->list
         take/e
         fold-enum

         nat/e
         range/e
         slice/e
         nat+/e

         ;; Base type enumerators
         any/e
         (rename-out [symbol/e var/e])
         var-prefix/e
         two-way-number/e
         integer/e
         bool/e
         two-way-real/e
         string/e)

(define (var-prefix/e s)
  (define as-str (symbol->string s))
  (map/e (compose string->symbol
                  (curry string-append as-str)
                  symbol->string)
         (compose string->symbol
                  list->string
                  (curry (flip drop) (string-length as-str))
                  string->list
                  symbol->string)
         symbol/e
         #:contract (and/c symbol?
                           (let ([reg (regexp (format "^~a" (regexp-quote as-str)))])
                             (λ (x) 
                               (regexp-match? reg (symbol->string x)))))))

(define (flip f)
  (λ (x y)
     (f y x)))

(define base/e
  (or/e (fin/e '())
        (cons two-way-number/e number?)
        string/e
        bool/e
        symbol/e))

(define any/e
  (delay/e
   (or/e (cons base/e (negate pair?))
         (cons (cons/e any/e any/e) pair?))
   #:size +inf.0))
