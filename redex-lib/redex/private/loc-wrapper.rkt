#lang racket/base

(require racket/contract
         racket/math
         racket/treelist
         (for-syntax racket/base)
         (for-syntax "loc-wrapper-ct.rkt")
         "loc-wrapper-rt.rkt")

(define-syntax (to-lw stx) 
  (syntax-case stx ()
    [(_ stx)
     (to-lw/proc #'stx)]))
(define-syntax (to-lw/uq stx)
  (syntax-case stx ()
    [(_ stx)
     (to-lw/uq/proc #'stx)]))

(define pnum (and/c number? (or/c zero? positive?)))

(provide/contract
 (struct lw ((e any/c)
             (line pnum)
             (line-span pnum)
             (column pnum)
             (column-span pnum)
             (unq? boolean?)
             (metafunction? boolean?)
             (pict-tag (or/c string? treelist? #f)))))

(provide to-lw
         to-lw/uq
         curly-quotes-for-strings
         build-lw)
