#lang racket/base
(require racket/match)

(provide check-for-cycles)

(define (check-for-cycles stx ntss/stx prodss/stx nt-identifiers)

  (define ntss (syntax->datum ntss/stx))
  (define prodss (syntax->datum prodss/stx))
  
  ;; hash[sym[nt] -o> #t]
  (define produces-hole (make-hash))
  (let loop ()
    (define any-change? #f)
    (for ([nts (in-list ntss)]
          [prods (in-list prodss)])
      (for ([prod (in-list prods)])
        (define (set-these)
          (for ([nt (in-list nts)])
            (unless (hash-ref produces-hole nt #f)
              (hash-set! produces-hole nt #t)
              (set! any-change? #t))))
        (match prod
          [`hole (set-these)]
          [`(nt ,name) 
           (when (hash-ref produces-hole name #f)
             (set-these))]
          [_
           (void)])))
    (when any-change? (loop)))
  
  ;; hash[sym[nt] -o> (listof sym[nt])
  (define neighbors-table (make-hash))
  
  ;; build the graph
  (for ([nts (in-list ntss)]
        [prods (in-list prodss)])
    (define base-nt (car nts))
    (for ([nt (in-list (cdr nts))])
      (hash-set! neighbors-table nt (list base-nt)))
    (hash-set! neighbors-table base-nt '())
    (for ([prod (in-list prods)])
      (define (add-link name)
        (hash-set! neighbors-table base-nt (cons name (hash-ref neighbors-table base-nt))))
      (match prod
        [`(nt ,name) (add-link name)]
        [`(in-hole hole (nt ,name)) (add-link name)]
        [`(in-hole (nt ,name1) (nt ,name2))
         (when (hash-ref produces-hole name1 #f)
           (add-link name2))]
        [_
         (void)])))
  
  ;; traverse the graph looking for cycles
  (define cycle
    (for/or ([(nt neighbors) (in-hash neighbors-table)])
      (define visited (make-hash))
      (for/or ([neighbor (in-list neighbors)]) 
        (let loop ([current-node neighbor])
          (cond
            [(eq? current-node nt) nt]
            [(hash-ref visited current-node #f) #f]
            [else
             (hash-set! visited current-node #t)
             (for/or ([neighbor (in-list (hash-ref neighbors-table current-node))])
               (loop neighbor))])))))
  
  (when cycle

    (define bad-path
      (for/or ([neighbor (in-list (hash-ref neighbors-table cycle))])
        (let loop ([node neighbor])
          (cond
            [(equal? node cycle) (list node)]
            [else
             (for/or ([neighbor (in-list (hash-ref neighbors-table node))])
               (define path (loop neighbor))
               (and path (cons node path)))]))))

    (define bad-path/stx-objects
      (for/list ([nt (in-list bad-path)])
        (define stx-lst (hash-ref nt-identifiers nt))
        (define lst (if (syntax? stx-lst) (syntax->list stx-lst) stx-lst))
        (define stx (car lst))
        (datum->syntax stx nt stx)))

    (define bad-path-starting-point
      (for/fold ([smallest (car bad-path/stx-objects)])
                ([point (in-list (cdr bad-path/stx-objects))])
        (define smaller?
          (< (or (syntax-position smallest) +inf.0)
             (or (syntax-position point) +inf.0)))
        (if smaller?
            smallest
            point)))
    (define bad-path-in-canonical-order
      (let loop ([bad-path bad-path/stx-objects])
        (cond
          [(equal? bad-path-starting-point (car bad-path))
           bad-path]
          [else
           (loop (append (cdr bad-path) (list (car bad-path))))])))
    (define full-path (cons (car (reverse bad-path-in-canonical-order))
                            bad-path-in-canonical-order))
    (raise-syntax-error 'define-language
                        (if (= 1 (length bad-path-in-canonical-order))
                            (format "the non-terminal ~a is defined in terms of itself"
                                    (syntax-e (car bad-path-in-canonical-order)))
                            (format
                             "found a cycle of non-terminals that doesn't consume input:~a"
                             (apply
                              string-append
                              (for/list ([node (in-list bad-path-in-canonical-order)])
                                (format " ~a" (syntax-e node))))))
                        stx
                        (car bad-path-in-canonical-order)
                        (cdr bad-path-in-canonical-order))))
