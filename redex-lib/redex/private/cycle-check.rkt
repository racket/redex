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

    (define full-path (cons cycle bad-path))
    (define all/backwards (for/list ([nt (in-list (reverse bad-path))])
                            (define stx-lst (hash-ref nt-identifiers nt))
                            (define lst (if (syntax? stx-lst) (syntax->list stx-lst) stx-lst))
                            (define stx (car lst))
                            (datum->syntax stx nt stx)))
    (raise-syntax-error 'define-language
                        (if (= 1 (length bad-path))
                            (format "the non-terminal ~a is defined in terms of itself"
                                    (car bad-path))
                            (format
                             "found a cycle of non-terminals that doesn't consume input:~a"
                             (apply
                              string-append
                              (for/list ([node (in-list full-path)])
                                (format " ~a" node)))))
                        stx
                        (car all/backwards)
                        (cdr all/backwards))))
