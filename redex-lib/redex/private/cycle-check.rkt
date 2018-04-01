#lang racket/base
(require racket/match
         (for-template "lang-struct.rkt"))

(provide build-graph-and-check-for-cycles
         check-for-cycles
         build-union-language-nt-neighbors/nt-hole-at-top)

(define (build-graph-and-check-for-cycles stx ntss/stx prodss/stx nt-identifiers
                                          aliases
                                          parent-language-nt-hole-at-top
                                          parent-language-nt-neighbors)

  (define ntss (syntax->datum ntss/stx))
  (define prodss (syntax->datum prodss/stx))

  ;; hash[sym[nt] -o> #t]
  ;; maps all nt aliases to #t
  (define nt-hole-at-top (make-hash))

  ;; hash[sym[nt] -o> (listof sym[nt])
  ;; contains no nt aliases -- at least, it isn't supposed to
  ;; (if you have a possibly-aliased nt, look it up in the
  ;;  alias table before you consult this hash)
  (define nt-neighbors (make-hash))

  (when parent-language-nt-hole-at-top
    (for ([(nt ans) (in-hash parent-language-nt-hole-at-top)])
      (define in-ntss?
        (for/or ([nts (in-list ntss)])
          (for/or ([nt2 (in-list nts)])
            (equal? nt nt2))))
      (unless in-ntss?
        (hash-set! nt-hole-at-top nt ans)
        (hash-set! nt-neighbors nt (hash-ref parent-language-nt-neighbors nt)))))

  (when parent-language-nt-neighbors
    (for ([(nt _) (in-hash parent-language-nt-neighbors)])
      (hash-set! nt-neighbors (hash-ref aliases nt nt) '())))

  (define (add-neighbors-link from/aliased to/aliased)
    (define from (hash-ref aliases from/aliased from/aliased))
    (define to (hash-ref aliases to/aliased to/aliased))
    (hash-set! nt-neighbors from
               (cons to
                     (hash-ref nt-neighbors from))))

  (let loop ()
    (define any-change? #f)
    (for ([nts (in-list ntss)]
          [prods (in-list prodss)])
      (for ([prod (in-list prods)])
        (define (set-these)
          (for ([nt (in-list nts)])
            (unless (hash-ref nt-hole-at-top nt #f)
              (hash-set! nt-hole-at-top nt #t)
              (set! any-change? #t))))
        (match prod
          [`hole (set-these)]
          [`(nt ,name)
           (when (hash-ref nt-hole-at-top name #f)
             (set-these))]
          [(? (λ (x) (member x extend-nt-ellipses)))
           (define parent-language-nt-has-hole?
             (and parent-language-nt-hole-at-top
                  (for/or ([nt (in-list nts)])
                    (hash-ref parent-language-nt-hole-at-top nt #f))))
           (when parent-language-nt-has-hole?
             (set-these))]
          [_
           (void)])))
    (when any-change? (loop)))

  ;; build the graph
  (for ([nts (in-list ntss)]
        [prods (in-list prodss)])
    (define base-nt (car nts))
    (hash-set! nt-neighbors base-nt '())
    (for ([prod (in-list prods)])
      (match prod
        [`(nt ,name) (add-neighbors-link base-nt name)]
        [`(in-hole hole (nt ,name)) (add-neighbors-link base-nt name)]
        [`(in-hole (nt ,name1) (nt ,name2))
         (when (hash-ref nt-hole-at-top name1 #f)
           (add-neighbors-link base-nt name2))]
        [(? (λ (x) (member x extend-nt-ellipses)))
         (when parent-language-nt-hole-at-top
           (when parent-language-nt-neighbors
             (define nt (hash-ref aliases (car nts) (car nts)))
             (for/or ([neighbor (hash-ref parent-language-nt-neighbors nt)])
               (add-neighbors-link base-nt neighbor))))]
        [_
         (void)])))

  (check-for-cycles stx nt-identifiers nt-neighbors)

  (values nt-hole-at-top nt-neighbors))

(define (build-union-language-nt-neighbors/nt-hole-at-top
         aliases
         prefixes
         parent-language-nt-hole-at-tops
         parent-language-nt-neighborss)

  (define nt-hole-at-top (make-hash))

  (define nt-neighbors (make-hash))

  (define (add-prefix prefix parent-nt)
    (if prefix
        (string->symbol (format "~a~a" prefix parent-nt))
        parent-nt))

  (for ([prefix (in-list prefixes)]
        [parent-language-nt-hole-at-top (in-list parent-language-nt-hole-at-tops)])
    (for ([(parent-nt has-hole?) (in-hash parent-language-nt-hole-at-top)])
      (when has-hole?
        (hash-set! nt-hole-at-top
                   (add-prefix prefix parent-nt)
                   #t))))

  (for ([prefix (in-list prefixes)]
        [parent-language-nt-neighbors (in-list parent-language-nt-neighborss)])
    (for ([(parent-nt neighbors) (in-hash parent-language-nt-neighbors)])
      (define nt/prefix (add-prefix prefix parent-nt))
      (define nt (hash-ref aliases nt/prefix nt/prefix))
      (hash-set! nt-neighbors
                 nt
                 (append (hash-ref nt-neighbors nt '())
                         (for/list ([neighbor (in-list neighbors)])
                           (define nt (add-prefix prefix neighbor))
                           (hash-ref aliases nt nt))))))
  (values nt-hole-at-top nt-neighbors))

(define (check-for-cycles stx nt-identifiers nt-neighbors)

  (define cycle
    (for/or ([(nt neighbors) (in-hash nt-neighbors)])
      (define visited (make-hash))
      (for/or ([neighbor (in-list neighbors)])
        (let loop ([current-node neighbor])
          (cond
            [(eq? current-node nt) nt]
            [(hash-ref visited current-node #f) #f]
            [else
             (hash-set! visited current-node #t)
             (for/or ([neighbor (in-list (hash-ref nt-neighbors current-node))])
               (loop neighbor))])))))

  (when cycle

    (define bad-path
      (for/or ([neighbor (in-list (hash-ref nt-neighbors cycle))])
        (let loop ([node neighbor])
          (cond
            [(equal? node cycle) (list node)]
            [else
             (for/or ([neighbor (in-list (hash-ref nt-neighbors node))])
               (define path (loop neighbor))
               (and path (cons node path)))]))))

    (define bad-path/stx-objects
      (for/list ([nt (in-list bad-path)])
        (define stx-lst (hash-ref nt-identifiers nt #f))
        (cond
          [stx-lst
           (define lst (if (syntax? stx-lst) (syntax->list stx-lst) stx-lst))
           (define stx (car lst))
           (datum->syntax stx nt stx)]
          [else nt])))

    (define bad-path-starting-point
      (for/fold ([smallest (car bad-path/stx-objects)])
                ([point (in-list (cdr bad-path/stx-objects))])
        (define smaller?
          (< (or (and (syntax? smallest) (syntax-position smallest)) +inf.0)
             (or (and (syntax? smallest) (syntax-position point)) +inf.0)))
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
    (define bad-path-in-canonical-order/stx-only
      (filter syntax? bad-path-in-canonical-order))
    (raise-syntax-error 'define-language
                        (if (= 1 (length bad-path-in-canonical-order))
                            (format "the non-terminal ~a is defined in terms of itself"
                                    (if (syntax? (car bad-path-in-canonical-order))
                                        (syntax-e (car bad-path-in-canonical-order))
                                        (car bad-path-in-canonical-order)))
                            (format
                             "found a cycle of non-terminals that doesn't consume input:~a"
                             (apply
                              string-append
                              (for/list ([node (in-list bad-path-in-canonical-order)])
                                (format " ~a" (if (syntax? node) (syntax-e node) node))))))
                        stx
                        (and (pair? bad-path-in-canonical-order/stx-only)
                             (car bad-path-in-canonical-order/stx-only))
                        (if (pair? bad-path-in-canonical-order/stx-only)
                            (cdr bad-path-in-canonical-order/stx-only)
                            '()))))
