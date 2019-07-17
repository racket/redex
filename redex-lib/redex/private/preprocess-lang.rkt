#lang racket/base
(require (for-syntax racket/base
                     racket/math)
         racket/bool
         racket/contract
         racket/list
         racket/math
         racket/match
         racket/set
         racket/promise
         "lang-struct.rkt"
         "match-a-pattern.rkt")

(provide
 (contract-out
  [sep-lang (-> (listof nt?)
                (or/c #f (hash/c symbol? (listof any/c)))
                (values (listof nt?)
                        (listof nt?)
                        (hash/c symbol? boolean?)))]
  [used-vars (-> (listof nt?)
                 (listof symbol?))]
  [can-enumerate? (-> any/c 
                      (hash/c symbol? any/c) 
                      (promise/c (hash/c symbol? any/c))
                      boolean?)]))

;; sep-lang : lang hash[sym -o> (listof any)] -> lang lang
;; EFFECT: sorts the lists in clang-all-ht to match the order
;;         in which the productions in the result are sorted
;; topologically sorts non-terminals by dependency
;; sorts rhs's so that recursive ones go last
(define (sep-lang lang clang-all-ht/f)
  (define (filter-edges edges lang)
    (for/fold ([filtered (hash)])
              ([nt (in-list lang)])
      (define name (nt-name nt))
      (hash-set filtered name (hash-ref edges name))))
  (define edges (find-edges lang))
  (define cyclic-nts (find-cycles edges))
  (define-values (cyclic non-cyclic)
    (partition (λ (nt)
                  (set-member? cyclic-nts (nt-name nt)))
               lang))
  ;; topological sort
  (define sorted-finite
    (topo-sort non-cyclic
               (filter-edges edges non-cyclic)))
  ;; rhs sort
  (define-values (sorted-cyclic unsolvables)
    (sort-productions cyclic clang-all-ht/f))
  (values sorted-finite
          sorted-cyclic
          (build-cant-enumerate-table lang edges unsolvables)))

;; find-edges : lang -> (hash[symbol] -o> (setof (listof symbol)))
(define (find-edges lang)
  (foldl
   (λ (nt m)
      (hash-set
       m (nt-name nt)
       (fold-map/set
        (λ (rhs)
           (let loop ([pat (rhs-pattern rhs)]
                      [s (set)])
             (match-a-pattern
               pat
               [`any s]
               [`number s]
               [`string s]
               [`natural s]
               [`integer s]
               [`real s]
               [`boolean s]
               [`variable s]
               [`(variable-except ,var ...) s]
               [`(variable-prefix ,var) s]
               [`variable-not-otherwise-mentioned s]
               [`hole s]
               [`(nt ,id) (set-add s id)]
               [`(name ,var ,pat)
                (loop pat s)]
               [`(mismatch-name ,name ,pat)
                (loop pat s)]
               [`(in-hole ,p1 ,p2)
                (set-union (loop p1 s)
                           (loop p2 s))]
               [`(hide-hole ,p) (loop p s)]
               [`(side-condition ,p ,_1 ,_2) (loop p s)]
               [`(cross ,id) (set-add s id)]
               [`(list ,sub-pats ...)
                (fold-map/set
                 (λ (sub-pat)
                    (match sub-pat
                      [`(repeat ,pat ,name ,mismatch)
                       (loop pat s)]
                      [else (loop sub-pat s)]))
                 sub-pats)]
               [(? (compose not pair?)) s])))
        (nt-rhs nt))))
   (hash)
   lang))

;; find-cycles : (hash[symbol -o> (setof symbol)]) -> (setof symbol)
(define (find-cycles edges)
  (foldl
   (λ (v s)
      (if (let rec ([cur v]
                    [seen (set)])
            (cond [(set-member? seen cur) #t]
                  [else
                   (ormap
                    (λ (next)
                       (rec next
                            (set-add seen cur)))
                    (set->list (hash-ref edges cur (set))))]))
          (set-add s v)
          s))
   (set)
   (hash-keys edges)))

;; calls-rec? : pat (setof symbol) -> bool
(define (calls-rec? pat recs)
  (let rec ([pat pat])
    (match-a-pattern
     pat
     [`any #f]
     [`number #f]
     [`string #f]
     [`natural #f]
     [`integer #f]
     [`real #f]
     [`boolean #f]
     [`variable #f]
     [`(variable-except ,s ...) #f]
     [`(variable-prefix ,s) #f]
     [`variable-not-otherwise-mentioned #f]
     [`hole #f]
     [`(nt ,id) (set-member? recs id)]
     [`(name ,name ,pat)
      (rec pat)]
     [`(mismatch-name ,name ,pat)
      (rec pat)]
     [`(in-hole ,p1 ,p2)
      (or (rec p1)
          (rec p2))]
     [`(hide-hole ,p) (rec p)]
     [`(side-condition ,p ,g ,e) #f]
     [`(cross ,s) (set-member? recs s)]
     [`(list ,sub-pats ...)
      (ormap (λ (sub-pat)
                (match sub-pat
                  [`(repeat ,pat ,name ,mismatch)
                   (rec pat)]
                  [else (rec sub-pat)]))
             sub-pats)]
     [(? (compose not pair?)) #f])))
      
;; topo-sort : lang (hash[symbol] -o> (setof symbol)) -> lang
(define (topo-sort lang edges)
  (define (find-top rem edges)
    (let find ([rem rem])
      (let ([v (car rem)])
        (let check ([vs (hash-keys edges)])
          (cond [(empty? vs) v]
                [(set-member? (hash-ref edges (car vs))
                              v)
                 (find (cdr rem))]
                [else (check (cdr vs))])))))
  (let loop ([rem (hash-keys edges)]
             [edges edges]
             [out-lang '()])
    (cond [(empty? rem) out-lang]
          [else
           (let ([v (find-top rem edges)])
             (loop (remove v rem)
                   (hash-remove edges v)
                   (cons
                    (find-nt lang v)
                    out-lang)))])))

;; find-nt : lang, symbol -> nt
(define (find-nt lang name)
  (findf (λ (nt)
            (eq? name (nt-name nt)))
         lang))


;; Problem: we need to find an ordering of the productions of each of
;; the metavariables such that the graph induced by the first
;; productions in each case has no cycles.
;; spanning-tree : HyperGraph -> (Listof (List Index (Setof NTName))) (Listof NTName)
(define (spanning-tree hg)
  (define init-vertices (hash-keys hg))
  (let loop ([edges (hash)]
             [vertices init-vertices]
             [time (length init-vertices)])
    (cond
      [(zero? time)
       (values edges vertices)]
      [else
       (match-define (cons v vs) vertices)
       (define good-edge
         (findf (λ (e) (andmap (λ (v2) (not (member v2 vertices))) (set->list (second e))))
                (hash-ref hg v)))
       (cond [good-edge
              (loop (hash-set edges v good-edge)
                    vs
                    (sub1 time))]
             [else
              (loop edges (append vs (list v)) (sub1 time))])])))

;; A HyperGraph is a Hash NTName (Listof (List Index (Setof NTName)))
;; associating each non-terminal to a list of out-going edges
(define (hypergraph lang)
  (for/hash ([nt (in-list lang)])
    (define out-edges
      (for/list ([i (in-naturals)]
                 [rhs (in-list (nt-rhs nt))])
        (list i (directly-used-nts (rhs-pattern rhs)))))
    (values (nt-name nt) out-edges)))

;; sort-productions : lang (or/c #f (hash[symbol -o> (list/c any)]))
;;                  -> lang
;; sorts the language
;;   SIDE EFFECT: if clang-all-ht/f is not #f, sorts it
(define (sort-productions lang clang-all-ht/f)
  (define-values (spanner unsolvables) (spanning-tree (hypergraph lang)))
  (define sorted
    (for/list ([cur-nt (in-list lang)])
      (match cur-nt
        [(nt name productions)
         (cond
           [(hash-has-key? spanner name)
            (define the-edge (first (hash-ref spanner name)))

            ;; less than if the left is the chosen one and the right is not
            (define (less-than? i1 i2)
              (and (equal? i1 the-edge)
                   (not (equal? i2 the-edge))))

            (define production-vec (apply vector productions))
            (define permutation
              (sort (build-list (vector-length production-vec) values)
                    less-than?
                    #:cache-keys? #t))
            (when clang-all-ht/f
              (define clang-all-ht-nt-vec (apply vector (hash-ref clang-all-ht/f name)))
              (hash-set! clang-all-ht/f name
                         (for/list ([i (in-list permutation)])
                           (vector-ref clang-all-ht-nt-vec i))))
            (nt name
                (for/list ([i (in-list permutation)])
                  (vector-ref production-vec i)))]
           [else (nt name productions)])])))
  (values sorted unsolvables))

;; A NTName is a symbol representing the name of a non-terminal

;; directly-used-nts : pat -> (setof symbol)
(define (directly-used-nts pat)
  (match-a-pattern/single-base-case pat
    [`(name ,n ,p)
     (directly-used-nts p)]
    [`(mismatch-name ,n ,p)
     (directly-used-nts p)]
    [`(in-hole ,p1 ,p2)
     (set-union (directly-used-nts p1)
                (directly-used-nts p2))]
    [`(hide-hole ,p)
     (directly-used-nts p)]
    [`(side-condition ,p ,c ,v)
     (directly-used-nts p)]
    [`(list ,sub-pats ...)
     (fold-map/set
      (λ (sub-pat)
         (match sub-pat
           ;; Not a direct reference since an empty list can always be
           ;; enumerated
           [`(repeat ,p ,n ,m) (set)]
           [else (directly-used-nts sub-pat)]))
      sub-pats)]
    [_ (match pat
         [`(nt ,id) (set id)]
         [`(cross ,id) (set id)]
         [_ (set)])]))

;; used-vars : lang -> (listof symbol)
(define (used-vars lang)
  (set->list
   (fold-map/set
    (λ (the-nt)
       (fold-map/set
        (λ (the-rhs)
           (let loop ([pat (rhs-pattern the-rhs)])
             (match-a-pattern
              pat
              [`any (set)]
              [`number (set)]
              [`string (set)]
              [`natural (set)]
              [`integer (set)]
              [`real (set)]
              [`boolean (set)]
              [`variable (set)]
              [`(variable-except ,s ...) (set)]
              [`(variable-prefix ,s) (set)]
              [`variable-not-otherwise-mentioned (set)]
              [`hole (set)]
              [`(nt ,id) (set)]
              [`(name ,name ,pat) (set)]
              [`(mismatch-name ,name ,pat) (set)]
              [`(in-hole ,p1 ,p2)
               (set-union (loop p1)
                          (loop p2))]
              [`(hide-hole ,p) (loop p)]
              [`(side-condition ,p ,g ,e) (set)] 
              [`(cross ,s) (set)]
              [`(list ,sub-pats ...)
               (fold-map/set
                (λ (sub-pat)
                   (match sub-pat
                     [`(repeat ,pat ,name ,mismatch)
                      (loop pat)]
                     [else (loop sub-pat)]))
                sub-pats)]
              [(? (compose not pair?))
               (if (symbol? pat)
                   (set pat)
                   (set))])))
        (nt-rhs the-nt)))
    lang)))

;; fold-map/set : (a -> setof b) (listof a) -> (setof b)
(define (fold-map/set f l)
  (for/fold ([acc (set)])
            ([x (in-list l)])
    (set-union (f x) acc)))

(define (pos-inf? n)
  (and (infinite? n)
       (positive? n)))

(define (my-max default new)
  (if (> new default)
      new
      default))

;; Short circuits for +inf
(define-syntax (for/max stx)
  (syntax-case stx ()
    [(_ clauses . defs+exprs)
     (with-syntax ([original stx])
       #'(for/fold/derived original
                           ([current-max -inf.0])
                           clauses
           #:break (pos-inf? current-max)
           (my-max current-max
                   (let () . defs+exprs))))]))

(define (build-cant-enumerate-table lang edges unsolvables)
  ;; cant-enumerate-table : hash[sym[nt] -o> boolean]
  (define cant-enumerate-table (make-hash))
  
  ;; fill in base cases
  (for ([nt (in-list lang)])
    (define name (nt-name nt))
    (unless (for/and ([rhs (in-list (nt-rhs nt))])
              (can-enumerate? (rhs-pattern rhs) #f #f))
      (hash-set! cant-enumerate-table name #t)))
  
  ;; short-circuiting graph traversal
  (define visited (make-hash))
  (define (cant-enumerate-nt/fill-table nt-sym)
    (hash-ref 
     cant-enumerate-table
     nt-sym
     (λ ()
       (define ans
         (cond
           [(hash-ref visited nt-sym #f) #f]
           [else 
            (hash-set! visited nt-sym #t)
            ;; the '() in the next line is supicious; take it out and see tests fail
            ;; that probably should be fixed not by putting it back....
            (for/or ([next (in-set (hash-ref edges nt-sym '()))])
              (cant-enumerate-nt/fill-table next))]))
       (hash-set! cant-enumerate-table nt-sym ans)
       ans)))
  
  ;; fill in the entire table
  (for ([nt (in-list lang)])
    (cant-enumerate-nt/fill-table (nt-name nt)))
  (for ([name (in-list unsolvables)])
    (hash-set! cant-enumerate-table name #t))
  cant-enumerate-table)
    
;; can-enumerate? : any/c hash[sym -o> any[boolean]] (promise hash[sym -o> any[boolean]])
(define (can-enumerate? pat can-enumerate-ht cross-can-enumerate-ht)
  (let loop ([pat pat] [inside-ellipsis? #f])
    (match-a-pattern
     pat
     [`any #t]
     [`number #t]
     [`string #t]
     [`natural #t]
     [`integer #t]
     [`real #t]
     [`boolean #t]
     [`variable #t]
     [`(variable-except ,s ...) #t]
     [`(variable-prefix ,s) #t]
     [`variable-not-otherwise-mentioned #t]
     [`hole #t]
     [`(nt ,id) 
      (or (not can-enumerate-ht)
          (and (hash-ref can-enumerate-ht id) #t))]
     [`(name ,n ,pat) (loop pat inside-ellipsis?)]
     [`(mismatch-name ,n ,pat) (and (not inside-ellipsis?) (loop pat inside-ellipsis?))]
     [`(in-hole ,p1 ,p2) (and (loop p1 inside-ellipsis?) (loop p2 inside-ellipsis?))]
     [`(hide-hole ,p) (loop p inside-ellipsis?)]
     [`(side-condition ,p ,g ,e) #f]
     [`(cross ,id) 
      (or (not cross-can-enumerate-ht) 
          (and (hash-ref (force cross-can-enumerate-ht) id)
               #t))]
     [`(list ,sub-pats ...)
      (for/and ([sub-pat (in-list sub-pats)])
        (match sub-pat
          [`(repeat ,pat ,_ ,_) (loop pat #t)]
          [else (loop sub-pat inside-ellipsis?)]))]
     [(? (compose not pair?)) #t])))
