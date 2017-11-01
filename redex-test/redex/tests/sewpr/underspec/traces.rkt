#lang scheme/gui

(require redex "oo.rkt" "../traces-colors.rkt" "../space-snip.rkt")

(define first/second-attempt-terms
  (list 
   '(0
     (+
      (set (+ (get) 1))
      (set (- (get) 1))))
   
   '(0
     ((λ X (+ X (set (- (get) 1))))
      (set (+ (get) 1))))
   
   '(0
     ((λ X (+ (set (+ (get) 1)) X))
      (set (- (get) 1))))
   
   '(0
     ((λ X (+ X (set (- (get) 1))))
      (set ((λ X1 (+ X1 1)) (get)))))
   '(0
     ((λ X (+ X (set (- (get) 1))))
      (set ((λ X1 (+ (get) X1)) 1))))))

(define (remove-duplicates tns)
  (let loop ([tns tns])
    (cond
      [(null? tns) null]
      [else (cons (car tns) 
                  (loop (remove* (list (car tns)) (cdr tns))))])))

(define (has-inside? candidate term)
  (let loop ([x (term-node-expr term)])
    (cond
      [(equal? x candidate) #t]
      [(list? x) (ormap loop x)]
      [else #f])))


(with-colors
 (λ ()
 
   (parameterize ([reduction-steps-cutoff 20])
     (traces/ps sch1-red 
                main-example
                "first-attempt.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:filter
                (λ (term red) (member term first/second-attempt-terms))
                #:layout
                (λ (tn)
                  (let* ([root (find-root tn)]
                         [first-row (list root)]
                         [second-row (term-node-children (find-root tn))]
                         [third-row (apply append (map term-node-children second-row))])
                    (term-node-set-position! root (+ (term-node-x root) 100) (term-node-y root))
                    (line-up-under first-row second-row)
                    (line-up-under second-row third-row))))

     (parameterize ([initial-char-width 
                     (lambda (x)
                       (cond
                         [(member x (list
                                     '(0
                                       ((λ X (+ (set (+ (get) 1)) X))
                                        (set (- (get) 1))))
                                     '(0
                                       ((λ X (+ X (set (- (get) 1))))
                                        (set (+ (get) 1))))))
                          30]
                         [else 40]))])
       (traces/ps sch2-red 
                  main-example
                  "second-attempt.ps"
                  #:post-process rewrite-pb
                  #:edge-label-font edge-label-font
                  #:edge-labels? #f
                  #:filter
                  (λ (term red) (member term first/second-attempt-terms))
                  #:layout
                  (λ (tn)
                    (let* ([root (find-root tn)]
                           [first-row (list root)]
                           [second-row (term-node-children (find-root tn))]
                           [third-row (apply append (map term-node-children second-row))])
                      (term-node-set-position! root (+ (term-node-x root) 100) (term-node-y root))
                      (line-up-under first-row second-row 4 14)
                      (line-up-under second-row third-row 4 14))))))
   
   
   (traces/ps red! 
              main-example
              "left-to-right.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:layout
              (λ (tns)
                (let* ([root (find-root tns)]
                       [tn1 (horizontal-line root 1 #:gap 80)]
                       [tn2 (vertical-line tn1 1 #:gap 26)]
                       [tn3 (horizontal-line tn2 1 #:left? #t #:gap 60)]
                       [_ (term-node-set-position! tn3 (term-node-x tn3) (- (term-node-y tn3) 30))]
                       [tn4 (vertical-line tn3 2 #:gap 26)]
                       [tn5 (horizontal-line tn4 2 #:gap 40)])
                  (slide-to-zero tns))))))


;                                             
;                                             
;                                             
;                                             
;  ;;;                                        
;                                             
;  ;;; ;;; ;;   ;;;;   ;;;;;  ;;; ;;    ;;;;  
;  ;;; ;;;;;;; ;;; ;; ;;;;;;; ;;;;;;;  ;; ;;; 
;  ;;; ;;; ;;; ;;;    ;;  ;;; ;;; ;;; ;;; ;;; 
;  ;;; ;;; ;;;  ;;;;    ;;;;; ;;; ;;; ;;;;;;; 
;  ;;; ;;; ;;;    ;;; ;;; ;;; ;;; ;;; ;;;     
;  ;;; ;;; ;;; ;; ;;; ;;; ;;; ;;; ;;;  ;;;;;; 
;  ;;; ;;; ;;;  ;;;;   ;;;;;; ;;; ;;;   ;;;;  
;                                             
;                                             
;                                             
;                                             



(define (insane-char-width expr)
  (cond
    [(member 
      expr 
      (list '(1
              (+ 1 (set (- 0 1))))
            '(0
              (+ (set 1) (set -1)))
            '(-1
              (+ (set (+ 0 1)) -1))))
     ;; 22 is two lines, but 21 and 20 go to 4 lines.
     20]
    [else 22]))
   
(define (insane-graph-pasteboard-mixin %)
  (class %
    (define/override (draw-single-edge dc dx dy from to from-x from-y to-x to-y arrow-point-ok?)
      (let* ([from-tn (send from get-term-node)]
             [to-tn (send to get-term-node)]
             [to-expr (term-node-expr to-tn)])
        (cond
          [(equal? to-expr '(-1
                             (+
                              (set (+ (get) 1))
                              -1)))
           (let ([mid-y (/ (+ from-y to-y) 2)]
                 [mid-x (min (term-node-x from-tn) (term-node-x to-tn))])
             (connect dc dx dy from-x from-y mid-x mid-y to-x to-y))]
          [(equal? to-expr '(1
                             (+
                              1
                              (set (- (get) 1)))))
           (let ([mid-y (/ (+ from-y to-y) 2)]
                 [mid-x (max (+ (term-node-x from-tn) (term-node-width from-tn))
                             (+ (term-node-x to-tn) (term-node-width to-tn)))])
             (connect dc dx dy from-x from-y mid-x mid-y to-x to-y))]
          [else
           (super draw-single-edge dc dx dy from to from-x from-y to-x to-y arrow-point-ok?)])))
    
    (define point1 (make-object point%))
    (define point2 (make-object point%))
    (define point3 (make-object point%))
    (define point4 (make-object point%))
    
    (inherit update-arrowhead-polygon)
    (define/private (connect dc dx dy from-x from-y mid-x mid-y to-x to-y)
      (send dc draw-spline 
            (+ dx from-x) (+ dy from-y)
            (+ dx mid-x) (+ dy mid-y)
            (+ dx to-x) (+ dy to-y))
      (update-arrowhead-polygon mid-x mid-y to-x to-y
                                point1 point2 point3 point4)
      (send dc draw-polygon (list point1 point2 point3 point4) dx dy))
    
    (super-new)))

(with-colors
 (λ ()
   (parameterize ([initial-char-width insane-char-width]
                  [reduction-steps-cutoff 100])
     (traces/ps C-red
                main-example
                "insane.ps"
                #:post-process rewrite-pb
                #:edge-labels? #f
                #:graph-pasteboard-mixin insane-graph-pasteboard-mixin
                #:layout 
                (λ (tns)
                  (define (next-level level)
                    (remove-duplicates (apply append (map term-node-children level))))
                  (define (has-no-get? tn) (not (has-inside? 'get tn)))
                  (let* ([level0 (list (find-root tns))]
                         [level1 (sort (next-level level0) < #:key (λ (x) (if (has-inside? '(- 0 1) x) 0 1)))]
                         [level2 (filter has-no-get? (next-level level1))]
                         [level3 (sort (next-level level2) < #:key (λ (x) (if (has-inside? '(set -1) x) 0 1)))]
                         [level4 (sort (next-level level3) < #:key (λ (x) (cond
                                                                            [(has-inside? '(+ 0 1) x) 0]
                                                                            [(has-inside? '(- 0 1) x) 2]
                                                                            [else 1])))]
                         [level5 (next-level level4)]
                         [level6 (next-level level5)]
                         [level7 (next-level level6)]
                         [mixed-up-levels (list level0 level1 level2 level3 level4 level5 level6 level7)])
                    (let loop ([this-level (car mixed-up-levels)]
                               [levels (cdr mixed-up-levels)])
                      (cond
                        [(null? levels) (void)]
                        [else
                         (line-up-under this-level (car levels) 4 12)
                         (loop (car levels) (cdr levels))]))
                    (let* ([left-branch0 (ormap (λ (x) (and (not (member x level2)) x)) (term-node-children (list-ref level1 0)))]
                           [right-branch0 (ormap (λ (x) (and (not (member x level2)) x)) (term-node-children (list-ref level1 1)))]
                           [left-branch1 (ormap (λ (x) (and (not (member x level3)) x)) (term-node-children left-branch0))]
                           [right-branch1 (ormap (λ (x) (and (not (member x level3)) x)) (term-node-children right-branch0))])
                      (center-left (list-ref level2 0) left-branch0 #:gap 2)
                      (center-right (list-ref level2 0) right-branch0 #:gap 2)
                      (center-below left-branch0 left-branch1)
                      (center-below right-branch0 right-branch1)
                      (term-node-set-position! left-branch1 
                                               (term-node-x left-branch1) 
                                               (- (term-node-y (list-ref level7 0)) 12))
                      (term-node-set-position! right-branch1 
                                               (term-node-x right-branch1)
                                               (- (term-node-y (list-ref level7 1)) 12))
                      
                      (let* ([x (vertical-line left-branch1 1 #:gap 14)]
                             [y (vertical-line x 1 #:gap 20)])
                        (horizontal-line y 2))
                      (let* ([x (vertical-line right-branch1 2 #:gap 14)]
                             [y (horizontal-line x 1 #:left? #t)])
                        (vertical-line y 1 #:up? #t #:gap 16)))
                    (slide-to-zero tns)))))))


;                                                           
;                                                           
;                                                           
;                                                           
;    ;                                                      
;  ;;;                                                      
;  ;;;; ;;; ;;; ;;;  ;;;   ;;; ;;; ;;; ;;;;;  ;;; ;;; ;;;;  
;  ;;;; ;;; ;;; ;;; ;;;;;  ;;; ;;; ;;;;;;;;;; ;;; ;;;;;; ;; 
;  ;;;   ;;;;;;;;; ;;; ;;;  ;;;;;;;;; ;;  ;;;  ;; ;; ;;;    
;  ;;;   ;;;; ;;;; ;;; ;;;  ;;;; ;;;;   ;;;;;  ;; ;;  ;;;;  
;  ;;;   ;;;; ;;;; ;;; ;;;  ;;;; ;;;; ;;; ;;;  ;; ;;    ;;; 
;  ;;;;   ;;   ;;   ;;;;;    ;;   ;;  ;;; ;;;   ;;;  ;; ;;; 
;   ;;;   ;;   ;;    ;;;     ;;   ;;   ;;;;;;   ;;;   ;;;;  
;                                             ;;;;;         
;                                             ;;;;          
;                                                           
;                                                           


;; twoways.ps
(with-colors
 (λ ()
   (parameterize ([initial-char-width
                   (λ (x)
                     (cond
                       [(equal? x main-example) 30]
                       [else 30]))])
     (traces/ps sch3-red
                main-example
                "twoways.ps"
                #:post-process rewrite-pb              
                #:edge-labels? #f
                #:layout
                (λ (tns)
                  (let* ([root (find-root tns)]
                         [children (term-node-children root)])
                    (let-values ([(up-child down-child)
                                  (let ([children (term-node-children root)]
                                        [up-key '(+ X (set (- (get) 1)))])
                                    (cond
                                      [(has-inside? up-key (car children))
                                       (apply values children)]
                                      [(has-inside? up-key (cadr children))
                                       (apply values (reverse children))]
                                      [else (error 'twoways "did not find term")]))])
                      (center-above root up-child #:gap 12)
                      
                      (let* ([t1 (vertical-line up-child 2 #:up? #t #:gap 12)]
                             [t2 (horizontal-line t1 1 #:gap 12)]
                             [t3 (vertical-line t2 5 #:gap 12)])
                        (void))
                      
                      (center-below root down-child #:gap 12)
                      
                      (let* ([t1 (vertical-line down-child 2 #:gap 12)]
                             [t2 (horizontal-line t1 1 #:gap 12)]
                             [t3 (vertical-line t2 5 #:up? #t #:gap 12)])
                        (void))))
                  
                  (slide-to-zero tns))))))

