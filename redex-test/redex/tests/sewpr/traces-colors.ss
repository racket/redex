#lang scheme/gui
(require redex)

(define (with-colors t)
  (parameterize ([light-pen-color "black"]
                 [light-brush-color "white"]
                 [light-text-color "black"])
    (t)))

(require texpict/mrpict "../redex-latex-config/pict-config-setup.ss")
(send (current-ps-setup) set-file "junk.ps")
(dc-for-text-size (new post-script-dc% [interactive #f]))
(pict-config-setup)

(define edge-label-font
  (send the-font-list find-or-create-font
        (label-font-size) 
        (default-style) ;; expected to be just a string
        'default
        'normal
        'normal))

(define default-gap (make-parameter 40))

;; -> term-node
;; puts the children in a horizontal line centered along the center of 'orig-tn'
;; returns the last one in the line (in order to start a new line)
(define (horizontal-line orig-tn count #:gap [gap (default-gap)] #:left? [left? #f])
  (let loop ([tn orig-tn]
             [i 0])
    (cond
      [(= i count) tn]
      [else
       (let ([child (first-child-of tn 'horizontal-line)])
         (term-node-set-position!
          child
          (if left? 
              (- (term-node-x tn) (term-node-width child) gap)
              (+ (term-node-x tn) (term-node-width tn) gap))
          (+ (term-node-y orig-tn) 
             (/ (term-node-height orig-tn) 2)
             (/ (term-node-height child) -2)))
         (loop child (+ i 1)))])))

;; like horizontal-line, but vertically.
(define (vertical-line orig-tn count #:gap [gap (default-gap)] #:up? [up? #f])
  (let loop ([tn orig-tn]
             [i 0])
    (cond
      [(= i count) tn]
      [else
       (let ([child (first-child-of tn 'horizontal-line)])
         (term-node-set-position!
          child
          (+ (term-node-x orig-tn) 
             (/ (term-node-width orig-tn) 2)
             (/ (term-node-width child) -2))
          (if up?
              (- (term-node-y tn) (term-node-height child) gap)
              (+ (term-node-y tn) (term-node-height tn) gap)))
         (loop child (+ i 1)))])))
       

(define (first-child-of tn sym)
  (let ([children (term-node-children tn)])
    (cond
      [(null? children) (error sym "term node has no children ~s" (term-node-expr tn))]
      [(null? (cdr children))
       (car children)]
      [else
       (error sym "term node has ~a children ~s" 
              (length (term-node-children tn))
              (term-node-expr tn))])))

(define (center-below main other #:gap [gap (default-gap)])
  (term-node-set-position! 
   other
   (+ (term-node-x main)
      (/ (term-node-width main) 2)
      (/ (term-node-width other) -2))
   (+ (term-node-y main)
      (term-node-height main)
      gap)))


(define (center-above main other #:gap [gap (default-gap)])
  (term-node-set-position! 
   other
   (+ (term-node-x main)
      (/ (term-node-width main) 2)
      (/ (term-node-width other) -2))
   (- (term-node-y main)
      (term-node-height other)
      gap)))

(define (center-left main other #:gap [gap (default-gap)])
  (term-node-set-position! 
   other
   (- (term-node-x main)
      (term-node-width other)
      gap)
   (+ (term-node-y main)
      (/ (term-node-height main) 2)
      (/ (term-node-height other) -2))))

(define (center-right main other #:gap [gap (default-gap)])
  (term-node-set-position! 
   other
   (+ (term-node-x main)
      (term-node-width main)
      gap)
   (+ (term-node-y main)
      (/ (term-node-height main) 2)
      (/ (term-node-height other) -2))))

(define (find-root tns)
  (ormap (λ (tn) (and (null? (term-node-parents tn)) tn)) 
         tns))

(define (slide-to-zero tns)
  (let ([min-x (apply min (map term-node-x tns))]
        [min-y (apply min (map term-node-y tns))])
    (for-each
     (λ (tn) 
       (term-node-set-position! tn 
                                (- (term-node-x tn) min-x)
                                (- (term-node-y tn) min-y)))
     tns)))
   
;; line-up-under : (listof tn) (listof tn) [number] [number] -> void
;; lines up one (row) of term nodes under another (already lined up) row.
(define (line-up-under row-above row-below [horizontal-gap 2] [vertical-gap 40])
  (let ([left-above (apply min (map term-node-x row-above))]
        [right-above (apply max (map (λ (x) (+ (term-node-x x) (term-node-width x))) row-above))])
    (let* ([below-top-edge
            (+ (apply max (map (λ (x) (+ (term-node-y x) (term-node-height x))) row-above)) 
               vertical-gap)]
           [below-width
            (apply + 
                   (* horizontal-gap (- (length row-below) 1))
                   (map term-node-width row-below))]
           [below-left-edge 
            (+ left-above
               (/ (- right-above left-above) 2)
               (/ below-width -2))])
      (let loop ([nodes row-below]
                 [left-offset 0])
        (cond
          [(null? nodes) (void)]
          [else
           (let ([node (car nodes)])
             (term-node-set-position! node
                                      (+ below-left-edge left-offset)
                                      below-top-edge)
             (loop (cdr nodes)
                   (+ left-offset (term-node-width node) horizontal-gap)))])))))


(provide with-colors
         vertical-line
         horizontal-line
         find-root
         
         center-left
         center-right
         center-above
         center-below
         line-up-under
         edge-label-font
         slide-to-zero)
