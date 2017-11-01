#lang racket/base
(require racket/gui)

(provide rewrite-pb)

(define blank-snip%
  (class snip%
    (init-field [spaces 1])
    (define/override (draw dc x y left top right bottom dx dy draw-caret?)
      (void))
    (inherit get-style)
    
    (define width #f)
    
    (define/override (size-cache-invalid) (set! width #f))
    
    (define/override (get-extent dc x y wb hb descentb spaceb lspace rspace)
      (unless width
        (let-values ([(w h d a) (send dc get-text-extent " " (send (get-style) get-font))])
          (set! width (* spaces w))))
      (set-box/f wb width)
      (set-box/f hb 0)
      (set-box/f descentb 0)
      (set-box/f spaceb 0)
      (set-box/f lspace 0)
      (set-box/f rspace 0))
    
    (define/override (get-count) 1)
    
    (super-new)))

(define (rewrite-pb pb)
  (let loop ([snip (send pb find-first-snip)])
    (when snip
      (when (is-a? snip editor-snip%)
        (let ([ed (send snip get-editor)])
          (when (is-a? ed text%)
            (rewrite-spaces ed))))
      (loop (send snip next)))))

(define (rewrite-spaces ed)
  (let loop ([pos 0])
    (when (< pos (send ed last-position))
      (when (pos . > . 2000)
        (error 'rewrite-space "too many!"))
      (let ([next-space (send ed find-string " " 'forward pos)])
        (cond
          [next-space
           (let ([end-pos 
                  (let loop ([i next-space])
                    (cond
                      [(equal? #\space (send ed get-character i))
                       (loop (+ i 1))]
                      [else i]))])
             (when (= end-pos next-space)
               (error 'rewrite-spaces "where are the spaces? ~s ~s\n" next-space end-pos))
             (send ed delete next-space end-pos #f)
             (send ed insert 
                   (new blank-snip% [spaces (- end-pos next-space)])
                   next-space next-space #f)
             (loop (+ next-space 1)))])))))


(define (set-box/f b v) (when (box? b) (set-box! b v)))
