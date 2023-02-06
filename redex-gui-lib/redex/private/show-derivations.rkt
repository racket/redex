#lang racket/base
(require racket/class
         racket/gui/base
         racket/match
         racket/pretty
         framework
         redex/private/derivations-layout
         "size-snip.rkt"
         redex/private/judgment-form
         "traces.rkt")

(provide show-derivations
         derivation/ps)

(define (derivation/ps derivation filename
                       #:pp [pp default-pretty-printer]
                       #:racket-colors? [racket-colors? #f]
                       #:post-process [post-process void])
  (define-values (ec pb)
    (parameterize ([actually-show-window #f])
      (show-derivations (list derivation)
                        #:pp pp
                        #:racket-colors? racket-colors?)))
  (post-process pb)
  (print-to-ps pb ec filename))

(define actually-show-window (make-parameter #t))

(define (show-derivations derivations
                          #:pp [pp default-pretty-printer]
                          #:racket-colors? [racket-colors? #f]
                          #:init-derivation [init-derivation 0])
  (define init-cw (initial-char-width))
  (define f (new (class deriv-frame%
                   (define size-callback-queued? #f)
                   (define/override (on-size w h)
                     (unless size-callback-queued?
                       (set! size-callback-queued? #t)
                       (queue-callback
                        (λ ()
                          (set! size-callback-queued? #f)
                          (send pb begin-edit-sequence)
                          (layout-derivation pb)
                          (send pb end-edit-sequence))
                        #f))
                     (super on-size w h))
                   (super-new [label "PLT Redex Judgment Form Derivations"]
                              [width 400]
                              [height 400]))))
  (define ac (send f get-area-container))
  (define pb #f)
  (define current-derivation #f)
  (define ec (new editor-canvas% 
                  [parent ac]))
  (send f reflow-container)
    
  (define (show-derivation i)
    (set! current-derivation i)
    (set! pb (new derivation-pb% [pp pp] [racket-colors? racket-colors?]))
    (send ec set-editor pb)
    (send f reflow-container)
    (send pb begin-edit-sequence)
    (parameterize ([initial-char-width
                    (if char-width-slider
                        (send char-width-slider get-value)
                        init-cw)])
      (fill-derivation-container pb (list-ref derivations i)))
    (layout-derivation pb)
    (send which-msg set-label (ith-label i))
    (send pb end-edit-sequence))
  
  (define controls-panel (new vertical-panel% [parent ac] [stretchable-height #f]))
  (define which-derivation-panel (new horizontal-panel%
                                      [parent ac]
                                      [stretchable-height #f]
                                      [alignment '(right center)]))
  
  (define (next/prev-derivation dir label)
    (new button%
         [label label]
         [parent which-derivation-panel]
         [callback
          (λ (x y)
            (show-derivation (modulo (+ current-derivation dir)
                                     (length derivations))))]))
  (next/prev-derivation -1 "Prev Derivation")
  (define (ith-label i)
    (format "~a / ~a" (+ i 1) (length derivations)))
  (define which-msg
    (new message% 
         [label (ith-label (- (length derivations) 1))]
         [parent which-derivation-panel]))
  (next/prev-derivation +1 "Next Derivation")
  (when (<= (length derivations) 1)
    (send ac change-children
          (λ (l) (remq which-derivation-panel l))))
  
  (define (set-all-cws cw)
    (when pb
      (let loop ([snip (send pb find-first-snip)])
        (when snip
          (when (is-a? snip deriv-editor-snip%)
            (send snip set-char-width cw))
          (loop (send snip next))))))
  
  (define char-width-slider 
    (and (number? init-cw)
         (new slider%
              [parent controls-panel]
              [min-value 2]
              [max-value 100]
              [init-value init-cw]
              [label "Pretty Print Width"]
              [callback
               (λ (_1 _2)
                 (when pb
                   (send pb begin-edit-sequence)
                   (set-all-cws (send char-width-slider get-value))
                   (layout-derivation pb)
                   (send pb end-edit-sequence)))])))
  (show-derivation 0)
  (cond
    [(actually-show-window)
     (send f show #t)]
    [else
     (values ec pb)]))

(define deriv-frame%
  (frame:standard-menus-mixin (frame:basic-mixin frame%)))

(define derivation-pb%
  (class pasteboard%

    ;; this method is called to give the pasteboard a
    ;; chance to relayout its snips based on font size
    (define/public (re-run-layout) (void))

    (init-field pp racket-colors?)
    (define root-snip #f)
    (define/public (set-root ts) (set! root-snip ts))
    (define/public (get-root) root-snip)

    (inherit insert)
    ;; called in the dynamic extent of the call to `fill-derivation-container`
    ;; so the `initial-char-width` setting from `show-derivation` will be in effect
    (define/public (add-node term label children)
      (define line-snip (new line-snip%))
      (define name-snip (and label
                             (make-object string-snip% (format " [~a]" label))))
      (define snip (make-snip term
                              children
                              pp
                              racket-colors?
                              (get-user-char-width 
                               (initial-char-width)
                               term)
                              line-snip
                              name-snip))
      (insert snip)
      (insert line-snip)
      (when name-snip (insert name-snip))
      snip)

    (inherit get-admin)
    (define/public (get-size)
      (define admin (get-admin))
      (cond
        [admin
         (define bw (box 0))
         (define bh (box 0))
         (send admin get-view #f #f bw bh)
         (values (unbox bw) (unbox bh))]
        [else
         (values 0 0)]))
    
    (define/augment (can-interactive-resize? evt) #f)
    (define/augment (can-interactive-move? evt) #f)
    (define/augment (can-select? snip on?) (not on?))
    
    (inherit get-focus-snip)
    
    (super-new)
    
    (inherit set-keymap)
    (set-keymap pb-km)))

(define pb-km (new keymap%))
(send pb-km add-function "set-focus"
      (λ (pb evt)
        (define-values (x y) (send pb dc-location-to-editor-location
                                   (send evt get-x)
                                   (send evt get-y)))
        (define snp (send pb find-snip x y))
        (cond
          [(not snp)
           (send pb set-caret-owner #f)]
          [(is-a? snp deriv-editor-snip%)
           (send pb set-caret-owner snp)])))
(send pb-km map-function "leftbutton" "set-focus")

(define deriv-text%
  (class size-text%
    (inherit get-admin)
    (define/override (on-focus on?)
      (define admin (get-admin))
      (when (is-a? admin editor-snip-editor-admin<%>)
        (define snip (send admin get-snip))
        (send snip show-border on?)))
    (super-new)))

(define (make-snip expr children pp code-colors? cw line-snip name-snip)
  (define text (new deriv-text%))
  (send text set-autowrap-bitmap #f)
  (send text set-max-width 'none)
  (send text freeze-colorer)
  (unless code-colors?
    (send text stop-colorer #t))
  (new deriv-editor-snip%
       [char-width cw]
       [editor text]
       [pp pp]
       [expr expr]
       [with-border? #f]
       [derivation-children children]
       [line-snip line-snip]
       [name-snip name-snip]))

(define deriv-editor-snip%
  (class* size-editor-snip% ()
    (init-field derivation-children)
    (init-field line-snip)
    (init-field name-snip)

    (inherit get-admin)
    (define/public (get-term-size)
      (define pb (send (get-admin) get-editor))
      (values (find-snip-width pb this) (find-snip-height pb this)))
    (define/public (get-name-size)
      (cond
        [name-snip
         (define pb (send (get-admin) get-editor))
         (values (find-snip-width pb name-snip) (find-snip-height pb name-snip))]
        [else (values #f #f)]))
    (define/public (set-term-position x y)
      (define pb (send (get-admin) get-editor))
      (send pb move-to this x y))
    (define/public (set-name-position x y)
      (define pb (send (get-admin) get-editor))
      (send pb move-to name-snip x y))
    (define/public (set-line-layout x y w)
      (define pb (send (get-admin) get-editor))
      (send pb move-to line-snip x y)
      (send line-snip set-width w))
    (define/public (get-children) derivation-children)
    
    (super-new)

    (inherit format-expr)
    (format-expr)))

(define line-snip%
  (class snip%
    (inherit get-admin)
    (define width 10)
    (define/public (set-width w) 
      (unless (equal? w width)
        (define admin (get-admin))
        (set! width w) 
        (when admin 
          (send admin resized this #f)
          (send admin needs-update this 0 0 w 1))))
    (define/override (copy)
      (define c (new line-snip%))
      (send c set-width width)
      c)
    (define/override (draw dc x y left top right bottom dx dy draw-caret)
      (define old-smoothing (send dc get-smoothing))
      (define old-pen (send dc get-pen))
      (send dc set-pen "black" 1 'transparent)
      (send dc set-brush "black" 'solid)
      (send dc set-smoothing 'aligned)
      (send dc draw-rectangle x y width 1)
      (send dc set-smoothing old-smoothing)
      (send dc set-pen old-pen))
    (define/override (get-extent dc x y wb hb db sb lb rb)
      (super get-extent dc x y wb hb db sb lb rb)
      (set-box/f wb width)
      (set-box/f hb 1))
    (inherit set-snipclass)
    (super-new)
    (set-snipclass line-snipclass)))

(define (set-box/f b v) (when (box? b) (set-box! b v)))

(define line-snipclass (new snip-class%))
(send line-snipclass set-classname "redex:derivation-line")
(send line-snipclass set-version 1)
(send (get-the-snip-class-list) add line-snipclass)
