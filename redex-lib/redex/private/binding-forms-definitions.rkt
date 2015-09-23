#lang racket

(provide (all-defined-out))

;; When this error occurs, it seems to come from 'wrap-modbeg.rkt'. That seems bad
(define-syntax (shadow stx) (raise-syntax-error #f "used outside of binding specification" stx))
(define-syntax (nothing stx) (raise-syntax-error #f "used outside of binding specification" stx))

(struct import/internal (body beta) #:prefab)
(struct .../internal (body drivers) #:prefab)

;; from the point of view of transcription, this is really just an nt reference to a value that's
;; stored weird and needs to be spliced
(struct ...bind/internal (export-name drivers bspec) #:prefab)

(struct shadow/internal (betas) #:prefab)

;; body: a tree, with `import/internal`s, `.../internal`s, and identifiers,
;;       representing the binding strucutre
;; export-beta: a beta indicating what `nt`s get exported
;; imported-nts: a list of nonterminals that are imported somewhere within this value
;; exported-nts: a list of nonterminals that appear in `export-beta`
;; ported-nts: a (duplicate-free) list of nonterminals on the previous two lists
;; transcription-depths: a list of pairs of names appearing in `body` and numbers indicating
;;       how many `...`s they are under
(struct bspec
        (body export-beta imported-nts exported-nts ported-nts transcription-depths)
        #:prefab)



;; An internal value that has already been matched and has a spec attached to it,
;; so no matching is required.
;; (Used by `#:...bind` for the layers of binding objects it creates).
(struct value-with-spec (match spec) #:transparent)
