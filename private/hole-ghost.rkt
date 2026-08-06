#lang racket/base

;; incr-parse/private/hole-ghost.rkt
;;
;; Hole and Ghost Node Kinds
;;
;; Both are ordinary Green node kinds (see green.rkt): they carry no
;; exceptional control-flow, just data. A totally-parsed CST is one where
;; every missing syntactically required piece is a ghost, and every
;; syntactically-invalid region is hoisted into a hole.

(require racket/contract
         "green.rkt"
         "span.rkt")

(provide (all-defined-out))

;; -----------------------------------------------------------------------------
;; Diagnostics
;; -----------------------------------------------------------------------------

;; severity : 'error | 'warning | 'info
;; message  : string?
;; span     : span? - RELATIVE to the start of the green-tree this diagnostic is
;;    diagnostic is attached to (see private/span.rkt).
(struct diagnostic (severity message span) #:transparent)

;; -----------------------------------------------------------------------------
;; Hole
;; -----------------------------------------------------------------------------

;; content : (or/c #f green-node?)
;;    #f            ⇒ empty hole  (missing statement/expression)
;;    green-tree?   ⇒ staged hole (wraps the malformed subtree verbatim)
(struct hole green-tree (content diagnostics) #:transparent)

(define (hole-status h)
  (if (hole-content h) 'staged 'empty))

(define (make-empty-hole #:diagnostics [diags null])
  (hole 'hole 0 #f diags))

(define (make-staged-hole content #:diagnostics [diags null])
  (hole 'hole (green-tree-width content) content diags))

;; -----------------------------------------------------------------------------
;; Ghost
;; -----------------------------------------------------------------------------

;; of : symbol? - names the expected (but absent) token this ghost stands in
;;    for, e.g., 'close-paren, 'in-kw.
;;
;; Width is always 0.
(struct ghost green-tree (of) #:transparent)

(define (make-ghost of)
  (ghost 'ghost 0 of))

(module+ test
  (require rackunit
           "span.rkt")

  (test-case "empty hole: width 0, status 'empty"
    (define h (make-empty-hole))
    (check-equal? (green-tree-width h) 0)
    (check-eq? (hole-status h) 'empty)
    (check-false (hole-content h)))

  (test-case "staged hole: width matches content, status 'staged"
    (define content (green-token 'unexpected 4 'fake-token))
    (define h (make-staged-hole content))
    (check-equal? (green-tree-width h) 4)
    (check-eq? (hole-status h) 'staged)
    (check-eq? (hole-content h) content))

  (test-case "diagnostics default to empty, attach when given"
    (define h1 (make-empty-hole))
    (check-equal? (hole-diagnostics h1) '())
    (define d (diagnostic 'error "oops" (span 0 0)))
    (define h2 (make-empty-hole #:diagnostics (list d)))
    (check-equal? (hole-diagnostics h2) (list d)))

  (test-case "ghost: always width 0, remembers what it stands in for"
    (define g (make-ghost 'RParen))
    (check-equal? (green-tree-width g) 0)
    (check-eq? (ghost-of g) 'RParen)))
