#lang racket/base

;; incr-parse/private/span.rkt
;;
;; A `span` is an (offset, width) pair. Its meaning is context-dependent:
;;   - Attached to a diagnostic on a Green node (hole-ghost.rkt): the offset
;;     is RELATIVE to the start of that Green node. This keeps Green nodes
;;     position-free and hash-cons-safe.
;;   - Attached to anything produced during Red traversal (red.rkt): the
;;     offset is ABSOLUTE from document start.

(provide (all-defined-out))

(struct span (offset width) #:transparent)

(define (span-end s) (+ (span-offset s) (span-width s)))
