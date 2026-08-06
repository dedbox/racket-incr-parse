#lang racket/base

;; incr-parse/private/green.rkt
;;
;; Green Trees
;;
;; Green nodes are immutable, position-free, and maximally share structure via
;; hash-consing. They know nothing about absolute positions in the document or
;; parent nodes in the tree.
;;
;; Identical branches collapse to the same object via `intern-branch`, so
;; `eq?` is a valid, O(1) structural equality test on interned Green nodes.

(require incr-lex)

(provide (all-defined-out))

;; Abstract base type
(struct green-tree (kind width) #:transparent)

;; Wraps a single incr-lex token
(struct green-token green-tree (token) #:transparent)

(define (make-green-token kind token)
  (green-token kind (token-width token) token))

;;; Interior node, hash-consed
(struct green-branch green-tree (children) #:transparent)

;; A parameter instead of a plain pmodule-level binding, for more flexible
;; testing.
(define green-cache (make-parameter (make-weak-hash)))

(define (intern-branch! kind children)
  (define key (cons kind children))     ; safe: children are already interned
  (hash-ref! (green-cache) key
             (λ () (green-branch kind (branch-width children) children))))

(define (branch-width children)
  (for/sum ([child (in-list children)]) (green-tree-width child)))

(module+ test
  (require rackunit)

  (test-case "hash-consing: structurally identical branches are eq?"
    (parameterize ([green-cache (make-weak-hash)])
      (define leaf (green-token 'atom 1 'fake-token))
      (define b1 (intern-branch! 'list (list leaf)))
      (define b2 (intern-branch! 'list (list leaf)))
      (check eq? b1 b2)))

  (test-case "structurally different branches are not eq?"
    (parameterize ([green-cache (make-weak-hash)])
      (define l1 (green-token 'atom 1 'a))
      (define l2 (green-token 'atom 1 'b))
      (check-false (eq? (intern-branch! 'list (list l1))
                        (intern-branch! 'list (list l2))))))

  (test-case "branch width is the sum of children's widths"
    (define l1 (green-token 'atom 3 'x))
    (define l2 (green-token 'atom 5 'y))
    (check-equal? (green-tree-width (intern-branch! 'pair (list l1 l2))) 8))

  (test-case "empty branch has width 0"
    (check-equal? (green-tree-width (intern-branch! 'empty '())) 0)))
