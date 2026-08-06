#lang racket/base

;; incr-parse/private/red.rkt
;;
;; Red Tree - lazy, ephemeral positional view over a Green tree
;;
;; A red-node pairs a Green subtree with its absolute offset in the document
;; and a link to its Red parent. Red nodes are never stored persistently and
;; carry no identity of their own - they are recomputed on demand by whoever
;; is walking the tree.

(require (prefix-in lex: incr-lex)
         "green.rkt"
         "hole-ghost.rkt"
         "span.rkt")

(provide (all-defined-out))

;; green  : green-tree?
;; offset : exact-nonnegative-integer? - absolute offset from doc start
;; parent : (or/c red-node? #f)        - #f only at the root
(struct red-node (green offset parent) #:transparent)

(define (red-root green) (red-node green 0 #f))

;;; ---------------------------------------------------------------------
;;; Basic Accessors (pass-through to the wrapped Green node)
;;; ---------------------------------------------------------------------

(define (red-node-kind r)  (green-tree-kind  (red-node-green r)))
(define (red-node-width r) (green-tree-width (red-node-green r)))
(define (red-node-end r)   (+ (red-node-offset r) (red-node-width r)))

(define (red-node-branch? r) (green-branch? (red-node-green r)))
(define (red-node-token? r)  (green-token?  (red-node-green r)))
(define (red-node-hole? r)   (hole?         (red-node-green r)))
(define (red-node-ghost? r)  (ghost?        (red-node-green r)))

(define (red-node-hole-staged? r)
  (and (red-node-hole? r) (hole-content (red-node-green r)) #t))

;; The wrapped incr-lex token, for leaf nodes only.
(define (red-node-token r)
  (unless (red-node-token? r)
    (error 'red-node-token "not a token leaf: ~a" (red-node-kind r)))
  (green-token-token (red-node-green r)))

;;; --------------------------------------------------------------------------
;;; A leaf's offset marks the start of its LEADING TRIVIA, not its own matched
;;; text - green-token's width already bakes in leading and trailing trivia
;;; widths. This matters any time you need the position of the token's actual
;;; payload, e.g. for shifting a lexer-level diagnostic (whose offset is
;;; relative to the matched-pattern start, not the leading-trivia start) into
;;; absolute document coordinates.
;;; --------------------------------------------------------------------------

(define (red-node-payload-offset r)
  (unless (red-node-token? r)
    (error 'red-node-payload-offset "not a token leaf: ~a" (red-node-kind r)))
  (define tok (red-node-token r))
  (define leading-width
    (for/sum ([triv (in-list (lex:token-leading tok))])
      (lex:token/trivia-width triv)))
  (+ (red-node-offset r) leading-width))

;;; ---------------------------------------------------------------------
;;; Children - the one place offsets actually get computed
;;; ---------------------------------------------------------------------

;; A node is a Red leaf (red-children ⇒ null) iff its Green node is a token, a
;; ghost, or an empty hole. A staged hole is not a leaf: its content is
;; exposed as a single child at the hole's own offset.
(define (red-leaf? r)
  (define g (red-node-green r))
  (or (green-token? g) (ghost? g) (and (hole? g) (not (hole-content g)))))

(define (red-children r)
  (define g (red-node-green r))
  (cond
    [(green-branch? g)
     (let loop ([kids (green-branch-children g)] [off (red-node-offset r)])
       (cond
         [(null? kids) null]
         [else (cons (red-node (car kids) off r)
                     (loop (cdr kids) (+ off (green-tree-width (car kids)))))]))]
    [(and (hole? g) (hole-content g))
     (list (red-node (hole-content g) (red-node-offset r) r))]
    [else null]))

;;; ---------------------------------------------------------------------
;;; Absolute Diagnostics - two separate channels
;;; ---------------------------------------------------------------------
;;
;; Lexical (from raw incr-lex tokens) and syntactic (from parser-level holes)
;; diagnostics stay as distinct accessors returning distinct struct types.

;; Hole-level (syntactic). Hole-diagnostics stores spans RELATIVE to the
;; hole's own start (see span.rkt / hole-ghost.rkt). Shift by this node's
;; offset to get document-absolute spans. Null for non-holes.
(define (red-node-diagnostics r)
  (define g (red-node-green r))
  (if (hole? g)
      (for/list ([d (in-list (hole-diagnostics g))])
        (struct-copy diagnostic d
                     [span (span (+ (red-node-offset r)
                                    (span-offset (diagnostic-span d)))
                                 (span-width (diagnostic-span d)))]))
      null))

;; Token-level (lexical). incr-lex's own diagnostic-offset is relative to the
;; token's matched-pattern start, NOT the red-node-offset (which includes
;; leading trivia). Returned as native lex:diagnostic values. Null for
;; non-tokens.
(define (red-node-lexer-diagnostics r)
  (if (red-node-token? r)
      (for/list ([d (in-list (lex:token-diagnostics (red-node-token r)))])
        (lex:diagnostic-shift d (red-node-payload-offset r)))
      null))

;;; ---------------------------------------------------------------------
;;; Spine Lookup - find the Red node covering a document offset
;;; ---------------------------------------------------------------------
;;
;; This operation is required for efficient re-parsing: given an edit at some
;; document offset, walk ONLY the spine from root to the innermost node
;; touching that offset - O(depth), not O(size).
;;
;; Containment rule per node k:
;;   width > 0  ⇒  offset_k <= o < offset_k + width_k     (half-open)
;;   width = 0  ⇒  offset_k == o                          (exact point)
;;
;; The width=0 case matters more than it looks: incr-lex always terminates a
;; token stream with a zero-width EOF sentinel, which lets this rule determine
;; when the cursor is at end of the document without a special case.
;;
;; Hole/content boundary handling: a STAGED hole's content shares the hole's
;; exact span (holes are width-transparent), so both would otherwise match at
;; every point in that span. Landing exactly on the hole's own left boundary
;; (target == the hole's offset) resolves to the hole itself; landing strictly
;; past it resolves to one hop into the content (not a further recursive
;; descent into the content's own children). Any other sibling tie (e.g. an
;; empty hole and a ghost sharing a point) resolves by plain document order,
;; same as any ordinary sibling tie - no special-casing.

(define (red-node-covers? node target)
  (define s (red-node-offset node))
  (define w (red-node-width node))
  (if (zero? w) (= target s) (and (<= s target) (< target (+ s w)))))

(define (red-find-at root target)
  (unless (and (>= target 0) (<= target (red-node-width root)))
    (error 'red-find-at "cursor offset ~a out of range [0,~a]" target (red-node-width root)))
  (let loop ([node root])
    (cond
      [(red-node-hole-staged? node)
       (if (> target (red-node-offset node))
           (car (red-children node))   ; one hop into contents; stop there
           node)]                      ; on the boundary: the hole itself
      [else
       (define hit (findf (λ (k) (red-node-covers? k target)) (red-children node)))
       (if hit (loop hit) node)])))

(module+ test
  (require rackunit
           rope)

  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) '() '() '()))

  ;; Hand-built tree: (branch 'list [tokA "foo", ghost 'RParen])
  (define tokA (green-token 'atom 3 (mk-tok 'Symbol "foo")))
  (define gh   (make-ghost 'RParen))
  (define tree (intern-branch! 'list (list tokA gh)))
  (define root (red-root tree))

  (test-case "offsets accumulate across siblings"
    (define kids (red-children root))
    (check-equal? (map red-node-offset kids) (list 0 3))
    (check-equal? (map red-node-width kids) (list 3 0)))

  (test-case "red-find-at: interior of a token"
    (check-eq? (red-node-green (red-find-at root 1)) tokA))

  (test-case "red-find-at: zero-width ghost at its exact point"
    (check-eq? (red-node-green (red-find-at root 3)) gh))

  (test-case "red-find-at: out-of-range offset errors"
    (check-exn exn:fail? (λ () (red-find-at root 99))))

  ;; Staged-hole boundary vs interior: landing exactly on the hole's own
  ;; offset returns the hole; landing past it returns the content, one hop
  ;; only.
  (define inner (green-token 'unexpected 2 (mk-tok 'RParen ")")))
  (define staged (make-staged-hole inner))
  (define htree (intern-branch! 'wrap (list staged)))
  (define hroot (red-root htree))

  (test-case "red-find-at: staged hole's own boundary returns the hole"
    (check-true (red-node-hole? (red-find-at hroot 0))))

  (test-case "red-find-at: strictly inside returns the content, one hop"
    (define found (red-find-at hroot 1))
    (check-eq? (red-node-green found) inner))

  (test-case "red-node-payload-offset accounts for leading trivia"
    (define triv (lex:trivia 'Whitespace (string->rope "  ")))
    (define tok  (lex:token 'Symbol 5 (string->rope "hi") (list triv) '() '()))
    (define leaf (green-token 'atom 5 tok))
    (define r    (red-node leaf 10 #f))
    ;; 10 (this leaf's own red offset) + 2 (leading trivia width) = 12
    (check-equal? (red-node-payload-offset r) 12)))
