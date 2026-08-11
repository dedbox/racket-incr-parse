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
         racket/list
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

;;; ---------------------------------------------------------------------
;;; Sibling Navigation
;;; ---------------------------------------------------------------------
;;
;; Red nodes are ephemeral and carry no identity or index of their own.
;; Instead, the index is recomputed on demand.

(define (red-sibling-index r)
  (define p (red-node-parent r))
  (and p
       (for/first ([k (in-list (red-children p))]
                   [i (in-naturals)]
                   #:when (and (eq? (red-node-green k) (red-node-green r))
                               (= (red-node-offset k) (red-node-offset r))))
         i)))

;; #f at the root, where there's no parent, and at the outermost and innermost
;; positions.
(define (red-next-sibling r)
  (define p (red-node-parent r))
  (define i (and p (red-sibling-index r)))
  (and i
       (let ([sibs (red-children p)])
         (and (< (add1 i) (length sibs)) (list-ref sibs (add1 i))))))

(define (red-prev-sibling r)
  (define p (red-node-parent r))
  (define i (and p (red-sibling-index r)))
  (and i (> i 0) (list-ref (red-children p) (sub1 i))))

;;; ---------------------------------------------------------------------
;;; Ancestor Walk / Enclosing Node - "expand selection" for an editor
;;; ---------------------------------------------------------------------

(define (red-ancestors r)
  (let loop ([p (red-node-parent r)])
    (if p (cons p (loop (red-node-parent p))) null)))

;; The nearest proper ancestor of r with the given kind. The kind of r itself
;; never matches. Calling this repeatedly on the previous result effectively
;; expands the selection outward one node of the given kind at a time.
(define (red-enclosing-of-kind r kind)
  (findf (λ (a) (eq? (red-node-kind a) kind)) (red-ancestors r)))

;;; ---------------------------------------------------------------------
;;; Tree-Wide Diagnostics
;;; ---------------------------------------------------------------------

(define (red-tree-diagnostics r)
  (append (red-node-lexer-diagnostics r)
          (red-node-diagnostics r)
          (append-map red-tree-diagnostics (red-children r))))

(module+ test
  (require rackunit
           rope)

  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))

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
    (define tok  (lex:token 'Symbol 5 (string->rope "hi") (list triv) null null))
    (define leaf (green-token 'atom 5 tok))
    (define r    (red-node leaf 10 #f))
    ;; 10 (this leaf's own red offset) + 2 (leading trivia width) = 12
    (check-equal? (red-node-payload-offset r) 12))

  ;; ---------------------------------------------------------------------
  ;; Sibling navigation, ancestor walk, tree-wide diagnostics
  ;; ---------------------------------------------------------------------
  ;; Reuses `root`/`tree` (branch 'list [tokA "foo", ghost 'RParen]) from
  ;; above.

  (test-case "red-next-sibling / red-prev-sibling walk a parent's children"
    (define kids (red-children root))
    (define first (car kids))
    (define second (cadr kids))
    (check-eq? (red-node-green (red-next-sibling first)) (red-node-green second))
    (check-eq? (red-node-green (red-prev-sibling second)) (red-node-green first))
    (check-false (red-prev-sibling first))
    (check-false (red-next-sibling second)))

  (test-case "red-next-sibling/red-prev-sibling: #f at the root, no parent"
    (check-false (red-next-sibling root))
    (check-false (red-prev-sibling root)))

  (test-case "red-ancestors: nearest first, root last"
    (define nested (intern-branch! 'outer (list tree)))
    (define nested-root (red-root nested))
    (define inner-list-node (car (red-children nested-root)))
    (define leaf (car (red-children inner-list-node)))
    (check-equal? (map red-node-kind (red-ancestors leaf)) '(list outer)))

  (test-case "red-enclosing-of-kind: nearest strict ancestor, never r itself"
    (define nested (intern-branch! 'outer (list tree)))
    (define nested-root (red-root nested))
    (define inner-list-node (car (red-children nested-root)))
    (define leaf (car (red-children inner-list-node)))
    (check-eq? (red-node-kind (red-enclosing-of-kind leaf 'list)) 'list)
    (check-eq? (red-node-kind (red-enclosing-of-kind leaf 'outer)) 'outer)
    ;; inner-list-node's OWN kind is 'list, but none of ITS ancestors is -
    ;; strict-ancestor, not inclusive-self, so this must be #f, not itself.
    (check-false (red-enclosing-of-kind inner-list-node 'list))
    (check-false (red-enclosing-of-kind leaf 'nonexistent)))

  (test-case "red-tree-diagnostics: collects hole diagnostics from across the whole tree, absolute offsets"
    (define d1 (diagnostic 'error "bad atom" (span 0 1)))
    (define staged-with-diag (make-staged-hole inner #:diagnostics (list d1)))
    ;; [ atomA(width 2), branch 'inner [ staged-hole-with-diag ] ]
    (define atomA (green-token 'atom 2 (mk-tok 'Symbol "hi")))
    (define inner-branch (intern-branch! 'inner (list staged-with-diag)))
    (define whole (intern-branch! 'outer (list atomA inner-branch)))
    (define diags (red-tree-diagnostics (red-root whole)))
    (check-equal? (length diags) 1)
    ;; staged-with-diag sits at offset 2 (after atomA's width 2); d1's own
    ;; span was relative [0,1) -> absolute [2,3).
    (check-equal? (span-offset (diagnostic-span (car diags))) 2)
    (check-equal? (diagnostic-message (car diags)) "bad atom")))
