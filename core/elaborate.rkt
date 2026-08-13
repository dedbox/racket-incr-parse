#lang racket

;; core/elaborate.rkt
;;
;; CST → AST elaboration pass.
;;
;; A separate, memoized pass over Green trees. Memoization key is the
;; eq?-identity of the Green node itself. Per-node-kind elaborators are
;; registered by each language module; grammar.rkt will emit these
;; registrations automatically.
;;
;; NOTE: ast-leaf-text holds a rope, not a plain string, per the real
;; current-leaf-text-extractor default. Any downstream code comparing it
;; against a string literal needs rope->string first.

(require (prefix-in lex: incr-lex)
         racket/match
         (for-syntax racket/base
                     syntax/parse)
         "green.rkt"
         "hole-ghost.rkt")

(provide (all-defined-out))

;; -----------------------------------------------------------------
;; AST Node Shapes
;; -----------------------------------------------------------------

;; One lexer token, elaborated to its own payload text. Trivia is excluded; it
;; is a concrete-syntax concern, not a semantic one. `token` is retained for
;; provenance.
(struct ast-leaf (kind text token) #:transparent)

;; Fallback shape used only when a branch kind has no registered elaborator,
;; to keep the transformation total. Once a grammar registers all of its
;; nonterminals, this constructor should never appear in that grammar's
;; output.
(struct ast-branch (kind children) #:transparent)

;; staged?      : #f for an empty hole, #t for one carrying content
;; content      : #f, or the recursively-elaborated AST of the hoisted
;;                green-tree
;; diagnostics  : the CST hole's diagnostic list, unmodified, kept
;;                separate from lexer-level diagnostics
(struct ast-hole (staged? content diagnostics) #:transparent)

;; of : symbol naming what was synthesized.
;;
;; Ghosts carry no diagnostics or of their own.
(struct ast-ghost (of) #:transparent)

;; -----------------------------------------------------------------
;; Elaborator Registry
;; -----------------------------------------------------------------

;; kind symbol → (green-branch? → any)
;;
;; Each registered elaborator is responsible for recursing into its own
;; children (by calling `elaborate` on whichever it wants, in whatever order
;; it wants). This mirrors the existing RD/Pratt combinator style of
;; per-production control rather than an imposed generic bottom-up walk.
(define current-ast-elaborators (make-parameter (make-hasheq)))

;; Weak by eq?-identity, matching `green-cache`'s existing precedent. This is
;; safe to share across documents because the key is the identity of
;; immutable, hash-consed Green data, and a weak table lets entries for
;; discarded Green nodes be reclaimed.
(define current-ast-cache (make-parameter (make-weak-hasheq)))

;; Hook for extracting a token's payload text, leading/trailing trivia
;; excluded.
(define current-leaf-text-extractor
  (make-parameter
   (λ (token) (lex:token-payload token))))

;; register-elaborator! : symbol (green-branch? -> any) -> void
;;
;; Narrowly-scoped internal mutation. Registration is one-time setup per
;; language module.
;;
;; Now errors on a duplicate `kind` instead of letting a second registration
;; silently win. This is the cheap half of guarding against cross-grammar kind
;; collisions. It only catches a collision within a single elaborator table.
;; It does not catch collisions across two different tables used together in
;; the same process.
(define (register-elaborator! kind proc)
  (when (hash-has-key? (current-ast-elaborators) kind)
    (error 'register-elaborator!
           "elaborator already registered for kind: ~e" kind))
  (hash-set! (current-ast-elaborators) kind proc))

;; Expands to a `register-elaborator!` call, binding `branch` to the raw
;; green-branch inside body.
(define-syntax (define-elaborator stx)
  (syntax-parse stx
    [(_ kind:id (branch:id) body:expr ...+)
     #'(register-elaborator! 'kind (λ (branch) body ...))]))

;; -----------------------------------------------------------------
;; Elaboration - memoized on Green eq?-identity
;; -----------------------------------------------------------------

(define ast-cache-miss (gensym 'ast-cache-miss))

(define (elaborate g)
  (define cache (current-ast-cache))
  (define cached (hash-ref cache g ast-cache-miss))
  (if (eq? cached ast-cache-miss)
      (let ([result (elaborate/dispatch g)])
        (hash-set! cache g result)
        result)
      cached))

;; Not memoized directly. `elaborate` is the memoized entry point. This is the
;; one-shot dispatch it wraps.
(define (elaborate/dispatch g)
  (match g
    [(ghost _ _ of)
     (ast-ghost of)]
    [(hole _ _ content diagnostics)
     (ast-hole (and content #t) (and content (elaborate content)) diagnostics)]
    [(green-token _ _ token)
     (ast-leaf (lex:token-kind token)
               ((current-leaf-text-extractor) token)
               token)]
    [(green-branch kind _ children)
     (define elaborator (hash-ref (current-ast-elaborators) kind #f))
     (if elaborator (elaborator g) (ast-branch kind (map elaborate children)))]
    ;; A node that is none of the above is an internal representation bug, not
    ;; malformed input. Totality guarantees recovery from bad source text, not
    ;; recovery from a broken Green tree, so raising here is the correct
    ;; failure mode.
    [_ (error 'elaborate "unrecognized green node: ~e" g)]))

;; -----------------------------------------------------------------
;; Tests
;; -----------------------------------------------------------------

(module+ test
  (require rackunit)

  ;; Isolated tables per test, per the established green-cache collision
  ;; lesson. The same convention is applied here as for the AST cache and
  ;; elaborator registry.
  (define (fresh-elaborators) (make-hasheq))
  (define (fresh-cache) (make-hasheq))

  ;; --- empty hole -----------------------------------------------
  (parameterize ([current-ast-cache (fresh-cache)]
                 [current-ast-elaborators (fresh-elaborators)])
    (define h (hole 'hole 0 #f null))
    (define a (elaborate h))
    (check-true (ast-hole? a))
    (check-false (ast-hole-staged? a))
    (check-false (ast-hole-content a)))

  ;; --- ghost -------------------------------------------------------
  (parameterize ([current-ast-cache (fresh-cache)]
                 [current-ast-elaborators (fresh-elaborators)])
    (define g (ghost 'ghost 0 'rparen))
    (define a (elaborate g))
    (check-true (ast-ghost? a))
    (check-eq? (ast-ghost-of a) 'rparen))

  ;; --- memoization: same Green node, second call is eq? to first --
  (parameterize ([current-ast-cache (fresh-cache)]
                 [current-ast-elaborators (fresh-elaborators)])
    (define g (ghost 'ghost 0 'rparen))
    (check-eq? (elaborate g) (elaborate g)))

  ;; --- unregistered branch kind falls back, never fails -----------
  (parameterize ([current-ast-cache (fresh-cache)]
                 [current-ast-elaborators (fresh-elaborators)])
    (define b (green-branch 'unregistered-kind 0 (list (ghost 'ghost 0 'x))))
    (define a (elaborate b))
    (check-true (ast-branch? a))
    (check-eq? (ast-branch-kind a) 'unregistered-kind))

  ;; --- registered elaborator is used in preference to fallback -----
  (parameterize ([current-ast-cache (fresh-cache)]
                 [current-ast-elaborators (fresh-elaborators)])
    (define-elaborator some-kind (branch)
      (cons 'elaborated (green-branch-children branch)))
    (define b (green-branch 'some-kind 0 (list (ghost 'ghost 0 'x))))
    (define a (elaborate b))
    (check-equal? (car a) 'elaborated))

  ;; --- duplicate registration for the same kind is an error --------
  (parameterize ([current-ast-elaborators (fresh-elaborators)])
    (register-elaborator! 'dup (λ (branch) 'first))
    (check-exn exn:fail?
               (λ () (register-elaborator! 'dup (λ (branch) 'second))))))
