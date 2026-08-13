#lang racket/base

;; incr-parse/core/combinators.rkt
;;
;; The no-fail combinator core.
;;
;;   Parser ≡ token-stream? → (values green-tree? token-stream?)
;;
;; toks is a token-stream value (a vector + integer position),
;; not a raw list, but every combinator here still treats it opaquely.
;;
;; Every combinator in this file returns a complete green-tree: either an
;; ordinary token/branch on success, or a hole or a ghost on failure to match.
;; If something can't be parsed as intended, that fact is recorded in the tree
;; as a hole with diagnostics.
;;
;; The one exception is try/alt's internal backtracking, which uses a private
;; exception purely for non-local control flow between alternatives that
;; haven't committed yet.

(require (prefix-in lex: incr-lex)
         "green.rkt"
         "hole-ghost.rkt"
         "memo.rkt"
         "span.rkt"
         "token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Token-stream primitives
;;; --------------------------------------------------------------------------

(define (peek-kind toks) (stream-peek-kind toks))

;; The kind of token just past the current one. This is a second
;; combinator-level primitive alongside peek-kind for a grammar that needs
;; exactly one extra token of lookahead to disambiguate two productions
;; without requiring try/alt.
(define (peek2-kind toks) (stream-peek-kind (stream-rest toks)))

(define (at-eof? toks) (eq? (peek-kind toks) 'incr-lex:eof))

;;; --------------------------------------------------------------------------
;;; Leaves
;;; --------------------------------------------------------------------------

;; Consumes exactly one token, unconditionally, as a green-token of the given
;; grammar-level kind. The caller is responsible for having already checked
;; (via peek-kind) that this is the right thing to do because this primitive
;; never inspects the token's own kind itself, which is how one grammar-level
;; kind (e.g., 'atom) can wrap several distinct lexer-level token kinds (e.g.,
;; Symbol, Number) uniformly. The distinction is recoverable later, via the
;; wrapped token's own lex:token-kind, e.g., for an AST elaboration pass to
;; split back out.
(define (consume-as kind toks)
  (when (zero? (vector-length (token-stream-vec toks)))
    (error 'consume-as "no tokens left (missing EOF sentinel?)"))
  (define tok (stream-peek toks))
  (bump-parse-offset! (lex:token-width tok))
  (values (make-green-token kind tok) (stream-rest toks)))

;; If the next token matches, consume it. If not, DON'T consume anything and
;; DON'T fail - insert a ghost standing in for the missing token instead.
(define ((expect expected-kind) toks)
  (if (eq? (peek-kind toks) expected-kind)
      (consume-as expected-kind toks)
      (values (make-ghost expected-kind) toks)))

;;; --------------------------------------------------------------------------
;;; Hole Insertion - for genuinely-unrecognized input
;;; --------------------------------------------------------------------------

;; Used where no grammar production can start from the current token (e.g. a
;; stray close-paren, or a token kind this grammar position has no rule for at
;; all). Puts the offending token into a staged hole and consumes it. This
;; minimal recovery step guarantees forward progress by ensuring every call
;; consumes at least 1 token - any caller looping on this will terminate.
(define (hole-for-unexpected message toks)
  (define-values (leaf rest) (consume-as 'unexpected toks))
  (define diag (diagnostic 'error message (span 0 (green-tree-width leaf))))
  (values (make-staged-hole leaf #:diagnostics (list diag)) rest))

;; Used where a production is entirely absent (e.g. an empty argument slot, or
;; where an expression was expected but the file just ended). No token is
;; consumed (width is 0).
(define (empty-hole-here message toks)
  (define diag (diagnostic 'error message (span 0 0)))
  (values (make-empty-hole #:diagnostics (list diag)) toks))

;;; --------------------------------------------------------------------------
;;; Structural Combinators
;;; --------------------------------------------------------------------------

;; Assembles named sub-parsers into a single branch, passing the token stream
;; through each in order and collecting every child. Nothing is ever dropped,
;; so the branch's width is always exactly the sum of its children's widths.
(define ((seq kind . parsers) toks)
  (let loop ([ps parsers] [toks toks] [children null])
    (if (null? ps)
        (values (intern-branch! kind (reverse children)) toks)
        (let-values ([(child toks*) ((car ps) toks)])
          (loop (cdr ps) toks* (cons child children))))))

;; Zero or more repetitions of elem-parser, stopping as soon as stop? (a
;; predicate on the next token's kind) is true. Peek-based, not backtracking.
;;
;; NOTE: stop? MUST return #t for 'incr-lex:eof, or rep can loop forever on
;; malformed/truncated input.
(define (rep kind elem-parser stop?)
  (unless (stop? 'incr-lex:eof)
    (error 'rep "stop? must return #t for 'incr-lex:eof"))
  (λ (toks)
    (let loop ([toks toks] [children null])
      (if (stop? (peek-kind toks))
          (values (intern-branch! kind (reverse children)) toks)
          (let-values ([(child toks*) (elem-parser toks)])
            (loop toks* (cons child children)))))))

;;; --------------------------------------------------------------------------
;;; Ordered Choice - for grammars needing real lookahead beyond one token
;;; --------------------------------------------------------------------------

(struct backtrack-signal ())
(define (fail) (raise (backtrack-signal)))

;; Runs p. If it fails, returns #f instead of propagating the error, and
;; rolls current-parse-offset back to where it was before.
;;
;; The current-parse-offset rollback is necessary because partial matches
;; inside p can affect the offset on their way through, causing the memo layer
;; to see a document position that doesn't match the returned tree.
(define (try p toks)
  (define saved-offset (unbox (current-parse-offset)))
  (with-handlers ([backtrack-signal?
                   (λ (_) (set-box! (current-parse-offset) saved-offset) #f)])
    (call-with-values (λ () (p toks)) cons)))

;; Tries each parser in order via try. The first that doesn't fail wins. If
;; all fail, falls back to else-parser (typically hole-for-unexpected).
(define ((alt else-parser . parsers) toks)
  (let loop ([ps parsers])
    (cond
      [(null? ps) (else-parser toks)]
      [(try (car ps) toks) => (λ (r) (values (car r) (cdr r)))]
      [else (loop (cdr ps))])))

(module+ test
  (require rackunit
           rope)

  ;; Manually constructed tokens, bypassing any real lexer, for testing the
  ;; combinator layer in isolation. Every fixture still ends with an explicit
  ;; EOF token, matching real incr-lex output, even though nothing here relies
  ;; on that specifically anymore.
  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))
  (define (toks . pairs)
    ;; pairs alternate kind str kind str ...
    (tokens->stream
     (let loop ([ps pairs])
       (if (null? ps) (list (mk-tok 'incr-lex:eof ""))
           (cons (mk-tok (car ps) (cadr ps)) (loop (cddr ps)))))))

  (test-case "consume-as wraps one token, advances the stream"
    (define-values (leaf rest) (consume-as 'atom (toks 'Symbol "x")))
    (check-true (green-token? leaf))
    (check-eq? (green-tree-kind leaf) 'atom)
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "expect: matching kind consumes"
    (define-values (leaf rest) ((expect 'LParen) (toks 'LParen "(")))
    (check-true (green-token? leaf))
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "expect: mismatched kind inserts a ghost, consumes nothing"
    (define input (toks 'Symbol "x"))
    (define-values (node rest) ((expect 'RParen) input))
    (check-true (ghost? node))
    (check-eq? (ghost-of node) 'RParen)
    (check-eq? rest input))

  (test-case "hole-for-unexpected consumes exactly one token"
    (define-values (h rest) (hole-for-unexpected "bad" (toks 'RParen ")" 'Symbol "y")))
    (check-true (hole? h))
    (check-eq? (hole-status h) 'staged)
    (check-eq? (peek-kind rest) 'Symbol))

  (test-case "empty-hole-here consumes nothing"
    (define input (toks 'Symbol "x"))
    (define-values (h rest) (empty-hole-here "missing" input))
    (check-eq? (hole-status h) 'empty)
    (check-eq? rest input))

  (test-case "seq assembles children in order into one branch"
    (define-values (tree rest)
      ((seq 'pair (expect 'LParen) (λ (t) (consume-as 'atom t)))
       (toks 'LParen "(" 'Symbol "x")))
    (check-eq? (green-tree-kind tree) 'pair)
    (check-equal? (length (green-branch-children tree)) 2)
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "rep collects until stop?, terminates at EOF"
    (define stop? (λ (k) (or (eq? k 'RParen) (eq? k 'incr-lex:eof))))
    (define-values (tree rest)
      ((rep 'items (λ (t) (consume-as 'atom t)) stop?)
       (toks 'Symbol "a" 'Symbol "b" 'RParen ")")))
    (check-equal? (length (green-branch-children tree)) 2)
    (check-eq? (peek-kind rest) 'RParen))

  (test-case "rep asserts stop? handles EOF"
    (check-exn exn:fail?
               (λ () (rep 'items (λ (t) (consume-as 'atom t)) (λ (k) (eq? k 'RParen)))))))
