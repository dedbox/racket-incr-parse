#lang racket/base

;; incr-parse/try-alt-coverage.rkt
;;
;; Exercises try/alt for real, inside an actual nested, memoized parse. This
;; file is a rough fixture, not a shipped grammar. It registers no lexer and
;; no AST elaborators, and nothing under langs/ depends on it.
;;
;; The toy grammar:
;;
;;   program := ambig*
;;   ambig   := digits TagA        ; production A
;;            | digits TagB        ; production B
;;   digits  := D+                 ; shared, arbitrary-length prefix
;;
;; digits is itself memoized and shared unmodified between both alternatives.
;; No fixed amount of lookahead can disambiguate A from B because the run of D
;; tokens is unbounded, and the two productions only diverge at the very last
;; token, so real backtracking is the only way through.
;;
;; expect/hole-for-unexpected never fail, so neither can be used at the
;; divergence point. tag-or-fail below calls (fail) explicitly to trigger
;; try/alt's backtracking.

(require (prefix-in lex: incr-lex)
         rope
         "private/combinators.rkt"
         "private/green.rkt"
         "private/hole-ghost.rkt"
         "private/memo.rkt"
         "private/printer.rkt"
         "private/token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Instrumentation
;;; --------------------------------------------------------------------------

;; A counter for real `digits` computations / thunk calls, so a test can
;; assert that digits ran exactly once despite being reached from two
;; different alt branches. This provides direct evidence of memoized reuse
;; across a real backtrack.
(define digits-computed-count (box 0))
(define (fresh-digits-computed-count!) (set-box! digits-computed-count 0))
(define (bump-digits-computed!)
  (set-box! digits-computed-count (add1 (unbox digits-computed-count))))

;;; --------------------------------------------------------------------------
;;; Grammar
;;; --------------------------------------------------------------------------

;; To test real backtracking, we need to deliberately break the no-fail
;; convention by manufacturing a real failure to backtrack from.
(define ((tag-or-fail expected-kind) toks)
  (if (eq? (peek-kind toks) expected-kind)
      (consume-as expected-kind toks)
      (fail)))

;; The shared prefix. Ths is memoized under its own rule-id and reused
;; unmodified by both parse-a and parse-b below.
(define parse-digits
  (memoize 'digits
           (λ (toks)
             (bump-digits-computed!)
             ((rep 'digits (λ (t) (consume-as 'digit t))
                   (λ (k) (not (eq? k 'D))))
              toks))))

(define parse-a (seq 'prod-a parse-digits (tag-or-fail 'TagA)))
(define parse-b (seq 'prod-b parse-digits (tag-or-fail 'TagB)))

(define parse-ambig
  (memoize 'ambig
           (alt (λ (toks) (hole-for-unexpected "neither TagA nor TagB" toks))
                parse-a parse-b)))

(define (ambig-stop? k) (eq? k 'incr-lex:eof))

(define parse-program
  (memoize 'program (rep 'program parse-ambig ambig-stop?)))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require rackunit)

  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))

  (define (D) (mk-tok 'D "5"))
  (define (eof) (mk-tok 'incr-lex:eof ""))

  ;; Fresh cache + fresh pass, every call - isolates one test from another,
  ;; the same convention memo.rkt's own tests use.
  (define (run-fresh toks)
    (fresh-digits-computed-count!)
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (parse-cache-begin-pass! cache)
      (parse-ambig toks)))

  (test-case "production A wins when the run of D's ends in TagA"
    (define-values (tree _rest)
      (run-fresh (tokens->stream (list (D) (D) (D) (mk-tok 'TagA "a") (eof)))))
    (check-eq? (green-tree-kind tree) 'prod-a)
    (check-equal? (green->source tree) "555a"))

  (test-case "production B wins when the run of D's ends in TagB"
    (define-values (tree _rest)
      (run-fresh (tokens->stream (list (D) (D) (mk-tok 'TagB "b") (eof)))))
    (check-eq? (green-tree-kind tree) 'prod-b)
    (check-equal? (green->source tree) "55b"))

  (test-case "zero-length shared prefix still disambiguates correctly"
    (define-values (tree-a _r1)
      (run-fresh (tokens->stream (list (mk-tok 'TagA "a") (eof)))))
    (check-eq? (green-tree-kind tree-a) 'prod-a)
    (define-values (tree-b _r2)
      (run-fresh (tokens->stream (list (mk-tok 'TagB "b") (eof)))))
    (check-eq? (green-tree-kind tree-b) 'prod-b))

  (test-case "neither tag present: both alternatives fail, resilience holds"
    ;; hole-for-unexpected consumes exactly one token (the first D), never
    ;; raising - Absolute Resilience holds even when every real alternative
    ;; has genuinely failed via (fail).
    (define-values (tree _rest)
      (run-fresh (tokens->stream (list (D) (D) (mk-tok 'TagC "c") (eof)))))
    (check-true (hole? tree))
    (check-eq? (hole-status tree) 'staged))

  (test-case
      "digits is computed exactly once, reused across the A-then-B backtrack"
    ;; parse-a is tried first (it precedes parse-b in the alt list) and
    ;; fails only at the very end, after digits has already run and
    ;; consumed three tokens. try must roll current-parse-offset all the
    ;; way back to before digits started - not just back to the failed tag
    ;; check - or production B's retry of the identical digits call would
    ;; record the wrong start offset: either a spurious cache miss, or
    ;; (worse) a same-pass collision.
    (define-values (tree _rest)
      (run-fresh (tokens->stream (list (D) (D) (D) (mk-tok 'TagB "b") (eof)))))
    (check-eq? (green-tree-kind tree) 'prod-b)
    (check-equal? (unbox digits-computed-count) 1))

  (test-case
      "offset lands correctly after a backtrack: a following ambig item parses right"
    ;; If try's rollback were off by even one token's width, this second
    ;; item would start at the wrong offset and either misparse its own
    ;; digits run or miss its tag token entirely.
    (fresh-digits-computed-count!)
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (parse-cache-begin-pass! cache)
      (define toks
        (tokens->stream
         (list (D) (D) (mk-tok 'TagB "b")   ; item 1: backtracks A -> B
               (D) (mk-tok 'TagA "a")       ; item 2: no backtrack needed
               (eof))))
      (define-values (tree rest) (parse-program toks))
      (check-equal? (green->source tree) "55b5a")
      (check-equal? (length (green-branch-children tree)) 2)
      (check-equal? (map green-tree-kind (green-branch-children tree))
                    '(prod-b prod-a))
      (check-eq? (peek-kind rest) 'incr-lex:eof)))

  (test-case
      "the SAME digits sub-tree survives an edit-driven re-parse of a later, untouched item"
    ;; Exercises try/alt together with span-based invalidation across an
    ;; edit, not just within one pass - the interaction the checkpoint
    ;; flags as never having been tested together before.
    (fresh-digits-computed-count!)
    (define cache (make-parse-cache))
    (define D1a (D)) (define D1b (D)) (define TB1 (mk-tok 'TagB "b"))
    (define D2 (D))  (define TA2 (mk-tok 'TagA "a"))
    (define toks1 (tokens->stream (list D1a D1b TB1 D2 TA2 (eof))))
    (define tree1
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (parse-cache-begin-pass! cache)
        (define-values (t _r) (parse-program toks1))
        t))
    (define (find-item kind t)
      (cond [(and (green-branch? t) (eq? (green-tree-kind t) kind)) t]
            [(green-branch? t)
             (ormap (λ (c) (find-item kind c)) (green-branch-children t))]
            [else #f]))
    (define item2-before (find-item 'prod-a tree1))
    ;; "edit": item 1's TagB replaced with a distinct-but-equal-content
    ;; token, confined to item 1's span [0, 3).
    (parse-cache-invalidate! cache 0 3)
    (define TB1* (mk-tok 'TagB "b"))
    (define toks2 (tokens->stream (list D1a D1b TB1* D2 TA2 (eof))))
    (define tree2
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (parse-cache-begin-pass! cache)
        (define-values (t _r) (parse-program toks2))
        t))
    (define item2-after (find-item 'prod-a tree2))
    (check-eq? item2-before item2-after)
    (check-equal? (green->source tree2) "55b5a")))
