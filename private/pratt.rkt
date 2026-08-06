#lang racket/base

;; incr-parse/private/pratt.rkt
;;
;; Generic Pratt/precedence-climbing expression parser. Shares the
;; exact Parser signature from combinators.rkt
;;
;;   (listof token?) → (values green-tree? (listof token?))
;;
;; for both nud and led entries, which lets RD combinators and Pratt table
;; entries call each other with no adapter shim: a grammar's RD side calls
;; (parse-expr toks 0) wherever it needs an expression, and nud/led entries
;; (e.g. a parenthesized sub-expression, see nud-paren below) cam freely call
;; back into ordinary combinators like `seq` and `expect`.
;;
;; Recovery: A nud lookup miss falls through to the same hole-for-unexpected /
;; empty-hole-here used everywhere else in the parser. An unrecognized leading
;; token becomes a staged hole. A missing one (EOF) becomes an empty hole. led
;; lookup misses simply end the precedence-climbing loop, same as reaching a
;; genuine expression boundary.
;;
;; Tables are dynamically scoped via parameters, since every recursive call
;; within a single top-level parse uses the same grammar's tables. See
;; langs/arith.rkt for how a grammar installs its tables via parameterize at
;; its entry point.

(require "combinators.rkt"
         "green.rkt"
         "memo.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Table Parameters
;;; --------------------------------------------------------------------------

;; nud-table : kind -> Parser  (a full parser for that leading token)
(define current-nud-table (make-parameter (hash)))

;; led-table : kind -> (green-tree? (listof token?) -> (values green-tree? (listof token?)))
;;   called with `left` already parsed and the operator token still at the
;;   head of the stream (not yet consumed) - mirrors nud getting its own
;;   leading token still at the head.
(define current-led-table (make-parameter (hash)))

;; bp-table : kind -> (cons left-bp right-bp), for led (infix/postfix) entries only.

;; Standard binding-power-pair technique: right-bp > left-bp encodes
;; left-associativity (the operator won't re-trigger while parsing its own
;; right operand); right-bp <= left-bp encodes right-associativity.
(define current-bp-table (make-parameter (hash)))

;;; --------------------------------------------------------------------------
;;; The Climb
;;; --------------------------------------------------------------------------

(define (parse-expr toks min-bp)
  (memo-ref! 'expr toks min-bp (λ () (parse-expr* toks min-bp))))

(define (parse-expr* toks min-bp)
  (define-values (left toks1) (parse-nud toks))
  (parse-led left toks1 min-bp))

(define (parse-nud toks)
  (define kind (peek-kind toks))
  (define nud (hash-ref (current-nud-table) kind #f))
  (cond
    [nud (nud toks)]
    [(eq? kind 'incr-lex:eof) (empty-hole-here "expected an expression" toks)]
    [else (hole-for-unexpected "expected an expression, found unrecognized input" toks)]))

(define (parse-led left toks min-bp)
  (define kind (peek-kind toks))
  (define bp   (hash-ref (current-bp-table) kind #f))
  (cond
    [(and bp (> (car bp) min-bp))
     (define led (hash-ref (current-led-table) kind))
     (define-values (combined toks*) (led left toks))
     (parse-led combined toks* min-bp)]
    [else (values left toks)]))

;;; --------------------------------------------------------------------------
;;; Reusable Table-Entry Builders
;;;
;;; These cover the common shapes (ordinary left-assoc-or-not binary infix,
;;; prefix unary, parenthesized grouping) so a grammar's own file is mostly
;;; just table data, not new parsing logic. A grammar can still hand-write a
;;; nud/led entry directly wherever these shapes don't fit (e.g. ternary ?:,
;;; postfix ++, function-call parens).
;;; --------------------------------------------------------------------------

;; Ordinary binary infix operator.
;;
;; Consume the operator token itself (wrapped as a green-token of its own
;; kind), parse the right operand at the operator's own right binding power,
;; combine into a single 'binop branch: (binop left <op-token> right). Its
;; specific operator stays recoverable from the middle child's green-tree-kind
;; - same pattern used for 'atom in langs/sexpr.rkt.
(define ((led-infix op-kind) left toks)
  (define-values (op-leaf toks1) (consume-as op-kind toks))
  (define rbp (cdr (hash-ref (current-bp-table) op-kind)))
  (define-values (right toks2) (parse-expr toks1 rbp))
  (values (intern-branch! 'binop (list left op-leaf right)) toks2))

;; Prefix unary operator.
;;
;; Consume the operator, parse its one operand at a fixed binding power,
;; combine into a 'unop branch: (unop <op-token> operand).
(define ((nud-prefix op-kind op-bp) toks)
  (define-values (op-leaf toks1) (consume-as op-kind toks))
  (define-values (operand toks2) (parse-expr toks1 op-bp))
  (values (intern-branch! 'unop (list op-leaf operand)) toks2))

;; Parenthesized/bracketed/etc. grouping.
;;
;; (open expr close), at min-bp 0 internally since parens reset precedence.
;; Uses ordinary RD combinators (seq/expect) directly, not anything
;; Pratt-specific - a concrete instance of nud entries freely calling back
;; into combinators.rkt. A missing close delimiter recovers like any other
;; `expect` mismatch: a ghost, no crash.
(define (nud-paren open-kind close-kind)
  (seq 'paren
       (expect open-kind)
       (λ (toks) (parse-expr toks 0))
       (expect close-kind)))

(module+ test
  (require (prefix-in lex: incr-lex)
           rackunit
           rope
           "hole-ghost.rkt")

  ;; Synthetic single-purpose token kinds, decoupled from any real grammar
  ;; (same isolation approach as combinators.rkt's tests).
  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))
  (define (toks . pairs)
    (let loop ([ps pairs])
      (if (null? ps) (list (mk-tok 'incr-lex:eof ""))
          (cons (mk-tok (car ps) (cadr ps)) (loop (cddr ps))))))

  (define test-nud (hash 'NUM (λ (t) (consume-as 'atom t))))
  (define test-led (hash 'PLUS (led-infix 'PLUS) 'STAR (led-infix 'STAR)))
  (define test-bp  (hash 'PLUS (cons 1 2) 'STAR (cons 3 4)))

  (define (run src . pairs)
    (parameterize ([current-nud-table test-nud]
                   [current-led-table test-led]
                   [current-bp-table  test-bp])
      (define-values (tree rest) (parse-expr (apply toks pairs) 0))
      tree))

  (test-case "single atom, no operators"
    (define tree (run "1" 'NUM "1"))
    (check-eq? (green-tree-kind tree) 'atom))

  (test-case "left-associativity: 1+2+3 nests as ((1+2)+3)"
    (define tree (run "1+2+3" 'NUM "1" 'PLUS "+" 'NUM "2" 'PLUS "+" 'NUM "3"))
    (check-eq? (green-tree-kind tree) 'binop)
    (define-values (l1 op1 r1) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l1) 'binop)  ; left child is (1+2), not 3
    (check-eq? (green-tree-kind r1) 'atom))  ; right child is 3, not (2+3)

  (test-case "precedence: 1+2*3 binds * tighter, giving (1+(2*3))"
    (define tree (run "1+2*3" 'NUM "1" 'PLUS "+" 'NUM "2" 'STAR "*" 'NUM "3"))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'atom)    ; left child is 1
    (check-eq? (green-tree-kind r) 'binop))  ; right child is (2*3)

  (test-case "missing right operand produces an empty hole, no crash"
    (parameterize ([current-nud-table test-nud]
                   [current-led-table test-led]
                   [current-bp-table  test-bp])
      (define-values (tree rest) (parse-expr (toks 'NUM "1" 'PLUS "+") 0))
      (define rhs (caddr (green-branch-children tree)))
      (check-true (hole? rhs))
      (check-eq? (hole-status rhs) 'empty)))

  (test-case "unrecognized leading token produces a staged hole via nud fallback"
    (parameterize ([current-nud-table test-nud]
                   [current-led-table test-led]
                   [current-bp-table  test-bp])
      (define-values (tree rest) (parse-expr (toks 'GARBAGE "?") 0))
      (check-true (hole? tree))
      (check-eq? (hole-status tree) 'staged)))

  (test-case "memoized parse-expr: repeated parse of the same token+min-bp reuses the tree"
    (parameterize ([current-nud-table test-nud]
                   [current-led-table test-led]
                   [current-bp-table  test-bp]
                   [current-parse-cache (make-parse-cache)])
      (define input (toks 'NUM "1" 'PLUS "+" 'NUM "2"))
      (define-values (t1 _r1) (parse-expr input 0))
      (define-values (t2 _r2) (parse-expr input 0))
      (check-eq? t1 t2))))
