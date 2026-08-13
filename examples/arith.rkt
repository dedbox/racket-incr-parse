#lang racket/base

;; incr-parse/examples/arith.rkt
;;
;; Example grammar #2: arithmetic expressions with real operator
;; precedence, built via define-operator-grammar - the whole Grammar
;; Tables section of this file used to be four hand-built hash literals
;; and a hand-picked binding-power scheme (see git history). Every
;; nud/led/bp table below is now generated; the words "nud", "led", and
;; "bp" don't appear anywhere in this file.
;;
;; Grammar:
;;   program := expr*
;;   expr    := Number | Ident
;;            | "-" expr                (prefix, binds tighter than * /)
;;            | "(" expr ")"
;;            | expr ("+" | "-") expr   (left-assoc)
;;            | expr ("*" | "/") expr   (left-assoc, binds tighter than + -)

(require (prefix-in : incr-lex)
         "../grammar.rkt"
         "../main.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Lexer
;;; --------------------------------------------------------------------------

(:define-tokens arith-tokens
  ;; Trivia
  [Whitespace := (+ :ws)]
  [Newline    := :nl]
  ;; Tokens
  [LParen     := "("]
  [RParen     := ")"]
  [Plus       := "+"]
  [Minus      := "-"]
  [Star       := "*"]
  [Slash      := "/"]
  [Number     := (+ :digit)]
  [Ident      := (seq :alpha (* :alnum))])

;; => defines arith-lex and arith-apply-edit
(:define-lexer arith
  #:tokens    arith-tokens
  #:token-set [LParen RParen Plus Minus Star Slash Number Ident]
  #:leading   [Whitespace Newline]
  #:trailing  [Whitespace]
  #:newline   [Newline])

;;; --------------------------------------------------------------------------
;;; Grammar - one sort (expr), declared by fixity + Agda-style precedence.
;;; Levels only need to preserve RELATIVE looseness/tightness - the DSL
;;; derives actual binding powers (see core/operator-grammar.rkt).
;;; Loosest to tightest: add(1) < mul(2) < unary-minus(3).
;;; ---------------------------------------------------------------------
;;; Also produces arith-grammar (a ready `grammar` value - see
;;; ../main.rkt), arith-nud-table/-led-table/-bp-table, and an explicitly
;;; bound parse-expr, none of which this file writes by hand.

(define-operator-grammar arith
  #:lexer arith-lex #:apply-edit arith-apply-edit
  #:entry expr
  (sort expr
    (atom Number Ident)
    (infixl 1 (_ 'Plus _))
    (infixl 1 (_ 'Minus _))
    (infixl 2 (_ 'Star _))
    (infixl 2 (_ 'Slash _))
    ;; Kind defaults to 'unop, matching the elaborator below - see
    ;; core/operator-grammar.rkt's prefix clause.
    (prefix 3 ('Minus _))
    ;; Kind defaults to 'binop for the plain 2-slot infix shapes above;
    ;; 'paren here is the form's own required name, matching the
    ;; elaborator below exactly the same way it always had to.
    (form paren 'LParen _ 'RParen)))

;;; --------------------------------------------------------------------------
;;; Top Level: program := expr*
;;; --------------------------------------------------------------------------

(define (program-stop? kind) (eq? kind 'incr-lex:eof))

(define parse-program
  (rep 'program (λ (toks) (parse-expr toks 0)) program-stop?))

;;; --------------------------------------------------------------------------
;;; AST
;;; --------------------------------------------------------------------------

;; op is the operator's own lexer-level kind, e.g. 'Plus, read back off its
;; leaf after elaboration.
(struct ast-binop (op left right) #:transparent)
(struct ast-unop (op operand) #:transparent)
(struct ast-program (exprs) #:transparent)

(define-elaborator unop (branch)
  (define children (green-branch-children branch))
  (define op (ast-leaf-kind (elaborate (car children))))
  (ast-unop op (elaborate (cadr children))))

(define-elaborator binop (branch)
  (define children (green-branch-children branch))
  (define op (ast-leaf-kind (elaborate (cadr children))))
  (ast-binop op (elaborate (car children)) (elaborate (caddr children))))

;; Parens carry no meaning once the tree shape encodes grouping, so
;; elaboration skips straight to the wrapped expression.
(define-elaborator paren (branch)
  (elaborate (cadr (green-branch-children branch))))

(define-elaborator program (branch)
  (ast-program (map elaborate (green-branch-children branch))))

;;; --------------------------------------------------------------------------
;;; Entry Point
;;; --------------------------------------------------------------------------

;; A one-shot "give me a tree from a string" convenience - runtime usage
;; (creates a document, parses it), so it reaches for ../main.rkt rather
;; than growing ../grammar.rkt a runtime concept. parse-program, not
;; arith-grammar's own #:start (parse-expr), since a whole file is
;; expr*, not one bare expr.
(define arith-program-grammar
  (make-grammar #:lexer arith-lex #:apply-edit arith-apply-edit #:start parse-program))

(define (parse-arith-string str)
  (document-tree (document-parse! (make-document arith-program-grammar str))))

(define (elaborate-arith-string str)
  (elaborate (parse-arith-string str)))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require rackunit
           racket/list)

  ;; parse-arith-string returns the 'program branch; for these
  ;; single-expression test inputs it always has exactly one child, which is
  ;; the actual expression tree under test.
  (define (top1 tree) (car (green-branch-children tree)))

  (define (check-round-trip src)
    (check-equal? (green->source (parse-arith-string src)) src))

  (test-case "round-trip: well-formed input"
    (check-round-trip "1 + 2 * 3")
    (check-round-trip "(1 + 2) * 3")
    (check-round-trip "-x * (y - 1)")
    (check-round-trip "a + b + c"))

  (test-case "precedence: 1 + 2 * 3 groups as 1 + (2 * 3)"
    (define expr (top1 (parse-arith-string "1+2*3")))
    (define-values (l op r) (apply values (green-branch-children expr)))
    (check-eq? (green-tree-kind l) 'atom)
    (check-eq? (green-tree-kind r) 'binop))

  (test-case "left-associativity: 1 - 2 - 3 groups as (1 - 2) - 3"
    (define expr (top1 (parse-arith-string "1-2-3")))
    (define-values (l op r) (apply values (green-branch-children expr)))
    (check-eq? (green-tree-kind l) 'binop)
    (check-eq? (green-tree-kind r) 'atom))

  (test-case "unary minus binds tighter than *: -2*3 groups as (-2)*3"
    (define expr (top1 (parse-arith-string "-2*3")))
    (define-values (l op r) (apply values (green-branch-children expr)))
    (check-eq? (green-tree-kind l) 'unop))

  (test-case "round-trip: recovery cases"
    (check-round-trip "1 +")            ; missing rhs -> empty hole
    (check-round-trip "(1 + 2")         ; missing RParen -> ghost
    (check-round-trip "1 @ 2"))         ; unrecognized token -> staged hole

  (test-case "missing rhs produces an empty hole"
    (define expr (top1 (parse-arith-string "1 +")))
    (define rhs (caddr (green-branch-children expr)))
    (check-true (hole? rhs))
    (check-eq? (hole-status rhs) 'empty))

  (test-case "missing RParen produces a ghost"
    (define expr (top1 (parse-arith-string "(1 + 2")))
    (define last-child (last (green-branch-children expr)))
    (check-true (ghost? last-child))
    (check-eq? (ghost-of last-child) 'RParen))

  (test-case "AST: precedence carries through elaboration"
    (define ast (elaborate-arith-string "1+2*3"))
    (define expr (car (ast-program-exprs ast)))
    (check-true (ast-binop? expr))
    (check-eq? (ast-binop-op expr) 'Plus)
    (check-true (ast-leaf? (ast-binop-left expr)))
    (check-true (ast-binop? (ast-binop-right expr))))

  (test-case "AST: parens are dropped, unop keeps its operator kind"
    (define ast (elaborate-arith-string "-(1+2)"))
    (define expr (car (ast-program-exprs ast)))
    (check-true (ast-unop? expr))
    (check-eq? (ast-unop-op expr) 'Minus)
    (check-true (ast-binop? (ast-unop-operand expr)))))
