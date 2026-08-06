#lang racket/base

;; incr-parse/langs/arith.rkt
;;
;; Toy grammar #2: arithmetic expressions with real operator precedence.
;; Exists to validate the RD<->Pratt handoff protocol. See private/pratt.rkt
;; for the shared mechanism this grammar is entirely table data against.
;;
;; Grammar:
;;   program := expr*
;;   expr    := Number | Ident
;;            | "-" expr                (prefix, binds tighter than * /)
;;            | "(" expr ")"
;;            | expr ("+" | "-") expr   (left-assoc)
;;            | expr ("*" | "/") expr   (left-assoc, binds tighter than + -)

(require (prefix-in : incr-lex)
         rope
         "../private/ast.rkt"
         "../private/combinators.rkt"
         "../private/green.rkt"
         "../private/hole-ghost.rkt"
         "../private/pratt.rkt"
         "../private/printer.rkt")

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
;;; Grammar Tables
;;; --------------------------------------------------------------------------

;; Standard binding-power-pair scheme: (left-bp . right-bp), right-bp =
;; left-bp + 1 encodes left-associativity (see pratt.rkt's header comment).
;; Star/Slash's right-bp (4) sits below unary minus's fixed bp (5), so "-2*3"
;; parses as "(-2)*3", the usual convention.
(define arith-bp-table
  (hash 'Plus  (cons 1 2)
        'Minus (cons 1 2)
        'Star  (cons 3 4)
        'Slash (cons 3 4)))

(define UNARY-MINUS-BP 5)

(define arith-nud-table
  (hash 'Number (λ (toks) (consume-as 'atom toks))
        'Ident  (λ (toks) (consume-as 'atom toks))
        'Minus  (nud-prefix 'Minus UNARY-MINUS-BP)
        'LParen (nud-paren 'LParen 'RParen)))

(define arith-led-table
  (hash 'Plus  (led-infix 'Plus)
        'Minus (led-infix 'Minus)
        'Star  (led-infix 'Star)
        'Slash (led-infix 'Slash)))

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

(define (parse-arith-string str)
  (define sess (:make-session arith-lex arith-apply-edit string-rope-ropeable str))
  (define toks (:session->tokens-list sess))
  (define-values (tree remaining)
    (parameterize ([current-nud-table arith-nud-table]
                   [current-led-table arith-led-table]
                   [current-bp-table  arith-bp-table])
      (parse-program toks)))
  (unless (eq? (peek-kind remaining) 'incr-lex:eof)
    (error 'parse-arith-string "parser did not consume the full token stream"))
  tree)

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

(module+ main
  (for ([src (list "1 + 2 * 3"
                    "(1 + 2) * 3"
                    "-x * (y - 1)"
                    "1 +"                ; missing rhs
                    "(1 + 2"             ; missing RParen
                    "1 @ 2"              ; unrecognized token
                    "1 2"                ; two juxtaposed atoms - see notes
                    "(1 2)")])           ; juxtaposed INSIDE parens - see notes
    (define tree (parse-arith-string src))
    (printf "--- source ---\n~a\n" src)
    (printf "--- debug tree ---\n~a\n" (green->debug-string tree))
    (printf "--- round-trip ~a ---\n\n"
            (if (equal? (green->source tree) src) "OK" "MISMATCH"))))
