#lang racket/base

;; incr-parse/langs/toplevel.rkt
;;
;; Toy grammar #3: newline-separated top-level statements over arith.rkt's own
;; expression grammar.
;;
;;   x = 1
;;   y = x + 2
;;   x + y
;;
;; Grammar:
;;   program   := stmt-line*
;;   stmt-line := stmt seps
;;   stmt      := Ident "=" expr   (assignment)
;;              | expr             (bare expression statement)
;;   seps      := Newline*
;;
;; expr is arith.rkt's parse-expr, reused directly against its own nud/led/bp
;; tables - this file adds no new expression syntax, only statement sequencing
;; on top.
;;
;; Newline is promoted from arith.rkt's trivia to a real token here, via a
;; second define-lexer instantiation over the same token definitions
;; (arith-tokens), not a reuse of arith-lex itself. arith-lex still treats
;; Newline as leading/trailing trivia, which would silently swallow the
;; newlines this grammar needs to see.
;;
;; Disambiguating "Ident = expr" from a bare "Ident" expression needs one
;; token of lookahead past the Ident. That's peek2-kind, a small addition to
;; combinators.rkt alongside peek-kind. try/alt would also work here.
;;
;; Malformed-input handling:
;;   - A missing separator between two statements is not diagnosed at all. The
;;     next stmt-line just starts wherever the previous one's tokens left off,
;;     the same permissive stance arith.rkt already takes on juxtaposed
;;     expressions (the "concave grout" gap).
;;   - A blank line before the very first statement currently surfaces as a
;;     staged hole wrapping that stray Newline token (parse-expr's
;;     unrecognized-token fallback, since Newline isn't in its nud table).
;;     Blank lines BETWEEN statements are fine, absorbed by seps; only a
;;     leading blank line hits this.
;;   - Anything parse-expr itself already recovers from (missing operand,
;;     unrecognized token, unbalanced parens) recovers exactly the same way
;;     here, since expr is arith.rkt's parse-expr, unmodified.

(require (prefix-in : incr-lex)
         rope
         "../private/ast.rkt"
         "../private/combinators.rkt"
         "../private/green.rkt"
         "../private/hole-ghost.rkt"
         "../private/memo.rkt"
         "../private/pratt.rkt"
         "../private/printer.rkt"
         "../private/token-stream.rkt"
         "arith.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Lexer
;;; --------------------------------------------------------------------------

(:define-tokens toplevel-extra-tokens
  [Equals := "="])

;; arith-tokens is arith.rkt's rule table, reused wholesale. The only new
;; clause this grammar needs is Equals, so that's all toplevel-extra-tokens
;; adds. define-lexer just needs one table covering every name it's given
;; across #:token-set/#:leading/#:trailing/#:newline, so the two get merged.
(define toplevel-token-table
  (for/fold ([table arith-tokens]) ([(name rule) (in-hash toplevel-extra-tokens)])
    (hash-set table name rule)))

;; => defines toplevel-lex and toplevel-apply-edit
(:define-lexer toplevel
  #:tokens    toplevel-token-table
  #:token-set [LParen RParen Plus Minus Star Slash Equals Number Ident Newline]
  #:leading   [Whitespace]
  #:trailing  [Whitespace]
  #:newline   [Newline])

;;; --------------------------------------------------------------------------
;;; Parser
;;; --------------------------------------------------------------------------

(define parse-assign
  (memoize 'assign
    (seq 'assign
         (expect 'Ident)
         (expect 'Equals)
         (λ (toks) (parse-expr toks 0)))))

;; One token of lookahead past a leading Ident is enough to tell an
;; assignment from a bare expression statement that just happens to start
;; with a variable reference.
(define parse-stmt
  (memoize 'stmt
    (λ (toks)
      (if (and (eq? (peek-kind toks) 'Ident) (eq? (peek2-kind toks) 'Equals))
          (parse-assign toks)
          (parse-expr toks 0)))))

(define parse-seps
  (rep 'seps
       (λ (toks) (consume-as 'newline toks))
       (λ (kind) (not (eq? kind 'Newline)))))

(define parse-stmt-line
  (memoize 'stmt-line (seq 'stmt-line parse-stmt parse-seps)))

(define (program-stop? kind) (eq? kind 'incr-lex:eof))

;; Named toplevel-program, not the generic program to avoid a conflict with
;; arith.rkt, required below, which registers its own top-level elaborator
;; under 'program for an unrelated top-level shape. Both modules load into the
;; same process wherever this file is used, so the two kind symbols must not
;; collide in the shared current-ast-elaborators table.

(define parse-program
  (rep 'toplevel-program parse-stmt-line program-stop?))

;;; --------------------------------------------------------------------------
;;; AST
;;; --------------------------------------------------------------------------

(struct ast-assign (name expr) #:transparent)
(struct ast-program (stmts) #:transparent)

(define-elaborator assign (branch)
  (define children (green-branch-children branch))
  (ast-assign (elaborate (car children)) (elaborate (caddr children))))

;; seps carries no semantic content, only the statement itself does.
(define-elaborator stmt-line (branch)
  (elaborate (car (green-branch-children branch))))

(define-elaborator toplevel-program (branch)
  (ast-program (map elaborate (green-branch-children branch))))

;;; --------------------------------------------------------------------------
;;; Entry Point
;;; --------------------------------------------------------------------------

(define (parse-toplevel-string str)
  (define sess (:make-session toplevel-lex toplevel-apply-edit string-rope-ropeable str))
  (define toks (tokens->stream (:session->tokens-list sess)))
  (define-values (tree remaining)
    (parameterize ([current-nud-table arith-nud-table]
                   [current-led-table arith-led-table]
                   [current-bp-table  arith-bp-table])
      (parse-program toks)))
  (unless (eq? (peek-kind remaining) 'incr-lex:eof)
    (error 'parse-toplevel-string "parser did not consume the full token stream"))
  tree)

(define (elaborate-toplevel-string str)
  (elaborate (parse-toplevel-string str)))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require racket/list
           rackunit
           incr-lex/engine)

  (define (check-round-trip src)
    (check-equal? (green->source (parse-toplevel-string src)) src))

  (test-case "round-trip: the checkpoint's own example"
    (check-round-trip "x = 1\ny = x + 2\nx + y"))

  (test-case "round-trip: blank lines between statements"
    (check-round-trip "x = 1\n\ny = 2\n"))

  (test-case "round-trip: bare expression statements, no assignment at all"
    (check-round-trip "1 + 2\n3 * 4"))

  (test-case "an assignment produces an 'assign branch: Ident, Equals, expr"
    (define tree (parse-toplevel-string "x = 1 + 2"))
    (define line (car (green-branch-children tree)))
    (define stmt (car (green-branch-children line)))
    (check-eq? (green-tree-kind stmt) 'assign)
    (define-values (name eq expr) (apply values (green-branch-children stmt)))
    (check-eq? (green-tree-kind name) 'Ident)
    (check-eq? (green-tree-kind eq) 'Equals)
    (check-eq? (green-tree-kind expr) 'binop))

  (test-case "a bare Ident that isn't followed by = is an expression, not an assignment"
    (define tree (parse-toplevel-string "x + 1"))
    (define line (car (green-branch-children tree)))
    (define stmt (car (green-branch-children line)))
    (check-eq? (green-tree-kind stmt) 'binop))

  (test-case "AST: assignment and expression statements elaborate distinctly"
    (define ast (elaborate-toplevel-string "x = 1\nx + 1"))
    (check-true (ast-program? ast))
    (define stmts (ast-program-stmts ast))
    (check-equal? (length stmts) 2)
    (check-true (ast-assign? (car stmts)))
    (check-true (ast-binop? (cadr stmts))))

  (test-case "recovery: parse-expr's own fallbacks still apply inside a statement"
    (check-round-trip "1 +")     ; missing rhs -> empty hole, same as arith.rkt
    (check-round-trip "(1 + 2")) ; missing RParen -> ghost, same as arith.rkt

  (test-case "incremental reparse: an untouched statement's tree survives an edit to a different line"
    (define src "x = 1\ny = 2\nz = 3")
    (define sess1 (make-parse-session toplevel-lex toplevel-apply-edit string-rope-ropeable src))
    (define tree1
      (parameterize ([current-nud-table arith-nud-table]
                     [current-led-table arith-led-table]
                     [current-bp-table  arith-bp-table])
        (parse-session-run sess1 parse-program)))
    ;; offset 4 is the "1" in "x = 1" - replace it with "11"
    (define sess2 (parse-session-edit sess1 4 1 "11"))
    (define tree2
      (parameterize ([current-nud-table arith-nud-table]
                     [current-led-table arith-led-table]
                     [current-bp-table  arith-bp-table])
        (parse-session-run sess2 parse-program)))
    (check-equal? (green->source tree2) "x = 11\ny = 2\nz = 3")
    (define (find-z-line t)
      (cond [(and (green-branch? t) (eq? (green-tree-kind t) 'stmt-line)
                  (let ([stmt (car (green-branch-children t))])
                    (and (eq? (green-tree-kind stmt) 'assign)
                         (equal? (rope->string
                                  (token-payload
                                   (green-token-token (car (green-branch-children stmt)))))
                                 "z"))))
             t]
            [(green-branch? t) (ormap find-z-line (green-branch-children t))]
            [else #f]))
    (define z-line-1 (find-z-line tree1))
    (define z-line-2 (find-z-line tree2))
    (check-eq? z-line-1 z-line-2)
    (parse-session-unload! sess2)))

(module+ main
  (for ([src (list "x = 1\ny = x + 2\nx + y"
                    "x = 1\n\ny = 2\n"      ; blank line between statements
                    "\nx = 1"                ; blank line before the first statement - see notes
                    "1 2"                    ; two juxtaposed statements, no separator
                    "x = ")])                ; missing rhs
    (define tree (parse-toplevel-string src))
    (printf "--- source ---\n~s\n" src)
    (printf "--- debug tree ---\n~a\n" (green->debug-string tree))
    (printf "--- round-trip ~a ---\n\n"
            (if (equal? (green->source tree) src) "OK" "MISMATCH"))))
