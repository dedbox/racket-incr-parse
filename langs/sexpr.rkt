#lang racket/base

;; incr-parse/langs/sexpr.rkt
;;
;; Toy grammar #1: parenthesized s-expressions.
;;
;; Grammar:
;;   program := sexpr*
;;   sexpr   := atom | list
;;   atom    := Symbol | Number
;;   list    := "(" sexpr* ")"
;;
;; Malformed-input handling:
;;   - a stray ")" anywhere an expression was expected -> staged hole
;;     wrapping that one token, consumed (guarantees progress)
;;   - an unrecognized token anywhere an expression was expected ->
;;     same, generic message
;;   - end of file where an expression was expected (only reachable
;;     inside an unterminated list) -> empty hole, no token consumed
;;   - a list missing its closing paren -> ghost RParen, no token
;;     consumed, list closes cleanly at EOF or wherever the enclosing
;;     context resumes

(require (prefix-in : incr-lex)
         rope
         "../private/ast.rkt"
         "../private/combinators.rkt"
         "../private/green.rkt"
         "../private/hole-ghost.rkt"
         "../private/memo.rkt"
         "../private/printer.rkt"
         "../private/token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Lexer
;;; --------------------------------------------------------------------------

;; Extra characters a Symbol may start or continue with, beyond alpha/alnum -
;; enough for a toy grammar.
(define symbol-extra-char (:char-set "+-*/<>=!?_.:"))

(:define-tokens sexpr-tokens
  ;; Trivia
  [Whitespace := (+ :ws)]
  [Newline    := :nl]
  [Comment    := (seq ";" (* (not-char :nl)))]
  ;; Tokens
  [LParen     := "("]
  [RParen     := ")"]
  [Number     := (+ :digit)]
  [Symbol     := (seq (or :alpha symbol-extra-char)
                       (* (or :alnum symbol-extra-char)))])

;; => defines sexpr-lex and sexpr-apply-edit
(:define-lexer sexpr
  #:tokens    sexpr-tokens
  #:token-set [LParen RParen Number Symbol]
  #:leading   [Whitespace Newline Comment]
  #:trailing  [Whitespace Comment]
  #:newline   [Newline])

;;; --------------------------------------------------------------------------
;;; Parser
;;; --------------------------------------------------------------------------

(define (sexpr-list-stop? kind)
  (or (eq? kind 'RParen) (eq? kind 'incr-lex:eof)))

(define (program-stop? kind)
  (eq? kind 'incr-lex:eof))

;; atom/list wrap Symbol and Number tokens under one grammar-level
;; 'atom kind - the lexer-level distinction (Symbol vs Number) stays
;; recoverable later via the wrapped token's own token-kind; see
;; consume-as's comment in combinators.rkt.
(define (match-peek toks)
  (case (peek-kind toks)
    [(LParen)        (parse-list toks)]
    [(Symbol Number) (consume-as 'atom toks)]
    [(RParen)        (hole-for-unexpected "unexpected closing parenthesis" toks)]
    [(incr-lex:eof)  (empty-hole-here "expected an expression" toks)]
    [else
     (hole-for-unexpected "expected an expression, found unrecognized input" toks)]))

(define parse-sexpr (memoize 'sexpr match-peek))

(define parse-list
  (memoize 'list
           (λ (toks)
             ((seq 'list
                   (expect 'LParen)
                   (rep 'elements parse-sexpr sexpr-list-stop?)
                   (expect 'RParen))
              toks))))

(define parse-program
  (rep 'sexprs parse-sexpr program-stop?))

;;; --------------------------------------------------------------------------
;;; AST
;;; --------------------------------------------------------------------------

;; ast-list holds already-elaborated elements, without the parens, since they
;; carry no semantic content once the grouping is in the tree. ast-program is
;; the top-level sequence of sexprs in a file.
(struct ast-list (elements) #:transparent)
(struct ast-program (sexprs) #:transparent)

(define-elaborator list (branch)
  (define elements (cadr (green-branch-children branch)))
  (ast-list (map elaborate (green-branch-children elements))))

(define-elaborator sexprs (branch)
  (ast-program (map elaborate (green-branch-children branch))))

;;; --------------------------------------------------------------------------
;;; Entry point
;;; --------------------------------------------------------------------------

;; Non-incremental for now, per the agreed build order - lexes the whole
;; string via a fresh incr-lex session, then parses the full token list in one
;; pass.
(define (parse-sexpr-string str)
  (define sess (:make-session sexpr-lex sexpr-apply-edit string-rope-ropeable str))
  (define toks (tokens->stream (:session->tokens-list sess)))
  (define-values (tree remaining) (parse-program toks))
  (unless (eq? (peek-kind remaining) 'incr-lex:eof)
    (error 'parse-sexpr-string "parser did not consume the full token stream"))
  tree)

(define (elaborate-sexpr-string str)
  (elaborate (parse-sexpr-string str)))

;; The bound grammar descriptor for this file, for use with
;; make-parse-session/parse-session-run/workspace-open!. Since sexpr.rkt is
;; RD-only and therefore installs no Pratt tables, we do not need to specify
;; #:with-setup.
(define sexpr-descriptor
  (make-grammar-descriptor sexpr-lex sexpr-apply-edit parse-program
                           #:ropeable string-rope-ropeable))

(module+ test
  (require racket/list
           rackunit
           incr-lex/engine)

  (define (check-round-trip src)
    (check-equal? (green->source (parse-sexpr-string src)) src))

  (test-case "round-trip: well-formed input"
    (check-round-trip "(+ 1 2)")
    (check-round-trip "(foo (bar 1 2) baz)")
    (check-round-trip "; just a comment\n(ok)"))

  (test-case "round-trip: recovery cases"
    (check-round-trip "(unclosed 1 2")
    (check-round-trip ") stray")
    (check-round-trip "(a (b )"))

  (test-case "missing RParen produces exactly one ghost of kind 'RParen"
    (define tree (parse-sexpr-string "(unclosed 1 2"))
    (define list-node (car (green-branch-children tree)))
    (define last-child (last (green-branch-children list-node)))
    (check-true (ghost? last-child))
    (check-eq? (ghost-of last-child) 'RParen))

  (test-case "stray RParen produces a staged hole wrapping one RParen token"
    (define tree (parse-sexpr-string ") stray"))
    (define first-child (car (green-branch-children tree)))
    (check-true (hole? first-child))
    (check-eq? (hole-status first-child) 'staged)
    (define wrapped (hole-content first-child))
    (check-true (green-token? wrapped))
    (check-eq? (:token-kind (green-token-token wrapped)) 'RParen)
    ;; and parsing continues past the bad token
    (define second-child (cadr (green-branch-children tree)))
    (check-eq? (green-tree-kind second-child) 'atom))

  (test-case "well-formed list has no holes or ghosts anywhere"
    (define tree (parse-sexpr-string "(foo (bar 1 2) baz)"))
    (define (clean? t)
      (cond [(hole? t) #f]
            [(ghost? t) #f]
            [(green-branch? t) (andmap clean? (green-branch-children t))]
            [else #t]))
    (check-true (clean? tree)))

  (test-case "atoms preserve their underlying lexer-level token kind"
    (define tree (parse-sexpr-string "(x 1)"))
    (define elements (cadr (green-branch-children (car (green-branch-children tree)))))
    (define kinds (map (λ (a) (:token-kind (green-token-token a)))
                        (green-branch-children elements)))
    (check-equal? kinds '(Symbol Number)))

  (test-case "incremental reparse: untouched subtree is eq? across an edit"
    (define sess1
      (make-parse-session
       sexpr-descriptor
       "(quux (bar 1 2) baz)")) ; was (foo ...) - collided with an earlier test-case's fixture
    (define tree1 (parse-session-tree (parse-session-run sess1)))
    ;; offset 10 is the "1" inside (bar 1 2) - replace it with "11"
    (define sess2 (parse-session-edit sess1 11 1 "11"))
    (define sess2* (parse-session-run sess2))
    (define tree2 (parse-session-tree sess2*))
    (check-equal? (green->source tree2) "(quux (bar 11 2) baz)")
    (define (find-baz t)
      (cond [(and (green-token? t)
                  (equal? (rope->string (token-payload (green-token-token t))) "baz")) t]
            [(green-branch? t) (ormap find-baz (green-branch-children t))]
            [else #f]))
    (define baz1 (find-baz tree1))
    (define baz2 (find-baz tree2))
    (check-eq? baz1 baz2)
    (parse-session-unload! sess2*))

  (test-case "AST: nested list elaborates to nested ast-list, parens dropped"
    (define ast (elaborate-sexpr-string "(foo (bar 1) baz)"))
    (check-true (ast-program? ast))
    (define top (car (ast-program-sexprs ast)))
    (check-true (ast-list? top))
    (define elems (ast-list-elements top))
    (check-equal? (length elems) 3)
    (check-true (ast-leaf? (car elems)))
    (check-equal? (rope->string (ast-leaf-text (car elems))) "foo")
    (check-true (ast-list? (cadr elems))))

  (test-case "AST: a hole survives elaboration with its diagnostics intact"
    (define ast (elaborate-sexpr-string ") stray"))
    (define first (car (ast-program-sexprs ast)))
    (check-true (ast-hole? first))
    (check-true (ast-hole-staged? first))
    (check-equal? (length (ast-hole-diagnostics first)) 1)))
