#lang racket/base

;; incr-parse/grammar.rkt
;;
;; The authoring API: everything needed to WRITE a grammar, in one require.
;;
;;   (require incr-parse/grammar)
;;
;; replaces the old prototype's pattern of five-to-seven separate
;; "private/*.rkt" requires at the top of every langs/*.rkt file. See
;; ../examples/sexpr.rkt for a complete, minimal worked example: a lexer
;; (built with incr-lex, required separately - this library doesn't
;; reprovide incr-lex's own API, since a grammar's lexer is genuinely a
;; separate concern), a parser built from the pieces below, and a `grammar`
;; value at the bottom ready to hand to a session (see ../main.rkt).
;;
;; This module has no opinion on HOW a grammar is written - core/dsl.rkt's
;; define-grammar sugar is included for the simple RD case, and
;; core/operator-grammar.rkt's define-operator-grammar covers Pratt/operator
;; grammars declaratively, but
;; every real example grammar in this library is written directly against
;; combinators.rkt/pratt.rkt, and that remains the fully-supported, expected
;; path for anything beyond the simplest single-token-lookahead grammar. See
;; core/dsl.rkt's own header for why.
;;
;; Reprovided, by concern:
;;
;;   Green trees & recovery vocabulary  - core/green.rkt, core/hole-ghost.rkt,
;;                                        core/span.rkt
;;   Parser input                       - core/token-stream.rkt
;;   Recursive-descent primitives       - core/combinators.rkt
;;   Pratt/precedence-climbing engine   - core/pratt.rkt
;;   Memoization (for a custom rule     - core/memo.rkt's memoize/memo-ref!;
;;     shape define-grammar can't         current-parse-cache/-offset are
;;     express, e.g. Pratt's own          re-provided too, for a grammar
;;     parse-expr)                        writing its own low-level entry
;;                                        point outside of document-parse!
;;   Optional case-dispatch/table sugar - core/dsl.rkt (see status note above)
;;   CST -> AST elaboration             - core/elaborate.rkt
;;   Exact-source round-tripping        - core/printer.rkt
;;   Positional (Red) tree views        - core/red.rkt
;;   The `grammar` value constructor    - core/session.rkt (only `make-grammar`
;;                                        and `make-grammar*` are relevant to
;;                                        an author; document/session belong
;;                                        to ../main.rkt's runtime API, not
;;                                        here, and are not reprovided)

(require "core/green.rkt"
         "core/hole-ghost.rkt"
         "core/span.rkt"
         "core/token-stream.rkt"
         "core/combinators.rkt"
         "core/pratt.rkt"
         "core/memo.rkt"
         "core/dsl.rkt"
         "core/elaborate.rkt"
         "core/printer.rkt"
         "core/red.rkt"
         (only-in "core/session.rkt" grammar? make-grammar make-grammar*
                  grammar-lexer grammar-apply-edit grammar-start
                  grammar-setup grammar-ropeable)
         (only-in "core/operator-grammar.rkt" define-operator-grammar))

(provide (all-from-out "core/green.rkt")
         (all-from-out "core/hole-ghost.rkt")
         (all-from-out "core/span.rkt")
         (all-from-out "core/token-stream.rkt")
         (all-from-out "core/combinators.rkt")
         (all-from-out "core/pratt.rkt")
         (all-from-out "core/memo.rkt")
         (all-from-out "core/dsl.rkt")
         (all-from-out "core/elaborate.rkt")
         (all-from-out "core/printer.rkt")
         (all-from-out "core/red.rkt")
         make-grammar grammar? make-grammar*
         grammar-lexer grammar-apply-edit grammar-start
         grammar-setup grammar-ropeable
         define-operator-grammar)
