#lang racket/base

;; incr-parse/core/printer.rkt
;;
;; Two printers over the same Green tree:
;;   green->source : exact bidirectional reproduction of the original text -
;;     ghosts contribute nothing, staged holes emit their wrapped content
;;     verbatim, and empty holes emit "".
;;   green->debug-string : human-legible tree dump for REPL/test use - ghosts
;;     and holes are rendered explicitly with markers, so you can see recovery
;;     structure while debugging the parser itself.

(require (prefix-in lex: incr-lex)
         racket/list
         racket/match
         racket/string
         rope
         "green.rkt"
         "hole-ghost.rkt")

(provide green->debug-string
         green->source)

;; ---------------------------------------------------------------------
;; Bidirectional (exact source reproduction)
;; ---------------------------------------------------------------------

(define (green->source g)
  (apply string-append (green->source-frags g)))

(define (green->source-frags g)
  (cond
    [(ghost? g) null]                   ; contributes no text
    [(hole? g)
     (if (hole-content g)
         (green->source-frags (hole-content g)) ; staged: verbatim
         null)]                                 ; empty: nothing
    [(green-token? g)
     (list (token->source-stub (green-token-token g)))]
    [(green-branch? g)
     (append-map green->source-frags (green-branch-children g))]))

;; Full leaf text = leading trivia + the token's own literal text + trailing
;; trivia. token-width already counts all three, so the reconstructed string's
;; length must match it exactly.
(define (token->source-stub tok)
  (string-append*
   (append (map trivia->source-stub (lex:token-leading tok))
           (list (rope->string (lex:token-payload tok)))
           (map trivia->source-stub (lex:token-trailing tok)))))

(define (trivia->source-stub triv)
  (rope->string (lex:trivia-payload triv)))

;; ---------------------------------------------------------------------
;; Debug (holes/ghosts visible, for REPL & test use)
;; ---------------------------------------------------------------------

(define (green->debug-string g [depth 0])
  (define pad (make-string (* 2 depth) #\space))
  (cond
    [(ghost? g)
     (format "~a⟨ghost:~a⟩" pad (ghost-of g))]
    [(hole? g)
     (if (hole-content g)
         (format "~a⟦hole:staged~a\n~a⟧"
                 pad
                 (diagnostics->debug-suffix (hole-diagnostics g))
                 (green->debug-string (hole-content g) (add1 depth)))
         (format "~a⟦hole:empty~a⟧"
                 pad (diagnostics->debug-suffix (hole-diagnostics g))))]
    [(green-token? g)
     (define tok (green-token-token g))
     ;; Shows the grammar-assigned kind (green-tree-kind), the raw lexer
     ;; token-kind (may differ, e.g. a grammar-level `Ident` wrapping a
     ;; lexer-level `Word`), the literal text (payload only, no trivia - debug
     ;; view, not meant to round-trip), and any lexer-level diagnostics riding
     ;; on the raw token itself, distinct from hole-level parse diagnostics.
     (format "~a~a/~a ‹~a›~a"
             pad
             (green-tree-kind g)
             (lex:token-kind tok)
             (rope->string (lex:token-payload tok))
             (lexer-diagnostics->debug-suffix (lex:token-diagnostics tok)))]
    [(green-branch? g)
     (string-join (cons (format "~a(~a" pad (green-tree-kind g))
                        (append (map (λ (c) (green->debug-string c (add1 depth)))
                                     (green-branch-children g))
                                (list (format "~a)" pad))))
                  "\n")]))

(define (diagnostics->debug-suffix diags)
  (if (null? diags)
      ""
      (format " [~a]" (string-join (map (λ (d) (format "~a: ~a"
                                                       (diagnostic-severity d)
                                                       (diagnostic-message d)))
                                        diags)
                                   "; "))))

;; incr-lex's own diagnostic struct has the same (severity message offset
;; width) shape as ours (see core/span.rkt notes), so this is intentionally
;; near-identical to diagnostics->debug-suffix above We keep them separate
;; because the two diagnostic sources (lexer-level on raw tokens vs.
;; hole-level on parse recovery) are conceptually distinct and I'd rather not
;; blur that in the debug output by sharing one formatter.
(define (lexer-diagnostics->debug-suffix diags)
  (if (null? diags)
      ""
      (format " {lex: ~a}"
              (string-join (map (λ (d) (format "~a: ~a"
                                               (lex:diagnostic-severity d)
                                               (lex:diagnostic-message d)))
                                diags)
                           "; "))))
