#lang racket/base

;; incr-parse/main.rkt
;;
;; The runtime API: create a session, install one or more grammars (each
;; with its own starting point - see grammar.rkt/core/session.rkt's
;; `grammar` constructor), open potentially many documents against them,
;; and incrementally edit those documents over time, without needing to
;; know anything about the library's internal machinery.
;;
;;   (require incr-parse
;;            (prefix-in sexpr: incr-parse/examples/sexpr))  ; a grammar
;;
;;   (define sess (make-session))
;;   (session-install-grammar! sess 'sexpr sexpr:sexpr-grammar)
;;   (session-open! sess 'sexpr "doc-1" "(+ 1 2)")
;;   (session-edit! sess "doc-1" 3 1 "-")          ; (- 1 2)
;;   (green->source (document-tree (session-document sess "doc-1")))
;;   ; => "(- 1 2)"
;;
;; A session is an explicit value, not a dynamically-scoped default - create
;; as many independent sessions as needed; they never share a grammar or
;; document table. "Concurrently" here means many documents open and
;; independently edited over time, matching a language-server-style backend
;; for a live editing session - it does NOT mean this library is safe for
;; literal, lock-free multi-threaded mutation of the SAME document or
;; session from two OS threads at once. Every mutable table involved (a
;; document's cache, a session's grammar/document tables) is a plain
;; mutable hash, the same convention used throughout core/, with no locking
;; anywhere in this library.
;;
;; This module re-provides core/session.rkt's full session/document/grammar
;; API, plus the minimal read-only vocabulary needed to inspect a parsed
;; document's tree (Green-tree predicates/accessors, Red-tree navigation,
;; diagnostics, and exact-source round-tripping) without also requiring
;; grammar.rkt. Writing a NEW grammar is grammar.rkt's job, not this file's
;; - see that module's header.

(require "core/session.rkt"
         (only-in "core/green.rkt"
                  green-tree? green-tree-kind green-tree-width
                  green-token? green-token-token
                  green-branch? green-branch-children)
         (only-in "core/hole-ghost.rkt"
                  hole? hole-status hole-content hole-diagnostics
                  ghost? ghost-of
                  diagnostic? diagnostic-severity diagnostic-message diagnostic-span)
         (only-in "core/span.rkt" span? span-offset span-width span-end)
         (only-in "core/red.rkt"
                  red-node? red-node-green red-node-offset red-node-width
                  red-node-kind red-node-parent red-children
                  red-next-sibling red-prev-sibling
                  red-ancestors red-enclosing-of-kind)
         (only-in "core/printer.rkt" green->source green->debug-string))

(provide (all-from-out "core/session.rkt")
         green-tree? green-tree-kind green-tree-width
         green-token? green-token-token
         green-branch? green-branch-children
         hole? hole-status hole-content hole-diagnostics
         ghost? ghost-of
         diagnostic? diagnostic-severity diagnostic-message diagnostic-span
         span? span-offset span-width span-end
         red-node? red-node-green red-node-offset red-node-width
         red-node-kind red-node-parent red-children
         red-next-sibling red-prev-sibling
         red-ancestors red-enclosing-of-kind
         green->source green->debug-string)

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------
;;
;; Exercises this file's OWN reprovided bindings end to end - not a repeat
;; of core/session.rkt's own unit tests (which cover the mechanics in much
;; more depth) - to catch a reprovide typo or an accidentally-dropped
;; binding, which a require/provide-only module can't catch any other way
;; without something actually calling each name.

(module+ test
  (require rackunit
           (prefix-in : incr-lex)
           (only-in "core/combinators.rkt" rep consume-as)
           (only-in "core/memo.rkt" memoize))

  (:define-tokens words-tokens
    [WS   := (+ :ws)]
    [Word := (+ :alpha)])

  (:define-lexer words
    #:tokens    words-tokens
    #:token-set [Word]
    #:leading   [WS]
    #:trailing  [WS]
    #:newline   [])

  ;; core/combinators.rkt's rep/consume-as/memoize are pulled in directly
  ;; here only because this is main.rkt's OWN test, exercising main.rkt's
  ;; reprovided bindings in isolation - a real grammar author would
  ;; `(require incr-parse/grammar)` for these instead (see grammar.rkt).
  (define parse-word (memoize 'word (λ (t) (consume-as 'word t))))

  (define (parse-words toks)
    ((rep 'words parse-word (λ (k) (eq? k 'incr-lex:eof)))
     toks))

  (define words-grammar
    (make-grammar #:lexer words-lex #:apply-edit words-apply-edit #:start parse-words))

  (test-case "end-to-end: session + grammar + open + edit + inspect, using only main.rkt's own reprovided bindings"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (session-open! sess 'words "doc-1" "foo bar")
    (define doc (session-edit! sess "doc-1" 0 3 "quux"))
    (check-equal? (green->source (document-tree doc)) "quux bar")
    (check-true (green-branch? (document-tree doc)))
    (check-equal? (length (green-branch-children (document-tree doc))) 2)
    (define root (document-red-root doc))
    (check-equal? (red-node-width root) 8)
    (define first-word (car (red-children root)))
    (check-equal? (red-node-kind first-word) 'word)
    (check-false (red-prev-sibling first-word))
    (check-eq? (red-node-kind (red-next-sibling first-word)) 'word)
    (check-equal? (document-diagnostics doc) null)))
