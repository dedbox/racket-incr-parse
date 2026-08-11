#lang racket/base

;; incr-parse/private/workspace.rkt
;;
;; A document-URI/ID -> parse-session table, sitting above individual
;; sessions. This abstraction enables many documents open at once.
;;
;; The key is whatever the caller wants to identify a document by. It can be a
;; URI string, a symbol, a path, or anything else that can be used as an
;; equal?-hashable key.

(require "memo.rkt")

(provide (all-defined-out))

(define current-workspace (make-parameter (make-hash)))

;; Creates a new session for key from raw-chunk using descriptor, installs it
;; in the current workspace, and returns it. It fails if key is already open.
;; Check workspace-has-key? first if collisions are possible.
(define (workspace-open! key descriptor raw-chunk)
  (when (hash-has-key? (current-workspace) key)
    (error 'workspace-open! "already open: ~e" key))
  (define sess (make-parse-session descriptor raw-chunk))
  (hash-set! (current-workspace) key sess)
  sess)

(define (workspace-has-key? key)
  (hash-has-key? (current-workspace) key))

(define (workspace-get key)
  (hash-ref (current-workspace) key #f))

;; After parse-session-edit or parse-session-run returns a new session value,
;; the caller should call here instead of modifying the table directly. Fails
;; if key isn't open.
(define (workspace-update! key f)
  (define sess (workspace-get key))
  (unless sess (error 'workspace-update! "not open: ~e" key))
  (define sess* (f sess))
  (hash-set! (current-workspace) key sess*)
  sess*)

;; Explicit, deterministic disposal. Drops the session from the table amd
;; clears its cache immediately. It does not wait on GC. When key isn't open,
;; this is a no-op.
(define (workspace-close! key)
  (define sess (workspace-get key))
  (when sess
    (parse-session-unload! sess)
    (hash-remove! (current-workspace) key))
  (void))

(define (workspace-keys) (hash-keys (current-workspace)))

(module+ test
  (require (except-in rackunit fail)
           racket/set
           rope
           (prefix-in : incr-lex)
           "combinators.rkt"
           "printer.rkt")

  ;; Minimal descriptor: a trivial one-token-kind lexer, RD-only entry point
  ;; (no Pratt tables, with-setup left at its identity default).
  (:define-tokens ws-test-tokens
                  [WS := (+ :ws)]
                  [Word := (+ :alpha)])

  (:define-lexer ws-test
                 #:tokens    ws-test-tokens
                 #:token-set [Word]
                 #:leading   [WS]
                 #:trailing  [WS]
                 #:newline   [])

  (define (parse-words toks)
    ((rep 'words (λ (t) (consume-as 'word t))
          (λ (k) (eq? k 'incr-lex:eof)))
     toks))

  (define ws-test-descriptor
    (make-grammar-descriptor ws-test-lex ws-test-apply-edit parse-words
                             #:ropeable string-rope-ropeable))

  (test-case "workspace-open!/get/close! round-trip"
    (parameterize ([current-workspace (make-hash)])
      (check-false (workspace-get "doc-1"))
      (define sess (workspace-open! "doc-1" ws-test-descriptor "foo bar"))
      (check-eq? (workspace-get "doc-1") sess)
      (check-true (workspace-has-key? "doc-1"))
      (workspace-close! "doc-1")
      (check-false (workspace-get "doc-1"))
      (check-false (workspace-has-key? "doc-1"))))

  (test-case "workspace-open!: opening an already-open key errors"
    (parameterize ([current-workspace (make-hash)])
      (workspace-open! "doc-1" ws-test-descriptor "foo")
      (check-exn exn:fail? (λ () (workspace-open! "doc-1" ws-test-descriptor "bar")))))

  (test-case "workspace-close!: closing a key that was never open is a no-op"
    (parameterize ([current-workspace (make-hash)])
      (workspace-close! "never-opened")))

  (test-case "workspace-update!: threads a new session value back into the table"
    (parameterize ([current-workspace (make-hash)])
      (workspace-open! "doc-1" ws-test-descriptor "foo bar")
      (define ran (workspace-update! "doc-1" parse-session-run))
      (check-eq? (workspace-get "doc-1") ran)
      (check-equal? (green->source (parse-session-tree ran)) "foo bar")))

  (test-case "workspace-update!: erroring on a key that isn't open"
    (parameterize ([current-workspace (make-hash)])
      (check-exn exn:fail? (λ () (workspace-update! "doc-1" values)))))

  (test-case "workspace-keys: reflects what's currently open"
    (parameterize ([current-workspace (make-hash)])
      (workspace-open! "a" ws-test-descriptor "foo")
      (workspace-open! "b" ws-test-descriptor "bar")
      (check-equal? (list->set (workspace-keys)) (list->set '("a" "b")))))

  (test-case "two sessions under different keys never share a cache"
    (parameterize ([current-workspace (make-hash)])
      (define s1 (workspace-open! "a" ws-test-descriptor "foo"))
      (define s2 (workspace-open! "b" ws-test-descriptor "bar"))
      (check-false (eq? (parse-session-cache s1) (parse-session-cache s2))))))
