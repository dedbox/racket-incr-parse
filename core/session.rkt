#lang racket/base

;; incr-parse/core/session.rkt
;;
;; Three layered types, each answering one question:
;;
;;   grammar   - HOW to parse a document: a lexer, a starting production,
;;               and whatever dynamic-extent setup that production needs
;;               (Pratt tables, etc). Stateless, freely shared.
;;   document  - ONE piece of text's current lex state, its own private
;;               memoization cache, the grammar it was opened with, and
;;               its own current parsed tree. Never shared across
;;               documents - two documents never see each other's cache
;;               entries, even if opened with the same grammar.
;;   session   - MANY installed grammars and MANY open documents, keyed by
;;               caller-chosen names. The thing a caller actually creates
;;               and holds onto. See ../main.rkt for the public entry
;;               points built on top of this file - this module is meant
;;               to be usable directly by advanced callers, but main.rkt
;;               is the intended front door.
;;
;; None of this is locked for literal multi-threaded access - every mutable
;; table here (a document's cache, a session's grammar/document tables) is a
;; plain mutable hash, exactly like green-cache and current-ast-cache
;; elsewhere in this library. "Many documents, incrementally edited over
;; time" is supported; concurrent mutation of the SAME document or session
;; from two OS threads at once is not.

(require (prefix-in lex: incr-lex)
         rope
         "green.rkt"
         "memo.rkt"
         "red.rkt"
         "token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Grammar - how to parse a document
;;; --------------------------------------------------------------------------

;; lexer      : handed straight to incr-lex's make-session.
;; apply-edit : handed straight to incr-lex's session-edit.
;; start      : Parser - (token-stream? -> (values green-tree? token-stream?)),
;;              this grammar's starting production. See core/combinators.rkt
;;              and core/pratt.rkt for the shape every Parser value shares.
;; setup      : Parser -> Parser - wraps `start` so whatever dynamic-extent
;;              parameterization the grammar's parser needs is installed
;;              automatically on every parse: Pratt's nud/led/bp tables and
;;              expr-rule-id for a grammar built on core/pratt.rkt, or left
;;              at the identity default for a grammar that needs none.
;; ropeable   : passed to incr-lex's make-session as its source-text
;;              adapter. Defaults to string-rope-ropeable, since every
;;              example grammar in this library parses from plain Racket
;;              strings; override it if a grammar reads from something else.
(struct grammar (lexer apply-edit start setup ropeable)
  #:transparent
  #:constructor-name make-grammar*)

(define (make-grammar #:lexer lexer
                       #:apply-edit apply-edit
                       #:start start
                       #:setup    [setup (λ (p) p)]
                       #:ropeable [ropeable string-rope-ropeable])
  (make-grammar* lexer apply-edit start setup ropeable))

;;; --------------------------------------------------------------------------
;;; Document - one piece of text's parse state
;;; --------------------------------------------------------------------------

;; tree : (or/c green-tree? #f) - #f until the first document-parse!;
;;   reset to #f by document-edit!, since the tree from before an edit no
;;   longer reflects the document's current text.
(struct document (lex-session cache grammar tree) #:transparent)

(define (make-document g raw-chunk)
  (document (lex:make-session (grammar-lexer g) (grammar-apply-edit g)
                              (grammar-ropeable g) raw-chunk)
            (make-parse-cache)
            g
            #f))

(define (document-tokens doc)
  (lex:session->tokens-list (document-lex-session doc)))

;; Runs this document's own grammar's `start` (through its `setup` wrapper)
;; against the document's current tokens, with the document's own cache
;; installed, so memoize/memo-ref! calls reuse entries from prior parses of
;; THIS document and write new ones back into it. Returns a NEW document
;; with `tree` filled in. Mutates the document's cache tables in place as a
;; side effect (that's what makes reuse across calls possible at all), hence
;; the `!`, even though the document value itself is threaded functionally.
(define (document-parse! doc)
  (parse-cache-begin-pass! (document-cache doc))
  (define g (document-grammar doc))
  (define run ((grammar-setup g) (grammar-start g)))
  (parameterize ([current-parse-cache (document-cache doc)]
                 [current-parse-offset (box 0)])
    (define-values (tree rest) (run (tokens->stream (document-tokens doc))))
    (struct-copy document doc [tree tree])))

;; Applies a text edit via incr-lex's own session-edit and returns a NEW
;; document value. Invalidates every stale cache entry in place BEFORE
;; swapping in the new lex-session. The cache object itself carries forward
;; unchanged (same instance), so surviving entries stay reusable on the next
;; document-parse!. tree resets to #f - stale until then.
(define (document-edit! doc start old-len new-chunk)
  (parse-cache-invalidate! (document-cache doc) start (+ start old-len))
  (struct-copy document doc
               [lex-session (lex:session-edit (document-lex-session doc)
                                              start old-len new-chunk)]
               [tree #f]))

;; Explicit, deterministic disposal for a caller managing many open
;; documents. Drops this document's cache entries immediately rather than
;; waiting on GC.
(define (document-unload! doc)
  (hash-clear! (parse-cache-table (document-cache doc)))
  (hash-clear! (parse-cache-spans (document-cache doc)))
  (hash-clear! (parse-cache-pass-seen (document-cache doc)))
  (void))

;; document-red-root : document? -> red-node?
;; Errors if the document has never been parsed - there's no tree yet to
;; root a Red view on.
(define (document-red-root doc)
  (define tree (document-tree doc))
  (unless tree
    (error 'document-red-root
           "document has no tree yet - call document-parse! first"))
  (red-root tree))

;; document-find-at : document? exact-nonnegative-integer? -> red-node?
(define (document-find-at doc target)
  (red-find-at (document-red-root doc) target))

;; document-diagnostics : document? -> (listof diagnostic?)
;; Every lexical + syntactic diagnostic anywhere in the document's current
;; tree, absolute-offset, document order.
(define (document-diagnostics doc)
  (red-tree-diagnostics (document-red-root doc)))

;;; --------------------------------------------------------------------------
;;; Session - many installed grammars, many open documents
;;; --------------------------------------------------------------------------
;;
;; A session is an explicit, first-class value a caller creates and holds
;; onto - not a dynamically-scoped default. Two independent sessions never
;; share a grammar or document table, so a caller juggling more than one
;; workspace at once never needs a parameterize block to keep them apart.

(struct session (grammars documents) #:transparent)

(define (make-session) (session (make-hash) (make-hash)))

;; session-install-grammar! : session? any/c grammar? -> void?
;; Errors if name is already installed - installing over it silently would
;; leave any document already open under the old grammar pointing at a
;; grammar value nothing else references anymore.
(define (session-install-grammar! sess name g)
  (when (hash-has-key? (session-grammars sess) name)
    (error 'session-install-grammar! "grammar already installed: ~e" name))
  (hash-set! (session-grammars sess) name g))

(define (session-grammar sess name)
  (hash-ref (session-grammars sess) name
            (λ () (error 'session-grammar "no such grammar installed: ~e" name))))

(define (session-grammar-names sess) (hash-keys (session-grammars sess)))

;; session-open! : session? any/c any/c string? -> document?
;; Opens a new document under the named grammar, parses it once, installs
;; it in the session under key, and returns it. Errors if key is already
;; open - see workspace-open!'s historical note: silently clobbering an
;; open document would leak its cache rather than disposing of it via
;; document-unload!.
(define (session-open! sess grammar-name key raw-chunk)
  (when (hash-has-key? (session-documents sess) key)
    (error 'session-open! "document already open: ~e" key))
  (define g (session-grammar sess grammar-name))
  (define doc (document-parse! (make-document g raw-chunk)))
  (hash-set! (session-documents sess) key doc)
  doc)

(define (session-has-document? sess key) (hash-has-key? (session-documents sess) key))

;; session-document : session? any/c -> (or/c document? #f)
(define (session-document sess key) (hash-ref (session-documents sess) key #f))

(define (session-document-keys sess) (hash-keys (session-documents sess)))

;; session-edit! : session? any/c exact-nonnegative-integer? exact-nonnegative-integer? string?
;;                 -> document?
;; The common case: apply an edit AND reparse in one call, install the
;; result back into the session, and return it. Errors if key isn't open.
;; A caller that wants to batch several edits before paying for a reparse
;; can instead call document-edit!/document-parse! directly and install the
;; result via session-update! below.
(define (session-edit! sess key start old-len new-chunk)
  (session-update! sess key
                   (λ (doc) (document-parse! (document-edit! doc start old-len new-chunk)))))

;; session-update! : session? any/c (document? -> document?) -> document?
;; The one place a document's table entry actually changes, for callers
;; doing anything session-edit! doesn't cover directly (batched edits,
;; re-running a parse without an edit, etc). Errors if key isn't open.
(define (session-update! sess key f)
  (define doc (session-document sess key))
  (unless doc (error 'session-update! "document not open: ~e" key))
  (define doc* (f doc))
  (hash-set! (session-documents sess) key doc*)
  doc*)

;; session-close! : session? any/c -> void?
;; A no-op, not an error, on a key that isn't open - "make sure this
;; document is closed" is the usual caller intent.
(define (session-close! sess key)
  (define doc (session-document sess key))
  (when doc
    (document-unload! doc)
    (hash-remove! (session-documents sess) key))
  (void))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require (except-in rackunit fail)
           racket/set
           (prefix-in : incr-lex)
           "combinators.rkt"
           "printer.rkt")

  ;; Minimal RD-only fixture grammar: one token kind, no Pratt tables, so
  ;; #:setup is left at its identity default - just enough to exercise
  ;; document and session mechanics without pulling in a full example
  ;; grammar from ../examples.
  (:define-tokens words-tokens
    [WS   := (+ :ws)]
    [Word := (+ :alpha)])

  (:define-lexer words
    #:tokens    words-tokens
    #:token-set [Word]
    #:leading   [WS]
    #:trailing  [WS]
    #:newline   [])

  ;; Each word is its own memoized rule - this is what makes
  ;; document-edit!'s eq?-across-an-edit tests below actually mean
  ;; something. A bare (rep ... consume-as ...) with no memoize anywhere
  ;; never populates the cache at all, so every reparse would trivially
  ;; produce fresh, non-eq? tokens regardless of whether span-based
  ;; invalidation was working correctly or not.
  (define parse-word (memoize 'word (λ (t) (consume-as 'word t))))

  (define (parse-words toks)
    ((rep 'words parse-word (λ (k) (eq? k 'incr-lex:eof)))
     toks))

  (define words-grammar
    (make-grammar #:lexer words-lex #:apply-edit words-apply-edit #:start parse-words))

  ;; --- grammar --------------------------------------------------------

  (test-case "grammar: keyword constructor fills in identity setup and string-rope-ropeable by default"
    (check-eq? (grammar-lexer words-grammar) words-lex)
    (check-eq? (grammar-start words-grammar) parse-words)
    (check-eq? (grammar-ropeable words-grammar) string-rope-ropeable)
    (check-equal? ((grammar-setup words-grammar) 'anything) 'anything))

  ;; --- document ---------------------------------------------------------

  (test-case "document-parse!: parses and round-trips through the printer"
    (define doc (document-parse! (make-document words-grammar "foo bar")))
    (check-equal? (green->source (document-tree doc)) "foo bar"))

  (test-case "document-edit!: resets tree to #f until reparsed"
    (define doc1 (document-parse! (make-document words-grammar "foo bar")))
    (define doc2 (document-edit! doc1 0 3 "quux"))
    (check-false (document-tree doc2))
    (define doc3 (document-parse! doc2))
    (check-equal? (green->source (document-tree doc3)) "quux bar"))

  (test-case "document-edit!: an untouched word survives an edit, eq?"
    (define doc1 (document-parse! (make-document words-grammar "foo bar baz")))
    (define (find-baz t)
      (cond [(and (green-token? t) (eq? (lex:token-kind (green-token-token t)) 'Word)
                  (equal? (rope->string (lex:token-payload (green-token-token t))) "baz"))
             t]
            [(green-branch? t) (ormap find-baz (green-branch-children t))]
            [else #f]))
    (define baz1 (find-baz (document-tree doc1)))
    (define doc3 (document-parse! (document-edit! doc1 0 3 "quux")))
    (define baz3 (find-baz (document-tree doc3)))
    (check-eq? baz1 baz3))

  (test-case "document-red-root: errors before the first parse, works after"
    (define doc0 (make-document words-grammar "foo bar"))
    (check-exn exn:fail? (λ () (document-red-root doc0)))
    (define doc1 (document-parse! doc0))
    (check-equal? (red-node-width (document-red-root doc1)) 7))

  (test-case "document-unload!: clears this document's cache without touching the document value"
    (define doc (document-parse! (make-document words-grammar "foo bar")))
    (document-unload! doc)
    (check-equal? (hash-count (parse-cache-table (document-cache doc))) 0))

  ;; --- session ------------------------------------------------------------

  (test-case "session-install-grammar!/session-grammar round-trip; double-install errors"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (check-eq? (session-grammar sess 'words) words-grammar)
    (check-exn exn:fail? (λ () (session-install-grammar! sess 'words words-grammar))))

  (test-case "session-open!/document/close! round-trip"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (check-false (session-document sess "doc-1"))
    (define doc (session-open! sess 'words "doc-1" "foo bar"))
    (check-eq? (session-document sess "doc-1") doc)
    (check-true (session-has-document? sess "doc-1"))
    (check-equal? (green->source (document-tree doc)) "foo bar")
    (session-close! sess "doc-1")
    (check-false (session-document sess "doc-1"))
    (check-false (session-has-document? sess "doc-1")))

  (test-case "session-open!: opening an already-open key errors"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (session-open! sess 'words "doc-1" "foo")
    (check-exn exn:fail? (λ () (session-open! sess 'words "doc-1" "bar"))))

  (test-case "session-close!: closing a key that was never open is a no-op"
    (define sess (make-session))
    (session-close! sess "never-opened"))

  (test-case "session-edit!: edits and reparses in one call"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (session-open! sess 'words "doc-1" "foo bar")
    (define doc (session-edit! sess "doc-1" 0 3 "quux"))
    (check-equal? (green->source (document-tree doc)) "quux bar")
    (check-eq? (session-document sess "doc-1") doc))

  (test-case "session-edit!: erroring on a key that isn't open"
    (define sess (make-session))
    (check-exn exn:fail? (λ () (session-edit! sess "doc-1" 0 0 "x"))))

  (test-case "session-document-keys/session-grammar-names reflect what's installed/open"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (session-open! sess 'words "a" "foo")
    (session-open! sess 'words "b" "bar")
    (check-equal? (list->set (session-document-keys sess)) (list->set '("a" "b")))
    (check-equal? (list->set (session-grammar-names sess)) (set 'words)))

  (test-case "two documents opened under the same grammar never share a cache"
    (define sess (make-session))
    (session-install-grammar! sess 'words words-grammar)
    (define d1 (session-open! sess 'words "a" "foo"))
    (define d2 (session-open! sess 'words "b" "bar"))
    (check-false (eq? (document-cache d1) (document-cache d2)))))
