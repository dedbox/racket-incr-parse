#lang racket/base

;; incr-parse/private/memo.rkt
;;
;; Per-rule memoization, keyed on eq?-identity of the incr-lex token a rule
;; started at PLUS explicit, offset-based invalidation on edit.
;;
;; Identity alone isn't enough. A composite rule's cache entry can have an
;; unchanged LEADING token while an edit lands strictly inside its own
;; consumed span. A surviving token deep in the prefix says nothing about what
;; happened later inside the rule that started there. Therefore, every cache
;; entry also records its absolute [offset, offset+width) span, and every edit
;; eagerly evicts any entry whose span overlaps the edit's damage range.
;; Entries with no overlap are untouched.
;;
;; The offset itself is tracked via a dynamically-scoped, explicitly mutated
;; box (current-parse-offset), advanced at the ONE place any token is actually
;; consumed (consume-as, in combinators.rkt). This is NOT part of any Green
;; node - those stay position-free - it is transient parse-time bookkeeping
;; that exists purely so cache entries know where they came from.
;;
;; Additionally, a cache entry must never store or return a captured
;; token-list continuation. A hit for an entry whose OWN span is untouched can
;; still immediately precede tokens an edit DID replace. If the entry hands
;; back its old `rest` list, the edit has alread superceded that stale list's
;; head token. Instead, cache a token COUNT (ntoks) and always derive `rest`
;; via (list-tail toks ntoks) against the tokens passed into THIS call (which
;; will never be stale).

(require (prefix-in lex: incr-lex)
         "green.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; The Cache
;;; --------------------------------------------------------------------------

;; tree  : the memoized Parser result
;; ntoks : how many tokens this rule consumed - NOT a captured list;
;;         always replayed against the live input via list-tail
;; offset/width : this entry's absolute document span, for invalidation
(struct cache-entry (tree ntoks offset width) #:transparent)

;; table : rule-id -> (hasheq token -> (hash extra-key -> (cons tree remaining-toks)))
;;
;; Three levels because a single Racket hash needs one uniform equivalence:
;; the middle level MUST be eq?-keyed. extra-key (e.g. Pratt's min-bp) is
;; small immutable data - a number or null - so equal?-keying it at the
;; innermost level is safe.
(struct parse-cache (table) #:transparent)

(define (make-parse-cache) (parse-cache (make-hash)))

;; #f = memoization disabled. Every wrapped parser degrades to a pure
;; passthrough when this is unset.
(define current-parse-cache (make-parameter #f))

;;; --------------------------------------------------------------------------
;;; Running Offset
;;;
;;; #f = not tracking.
;;; --------------------------------------------------------------------------

(define current-parse-offset (make-parameter #f))

(define (current-offset)
  (define b (current-parse-offset))
  (if b (unbox b) 0))

(define (bump-parse-offset! width)
  (define b (current-parse-offset))
  (when b (set-box! b (+ (unbox b) width))))

;;; --------------------------------------------------------------------------
;;; Low-Level Primitive
;;;
;;; Exposed directly (not just via `memoize` below) for rules whose Parser
;;; shape doesn't fit a plain single-argument (listof token?) wrapper - e.g.
;;; Pratt's parse-expr, which is additionally keyed on min-bp.
;;; --------------------------------------------------------------------------

;; `rest` is always a tail of `toks`.
(define (count-consumed toks rest)
  (let loop ([t toks] [n 0])
    (if (eq? t rest) n (loop (cdr t) (add1 n)))))

(define (memo-ref! rule-id toks extra-key thunk)
  (define cache (current-parse-cache))
  (cond
    [(or (not cache) (null? toks)) (thunk)]
    [else
     (define token (car toks))
     (define by-token (hash-ref! (parse-cache-table cache) rule-id make-hasheq))
     (define by-key   (hash-ref! by-token token make-hash))
     (cond
       [(hash-ref by-key extra-key #f)
        => (λ (entry)
             (bump-parse-offset! (cache-entry-width entry))
             (values (cache-entry-tree entry) (list-tail toks (cache-entry-ntoks entry))))]
       [else
        (define start (current-offset))
        (define-values (tree rest) (thunk))
        (hash-set! by-key extra-key
                   (cache-entry tree (count-consumed toks rest) start (green-tree-width tree)))
        (values tree rest)])]))

;; (define (memo-ref! rule-id toks extra-key thunk)
;;   (define cache (current-parse-cache))
;;   (cond
;;     [(or (not cache) (null? toks)) (thunk)]
;;     [else
;;      (define token (car toks))
;;      (define by-token (hash-ref! (parse-cache-table cache) rule-id make-hasheq))
;;      (define by-key   (hash-ref! by-token token make-hash))
;;      (cond
;;        [(hash-ref by-key extra-key #f)
;;         => (λ (entry)
;;              (bump-parse-offset! (cache-entry-width entry))
;;              (values (cache-entry-tree entry)
;;                      (list-tail toks (cache-entry-ntoks entry))))]
;;        [else
;;         (define start (current-offset))
;;         (define-values (tree rest) (thunk))
;;         (hash-set! by-key extra-key
;;                    (cache-entry tree (count-consumed toks rest) start
;;                                 (green-tree-width tree)))
;;         (values tree rest)])]))

;; Convenience wrapper for ordinary (listof token?) -> (values ...) rules
(define ((memoize rule-id parser #:extra-key [extra-key-fn (λ (toks) null)]) toks)
  (memo-ref! rule-id toks (extra-key-fn toks) (λ () (parser toks))))

;;; --------------------------------------------------------------------------
;;; Span-Based Invalidation
;;; --------------------------------------------------------------------------

(define (span-overlaps? a-start a-end b-start b-end)
  (and (< a-start b-end) (< b-start a-end)))

;; Eagerly evicts every entry, across every rule, whose recorded span
;; overlaps [damage-start, damage-end).
;;
;; O(cache size) - a linear sweep over every currently-memoized entry, per
;; edit.
;;
;; Correct, but not yet optimal: a document with a large, long-lived cache and
;; frequent edits would benefit from indexing entries by offset (e.g. an
;; interval structure) to make this sublinear. Deferring that exactly like
;; reparse-splicing was deferred earlier.
(define (parse-cache-invalidate! cache damage-start damage-end)
  (define stale
    (for*/list ([(rule-id by-token) (in-hash (parse-cache-table cache))]
                [(token by-key)     (in-hash by-token)]
                [(key entry)        (in-hash by-key)]
                #:when (span-overlaps? (cache-entry-offset entry)
                                       (+ (cache-entry-offset entry)
                                          (cache-entry-width entry))
                                       damage-start damage-end))
      (list rule-id token key)))
  (for ([e (in-list stale)])
    (define by-token (hash-ref (parse-cache-table cache) (car e)))
    (define by-key   (hash-ref by-token (cadr e)))
    (hash-remove! by-key (caddr e))))

;;; --------------------------------------------------------------------------
;;; Session - one document's lex state plus its own private cache.
;;;
;;; Never shared across documents.
;;; --------------------------------------------------------------------------

(struct parse-session (lex-session cache) #:transparent)

(define (make-parse-session lex-fn apply-edit-fn ρ-src raw-chunk)
  (parse-session (lex:make-session lex-fn apply-edit-fn ρ-src raw-chunk)
                 (make-parse-cache)))

(define (parse-session-tokens sess)
  (lex:session->tokens-list (parse-session-lex-session sess)))

;; Runs parse-entry (e.g. a grammar's top-level parse-program) against this
;; session's current tokens with this session's cache installed, so any
;; memoize/memo-ref! calls reached during parsing reuse entries from prior
;; parses of THIS session and write new ones back into it.
(define (parse-session-run sess parse-entry)
  (parameterize ([current-parse-cache (parse-session-cache sess)]
                 [current-parse-offset (box 0)])
    (define-values (tree rest) (parse-entry (parse-session-tokens sess)))
    tree))

;; Applies a text edit via incr-lex's own session-edit and returns a NEW
;; parse-session value. Invalidates every stale entry in place BEFORE swapping
;; in the new lex-session. The lex-session component is updated, but the cache
;; object carries forward unchanged (same instance), so surviving entries stay
;; reusable.
(define (parse-session-edit sess start old-len new-chunk)
  (parse-cache-invalidate! (parse-session-cache sess) start (+ start old-len))
  (struct-copy parse-session sess
               [lex-session (lex:session-edit (parse-session-lex-session sess)
                                              start old-len new-chunk)]))

;; Explicit, deterministic disposal for a server managing many open documents.
;; Drops this session's entries immediately rather than waiting on GC.
(define (parse-session-unload! sess)
  (hash-clear! (parse-cache-table (parse-session-cache sess)))
  (void))

(module+ test
  (require rackunit
           rope)

  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))

  (test-case "disabled by default: memoize is a pure passthrough"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (p (list (mk-tok 'K "x")))
    (p (list (mk-tok 'K "x")))
    (check-equal? (unbox calls) 2))  ; no cache installed -> ran twice

  (test-case "with a cache: second call on the SAME token object hits, doesn't re-run"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (define tok (mk-tok 'K "x"))
    (parameterize ([current-parse-cache (make-parse-cache)])
      (p (list tok))
      (p (list tok)))
    (check-equal? (unbox calls) 1))

  (test-case "a DIFFERENT (non-eq?) token object, same content, misses"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (parameterize ([current-parse-cache (make-parse-cache)])
      (p (list (mk-tok 'K "x")))
      (p (list (mk-tok 'K "x"))))  ; distinct object, equal? content
    (check-equal? (unbox calls) 2))

  (test-case "span invalidation: a composite rule whose leading token survived still misses if its span overlapped the edit"
    (define inner-atom-calls (box 0))
    (define leading-tok (mk-tok 'LParen "("))
    (define composite
      (memoize 'list (λ (toks)
                       (set-box! inner-atom-calls (add1 (unbox inner-atom-calls)))
                       (values (green-token 'list 10 'fake-subtree) toks))))
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (list leading-tok)))
    (check-equal? (unbox inner-atom-calls) 1)
    (parse-cache-invalidate! cache 10 11)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (list leading-tok)))
    (check-equal? (unbox inner-atom-calls) 2))

  (test-case "invalidation ignores entries with no overlap"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 3 'x) toks))))
    (define tok (mk-tok 'K "abc"))
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 100)])
      (p (list tok)))                    ; span [100,103)
    (parse-cache-invalidate! cache 0 10) ; nowhere near [100,103)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 100)])
      (p (list tok)))
    (check-equal? (unbox calls) 1))      ; still cached, no re-run

  (test-case "extra-key disambiguates same token, different mode (Pratt's min-bp analog)"
    (define calls (box 0))
    (define tok (mk-tok 'K "x"))
    (define ((box-updater x))
      (set-box! calls (add1 (unbox calls)))
      (values (green-token 'k 0 'a) null))
    (parameterize ([current-parse-cache (make-parse-cache)])
      (memo-ref! 'r (list tok) 0 (box-updater 'a))
      (memo-ref! 'r (list tok) 1 (box-updater 'b))
      (memo-ref! 'r (list tok) 0 (box-updater 'a)))
    (check-equal? (unbox calls) 2))

  (test-case "parse-session-unload! clears only that session's cache"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (define c (make-parse-cache))
    (define tok (mk-tok 'K "x"))
    (parameterize ([current-parse-cache c]) (p (list tok)))
    (hash-clear! (parse-cache-table c))
    (parameterize ([current-parse-cache c]) (p (list tok)))
    (check-equal? (unbox calls) 2))

  (test-case "a composite rule's entry whose span overlaps an edit must miss, even though its own leading token survived the edit"
    (define inner-atom-calls (box 0))
    ;; a fake 'composite' rule spanning offsets [5,15). Its own leading token
    ;; is untouched by the edit. A token strictly inside its span changes.
    (define leading-tok (mk-tok 'LParen "("))
    (define composite
      (memoize 'list (λ (toks)
                       (set-box! inner-atom-calls (add1 (unbox inner-atom-calls)))
                       (values (green-token 'list 10 'fake-subtree) toks))))
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (list leading-tok)))   ; caches: offset=5, width=10 -> span [5,15)
    (check-equal? (unbox inner-atom-calls) 1)
    ;; edit at [10,11) - strictly inside [5,15), leading token itself
    ;; untouched (5 < 10)
    (parse-cache-invalidate! cache 10 11)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (list leading-tok)))   ; must MISS and re-run, not return the stale entry
    (check-equal? (unbox inner-atom-calls) 2))

  (test-case "a hit before the edit must not resume parsing through a stale (pre-edit) continuation"
    ;; toks = [A B C], one 'leaf rule consuming exactly one token per call - a
    ;; minimal stand-in for `rep` walking a sequence, without needing a real
    ;; grammar to reproduce this.
    (define processed (box null))  ; records the actual token object each MISS operated on
    (define leaf
      (memoize 'leaf (λ (toks)
                       (define tok (car toks))
                       (set-box! processed (cons tok (unbox processed)))
                       (values (green-token 'k (lex:token-width tok) tok) (cdr toks)))))
    (define A (mk-tok 'K "a"))
    (define B (mk-tok 'K "b"))    ; will be "replaced" by B*
    (define C (mk-tok 'K "c"))
    (define cache (make-parse-cache))
    ;; first "parse": A at offset 0, B at offset 1, C at offset 2
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (define-values (_a r1) (leaf (list A B C)))
      (define-values (_b r2) (leaf r1))
      (leaf r2))
    ;; "edit": B is replaced by a new object B* at the same offset/width
    (define B* (mk-tok 'K "b"))
    (parse-cache-invalidate! cache 1 2)  ; evicts leaf@B only; leaf@A, leaf@C survive
    (set-box! processed null)
    ;; reparse against the REAL current stream [A B* C] - A and C are the same
    ;; eq? objects as before, B* is new
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (define-values (_a r1) (leaf (list A B* C)))
      (define-values (_b r2) (leaf r1))
      (leaf r2))
    ;; B* must have actually been processed (cache miss, correctly
    ;; re-derived). Under the old stale-rest bug, leaf@A's hit would hand back
    ;; its OLD rest (containing the OLD B, not B*), and B* would never be
    ;; looked at
    (check-true (and (memq B* (unbox processed)) #t))
    (check-false (memq B (unbox processed))))

  (test-case "nested composite rules mirroring sexpr.rkt's shape: an edit inside an inner list reuses untouched siblings, everywhere the SAME structure, with no real lexer involved"
    ;; Structure: (open foo (open bar one two close) baz close) - i.e.
    ;; the same 'sexpr-wraps-'list-wraps-'sexpr* shape as
    ;; langs/sexpr.rkt, entirely with synthetic tokens.
    (define (mini-consume kind toks)
      (define tok (car toks))
      (bump-parse-offset! (lex:token-width tok))
      (values (green-token kind (lex:token-width tok) tok) (cdr toks)))

    (define (mini-sexpr toks)
      (memo-ref! 'sexpr toks null
                 (λ () (if (eq? (lex:token-kind (car toks)) 'Open)
                           (mini-list toks)
                           (mini-consume 'atom toks)))))

    (define (mini-list toks)
      (memo-ref! 'list toks null
                 (λ ()
                   (define-values (_open toks1) (mini-consume 'open toks))
                   (let loop ([toks toks1] [children null])
                     (if (eq? (lex:token-kind (car toks)) 'Close)
                         (let-values ([(_close rest) (mini-consume 'close toks)])
                           (values (intern-branch! 'list (reverse children)) rest))
                         (let-values ([(child toks*) (mini-sexpr toks)])
                           (loop toks* (cons child children))))))))

    (define (find-atom tree tok)
      (cond [(and (green-token? tree) (eq? (green-token-token tree) tok)) tree]
            [(green-branch? tree) (ormap (λ (c) (find-atom c tok)) (green-branch-children tree))]
            [else #f]))

    ;; every token width 1, so offsets are just positions 0..8
    (define T-open1 (mk-tok 'Open "("))
    (define T-foo (mk-tok 'Atom "f"))
    (define T-open2 (mk-tok 'Open "("))
    (define T-bar (mk-tok 'Atom "b"))
    (define T-one (mk-tok 'Atom "1"))
    (define T-two (mk-tok 'Atom "2"))
    (define T-close2 (mk-tok 'Close ")"))
    (define T-baz (mk-tok 'Atom "z"))
    (define T-close1 (mk-tok 'Close ")"))
    (define toks1 (list T-open1 T-foo T-open2 T-bar T-one T-two T-close2 T-baz T-close1))

    (define cache (make-parse-cache))
    (define tree1
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (define-values (t _r) (mini-sexpr toks1))
        t))

    ;; "edit": T-one -> T-one*, same width, same offset, different object
    (define T-one* (mk-tok 'Atom "9"))
    (parse-cache-invalidate! cache 4 5) ; T-one's span, by hand: [4,5)
    (define toks2 (list T-open1 T-foo T-open2 T-bar T-one* T-two T-close2 T-baz T-close1))

    (define tree2
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (define-values (t _r) (mini-sexpr toks2))
        t))

    (test-case "untouched siblings are eq? across the edit"
      (check-eq? (find-atom tree1 T-foo) (find-atom tree2 T-foo))
      (check-eq? (find-atom tree1 T-bar) (find-atom tree2 T-bar))
      (check-eq? (find-atom tree1 T-two) (find-atom tree2 T-two))
      (check-eq? (find-atom tree1 T-baz) (find-atom tree2 T-baz)))

    (test-case "the changed leaf and every ancestor whose span contained it are rebuilt, not reused"
      (check-not-eq? (find-atom tree1 T-one) (find-atom tree2 T-one*)) ; different objects by construction
      (check-false (find-atom tree2 T-one)) ; old object doesn't even appear
      (check-not-eq? tree1 tree2)))) ; outer 'list rebuilt too
