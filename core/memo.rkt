#lang racket/base

;; incr-parse/core/memo.rkt
;;
;; Per-rule memoization, keyed on eq?-identity of the incr-lex token a rule
;; started at plus a rule-specific extra key, PLUS explicit, offset-based
;; invalidation on edit, PLUS a same-pass collision guard.
;;
;; First: a composite rule's cache entry can have an unchanged leading token
;; for an edit strictly inside its consumed span. A surviving token deep in
;; the prefix says nothing about what happened later inside the rule that
;; started there. Therefore, every cache entry also records its absolute
;; [offset, offset+width) span, and every edit eagerly evicts any entry whose
;; span overlaps the edit's damage range. Entries with no overlap are
;; unaffected.
;;
;; Second, and the reason a cache entry is not keyed on its own offset:
;; incr-lex content-interns tokens process-wide, so two unrelated occurrences
;; of identical text with identical trivia become the same token object. An
;; edit anywhere in the document shifts the absolute offset of everything
;; after it, even unrelated content. Since reusing old cached data at new
;; offsets is what the cache is for, keying on absolute offsets breaks it.
;; Because edits that change the length of cache entries shift all subsequent
;; tokens, an offset-keyed lookup would never find its own entry again,
;; defeating incremental reuse for anything after the edit point.
;;
;; We do, however, need to be careful in the narrower case where two different
;; positions within the same parse pass share one content-interned token.
;; That's a same-pass collision, not a cross-pass position shift, and the two
;; need opposite treatment. A collision must never return the other position's
;; tree, and a shift must always be allowed to hit.
;;
;; current-pass-seen distinguishes them. It records the offset where each
;; (rule-id, token, extra-key) triple was found during the current pass and
;; resets at the start of every fresh top-level parse via
;; parse-cache-begin-pass!, which must be called at the top of anything that
;; starts a parse pass. document-parse! (core/session.rkt) does this, and
;; anything that
;; bypasses it (by calling memo-ref!/memoize directly against a shared cache
;; across what should be two separate passes) also needs to call it
;; explicitly, or a later pass will see the earlier pass's stale offsets and
;; wrongly treat ordinary cross-edit reuse as a collision. A repeat lookup of
;; the same triple within one pass, at a different offset, can only mean a
;; same-pass collision, and forces a fresh, uncached computation instead of
;; trusting whatever is in the table. A lookup in a new pass starts this
;; tracking over, so tokens preserved across a splice at shifted absolute
;; positions are never penalized.
;;
;; current-pass-seen is indexed with the same three-level, eq?-on-token shape
;; as `table`. Originally, it was a flat equal?-hashed key, but since a token
;; is a #:transparent wrapper around a rope payload, a profile of 200
;; sequential edits against a 500K-char document showed the flat version's
;; equal? comparisons alone accounted for 47% of the total time spent in
;; memo-ref!, hit or miss.
;;
;; The offset itself is tracked in a dynamically-scoped, explicitly mutated
;; box (current-parse-offset), which is advanced at the one place tokens are
;; consumed - consume-as, in combinators.rkt. This is not part of any Green
;; node, which stay position-free. It is transient parse-time bookkeeping that
;; exists purely so cache entries know where they came from.
;;
;; A cache entry never stores or returns a captured token-stream continuation.
;; A hit for an entry whose span is not directly affected can still
;; immediately precede tokens an edit replaced. If the entry were to return
;; its old `rest` stream, the edit would have already superseded whatever
;; comes after it. Instead, a hit caches a token count (ntoks) and always
;; derives `rest` via (stream-advance toks ntoks) against the stream passed
;; into the current call, which will never be stale. Since toks is a token
;; stream, stream-advance is an O(1) index update.

(require (prefix-in lex: incr-lex)
         racket/list
         rope
         "green.rkt"
         "token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; The Cache
;;; --------------------------------------------------------------------------

;; tree  : the memoized Parser result
;; ntoks : how many tokens this rule consumed - NOT a captured stream;
;;         always replayed against the live input via stream-advance
;; offset/width : this entry's absolute document span, for invalidation
(struct cache-entry (tree ntoks offset width) #:transparent)

;; table     : rule-id -> (hasheq token -> (hash extra-key -> cache-entry))
;; spans     : bucket-index -> (listof entry-ref) - see "Span-Based
;;             Invalidation" below for details.
;; pass-seen : rule-id -> (hasheq token -> (hash extra-key -> offset)) -
;;             the offset each (rule-id, token, extra-key) triple was first
;;             looked up at during the current pass only. See memo-ref!'s
;;             comment and this file's header comment for what this guards
;;             against, why it must be reset per-pass, and why it needs the
;;             exact same three-level, eq?-on-token shape as `table`.
;;
;; table and pass-seen both have three levels because each Racket hash needs
;; one uniform equivalence. The middle level must be eq?-keyed. token is a
;; #:transparent struct wrapping a rope payload, and equal? on one is not
;; O(1). extra-key (e.g. Pratt's min-bp) must be small immutable data, e.g.,
;; Pratt's min-bp, to ensure equal?-keying it at the innermost level is safe.
(struct parse-cache (table spans pass-seen) #:transparent)

(define (make-parse-cache) (parse-cache (make-hash) (make-hash) (make-hash)))

(define (parse-cache-begin-pass! cache)
  (hash-clear! (parse-cache-pass-seen cache)))

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
;;; shape doesn't fit a plain single-argument token-stream? wrapper - e.g.
;;; Pratt's parse-expr, which is additionally keyed on min-bp.
;;; --------------------------------------------------------------------------

(define (memo-ref! rule-id toks extra-key thunk)
  (define cache (current-parse-cache))
  (cond
    [(or (not cache) (zero? (vector-length (token-stream-vec toks)))) (thunk)]
    [else
     (define token (stream-peek toks))
     (define start (current-offset))
     (define by-token-seen (hash-ref! (parse-cache-pass-seen cache) rule-id make-hasheq))
     (define by-key-seen   (hash-ref! by-token-seen token make-hash))
     (define prior-start (hash-ref by-key-seen extra-key #f))
     (cond
       [(and prior-start (not (= prior-start start)))
        ;; This is the same (rule-id, token, extra-key) triple, already looked
        ;; up earlier in this pass, at a different offset, which only happens
        ;; on a content-interning collision. Compute it fresh, without
        ;; touching the table. The table entry belongs to whichever position
        ;; got here first, and overwriting it would just move the problem onto
        ;; that position's next lookup instead of fixing it.
        (thunk)]
       [else
        (hash-set! by-key-seen extra-key start)
        (define by-token (hash-ref! (parse-cache-table cache) rule-id make-hasheq))
        (define by-key   (hash-ref! by-token token make-hash))
        (cond
          [(hash-ref by-key extra-key #f)
           => (λ (entry)
                (bump-parse-offset! (cache-entry-width entry))
                (values (cache-entry-tree entry)
                        (stream-advance toks (cache-entry-ntoks entry))))]
          [else
           (define-values (tree rest) (thunk))
           (define width (green-tree-width tree))
           (hash-set! by-key extra-key (cache-entry tree (stream-delta toks rest) start width))
           (bucket-index-add! cache (entry-ref rule-id token extra-key start (+ start width)))
           (values tree rest)])])]))

;; Convenience wrapper for ordinary (listof token?) -> (values ...) rules
(define ((memoize rule-id parser #:extra-key [extra-key-fn (λ (toks) null)]) toks)
  (memo-ref! rule-id toks (extra-key-fn toks) (λ () (parser toks))))

;;; --------------------------------------------------------------------------
;;; Span-Based Invalidation
;;; --------------------------------------------------------------------------

;; A bucket/grid index over cache-entry spans, so an edit's eviction sweep
;; only ever looks at entries whose span falls near the damage range, instead
;; of walking the entire cache. This is NOT a general interval tree A real
;; interval tree is still the more complete fix if profiling ever shows this
;; insufficient.

(define (span-overlaps? a-start a-end b-start b-end)
  (and (< a-start b-end) (< b-start a-end)))

;; A bucket should be wide enough that most rule spans live in one or two
;; buckets, and narrow enough that a damage range only ever touches a handful
;; of buckets even in a large document. Tune this once there's a real corpus
;; to benchmark against - see the caveat below.
(define BUCKET-WIDTH 256)

(define (bucket-of offset) (quotient offset BUCKET-WIDTH))

;; The self-contained record stored in a bucket - self-contained so
;; eviction never needs a second lookup into `table` just to find out
;; which OTHER buckets the same entry is registered under.
(struct entry-ref (rule-id token key start end) #:transparent)

;; A zero-width entry needs to go into the bucket containing its own point,
;; not zero buckets.
(define (bucket-range start end)
  (in-range (bucket-of start) (add1 (bucket-of (max start (sub1 end))))))

(define (bucket-index-add! cache er)
  (for ([b (bucket-range (entry-ref-start er) (entry-ref-end er))])
    (hash-update! (parse-cache-spans cache) b (λ (l) (cons er l)) null)))

(define (bucket-index-remove! cache er)
  (for ([b (bucket-range (entry-ref-start er) (entry-ref-end er))])
    (hash-update! (parse-cache-spans cache) b (λ (l) (remove er l eq?)) null)))

;; Evicts every entry, across every rule, whose recorded span overlaps
;; [damage-start, damage-end). Entries with no overlap are untouched.
;;
;; Complexity: O(buckets touched by the damage range + entries registered in
;; them). This is an improvement over a full linear sweep, but it is NOT a
;; worst-case guarantee. A rule spanning most of the document would still
;; register itself across many buckets and show up in most queries. It's good
;; enough for a first pass, but should be revisited with a real interval
;; structure if it ever becomes a bottleneck.
(define (parse-cache-invalidate! cache damage-start damage-end)
  (define candidates
    (remove-duplicates
     (append* (for/list ([b (bucket-range damage-start damage-end)])
                (hash-ref (parse-cache-spans cache) b null)))
     eq?))
  (for ([er (in-list candidates)]
        #:when (span-overlaps? (entry-ref-start er) (entry-ref-end er)
                                damage-start damage-end))
    (define by-token (hash-ref (parse-cache-table cache) (entry-ref-rule-id er) #f))
    (when by-token
      (define by-key (hash-ref by-token (entry-ref-token er) #f))
      (when by-key (hash-remove! by-key (entry-ref-key er))))
    (bucket-index-remove! cache er)))

(module+ test
  (require rackunit)

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
      (p (tokens->stream (list tok)))
      (p (tokens->stream (list tok))))
    (check-equal? (unbox calls) 1))

  (test-case "a DIFFERENT (non-eq?) token object, same content, misses"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (parameterize ([current-parse-cache (make-parse-cache)])
      (p (tokens->stream (list (mk-tok 'K "x"))))
      (p (tokens->stream (list (mk-tok 'K "x")))))  ; distinct object, equal? content
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
      (composite (tokens->stream (list leading-tok))))
    (check-equal? (unbox inner-atom-calls) 1)
    (parse-cache-invalidate! cache 10 11)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (tokens->stream (list leading-tok))))
    (check-equal? (unbox inner-atom-calls) 2))

  (test-case "invalidation ignores entries with no overlap"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 3 'x) toks))))
    (define tok (mk-tok 'K "abc"))
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 100)])
      (p (tokens->stream (list tok))))   ; span [100,103)
    (parse-cache-invalidate! cache 0 10) ; nowhere near [100,103)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 100)])
      (p (tokens->stream (list tok))))
    (check-equal? (unbox calls) 1))      ; still cached, no re-run

  (test-case "extra-key disambiguates same token, different mode (Pratt's min-bp analog)"
    (define calls (box 0))
    (define tok (mk-tok 'K "x"))
    (define ((box-updater x))
      (set-box! calls (add1 (unbox calls)))
      (values (green-token 'k 0 'a) (tokens->stream null)))
    (parameterize ([current-parse-cache (make-parse-cache)])
      (memo-ref! 'r (tokens->stream (list tok)) 0 (box-updater 'a))
      (memo-ref! 'r (tokens->stream (list tok)) 1 (box-updater 'b))
      (memo-ref! 'r (tokens->stream (list tok)) 0 (box-updater 'a)))
    (check-equal? (unbox calls) 2))

  (test-case "clearing a cache's table directly forces every rule to recompute"
    (define calls (box 0))
    (define p (memoize 'r (λ (toks)
                            (set-box! calls (add1 (unbox calls)))
                            (values (green-token 'k 1 'x) toks))))
    (define c (make-parse-cache))
    (define tok (mk-tok 'K "x"))
    (parameterize ([current-parse-cache c]) (p (tokens->stream (list tok))))
    (hash-clear! (parse-cache-table c))
    (parameterize ([current-parse-cache c]) (p (tokens->stream (list tok))))
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
      (composite (tokens->stream (list leading-tok)))) ; caches: offset=5, width=10 -> span [5,15)
    (check-equal? (unbox inner-atom-calls) 1)
    ;; edit at [10,11) - strictly inside [5,15), leading token itself
    ;; untouched (5 < 10)
    (parse-cache-invalidate! cache 10 11)
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 5)])
      (composite (tokens->stream (list leading-tok))))   ; must MISS and re-run, not return the stale entry
    (check-equal? (unbox inner-atom-calls) 2))

  (test-case "a hit before the edit must not resume parsing through a stale (pre-edit) continuation"
    ;; toks = [A B C], one 'leaf rule consuming exactly one token per call - a
    ;; minimal stand-in for `rep` walking a sequence, without needing a real
    ;; grammar to reproduce this.
    (define processed (box null))  ; records the actual token object each MISS operated on
    (define leaf
      (memoize 'leaf (λ (toks)
                       (define tok (stream-peek toks))
                       (set-box! processed (cons tok (unbox processed)))
                       (values (green-token 'k (lex:token-width tok) tok) (stream-rest toks)))))
    (define A (mk-tok 'K "a"))
    (define B (mk-tok 'K "b"))    ; will be "replaced" by B*
    (define C (mk-tok 'K "c"))
    (define cache (make-parse-cache))
    ;; first "parse": A at offset 0, B at offset 1, C at offset 2
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (define-values (_a r1) (leaf (tokens->stream (list A B C))))
      (define-values (_b r2) (leaf r1))
      (leaf r2))
    ;; "edit": B is replaced by a new object B* at the same offset/width
    (define B* (mk-tok 'K "b"))
    (parse-cache-invalidate! cache 1 2)  ; evicts leaf@B only; leaf@A, leaf@C survive
    (set-box! processed null)
    ;; reparse against the REAL current stream [A B* C] - A and C are the same
    ;; eq? objects as before, B* is new
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (define-values (_a r1) (leaf (tokens->stream (list A B* C))))
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
      (define tok (stream-peek toks))
      (bump-parse-offset! (lex:token-width tok))
      (values (green-token kind (lex:token-width tok) tok) (stream-rest toks)))

    (define (mini-sexpr toks)
      (memo-ref! 'sexpr toks null
                 (λ () (if (eq? (lex:token-kind (stream-peek toks)) 'Open)
                           (mini-list toks)
                           (mini-consume 'atom toks)))))

    (define (mini-list toks)
      (memo-ref! 'list toks null
                 (λ ()
                   (define-values (_open toks1) (mini-consume 'open toks))
                   (let loop ([toks toks1] [children null])
                     (if (eq? (lex:token-kind (stream-peek toks)) 'Close)
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
    (define toks1
      (tokens->stream
       (list T-open1 T-foo T-open2 T-bar T-one T-two T-close2 T-baz T-close1)))

    (define cache (make-parse-cache))
    (define tree1
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (define-values (t _r) (mini-sexpr toks1))
        t))

    ;; "edit": T-one -> T-one*, same width, same offset, different object
    (define T-one* (mk-tok 'Atom "9"))
    (parse-cache-invalidate! cache 4 5) ; T-one's span, by hand: [4,5)
    (define toks2
      (tokens->stream
       (list T-open1 T-foo T-open2 T-bar T-one* T-two T-close2 T-baz T-close1)))

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
      (check-not-eq? tree1 tree2))) ; outer 'list rebuilt too

  (test-case "two eq? tokens at DIFFERENT offsets must not alias onto the same cache slot"
    ;; A single token object standing in for two unrelated occurrences of
    ;; identical text plus identical trivia. Without the offset folded into
    ;; the cache key, the second call below would incorrectly hit the first's
    ;; entry and return 'first instead of parsing 'second.
    (define shared-tok (mk-tok 'K "x"))
    (define (run label)
      (memoize 'r (λ (toks) (values (green-token 'k 1 label) toks))))
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      ((run 'first) (tokens->stream (list shared-tok))))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 100)])
      (define-values (tree _rest) ((run 'second) (tokens->stream (list shared-tok))))
      (check-eq? (green-token-token tree) 'second)))

  (test-case "a length-changing edit shifts a later, untouched leaf's absolute offset - it must still be reused (eq?), not just left uninvalidated"
    ;; We implement a custom alternative to consume-as, since memo.rkt cannot
    ;; depend on combinators.rkt because combinators.rkt depends on memo.rkt.
    ;; We must make sure to increment current-parse-offset, just as consume-as
    ;; would. A cache miss in memo-ref! never increments the offset on its
    ;; own. Only a hit increments the offset, because then it skips calling
    ;; this thunk entirely. A miss trusts the thunk, or whatever real
    ;; consuming primitive it wraps, to have already advanced the offset as a
    ;; side effect. A thunk that consumes a token without incrementing breaks
    ;; that assumption silently: the next sibling's cache entry gets the wrong
    ;; start offset, which can make an unrelated edit's invalidation sweep
    ;; spuriously overlap and evict it.
    (define leaf
      (memoize 'leaf (λ (toks)
                       (define tok (stream-peek toks))
                       (bump-parse-offset! (lex:token-width tok))
                       (values (green-token 'k (lex:token-width tok) tok) (stream-rest toks)))))
    (define A (mk-tok 'K "a"))     ; width 1
    (define B (mk-tok 'K "bbb"))   ; width 3, distinct content - never collides with A
    (define cache (make-parse-cache))
    (define tree-b-1
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (define-values (_a r1) (leaf (tokens->stream (list A B))))
        (define-values (tb _r2) (leaf r1))
        tb))
    (define A+ (mk-tok 'K "aaa"))  ; width 3, was 1
    (parse-cache-invalidate! cache 0 1)  ; A's old span only
    (parse-cache-begin-pass! cache)      ; a fresh top-level parse, same as document-parse! does
    (define tree-b-2
      (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
        (define-values (_a r1) (leaf (tokens->stream (list A+ B))))
        (define-values (tb _r2) (leaf r1))
        tb))
    (check-eq? tree-b-1 tree-b-2)))
