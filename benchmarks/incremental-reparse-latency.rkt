#lang racket

;; incr-parse/benchmarks/incremental-reparse-latency.rkt
;;
;; Incremental-reparse latency vs. cold-full-parse baseline, across a
;; document-size sweep and edit position (start / mid / end). Mirrors
;; incr-lex/benchmarks/incremental-edit-latency.rkt's own methodology
;; (median-of-trials, batching for clock resolution, monotonic clock,
;; controlled corpus generation, position-targeted edits) applied one
;; layer up, at the parser rather than the lexer.
;;
;; "Incremental" here times parse-session-edit followed by
;; parse-session-run together, since that combined cost - edit to
;; refreshed tree - is what an editor-facing latency actually is. That
;; necessarily includes incr-lex's own incremental relex cost too, not
;; just this project's own memo/invalidation layer in isolation; this is
;; deliberate; it's the real end-to-end number, not a component
;; microbenchmark. "Full" is a brand new parse-session (fresh lex session,
;; fresh parse cache) built from the already-edited text - the cost of
;; having no incremental machinery at all.
;;
;; The edit itself is deliberately length-changing (replaces one digit
;; with a two-digit number), not a same-width replacement - a same-width
;; edit never shifts anything after it, so it exercises neither the
;; span-invalidation bucket index nor the cross-pass position-shift reuse
;; path a length-changing edit does. See private/memo.rkt's own header
;; comment for why that distinction mattered enough to be worth a
;; dedicated regression test there too.
;;
;; toplevel.rkt is the fixture, per the earlier checkpoint's own call:
;; "the natural medium-complexity, mixed-parser-style fixture" (RD-over-
;; Pratt composition), and it scales cleanly by adding more independent
;; statements, unlike hazelnut.rkt's single-expression grammar.

(require "../langs/toplevel.rkt"
         "../private/memo.rkt"
         racket/format)

(provide run-reparse-latency-sweep)

;;; --------------------------------------------------------------------------
;;; Timing - identical methodology to incr-lex's own benchmark, unexported
;;; there so reimplemented here rather than duplicated across packages via
;;; a shared dependency for ~15 lines of code.
;;; --------------------------------------------------------------------------

(define (median xs)
  (define s (sort xs <))
  (define n (length s))
  (if (odd? n)
      (list-ref s (quotient n 2))
      (/ (+ (list-ref s (sub1 (quotient n 2))) (list-ref s (quotient n 2))) 2)))

(define (batch-ms thunk reps)
  (define t0 (current-inexact-monotonic-milliseconds))
  (for ([_ (in-range reps)]) (thunk))
  (/ (- (current-inexact-monotonic-milliseconds) t0) reps))

;; Fewer reps for bigger documents (full-parse cost is at least Theta(width)),
;; enough reps for small ones to clear the millisecond resolution floor.
(define (reps-for width)
  (max 3 (min 200 (quotient 200000 (max 1 width)))))

(define (median-ms thunk width #:trials [trials 5])
  (define reps (reps-for width))
  (median (for/list ([_ (in-range trials)]) (batch-ms thunk reps))))

;; A deep-enough copy of a parse-cache for repeated, independent timing
;; trials against the SAME warmed-up session. table needs a genuine two-
;; level deep copy - its inner hashes are mutated in place by
;; hash-set!/hash-remove!, so a shallow hash-copy of the outer table would
;; still share those inner hash objects between the original and the
;; "copy", contaminating every trial after the first with whatever the
;; previous trial's edit+reparse already wrote. spans/pass-seen only need
;; a shallow copy - their values are either immutable (numbers) or
;; replaced wholesale rather than mutated in place (bucket lists are
;; extended via cons, never mutated), so sharing those specific value
;; objects between copies is safe.
(define (copy-table table)
  (define t2 (make-hash))
  (for ([(rule-id by-token) (in-hash table)])
    (define by-token2 (make-hasheq))
    (for ([(token by-key) (in-hash by-token)])
      (hash-set! by-token2 token (hash-copy by-key)))
    (hash-set! t2 rule-id by-token2))
  t2)

(define (copy-cache cache)
  (parse-cache (copy-table (parse-cache-table cache))
               (hash-copy (parse-cache-spans cache))
               (hash-copy (parse-cache-pass-seen cache))))

;;; --------------------------------------------------------------------------
;;; Corpus - independent statements with varied (not repeated) content, so
;;; the corpus itself doesn't artificially trigger memo.rkt's same-pass
;;; content-interning collision guard (see private/memo.rkt) on every
;;; line - that guard exists for a real, rare edge case, not for "every
;;; statement is textually identical", which isn't realistic code anyway.
;;; --------------------------------------------------------------------------

(define (make-line i)
  (format "x~a = ~a + ~a * ~a\n"
          i (add1 (modulo i 97)) (add1 (modulo (* i 7) 89)) (add1 (modulo (* i 13) 83))))

;; Builds statement lines until reaching (at least) the target width, so
;; size is controlled directly rather than emerging from a shrink-prone
;; process.
(define (make-corpus width)
  (let loop ([i 0] [acc null] [len 0])
    (if (>= len width)
        (apply string-append (reverse acc))
        (let ([line (make-line i)])
          (loop (add1 i) (cons line acc) (+ len (string-length line)))))))

;;; --------------------------------------------------------------------------
;;; A controlled, position-targeted, length-changing edit: replace the
;;; single digit nearest a chosen fractional offset with a two-digit
;;; number. Isolates position as the only variable per row, same as
;;; incr-lex's own benchmark's edit-at.
;;; --------------------------------------------------------------------------

(define (nearest-digit-index raw around)
  (define n (string-length raw))
  (let loop ([d 0])
    (cond [(> d n) (min around (sub1 n))] ; degenerate fallback, shouldn't hit
          [(and (<= 0 (- around d)) (< (- around d) n) (char-numeric? (string-ref raw (- around d))))
           (- around d)]
          [(and (<= 0 (+ around d)) (< (+ around d) n) (char-numeric? (string-ref raw (+ around d))))
           (+ around d)]
          [else (loop (add1 d))])))

(define (edit-at raw fraction)
  (define n (string-length raw))
  (define around (min (sub1 n) (max 0 (inexact->exact (round (* fraction n))))))
  (define pos (nearest-digit-index raw around))
  (values pos 1 "93"))

(define POSITIONS `((start . 0.05) (mid . 0.5) (end . 0.95)))

;;; --------------------------------------------------------------------------
;;; A small, deterministic (not random) warmup history - a handful of
;;; edits at varied positions before the measured one, so the session
;;; isn't a freshly-built one-shot document. Kept deterministic rather
;;; than randomized, unlike incr-lex's own bounded-random-edit, so a
;;; re-run of this file produces directly comparable numbers turn to turn.
;;; --------------------------------------------------------------------------

(define (run-parse sess)
  (parse-session-run sess))

(define WARMUP-FRACTIONS '(0.1 0.3 0.7 0.9))

(define (warm-up sess0 raw0)
  (for/fold ([sess sess0] [raw raw0]) ([frac (in-list WARMUP-FRACTIONS)])
    (define-values (start old-len chunk) (edit-at raw frac))
    (define sess* (parse-session-edit sess start old-len chunk))
    (run-parse sess*) ; realize the reparse, not just the invalidation
    (values sess* (string-append (substring raw 0 start) chunk (substring raw (+ start old-len))))))

;; Each repetition gets its OWN independent copy of sess1's cache, built
;; and discarded outside the timed region - see copy-cache's own comment
;; for why this matters: without it, repetition 2 onward would be timing
;; "edit an already-edited cache" instead of "edit this exact warmed-up
;; state", which isn't the same operation and isn't repeatable.
(define (batch-incremental-ms sess1 start old-len chunk reps)
  (/ (for/sum ([_ (in-range reps)])
       (define fresh-sess (struct-copy parse-session sess1
                                        [cache (copy-cache (parse-session-cache sess1))]))
       (define t0 (current-inexact-monotonic-milliseconds))
       (run-parse (parse-session-edit fresh-sess start old-len chunk))
       (- (current-inexact-monotonic-milliseconds) t0))
     reps))

(define (median-incremental-ms sess1 start old-len chunk width #:trials [trials 5])
  (define reps (reps-for width))
  (median (for/list ([_ (in-range trials)]) (batch-incremental-ms sess1 start old-len chunk reps))))

;;; --------------------------------------------------------------------------
;;; One (width, position) cell.
;;; --------------------------------------------------------------------------

(define (bench-cell width fraction #:trials [trials 5])
  (define raw0 (make-corpus width))
  (define sess0 (make-parse-session toplevel-descriptor raw0))
  (run-parse sess0) ; cold parse once before warmup, matching real "open a file" behavior
  (define-values (sess1 raw1) (warm-up sess0 raw0))
  (define final-width (string-length raw1))
  (define-values (start old-len chunk) (edit-at raw1 fraction))
  (define incr-ms (median-incremental-ms sess1 start old-len chunk final-width #:trials trials))
  (define new-raw (string-append (substring raw1 0 start) chunk (substring raw1 (+ start old-len))))
  (define full-ms
    (median-ms (λ () (run-parse (make-parse-session toplevel-descriptor new-raw)))
               final-width #:trials trials))
  (list final-width fraction incr-ms full-ms (/ full-ms (max incr-ms 0.001))))

;;; --------------------------------------------------------------------------
;;; Full sweep: document-size x start/mid/end.
;;; --------------------------------------------------------------------------

(define (run-reparse-latency-sweep
         #:sizes [sizes '(2000 8000 32000 128000)]
         #:trials [trials 10])
  (for* ([width (in-list sizes)]
         [pos (in-list POSITIONS)])
    (match-define (list final-width _frac incr-ms full-ms speedup)
      (bench-cell width (cdr pos) #:trials trials))
    (printf "width=~a  pos=~a  incr=~ams  full=~ams  speedup=~ax\n"
            (~a final-width #:width 7) (~a (car pos) #:width 5)
            (~r incr-ms #:precision '(= 4)) (~r full-ms #:precision '(= 4))
            (~r speedup #:precision 2))))

(module+ main
  (run-reparse-latency-sweep))
