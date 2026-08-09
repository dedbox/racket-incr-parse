#lang racket

;; incr-parse/benchmarks/profile-hotspots.rkt
;;
;; Statistical CPU profile (racket/profile), not wall-clock latency - for
;; "where does the time actually go", not "how much of it is there".
;; Complements incremental-reparse-latency.rkt rather than replacing it:
;; that file answers "is incremental reuse paying off"; this one answers
;; "if it isn't, or isn't enough, which part is the actual bottleneck" -
;; green-cache hash-consing (intern-branch!), the memo table/bucket-index
;; itself, incr-lex's own relex, or genuine re-parse work on the content
;; that actually changed. Modeled on
;; incr-lex/benchmarks/reprofile-post-rope-fix.rkt's own split between a
;; cold full-parse profile, a typical-incremental-edits profile, and one
;; isolated single-edit profile.
;;
;; toplevel.rkt, same fixture as incremental-reparse-latency.rkt, so
;; results from the two files are directly comparable rather than
;; describing two different documents' behavior.

(require profile
         rope
         (only-in "../langs/arith.rkt" arith-nud-table arith-led-table arith-bp-table)
         "../langs/toplevel.rkt"
         "../private/memo.rkt"
         "../private/pratt.rkt")

;;; --------------------------------------------------------------------------
;;; Corpus - same generator as incremental-reparse-latency.rkt, duplicated
;;; rather than shared since neither file provides it and it's ~10 lines.
;;; --------------------------------------------------------------------------

(define (make-line i)
  (format "x~a = ~a + ~a * ~a\n"
          i (add1 (modulo i 97)) (add1 (modulo (* i 7) 89)) (add1 (modulo (* i 13) 83))))

(define (make-corpus width)
  (let loop ([i 0] [acc null] [len 0])
    (if (>= len width)
        (apply string-append (reverse acc))
        (let ([line (make-line i)])
          (loop (add1 i) (cons line acc) (+ len (string-length line)))))))

(define (nearest-digit-index raw around)
  (define n (string-length raw))
  (let loop ([d 0])
    (cond [(> d n) (min around (sub1 n))]
          [(and (<= 0 (- around d)) (< (- around d) n) (char-numeric? (string-ref raw (- around d))))
           (- around d)]
          [(and (<= 0 (+ around d)) (< (+ around d) n) (char-numeric? (string-ref raw (+ around d))))
           (+ around d)]
          [else (loop (add1 d))])))

(define (run-parse sess)
  (parameterize ([current-nud-table arith-nud-table]
                 [current-led-table arith-led-table]
                 [current-bp-table  arith-bp-table])
    (parse-session-run sess parse-program)))

;;; --------------------------------------------------------------------------
;;; profile-cold-parse: a single full parse of a large document, from a
;;; fresh session and a fresh cache. Where time goes here is entirely
;;; "first parse" cost - relex, green-tree construction/hash-consing,
;;; memo bookkeeping for entries that all miss (nothing to hit yet).
;;; --------------------------------------------------------------------------

(define (profile-cold-parse #:width [width 500000])
  (define raw (make-corpus width))
  (printf "profiling a single cold parse, width=~a chars\n" (string-length raw))
  (void (profile-thunk
         (λ () (run-parse (make-parse-session toplevel-lex toplevel-apply-edit
                                              string-rope-ropeable raw))))))

;;; --------------------------------------------------------------------------
;;; profile-typical-edits: many sequential small edits against one
;;; long-lived, warmed-up session - "steady-state editing", aggregated.
;;; Deterministic positions (cycling through a handful of fractions), not
;;; random, so a re-run profiles the identical scenario.
;;; --------------------------------------------------------------------------

(define EDIT-FRACTIONS '(0.1 0.2 0.35 0.5 0.65 0.8 0.9))

(define (profile-typical-edits #:width [width 500000] #:edits [edits 200])
  (define raw0 (make-corpus width))
  (define sess0 (make-parse-session toplevel-lex toplevel-apply-edit string-rope-ropeable raw0))
  (run-parse sess0)
  (printf "profiling ~a typical incremental edits against a width=~a session\n" edits (string-length raw0))
  (void
   (profile-thunk
    (λ ()
      (for/fold ([sess sess0] [raw raw0]) ([i (in-range edits)])
        (define frac (list-ref EDIT-FRACTIONS (modulo i (length EDIT-FRACTIONS))))
        (define around (min (sub1 (string-length raw)) (inexact->exact (round (* frac (string-length raw))))))
        (define pos (nearest-digit-index raw around))
        (define sess* (parse-session-edit sess pos 1 "93"))
        (run-parse sess*)
        (values sess* (string-append (substring raw 0 pos) "93" (substring raw (add1 pos)))))
      (void)))))

;;; --------------------------------------------------------------------------
;;; profile-single-edit: one isolated edit+reparse, profiled and timed on
;;; its own rather than averaged into 200 - the shape a single keystroke's
;;; worth of work actually has, uncluttered by everything else's noise.
;;; --------------------------------------------------------------------------

(define (profile-single-edit #:width [width 500000])
  (define raw (make-corpus width))
  (define sess0 (make-parse-session toplevel-lex toplevel-apply-edit string-rope-ropeable raw))
  (run-parse sess0)
  (define mid (quotient (string-length raw) 2))
  (define pos (nearest-digit-index raw mid))
  (printf "profiling one isolated edit+reparse at width=~a, offset=~a\n" (string-length raw) pos)
  (define t0 (current-inexact-monotonic-milliseconds))
  (void (profile-thunk (λ () (run-parse (parse-session-edit sess0 pos 1 "93")))))
  (printf "wall time: ~ams\n" (- (current-inexact-monotonic-milliseconds) t0)))

(module+ main
  (printf "== cold parse profile ==\n")
  (profile-cold-parse)
  (newline)
  (printf "== typical incremental-edits profile ==\n")
  (profile-typical-edits)
  (newline)
  (printf "== single isolated edit profile ==\n")
  (profile-single-edit))
