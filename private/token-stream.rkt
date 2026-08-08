#lang racket/base

;; incr-parse/private/token-stream.rkt
;;
;; Parser's input representation. A vector of tokens plus an integer position,
;; replacing the earlier (listof token?) representation.
;;
;; Advancing past N tokens is O(1), not O(N). That matters specifically for a
;; memo hit's continuation, which used to replay list-tail across every token
;; the cached rule had consumed, on every hit.
;;
;; A stream's identity is never compared - only its CURRENT token (via
;; stream-peek) is, exactly as (car toks) was under the list representation.

(require (prefix-in lex: incr-lex))

(provide (all-defined-out))

(struct token-stream (vec pos) #:transparent)

;; The one conversion point. Session entry points build a stream from
;; incr-lex's token list once, at the top of a parse; test fixtures do the
;; same over manually constructed tokens.
(define (tokens->stream toks)
  (token-stream (list->vector toks) 0))

;; Clamped peek. Nothing should ever legitimately advance past the eof
;; sentinel, which is always the vector's last element, but clamping keeps
;; peek total.
(define (stream-peek s)
  (define vec (token-stream-vec s))
  (vector-ref vec (min (token-stream-pos s) (sub1 (vector-length vec)))))

(define (stream-peek-kind s) (lex:token-kind (stream-peek s)))

(define (stream-at-eof? s)
  (>= (token-stream-pos s) (sub1 (vector-length (token-stream-vec s)))))

;; O(1): advances past the current token.
(define (stream-rest s)
  (token-stream (token-stream-vec s) (add1 (token-stream-pos s))))

;; O(1): skip n tokens without re-walking them.
(define (stream-advance s n)
  (token-stream (token-stream-vec s) (+ (token-stream-pos s) n)))

;; O(1): the number of tokens between two streams over the SAME vector.
(define (stream-delta before after)
  (- (token-stream-pos after) (token-stream-pos before)))

(module+ test
  (require rackunit
           rope)

  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))

  (test-case "peek/rest/advance walk the same underlying vector"
    (define s (tokens->stream (list (mk-tok 'A "a") (mk-tok 'B "b")
                                    (mk-tok 'incr-lex:eof ""))))
    (check-eq? (stream-peek-kind s) 'A)
    (define s1 (stream-rest s))
    (check-eq? (stream-peek-kind s1) 'B)
    (define s2 (stream-advance s 2))
    (check-eq? (stream-peek-kind s2) 'incr-lex:eof)
    (check-true (stream-at-eof? s2)))

  (test-case "peek clamps past the eof sentinel instead of failing"
    (define s (tokens->stream (list (mk-tok 'incr-lex:eof ""))))
    (define s1 (stream-advance s 5))
    (check-eq? (stream-peek-kind s1) 'incr-lex:eof))

  (test-case "stream-delta measures tokens consumed between two streams"
    (define s (tokens->stream (list (mk-tok 'A "a") (mk-tok 'B "b")
                                    (mk-tok 'incr-lex:eof ""))))
    (define s2 (stream-rest (stream-rest s)))
    (check-equal? (stream-delta s s2) 2)))
