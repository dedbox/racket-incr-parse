#lang info

(define collection "incr-parse")
(define version "0.1")
(define pkg-authors '("Eric Griffis <dedbox@gmail.com>"))
(define pkg-desc "An incremental parser for modern, well-behaved programming languages.")
(define license '(MIT OR Apache-2.0))

(define deps
  '("base"
    "reprovide-lang-lib"
    "rope"))

(define build-deps
  '("racket-doc"
    "rackunit-lib"
    "scribble-lib"))

(define scribblings
  '(("scribblings/incr-parse.scrbl" ())))
