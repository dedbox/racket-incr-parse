#lang scribble/manual

@; scribblings/incr-lex.scrbl

@(require scribble/example
          racket/sandbox
          @for-label[incr-lex
                     incr-parse
                     racket/base
                     racket/contract
                     rope])

@(define incr-parse-eval (make-base-eval))
@(incr-parse-eval '(require incr-parse incr-lex rope))

@title{incr-parse: An incremental parser for modern, well-behaved languages}
@author{@author+email["Eric Griffis" "dedbox@gmail.com"]}

@defmodule[incr-parse]

@(close-eval incr-parse-eval)
