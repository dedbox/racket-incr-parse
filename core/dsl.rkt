#lang racket/base

;; incr-parse/core/dsl.rkt
;;
;; A syntax/parse-based grammar meta-language, compiling directly to the
;; core/combinators.rkt and core/pratt.rkt API.
;;
;; define-grammar covers RD productions: single-token case-dispatch,
;; guarded (multi-token-lookahead) dispatch, seq, rep, leaf tokens, the
;; hole/ghost recovery vocabulary, and try/alt backtracking. Every rule it
;; compiles is wrapped in memoize.
;;
;; define-pratt has been removed - see core/operator-grammar.rkt's
;; define-operator-grammar instead.
;;
;; Lexer definitions, session plumbing, and string entry points must be
;; defined separately for each language. This file only ever produces
;; parse-* bindings.
;;
;; STATUS (this phase's RD DSL redesign): #:dispatch alone could only ever
;; express single-token-of-lookahead case dispatch, which is why NONE of
;; the example grammars used this layer - toplevel.rkt needs one token of
;; lookahead PAST the leading token (peek2-kind) to tell "Ident = expr"
;; apart from a bare "Ident" expression, and test/try-alt-coverage.rkt's
;; toy ambig grammar needs real try/alt backtracking, neither of which
;; #:dispatch's literal-kind table could express. This redesign adds two
;; things, deliberately kept as two SEPARATE escape hatches rather than
;; one do-everything mechanism, mirroring how operator-grammar.rkt
;; documents mixfix templates as covering the common shapes and leaves
;; genuinely irregular cases to hand-written combinators:
;;
;;   1. #:cond - an ordered list of [guard prod] clauses plus a mandatory
;;      trailing [else prod], where a guard is a tiny hygienic mini-
;;      language (peek/peek2/and/or/not) rather than raw user Racket code
;;      touching the token stream directly - see "Guard mini-language"
;;      below for why raw code isn't an option here. This covers
;;      toplevel.rkt's stmt disambiguation exactly, and generalizes past
;;      it (peek/peek2 both take multiple kinds, e.g. (peek Ident Number)).
;;
;;   2. `commit`/`alt` prod forms, compiling directly to
;;      combinators.rkt's existing fail/try/alt - a `commit` leaf fails
;;      (via `fail`) on a kind mismatch instead of ghost-recovering, and
;;      is only meaningful inside an `alt`, which tries each branch in
;;      order and rolls back the parse offset on failure. This is a thin
;;      syntactic wrapper, not new engine behavior - core/combinators.rkt
;;      already does all the real work (rollback, memoized-subtree reuse
;;      across a backtrack); see test/try-alt-coverage.rkt for what that
;;      already-proven behavior looks like.
;;
;; Guard mini-language, and why it isn't just "drop into Racket":
;;
;;   A #:cond guard is NOT spliced in as arbitrary user Racket code
;;   referencing a raw `toks` identifier. If it were, the user's own
;;   `toks` reference and this macro's own `(lambda (toks) ...)` binder
;;   would be different identifiers under Racket's hygiene (same textual
;;   name, different lexical context - the classic "shadowing intent"
;;   hygiene trap), and the guard just wouldn't see the right value.
;;   Instead, compile-guard walks a small closed vocabulary
;;   (peek/peek2/and/or/not) at compile time and generates ALL the
;;   `(peek-kind ...)`/`(peek2-kind ...)` calls itself, threading through
;;   the exact same toks-id syntax object used for the rule's own lambda
;;   parameter - the user never types `toks` at all. This is the same
;;   pattern operator-grammar.rkt's compile-slot already uses (compile a
;;   restricted template into code that references identifiers the macro
;;   itself introduces, never ones the user is expected to write raw).

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         syntax/parse/define
         "combinators.rkt"
         "memo.rkt"
         "pratt.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Compile-time helpers
;;; --------------------------------------------------------------------------

(begin-for-syntax
  (define (parse-id name-stx)
    (format-id name-stx "parse-~a" (syntax-e name-stx)))

  ;; A prod compiles to a Parser VALUE, i.e. something usable directly as an
  ;; argument to seq/rep/alt, or applied to toks at a case/cond-clause site.
  ;;
  ;;   (call name)                 -> parse-name
  ;;   (token kind)                -> (expect 'kind)
  ;;   (leaf kind)                 -> a leaf consumer of that grammar kind
  ;;   (hole msg)                  -> hole-for-unexpected, wrapped
  ;;   (commit kind)               -> consume-as on match, (fail) otherwise -
  ;;                                   only meaningful as an alt branch's own
  ;;                                   divergence point (see try/alt below)
  ;;   (seq [name] part ...)       -> a branch, tagged `name` if given,
  ;;                                   otherwise the enclosing rule's own name
  ;;                                   - the [name] override is what lets
  ;;                                   distinct alt branches (e.g. two
  ;;                                   productions of one ambiguous rule)
  ;;                                   each get their own green-tree kind
  ;;   (rep binding elem #:until (kind ...)) -> a rep, stopping at those
  ;;                                   kinds or eof-kind
  ;;   (alt else-msg part ...)     -> tries each part via try/alt in order,
  ;;                                   rolling back the parse offset between
  ;;                                   attempts; else-msg becomes a
  ;;                                   hole-for-unexpected if every part
  ;;                                   fails. Each part is typically a `seq`
  ;;                                   whose divergence point is a `commit`.
  (define (compile-prod stx eof-kind enclosing-name)
    (syntax-parse stx
      #:datum-literals (call leaf hole token seq rep alt commit)
      [(call name:id)
       (parse-id #'name)]
      [(token kind:id)
       (syntax/loc stx (expect 'kind))]
      [(leaf kind:id)
       (syntax/loc stx (λ (toks) (consume-as 'kind toks)))]
      [(hole msg:str)
       (syntax/loc stx (λ (toks) (hole-for-unexpected msg toks)))]
      [(commit kind:id)
       ;; Deliberately breaks the no-fail convention on purpose - the
       ;; whole point of a commit slot is to be the divergence point an
       ;; enclosing `alt` backtracks past. A `commit` used outside any
       ;; `alt` will simply raise past the top of the parse; that's a
       ;; grammar-authoring error, not something this macro tries to
       ;; guard against statically.
       (syntax/loc stx
         (λ (toks)
           (if (eq? (peek-kind toks) 'kind)
               (consume-as 'kind toks)
               (fail))))]
      [(seq (~optional name:id) part ...)
       #:with (part-i ...) (for/list ([p (in-list (attribute part))])
                             (compile-prod p eof-kind enclosing-name))
       #:do [(define branch-name (if (attribute name) #'name enclosing-name))]
       (quasisyntax/loc stx (seq '#,branch-name part-i ...))]
      ;; #:until - stop as soon as the next kind is IN this allowlist (or
      ;; eof-kind, always implicitly included). Fits "keep going until you
      ;; see a closing delimiter" shapes, e.g. sexpr.rkt's list elements.
      [(rep binding:id elem #:until (until-kind:id ...))
       #:with elem-prod (compile-prod #'elem eof-kind enclosing-name)
       (quasisyntax/loc stx
         (rep 'binding elem-prod
              (λ (k) (case k [(until-kind ... #,eof-kind) #t] [else #f]))))]
      ;; #:while - keep going only as long as the next kind is IN this
      ;; allowlist; stop on anything else (or eof-kind). The inverse of
      ;; #:until, needed for "consume-while" shapes #:until's finite stop-
      ;; set can't express, e.g. try-alt-coverage.rkt's digits := D+, which
      ;; must stop on ANY non-D token (TagA, TagB, or whatever else follows
      ;; - not a fixed, enumerable stop set).
      [(rep binding:id elem #:while (while-kind:id ...))
       #:with elem-prod (compile-prod #'elem eof-kind enclosing-name)
       (quasisyntax/loc stx
         (rep 'binding elem-prod
              (λ (k) (case k [(while-kind ...) #f] [else #t]))))]
      [(alt else-msg:str part ...)
       #:with (part-i ...) (for/list ([p (in-list (attribute part))])
                             (compile-prod p eof-kind enclosing-name))
       (syntax/loc stx
         (alt (λ (toks) (hole-for-unexpected else-msg toks)) part-i ...))]))

  ;; A guard is the tiny closed vocabulary #:cond clauses are written in -
  ;; see the module header for why this isn't just raw Racket code. Always
  ;; compiled against toks-id, the SAME syntax object used for the
  ;; enclosing rule's own lambda parameter, so there is exactly one `toks`
  ;; identifier in the whole expansion and every reference to it - whether
  ;; generated for a guard or for a prod - resolves to that one binding.
  (define (compile-guard stx toks-id)
    (syntax-parse stx
      #:datum-literals (peek peek2 and or not)
      [(peek kind:id ...+)
       #`(memq (peek-kind #,toks-id) '(kind ...))]
      [(peek2 kind:id ...+)
       #`(memq (peek2-kind #,toks-id) '(kind ...))]
      [(and g ...+)
       #`(and #,@(for/list ([gi (in-list (attribute g))]) (compile-guard gi toks-id)))]
      [(or g ...+)
       #`(or #,@(for/list ([gi (in-list (attribute g))]) (compile-guard gi toks-id)))]
      [(not g)
       #`(not #,(compile-guard #'g toks-id))]))

  ;; A rule is a single-token case-dispatch, a guarded (#:cond) dispatch,
  ;; or a single prod standing in for the whole rule body (list and
  ;; program in sexpr.rkt, and any alt-rooted rule, are all this shape).
  (define (compile-rule stx eof-kind)
    (syntax-parse stx
      #:datum-literals (rule)
      ;; ---- single-token case-dispatch (unchanged from before this phase) --
      [(rule name:id #:dispatch [(kind:id ...) p] ...
             #:eof eof-msg:str #:else else-msg:str)
       #:with pid (parse-id #'name)
       #:with (clause ...) (for/list ([ks   (in-list (attribute kind))]
                                      [prod (in-list (attribute p))])
                             (quasisyntax/loc (car ks)
                               [#,ks (#,(compile-prod prod eof-kind #'name) toks)]))
       (quasisyntax/loc stx
         (define pid
           (memoize 'name (λ (toks)
                            (case (peek-kind toks)
                              clause ...
                              [(#,eof-kind) (empty-hole-here eof-msg toks)]
                              [else (hole-for-unexpected else-msg toks)])))))]
      ;; ---- guarded dispatch: arbitrary peek/peek2 lookahead ---------------
      ;;
      ;; Unlike #:dispatch, there's no separate #:eof/#:else - the final
      ;; [else prod] clause is an ordinary production, not automatically a
      ;; hole. This matters: toplevel.rkt's real disambiguation is "if
      ;; Ident is followed by Equals, it's an assignment; OTHERWISE it's a
      ;; full expression production" - the fallback is a real parse, not
      ;; an error. A grammar that DOES want a hole on the fallback path can
      ;; still say so explicitly: [else (hole "...")].
      [(rule name:id #:cond
             [guard prod] ...+
             [(~datum else) else-prod])
       #:with pid (parse-id #'name)
       #:with toks-id (generate-temporary 'toks)
       #:with (guard-code ...) (for/list ([g (in-list (attribute guard))])
                                 (compile-guard g #'toks-id))
       #:with (prod-i ...) (for/list ([p (in-list (attribute prod))])
                             (compile-prod p eof-kind #'name))
       #:with else-prod-i (compile-prod #'else-prod eof-kind #'name)
       (quasisyntax/loc stx
         (define pid
           (memoize 'name (λ (toks-id)
                            (cond
                              [guard-code (prod-i toks-id)] ...
                              [else (else-prod-i toks-id)])))))]
      ;; ---- single-prod rule body (seq/rep/alt/call standing alone) -------
      [(rule name:id p)
       #:with pid (parse-id #'name)
       #:with prod (compile-prod #'p eof-kind #'name)
       (quasisyntax/loc stx (define pid (memoize 'name prod)))])))

;;; --------------------------------------------------------------------------
;;; define-grammar
;;; --------------------------------------------------------------------------

;; grammar-name is unused in the expansion today, kept only so a grammar reads
;; like a named unit at its call site, matching how the two hand-written toy
;; grammars are each identified by their file, not by any binding inside it.
(define-simple-macro (define-grammar grammar-name:id
                       (~optional (~seq #:eof-kind eof-kind:id)
                                  #:defaults ([eof-kind #'incr-lex:eof]))
                       rule-form ...)
  #:with (rule ...) (for/list ([r (in-list (attribute rule-form))])
                      (compile-rule r #'eof-kind))
  (begin rule ...))

;;; --------------------------------------------------------------------------
;;; define-pratt has been removed. See core/operator-grammar.rkt's
;;; define-operator-grammar instead - an Agda-style fixity + precedence
;;; declaration layer that never exposes nud/led/bp, replacing this macro
;;; entirely rather than sitting alongside it.
;;; --------------------------------------------------------------------------

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require (prefix-in lex: incr-lex)
           rackunit
           racket/list
           rope
           "green.rkt"
           "hole-ghost.rkt"
           "printer.rkt"
           "token-stream.rkt")

  ;; Hand-built tokens, bypassing a real lexer.
  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))
  (define (toks . pairs)
    (tokens->stream
     (let loop ([ps pairs])
       (if (null? ps)
           (list (mk-tok 'incr-lex:eof ""))
           (cons (mk-tok (car ps) (cadr ps)) (loop (cddr ps)))))))

  ;; Fresh cache + fresh pass helper, matching memo.rkt's own test
  ;; convention - needed here (unlike the plain #:dispatch tests below)
  ;; because the try/alt tests exercise real backtracking, which reads
  ;; current-parse-offset/current-parse-cache.
  (define (run-fresh parser toks)
    (define cache (make-parse-cache))
    (parameterize ([current-parse-cache cache] [current-parse-offset (box 0)])
      (parse-cache-begin-pass! cache)
      (parser toks)))

  ;;; ------------------------------------------------------------------------
  ;;; #:dispatch - reimplements langs/sexpr.rkt's grammar (unchanged coverage)
  ;;; ------------------------------------------------------------------------

  (define-grammar sx-grammar
    (rule sexpr
          #:dispatch
          [(LParen)        (call list)]
          [(Symbol Number) (leaf atom)]
          [(RParen)        (hole "unexpected closing parenthesis")]
          #:eof  "expected an expression"
          #:else "expected an expression, found unrecognized input")
    (rule list
          (seq (token LParen)
               (rep elements (call sexpr) #:until (RParen))
               (token RParen)))
    (rule sx-program
          (rep sexprs (call sexpr) #:until ())))

  (test-case "define-grammar: well-formed input produces the expected shape"
    (define-values (tree rest)
      (parse-sx-program (toks 'LParen "(" 'Symbol "foo" 'Number "1" 'RParen ")")))
    (check-eq? (peek-kind rest) 'incr-lex:eof)
    (check-eq? (green-tree-kind tree) 'sexprs)
    (define top (car (green-branch-children tree)))
    (check-eq? (green-tree-kind top) 'list)
    (define elements (cadr (green-branch-children top)))
    (check-equal? (length (green-branch-children elements)) 2))

  (test-case "define-grammar: stray RParen produces a staged hole"
    (define-values (tree rest) (parse-sx-program (toks 'RParen ")")))
    (define first (car (green-branch-children tree)))
    (check-true (hole? first))
    (check-eq? (hole-status first) 'staged))

  (test-case "define-grammar: unterminated list produces a ghost RParen"
    (define-values (tree rest) (parse-sx-program (toks 'LParen "(" 'Symbol "x")))
    (define lst (car (green-branch-children tree)))
    (define last-child (last (green-branch-children lst)))
    (check-true (ghost? last-child))
    (check-eq? (ghost-of last-child) 'RParen))

  ;;; ------------------------------------------------------------------------
  ;;; #:cond - reimplements toplevel.rkt's peek2-kind disambiguation
  ;;;
  ;;; A minimal stand-in for arith.rkt's real parse-expr: just a leaf atom,
  ;;; enough to prove #:cond's fallback branch is a real production, not a
  ;;; hole, and that the assignment branch and the plain-expression branch
  ;;; produce genuinely different tree shapes from the identical leading
  ;;; Ident token.
  ;;; ------------------------------------------------------------------------

  (define-grammar cond-grammar
    (rule expr (leaf atom))
    (rule assign (seq (token Ident) (token Equals) (call expr)))
    (rule stmt
          #:cond
          [(and (peek Ident) (peek2 Equals)) (call assign)]
          [else (call expr)]))

  (test-case "#:cond: Ident followed by Equals dispatches to assign"
    (define-values (tree rest)
      (parse-stmt (toks 'Ident "x" 'Equals "=" 'Number "1")))
    (check-eq? (green-tree-kind tree) 'assign)
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "#:cond: bare Ident (no following Equals) falls through to expr"
    (define-values (tree rest) (parse-stmt (toks 'Ident "x")))
    (check-eq? (green-tree-kind tree) 'atom)
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "#:cond: Number never matches the guard, still falls through to expr"
    (define-values (tree rest) (parse-stmt (toks 'Number "1")))
    (check-eq? (green-tree-kind tree) 'atom))

  ;;; ------------------------------------------------------------------------
  ;;; commit/alt - reimplements test/try-alt-coverage.rkt's ambig grammar
  ;;;
  ;;;   program := ambig*
  ;;;   ambig   := digits TagA        ; production A
  ;;;            | digits TagB        ; production B
  ;;;   digits  := D+                 ; #:while (D), not #:until - the stop
  ;;;                                 ; set here is "anything that isn't D",
  ;;;                                 ; not a fixed enumerable list, which is
  ;;;                                 ; exactly why #:while exists alongside
  ;;;                                 ; #:until (see the rep clause above)
  ;;;
  ;;; digits is unbounded, so no fixed lookahead can disambiguate A from B -
  ;;; this is exactly the case #:cond CANNOT express and alt/commit exists
  ;;; for. Real reuse-across-backtrack of a memoized sub-parse (digits, in
  ;;; this shape) is already proven, with call-counting instrumentation, by
  ;;; the untouched test/try-alt-coverage.rkt at the combinator level - that
  ;;; proof doesn't need re-deriving here. What's specific to THIS test
  ;;; module is that commit/alt's *compiled expansion* through the DSL
  ;;; produces the same observable behavior as the hand-written combinators
  ;;; it compiles down to.
  ;;; ------------------------------------------------------------------------

  (define-grammar ambig-grammar
    (rule digits (rep ds (leaf digit) #:while (D)))
    (rule ambig
          (alt "neither TagA nor TagB"
               (seq prod-a (call digits) (commit TagA))
               (seq prod-b (call digits) (commit TagB))))
    (rule program
          (rep items (call ambig) #:until ())))

  (test-case "commit/alt: production A wins when the run of D's ends in TagA"
    (define-values (tree _rest)
      (run-fresh parse-ambig (toks 'D "5" 'D "5" 'D "5" 'TagA "a")))
    (check-eq? (green-tree-kind tree) 'prod-a)
    (check-equal? (green->source tree) "555a"))

  (test-case "commit/alt: production B wins when the run of D's ends in TagB"
    (define-values (tree _rest)
      (run-fresh parse-ambig (toks 'D "5" 'D "5" 'TagB "b")))
    (check-eq? (green-tree-kind tree) 'prod-b)
    (check-equal? (green->source tree) "55b"))

  (test-case "commit/alt: zero-length shared prefix still disambiguates correctly"
    (define-values (tree-a _r1) (run-fresh parse-ambig (toks 'TagA "a")))
    (check-eq? (green-tree-kind tree-a) 'prod-a)
    (define-values (tree-b _r2) (run-fresh parse-ambig (toks 'TagB "b")))
    (check-eq? (green-tree-kind tree-b) 'prod-b))

  (test-case "commit/alt: neither tag present - resilience holds, no raise escapes"
    (define-values (tree _rest)
      (run-fresh parse-ambig (toks 'D "5" 'D "5" 'TagC "c")))
    (check-true (hole? tree))
    (check-eq? (hole-status tree) 'staged))

  (test-case "commit/alt: a 3-item program - backtrack on item 1 does not disturb items 2/3"
    ;; The project's own standing caution (Design Fact 9's postmortem):
    ;; trace the 3-item case, not just the 2-item case, for anything
    ;; involving repetition or chaining - a single ambig item backtracking
    ;; correctly says nothing about whether `rep`'s own loop state (the
    ;; token stream position it threads to the NEXT item) survives that
    ;; backtrack intact.
    (define-values (tree rest)
      (run-fresh parse-program
                 (toks 'D "5" 'D "5" 'TagB "b"      ; item 1: backtracks A -> B
                       'D "5" 'TagA "a"              ; item 2: no backtrack needed
                       'TagA "a")))                  ; item 3: zero-length digits run
    (check-equal? (green->source tree) "55b5aa")
    (check-equal? (map green-tree-kind (green-branch-children tree))
                  '(prod-b prod-a prod-a))
    (check-eq? (peek-kind rest) 'incr-lex:eof)))
