#lang racket/base

;; incr-parse/langs/hazelnut.rkt
;;
;; Stress-test grammar: a minimal Hazelnut-style typed core language.
;;
;; "Hazelnut" is Hazel's pedagogical calculus (Omar et al., "Hazelnut: A
;; Bidirectionally Typed Structure Editor Calculus" (POPL 2017)). This is a
;; concrete surface syntax for something close to that calculus's expression
;; language.
;;
;;   let double = λx:ℕ.x + 1 in double (double 3)
;;   λf:ℕ→ℕ.λx:ℕ.f (f x)
;;
;; Grammar:
;;   Type := ℕ | 𝔹 | Type "→" Type | "(" Type ")"
;;   Expr := Ident | Number | 𝕥 | 𝕗
;;         | "λ" Ident ":" Type "." Expr        (lambda)
;;         | "let" Ident "=" Expr "in" Expr     (let)
;;         | Expr "?" Expr ":" Expr             (ternary conditional)
;;         | Expr Expr                          (application, juxtaposition)
;;         | Expr ("+"|"-") Expr
;;         | Expr ("*"|"/") Expr
;;         | Expr ("<"|"≡") Expr
;;         | "(" Expr ")"
;;
;; There are two sorts in one grammar file with one Pratt engine.
;;
;; A program is a single Expr, and Expr embeds Type wherever a lambda names
;; its parameter's type. Both sorts reuse pratt.rkt's parse-expr/
;; parse-nud/parse-led without modification. parse-type just installs a second,
;; independent set of nud/led/bp tables via parameterize, plus its own
;; memoization rule-id. Without a distinct rule-id, a Type
;; parse and an Expr parse could go into the same memo bucket if they ever
;; started at the same token object, and one sort's cached tree could be returned for
;; the other.
;;
;; Nesting works by ordinary parameterize dynamic extent. A lambda's nud calls
;; parse-type for its annotation, which installs Type's tables for that
;; sub-parse, then Expr's tables are restored automatically upon return. No
;; manual save/restore is needed.
;;
;; Every nud/led entry here is built from ordinary seq/expect/consume-as, so
;; recovery uses the same ghost/hole machinery throughout the project. A
;; missing "." after a lambda's type annotation, a missing "in" in a let, and
;; a missing ":" in a ternary all recover as a ghost with no crash.

(require (prefix-in : incr-lex)
         rope
         "../private/ast.rkt"
         "../private/combinators.rkt"
         "../private/green.rkt"
         "../private/hole-ghost.rkt"
         "../private/memo.rkt"
         "../private/pratt.rkt"
         "../private/printer.rkt"
         "../private/token-stream.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Lexer
;;; --------------------------------------------------------------------------

(:define-tokens hazelnut-tokens
  ;; Trivia
  [Whitespace   := (+ :ws)]
  [Newline      := :nl]
  ;; Types
  [NumT         := "ℕ"]
  [BoolT        := "𝔹"]
  [Arrow        := "→"]
  ;; Expressions
  [Fun          := "λ"]
  [Dot          := "."]
  [Colon        := ":"]
  [Let          := "let"]
  [Eq           := "="]
  [In           := "in"]
  [Question     := "?"]
  [True         := "𝕥"]
  [False        := "𝕗"]
  [Keyword      := (or Let In)]
  [GlyphKeyword := (or Fun NumT BoolT True False)]
  ;; Shared
  [LParen       := "("]
  [RParen       := ")"]
  [Plus         := "+"]
  [Minus        := "-"]
  [Star         := "*"]
  [Slash        := "/"]
  [Lt           := "<"]
  [EqEq         := "≡"]
  [Number       := (+ :digit)]
  [Ident        := (and (seq :alpha (* :alnum))
                        (not Keyword)
                        (not-containing GlyphKeyword))])

;; => defines hazelnut-lex and hazelnut-apply-edit
(:define-lexer hazelnut
  #:tokens    hazelnut-tokens
  #:token-set [NumT BoolT Arrow Fun Dot Colon Let Eq In Question True False
               LParen RParen Plus Minus Star Slash Lt EqEq Number Ident]
  #:leading   [Whitespace Newline]
  #:trailing  [Whitespace Newline]
  #:newline   [Newline])

;;; --------------------------------------------------------------------------
;;; Type Tables
;;; --------------------------------------------------------------------------

(define type-nud-table
  (hash 'NumT   (λ (toks) (consume-as 'base toks))
        'BoolT  (λ (toks) (consume-as 'base toks))
        'LParen (nud-paren 'LParen 'RParen)))

(define type-led-table
  (hash 'Arrow (led-infix 'Arrow #:kind 'arrow-type)))

;; Arrow is right-associative: ℕ→ℕ→𝔹 is ℕ→(ℕ→𝔹). right-bp = left-bp - 1 is
;; the minimum change that lets the SAME operator recur while parsing its
;; own right operand, under this engine's strict left-bp > min-bp loop
;; condition - see private/grammar.rkt's define-pratt for where this was
;; first derived and unit-tested in isolation.
(define type-bp-table
  (hash 'Arrow (cons 1 0)))

;; The one place a Type parse begins - swaps in Type's own tables AND its
;; own memoization rule-id for the dynamic extent of this call, then
;; parse-expr's own generic climbing engine does the rest.
(define (parse-type toks min-bp)
  (parameterize ([current-nud-table type-nud-table]
                 [current-led-table type-led-table]
                 [current-bp-table  type-bp-table]
                 [current-expr-rule-id 'type])
    (parse-expr toks min-bp)))

;;; --------------------------------------------------------------------------
;;; Expr Tables
;;; --------------------------------------------------------------------------

;; λ Ident ":" Type "." Expr
(define nud-fun
  (seq 'fun
       (expect 'Fun)
       (expect 'Ident)
       (expect 'Colon)
       (λ (toks) (parse-type toks 0))
       (expect 'Dot)
       (λ (toks) (parse-expr toks 0))))

;; "let" Ident "=" Expr "in" Expr
(define nud-let
  (seq 'let
       (expect 'Let)
       (expect 'Ident)
       (expect 'Eq)
       (λ (toks) (parse-expr toks 0))
       (expect 'In)
       (λ (toks) (parse-expr toks 0))))

;; Expr "?" Expr ":" Expr - a hand-written led entry, not one of pratt.rkt's
;; reusable builders, since none of led-infix/nud-prefix/nud-paren fit a
;; three-part, two-delimiter shape. Right-associative, lowest precedence -
;; see TERNARY-BP below.
(define (led-ternary left toks)
  (define-values (q toks1) (consume-as 'Question toks))
  (define-values (then-branch toks2) (parse-expr toks1 0))
  (define-values (c toks3) ((expect 'Colon) toks2))
  (define-values (else-branch toks4) (parse-expr toks3 TERNARY-RBP))
  (values (intern-branch! 'ternary (list left q then-branch c else-branch)) toks4))

;; Application by juxtaposition - no operator token at all, the "operator"
;; is simply another atom-shaped expression appearing right after a
;; complete one. Tightest binding power, left-associative (f x y is
;; (f x) y), via the same led-loop mechanism as any ordinary infix
;; operator, just without led-infix's own leading consume-as.
(define (led-apply left toks)
  (define-values (arg toks*) (parse-expr toks APP-RBP))
  (values (intern-branch! 'app (list left arg)) toks*))

;; bp numbering, loosest to tightest: ternary < comparison < additive 
;; multiplicative < application. Ternary's right-bp of 0 is what lets a
;; nested ternary's own else-branch re-trigger the SAME operator
;; (right-associative, matching the ?: convention in every C-family
;; language that has one).
(define TERNARY-LBP 1)  (define TERNARY-RBP 0)
(define CMP-LBP      3) (define CMP-RBP      4)
(define ADD-LBP      5) (define ADD-RBP      6)
(define MUL-LBP      7) (define MUL-RBP      8)
(define APP-LBP      9) (define APP-RBP     10)

;; Every atom-starting kind that can stand as a juxtaposed application
;; argument. Deliberately narrower than the full nud-table key set: an
;; unparenthesized fun/let as a bare application argument reads as
;; ambiguous to a human even though it wouldn't be to this parser, so (like
;; most real languages) it's required to be parenthesized instead.
(define APPLICABLE-KINDS '(Ident Number True False LParen))

(define expr-nud-table
  (hash 'Ident   (λ (toks) (consume-as 'var toks))
        'Number  (λ (toks) (consume-as 'num toks))
        'True    (λ (toks) (consume-as 'bool toks))
        'False   (λ (toks) (consume-as 'bool toks))
        'LParen  (nud-paren 'LParen 'RParen)
        'Fun     nud-fun
        'Let     nud-let))

(define expr-led-table
  (for/fold ([t (hash 'Plus  (led-infix 'Plus)
                       'Minus (led-infix 'Minus)
                       'Star  (led-infix 'Star)
                       'Slash (led-infix 'Slash)
                       'Lt    (led-infix 'Lt)
                       'EqEq  (led-infix 'EqEq)
                       'Question led-ternary)])
            ([k (in-list APPLICABLE-KINDS)])
    (hash-set t k led-apply)))

(define expr-bp-table
  (for/fold ([t (hash 'Question (cons TERNARY-LBP TERNARY-RBP)
                       'Plus  (cons ADD-LBP ADD-RBP)
                       'Minus (cons ADD-LBP ADD-RBP)
                       'Star  (cons MUL-LBP MUL-RBP)
                       'Slash (cons MUL-LBP MUL-RBP)
                       'Lt    (cons CMP-LBP CMP-RBP)
                       'EqEq  (cons CMP-LBP CMP-RBP))])
            ([k (in-list APPLICABLE-KINDS)])
    (hash-set t k (cons APP-LBP APP-RBP))))

;;; --------------------------------------------------------------------------
;;; AST
;;; --------------------------------------------------------------------------

;; This grammar never requires arith.rkt/sexpr.rkt/toplevel.rkt, so it can't
;; rely on any of THEIR elaborator registrations either - ast.rkt's registry
;; is one shared table keyed by symbol, populated only by whichever grammar
;; modules happen to have been loaded into the same process, and that's not
;; something this file's own correctness should depend on. Every kind this
;; grammar actually produces gets its own registration here, even 'paren
;; and 'binop, which arith.rkt also happens to use for the exact same shape.
;;
;; 'base (NumT/BoolT) needs no elaborator at all: consume-as makes it a leaf,
;; not a branch, so ast.rkt's built-in green-token case already covers it -
;; the elaborated leaf's own .kind is the underlying lexer kind (NumT or
;; BoolT), not the grammar-level 'base label, exactly like 'atom in
;; langs/arith.rkt never needing one either.

(define-elaborator paren (branch)
  (elaborate (cadr (green-branch-children branch))))

(struct ast-binop (op left right) #:transparent)

(define-elaborator binop (branch)
  (define c (green-branch-children branch))
  (ast-binop (ast-leaf-kind (elaborate (cadr c))) (elaborate (car c)) (elaborate (caddr c))))

(struct ast-arrow-type (from to) #:transparent)

(define-elaborator arrow-type (branch)
  (define c (green-branch-children branch))
  (ast-arrow-type (elaborate (car c)) (elaborate (caddr c))))

(struct ast-fun (param param-type body) #:transparent)
(struct ast-let (name expr body) #:transparent)
(struct ast-ternary (test then else) #:transparent)
(struct ast-app (fn arg) #:transparent)

(define-elaborator fun (branch)
  (define c (green-branch-children branch))
  ;; c: Fun-leaf, Ident-leaf, Colon-leaf, Type, Dot-leaf, Expr
  (ast-fun (elaborate (list-ref c 1)) (elaborate (list-ref c 3)) (elaborate (list-ref c 5))))

(define-elaborator let (branch)
  (define c (green-branch-children branch))
  ;; c: Let-leaf, Ident-leaf, Eq-leaf, Expr, In-leaf, Expr
  (ast-let (elaborate (list-ref c 1)) (elaborate (list-ref c 3)) (elaborate (list-ref c 5))))

(define-elaborator ternary (branch)
  (define c (green-branch-children branch))
  (ast-ternary (elaborate (car c)) (elaborate (cadr c)) (elaborate (caddr c))))

(define-elaborator app (branch)
  (define c (green-branch-children branch))
  (ast-app (elaborate (car c)) (elaborate (cadr c))))

;; var/num/bool need no elaborator registration at all - they're leaves
;; (consume-as, not a branch), so ast.rkt's built-in green-token case
;; already covers them.

;;; --------------------------------------------------------------------------
;;; Entry Point
;;; --------------------------------------------------------------------------

(define (parse-hazelnut-string str)
  (define sess (:make-session hazelnut-lex hazelnut-apply-edit string-rope-ropeable str))
  (define toks (tokens->stream (:session->tokens-list sess)))
  (define-values (tree remaining)
    (parameterize ([current-nud-table expr-nud-table]
                   [current-led-table expr-led-table]
                   [current-bp-table  expr-bp-table]
                   [current-expr-rule-id 'expr])
      (parse-expr toks 0)))
  (unless (eq? (peek-kind remaining) 'incr-lex:eof)
    (error 'parse-hazelnut-string "parser did not consume the full token stream"))
  tree)

(define (elaborate-hazelnut-string str)
  (elaborate (parse-hazelnut-string str)))

;; The bound grammar descriptor for this file. The entry point is Expr. Type
;; is only ever reached internally, via parse-type, wherever an Expr
;; production expects one. #:with-setup installs Expr's tables and
;; expr-rule-id. parse-type installs Type's own tables for its dynamic extent
;; regardless, but setting expr-rule-id here too keeps this descriptor's setup
;; a complete, self-contained mirror of parse-hazelnut-string's parameterize
;; block below, instead of a partial one that relies on the default
;; coincidentally being 'expr.
(define (hazelnut-with-setup run)
  (λ (toks)
    (parameterize ([current-nud-table expr-nud-table]
                   [current-led-table expr-led-table]
                   [current-bp-table  expr-bp-table]
                   [current-expr-rule-id 'expr])
      (run toks))))

(define hazelnut-descriptor
  (make-grammar-descriptor hazelnut-lex hazelnut-apply-edit
                           (λ (toks) (parse-expr toks 0))
                           #:with-setup hazelnut-with-setup
                           #:ropeable string-rope-ropeable))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require racket/list
           rackunit
           incr-lex/engine)

  (define (check-round-trip src)
    (check-equal? (green->source (parse-hazelnut-string src)) src))

  (test-case "round-trip: a lambda with an arrow-typed parameter"
    (check-round-trip "λf:ℕ→ℕ.λx:ℕ.f (f x)"))

  (test-case "round-trip: let, ternary, arithmetic, application together"
    (check-round-trip "let double = λx:ℕ.x * 2 in double (double 3) < 100 ? 𝕥 : 𝕗"))

  (test-case "round-trip: recovery cases"
    (check-round-trip "λx:ℕ x")               ; missing "." -> ghost
    (check-round-trip "let x = 1 x + 1")      ; missing "▸" -> ghost (round-trip
                                              ; holds regardless of how the
                                              ; surrounding tokens end up
                                              ; grouped - application is
                                              ; greedy, so this doesn't parse
                                              ; as a clean 3-piece let, but
                                              ; every token still round-trips)
    (check-round-trip "1 < 2 ? 3")            ; missing ":"+else -> ghost + empty hole
    (check-round-trip "(1 + 2"))              ; missing ")" -> ghost, same as arith.rkt

  (test-case "sort transition: a lambda's annotation is genuinely parsed as a Type, not an Expr"
    (define tree (parse-hazelnut-string "λx:ℕ→𝔹.𝕥"))
    (define ty (list-ref (green-branch-children tree) 3))
    ;; 'arrow-type, not 'binop - Type's own Arrow led is kept distinct from
    ;; Expr's arithmetic binops precisely so the two sorts can't collide in
    ;; ast.rkt's shared, symbol-keyed elaborator registry. See led-infix's
    ;; #:kind argument.
    (check-eq? (green-tree-kind ty) 'arrow-type)
    (define-values (l op r) (apply values (green-branch-children ty)))
    (check-eq? (green-tree-kind l) 'base)
    (check-eq? (:token-kind (green-token-token op)) 'Arrow)
    (check-eq? (green-tree-kind r) 'base))

  (test-case "application is left-associative and tighter than arithmetic: f x + 1 is (f x) + 1"
    (define tree (parse-hazelnut-string "f x + 1"))
    (check-eq? (green-tree-kind tree) 'binop)
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'app)
    (check-eq? (green-tree-kind r) 'num))

  (test-case "ternary is right-associative: a ? b : c ? d : e is a ? b : (c ? d : e)"
    (define tree (parse-hazelnut-string "1 < 2 ? 3 : 4 < 5 ? 6 : 7"))
    (check-eq? (green-tree-kind tree) 'ternary)
    (define-values (test _q then _c else) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind test) 'binop)
    (check-eq? (green-tree-kind then) 'num)
    (check-eq? (green-tree-kind else) 'ternary))

  (test-case "AST: sort transition is visible in the elaborated tree too"
    (define ast (elaborate-hazelnut-string "λx:ℕ→𝔹.𝕥"))
    (check-true (ast-fun? ast))
    (check-true (ast-arrow-type? (ast-fun-param-type ast)))
    ;; A simple (non-arrow) Type is just a leaf - see the AST section's own
    ;; header comment on why 'base needs no elaborator of its own.
    (check-eq? (ast-leaf-kind (ast-arrow-type-from (ast-fun-param-type ast))) 'NumT)
    (check-eq? (ast-leaf-kind (ast-arrow-type-to (ast-fun-param-type ast))) 'BoolT))

  (test-case "AST: let and application elaborate distinctly"
    (define ast (elaborate-hazelnut-string "let id = λx:ℕ.x in id 5"))
    (check-true (ast-let? ast))
    (check-true (ast-fun? (ast-let-expr ast)))
    (check-true (ast-app? (ast-let-body ast))))

  (test-case "incremental reparse: an untouched deeply-nested sibling survives an edit"
    (define src "λx:ℕ.((x + 1) * (x + 2)) + x")
    (define sess1 (make-parse-session hazelnut-descriptor src))
    (define tree1 (parse-session-tree (parse-session-run sess1)))
    ;; offset 11 is the "1" inside "x + 1" - replace it with "11"
    (define sess2 (parse-session-edit sess1 11 1 "11"))
    (define tree2 (parse-session-tree (parse-session-run sess2)))
    (check-equal? (green->source tree2) "λx:ℕ.((x + 11) * (x + 2)) + x")
    (define (find-plus-2 t)
      (cond [(and (green-branch? t) (eq? (green-tree-kind t) 'binop)
                  (let ([r (caddr (green-branch-children t))])
                    (and (eq? (green-tree-kind r) 'num)
                         (equal? (rope->string (token-payload (green-token-token r))) "2"))))
             t]
            [(green-branch? t) (ormap find-plus-2 (green-branch-children t))]
            [else #f]))
    (define p1 (find-plus-2 tree1))
    (define p2 (find-plus-2 tree2))
    (check-not-false p1)
    (check-eq? p1 p2)
    (parse-session-unload! sess2)))

(module+ main
  (for ([src (list "λf:ℕ→ℕ.λx:ℕ.f (f x)"
                    "let double = λx:ℕ.x * 2 in double (double 3) < 100 ? 𝕥 : 𝕗"
                    "λx:ℕ x"          ; missing "."
                    "1 < 2 ? 3")])    ; missing ":" and else-branch
    (define tree (parse-hazelnut-string src))
    (printf "--- source ---\n~s\n" src)
    (printf "--- debug tree ---\n~a\n" (green->debug-string tree))
    (printf "--- round-trip ~a ---\n\n"
            (if (equal? (green->source tree) src) "OK" "MISMATCH"))))
