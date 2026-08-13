#lang racket/base

;; incr-parse/examples/hazelnut.rkt
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
;; Two sorts, one Pratt engine, declared as one define-operator-grammar
;; below - what used to be ~90 lines of hand-built nud/led/bp hashes (see
;; git history) is now a couple of `sort` blocks reading close to the
;; grammar comment above. Neither sort's table-installation is written by
;; hand either: parse-expr/parse-type are both generated, and each
;; installs its own tables via parameterize before delegating to
;; core/pratt.rkt's shared climbing engine - a lambda's Type annotation
;; nests correctly by ordinary dynamic extent, no manual save/restore.
;;
;; Every nud/led entry here still ultimately compiles to ordinary
;; seq/expect/consume-as, so recovery uses the same ghost/hole machinery
;; as everywhere else in this project. A missing "." after a lambda's type
;; annotation, a missing "in" in a let, and a missing ":" in a ternary all
;; recover as a ghost with no crash.

(require (prefix-in : incr-lex)
         "../grammar.rkt"
         "../main.rkt")

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
;;; Grammar
;;; --------------------------------------------------------------------------
;;
;; bp levels only need to preserve relative looseness/tightness within each
;; sort - loosest to tightest in Expr: ternary(1) < comparison(2) <
;; additive(3) < multiplicative(4) < application(5). Comparison is
;; deliberately `infixl`, not the genuinely-non-associative `infix` - a < b
;; < c parses as (a < b) < c, matching this grammar's original hand-picked
;; bp values (CMP-RBP = CMP-LBP + 1) exactly; unusual for comparison
;; operators in most languages, but that's what this grammar already did,
;; and porting it should not silently change behavior.
;;
;; fun/let read close to their own BNF-comment shape (λ Ident : Type .
;; Expr / let Ident = Expr in Expr) as `form`s - `(: type)` is what makes
;; a lambda's annotation a genuine Type-sort parse, not another Expr.
;; Juxtaposition (app) deliberately excludes Fun/Let from #:over, exactly
;; like the original hand-written APPLICABLE-KINDS did: an unparenthesized
;; fun/let as a bare application argument reads as ambiguous to a human
;; even though it wouldn't be to this parser, so it's required to be
;; parenthesized instead, same as most real languages.

(define-operator-grammar hazelnut
  #:lexer hazelnut-lex #:apply-edit hazelnut-apply-edit
  #:entry expr
  (sort expr
    (atom [Ident 'var] [Number 'num] [True 'bool] [False 'bool])
    (form fun 'Fun 'Ident 'Colon (: type) 'Dot _)
    (form let 'Let 'Ident 'Eq _ 'In _)
    (form paren 'LParen _ 'RParen)
    (infixl 3 (_ 'Plus _))
    (infixl 3 (_ 'Minus _))
    (infixl 4 (_ 'Star _))
    (infixl 4 (_ 'Slash _))
    (infixl 2 (_ 'Lt _))
    (infixl 2 (_ 'EqEq _))
    (infixr 1 ternary (_ 'Question _ 'Colon _))
    (infixl 5 (_ _) #:over (Ident Number True False LParen)))
  (sort type
    (atom [NumT 'base] [BoolT 'base])
    (infixr 1 arrow-type (_ 'Arrow _))
    (form paren 'LParen _ 'RParen)))

;;; --------------------------------------------------------------------------
;;; AST
;;; --------------------------------------------------------------------------
;;
;; This grammar never requires arith.rkt/sexpr.rkt/toplevel.rkt, so it
;; can't rely on any of THEIR elaborator registrations either -
;; elaborate.rkt's registry is one shared table keyed by symbol, populated
;; only by whichever grammar modules happen to have been loaded into the
;; same process, and that's not something this file's own correctness
;; should depend on. Every kind this grammar actually produces gets its
;; own registration here, even 'paren and 'binop, which arith.rkt also
;; happens to use for the exact same shape.
;;
;; var/num/bool/base need no elaborator registration at all - they're
;; leaves (consume-as, not a branch), so elaborate.rkt's built-in
;; green-token case already covers them, reading the underlying LEXER
;; kind (NumT/BoolT/Number/...), not this grammar's own CST-level tag.

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

;;; --------------------------------------------------------------------------
;;; Entry Point
;;; --------------------------------------------------------------------------

;; A one-shot "give me a tree from a string" convenience - runtime usage
;; (creates a document, parses it), so it reaches for ../main.rkt rather
;; than growing ../grammar.rkt a runtime concept, same as arith.rkt/sexpr.rkt.
(define (parse-hazelnut-string str)
  (document-tree (document-parse! (make-document hazelnut-grammar str))))

(define (elaborate-hazelnut-string str)
  (elaborate (parse-hazelnut-string str)))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require racket/list
           rackunit
           rope)

  (define (check-round-trip src)
    (check-equal? (green->source (parse-hazelnut-string src)) src))

  (test-case "round-trip: a lambda with an arrow-typed parameter"
    (check-round-trip "λf:ℕ→ℕ.λx:ℕ.f (f x)"))

  (test-case "round-trip: let, ternary, arithmetic, application together"
    (check-round-trip "let double = λx:ℕ.x * 2 in double (double 3) < 100 ? 𝕥 : 𝕗"))

  (test-case "round-trip: recovery cases"
    (check-round-trip "λx:ℕ x")               ; missing "." -> ghost
    (check-round-trip "let x = 1 x + 1")      ; missing "in" -> ghost (round-trip
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
    ;; elaborate.rkt's shared, symbol-keyed elaborator registry.
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
    (define sess (make-session))
    (session-install-grammar! sess 'hazelnut hazelnut-grammar)
    (session-open! sess 'hazelnut "doc-1" src)
    (define tree1 (document-tree (session-document sess "doc-1")))
    ;; offset 11 is the "1" inside "x + 1" - replace it with "11"
    (define doc2 (session-edit! sess "doc-1" 11 1 "11"))
    (define tree2 (document-tree doc2))
    (check-equal? (green->source tree2) "λx:ℕ.((x + 11) * (x + 2)) + x")
    (define (find-plus-2 t)
      (cond [(and (green-branch? t) (eq? (green-tree-kind t) 'binop)
                  (let ([r (caddr (green-branch-children t))])
                    (and (eq? (green-tree-kind r) 'num)
                         (equal? (rope->string (:token-payload (green-token-token r))) "2"))))
             t]
            [(green-branch? t) (ormap find-plus-2 (green-branch-children t))]
            [else #f]))
    (define p1 (find-plus-2 tree1))
    (define p2 (find-plus-2 tree2))
    (check-not-false p1)
    (check-eq? p1 p2)
    (session-close! sess "doc-1")))

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
