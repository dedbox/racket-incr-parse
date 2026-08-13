#lang racket/base

;; incr-parse/core/operator-grammar.rkt
;;
;; define-operator-grammar - an Agda-flavored declarative layer over
;; core/pratt.rkt. Replaces the old define-pratt entirely (see git history
;; for what it looked like - it was never anything more than a thin,
;; type-unsafe wrapper around hand-building nud/led/bp hashes).
;;
;; A grammar author using this file never writes the words nud, led, or bp,
;; and never builds a hash table by hand. They declare fixity + precedence,
;; Agda-style, with `_` marking operand positions in an operator's own
;; notation:
;;
;;   (infixl 6 (_ '+ _))              ; ordinary left-assoc binary +
;;   (infixr 1 (_ '→ _))              ; right-assoc arrow
;;   (prefix 8 ('- _))                ; unary prefix minus
;;   (postfix 9 (_ '!))               ; postfix factorial
;;   (infixl 10 app (_ _) #:over (Ident Number LParen))  ; juxtaposition
;;   (infixr 1 ternary (_ 'Question _ 'Colon _))          ; mixfix, 3 operands
;;
;; and compound, non-operator forms - anything with its own unique leading
;; keyword, entered only via the nud table, never via precedence climbing -
;; as a `form`, which reads close to the grammar-shape comments every
;; example grammar in this library already writes by hand:
;;
;;   ;; "let" Ident "=" Expr "in" Expr
;;   (form let 'Let 'Ident 'Eq _ 'In _)
;;
;; Every declared sort gets an explicitly-bound parse-<sort> function
;; (parse-expr, parse-type, ...) - no more asymmetry where one sort's entry
;; point is an anonymous lambda buried in a parameterize block and the
;; other one happens to have a name.
;;
;; A sort with an embedded second sort (a lambda's Type annotation) doesn't
;; need its own setup wrapper written by hand either: parse-<sort> always
;; installs its own tables via parameterize before delegating to
;; core/pratt.rkt's parse-expr, so nesting falls out of ordinary dynamic
;; extent automatically, exactly as it already did by hand in the old
;; hazelnut.rkt. That is also why define-operator-grammar's generated
;; `grammar` value never needs a #:setup of its own: #:start is already
;; self-installing.
;;
;; MULTI-SORT OPERANDS - e.g. a JS-style assignment, pattern = expr:
;;
;; `(: sort-name)` slots are not restricted to `form` - they work inside
;; infixl/infixr/infix/prefix/postfix templates too, since compile-slot's
;; `embed` case was always generic; only this comment previously claimed
;; otherwise. So the RIGHT side of any operator CAN be a different sort:
;;
;;   (infixr 1 assign (_ '= (: rhs-sort)))
;;
;; The LEFT side cannot, structurally, not just as a matter of this DSL's
;; scope: by the time a led/infix/postfix entry is even invoked, `left`
;; has ALREADY been parsed by this SAME sort's own nud/led loop - there is
;; no earlier point at which to have chosen a different sort's grammar for
;; it. This isn't a gap to fix; it's what "left" means in precedence
;; climbing. Real hybrid RD/Pratt parsers (JS engines included) handle
;; "pattern on the left of =" the same way: parse the LHS permissively as
;; an ordinary expression (a bare identifier IS a valid expression), then
;; validate-or-reinterpret it as an assignment target afterward - the
;; "cover grammar" technique. That validation is exactly what belongs in
;; the AST elaborator pass, not the CST grammar - matches this project's
;; own no-fail philosophy (the parser stays permissive; a later pass
;; decides what's semantically well-formed) and the standing plan to
;; treat elaboration as its own, later piece of work.
;;
;; STATUS / SCOPE OF THIS DRAFT:
;;   - `#:over` for juxtaposition is explicit, not auto-inferred from the
;;     sort's own nud-table key set. hazelnut.rkt's original hand-written
;;     APPLICABLE-KINDS deliberately excludes `fun`/`let` from bare
;;     application arguments for human readability reasons a fully
;;     automatic inference would have silently overridden. See the `sort`
;;     clause compiler below for exactly what this means for the RD/Pratt
;;     handoff.
;;   - This has NOT been run by me. A first compile attempt elsewhere
;;     already found and fixed two real bugs (see the project's session
;;     history) - treat this as still a working draft.

(require (for-syntax racket/base
                     racket/list
                     racket/syntax
                     syntax/parse)
         syntax/parse/define
         "combinators.rkt"
         "green.rkt"
         "memo.rkt"
         "pratt.rkt"
         "session.rkt")

(provide (all-defined-out))

;;; --------------------------------------------------------------------------
;;; Compile-time: binding-power derivation
;;; --------------------------------------------------------------------------

(begin-for-syntax
  (define (parse-id sort-name) (format-id sort-name "parse-~a" (syntax-e sort-name)))
  (define (nud-id sort-name)   (format-id sort-name "~a-nud-table" (syntax-e sort-name)))
  (define (led-id sort-name)   (format-id sort-name "~a-led-table" (syntax-e sort-name)))
  (define (bp-id sort-name)    (format-id sort-name "~a-bp-table"  (syntax-e sort-name)))

  ;; Agda-style: the AUTHOR writes small, ordinary integers (1, 2, 3, ...),
  ;; tighter-binding operators at higher numbers, with no gaps to leave by
  ;; hand. Scaled by 2 here so every level's associativity-derived neighbor
  ;; (lbp +/- 1) can never collide with an adjacent level's own lbp - the
  ;; same technique the hand-written arith.rkt/hazelnut.rkt tables already
  ;; used, just computed instead of hand-picked.
  (define (level->lbp level-stx) (* 2 (syntax-e level-stx)))

  (define (assoc->rbp lbp assoc)
    (case assoc
      [(left)  (add1 lbp)]   ; rbp > lbp: the same operator won't re-trigger
      [(right) (sub1 lbp)]   ;   while parsing its own right operand -
      [(none)  lbp]))        ;   rbp = lbp: it can't re-trigger AT ALL,
                              ;   i.e. genuinely non-associative.

  ;;; ------------------------------------------------------------------------
  ;;; Compile-time: slot templates
  ;;; ------------------------------------------------------------------------
  ;;
  ;; A slot is a tagged pair:
  ;;   (cons 'hole  #f)        - `_`      : an operand of THIS sort
  ;;   (cons 'lit   kind-stx)  - `'Kind`  : a literal token to consume/expect
  ;;   (cons 'embed sort-stx)  - `(: s)`  : an operand of a DIFFERENT sort s
  ;;                             (form slots only - see the module header)

  (define (parse-slot stx)
    (syntax-parse stx
      #:literals (quote)
      #:datum-literals (:)
      [(~datum _)      (cons 'hole #f)]
      [(quote kind:id) (cons 'lit #'kind)]
      [(: sort:id)     (cons 'embed #'sort)]
      [_ (raise-syntax-error 'define-operator-grammar
                             "expected _, 'Kind, or (: sort-name)" stx)]))

  (define (parse-template stx) (map parse-slot (syntax->list stx)))

  ;; Compiles ONE already-classified slot into a let*-values clause
  ;; [(val-id toks-id) (...)], threading toks-prev -> toks-id.
  ;;   first?  - this is the slot immediately after the dispatch position
  ;;             (the leading `_` for infix, or the leading literal for
  ;;             prefix/form) - its presence is guaranteed by table
  ;;             dispatch, so it's consumed via consume-as, never expect.
  ;;   own-bp  - the bp a `_` slot should parse its sub-expression at.
  (define (compile-slot slot sort-name toks-prev first? own-bp)
    (define val-id (generate-temporary 'v))
    (define toks-id (generate-temporary 'toks))
    (define clause
      (case (car slot)
        [(lit)
         (define kind (cdr slot))
         (if first?
             #`[(#,val-id #,toks-id) (consume-as '#,kind #,toks-prev)]
             #`[(#,val-id #,toks-id) ((expect '#,kind) #,toks-prev)])]
        [(hole)
         #`[(#,val-id #,toks-id) (#,(parse-id sort-name) #,toks-prev #,own-bp)]]
        [(embed)
         #`[(#,val-id #,toks-id) (#,(parse-id (cdr slot)) #,toks-prev 0)]]))
    (values val-id toks-id clause))

  ;; Compiles a whole slot list into: the ordered list of value-ids, the
  ;; ordered list of let*-values clauses (toks threaded through, starting
  ;; from toks0), and the final toks-id. Every interior `_` parses at bp 0
  ;; (it's bracketed by neighboring literal tokens, same as a parenthesized
  ;; sub-expression); only the LAST slot, if it's `_`, uses the caller's
  ;; own associativity-derived bp - this one rule is what makes a simple
  ;; 2-slot infix, a juxtaposition, AND a multi-part mixfix like ternary
  ;; all fall out of the exact same walk.
  (define (compile-slots slots sort-name toks0 trailing-bp)
    (let loop ([slots slots] [toks-prev toks0] [i 0] [vals '()] [clauses '()])
      (cond
        [(null? slots) (values (reverse vals) (reverse clauses) toks-prev)]
        [else
         (define last? (null? (cdr slots)))
         (define-values (val-id toks-id clause)
           (compile-slot (car slots) sort-name toks-prev (zero? i)
                         (if last? trailing-bp 0)))
         (loop (cdr slots) toks-id (add1 i) (cons val-id vals) (cons clause clauses))])))

  ;;; ------------------------------------------------------------------------
  ;;; Compile-time: one declaration -> table contributions
  ;;; ------------------------------------------------------------------------
  ;;
  ;; Returns (values nud-pairs led-pairs bp-pairs), each a plain
  ;; (listof (cons kind-stx expr-stx)). A single declaration can contribute
  ;; to more than one table slot at once (e.g. juxtaposition contributes one
  ;; led/bp pair PER kind in its #:over list, all pointing at the same
  ;; compiled closure).

  (define (compile-sort-clause clause sort-name)
    (syntax-parse clause
      #:datum-literals (atom form infixl infixr infix prefix postfix)
      ;; ---- atom: a leaf, wrapped uniformly as grammar-level 'atom -------
      [(atom kind:id ...)
       (values (for/list ([k (in-list (attribute kind))])
                 (cons k #'(λ (toks) (consume-as 'atom toks))))
               '() '())]

      ;; ---- form: a standalone, non-operator, leading-token production --
      [(form name:id slot ...)
       #:do [(define slots (parse-template #'(slot ...)))]
       #:fail-when (null? slots) "form needs at least one slot"
       #:fail-when (not (eq? (car (car slots)) 'lit))
       "a form must begin with a literal token ('Kind), so it has a leading token to dispatch on"
       #:do [(define dispatch-kind (cdr (car slots)))
             (define toks0 (generate-temporary 'toks))
             (define-values (vals clauses final-toks)
               (compile-slots slots sort-name toks0 0))]
       (values (list (cons dispatch-kind
                           #`(λ (#,toks0)
                               (let*-values (#,@clauses)
                                 (values (intern-branch! '#,#'name (list #,@vals)) #,final-toks)))))
               '() '())]

      ;; ---- infixl / infixr / infix: operand _ TOK-or-_ ... -------------
      [((~and head (~or infixl infixr infix)) level:nat
        (~optional name:id) (slot ...)
        (~optional (~seq #:over (over-kind:id ...))))
       #:do [(define assoc (case (syntax-e #'head) [(infixl) 'left] [(infixr) 'right] [(infix) 'none]))
             (define lbp (level->lbp #'level))
             (define rbp (assoc->rbp lbp assoc))
             (define slots (parse-template #'(slot ...)))]
       #:fail-when (or (null? slots) (not (eq? (car (car slots)) 'hole)))
       "an infixl/infixr/infix template must begin with _ (the already-parsed left operand)"
       #:do [(define rest-slots (cdr slots))
             (define juxtaposition? (and (pair? rest-slots) (eq? (caar rest-slots) 'hole)))
             (define kind-name (cond [(attribute name) #`(quote #,(attribute name))]
                                     [juxtaposition? #''app]
                                     [else #''binop]))
             (define left-id (generate-temporary 'left))
             (define toks0 (generate-temporary 'toks))
             (define-values (vals clauses final-toks)
               (compile-slots rest-slots sort-name toks0 rbp))
             (define fn-stx
               #`(λ (#,left-id #,toks0)
                   (let*-values (#,@clauses)
                     (values (intern-branch! #,kind-name (list #,left-id #,@vals)) #,final-toks))))]
       (cond
         [juxtaposition?
          (unless (attribute over-kind)
            (raise-syntax-error 'define-operator-grammar
                                "juxtaposition (_ _) needs #:over (Kind ...) - which token kinds may start a bare application argument"
                                clause))
          (values '()
                  (for/list ([k (in-list (attribute over-kind))]) (cons k fn-stx))
                  (for/list ([k (in-list (attribute over-kind))]) (cons k #`(cons #,lbp #,rbp))))]
         [else
          (define dispatch-kind (cdr (car rest-slots)))
          (values '()
                  (list (cons dispatch-kind fn-stx))
                  (list (cons dispatch-kind #`(cons #,lbp #,rbp))))])]

      ;; ---- prefix: TOK operand-or-more, no left operand -----------------
      [(prefix level:nat (~optional name:id) (slot ...))
       #:do [(define lbp (level->lbp #'level))
             (define slots (parse-template #'(slot ...)))]
       #:fail-when (or (null? slots) (not (eq? (car (car slots)) 'lit)))
       "a prefix template must begin with a literal dispatch token ('Kind)"
       #:do [(define dispatch-kind (cdr (car slots)))
             (define kind-name (if (attribute name) #`(quote #,(attribute name)) #''unop))
             (define toks0 (generate-temporary 'toks))
             (define-values (vals clauses final-toks)
               (compile-slots slots sort-name toks0 lbp))]
       (values (list (cons dispatch-kind
                           #`(λ (#,toks0)
                               (let*-values (#,@clauses)
                                 (values (intern-branch! #,kind-name (list #,@vals)) #,final-toks)))))
               '() '())]

      ;; ---- postfix: operand TOK-or-more, nothing parsed afterward -------
      [(postfix level:nat (~optional name:id) (slot ...))
       #:do [(define lbp (level->lbp #'level))
             (define slots (parse-template #'(slot ...)))]
       #:fail-when (or (null? slots) (not (eq? (car (car slots)) 'hole)))
       "a postfix template must begin with _ (the already-parsed left operand)"
       #:do [(define rest-slots (cdr slots))]
       #:fail-when (or (null? rest-slots) (not (eq? (car (car rest-slots)) 'lit)))
       "a postfix template needs at least one literal dispatch token ('Kind) after the leading _"
       #:fail-when (ormap (λ (s) (eq? (car s) 'hole)) rest-slots)
       "a postfix template's slots after the leading _ must all be literal tokens - if another operand follows, this is an infixl/infixr/infix shape instead"
       #:do [(define dispatch-kind (cdr (car rest-slots)))
             (define kind-name (if (attribute name) #`(quote #,(attribute name)) #''unop))
             (define left-id (generate-temporary 'left))
             (define toks0 (generate-temporary 'toks))
             ;; No slot here is ever a `_`, so the trailing-bp argument is
             ;; never actually read - passed as lbp only so the (lbp . rbp)
             ;; pair's rbp still has a defined, harmless value.
             (define-values (vals clauses final-toks)
               (compile-slots rest-slots sort-name toks0 lbp))]
       (values '()
               (list (cons dispatch-kind
                          #`(λ (#,left-id #,toks0)
                              (let*-values (#,@clauses)
                                (values (intern-branch! #,kind-name (list #,left-id #,@vals)) #,final-toks)))))
               (list (cons dispatch-kind #`(cons #,lbp #,lbp))))]))

  ;;; ------------------------------------------------------------------------
  ;;; Compile-time: one whole sort -> its three tables + parse-<sort>
  ;;; ------------------------------------------------------------------------

  ;; Errors at macro-expansion time - before the generated code even runs -
  ;; if the same kind was registered twice into the same table by this
  ;; sort's own declarations. The same protection register-elaborator!
  ;; (core/elaborate.rkt) enforces at runtime for a different registry;
  ;; this is its compile-time counterpart, catching e.g. two `infixl`
  ;; declarations that accidentally reuse the same operator token, or an
  ;; `atom` and a `form` both claiming the same leading kind.
  (define (check-no-duplicates! pairs table-name sort-name)
    (define dupe (check-duplicates pairs free-identifier=?))
    (when dupe
      (raise-syntax-error 'define-operator-grammar
                          (format "duplicate ~a entry for kind ~a in sort ~a"
                                  table-name (syntax-e dupe) (syntax-e sort-name))
                          dupe)))

  (define (compile-sort sort-stx)
    (syntax-parse sort-stx
      #:datum-literals (sort)
      [(sort name:id clause ...)
       #:with (((nud-key . nud-val) ...)
               ((led-key . led-val) ...)
               ((bp-key  . bp-val)  ...))
       (for/fold ([nud null] [led null] [bp null] #:result (list nud led bp))
                 ([c (in-list (attribute clause))])
         (define-values (n l b) (compile-sort-clause c #'name))
         (values (append nud n) (append led l) (append bp b)))
       #:do [(check-no-duplicates! (attribute nud-key) "nud" #'name)
             (check-no-duplicates! (attribute led-key) "led" #'name)
             (check-no-duplicates! (attribute bp-key)  "bp"  #'name)]
       #:with nud-tbl-id (nud-id #'name)
       #:with led-tbl-id (led-id #'name)
       #:with bp-tbl-id  (bp-id  #'name)
       #:with pid        (parse-id #'name)
       #'(begin
           (define nud-tbl-id (hash (~@ 'nud-key nud-val) ...))
           (define led-tbl-id (hash (~@ 'led-key led-val) ...))
           (define bp-tbl-id  (hash (~@ 'bp-key  bp-val)  ...))
           ;; Explicitly bound, every sort, no exceptions - this is what
           ;; makes a Type-embedded-in-Expr grammar's Type entry point just
           ;; as discoverable as its Expr one. Calls core/pratt.rkt's own
           ;; shared parse-expr - the ONE climbing engine every sort
           ;; installs its own tables around - never a sort-specific
           ;; function of the same name (that would just be this
           ;; definition calling itself, forever).
           (define (pid toks min-bp)
             (parameterize ([current-nud-table nud-tbl-id]
                            [current-led-table led-tbl-id]
                            [current-bp-table  bp-tbl-id]
                            [current-expr-rule-id 'name])
               (parse-expr toks min-bp))))])))

;;; --------------------------------------------------------------------------
;;; The public macro
;;; --------------------------------------------------------------------------

;; (define-operator-grammar NAME
;;   #:lexer lexer-fn #:apply-edit apply-edit-fn
;;   #:entry entry-sort-name
;;   (sort SORT-NAME clause ...) ...)
;;
;; Expands to: every sort's nud/led/bp tables and its own parse-<sort>
;; function, PLUS a ready-to-install NAME-grammar value (see
;; core/session.rkt's `make-grammar`) whose #:start is entry-sort's own
;; parse-<entry-sort> - no separate #:setup needed, since parse-<entry-sort>
;; already installs its own tables on every call.
(define-simple-macro (define-operator-grammar name:id
                       #:lexer lexer:expr #:apply-edit apply-edit:expr
                       #:entry entry-sort:id
                       (~optional (~seq #:ropeable ropeable:expr))
                       sort-clause ...)
  #:with (sort-def ...) (for/list ([sc (in-list (attribute sort-clause))])
                          (compile-sort sc))
  #:with entry-pid (parse-id #'entry-sort)
  #:with grammar-id (format-id #'name "~a-grammar" (syntax-e #'name))
  (begin
    sort-def ...
    (define grammar-id
      (make-grammar #:lexer lexer
                    #:apply-edit apply-edit
                    #:start (λ (toks) (entry-pid toks 0))
                    (~? (~@ #:ropeable ropeable))))))

(module+ test
  (require (prefix-in lex: incr-lex)
           rackunit
           rope
           "hole-ghost.rkt"
           "token-stream.rkt")

  ;; Synthetic tokens, decoupled from any real lexer - same isolation
  ;; approach as combinators.rkt/pratt.rkt's own tests.
  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))
  (define (toks . pairs)
    (tokens->stream
     (let loop ([ps pairs])
       (if (null? ps) (list (mk-tok 'incr-lex:eof ""))
           (cons (mk-tok (car ps) (cadr ps)) (loop (cddr ps)))))))

  ;; A slice of arith.rkt's own shape, plus a right-assoc Caret neither
  ;; example grammar exercises, specifically to check infixr's derived bp
  ;; against infixl's, by hand-verifiable example (not just by inspection).
  (define-operator-grammar ar
    #:lexer (λ (x) x) #:apply-edit (λ (x . _) x) ; unused by these tests
    #:entry expr
    (sort expr
      (atom Number)
      (infixl 1 (_ 'Plus _))
      (infixl 2 (_ 'Star _))
      (infixr 3 (_ 'Caret _))
      (form paren 'LParen _ 'RParen)))

  (test-case "infixl: left-associativity, 1+2+3 groups as (1+2)+3"
    (define-values (tree _r)
      (parse-expr (toks 'Number "1" 'Plus "+" 'Number "2" 'Plus "+" 'Number "3") 0))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'binop)
    (check-eq? (green-tree-kind r) 'atom))

  (test-case "infixl vs infixl: precedence, 1+2*3 groups as 1+(2*3)"
    (define-values (tree _r)
      (parse-expr (toks 'Number "1" 'Plus "+" 'Number "2" 'Star "*" 'Number "3") 0))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'atom)
    (check-eq? (green-tree-kind r) 'binop))

  (test-case "infixr: right-associativity, 2^3^4 groups as 2^(3^4)"
    (define-values (tree _r)
      (parse-expr (toks 'Number "2" 'Caret "^" 'Number "3" 'Caret "^" 'Number "4") 0))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'atom)
    (check-eq? (green-tree-kind r) 'binop))

  (test-case "form: paren consumes both delimiters, missing close still recovers as a ghost"
    (define-values (t1 _r1)
      (parse-expr (toks 'LParen "(" 'Number "1" 'Plus "+" 'Number "2" 'RParen ")") 0))
    (check-eq? (green-tree-kind t1) 'paren)
    (define-values (open mid close) (apply values (green-branch-children t1)))
    (check-eq? (lex:token-kind (green-token-token open)) 'LParen)
    (check-eq? (green-tree-kind mid) 'binop)
    (define-values (t2 _r2) (parse-expr (toks 'LParen "(" 'Number "1") 0))
    (define last-child (caddr (green-branch-children t2)))
    (check-true (ghost? last-child))
    (check-eq? (ghost-of last-child) 'RParen))

  ;; Juxtaposition + a mixfix ternary in one grammar, mirroring
  ;; hazelnut.rkt's own (harder) shape, at a scale small enough to hand-
  ;; verify: application binds tighter than +, ternary is right-assoc and
  ;; looser than everything.
  ;;
  ;; Sort named `mx`, not `expr` - a real grammar only ever declares one
  ;; sort called `expr` per FILE (each example grammar lives in its own
  ;; module), but this test file deliberately holds two independent
  ;; operator grammars (`ar` above, `mx` here) side by side, and every
  ;; sort's generated bindings (parse-<sort>, <sort>-nud-table, ...) are
  ;; named from the sort alone, not grammar-qualified - two sorts sharing
  ;; a name in ONE module collide as a plain Racket "already defined"
  ;; error, exactly like any other duplicate top-level define. Real
  ;; grammars won't hit this; this test file avoids it by choosing
  ;; distinct sort names, the same way any two same-file grammars must.
  (define-operator-grammar mix
    #:lexer (λ (x) x) #:apply-edit (λ (x . _) x)
    #:entry mx
    (sort mx
      (atom Ident)
      (infixr 1 ternary (_ 'Question _ 'Colon _))
      (infixl 2 (_ 'Plus _))
      (infixl 3 (_ _) #:over (Ident))))

  (test-case "juxtaposition: application binds tighter than +, f x + 1 is (f x) + 1"
    (define-values (tree _r)
      (parse-mx (toks 'Ident "f" 'Ident "x" 'Plus "+" 'Ident "1") 0))
    (check-eq? (green-tree-kind tree) 'binop)
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'app)
    (check-eq? (green-tree-kind r) 'atom))

  (test-case "ternary: mixfix with two literal delimiters, right-associative"
    (define-values (tree _r)
      (parse-mx (toks 'Ident "a" 'Question "?" 'Ident "b" 'Colon ":"
                      'Ident "c" 'Question "?" 'Ident "d" 'Colon ":" 'Ident "e")
                0))
    (check-eq? (green-tree-kind tree) 'ternary)
    (define-values (test q then c else) (apply values (green-branch-children tree)))
    (check-eq? (lex:token-kind (green-token-token q)) 'Question)
    (check-eq? (lex:token-kind (green-token-token c)) 'Colon)
    (check-eq? (green-tree-kind then) 'atom)
    (check-eq? (green-tree-kind else) 'ternary))

  (test-case "ternary: missing Colon recovers as a ghost, not a crash"
    (define-values (tree _r)
      (parse-mx (toks 'Ident "a" 'Question "?" 'Ident "b") 0))
    (check-eq? (green-tree-kind tree) 'ternary)
    (define c (list-ref (green-branch-children tree) 3))
    (check-true (ghost? c))
    (check-eq? (ghost-of c) 'Colon))

  ;; postfix, and cross-sort embedding on an operator's RIGHT side (not
  ;; just inside a form) - a JS-style assignment shape, pattern = expr,
  ;; where `rhs` is deliberately a DIFFERENT sort from `expr` itself, to
  ;; prove this isn't just "the same sort, spelled differently."
  (define-operator-grammar multisort
    #:lexer (λ (x) x) #:apply-edit (λ (x . _) x)
    #:entry ms-expr
    (sort ms-expr
      (atom Ident Number)
      (postfix 5 (_ '!))
      (infixr 1 assign (_ '= (: rhs))))
    (sort rhs
      (atom Number)
      (infixl 2 (_ 'Plus _))))

  (test-case "postfix: consumes the trailing token, no further operand parsed"
    (define-values (tree rest)
      (parse-ms-expr (toks 'Number "5" 'Bang "!") 0))
    (check-eq? (green-tree-kind tree) 'unop)
    (define-values (n bang) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind n) 'atom)
    (check-eq? (lex:token-kind (green-token-token bang)) 'Bang)
    (check-eq? (peek-kind rest) 'incr-lex:eof))

  (test-case "cross-sort embedding on an operator's right side: RHS parses via a DIFFERENT sort's own table"
    (define-values (tree _r)
      (parse-ms-expr (toks 'Ident "x" 'Eq "=" 'Number "1" 'Plus "+" 'Number "2") 0))
    (check-eq? (green-tree-kind tree) 'assign)
    (define-values (lhs eq rhs) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind lhs) 'atom)
    ;; rhs parsed via parse-rhs's OWN table (infixl + on rhs, not ms-expr) -
    ;; if this were still ms-expr's table, 1+2 wouldn't parse as binop at
    ;; all (ms-expr has no infix + declared in this fixture).
    (check-eq? (green-tree-kind rhs) 'binop)))
 
