#lang racket/base

;; incr-parse/private/grammar.rkt
;;
;; A syntax/parse-based grammar meta-language, compiling directly to the
;; private/combinators.rkt and private/pratt.rkt API.
;;
;; define-grammar covers RD productions: case-dispatch on a leading token,
;; seq, rep, leaf tokens, and the hole/ghost recovery vocabulary. Every rule
;; it compiles is wrapped in memoize.
;;
;; define-pratt covers Pratt tables: atom, prefix, paren, and infix/infixr
;; operator entries.
;;
;; Lexer definitions, session plumbing, and string entry points must be
;; defined separately for each language. This file only ever produces parse-*
;; bindings and Pratt tables.

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
  ;; argument to seq/rep, or applied to toks at a case-clause site.
  ;;
  ;;   (call name)                 -> parse-name
  ;;   (token kind)                -> (expect 'kind)
  ;;   (leaf kind)                 -> a leaf consumer of that grammar kind
  ;;   (hole msg)                  -> hole-for-unexpected, wrapped
  ;;   (seq part ...)              -> a branch under the enclosing rule's name
  ;;   (rep binding elem #:until (kind ...)) -> a rep, stopping at those
  ;;                                   kinds or eof-kind
  (define (compile-prod stx eof-kind enclosing-name)
    (syntax-parse stx
      #:datum-literals (call leaf hole token seq rep)
      [(call name:id)
       (parse-id #'name)]
      [(token kind:id)
       (syntax/loc stx (expect 'kind))]
      [(leaf kind:id)
       (syntax/loc stx (λ (toks) (consume-as 'kind toks)))]
      [(hole msg:str)
       (syntax/loc stx (λ (toks) (hole-for-unexpected msg toks)))]
      [(seq part ...)
       #:with (part-i ...) (for/list ([p (in-list (attribute part))])
                             (compile-prod p eof-kind enclosing-name))
       (quasisyntax/loc stx (seq '#,enclosing-name part-i ...))]
      [(rep binding:id elem #:until (until-kind:id ...))
       #:with elem-prod (compile-prod #'elem eof-kind enclosing-name)
       (quasisyntax/loc stx
         (rep 'binding elem-prod
              (λ (k) (case k [(until-kind ... #,eof-kind) #t] [else #f]))))]))

  ;; A rule is either a case-dispatch over the leading token's kind, or a
  ;; single prod standing in for the whole rule body (list and program in
  ;; sexpr.rkt are both this shape).
  (define (compile-rule stx eof-kind)
    (syntax-parse stx
      #:datum-literals (rule)
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
;;; define-pratt
;;; --------------------------------------------------------------------------

;; #:atom kinds all consume as a single 'atom leaf, matching how
;; langs/arith.rkt treats Number and Ident uniformly. #:infix entries get
;; right-bp = left-bp + 1 (left-associative); #:infixr entries get right-bp =
;; left-bp - 1 (right-associative), the minimum change needed to let the same
;; operator recur while parsing its own right operand, under this parser's
;; strict left-bp > min-bp loop condition.
(define-simple-macro (define-pratt name:id
                       (~optional (~seq #:atom   (atom-kind:id ...)))
                       (~optional (~seq #:prefix ([pfx-kind:id pfx-bp] ...)))
                       (~optional (~seq #:paren  ([open:id close:id] ...)))
                       (~optional (~seq #:infix  ([inf-kind:id inf-lbp] ...)))
                       (~optional (~seq #:infixr ([infr-kind:id infr-lbp] ...))))
  #:with bp-id  (format-id #'name "~a-bp-table"  (syntax-e #'name))
  #:with nud-id (format-id #'name "~a-nud-table" (syntax-e #'name))
  #:with led-id (format-id #'name "~a-led-table" (syntax-e #'name))
  #:do [(define (bp-entries kinds lbps rbp-of)
          (append* (for/list ([k (in-list kinds)] [l (in-list lbps)])
                     (list (quasisyntax/loc #'k '#,k)
                           (quasisyntax/loc #'l (cons #,l #,(rbp-of l)))))))]
  #:with (inf-bp-entry ...)  (bp-entries (attribute inf-kind) (attribute inf-lbp)
                                         (λ (l) #`(add1 #,l)))
  #:with (infr-bp-entry ...) (bp-entries (attribute infr-kind) (attribute infr-lbp)
                                         (λ (l) #`(sub1 #,l)))
  #:with (consume-entry ...) (append*
                              (for/list ([k (in-list (attribute atom-kind))])
                                (list (quasisyntax/loc k '#,k)
                                      (quasisyntax/loc k
                                        (λ (toks) (consume-as 'atom toks))))))
  #:with (prefix-entry ...)  (append*
                              (for/list ([k (in-list (attribute pfx-kind))]
                                         [b (in-list (attribute pfx-bp))])
                                (list (quasisyntax/loc k '#,k)
                                      (quasisyntax/loc k (nud-prefix '#,k #,b)))))
  #:with (paren-entry ...)   (append*
                              (for/list ([o (in-list (attribute open))]
                                         [c (in-list (attribute close))])
                                (list (quasisyntax/loc o '#,o)
                                      (quasisyntax/loc o (nud-paren '#,o '#,c)))))
  #:with (infix-entry ...)   (append*
                              (for/list ([k (in-list (append (attribute inf-kind)
                                                             (attribute infr-kind)))])
                                (list (quasisyntax/loc k '#,k)
                                      (quasisyntax/loc k (led-infix '#,k)))))
  (begin
    (define bp-id  (hash inf-bp-entry ... infr-bp-entry ...))
    (define nud-id (hash consume-entry ... prefix-entry ... paren-entry ...))
    (define led-id (hash infix-entry ...))))

;;; --------------------------------------------------------------------------
;;; Tests
;;; --------------------------------------------------------------------------

(module+ test
  (require (prefix-in lex: incr-lex)
           rackunit
           racket/list
           rope
           "green.rkt"
           "hole-ghost.rkt")

  ;; Hand-built tokens, bypassing a real lexer.
  (define (mk-tok kind str)
    (lex:token kind (string-length str) (string->rope str) null null null))
  (define (toks . pairs)
    (let loop ([ps pairs])
      (if (null? ps) (list (mk-tok 'incr-lex:eof ""))
          (cons (mk-tok (car ps) (cadr ps)) (loop (cddr ps))))))

  ;; Reimplements langs/sexpr.rkt's grammar, to check the expansion has
  ;; the same shape as that hand-written file.
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
    (rule program
          (rep sexprs (call sexpr) #:until ())))

  (test-case "define-grammar: well-formed input produces the expected shape"
    (define-values (tree rest)
      (parse-program (toks 'LParen "(" 'Symbol "foo" 'Number "1" 'RParen ")")))
    (check-eq? (peek-kind rest) 'incr-lex:eof)
    (check-eq? (green-tree-kind tree) 'program)
    (define top (car (green-branch-children tree)))
    (check-eq? (green-tree-kind top) 'list)
    (define elements (cadr (green-branch-children top)))
    (check-equal? (length (green-branch-children elements)) 2))

  (test-case "define-grammar: stray RParen produces a staged hole"
    (define-values (tree rest) (parse-program (toks 'RParen ")")))
    (define first (car (green-branch-children tree)))
    (check-true (hole? first))
    (check-eq? (hole-status first) 'staged))

  (test-case "define-grammar: unterminated list produces a ghost RParen"
    (define-values (tree rest) (parse-program (toks 'LParen "(" 'Symbol "x")))
    (define lst (car (green-branch-children tree)))
    (define last-child (last (green-branch-children lst)))
    (check-true (ghost? last-child))
    (check-eq? (ghost-of last-child) 'RParen))

  ;; A slice of langs/arith.rkt, plus a right-assoc operator neither toy
  ;; grammar exercises, to check #:infixr's bp encoding directly.
  (define-pratt ar-grammar
    #:atom   [Number Ident]
    #:prefix [[Minus 5]]
    #:paren  [[LParen RParen]]
    #:infix  [[Plus 1] [Minus 1] [Star 3] [Slash 3]]
    #:infixr [[Caret 7]])

  (define (parse-ar t)
    (parameterize ([current-nud-table ar-grammar-nud-table]
                   [current-led-table ar-grammar-led-table]
                   [current-bp-table  ar-grammar-bp-table])
      (parse-expr t 0)))

  (test-case "define-pratt: left-assoc precedence matches arith.rkt's own tables"
    (define-values (tree rest)
      (parse-ar (toks 'Number "1" 'Plus "+" 'Number "2" 'Star "*" 'Number "3")))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'atom)
    (check-eq? (green-tree-kind r) 'binop))

  (test-case "define-pratt: #:infixr right-associates, 2^3^4 groups as 2^(3^4)"
    (define-values (tree rest)
      (parse-ar (toks 'Number "2" 'Caret "^" 'Number "3" 'Caret "^" 'Number "4")))
    (define-values (l op r) (apply values (green-branch-children tree)))
    (check-eq? (green-tree-kind l) 'atom)
    (check-eq? (green-tree-kind r) 'binop)))
