#lang racket

(require racket/sandbox)
(require "solver.rkt")

(provide (all-defined-out))

(struct type-decl (name) #:transparent)
(struct immrel-decl (name sorts) #:transparent)
(struct mutrel-decl (name sorts) #:transparent)
(struct immconst-decl (name sort) #:transparent)
(struct mutconst-decl (name sort) #:transparent)
(struct immfun-decl (name sorts sort) #:transparent)
(struct mutfun-decl (name sorts sort) #:transparent)
(struct axiom-decl (name formula) #:transparent)
(struct init-decl (name formula) #:transparent)
(struct transition-decl (name formula) #:transparent)
(struct invariant-decl (name formula) #:transparent)
(struct corollary-decl (name formula) #:transparent)

(struct labeled-formula (name formula) #:transparent)

(define decl-name
  (match-lambda
    [(type-decl t) t]
    [(immrel-decl R _) R]
    [(mutrel-decl R _) R]
    [(immconst-decl C _) C]
    [(mutconst-decl C _) C]
    [(immfun-decl F _ _) F]
    [(mutfun-decl F _ _) F]

    ; the ones below here are kinda bogus
    [(axiom-decl name _) name]
    [(init-decl name _) name]
    [(transition-decl name _) name]
    [(invariant-decl name _) name]
    [(corollary-decl name _) name]))


(define-syntax-rule (type t) (type-decl 't))
(define-syntax-rule (immutable-relation R (args ...)) (immrel-decl 'R '(args ...)))
(define-syntax-rule (mutable-relation R (args ...)) (mutrel-decl 'R '(args ...)))
(define-syntax-rule (immutable-constant C t) (immconst-decl 'C 't))
(define-syntax-rule (mutable-constant C t) (mutconst-decl 'C 't))
(define-syntax-rule (immutable-function F (args ...) t)
  (begin
    (when (null? '(args ...))
      (error "functions must take at least one argument; consider using a constant instead"))
    (immfun-decl 'F '(args ...)'t)))
(define-syntax-rule (mutable-function F (args ...) t)
  (begin
    (when (null? '(args ...))
      (error "functions must take at least one argument; consider using a constant instead"))
    (mutfun-decl 'F '(args ...) 't)))

(define-syntax axiom
  (syntax-rules ()
    [(axiom f) (axiom-decl (symbol-append 'anonymous- (gensym)) 'f)]
    [(axiom name f) (axiom-decl 'name 'f)]))
(define-syntax init
  (syntax-rules ()
    [(init f) (init-decl (symbol-append 'anonymous- (gensym)) 'f)]
    [(init name f) (init-decl 'name 'f)]))
(define-syntax transition
  (syntax-rules ()
    [(transition f) (transition-decl (symbol-append 'anonymous- (gensym)) 'f)]
    [(transition name f) (transition-decl 'name 'f)]))
(define-syntax invariant
  (syntax-rules ()
    [(invariant f) (invariant-decl (symbol-append 'anonymous- (gensym)) 'f)]
    [(invariant name f) (invariant-decl 'name 'f)]))
(define-syntax corollary
  (syntax-rules ()
    [(corollary f) (corollary-decl (symbol-append 'anonymous- (gensym)) 'f)]
    [(corollary name f) (corollary-decl 'name 'f)]))

(define (decl-stream decls [pred (λ (x) #t)])
  (for/stream ([decl decls]
               #:when (pred decl))
    decl))

(define (sort-stream decls)
  (decl-stream decls type-decl?))

(define (inits-as-labeled-formulas decls)
  (for/stream ([decl decls] #:when (init-decl? decl))
    (match decl
      [(init-decl name f) (labeled-formula name f)])))

(define (invariants-as-labeled-formulas decls)
  (for/stream ([decl decls] #:when (invariant-decl? decl))
    (match decl
      [(invariant-decl name f) (labeled-formula name f)])))

(define (corollaries-as-labeled-formulas decls)
  (for/stream ([decl decls] #:when (corollary-decl? decl))
    (match decl
      [(corollary-decl name f) (labeled-formula name f)])))

(define (transitions-as-labeled-formulas decls)
  (for/stream ([decl decls] #:when (transition-decl? decl))
    (match decl
      [(transition-decl name f) (labeled-formula name f)])))

(define (get-labeled-formula-by-name name lfs)
  (labeled-formula-formula
   (stream-first
    (stream-filter (λ (lf) (equal? name (labeled-formula-name lf)))
                   lfs))))

(define (get-transition-by-name decls name)
  (get-labeled-formula-by-name name (transitions-as-labeled-formulas decls)))

(define (get-invariant-by-name decls name)
  (get-labeled-formula-by-name name (invariants-as-labeled-formulas decls)))

(define (get-corollary-by-name decls name)
  (get-labeled-formula-by-name name (corollaries-as-labeled-formulas decls)))

(define (myvy-declare-globals decls)
  (for ([decl decls])
    (match decl
      [(type-decl ty) (solver-declare-sort ty)]
      [(immrel-decl R sorts) (solver-declare-fun R sorts 'Bool)]
      [(immconst-decl C sort)
       (solver-declare-const C sort)
       #;(let ([x (gensym)])
         (solver-assert `(exists ((,x ,sort)) (= ,x ,C))))]
      [(immfun-decl F sorts sort)
       (solver-declare-fun F sorts sort)
       #;(let ([bvs (map (λ (s) (list (gensym) s)) sorts)]
             [y (list (gensym) sort)])
         (solver-assert `(forall ,bvs
                           (exists (,y)
                             (= (,F ,@(map car bvs)) ,(car y))))))]

      [(axiom-decl name f)
       (solver-assert #:label (symbol-append 'axiom- name) f)]

      [_ (void)])))

(define (myvy-declare-mutable-signature-mangle decls mangle)
  (for ([decl decls])
    (match decl
      [(mutrel-decl R sorts) (solver-declare-fun (mangle R) sorts 'Bool)]
      [(mutconst-decl C sort)
       (solver-declare-const (mangle C) sort)
       #;(let ([x (gensym)])
         (solver-assert `(exists ((,x ,sort)) (= ,x ,(mangle C)))))]
      [(mutfun-decl F sorts sort)
       (solver-declare-fun (mangle F) sorts sort)
       #;(let ([bvs (map (λ (s) (list (gensym) s)) sorts)]
             [y (list (gensym) sort)])
         (solver-assert `(forall ,bvs
                           (exists (,y)
                             (= (,(mangle F) ,@(map car bvs)) ,(car y))))))]
      [_ (void)])))

(define (myvy-declare-mutable-signature decls)
  (myvy-declare-mutable-signature-mangle decls (λ (x) x)))

(define (myvy-assert-inits decls [mangle (λ (x) x)])
  (for ([decl decls])
    (match decl
      [(init-decl name f) (solver-assert #:label (symbol-append 'init- name)
                                         (myvy-mangle-formula-one-state decls mangle f))]
      [_ (void)])))

(define (refers-to-mutable decls sym)
  (for/or ([decl decls])
    (match decl
      [(mutrel-decl R _) (equal? sym R)]
      [(mutconst-decl C _) (equal? sym C)]
      [(mutfun-decl F _ _) (equal? sym F)]
      [_ false])))

(define (myvy-mangle-formula-one-state decls mangle f)
  (match f
    [(? symbol? sym) (if (refers-to-mutable decls sym) (mangle sym) sym)]
    [(? list? l) (map (λ (x) (myvy-mangle-formula-one-state decls mangle x)) l)]
    [_ f]))

(define (model-get-elements-of-sort model sort)
  ; (printf "~a\n" sort)
  (apply append
         (for/list ([decl model])
           (match decl
             [`(declare-fun ,sym () ,(== sort)) (list sym)]
             [_ null]))))

(define (myvy-assert-cardinality sort k)
  (define bounds (for/list ([i (in-range k)]) (gensym)))
  (for ([b bounds])
    (solver-declare-fun b '() sort))
  (define x (gensym))
  (solver-assert #:label (symbol-append 'cardinality-constraint-for- sort)
   `(forall ((,x ,sort))
      (or
       ,@(for/list ([b bounds])
           `(= ,x ,b))))))

; compute a minimal model by iteratively tightening cardinality
; constraints on the uninterpreted sorts.
; this function pushes a solver frame which it does not pop.
; on return, that frame contains all the cardinality constraints for the minimal model,
; and nothing else.
; caller should call (solver-pop) when they want to return to the cardinality-unconstrained
; context.
(define (myvy-get-minimal-model decls)
  (match-define `(model ,model ...) (solver-get-model))
  (define (update-model)
    (define res (solver-check-sat))
    (match res
      ['sat (set! model (solver-get-model))
            #t]
      [res #f]))
  (solver-push)
  (for ([sort (stream-map type-decl-name (sort-stream decls))])
    (define n (length (model-get-elements-of-sort model sort)))
    ; (printf "~a ~a\n" sort n)
    (when (= n 1)
      ; (printf "asserted ~a ~a on cardinality frame\n" sort 1)
      (myvy-assert-cardinality sort 1))
    (do ([k (- n 1) (- k 1)]
         [done? #f])
        ((or done? (= k 0)))
      (solver-push)
      (myvy-assert-cardinality sort k)
      (set! done? (not (update-model)))
      (solver-pop)
      ; add last known satisfiable cardinality constraint
      (cond
        [done?
         ; (printf "asserted ~a ~a on cardinality frame\n" sort (+ k 1))
         (myvy-assert-cardinality sort (+ k 1))]
        [(= k 1)
         ; (printf "asserted ~a ~a on cardinality frame\n" sort k)
         (myvy-assert-cardinality sort k)]
        [else (void)])))

  ; call check-sat one more time just to make the model available in the context
  (match (solver-check-sat)
    ['sat (solver-get-model)]))

; checks all the labeled formulas in decls.
; if all checks pass, then #f is returned and the solver context is left unchanged.
; if a check fails, no further checks are performed, and a countermodel is returned.
; in that case, the solver context is left with two additional frames on it.
; the outer frame (next-on-stack) contains (assert (not failing-invariant)).
; the inner frame (top-of-stack) contains minimal cardinality constraints for
; all the uninterpreted sorts.
;
; in other words, if this returns non-#f, the caller must call (solver-pop 2)
; after they are done interacting with the countermodel.
(define (myvy-check-labeled-formulas-mangle mapper decls mangle)
  (for/or ([decl (mapper decls)])
    (match decl
      [(labeled-formula name f)
       (printf "  ~a " name)
       (solver-push)
       (solver-assert #:label (symbol-append 'goal- name)
         (solver-not (myvy-mangle-formula-one-state decls mangle f)))
       (match (solver-check-sat)
         ['sat
          (printf "failed\n")
          (define model (myvy-get-minimal-model decls))

          model]
         ['unsat (printf "ok!\n") (solver-pop) #f])]
      [_ #f])))

(define (myvy-check-labeled-formulas mapper decls)
  (myvy-check-labeled-formulas-mangle mapper decls (λ (x) x)))

(define (myvy-check-init-invariants decls)
  (printf "checking initial state implies invariants\n")
  (solver-push)
  (myvy-declare-mutable-signature decls)
  (myvy-assert-inits decls)
  (let ([res (myvy-check-labeled-formulas invariants-as-labeled-formulas decls)])
    (when res
      (solver-pop 2))
    (solver-pop)
    res))

(define (myvy-assert-invs decls [mangle (λ (x) x)])
  (for ([decl decls])
    (match decl
      [(invariant-decl inv-name f)
       (solver-assert #:label (symbol-append 'hypothesis-invariant- inv-name)
         (myvy-mangle-formula-one-state decls mangle f))]
      [_ (void)])))

(define (number->symbol n)
  (string->symbol (number->string n)))

(define (myvy-mangle-old s) (symbol-append 'old- s))
(define (myvy-mangle-new s) (symbol-append 'new- s))
(define ((myvy-mangle-i i) s)
  (symbol-append 'state- (number->symbol i) '- s))

(define (myvy-mangle-formula-two-state decls mangle-old mangle-new f)
  (define (go old? f)
    (match f
      [(? symbol? sym)
       (if (refers-to-mutable decls sym)
           (if old? (mangle-old sym) (mangle-new sym))
           sym)]
      [`(old ,f2) (if old? (error "nested old") (go true f2))]
      [(? list? l) (map (λ (x) (go old? x)) l)]
      [_ f]))
  (go false f))

(define (myvy-frame-formula-for-modifies-clause decls mangle-old mangle-new nonce mods)
  (solver-and*
   (append*
    (for/list ([decl decls])
      (match decl
        [(mutrel-decl name sorts) #:when (not (member name mods))
         (let ([bounds (map (λ (s) (list (gensym) s)) sorts)])
           (list (solver-label
                  #:label (symbol-append 'frame- nonce '- name)
                  (if (null? bounds)
                      `(= ,(mangle-old name) ,(mangle-new name))
                      `(forall ,bounds
                         (= (,(mangle-old name) ,@(map car bounds))
                            (,(mangle-new name) ,@(map car bounds))))))))]
        [(mutconst-decl name sort) #:when (not (member name mods))
         (list (solver-label #:label (symbol-append 'frame- nonce '- name)
                             `(= ,(mangle-old name) ,(mangle-new name))))]
        [(mutfun-decl name sorts sort) #:when (not (member name mods))
         (let ([bounds (map (λ (s) (list (gensym) s)) sorts)])
           (list (solver-label
                  #:label (symbol-append 'frame- nonce '- name)
                  `(forall ,bounds
                     (= (,(mangle-old name) ,@(map car bounds))
                        (,(mangle-new name) ,@(map car bounds)))))))]

        [_ null])))))

(define (myvy-desugar-transition-relation decls mangle-old mangle-new name formula)
  (match formula
    [`(modifies ,mods ,formula)
     (solver-and
      (myvy-frame-formula-for-modifies-clause decls mangle-old mangle-new name mods)
      (myvy-desugar-transition-relation decls mangle-old mangle-new name formula))]
    [_ (solver-label #:label (symbol-append 'transition-relation- name)
                      (myvy-mangle-formula-two-state decls mangle-old mangle-new formula))]))


(define (myvy-assert-transition-relation decls mangle-old mangle-new name formula)
  (solver-assert (myvy-desugar-transition-relation decls mangle-old mangle-new name formula)))

(define (enumerate-relation eval model elt-map #:mangle [mangle (λ (x) x)] R sorts)
  (if (null? sorts)
      (list R (if (defined-in-model model (mangle R))
                  (eval (mangle R))
                  #f))
      (for/list ([tuple (apply cartesian-product (map (λ (s) (hash-ref elt-map s)) sorts))])
        (list (cons R tuple)
              (if (defined-in-model model (mangle R))
                  (eval (cons (mangle R) tuple))
                  #f)))))

(define (enumerate-function eval model elt-map #:mangle [mangle (λ (x) x)] F sorts sort)
  (for/list ([tuple (apply cartesian-product (map (λ (s) (hash-ref elt-map s)) sorts))])
    (list (cons F tuple)
            (if (defined-in-model model (mangle F))
                (eval (cons (mangle F) tuple))
                (first (hash-ref elt-map sort))))))


(define/match (myvy-expr-to-racket expr)
  [(`(ite ,args ...)) `(if ,@(map myvy-expr-to-racket args))]
  [(`(= ,args ...)) `(equal? ,@(map myvy-expr-to-racket args))]
  [((? list? l)) (map myvy-expr-to-racket l)]
  [(x) x])

(define/match (myvy-model-to-racket model)
  [(`(model ,model ...))
   `(begin
      ,@(apply append
         (for/list ([decl model])
           (match decl
             [`(declare-fun ,nm () ,_) (list `(define ,nm ',nm))]
             [`(define-fun ,nm ,args-with-sorts ,_ ,body)
              (list `(define ,(if (null? args-with-sorts) nm
                                  (cons nm (map car args-with-sorts)))
                       ,(myvy-expr-to-racket body)))]
             [_ null]))))])

(define/match (defined-in-model model name)
  [(`(model ,model ...) _)
   (for/or ([decl model])
     (match decl
       [`(define-fun ,nm ,_ ,_ ,_)
        (equal? name nm)]
       [_ false]))])

(define the-racket-model (void))
(define the-racket-model-decls (void))
(define the-racket-model-z3-model (void))

(define (myvy-make-evaluator-for-model racket-model)
  (define e (make-evaluator 'racket/base #:allow-for-load '("/")))
      #;(λ (x)
          (with-handlers
            ([(λ (_) #t)
              (λ (err)
                (printf "myvy-to-racket eval failed; trying z3's eval as last-ditch effort\n")
                (pretty-print err)
                (newline)
                (solver-eval x))])
            (e x)))

  (e '(define true #t))
  (e '(define false #f))
  (e racket-model)
  e)

(define (myvy-set-up-racket-model-two-state decls model)
  (set! the-racket-model (myvy-model-to-racket model))
  (set! the-racket-model-decls decls)
  (set! the-racket-model-z3-model model))

(define (myvy-model-elt-map decls model)
  (for/hash ([sort (stream-map type-decl-name (sort-stream decls))])
    (values sort (model-get-elements-of-sort model sort))))


(define (enumerate-constant eval model elt-map #:mangle [mangle (λ (x) x)] C sort)
  (if (defined-in-model model (mangle C))
      (list C (eval (mangle C)))
      (list C (first (hash-ref elt-map sort)))))

(define (myvy-enumerate-model-one-state decls mangle model
                                        #:only [the-thing null])

  (define elt-map (myvy-model-elt-map decls model))
  (define eval (myvy-make-evaluator-for-model (myvy-model-to-racket model)))
  (apply append
   (for/list ([decl decls]
              #:when (or (null? the-thing) (equal? the-thing (decl-name decl))))
     (match decl
       [(immrel-decl R sorts)
        (list (enumerate-relation eval model elt-map R sorts))]
       [(mutrel-decl R sorts)
        (list (enumerate-relation eval model elt-map #:mangle mangle R sorts))]
       [(immconst-decl C sort)
        (list (enumerate-constant eval model elt-map C sort))]
       [(mutconst-decl C sort)
        (list (enumerate-constant eval model elt-map #:mangle mangle C sort))]
       [(immfun-decl F sorts sort)
        (list (enumerate-function eval model elt-map F sorts sort))]
       [(mutfun-decl F sorts sort)
        (list (enumerate-function eval model elt-map #:mangle mangle F sorts sort))]
       [_ null]))))

(define (myvy-enumerate-model-two-state decls model
                                        #:only [the-thing null])

  (define elt-map (myvy-model-elt-map decls model))
  (define eval (myvy-make-evaluator-for-model (myvy-model-to-racket model)))
  (apply append
   (for/list ([decl decls]
              #:when (or (null? the-thing) (equal? the-thing (decl-name decl))))
     (match decl
       [(immrel-decl R sorts)
        (list (enumerate-relation eval model elt-map R sorts))]
       [(mutrel-decl R sorts)
        (list (enumerate-relation eval model elt-map (myvy-mangle-old R) sorts)
              (enumerate-relation eval model elt-map (myvy-mangle-new R) sorts))]
       [(immconst-decl C sort)
        (list (enumerate-constant eval model elt-map C sort))]
       [(mutconst-decl C sort)
        (list
         (enumerate-constant eval model elt-map (myvy-mangle-old C) sort)
         (enumerate-constant eval model elt-map (myvy-mangle-new C) sort))]
       [(immfun-decl F sorts sort)
        (list (enumerate-function eval model elt-map F sorts sort))]
       [(mutfun-decl F sorts sort)
        (list
         (enumerate-function eval model elt-map (myvy-mangle-old F) sorts sort)
         (enumerate-function eval model elt-map (myvy-mangle-new F) sorts sort))]
       [_ null]))))

(define (myvy-enumerate-the-model-two-state #:only [the-thing null])
  (myvy-enumerate-model-two-state
    the-racket-model-decls
    the-racket-model-z3-model
    #:only the-thing))

(define (myvy-check-transitions-preserve-invariants decls #:transition [the-thing null])
  (printf "checking transitions preserve invariants\n")
  (solver-push)
  (myvy-declare-mutable-signature-mangle decls myvy-mangle-old)
  (myvy-assert-invs decls myvy-mangle-old)
  (myvy-declare-mutable-signature-mangle decls myvy-mangle-new)
  (let ([res
         (for/or ([decl decls])
           (match decl
             [(transition-decl name f)
              (if (or (null? the-thing) (equal? the-thing name))
                  (begin
                    (printf "transition ~a:\n" name)
                    (solver-push)
                    (myvy-assert-transition-relation decls myvy-mangle-old myvy-mangle-new name f)
                    (let ([res (myvy-check-labeled-formulas-mangle
                                invariants-as-labeled-formulas
                                decls
                                myvy-mangle-new)])
                      (when res
                        (myvy-set-up-racket-model-two-state decls res)
                        ; (pretty-print (myvy-enumerate-the-model-two-state)) (newline)
                        (solver-dont-pop!)
                        (solver-pop 2))
                      (solver-pop)
                      res))
                  #f)]
             [_ #f]))])
    (unless res
      (printf "all checked transitions preserve the invariants!\n"))
    (solver-pop)
    res))

(define (myvy-diagram decls model [mangle (λ (x) x)])
  (define elt-map (myvy-model-elt-map decls model))

  (define rename-map
    (for*/hash ([(sort elts) elt-map]
                [e elts])
      (values e (list (symbol-append sort '- (gensym)) sort))))

  (define (rename s) (car (hash-ref rename-map s)))

  (define vars
    (for/list ([(v1 v2) rename-map])
      v2))

  (define distinct
    (for*/list ([(sort elts) elt-map]
                 [e1 elts]
                 [e2 elts]
                 #:when (symbol<? e1 e2))
       (solver-not `(= ,(rename e1) ,(rename e2)))))

  (define enum (myvy-enumerate-model-one-state decls mangle model))

  ; (printf "enumeration for diagram:\n")
  ; (pretty-print enum)
  ; (newline)

  (define atomic
    (append*
     (for/list ([sym-enum enum])
       (match sym-enum
         [`(,(? symbol? atom) ,value)
          (if (boolean? value)
              (list (if value atom (solver-not atom)))
              (list `(= ,atom ,(rename value))))]
         [_
          (for/list ([clause sym-enum])
            (match clause
              [`((,R ,args ...) ,value)
               (let ([atom `(,R ,@(map rename args))])
                 (if (boolean? value)
                     (if value atom (solver-not atom))
                     `(= ,atom ,(rename value))))]))]))))

  (define (wrap cs)
    (match cs
      ['() 'true]
      [(list x) x]
      [_ `(and ,@cs)]))

  `(exists ,vars ,(wrap (append distinct atomic))))

(define (myvy-init decls)
  (set! the-racket-model null)
  (set! the-racket-model-decls null)
  (set! the-racket-model-z3-model null)
  (set! inductive-frame null)

  (parameterize ([z3 "/Users/jrw12/local/bin/z3"])
    (solver-init))
  (solver-set-option ':auto-config 'false)
  (solver-set-option ':smt.mbqi 'true)
  (solver-set-option ':interactive-mode 'true)
  (solver-set-option ':produce-unsat-cores 'true)

  (myvy-declare-globals decls))

(define (myvy-check-corollaries decls)
  (printf "checking invariants imply corollaries\n")
  (solver-push)
  (myvy-declare-mutable-signature decls)
  (myvy-assert-invs decls)
  (let ([res (myvy-check-labeled-formulas corollaries-as-labeled-formulas decls)])
    (when res
      (solver-pop 2))
    (solver-pop)
    res))

(define (solver-labeled-or #:nonce [nonce null] . args)
  (define (mk-label)
    (if (null? nonce)
        (symbol-append 'label- (gensym))
        (symbol-append 'label- (number->symbol nonce) '- (gensym))))
  (solver-or* (map (λ (disjunct) (solver-and (mk-label) disjunct))
                   args)))

(define (solver-labeled-or* #:nonce [nonce null] l)
  (apply solver-labeled-or l #:nonce nonce))

(define (solver-labels-of-labeled-or expr)
  (match expr
    [`(or ,disjuncts ...)
     (map second disjuncts)]))

(define (myvy-disjunction-of-all-transition-relations decls nonce mangle-old mangle-new)
  (solver-labeled-or* #:nonce nonce
   (for/list ([decl (transitions-as-labeled-formulas decls)])
     (match decl
       [(labeled-formula name f)
        (myvy-desugar-transition-relation decls mangle-old mangle-new
                                          (symbol-append name '- (number->symbol nonce))
                                          f)]))))


(define (myvy-declare-labels lbls)
  (for ([lbl lbls])
    (solver-declare-const lbl 'Bool)))

(define (myvy-bmc-no-init decls n goal)
  (solver-push)
  (myvy-declare-mutable-signature-mangle decls (myvy-mangle-i 0))
  (myvy-assert-inits decls (myvy-mangle-i 0))
  (for ([i (in-range 1 (+ n 1))])
    (myvy-declare-mutable-signature-mangle decls (myvy-mangle-i i))
    (define t (myvy-disjunction-of-all-transition-relations
               decls i
               (myvy-mangle-i (- i 1))
               (myvy-mangle-i i)))
    (myvy-declare-labels (solver-labels-of-labeled-or t))
    (solver-assert
     #:label (symbol-append 'bmc-transition- (number->symbol i))
     t))

  (solver-assert #:label 'bmc-goal
                 (myvy-mangle-formula-one-state decls (myvy-mangle-i n) goal))
  (match (solver-check-sat)
    ['unsat (solver-pop) 'unsat]
    ['sat (myvy-get-minimal-model decls)]))

(define (myvy-bmc decls n goal)
  (myvy-init decls)
  (myvy-bmc-no-init decls n goal))

(define (myvy-verify decls)
  (myvy-init decls)
  (not
   (or
    (myvy-check-init-invariants decls)
    (myvy-check-transitions-preserve-invariants decls)
    (myvy-check-corollaries decls))))

(define (myvy-updr-frame-to-formula f)
  (solver-and* f))

(define (myvy-updr-check-frontier decls bad fs)
  (solver-push)
    (printf "checking whether frontier has any bad states: ")
    (myvy-declare-mutable-signature decls)
    (solver-assert (myvy-updr-frame-to-formula (first fs)))
    (solver-assert bad)
    (match (solver-check-sat)
      ['unsat (solver-pop) 'unsat]
      [x x]))

(define (myvy-updr-analyze-counterexample decls bad fs diag)
  (printf "abstract counterexample found!\n")
  (pretty-print fs)
  (newline)
  (printf "trying bmc with ~a steps...\n" (- (length fs) 1))
  (match (myvy-bmc-no-init decls (- (length fs) 1) bad)
    ['unsat (list 'no-universal-invariant fs (list diag))]
    [model (solver-pop 2) (list 'invalid model)]))

(define (myvy-updr-check-predecessor decls pre diag)
  (solver-push)
    (printf "checking whether diagram has a predecessor in prestate\n")
    ; (pretty-print pre)
    ; (newline)
    (myvy-declare-mutable-signature-mangle decls myvy-mangle-old)
    (myvy-declare-mutable-signature-mangle decls myvy-mangle-new)
    (solver-assert #:label 'prestate-clauses
                   (myvy-mangle-formula-one-state decls myvy-mangle-old pre))
    (solver-assert-skolemize
     #:label 'diagram
     (myvy-mangle-formula-one-state decls myvy-mangle-new diag))
  
    (define t (myvy-disjunction-of-all-transition-relations
               decls 0 myvy-mangle-old myvy-mangle-new))
    (myvy-declare-labels (solver-labels-of-labeled-or t))

    (solver-assert #:label 'transition t)

    (match (solver-check-sat)
      ['unsat (begin0
                  (list 'unsat (list (list (solver-get-stack) (solver-get-unsat-core))))
                (solver-pop))]
      ['sat (define model (myvy-get-minimal-model decls))
            (begin0
                (list 'sat
                      (myvy-diagram decls model myvy-mangle-old)
                      model
                      (myvy-enumerate-model-one-state decls myvy-mangle-old model))
              ; (printf "would you like the solver stack?\n")
              ; (match (read)
              ;   ['no (void)]
              ;   ('yes (pretty-print (solver-get-stack))))
              ; (printf "would you like the minimal model?\n")
              ; (match (read)
              ;   ['no (void)]
              ;   ('yes (pretty-print model)))


              (solver-pop 2))])

    #;(define log null)
    #;(begin0
        (or
         (for/or ([t (transitions-as-labeled-formulas decls)])
           (match t
             [(labeled-formula name f)
              (printf "  transition ~a: " name)
              (solver-push)
              (myvy-assert-transition-relation decls myvy-mangle-old myvy-mangle-new name f)
              (match (solver-check-sat)
                ['unsat (printf "unsat\n")
                        (set! log (cons (list (solver-get-stack)
                                              (solver-get-unsat-core))
                                        log))
                        (solver-pop)
                        #f]
                ['sat (printf "sat!\n")
                      (define model (myvy-get-minimal-model decls))
                      (begin0
                          (list 'sat
                                (myvy-diagram decls model myvy-mangle-old)
                                name)
                        ; (printf "would you like the solver stack?\n")
                        ; (match (read)
                        ;   ['no (void)]
                        ;   ('yes (pretty-print (solver-get-stack))))
                        ; (printf "would you like the minimal model?\n")
                        ; (match (read)
                        ;   ['no (void)]
                        ;   ('yes (pretty-print model)))


                        (solver-pop 2))])]))
         (list 'unsat log))
      (solver-pop)))

(define (myvy-one-state-implies decls hyps goal)
  (solver-push)
    (myvy-declare-mutable-signature decls)
    (for ([hyp hyps])
      (solver-assert hyp))
    (solver-assert (solver-not goal))
    (begin0
        (match (solver-check-sat)
          ['sat #f]
          ['unsat #t])
      (solver-pop)))

(define (myvy-updr-conjoin-frames-up-through decls j fs phi)
  (define (go fs)
    (match fs
      ['() (list 0 '())]
      [(cons f fs)
       (match (go fs)
         [(list i fs)
          (list (+ i 1)
                (if (and (<= i j) (not (myvy-one-state-implies decls f phi)))
                    (cons (cons phi f) fs)
                    (cons f fs)))])]))

  (match (go fs)
    [(list _ fs)
     ; (printf "blocked. new frames\n")
     ; (pretty-print fs)
     ; (newline)
     fs]))

(define (myvy-updr-minimize-diag-with-unsat-core decls unsat-log diag)
  ; (printf "unsat core\n")
  ; (pretty-print unsat-log)
  ; (newline)

  (define core-names
    (remove-duplicates
     (filter (λ (x) (string-prefix? (symbol->string x) "diagram-"))
             (append* (map cadr unsat-log)))))

  (define named-conjuncts
    (append*
     (for/list ([decl (second (caar unsat-log))])
       (match decl
         [`(assert (! ,conjunct :named ,name))
          (list (list name conjunct))]
         [_ null]))))

  (define (in-core formula)
    (for/or ([named-conjunct named-conjuncts])
      (match named-conjunct
        [(list name conjunct)
         (and (equal? conjunct formula)
              (member name core-names))])))


  (define (free-in var expr)
    ; note: this doesn't handle variable binding.
    ; it's probably fine since we gensym a lot.
    (define (go expr)
      (match expr
        [(? symbol? v) (equal? var v)]
        [(list args ...) (ormap go args)]))

    (go expr))

  (define (filter-free-vars-of expr bvs)
    (filter (λ (bv) (free-in (first bv) expr)) bvs))

  (define (reconstruct-unsat-core-diagram formula)
    (match formula
      [`(exists ,vars ,body)
       (match (reconstruct-unsat-core-diagram body)
         ['() '()]
         [x `(exists ,(filter-free-vars-of x vars) ,x)])]
      [`(and ,body ...)
       (match (filter (λ (x) (not (null? x)))
                      (map reconstruct-unsat-core-diagram body))
         ['() '()]
         [x `(and ,@x)])]

      [_ (if (in-core (myvy-mangle-formula-one-state decls myvy-mangle-new formula))
             formula
             '())]))

  (reconstruct-unsat-core-diagram diag))

(define (get-frame j fs)
  (list-ref fs (- (length fs) j 1)))

(define (myvy-get-inits decls)
  (stream-map
   labeled-formula-formula
   (inits-as-labeled-formulas decls)))

(define (myvy-minimize-conj-relative-inductive decls frame expr)
  (match-define `(forall ,bvs (or ,disjs ...)) expr)

  ; (printf "minimizing unsat core for relative inductiveness!\n")
  ; (pretty-print expr)
  ; (pretty-print bvs)
  ; (pretty-print disjs)

  (unless (and (myvy-one-state-implies decls (myvy-get-inits decls) expr)
               (myvy-updr-relative-inductive decls frame expr))
    (printf "xxx: not starting with relative-inductive conjecture!\n"))

  (define (build disjs)
    `(forall ,bvs ,(solver-or* disjs)))

  (define (go head tail)
    (match tail
      ['() (reverse head)]
      [(cons t tail)
       (define e (build (append head tail)))
       (if (and (myvy-one-state-implies decls (myvy-get-inits decls) e)
                (myvy-updr-relative-inductive decls frame e))
           (go head tail)
           (go (cons t head) tail))]))

  (define ans (build (go '() disjs)))
  (when (not (equal? ans expr))
    (printf "minimized conjecture!\n"))
    (pretty-print ans)
  ans)

(define inductive-frame (void))

(define (myvy-updr-block-diagram decls bad fs diag model enum j)
  (printf "updr blocking diagram in frame ~a\n" j)
  (pretty-print diag)
  (newline)

  #;(unless (myvy-one-state-implies decls (list diag)
            `(not ,(myvy-get-invariants-as-formula decls)))
    (parameterize ([z3-log? true])
      (displayln "parent stack")
      (pretty-print (solver-get-stack))
      (myvy-one-state-implies decls (list diag)
            `(not ,(myvy-get-invariants-as-formula decls))))
    (pretty-print model)
    (pretty-print enum)
    (error "diagram does not violate inductive invariant"))

  (if (= j 0)
      (myvy-updr-analyze-counterexample decls bad fs diag)
      (match (myvy-updr-check-predecessor
              decls
              (myvy-updr-frame-to-formula (get-frame (- j 1) fs))
              diag)
        [(list 'unsat log)
         (printf "diagram has no predecessor, computing unsat core to block\n")
         (let ([conj (solver-not (myvy-updr-minimize-diag-with-unsat-core decls log diag))])
           (pretty-print conj)
           ;(newline)
           ;(printf "would you like to enter a inductive strengethening?\n")
           (let ([conj
                  conj
                  #;(match (read)
                    ['yes (read)]
                    ['no conj])])
             (when (not (myvy-updr-relative-inductive decls (get-frame (- j 1) fs) conj))
               (printf "ZZZ: unsat core is not relative inductive\n"))

             (set! conj (myvy-minimize-conj-relative-inductive decls (get-frame (- j 1) fs) conj))

             (when (and (myvy-one-state-implies decls (myvy-get-inits decls) conj)
                        (myvy-updr-relative-inductive decls inductive-frame conj)
                        (not (myvy-one-state-implies decls inductive-frame conj)))
               (set! inductive-frame
                     (myvy-updr-simplify-frame decls (cons conj inductive-frame)))
               (printf "discovered new inductive invariant\n")
               (pretty-print inductive-frame)
               (for ([i inductive-frame])
                 (set! fs (myvy-updr-conjoin-frames-up-through decls (length fs) fs i)))
               (when (and (myvy-one-state-implies decls (myvy-get-inits decls)
                                                  (solver-and* inductive-frame))
                          (myvy-updr-relative-inductive decls inductive-frame
                                                        (solver-and* inductive-frame))
                          (myvy-one-state-implies decls inductive-frame
                                                  (solver-not bad)))
                 (printf "WOW! inductive frame already inductive!!!\n")))


             (list 'blocked (myvy-updr-conjoin-frames-up-through decls j fs conj))))]
        [(list 'sat diag2 model2 enum2 #;transition-name)
         #;(printf "diagram has predecessor via ~a\n" transition-name)
         (printf "diagram has predecessor\n")
         (printf "recursively blocking predecessor\n")
         (match (myvy-updr-block-diagram decls bad fs diag2 model2 enum2 (- j 1))
           [(list 'blocked fs) (myvy-updr-block-diagram decls bad fs diag model enum j)]
           [(list 'no-universal-invariant fs diags)
            (list 'no-universal-invariant fs (cons diag diags))]
           [res res])])))


#;(define (myvy-updr-simplify-frame decls f)
  (match f
    ['() '()]
    [(cons c f)
     (cons c
           (filter (λ (c2) (not (myvy-one-state-implies decls (list c) c2)))
                   (myvy-updr-simplify-frame decls f)))]))

#;(define (myvy-updr-simplify-frames2 decls fs)
  (printf "simplifying frames...\n")

  (for/list ([f fs])
    (myvy-updr-simplify-frame decls f)))

#;(define (myvy-updr-simplify-frames decls fs)
  (map reverse
       (myvy-updr-simplify-frames2
        decls
        (map reverse (myvy-updr-simplify-frames2 decls fs)))))

(define (myvy-updr-simplify-frame decls f)
  (printf "simplifying frame\n")
  (solver-push)
  (myvy-declare-mutable-signature decls)
  (begin0
      (myvy-simplify-all-in-context '() f)
    (solver-pop)
    (printf "done simplifying")))

(define (myvy-updr-simplify-frames decls fs)
  (printf "simplifying frames\n")
  (solver-push)
  (myvy-declare-mutable-signature decls)
  (begin0
      (for/list ([f fs])
        (myvy-simplify-all-in-context '() f))
    (solver-pop)
    (printf "done simplifying")))

(define (check-frame-implies decls hyps goals)
  (solver-push)
    (myvy-declare-mutable-signature decls)
    (for ([hyp hyps])
      (solver-assert hyp))
    (begin0
        (for/and ([goal goals])
          (solver-push)
          (solver-assert (solver-not goal))
          (begin0
              (match (solver-check-sat)
                ['sat (printf "goal not implied\n")
                      (pretty-print goal)
                      #f]
                ['unsat #t])
            (solver-pop)))
      (solver-pop)))

(define (myvy-updr-relative-inductive decls hyps expr)
  (solver-push)
    (myvy-declare-mutable-signature-mangle decls myvy-mangle-old)
    (myvy-declare-mutable-signature-mangle decls myvy-mangle-new)

    (for ([hyp hyps])
      (solver-assert (myvy-mangle-formula-one-state decls myvy-mangle-old hyp)))

    (solver-assert (myvy-mangle-formula-one-state decls myvy-mangle-old expr))
    (solver-assert (myvy-mangle-formula-one-state decls myvy-mangle-new (solver-not expr)))

    (begin0
        (for/and ([t (transitions-as-labeled-formulas decls)])
           (match t
             [(labeled-formula name f)
              (solver-push)
              (myvy-assert-transition-relation decls myvy-mangle-old myvy-mangle-new name f)
              (begin0
                  (match (solver-check-sat)
                    ['sat #f]
                    ['unsat #t])
                (solver-pop))]))
      (solver-pop)))


(define (myvy-updr-push-forward decls f)
  (for/list ([conj f]
             #:when (myvy-updr-relative-inductive decls f conj))
    conj))

(define (myvy-updr-push-forward-all decls fs)
  (define (go fs)
    (match fs
      ['() '()]
      [(list f) (list f)]
      [(cons f fs)
       (let ([fs (go fs)])
         (cons (set-union f (myvy-updr-push-forward decls (first fs))) fs))]))

  (printf "pushing forward lemmas...\n")
  (go fs))

(define (myvy-get-safety-property-as-formula decls)
  (solver-and*
   (stream->list
    (stream-map labeled-formula-formula
                (corollaries-as-labeled-formulas decls)))))

(define (myvy-get-invariants-as-formula decls)
  (solver-and*
   (stream->list
    (stream-map labeled-formula-formula
                (invariants-as-labeled-formulas decls)))))


(define (myvy-updr decls)
  (myvy-init decls)

  (define inits (stream-map
                 labeled-formula-formula
                 (inits-as-labeled-formulas decls)))

  (define safety (myvy-get-safety-property-as-formula decls))

  (printf "checking whether initial state imilpies safety: ")
  (unless (myvy-one-state-implies decls inits safety)
    (error "no"))
  (printf "ok!\n")

  (define bad (solver-not safety))

  (define fs (myvy-updr-push-forward-all decls (list (list 'true) (stream->list inits))))

  (printf "initializing updr with inits\n")
  (pretty-print (stream->list inits))

  (printf "initializing updr with bad states\n")
  (pretty-print bad)

  (define (go fs)
    (set! fs (myvy-updr-simplify-frames decls fs))

    (printf "outer updr loop considering frame ~a\n" (- (length fs) 1))
    (pretty-print inductive-frame)
    (pretty-print fs)
    (newline)

    (printf "(solver stack height is ~a)\n" (length (solver-get-stack)))

    (match (myvy-updr-check-frontier decls bad fs)
      ['unsat
       (printf "frontier is safe.\n")
       (printf "moving to new frame\n")
       (set! fs (myvy-updr-push-forward-all decls (cons (list 'true) fs)))
       (set! fs (myvy-updr-simplify-frames decls fs))
       (define I (for/or ([next fs]
                          [prev (rest fs)]
                          #:when (check-frame-implies decls next prev))
                   prev))
       (if I
           (list 'valid I)
           (go fs))]
      ['sat
       (printf "frontier is not safe, blocking minimal model\n")
       (let* ([model (myvy-get-minimal-model decls)]
              [diag (myvy-diagram decls model)])
         #;(pretty-print diag)
         #;(newline)
         (solver-pop 2)
         (match (myvy-updr-block-diagram decls bad fs diag model
                  (myvy-enumerate-model-one-state decls (λ (x) x) model)
                  (- (length fs) 1))
           [(list 'invalid cex)  (list 'invalid cex)]
           [(list 'no-universal-invariant fs diags)
            (list 'no-universal-invariant (reverse fs) (reverse diags))]
           [(list 'blocked fs) (go fs)]))]))

  (go fs))

(define (myvy-sat-yes-unsat-no msg)
  (printf "checking whether ~a: " msg)
  (match (solver-check-sat)
    ['sat (displayln "yes")]
    ['unsat (displayln "no")]))

(define (myvy-updr-check-abstract-cex decls acex)
  (solver-push)
    (solver-push)
      (myvy-declare-mutable-signature decls)
      (solver-push)
        (myvy-assert-inits decls)
        (solver-assert #:label 'phi-0 (first acex))
        (myvy-sat-yes-unsat-no "counterexample starts in initial state")
      (solver-pop)
      (solver-push)
        (solver-assert #:label 'bad (solver-not (myvy-get-safety-property-as-formula decls)))
        (solver-assert #:label 'phi-n (last acex))
        (myvy-sat-yes-unsat-no "counterexample ends in bad state")
      (solver-pop)
    (solver-pop)
    (solver-push)
      (myvy-declare-mutable-signature-mangle decls myvy-mangle-old)
      (myvy-declare-mutable-signature-mangle decls myvy-mangle-new)
      (for ([phi-current acex]
            [phi-next (rest acex)]
            [i (in-naturals)])
        (solver-push)
          (solver-assert #:label 'phi-current
            (myvy-mangle-formula-one-state decls myvy-mangle-old phi-current))
          (solver-assert #:label 'phi-next
            (myvy-mangle-formula-one-state decls myvy-mangle-new phi-next))
          (define t (myvy-disjunction-of-all-transition-relations
                     decls 0 myvy-mangle-old myvy-mangle-new))
          (myvy-declare-labels (solver-labels-of-labeled-or t))
      
          (solver-assert #:label 'transition t)

          (myvy-sat-yes-unsat-no (format "counterexample transition ~a is allowed" i))
          ;(when (= i 3)
            (pretty-print phi-current)
            (pretty-print t)
            (pretty-print phi-next)
            (pretty-print (solver-get-model))
        ;)
        (solver-pop))
    (solver-pop)
  (solver-pop))
      
(define (solver-query e)
  (solver-push)
    (solver-assert (solver-not e))
    (begin0
        (match (solver-check-sat)
          ['sat #f]
          ['unsat #;(pretty-print (solver-get-stack)) #t])
      (solver-pop)))

(define (myvy-with-hyps hyps f)
  (solver-push)
  (for ([hyp hyps])
    (solver-assert hyp))
  (begin0
      (f)
    (solver-pop)))

(define (myvy-simplify-in-context hyps goal)
  (define (must-be-true e) (solver-query e))
  (define (must-be-false e) (solver-query (solver-not e)))

  (define (declare bvs)
    (for ([bv bvs])
      (match bv
        [(list x sort)
         (solver-declare-const x sort)])))

  (define (go-list exprs [f (λ (x) x)])
    (match exprs
      ['() '()]
      [(cons expr exprs)
       (let ([expr (go expr)])
         (solver-push)
         (solver-assert (f expr))
         (begin0
             (cons expr (go-list exprs f))
           (solver-pop)))]))

  (define (reorder-nots l)
    (let-values ([(neg pos) (partition (match-lambda [`(not ,_) #t] [_ #f]) l)])
      (append neg pos)))

  (define (go goal)
    (cond
      [(must-be-true goal) 'true]
      [(must-be-false goal) 'false]
      [else (match goal
              [`(forall ,bvs ,body)
               (solver-push)
               (declare bvs)
               (begin0
                   `(forall ,bvs ,(go body))
                 (solver-pop))]
              [`(exists ,bvs ,body)
               (solver-push)
               (declare bvs)
               (begin0
                   `(exists ,bvs ,(go body))
                 (solver-pop))]
              [`(and ,conjs ...)
               (solver-and* (go-list conjs))]
              [`(or ,conjs ...)
               (solver-or* (go-list (reorder-nots conjs) solver-not))]
              [`(=> ,P ,Q)
               (go `(or (not ,P) ,Q))]
              [_ goal])]))

  (myvy-with-hyps hyps (λ () (go goal))))

(define (myvy-simplify-all-in-context hyps goals)
  (define (go head tail)
    (match tail
      ['() (reverse (filter (λ (x) (not (equal? 'true x))) head))]
      [(cons e tail)
       (go (cons (myvy-simplify-in-context (append head tail) e) head) tail)]))

  (myvy-with-hyps hyps
   (λ () (go '() goals))))



