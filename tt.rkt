#lang typed/racket

;; This is me learning Racket by attempting to implement a somewhat
;; NuPRL-inspired system on top of it.
;; No guarantees are made as to the goodness of it.

(require racket/set)

(module+ test (require typed/rackunit))


;;;; Helpers
(: zip (All (a b) (-> (Listof a) (Listof b) (Listof (Pair a b)))))
(define (zip l1 l2) (zip-with #{cons @ a b} l1 l2))

(: zip-with (All (a b c)
                 (-> (-> a b c)
                     (Listof a)
                     (Listof b)
                     (Listof c))))
(define (zip-with f l1 l2)
  (match* (l1 l2)
    [((cons x xs) (cons y ys))
     (cons (f x y) (zip-with f xs ys))]
    [(empty empty) (list)]
    [(_ _) (error "Mismatched list lengths")]))



;;;; Terms are old-school Lisp terms for now
(define-type Term
  (U Symbol (Listof Term) Integer Null))

(define-type Well-Formed-Lambda
  (List 'λ (Listof Symbol) Term))

(define-predicate well-formed-lambda? Well-Formed-Lambda)

(define-type (Typed-Binding-Form sym)
  (List sym (Listof (List Symbol Term)) Term))

(define-type Well-Formed-Pi
  (Typed-Binding-Form 'Π))

(define-predicate well-formed-pi? Well-Formed-Pi)

(: pi-get-arguments (-> Well-Formed-Pi (Listof (List Symbol Term))))
(define (pi-get-arguments term)
  (cadr term))

(: pi-get-body (-> Well-Formed-Pi Term))
(define (pi-get-body term)
  (caddr term))

;;; Intersections start with \bigcap, not \cap
(define-type Well-Formed-Intersection
  (Typed-Binding-Form '⋂))

(define-predicate well-formed-intersection? Well-Formed-Intersection)

(: intersection-get-arguments (-> Well-Formed-Intersection
                                  (Listof (List Symbol Term))))
(define (intersection-get-arguments term) (cadr term))

(: intersection-get-body (-> Well-Formed-Intersection Term))
(define (intersection-get-body term) (caddr term))


(: binding-list? (Any -> Boolean : (Listof Symbol)))
(define-predicate binding-list? (Listof Symbol))

(: typed-binding-list? (Any -> Boolean : (Listof (List Symbol Term))))
(define-predicate typed-binding-list? (Listof (List Symbol Term)))

(: decompose-binding-list (-> (Listof (List Symbol Term))
                              (List (Listof Symbol) (Listof Term))))
(define (decompose-binding-list names-and-types)
  (if (null? names-and-types)
      '(() ())
      (let ((rest (decompose-binding-list (cdr names-and-types))))
        (list (cons (caar names-and-types) (car rest))
              (cons (cadar names-and-types) (cadr rest))))))


(: free-variables (-> Term (Setof Symbol)))
(define (free-variables term)
  (: no-vars (Setof Symbol))
  (define no-vars (list->set empty))
  (: combine (-> (Setof Symbol) (Setof Symbol) (Setof Symbol)))
  (define combine set-union)

  (match term
    [`(λ ,args ,body)
     (if (binding-list? args)
         (set-subtract (free-variables body) (list->set args))
         (error "Malformed term"))]
    [`(Π ,args ,body)
     (if (typed-binding-list? args)
         (match-let ((`(,names ,types) (decompose-binding-list args)))
           (set-union (foldr combine no-vars (map free-variables types))
                      (set-subtract (free-variables body)
                                    (list->set names))))
         (error "Malformed term"))]
    [xs (cond ((list? xs)
               (foldr combine
                      no-vars
                      (map free-variables xs)))
              ((symbol? xs)
               (set xs))
              (#t no-vars))]))

(module+ test
  (check-equal? (free-variables '(λ (x) (+ x y))) (set 'y '+))
  (check-equal? (free-variables '(Π ([x t]) y)) (set 't 'y)))

(: α-equiv? (-> (Listof (Pair Symbol Symbol)) Term Term Boolean))
(define (α-equiv? context left right)
  (match* (left right)
    [((list 'λ args1 body1) (list 'λ args2 body2))
     (if (and (binding-list? args1)
              (binding-list? args2))
         (and (= (length args1) (length args2))
              (α-equiv? ((inst append (Pair Symbol Symbol))
                         (for/list ([x args1] [y args2])
                           (cons x y))
                         context)
                        body1
                        body2))
         (error "Malformed term"))]

    [((list 'Π args1 body1) (list 'Π args2 body2))
     (: all (-> (Listof Any) Any))
     (define (all bools)
       (if (null? bools) #t (and (car bools) (all (cdr bools)))))
     (if (and (typed-binding-list? args1)
              (typed-binding-list? args2))
         (let ([names1 (map (inst car Symbol Term) args1)]
               [types1 (map (inst cadr Symbol Term Null) args1)]
               [names2 (map (inst car Symbol Term) args2)]
               [types2 (map (inst cadr Symbol Term Null) args2)])
           (and (= (length args1) (length args2))
                (all (map (lambda ([type-1 : Term]
                                   [type-2 : Term])
                            (α-equiv? context type-1 type-2))
                          types1
                          types2))
                (α-equiv? ((inst append (Pair Symbol Symbol))
                           (for/list ([x names1] [y names2])
                             (cons x y))
                           context)
                          body1
                          body2)))
         #f)]

    [(app1 app2)
     #:when (and (list? app1) (list? app2))
     ;; todo: rule out lists starting with lambda/pi
     (for/and ((term1 app1)
               (term2 app2))
       (α-equiv? context term1 term2))]

    [(x y)
     #:when (and (number? x) (number? y))
     (= x y)]

    [(x y)
     #:when (and (symbol? x) (symbol? y))
     (let ((found (assoc x context)))
       (if found
           ;; bound
           (eq? y (cdr found))
           ;; free
           (eq? x y)))]

    [(_ _) #f]))

(module+ test
  (check-equal? (α-equiv? empty
                          '(λ (x) (+ x 2))
                          '(λ (y) (+ y 2)))
                #t)
  (check-equal? (α-equiv? empty
                          '(Π ((x Integer)) Integer)
                          '(Π ((y Integer)) Integer))
                #t)
  (check-equal? (α-equiv? empty 'x 'y) #f)
  )


(: rename-free-variables (-> (HashTable Symbol Symbol)
                             Term
                             Term))
(define (rename-free-variables renames term)
  (: remove-renames (-> (Listof Symbol)
                        (HashTable Symbol Symbol)
                        (HashTable Symbol Symbol)))
  (define (remove-renames vars renames)
    (for/fold ([so-far renames])
              ([x vars])
      (hash-remove so-far x)))
  
  (match term
    [`(λ ,args ,body)
     (if (binding-list? args)
         `(λ ,args ,(rename-free-variables (remove-renames args
                                                           renames)
                                           body))
         (error "Malformed term"))]
    [`(Π ,typed-args ,body)
     (if (typed-binding-list? typed-args)
         (match-let ((`(,names ,types)
                      (decompose-binding-list typed-args)))
           `(Π ,(zip-with
                 (λ ([x : Symbol] [y : Term]) (list x y))
                 names
                 (map (λ ([type : Term])
                        (rename-free-variables renames type)) types))
               ,(rename-free-variables (remove-renames names renames)
                                       body)))
         (error "Malformed term"))]
    [application
     #:when (list? application)
     (map (λ ([subterm : Term])
            (rename-free-variables renames subterm))
          application)]
    [x #:when (symbol? x)
       (let ((new-var (hash-ref renames x #f)))
         (if new-var
             new-var
             x))]))

;;; Construct a new symbol based on an existing one that resembles the
;;; original, for use when uniquifying binder names
(: next-symbol (-> Symbol Symbol))
(define (next-symbol symbol)
  (: symbol-number Regexp)
  (define symbol-number #rx"^(.*[^0-9])([0-9]*)$")

  (let ((name-and-number
         (regexp-match symbol-number
                       (symbol->string symbol))))
    (match name-and-number
      [#f (string->symbol (string-append (symbol->string symbol)
                                         "1"))]
      [(list _ name num) #:when (and name num)
       (let ((the-number (string->number num)))
         (string->symbol
          (string-append name
                         (if the-number
                             (number->string (+ the-number 1))
                             "1"))))])))

(module+ test
  (check-equal? (next-symbol 'x) 'x1)
  (check-equal? (next-symbol 'x23) 'x24)
  (check-equal? (next-symbol '|123|)
                '|1231|)
  (check-equal? (next-symbol 'lkj1lk3jl1k2j3l1k2j3)
                'lkj1lk3jl1k2j3l1k2j4))

(: next-available-symbol (-> (Setof Symbol) Symbol Symbol))
(define (next-available-symbol taken start)
  (if (set-member? taken start)
      (next-available-symbol taken (next-symbol start))
      start))

(module+ test
  (check-equal? (next-available-symbol (set 'x 'y) 'z) 'z)
  (check-equal? (next-available-symbol (set 'x 'x1 'x2) 'x) 'x3))

(: rename-binders (-> (Setof Symbol)
                      (Listof Symbol)
                      (Pair (Listof Symbol)
                            (HashTable Symbol Symbol))))
(define (rename-binders taken input)
  (: helper (-> (Setof Symbol) (Listof Symbol)
                (Listof Symbol) (HashTable Symbol Symbol)
                (Pair (Listof Symbol)
                      (HashTable Symbol Symbol))))
  (define (helper all-taken remaining output renames)
    (if (null? remaining)
        (cons (reverse output) renames)
        (let* ((old-name (car remaining))
               (new-name
                (next-available-symbol all-taken
                                       old-name)))
          (helper (set-add all-taken new-name)
                  (cdr remaining)
                  (cons new-name output)
                  (hash-set renames old-name new-name)))))

  (helper taken input empty (hash)))

(: rename-typed-binders (-> (Setof Symbol)
                            (Listof (List Symbol Term))
                            (Pair (Listof (List Symbol Term))
                                  (HashTable Symbol Symbol))))
(define (rename-typed-binders taken input)
  (let* ((names (map (inst car Symbol Term) input))
         (types (map (inst cadr Symbol Term Null) input))
         (renames (rename-binders taken names)))
    (cons (map (lambda ([name : Symbol] [type : Term])
                 (list name type))
               (car renames)
               types)
          (cdr renames))))

;;; Substitution for pi and intersection
(: substitute-typed-binder
   (All (S)
        (-> S
            Term
            Symbol
            (Typed-Binding-Form S)
            (Typed-Binding-Form S))))
(define (substitute-typed-binder head-symbol new-term name in-term)
  (let ((arguments (cadr in-term)))
    (if (memf (lambda ([b : (List Symbol Term)])
                (equal? (car b) name))
              arguments)
        ;; The variable is bound here -
        ;; substitute only in type annots
        (list head-symbol
              (map (λ ([binding : (List Symbol Term)])
                     (list (car binding)
                           (substitute new-term name (cadr binding))))
                   arguments)
              (caddr in-term))
        ;; Descend into body
        (let ((body (caddr in-term))
              (renamed (rename-typed-binders
                        (free-variables new-term)
                        arguments)))
          (list head-symbol
                (map (λ ([binding : (List Symbol Term)])
                       (list (car binding)
                             (substitute new-term
                                         name
                                         (cadr binding))))
                     (car renamed))
                (substitute new-term
                            name
                            (rename-free-variables
                             (cdr renamed)
                             body)))))))

(: substitute (-> Term Symbol Term Term))
(define (substitute new-term name in-term)
  (cond [(symbol? in-term)
         (if (equal? in-term name)
             new-term
             in-term)]
        [(integer? in-term) in-term]
        [(pair? in-term)
         (let ((head (car in-term)))
           (cond [(equal? head 'λ)
                  (if (well-formed-lambda? in-term)
                      (let ((λ-arguments (cadr in-term)))
                        (if (member name λ-arguments)
                            in-term
                            (let ((λ-body (caddr in-term))
                                  (renamed (rename-binders
                                            (free-variables new-term)
                                            λ-arguments)))
                              `(λ ,(car renamed)
                                 ,(substitute new-term
                                              name
                                              (rename-free-variables
                                               (cdr renamed)
                                               λ-body))))))
                      (error "Malformed term: bad lambda" in-term))]
                 [(or (equal? head 'Π)
                      (equal? head '⋂))
                  (cond [(well-formed-pi? in-term)
                         (substitute-typed-binder
                          'Π new-term name in-term)]
                        [(well-formed-intersection? in-term)
                         (substitute-typed-binder
                          '⋂ new-term name in-term)]
                        [#t (error "Malformed term" in-term)])]
                 [#t (map (lambda ([subterm : Term])
                            (substitute new-term name subterm))
                          in-term)]))]
        [#t (error "Malformed term" in-term)]))

(module+ test
  (check-equal? (substitute 42 'x '(+ x 12)) '(+ 42 12))
  (check-equal? (substitute 'x 'y -23) -23)
  (check-equal? (substitute 42 'x '(λ (y) (+ y x)))
                '(λ (y) (+ y 42)))
  ;; Substitution stops when it hits shadowing
  (check-equal? (substitute 3 'x '(λ (x y z) x))
                '(λ (x y z) x))
  (check-equal? (substitute 3 'x '(Π ((x Integer)) x))
                '(Π ((x Integer)) x))
  (check-equal? (substitute 'Integer 'x '(Π ((x Integer) (y x))
                                            (= x y Integer)))
                '(Π ((x Integer) (y Integer))
                    (= x y Integer)))

  ;; Check capture-avoidance
  (check-equal? (substitute 'y 'x '(λ (y) (+ y x)))
                '(λ (y1) (+ y1 y)))
  (check-equal? (substitute 'y 'x '(Π ((y Integer)) x))
                '(Π ((y1 Integer)) y))
  (check-equal? (substitute 'y 'x '(⋂ ((y Integer)) x))
                '(⋂ ((y1 Integer)) y)))


;;;; Abbreviations for the full equality type
(define-match-expander is-type
  (lambda (stx)
    (syntax-case stx ()
      [(_ term)
       #'(list '=-in term term 'Type)]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ term)
       #'(list '=-in term term 'Type)])))

(define-match-expander has-type
  (lambda (stx)
    (syntax-case stx ()
      [(_ term type)
       #'(list '=-in term term type)]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ term type)
       #'(list '=-in term term type)])))

(define-match-expander =-type
  (lambda (stx)
    (syntax-case stx ()
      [(_ left right)
       #'(list '=-in left right 'Type)]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ left right)
       #'(list '=-in left right 'Type)])))



;;;; Contexts and hypothetical judgments

;;; Contexts are represented in reverse order because hypotheses are
;;; counted from the most-recent first, to make proof steps rely less
;;; on global knowledge
(define-type Context (Listof (List Symbol Term)))

;; Hypothetical judgments. The extracted term is represented
;; elsewhere.
(struct ⊢
  ([context : Context]
   [goal : Term])
  #:transparent)

(: split-context (-> Context
                     Natural (List Context
                                   (List Symbol Term)
                                   Context)))
(define (split-context context which-hypothesis)
  (if (>= which-hypothesis (length context))
      (error "Hypothesis out of range")
      (let*-values
          (((Δ rest)
            (split-at context which-hypothesis))
           ((this-hypothesis)
            (car rest))
           ((Γ)
            (cdr rest)))
        (list Δ this-hypothesis Γ))))




;;;; Refinement infrastructure

(struct exn:fail:refinement exn ([cant-refine : ⊢])
  #:transparent)

(: cant-refine (All (a) (-> ⊢ a)))
(define (cant-refine j)
  (raise (exn:fail:refinement
          (format "Refinement failure: ~a" j)
          (current-continuation-marks) j)))

(struct refinement
  ([new-goals : (Listof ⊢)]
   [extract : (-> (Listof Term) Term)])
  #:transparent)

(: refine-ax (-> (Listof ⊢) refinement))
(define (refine-ax subgoals) (refinement subgoals (λ (_) empty)))

(: refine-done (-> Term refinement))
(define (refine-done out)
  (refinement empty (λ (_) out)))

(: refine-done-ax refinement)
(define refine-done-ax
  (refinement empty (λ (_) empty)))

(define-type Rule (-> ⊢ refinement))

(define-syntax-rule (refinement-rule cases ...)
  (lambda (j) (match j cases ... [other (cant-refine other)])))

(define-syntax-rule (define-refinement-rule id cases ...)
  (begin
    (: id Rule)
    (define id (refinement-rule cases ...))))


;;;; Temporary bogus rules until universe levels are instituted
(: type-in-type Rule)
(define (type-in-type j)
  (match j
    [(⊢ Γ (is-type 'Type))
     refine-done-ax]
    [other (cant-refine other)]))


;;;; Structural rules

;;; Refinement failure if hypothesis index out of bounds
(: get-hypothesis (-> ⊢ Natural (List Symbol Term)))
(define (get-hypothesis sequent which)
  (let ((context (⊢-context sequent)))
    (if (>= which (length context))
        (cant-refine sequent)
        (list-ref context which))))



(: hypothesis (-> Natural Rule))
(define (hypothesis which-hypothesis)
  (lambda (j)
    (match-let (((list x ty) (get-hypothesis j which-hypothesis)))
      ;; conversion check for type in hypothesis
      (if (α-equiv? (map (lambda ([h : (List Symbol Term)])
                           (cons (car h) (car h)))
                         (drop (⊢-context j)
                               which-hypothesis))
                    ty
                    (⊢-goal j))
          (refine-done x)
          (cant-refine j)))))

(: hypothesis-equality (-> Natural Rule))
(define (hypothesis-equality which-hypothesis)
  (lambda (j)
    (match-let (((⊢ context (has-type x type)) j)
                ((list h hypothesis-type)
                 (get-hypothesis j which-hypothesis)))
      (cond ((not (equal? x h)) (cant-refine j))
            ((not (α-equiv? (map (lambda ([x : (List Symbol Term)])
                                   (cons (car x) (car x)))
                                 (drop (⊢-context j) which-hypothesis))
                            type
                            hypothesis-type))
             (cant-refine j))
            (else refine-done-ax)))))


;;;; The Equality Type



;;;; This theory uses the empty list as the canonical unit value. This
;;;; breaks somewhat with the Lisp tradition - ah well, it makes sense
;;;; because it can always be trivially constructed.

;;;; TODO - rules for Ax a la Nuprl



;;;; Function rules
(define-refinement-rule pi-f
  [(⊢ Γ (is-type term))
   #:when (well-formed-pi? term)
   (let ((args (pi-get-arguments term))
         (body (pi-get-body term)))
     (refinement
      (append
       ;; All the binder types are types
       (map (λ ([bind : (List Symbol Term)])
              (⊢ Γ (is-type (cadr bind))))
            args)
       ;; The body is a type
       (list (⊢ (append (reverse args)
                        Γ)
                (is-type body))))
      (λ ([extracts : (Listof Term)])
        `(Π ,((inst zip-with Symbol Term (List Symbol Term))
              (lambda ([x : Symbol] [ty : Term]) (list x ty))
              (map (inst car Symbol Term) args) extracts)
            ,(last extracts)))))])

(: lambda-intro (-> (Listof Symbol) Rule))
(define ((lambda-intro names) j)
  (match j
    [(⊢ Γ type)
     #:when (well-formed-pi? type)
     (let ((arguments (cadr type))
           (body (caddr type)))
       (if (not (= (length arguments) (length names)))
           (cant-refine j)
           (refinement
            (cons
             ;; The interesting new goal is to construct a body with
             ;; the right type, under suitably-named assumptions
             (⊢ (append
                 (reverse
                  (for/list : (Listof (List Symbol Term))
                            ([new-name : Symbol
                                       names]
                             [typed-binder : (List Symbol Term)
                                           arguments])
                    (list new-name (cadr typed-binder))))
                 Γ)
                (rename-free-variables
                 (for/fold : (HashTable Symbol Symbol)
                           ([renames : (HashTable Symbol Symbol)
                                     (hash)])
                           ([new-name names]
                            [typed-binder : (List Symbol Term)
                                          arguments])
                   (#{hash-set @ Symbol Symbol} renames
                    (car typed-binder)
                    new-name))
                 body))
             ;; The boring goals are to make sure that everything is
             ;; still a type
             (for/list : (Listof ⊢)
                       ([typed-binder arguments])
               (⊢ Γ (is-type (cadr typed-binder)))))
            ;; The extracted term is the extract of the new goal,
            ;; wrapped in the lambda
            (lambda (extracts) `(λ ,names ,(car extracts))))))]
    [other (cant-refine other)]))

(: pi-type-equality (-> (Listof Symbol) Rule))
(define ((pi-type-equality argument-names) j)
  ;; The empty rename set
  (: no-renames (HashTable Symbol Symbol))
  (define no-renames (hash))

  (match j
    [(⊢ Γ (=-type left right))
     #:when (and (well-formed-pi? left) (well-formed-pi? right))
     (let ((left-args (pi-get-arguments left))
           (left-body (pi-get-body left))
           (right-args (pi-get-arguments right))
           (right-body (pi-get-body right)))
       (if (= (length left-args) (length right-args))
           (refine-ax
            (append
             ;; the pairwise argument types are equal types
             (map (λ ([s : (List Symbol Term)]
                      [t : (List Symbol Term)])
                    (⊢ Γ (=-type (cadr s) (cadr t))))
                  left-args
                  right-args)
             ;; the body types are equal in the extended context,
             ;; using the names from the left type
             (list (⊢ (append ((inst reverse (List Symbol Term))
                               (for/list ([x : Symbol
                                             argument-names]
                                          [arg : (List Symbol Term)
                                               left-args])
                                 (list x (cadr arg))))
                              Γ)
                      (=-type
                       (rename-free-variables
                        (for/fold ([renames no-renames])
                                  ([from : (List Symbol Term)
                                         left-args]
                                   [to : Symbol
                                       argument-names])
                          (hash-set renames (car from) to))
                        left-body)
                       (rename-free-variables
                        (for/fold ([renames no-renames])
                                  ([from : (List Symbol Term)
                                         left-args]
                                   [to : Symbol
                                       argument-names])
                          (hash-set renames (car from) to))
                        right-body))))))
           (cant-refine j)))]
    [other (cant-refine other)]))


;;;; Integer rules

(: integer-formation Rule)
(define-refinement-rule integer-formation
  [(⊢ _ (is-type 'Integer))
   (refine-done 'Integer)])

(: integer-intro Rule)
(define-refinement-rule integer-intro
  [(⊢ _ (has-type i 'Integer))
   #:when (integer? i)
   (refine-done i)])

(define-refinement-rule int-type-eq
  [(⊢ _ (=-type 'Integer 'Integer))
   refine-done-ax])

(: integer-aritmetic-op Rule)
(define (integer-aritmetic-op j)
  ;; These arithmetic operators don't necessarily need an argument
  (define arith-ops '(+ *))
  ;; These operators need at least one argument
  (define arith-ops-need-arg '(- /))
  (match j
    [(⊢ Γ (has-type (cons op args) 'Integer))
     #:when (member op arith-ops)
     (refinement (map (λ ([arg : Term]) (⊢ Γ (has-type arg 'Integer)))
                      args)
                 (λ ([exts : (Listof Term)])
                   (cons op exts)))]
    [(⊢ Γ (has-type (cons op (cons arg1 args)) 'Integer))
     #:when (member op arith-ops-need-arg)
     (refinement (map (λ ([arg : Term]) (⊢ Γ (has-type arg 'Integer)))
                      (cons arg1 args))
                 (λ ([exts : (Listof Term)])
                   (cons op exts)))]
    [other (cant-refine other)]))


;;;; Rules for intersections

;;; An intersection is a type if all quantifiers are types and the
;;; body is a type given the extended context
(define-refinement-rule intersection-formation
  [(⊢ Γ (is-type term))
   #:when (well-formed-intersection? term)
   (let ((arguments (intersection-get-arguments term))
         (body (intersection-get-body term)))
     (refinement
      (append
       ;; First the quantified types need to actually be types
       (map (λ ([argument-binder : (List Symbol Term)])
              (⊢ Γ (is-type (cadr argument-binder))))
            arguments)

       ;; Also, the body needs to be a type given the bindings
       (list (⊢ (append (reverse arguments) Γ)
                (is-type body))))
      (λ (extracts) `(⋂ ,arguments ,(last extracts)))))])

;;; A term is an element of an intersection if it is a member of the
;;; body for any instantiation of the arguments.
(define-refinement-rule intersection-membership
  [(⊢ Γ type)
   #:when (well-formed-intersection? type)
   (let ((⋂-arguments (intersection-get-arguments type))
         (⋂-body (intersection-get-body type)))
     (refinement
      (cons (⊢ (append (reverse ⋂-arguments) Γ)
               ⋂-body)
            (map (lambda ([binding : (List Symbol Term)])
                   (⊢ Γ (is-type (cadr binding))))
                 ⋂-arguments))
        ;; The extract is the term itself
        car))])


;;; Intersections in the context can be instantiated freely with
;;; well-typed values for the arguments.
(: intersection-elimination (-> Natural (Listof Term)
                                Symbol Symbol
                                Rule))
(define (intersection-elimination which-hypothesis
                                  instantiations
                                  new-hypothesis
                                  equality-hypothesis)
  (lambda (hypothetical)
    (match hypothetical
      [(⊢ context judgment)
       #:when (< which-hypothesis (length context))
       (match-let (((list Δ (list x type) Γ)
                    (split-context context which-hypothesis)))
         (match type
           [(list '⋂ arguments body)
            #:when (typed-binding-list? arguments)
            (refinement
             (append
              ;; Each instantiation is well-typed
              (zip-with (lambda ([term : Term]
                                 [argument : (List Symbol Term)])
                          (⊢ context (has-type term (cadr argument))))
                        instantiations
                        arguments)
              ;; The original goal is provable
              (list
               (let ((new-type
                      (for/fold : Term
                                ([result : Term
                                         body])
                                ([argument : (List Symbol Term)
                                           arguments]
                                 [new-term : Term
                                           instantiations])
                        (substitute new-term
                                    (car argument)
                                    result))))
                 (⊢ (append Δ
                            (list
                             (list equality-hypothesis
                                   `(= ,new-hypothesis
                                       ,x
                                       ,new-type))
                             (list new-hypothesis
                                   new-type)
                             (list x type)
                               )
                              Γ)
                      judgment))))
               (lambda (extracts)
                 (let ((term (last extracts)))
                 ;;; TODO: understand why this is what it is in the
                 ;;; Nuprl manual
                   (substitute '() new-hypothesis term))))]
             [other (cant-refine hypothetical)]))]
        [other (cant-refine other)])))


;;;; Infrastructure for proofs

(define-type Proof-Step (U proof-goal proof-step))
(struct proof-goal ([goal : ⊢]) #:transparent)
(struct proof-step
  ([goal : ⊢]
   [by : Rule]
   [subgoals : (Listof Proof-Step)])
  #:transparent)

(: proof-statement (-> Proof-Step ⊢))
(define (proof-statement step)
  (match step
    [(proof-goal g) g]
    [(proof-step g _ _) g]))

(: proof-complete? (-> Proof-Step Boolean))
(define (proof-complete? prf)
  (and (proof-step? prf)
       (for/and ((subgoal (proof-step-subgoals prf)))
         (proof-complete? subgoal))))

(define-type Proof-Status (U proof-done proof-incomplete))
(struct proof-done ([extract : Term]) #:transparent)
(struct proof-incomplete ([remaining : (Listof ⊢)]) #:transparent)

(: all-complete (-> (Listof Proof-Status)
                    (U (Pairof #t (Listof Term))
                       (Pairof #f (Listof ⊢)))))
(define (all-complete results)
  (match results
    ['() (list #t)]
    [(cons x xs)
     (match* (x (all-complete xs))
       [((proof-done term) (cons #t terms))
        (cons #t (cons term terms))]
       [((proof-done term) (cons #f todos))
        (cons #f todos)]
       [((proof-incomplete todo) (cons #t _))
        (cons #f todo)]
       [((proof-incomplete todo) (cons #f todos))
        (cons #f (append todo todos))])]))

(: check-proof (-> Proof-Step Proof-Status))
(define (check-proof step)
  (match step
    [(proof-goal goal)
     (proof-incomplete (list goal))]
    [(proof-step goal rule subproofs)
     ;; First try to refine. If fail, fail.
     (match-let (((refinement subgoals extract) (rule goal)))
       ;; Check that there's the right number of subtrees.
       (if (not (= (length subgoals) (length subproofs)))
           (error "Mismatched goal count")
           (let ((to-check (zip subgoals subproofs)))
             ;; Now check that each sub-tree's head matches the
             ;; subgoal.  This is a straight syntactic equality.
             (for ((x to-check))
               (unless (equal? (car x) (proof-statement (cdr x)))
                 (error "Mismatched proof statements"
                        (car x) (cdr x))))
             ;; Sanity checking is done, accumulate the results
             (match (all-complete (map check-proof subproofs))
               [(cons #t subterms) (proof-done (extract subterms))]
               [(cons #f todos) (proof-incomplete todos)]))))]))

(module+ test
  (define proof-1
    (proof-step (⊢ empty (has-type '(+ 1 2 3) 'Integer))
                integer-aritmetic-op
                (list (proof-step (⊢ empty (has-type 1 'Integer))
                                  integer-intro
                                    empty)
                        (proof-step (⊢ empty (has-type 2 'Integer))
                                    integer-intro
                                    empty)
                        (proof-step (⊢ empty (has-type 3 'Integer))
                                    integer-intro
                                    empty))))
    (check-equal? (check-proof proof-1) (proof-done '(+ 1 2 3)))

    (define proof-2
      (proof-step (⊢ (list '(x Integer)) (has-type '(+ x 1) 'Integer))
                  integer-aritmetic-op
                  (list (proof-step (⊢ (list '(x Integer))
                                       (has-type 'x 'Integer))
                                    (hypothesis-equality 0)
                                    empty)
                        (proof-goal (⊢ (list '(x Integer))
                                       (has-type 1 'Integer))))))
    (check-equal? (check-proof proof-2)
                  (proof-incomplete (list (⊢ (list '(x Integer))
                                             (has-type 1 'Integer)))))
    (define proof-3
      (proof-step (⊢ empty
                     (=-type '(Π ([x Integer] [y Integer]) Integer)
                             '(Π ([y Integer] [x Integer]) Integer)))
                  (pi-type-equality '(n m))
                  (list (proof-step (⊢ empty
                                       (=-type 'Integer 'Integer))
                                    int-type-eq
                                    empty)
                        (proof-goal (⊢ empty
                                       (=-type 'Integer 'Integer)))
                        (proof-step (⊢ '([m Integer] [n Integer])
                                       (=-type 'Integer 'Integer))
                                    int-type-eq
                                    empty))))

    (check-equal? (check-proof proof-3)
                  (proof-incomplete
                   (list (⊢ '() (=-type 'Integer 'Integer)))))

    (define proof-4
      (proof-step (⊢ empty
                     '(⋂ ((t Type))
                         (Π ((y t))
                            t)))
                  intersection-membership
                  (list
                   (proof-step (⊢ '((t Type))
                                  '(Π ((y t)) t))
                               (lambda-intro '(x))
                               (list (proof-step
                                      (⊢ '((x t) (t Type))
                                         't)
                                      (hypothesis 0)
                                      empty)
                                     (proof-step
                                      (⊢ '((t Type))
                                         (is-type 't))
                                      (hypothesis-equality 0)
                                      empty)))
                   (proof-step (⊢ '() (is-type 'Type))
                               type-in-type
                               empty))
                  ))
  (check-equal? (check-proof proof-4)
                (proof-done '(λ (x) x))))


;; Local Variables:
;; whitespace-line-column: 70
;; eval: (whitespace-mode 1)
;; eval: (set-input-method "TeX")
;; End:
