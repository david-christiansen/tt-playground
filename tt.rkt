#lang typed/racket

;; This is me learning Racket by attempting to implement a somewhat
;; NuPRL-inspired system on top of it.
;; No guarantees are made as to the goodness of it.

(provide (all-defined-out))

(require racket/set)
(require "tt-helpers.rkt")
(require "terms.rkt")
(require "tt-macros.rkt")

(module+ test (require typed/rackunit))



;;;; Pattern synonym for the is-value type

(define-match-expander is-value
  (lambda (stx)
    (syntax-case stx ()
      [(_ term type)
       #'(list 'is-value term type)]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ term type)
       #'(list 'is-value term type)])))


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

;;; Readable name for sequents
(define-type Sequent ⊢)

(define-predicate sequent? Sequent)

(: split-context (-> Context
                     Natural
                     (List Context
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

(struct exn:fail:refinement exn:fail ([cant-refine : Sequent])
  #:transparent)

(: cant-refine (All (a) (-> Sequent a)))
(define (cant-refine j)
  (raise (exn:fail:refinement
          (format "Refinement failure: ~a" j)
          (current-continuation-marks) j)))

(struct refinement
  ([new-goals : (Listof Sequent)]
   [extract : (-> (Listof Term) Term)])
  #:transparent)

(: refine-ax (-> (Listof Sequent) refinement))
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




;;;; The Equality Type

(: equality-formation (-> Term Rule))
(define (equality-formation type)
  (refinement-rule
   [(⊢ Γ 'Type)
    (refinement (list (⊢ Γ (is-type type))
                      (⊢ Γ type)
                      (⊢ Γ type))
                (lambda (extracts)
                  (=-in
                   (second extracts)
                   (third extracts)
                   (first extracts))))]))

;; TODO: consider an explicit representation of one-hole contexts
;; rather than using a free variable in a term as here. This might be
;; nice for doing computation rules as well.
(: substitute-using (-> Term Symbol Term Rule))
(define (substitute-using equality x context)
  (match equality
    [(=-in left right type)
     (refinement-rule
      [(⊢ Γ term)
       #:when (α-equiv? (map (lambda ([b : (List Symbol Term)])
                               (cons (car b) (car b)))
                             Γ)
                        term
                        (substitute left x context))
       (refinement
        (list (⊢ Γ (=-in left right type))
              (⊢ Γ (substitute right x context))
              (⊢ (cons (list x type) Γ) (is-type context)))
        second)])]
    [_ cant-refine]))

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


;;;; The empty type is called Absurd, to avoid confusion with the
;;;; Racket notion of void.
(define-refinement-rule absurd-formation
  [(⊢ Γ Type)
   (refine-done 'Absurd)])

(define-refinement-rule absurd-equality
  [(⊢ Γ (=-type 'Absurd 'Absurd))
   refine-done-ax])

(define-refinement-rule crash-equality
  [(⊢ Γ (=-in (list 'error left) (list 'error right) type))
   (refine-ax (list (⊢ Γ (=-in left right 'Absurd))))])

(: ex-falso-quodlibet (-> Natural Rule))
(define (ex-falso-quodlibet which-hypothesis)
  (refinement-rule
   [(⊢ context goal)
    #:when (< which-hypothesis (length context))
    ;; TODO: rewrite as view pattern
    (match (split-context context which-hypothesis)
      [(list Δ (list x 'Absurd) Γ)
       (refine-done `(error ,x))]
      [other (cant-refine (⊢ context goal))])]))



;;;; This theory uses the empty list as the canonical unit value. This
;;;; breaks somewhat with the Lisp tradition - ah well, it makes sense
;;;; because it can always be trivially constructed.

;;;; TODO - rules for Ax a la Nuprl



;;;; List rules
(define-refinement-rule list-formation
  [(⊢ Γ 'Type)
   (refinement (list (⊢ Γ 'Type)) (lambda (t) `(Listof ,t)))])

(define-refinement-rule list-equality
  [(⊢ Γ (=-type (list 'Listof left) (list 'Listof right)))
   (refine-ax (list (⊢ Γ (=-type left right))))])

(define-refinement-rule nil-equality
  [(⊢ Γ (=-in empty empty (list 'Listof type)))
   (refine-ax (list (⊢ Γ (is-type type))))])

(define-refinement-rule cons-equality
  [(⊢ Γ (=-in (list 'cons x xs)
              (list 'cons y ys)
              (list 'Listof type)))
   (refine-ax (list (⊢ Γ (=-in x y type))
                    (⊢ Γ (=-in xs ys `(Listof ,type)))))])

(define-refinement-rule nil-formation
  [(⊢ Γ (list 'Listof type))
   (refinement (list (⊢ Γ (is-type type)))
               (lambda (_) 'empty))])

(define-refinement-rule cons-formation
  [(⊢ Γ (list 'Listof type))
   (refinement (list (⊢ Γ type)
                     (⊢ Γ `(Listof ,type)))
               (lambda (extracts)
                 `(cons ,(car extracts) ,(cadr extracts))))])


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
             (for/list : (Listof Sequent)
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

(define-refinement-rule integer-formation
  [(⊢ _ (is-type 'Integer))
   (refine-done 'Integer)])

(define-refinement-rule integer-constant-value
  [(⊢ _ (is-value i 'Integer))
   #:when (integer? i)
   refine-done-ax])

(define-refinement-rule integer-constant-equality
  [(⊢ _ (has-type i 'Integer))
   #:when (integer? i)
   (refine-done i)])

(define-refinement-rule integer-type-equality
  [(⊢ _ (=-type 'Integer 'Integer))
   refine-done-ax])

;; These arithmetic operators don't necessarily need an argument
(define arith-ops '(+ *))
;; These operators need at least one argument
(define arith-ops-need-arg '(- /))


(: integer-arithmetic-op-formation (-> Symbol Natural Rule))
(define (integer-arithmetic-op-formation op argument-count)
  (refinement-rule
   [(⊢ Γ 'Integer)
    #:when (or (member op arith-ops)
               (and (member op arith-ops-need-arg)
                    (> argument-count 0)))
    (refinement (for/list ([i (in-range 0 argument-count)])
                  (⊢ Γ 'Integer))
                (lambda (extracted)
                  (cons op extracted)))]))

(: integer-arithmetic-op-equality Rule)
(define-refinement-rule integer-arithmetic-op-equality
  [(⊢ Γ (=-in (cons op1 args1)
              (cons op2 args2)
              'Integer))
   #:when (and (member op1 arith-ops)
               (equal? op1 op2)
               (well-formed-application? args1)
               (well-formed-application? args2)
               (= (length args1) (length args2)))
   (refine-ax (for/list : (Listof Sequent)
                        ([arg1 args1] [arg2 args2])
                (⊢ Γ (=-in arg1 arg2 'Integer))))]
  [(⊢ Γ (=-in (cons op1 args1)
              (cons op2 args2)
              'Integer))
   #:when (and (member op1 arith-ops-need-arg)
               (equal? op1 op2)
               (well-formed-application? args1)
               (pair? args1)
               (well-formed-application? args2)
               (pair? args2)
               (= (length args1) (length args2)))
   (refine-ax (for/list : (Listof Sequent)
                        ([arg1 args1] [arg2 args2])
                (⊢ Γ (=-in arg1 arg2 'Integer))))])


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

(define-namespace-anchor tt)

(: eval-rule (-> Any Rule))
(define (eval-rule code)
  ((cast eval (-> Any Namespace Rule))
   code
   (namespace-anchor->namespace tt)))

(define-type Proof-Step (U proof-goal proof-step))
(struct proof-goal ([goal : Sequent]) #:transparent)
(struct proof-step
  ([goal : Sequent]
   [by : Any] ;; code that should eval to a Rule
   [subgoals : (Listof Proof-Step)])
  #:transparent #:mutable)

(: refine-proof-goal (-> proof-goal Rule proof-step))
(define (refine-proof-goal goal rule)
  (match-let* ((goal-statement (proof-goal-goal goal))
               ((refinement subgoals extractor)
                ((eval-rule rule) goal-statement)))
    (proof-step goal-statement rule (map proof-goal subgoals))))

(: proof-statement (-> Proof-Step Sequent))
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
(struct proof-incomplete ([remaining : (Listof Sequent)]) #:transparent)

(: all-complete (-> (Listof Proof-Status)
                    (U (Pairof #t (Listof Term))
                       (Pairof #f (Listof Sequent)))))
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
     (match-let (((refinement subgoals extract)
                  ((eval-rule rule) goal)))
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
                'integer-arithmetic-op-equality
                (list (proof-step (⊢ empty (has-type 1 'Integer))
                                  'integer-constant-equality
                                  empty)
                      (proof-step (⊢ empty (has-type 2 'Integer))
                                  'integer-constant-equality
                                  empty)
                      (proof-step (⊢ empty (has-type 3 'Integer))
                                  'integer-constant-equality
                                  empty))))
    (check-equal? (check-proof proof-1) (proof-done '()))

    (define proof-2
      (proof-step (⊢ (list '(x Integer)) (has-type '(+ x 1) 'Integer))
                  'integer-arithmetic-op-equality
                  (list (proof-step (⊢ (list '(x Integer))
                                       (has-type 'x 'Integer))
                                    '(hypothesis-equality 0)
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
                  '(pi-type-equality '(n m))
                  (list (proof-step (⊢ empty
                                       (=-type 'Integer 'Integer))
                                    'integer-type-equality
                                    empty)
                        (proof-goal (⊢ empty
                                       (=-type 'Integer 'Integer)))
                        (proof-step (⊢ '([m Integer] [n Integer])
                                       (=-type 'Integer 'Integer))
                                    'integer-type-equality
                                    empty))))

    (check-equal? (check-proof proof-3)
                  (proof-incomplete
                   (list (⊢ '() (=-type 'Integer 'Integer)))))

    (define proof-4
      (proof-step (⊢ empty
                     '(⋂ ((t Type))
                         (Π ((y t))
                            t)))
                  'intersection-membership
                  (list
                   (proof-step (⊢ '((t Type))
                                  '(Π ((y t)) t))
                               '(lambda-intro '(x))
                               (list (proof-step
                                      (⊢ '((x t) (t Type))
                                         't)
                                      '(hypothesis 0)
                                      empty)
                                     (proof-step
                                      (⊢ '((t Type))
                                         (is-type 't))
                                      '(hypothesis-equality 0)
                                      empty)))
                   (proof-step (⊢ '() (is-type 'Type))
                               'type-in-type
                               empty))))
  (check-equal? (check-proof proof-4)
                (proof-done '(λ (x) x))))


;; Local Variables:
;; whitespace-line-column: 70
;; eval: (whitespace-mode 1)
;; eval: (set-input-method "TeX")
;; End:
