#lang typed/racket

;; This is me learning Racket by attempting to implement a somewhat
;; NuPRL-inspired system on top of it.
;; No guarantees are made as to the goodness of it.

(require racket/set)

(module+ test (require typed/rackunit))


;;;; Helpers - TODO: figure out racket idiom
(: zip (All (a b) (-> (Listof a) (Listof b) (Listof (Pair a b)))))
(define (zip l1 l2)
  (match* (l1 l2)
    [((cons x xs) (cons y ys))
     (cons (cons x y) (zip xs ys))]
    [(_ _) empty]))

(: zip-with (All (a b c)
                 (-> (-> a b c)
                     (Listof a)
                     (Listof b)
                     (Listof c))))
(define (zip-with f l1 l2)
  (match* (l1 l2)
    [((cons x xs) (cons y ys))
     (cons (f x y) (zip-with f xs ys))]
    [(_ _) empty]))



;;;; Terms are old-school Lisp terms for now
(define-type Term
  (U Symbol (Listof Term) Integer Null))

(define-type Well-Formed-Lambda
  (List 'λ (Listof Symbol) Term))

(define-type Well-Formed-Pi
  (List 'Π (Listof (List Symbol Term)) Term))

(define-predicate well-formed-pi? Well-Formed-Pi)

(: pi-get-arguments (-> Well-Formed-Pi (Listof (List Symbol Term))))
(define (pi-get-arguments term)
  (cadr term))

(: pi-get-body (-> Well-Formed-Pi Term))
(define (pi-get-body term)
  (caddr term))


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
    [(`(λ ,args1 ,body1) `(λ ,args2 ,body2))
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

    [(`(Π ,args1 ,body1) `(Π ,args2 ,body2))
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



;; Hypothetical judgments
(struct ⊢
  ([context : (Listof (List Symbol Term))]
   [judgment : Judgment])
  #:transparent)

;;;; Here we have the traditional four judgments of Martin-Löf type
;;;; theory, although in this style of type theory, they can all be
;;;; reduced to the equality judgment. That's done by
;;;; `simplify-judgment', which is used to see if two are
;;;; equivalent. The point of this is to maintain syntax in the form
;;;; that the user wrote it, but it will require a more complicated
;;;; equality process later. It might be better to internally treat
;;;; the others as abbreviations, then display them as simply as
;;;; possible.

(define-type Judgment (U is-type =-type has-type =-in))

(struct is-type
  ([term : Term])
  #:transparent)

(struct =-type
  ([type-1 : Term]
   [type-2 : Term])
  #:transparent)

(struct has-type
  ([term : Term]
   [type : Term])
  #:transparent)

(struct =-in
  ([left : Term]
   [right : Term]
   [in-type : Term])
  #:transparent)

(: simplify-judgment (-> Judgment Judgment))
(define (simplify-judgment j)
  (match j
    [(is-type ty) (=-in ty ty '(Univ i))]
    [(=-type t1 t2) (=-in t1 t2 '(Univ i))]
    [(has-type tm ty) (=-in tm tm ty)]
    [(=-in tm1 tm2 ty) (=-in tm1 tm2 ty)]))

(: judgment-equivalent? (-> (Listof Symbol)
                            Judgment
                            Judgment
                            Boolean))
(define (judgment-equivalent? hs j1 j2)
  (match* ((simplify-judgment j1) (simplify-judgment j2))
    [((=-in tm1 tm2 ty1) (=-in tm3 tm4 ty2))
     (and (α-equiv? (zip hs hs) tm1 tm2))]
    [(j1 j2) (error "Failed to simplify: ~a ~a" j1 j2)])) ;;todo


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

(define-syntax-rule (rule-match j (cases ...))
  (match j (cases ... [other (cant-refine other)])))


;;;; Structural rules
(: hypothesis (-> Natural Rule))
(define (hypothesis which-hypothesis)
  (lambda (j)
    (let ((ctxt (⊢-context j)))
      (if (>= which-hypothesis (length ctxt))
          (cant-refine j)
          (match-let ((`(,x ,ty) (list-ref ctxt which-hypothesis)))
            ;; conversion check for type in hypothesis
            (if (judgment-equivalent? (map (inst car Symbol Term)
                                           (drop ctxt
                                                 which-hypothesis))
                                      (has-type x ty)
                                      (⊢-judgment j))
                (refine-done x)
                (cant-refine j)))))))


;;;; Function rules
(: pi-f Rule)
(define (pi-f j)
  (match j
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
              ,(last extracts)))))
     ]
    [other (cant-refine other)]))

(: pi-type-equality (-> (Listof Symbol) Rule))
(define (pi-type-equality argument-names)
  ;; The empty rename set
  (: no-renames (HashTable Symbol Symbol))
  (define no-renames (hash))
  
  (lambda (j)
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
      [other (cant-refine other)])))


;;;; Integer rules

(: int-f Rule)
(define (int-f j)
  (match j
    [(⊢ _ (is-type 'Integer))
     (refine-done 'Integer)]
    [other (cant-refine other)]))

(: int-intro Rule)
(define (int-intro j)
  (match j
    [(⊢ _ (has-type i 'Integer))
     #:when (integer? i)
     (refine-done i)]
    [other (cant-refine other)]))

(: int-type-eq Rule)
(define (int-type-eq j)
  (match j
    [(⊢ _ (=-type 'Integer 'Integer))
     refine-done-ax]
    [other (cant-refine other)]))

(: int-intro-op Rule)
(define (int-intro-op j)
  (define arith-ops '(+ *))
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
                int-intro-op
                (list (proof-step (⊢ empty (has-type 1 'Integer))
                                  int-intro
                                  empty)
                      (proof-step (⊢ empty (has-type 2 'Integer))
                                  int-intro
                                  empty)
                      (proof-step (⊢ empty (has-type 3 'Integer))
                                  int-intro
                                  empty))))
  (check-equal? (check-proof proof-1) (proof-done '(+ 1 2 3)))

  (define proof-2
    (proof-step (⊢ (list '(x Integer)) (has-type '(+ x 1) 'Integer))
                int-intro-op
                (list (proof-step (⊢ (list '(x Integer))
                                     (has-type 'x 'Integer))
                                  (hypothesis 0)
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
                 (list (⊢ '() (=-type 'Integer 'Integer))))))

;; Local Variables:
;; whitespace-line-column: 70
;; eval: (whitespace-mode 1)
;; End:
