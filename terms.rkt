#lang typed/racket

(require "tt-helpers.rkt")

(provide intersection-get-arguments
         intersection-get-body
         rename-free-variables
         pi-get-arguments
         pi-get-body
         substitute
         Term
         term?
         typed-binding-list?
         well-formed-application?
         well-formed-intersection?
         well-formed-pi?
         α-equiv?)

(module+ test (require typed/rackunit))

;;;; Terms are old-school Lisp terms for now
(define-type Term
  (U Symbol (Pairof Term Term) Integer Null))

(define-predicate term? Term)

(define-type Well-Formed-Application (Listof Term))
(define-predicate well-formed-application? Well-Formed-Application)

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
    [(? well-formed-application? xs)
     (foldr combine
            no-vars
            (map free-variables xs))]
    [(? symbol? x) (set x)]
    [(? integer?) no-vars]
    [other (error "Malformed term" other)]))

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
                         (zip-with (lambda ([x : Symbol] [y : Symbol])
                                     (cons x y))
                                   args1
                                   args2)
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
                           (zip-with (inst cons Symbol Symbol)
                                     names1
                                     names2)
                           context)
                          body1
                          body2)))
         #f)]

    [(app1 app2)
     #:when (and (well-formed-application? app1)
                 (well-formed-application? app2))
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
     #:when (well-formed-application? application)
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
                        [#t (error "Malformed term: bad binder"
                                   in-term)])]
                 [(well-formed-application? in-term)
                  (map (lambda ([subterm : Term])
                         (substitute new-term name subterm))
                       in-term)]
                 [else (error "Malformed term: not a list"
                              in-term)]))]
        [#t (error "Malformed term ~a" in-term)]))

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


