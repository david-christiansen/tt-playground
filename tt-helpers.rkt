#lang typed/racket

(provide (all-defined-out))

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
