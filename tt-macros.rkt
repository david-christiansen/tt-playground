#lang racket

(provide (all-defined-out))

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

(define-match-expander =-in
  (lambda (stx)
    (syntax-case stx ()
      [(_ left right type)
       #'(list '=-in left right type)]))
  (lambda (stx)
    (syntax-case stx ()
      [(_ left right type)
       #'(list '=-in left right type)])))
