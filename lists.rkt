#lang racket

(require "fast-mk/mk.rkt" "macros.rkt")

(provide (all-defined-out))

;; "L is a list all of whose members satisfy p."
;; `p` is not a logic variable but a unary relation parameter.
(define (forall L p)
  (matche L (x xs)
    ['()]
    [(cons x xs) (p x) (forall xs p)]))

;; "Appending the lists X and Y yields X++Y."
(define-rules (appendo X Y X++Y) (x xs rest)
  [('() Y Y)]
  [((cons x xs) Y (cons x rest)) (appendo xs Y rest)])

;; "The concatenation of Xs is Z."
(define-rules (concato Xs Z) (x xs z-tail)
  [('() '())]
  [((cons x xs) Z)
   (appendo x z-tail Z)
   (concato xs z-tail)])

;; "X is an element of the list L."
(define-rules (membero X L) (xs y ys)
  [(X (cons X xs))]
  [(X (cons y ys)) (=/= X y) (membero X ys)])

;; "X is not an element of the list L."
(define-rules (not-membero X L) (xs y ys)
  [(X '())]
  [(X (cons y ys)) (=/= X y) (not-membero X ys)])

;; "X is an element of L; removing the first occurrence of X gives L-without-X."
(define-rules (rembero X L L-without-X) (xs y ys)
  [(X (cons X xs) xs)]
  [(X (cons y xs) (cons y ys))
    (=/= X y)
    (rembero X xs ys)])

;; "Alist associates Key with Val."
(define-rules (assoco Key Val Alist) (k v rest)
  [(Key Val `((,Key ,Val) ,@rest))]
  [(Key Val `((,k ,v) ,@rest))
    (=/= Key k)
    (assoco Key Val rest)])

;; "Alist has no association for Key."
(define-rules (not-assoco Key Alist) (k v rest)
  [(Key '())]
  [(Key `((,k ,v) ,@rest))
   (=/= Key k)
   (not-assoco Key rest)])


;; Monadic operations. TODO: examples? use-cases?
(define (mapo r In Out)
  (matche* (In Out) (x xs y ys)
    [('() '())]
    [((cons x xs) (cons y ys))
     (r x y) (mapo r xs ys)]))

(define (bindo r In Out)
  (fresh (Tmp)
    (mapo r In Tmp)
    (concato Tmp Out)))
