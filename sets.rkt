#lang racket

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt")

(provide permuteo remove-allo nubo nodupso subseto set==)

(define (permuteo X Y)
  (fresh () (length== X Y) (permute-helper X Y)))

(define-rules (permute-helper X Y) (x xs y ys xs^ ys^)
  [('() '())]
  ;; a small optimization.
  [((cons x xs) (cons x ys)) (permute-helper xs ys)]
  [((cons x xs) (cons y ys))
   (=/= x y)
   (rembero x ys ys^)
   (rembero y xs xs^)
   (permute-helper xs^ ys^)])

;; "L-sans-X is L without any Xes."
(define-rules (remove-allo X L L-sans-X) (y ys ys^)
  [(X '() '())]
  [(X (cons X ys) L-sans-X) (remove-allo X ys L-sans-X)]
  [(X (cons y ys) (cons y ys^)) (=/= X y) (remove-allo X ys ys^)])

;; "Y is X with only the first instance of each duplicate kept."
(define-rules (nubo X Y) (x xs xs^ ys)
  [('() '())]
  [((cons x xs) (cons x ys))
   (remove-allo x xs xs^)
   (nubo xs^ ys)])

;; a list has no duplicates iff its nub is itself.
(define (nodupso X) (nubo X X))

;; subseto and set== work perfectly well (in either direction) if you care about
;; *all* lists representing a set. but if you care about only duplicate-free
;; lists, I'm not sure...
(define (subseto A B) (forallo A (lambda (x) (membero x B))))
(define (set== A B) (fresh (X Y) (nubo A X) (nubo B Y) (permuteo X Y)))

;; ;; a different definition. probably slower? TODO: test.
;; (define (set==2 A B) (fresh () (subseto A B) (subseto B A)))
