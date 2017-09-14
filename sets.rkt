#lang racket

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt")

(provide permute)

(define (permute X Y)
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

;; "L without duplicates is S."
;; this is wrong.
;;
;; (define-rules (nubo L S) (x xs S^)
;;   [('() '())]
;;   [((cons x xs) S)
;;    (rembero x S S^)
;;    (nubo xs S^)])
