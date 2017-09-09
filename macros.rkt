#lang racket

(require "fast-mk/mk.rkt")

(provide matche* matche rules define-rules)

;; Some macros that make minikanren more concise and logic-programming-y.

(define-syntax-rule
  (matche* (examinee ...) (fresh-var ...)
           [(pat ...) body ...] ...)
  ;; With fresh variables (fresh-var ...), matches the tuple (examinee ...)
  ;; against the tuple-patterns (pat ...) ... in turn, executing the
  ;; corresponding (body ...) on a match.
  (fresh (fresh-var ...)
    (conde
      [(== examinee pat) ... body ...] ...)))

;; matche* for a single examinee.
(define-syntax-rule (matche examinee (fresh-var ...) [pat body ...] ...)
  (matche* (examinee) (fresh-var ...) [(pat) body ...] ...))

;; Makes a relation on (arg ...) by pattern-matching.
(define-syntax-rule (rules (arg ...) (fresh-var ...)
                           [(pat ...) body ...] ...)
  (lambda (arg ...)
    (matche* (arg ...) (fresh-var ...)
      [(pat ...) body ...] ...)))

;; Defines a relation (name arg ...) by pattern-matching.
(define-syntax-rule (define-rules (name arg ...) (fresh-var ...)
                      [(pat ...) body ...] ...)
  (define name
    (rules (arg ...) (fresh-var ...)
      [(pat ...) body ...] ...)))

 ;; Examples demonstrating the above:
(module+ examples

 ;; "Appending the lists X and Y yields X++Y."
 (define-rules (appendo X Y X++Y) (x xs rest)
   [('() Y Y)]
   [((cons x xs) Y (cons x rest)) (appendo xs Y rest)])

 ;; this is equivalent to:
 (define (appendo-2 X Y X++Y)
   (matche* (X Y X++Y) (x xs rest)
            [('() Y Y)]
            [((cons x xs) Y (cons x rest)) (appendo-2 xs Y rest)]))

 ;; which is equivalent to:
 (define (appendo-3 X Y X++Y)
   (fresh (x xs rest)
          (conde
           [(== X '()) (== Y Y) (== X++Y Y)]
           [(== X (cons x xs)) (== Y Y) (== X++Y (cons x rest)) (appendo-3 xs Y rest)])))

 ;; which after removing redundant uses of (== Y Y) is:
 (define (appendo-4 X Y X++Y)
   (fresh (x xs rest)
          (conde
           [(== X '()) (== Y X++Y)]
           [(== X (cons x xs)) (== X++Y (cons x rest)) (appendo-4 xs Y rest)])))

 ;; which, modulo placement of `fresh`, is identical to what you'd write by hand:
 (define (appendo-5 X Y X++Y)
   (conde
    [(== X '()) (== Y X++Y)]
    [(fresh (x xs rest)
            (== X (cons x xs)) (== X++Y (cons x rest)) (appendo-5 xs Y rest))])))
