#lang racket

(require "fast-mk/mk.rkt" "macros.rkt")

(provide (all-defined-out))

(define-rules (list?o X) (x xs)
  [('())]
  [((cons x xs)) (list?o xs)])

(define-rules (length== X Y) (x xs y ys)
  [('() '())]
  [((cons x xs) (cons y ys)) (length== xs ys)])

;; "L is a list all of whose members satisfy p."
;; `p` is not a logic variable but a unary relation parameter.
(define (forallo L p)
  (matche L (x xs)
    ['()]
    [(cons x xs) (p x) (forallo xs p)]))

(define (existso L p)
  (matche L (x xs)
    [(cons x xs) (p x)]
    [(cons x xs) (existso xs p)]))

(define-syntax-rule (foralle x L body ...)
  (forallo L (lambda (x) (fresh () body ...))))

(define-syntax-rule (existse x L body ...)
  (existso L (lambda (x) (fresh () body ...))))

(define-syntax-rule
  (forall-matche L (fresh-vars ...) [pat body ...] ...)
  (foralle x L (matche x (fresh-vars ...) [pat body ...] ...)))

 ;; Basic list operations.
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
(define (membero X L) (existse Y L (== X Y)))

;; "X is not an element of the list L."
(define (¬membero X L) (foralle Y L (=/= X Y)))

;; "Inserting X somewhere in L gives L-with-X."
(define-rules (inserto X L L-with-X) (x xs ys)
  [(X L (cons X L))]
  [(X (cons x xs) (cons x ys)) (inserto X xs ys)])

;; "Removing the _first_ occurrence of X in L gives L-sans-X."
(define-rules (rembero X L L-sans-X) (xs y ys)
  [(X (cons X xs) xs)]
  [(X (cons y xs) (cons y ys))
    (=/= X y)
    (rembero X xs ys)])

 ;; Association lists.

;; "Alist associates Key with Val."
;;
;; In particular, searches for the *first* association of Key in Alist.
;; Otherwise this is just (membero (cons Key Val) Alist).
(define-rules (assoco Key Val Alist) (k v rest)
  [(Key Val `((,Key . ,Val) ,@rest))]
  [(Key Val `((,k . ,v) ,@rest))
    (=/= Key k)
    (assoco Key Val rest)])

;; "Alist has no association for Key."
(define (¬assoco Key Alist)
  (forall-matche Alist (k v)
     [(cons k v) (=/= Key k)]))

;; "Setting K to V in S produces S-out."
;; Fails if K is already bound to some V2 =/= V.
(define-rules (assigno K V S S-out) ()
  [(K V S S) (assoco K V S)]
  [(K V S `((,K . ,V) ,@S)) (¬assoco K S)])


;; Monadic operations. TODO: examples? use-cases?
(define (mapo A B rel)
  (matche* (A B) (x xs y ys)
    [('() '())]
    [((cons x xs) (cons y ys))
     (rel x y)
     (mapo xs ys rel)]))

(define (bindo In Out rel)
  (fresh (Tmp)
    ;; this seems optimized for going In -> Out.
    ;; what about Out -> In?
    (mapo In Tmp rel)
    (concato Tmp Out)))

;; bindo can be used to define forallo. I don't *think* it can be used to define
;; existso.
(define (weird-forallo L p)
  (bindo L '()
    (rules (x ys) () [(x '()) (p x)])))

;; an example test.
(define (weird-forallo-test1 [weird-forallo weird-forallo])
  (list
   (run 10 (X) (weird-forallo '(a a) (curry == X)))
   (run 10 (X) (weird-forallo '(a b) (curry == X)))))


;; Some old definitions.

;; (define (membero X L) (fresh (a b) (appendo a (cons X b) L)))

;; (define-rules (membero X L) (xs y ys)
;;   [(X (cons X xs))]
;;   [(X (cons y ys)) (=/= X y) (membero X ys)])

;; (define-rules (¬membero X L) (xs y ys)
;;   [(X '())]
;;   [(X (cons y ys)) (=/= X y) (¬membero X ys)])

;; (define-rules (¬assoco Key Alist) (k v rest)
;;   [(Key '())]
;;   [(Key `((,k . ,v) ,@rest))
;;    (=/= Key k)
;;    (¬assoco Key rest)])
