#lang racket

(require "fast-mk/mk.rkt")

(define (nullo x) (== x '()))

(define-syntax-rule (matche* (E ...) (V ...) [(P ...) Body ...] ...)
  (fresh (V ...)
    (conde
      [(== E P) ... Body ...] ...)))

(define-syntax-rule (matche E (V ...) [P Body ...] ...)
  (matche* (E) (V ...) [(P) Body ...] ...))

(define-syntax-rule (rules (V ...) [(P ...) Body ...] ...)
  (lambda args
    (matche args (V ...)
      [(list P ...) Body ...] ...)))

(define-syntax-rule (define-rules name (V ...) [(P ...) Body ...] ...)
  (define name (rules (V ...) [(P ...) Body ...] ...)))

(define-rules appendo (x xs ys rest)
  [('() rest rest)]
  [((cons x xs) ys (cons x rest)) (appendo xs ys rest)])


;; a rule is:
;;
;;  ((PRED ARG0 ... ARGN)   ;; <- the conclusion
;;   (PRED0 ARG ...)        ;; <- the premises
;;   ...
;;   (PREDN ARG ...))
;;
;; arguments are:
;;
;;    (quote x) ;; variables, which are quoted symbols
;;  | x         ;; atoms, which are symbols

(define-rules varo (_) [(`(quote ,_))])

(define (atomo x)
  (conde
   [(symbolo x) (=/= x 'quote)]
   [(nullo x)]))


;; Sets as lists
(define-rules membero (x xs y ys)
  [(x (cons x ys))]
  [(x (cons y ys)) (=/= x y) (membero x ys)])

;; (rembero x l l-without-x)
(define-rules rembero (e x xs y ys)
  [(e (cons e xs) xs)]
  [(e (cons x xs) (cons x ys))
    (=/= e x) (rembero e xs ys)])

(define-rules not-membero (x y ys)
  [(x '())]
  [(x (cons y ys)) (=/= x y) (not-membero x ys)])


;; Substitutions as association lists

;; (assoco key val subst)
(define-rules assoco (key val rest k v)
  [(key val `((,key ,val) ,@rest))]
  [(key val `((,k ,v) ,@rest))
    (=/= key k)
    (assoco key val rest)])

;; (not-assoco key subst)
(define-rules not-assoco (key rest k v)
  [(key '())]
  [(key `((,k ,v) ,@rest)) (=/= key k) (not-assoco key rest)])

;; (assigno key value subst subst-out)
(define-rules assigno (K V S)
  [(K V S S) (assoco K V S)]
  [(K V S `((,K ,V) ,@S)) (not-assoco K S)])

;; (substo subst term-in term-out)
(define-rules substo (S X R X0 X1 R0 R1)
  [(S X X) (atomo X)]
  [(S X X) (varo X) (not-assoco X S)]
  [(S X R) (varo X) (assoco X R S)]
  [(S (cons X0 X1) (cons R0 R1))
    (substo S X0 R0)
    (substo S X1 R1)])

;; (unifies term ground S S-out)
(define-rules unifies (M G S S1 S2 M0 M1 G0 G1)
  [(M M S S) (atomo M)]
  [(M G S S1) (varo M) (assigno M G S S1)]
  [((cons M0 M1) (cons G0 G1) S S2)
    (unifies M0 G0 S S1)
    (unifies M1 G1 S1 S2)])

;; (not-unifies term ground S)
(define-rules not-unifies (M G S S1 M0 M1 G0 G1)
  [(M G S) (atomo M) (=/= M G)]
  [((cons M0 M1) G) (atomo G)]
  [(M G S) (varo M) (assoco M G0 S) (=/= G G0)]
  [((cons M0 M1) (cons G0 G1) S)
   (conde
     [(not-unifies M0 G0 S)]
     [(unifies M0 G0 S S1) (not-unifies M1 G1 S1)])])



;; Querying

;; (query db query subst)
(define-rules query (DB Q QS S0 S1 fact)
  [(DB '() '())]
  [(DB (cons Q QS) S1)
    ;; solve the rest of the query
    (query DB QS S0)
    ;; find a fact in DB matching Q under S0.
    (membero fact DB)
    (unifies Q fact S0 S1)])


;; Stepping a datalog program
(define-rules apply-rule (DB conc prems result S)
  [(DB (cons conc prems) result)
    (query DB prems S)
    (substo S conc result)])

(define (apply-any DB rules result)
  (fresh (rule)
    (membero rule rules)
    (apply-rule DB rule result)))

(define-rules step (rules DB result)
  [(rules DB (cons result DB))
    (apply-any DB rules result)
    (not-membero result DB)])

(define-rules step* (rules DB DB1 DB2)
  [(rules DB DB)]
  [(rules DB DB2)
    (step rules DB DB1)
    (step* rules DB1 DB2)])


;; When is a model/database/set of facts stable? When no rules can fire productively.
(define (forall L p)
  (matche L (x xs)
    ['()]
    [(cons x xs) (p x) (forall xs p)]))

;; (query-all S term DB substs)
;;
;; `substs`: the list of all substitutions extending `S` which make `term` a
;; ground element of `DB`.
(define-rules query-all (S term DB substs fact S-out)
  [(S term '() '())]
  [(S term (cons fact DB) (cons S-out substs))
    (unifies term fact S S-out)
    ;; now, find the rest of the solutions
    (query-all S term DB substs)]
  [(S term (cons fact DB) substs)
    (not-unifies term fact S)
    (query-all S term DB substs)])

;; (nothing-new DB conc subst prems)
(define-rules nothing-new (DB conc S P PS result substs)
  [(DB conc S '())
    (substo S conc result)
    (membero result DB)]
  [(DB conc S (cons P PS))
    (query-all S P DB substs)
    (forall substs (lambda (s) (nothing-new DB conc s PS)))])

;; (idempotent DB rule)
(define-rules idempotent (DB conc prems)
  [(DB (cons conc prems))
    (nothing-new DB conc '() prems)])

(define (stable rules DB)
  (forall rules (curry idempotent DB)))

(define (deduce-all rules init-DB final-DB)
  (fresh ()
    (step* rules init-DB final-DB)
    (stable rules final-DB)))


;; Some examples
(define p-facts '((person bob) (person john)))
(define self-love '((loves 'X 'X) (person 'X)))
(define p-rules (list self-love))

(define p-facts-saturated
  (append p-facts '((loves bob bob) (loves john john))))

(define (p-test1 [n 10])
  (run n (R) (step* p-rules p-facts R)))

(define (p-test2 [n 10])
  (run n (R) (deduce-all p-rules p-facts R)))


;;; Graph examples
(define g-facts '((edge a b) (edge b a)))
(define g-rules `(((path 'X 'Y) (edge 'X 'Y))
                  ((path 'X 'Z) (path 'X 'Y) (path 'Y 'Z))))

(define (g-test1 [n 10])
  (run n (R) (step* g-rules g-facts R)))

(define (g-test2 [n 10])
  (run n (R) (deduce-all g-rules g-facts R)))
