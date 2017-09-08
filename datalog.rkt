#lang racket

;; This is a datalog-without-negation interpreter in minikanren.

(require "fast-mk/mk.rkt")

 ;; Some macros that make minikanren more concise and logic-programming-y.

;; With fresh variables (fresh-var ...), matches the tuple (examinee ...)
;; against the tuple-patterns (pat ...) ... in turn, executing the corresponding
;; (body ...) on a match.
(define-syntax-rule
  (matche* (examinee ...) (fresh-var ...)
    [(pat ...) body ...] ...)
  (fresh (fresh-var ...)
    (conde
      [(== examinee pat) ... body ...] ...)))

;; matche for a single examinee.
(define-syntax-rule (matche examinee (fresh-var ...) [pat body ...] ...)
  (matche* (examinee) (fresh-var ...) [(pat) body ...] ...))

;; Constructs a relation on (arg ...) by immediately matching against (arg ...).
(define-syntax-rule
  (rules (arg ...) (fresh-var ...)
    [(pat ...) body ...] ...)
  (lambda (arg ...)
    (matche* (arg ...) (fresh-var ...)
      [(pat ...) body ...] ...)))

;; Defines a relation (name arg ...) by immediately matching against (arg ...).
(define-syntax-rule
  (define-rules (name arg ...) (fresh-var ...)
    [(pat ...) body ...] ...)
  (define name
    (rules (arg ...) (fresh-var ...)
      [(pat ...) body ...] ...)))

 ;; An example demonstrating the above:
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
       (== X (cons x xs)) (== X++Y (cons x rest)) (appendo-5 xs Y rest))]))

 ;; Some more examples:
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

 ;; Datatype definitions.

;; A term is:
;;
;;   (quote x)   ;; a variable, which are quoted symbols
;; | x           ;; an atom, which is an unquoted symbol
;; | (M0 . M1)   ;; a pair of terms
;; | ()          ;; an empty list
;;
;; A ground term is one which contains no variables.
;;
;; An argument is a term which is either a variable or an atom.
;;
;; A fact is a term of the form (pred ARG...) where pred is a symbol and
;; ARG... is a list of arguments.
;;
;; A query is a list of facts, ((pred0 ARGS0 ...) ... (predn ARGSN ...)).
;;
;; A rule is of the form: (HEAD . QUERY) where HEAD is a fact and QUERY is a
;; query. In Datalog, only certain rules are valid. TODO: describe Datalog's
;; restrictions on rules. TODO: implement a minikanren relation detecting
;; valid/invalid rules.
;;
;; A database is a set (list without duplicates) of ground facts.

(define-rules (varo X) (_) [(`(quote ,_))])
(define (atomo x)
  (conde
   ;; is (=/= x 'quote) important, given that we have that constraint in
   ;; not-unifies and substo?
   [(symbolo x) #;(=/= x 'quote)]
   [(== x '())]))

 ;; Substitutions as association lists.

;; "Setting K to V in S produces S-out."
;; Fails if K is already bound to some V2 =/= V.
(define-rules (assigno K V S S-out) ()
  [(K V S S) (assoco K V S)]
  [(K V S `((,K ,V) ,@S)) (not-assoco K S)])

;; "Applying the substitution S to the term X produces the term R."
(define-rules (substo S X R) (x0 x1 r0 r1)
  [(S X X) (atomo X)]
  [(S X X) (varo X) (not-assoco X S)]
  [(S X R) (varo X) (assoco X R S)]
  [(S (cons x0 x1) (cons r0 r1))
    (=/= x0 'quote)
    (substo S x0 r0)
    (substo S x1 r1)])

;; "Under substitution S, term M unifies with ground term G, producing
;; substitution S-out."
(define-rules (unifies M G S S-out) (m0 m1 g0 g1 s^)
  [(M M S S) (atomo M)]
  [(M G S S-out) (varo M) (assigno M G S S-out)]
  [((cons m0 m1) (cons g0 g1) S S-out)
   (unifies m0 g0 S s^)
   (unifies m1 g1 s^ S-out)])

;; "Term M cannot unify with ground term G under substitution S."
(define-rules (not-unifies M G S) (m0 m1 g0 g1 s^)
  [(M G S) (atomo M) (=/= M G)]
  [(M G S) (varo M) (assoco M g0 S) (=/= G g0)]
  ;; note the extremely important check that m0 =/= 'quote.
  [((cons m0 m1) G S) (=/= m0 'quote) (atomo G)]
  [((cons m0 m1) (cons g0 g1) S)
   (conde
     [(not-unifies m0 g0 S)]
     [(unifies m0 g0 S s^) (not-unifies m1 g1 s^)])])

 ;; Stepping datalog programs / nondeterministically deriving new facts

;; "In database DB, substitution S satisfies Query."
(define-rules (query DB Query S) (Q Qs S0 fact)
  [(DB '() '())]
  [(DB (cons Q Qs) S)
    ;; solve the rest of the query
    (query DB Qs S0)
    ;; find a fact in DB matching Q under S0.
    (membero fact DB)
    (unifies Q fact S0 S)])

;; "Applying `rule` derives the ground fact `fact` from the facts in `DB`."
(define-rules (apply-rule rule DB fact) (conc prems S)
  [((cons conc prems) DB fact)
   ;; satisfy prems with substitution S.
   (query DB prems S)
   ;; then apply S to the conclusion.
   (substo S conc fact)])

;; "Applying a rule in `rules` to `DB` yields the strictly larger database DB^."
(define-rules (step rules DB DB^) (fact rule)
  [(rules DB (cons fact DB))
   (membero rule rules)
   (apply-rule rule DB fact)
   ;; the fact must be new, to avoid duplicating facts.
   (not-membero fact DB)])

;; "Applying zero or more of `rules` to DB yields the larger database DB^."
(define-rules (step* rules DB DB^) (DB1)
  [(rules DB DB)] ;; we can do nothing if we want to
  ;; or we can take a step, possibly followed by more steps
  [(rules DB DB^) (step rules DB DB1) (step* rules DB1 DB^)])

 ;; Stable databases.
;; A Datalog program is done executing when the database is stable: no rule can
;; derive a fact that isn't already in the database.

;; "`solns` is a list of all substitutions extending `S` which make `term` a
;; ground element of `DB`."
(define-rules (query-all S term DB solns) (F Fs S^ S^s)
  ;; if there are no facts, there are no solutions.
  [(S term '() '())]
  ;; if a fact in DB unifies with term, we add the unifying substitution to our
  ;; output...
  [(S term (cons F Fs) (cons S^ S^s))
    (unifies term F S S^)
    ;; and proceed recursively.
    (query-all S term Fs S^s)]
  ;; If the fact doesn't unify, we ignore it and proceed recursively.
  [(S term (cons F Fs) solns)
    (not-unifies term F S)
    (query-all S term Fs solns)])

;; "L is a list all of whose members satisfy p."
;; `p` is not a logic variable but a unary relation parameter.
(define (forall L p)
  (matche L (x xs)
    ['()]
    [(cons x xs) (p x) (forall xs p)]))

;; "There is no solution to `query` extending `S` which, when substituted into
;; `conc`, yields a result that isn't already in `DB`."
;;
;; i.e. there's nothing new to be found here.
(define-rules (nothing-new DB S conc query) (term query-rest result substs)
  [(DB S conc '())
    (substo S conc result)
    (membero result DB)]
  [(DB S conc (cons term query-rest))
    (query-all S term DB substs)
    (forall substs (lambda (s) (nothing-new DB s conc query-rest)))])

;; "`rule` cannot deduce anything new in `DB`."
(define-rules (idempotent rule DB) (conc prems)
  [((cons conc prems) DB) (nothing-new DB '() conc prems)])

;; "`DB` is stable under the rules in `rules`."
(define (stable rules DB) (forall rules (lambda (rule) (idempotent rule DB))))

;; "Applying all rules in `rules` repeatedly to `init-DB` until it is stable
;; yields `final-DB`."
(define (deduce-all rules init-DB final-DB)
  (fresh ()
    (step* rules init-DB final-DB)
    (stable rules final-DB)))

 ;; A small example
(define p-facts '((person bob) (person john)))
(define self-love '((loves 'X 'X) (person 'X)))
(define p-rules (list self-love))

(define p-facts-saturated
  (append p-facts '((loves bob bob) (loves john john))))

(define (p-test0 [n 10]) (run n (R) (step p-rules p-facts R)))
(define (p-test1 [n 10]) (run n (R) (step* p-rules p-facts R)))
(define (p-test2 [n 10]) (run n (R) (deduce-all p-rules p-facts R)))

 ;; A graph example
(define g-facts '((edge a b) (edge b a)))
(define g-rules `(((path 'X 'Y) (edge 'X 'Y))
                  ((path 'X 'Z) (path 'X 'Y) (path 'Y 'Z))))

(define (g-test1 [n 10])
  (run n (R) (step* g-rules g-facts R)))

(define (g-test2 [n 10])
  (run n (R) (deduce-all g-rules g-facts R)))
