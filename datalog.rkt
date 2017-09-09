#lang racket

;; This is a datalog-without-negation interpreter in minikanren.
;;
;; Even if you already know minikanren, you'll want to read macros.rkt in order
;; to understand this file. lists.rkt defines some helper relations on lists.

(require "fast-mk/mk.rkt")
(require "macros.rkt" "lists.rkt")

 ;; Datatype definitions.

;; A term is:
;;
;;   (quote x)   ;; a variable, which is a quoted symbol
;; | x           ;; a constant, which is an unquoted symbol
;; | (M0 . M1)   ;; a pair of terms, the first of which is not 'quote
;; | ()          ;; an empty list
;;
;; An atom is a constant or ().
;;
;; A term is ground iff it contains no variables.
;;
;; An argument is a variable or a constant.
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

(define-rules (var?o X) (_) [(`(quote ,_))])
(define const?o symbolo)
(define (arg?o M) (conde [(var?o M)] [(const?o M)]))
(define (atom?o x) (conde [(const?o x)] [(== x '())]))

(define (term?o M)
  (conde [(arg?o M)]
         [(matche M (m0 m1)
            ['()]
            [(cons m0 m1) (=/= m0 'quote) (term?o m0) (term?o m1)])]))

(define-rules (fact?o F) (pred args)
  [((cons pred args)) (symbolo pred) (=/= pred 'quote) (forall args arg?o)])

(define (query?o Q) (forall Q fact?o))

;; TODO: groundo.

;; TODO: encode datalog's constraints on rules.
(define (rule?o R) (forall R fact?o))
(define (rules?o Rs) (forall Rs rule?o))

 ;; Substitutions as association lists.

;; "Setting K to V in S produces S-out."
;; Fails if K is already bound to some V2 =/= V.
(define-rules (assigno K V S S-out) ()
  [(K V S S) (assoco K V S)]
  [(K V S `((,K ,V) ,@S)) (not-assoco K S)])

;; "Applying the substitution S to the term X produces the term R."
(define-rules (substo S X R) (x0 x1 r0 r1)
  [(S X X) (atom?o X)]
  [(S X X) (var?o X) (not-assoco X S)]
  [(S X R) (var?o X) (assoco X R S)]
  [(S (cons x0 x1) (cons r0 r1))
    (=/= x0 'quote)
    (substo S x0 r0)
    (substo S x1 r1)])

;; There's some appropriate notion of "refutable relation" that would let me
;; combine `unifies` and `not-unifies` into one thing, but I can't figure out
;; exactly what it is.

;; "Under substitution S, term M unifies with ground term G, producing
;; substitution S-out."
(define-rules (unifies M G S S-out) (m0 m1 g0 g1 s^)
  [(M M S S) (atom?o M)]
  [(M G S S-out) (var?o M) (assigno M G S S-out)]
  [((cons m0 m1) (cons g0 g1) S S-out)
   (unifies m0 g0 S s^)
   (unifies m1 g1 s^ S-out)])

;; "Term M cannot unify with ground term G under substitution S."
(define-rules (not-unifies M G S) (m0 m1 g0 g1 s^)
  [(M G S) (atom?o M) (=/= M G)]
  [(M G S) (var?o M) (assoco M g0 S) (=/= G g0)]
  ;; note the extremely important check that m0 =/= 'quote.
  [((cons m0 m1) G S) (=/= m0 'quote) (atom?o G)]
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
   (fact?o conc) (query?o prems) ;; well-formedness; helps with rule synthesis.
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
