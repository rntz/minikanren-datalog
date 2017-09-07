#lang racket

;; a rule is:
;;
;;  ((PRED ARG0 ... ARGN)   ;; <- the conclusion
;;   (PRED0 ARG ...)        ;; <- the premises
;;   ...
;;   (PREDN ARG ...))
;;
;; arguments are:
;;
;;    X           ;; variables, which are uppercase symbols
;;  | x           ;; atoms, which are lowercase symbols

(define (pr . args)
  (apply printf args)
  (newline))

(define (var? x)
  (and (symbol? x)
       (char-upper-case? (string-ref (symbol->string x) 0))))

(define (atom? x) (and (symbol? x) (not (var? x))))

;; "sets" of facts, implemented as lists
(define empty '())
(define (singleton x) (list x))
(define (union xs ys) (remove-duplicates (append xs ys)))
(define (unions xs) (remove-duplicates (append* xs)))
(define setof list)

;; substitutions, implemented as association lists
(define empty-subst '())

(define (lookup subst key
                [on-failure (lambda () (error "lookup failure"))]
                [on-success (lambda (x) x)])
  (match (assoc key subst eq?)
    [(cons _ r) (on-success r)]
    [_ (on-failure)]))

(define (update subst key value)
  ;; assumes key not yet bound in subst
  (cons (cons key value) subst))

(define (substitute term subst)
  (match term
    ['() '()]
    [(? var?) (lookup subst term (lambda () term))]
    [(? atom?) term]
    [(cons x xs)
     (cons (substitute x subst) (substitute xs subst))]))

;; returns #f on unification failure.
(define (unify subst args grounds)
  ;; (pr "unifying: ~a ~a ~a" subst args grounds)
  (cond
    [(eq? args grounds) subst]
    [(var? args)
     (lookup subst args
             ;; "failure", variable not yet bound
             (lambda () (update subst args grounds))
             ;; "success", variable already substituted for
             (lambda (v) (and (eq? v grounds) subst)))]
    [(and (cons? args) (cons? grounds))
     (unify (unify subst (car args) (car grounds))
            (cdr args) (cdr grounds))]
    [#t #f]))

(define (solve premises facts [subst empty-subst])
  (match premises
    ['() (singleton subst)]
    [(cons `(,pred . ,args) premises)
     ;; try to find (pred . args) in facts
     (unions
      (for/list ([fact facts] #:when (eq? (car fact) pred))
        (define new-subst (unify subst args (cdr fact)))
        (if new-subst
          (solve premises facts new-subst)
          empty)))]))

(define (fire rule facts)
  ;; Try to solve the premises.
  (define conclusion (car rule))
  (define premises (cdr rule))
  (unions
   (for/list ([s (solve premises facts)])
     (singleton (substitute conclusion s)))))

(define (step rules facts)
  (for ((rule rules))
    (set! facts (union facts (fire rule facts))))
  facts)

(define (deduce-all rules facts [limit #f])
  (let loop ([facts facts] [n 0])
    (and limit (< limit n) (error "over limit"))
    (define new-facts (step rules facts))
    ;; (pr "facts: ~v\nnew-facts: ~v\n" facts new-facts)
    ;; I'm not sure whether equal? is ok here, or whether we need set=?.
    (if (set=? facts new-facts)
        ;; fixed point reached!
        facts
        ;; otherwise, keep looping
        (loop new-facts (+ n 1)))))


;; some examples
(define some-facts
  (setof
   '(person bob) '(person john)
   '(loves bob john)))

(define some-rules
  (setof
   '((loves X X) (person X))))
