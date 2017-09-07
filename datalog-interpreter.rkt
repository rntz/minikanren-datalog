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

(define (atom? x)
  (and (symbol? x)
       (char-lower-case? (string-ref (symbol->string x) 0))))

(define (var? x)
  (and (symbol? x) (not (atom? x))))

(define (substitute term subst)
  (match term
    ['() '()]
    [(? var?) (hash-ref subst term (lambda () term))]
    [(? atom?) term]
    [(cons x xs)
     (cons (substitute x subst) (substitute xs subst))]))

(define empty (set))
(define (singleton x) (set x))
(define (union xs ys) (set-union xs ys))
(define (unions xs) (apply set-union (set) xs))

;; returns #f on unification failure.
(define (unify subst args grounds)
  ;; (printf "unifying: ~a ~a ~a\n" subst args grounds)
  (cond
    [(eq? args grounds) subst]
    [(var? args)
     (if (hash-has-key? subst args)
         ;; already substituted for
         (and (eq? (hash-ref subst args) grounds) subst)
         ;; bind it
         (hash-set subst args grounds))]
    [(and (cons? args) (cons? grounds))
     (unify (unify subst (car args) (car grounds))
            (cdr args) (cdr grounds))]
    [#t #f]))

(define (solve premises facts [subst (hash)])
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
    ;; (printf "facts: ~v\nnew-facts: ~v\n\n" facts new-facts)
    (if (set=? facts new-facts)
        ;; fixed point reached!
        facts
        ;; otherwise, keep looping
        (loop new-facts (+ n 1)))))


;; some examples
(define some-facts
  (set
   '(person bob) '(person john)
   '(loves bob john)))

(define some-rules
  (set
   '((loves X X) (person X))))
