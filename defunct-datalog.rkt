#lang racket

;; This is an abandoned datalog implementation in minikanren.
;;
;; It is buggy; I didn't spend enough time to figure out what was wrong.

(require "fast-mk/mk.rkt")

(define (appendo l s ls)
  (conde
   [(== '() l) (== s ls)]
   [(fresh (x rest rest+s)
      (== `(,x . ,rest) l)
      (== `(,x . ,rest+s) ls)
      (appendo rest s rest+s))]))

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

(define (atomo x) (conde [(symbolo x) (=/= x 'quote)] [(== x '())]))
(define (varo x) (fresh (y) (== x `(quote ,y))))


;; sets as lists.
(define (membero x ys)
  (fresh (y ys+)
    (== ys (cons y ys+))
    (conde
     [(== x y)]
     [(=/= x y) (membero x ys+)])))

(define (not-membero x ys)
  (conde
   [(== ys '())]
   [(fresh (y y+)
      (== ys (cons y y+))
      (=/= x y)
      (not-membero x y+))]))

(define (rembero x l out)
  (fresh (y rest)
    (== `(,y . ,rest) l)
    (conde
     [(== x y) (== rest out)]
     [(fresh (res)
             (=/= x y)
             (== `(,y . ,res) out)
             (rembero x rest res))])))

(define (subseto xs ys)
  (conde
    [(== xs '())]
    [(fresh (x xs+ ys-rest)
       (== xs (cons x xs+))
       (rembero x ys ys-rest)
       (subseto xs+ ys-rest))]))

(define (emptyo x) (== x '()))
(define (uniono both xs ys)
  (fresh ()
   (subseto xs both)
   (subseto ys both)
   (fresh (xys)
     (appendo xs ys xys)
     (subseto both xys))))


;;; Assoc lists
(define (assoco alist key value)
  (fresh (k v as)
    (== alist (cons (cons k v) as))
    (conde
     [(== k key) (== v value)]
     [(=/= k key) (assoco as key value)])))

;; (define (not-membero x ys)
;;   (conde
;;    [(== ys '())]
;;    [(fresh (y y+)
;;       (== ys (cons y y+))
;;       (=/= x y)
;;       (not-membero x y+))]))

(define (not-assoco alist key)
  (conde [(== alist '())]
         [(fresh (k v a+)
            (== alist `((,k . ,v) . ,a+))
            (=/= k key)
            (not-assoco a+ key))]))

(define (substo S term result)
  (conde
   [(atomo term) (== term result)]
   [(varo term) (assoco S term result)]
   [(varo term) (not-assoco S term) (== term result)]
   [(fresh (M0 M1 R0 R1)
      (== term (cons M0 M1))
      (== result (cons R0 R1))
      (substo S M0 R0)
      (substo S M1 R1))]))

(define (assigno S key value S^)
  (conde
   [(assoco S key value) (== S S^)]
   [(not-assoco S key) (== S^ `((,key . ,value) . ,S))]))

(define (unifyo S term ground S^)
  (conde
   [(atomo term) (atomo ground) (== term ground) (== S S^)]
   [(varo term) (assigno S term ground S^)]
   [(fresh (M0 M1 G0 G1 S1)
      (== term (cons M0 M1))
      (== ground (cons G0 G1))
      (unifyo S M0 G0 S1)
      (unifyo S1 M1 G1 S^))]))

;;; this feels shaky.
(define (not-unifyo S term ground)
  (conde
   [(atomo term) (atomo ground) (=/= term ground)]
   [(varo term) (fresh (X) (assoco S term X) (=/= X ground))]
   [(fresh (M0 M1 G0 G1 S1)
      (== term `(,M0 . ,M1))
      (== ground `(,G0 . ,G1))
      (conde [(not-unifyo S M0 G0)]
             [(unifyo S M0 G0 S1)
              (not-unifyo S1 M1 G1)]))]))


;;; Querying and such

;; This isn't used by anything, it's just a simple example.
(define (find-facto DB query-term substs)
  (conde
   [(== DB '()) (== substs '())]
   [(fresh (F F+ R0 R1)
      (== DB (cons F F+))
      (unifyo '() query-term F R0)
      (find-facto F+ query-term R1)
      (appendo R0 R1 substs))]
   [(fresh (F F+)
      (== DB (cons F F+))
      (not-unifyo '() query-term F)
      (find-facto F+ query-term substs))]))

(define (queryo DB result-term Q S results)
  (conde
   ;; if we're done, substitute the result-term and put it into results
   [(== Q '())
    (fresh (R)
     (substo S result-term R)
     (== results (list R)))]
   ;; otherwise, solve the first element of the query and recurse
   [(fresh (term Q+)
      (== Q `(,term . ,Q+))
      ;; try to find something unifying with term in facts
      (letrec ([loop (lambda (facts results)
                       (conde
                        [(== facts '()) (== results '())]
                        [(fresh (F F+ R0 R1 S^)
                           (== facts (cons F F+))
                           (unifyo S term F S^)
                           ;; recursively query with the updated substitution
                           (queryo DB result-term Q+ S^ R0)
                           ;; try the rest of the things
                           (loop F+ R1)
                           (uniono results R0 R1))]
                        [(fresh (F F+)
                           (== facts (cons F F+))
                           (not-unifyo S term F)
                           (loop F+ results))]))])
        (loop DB results)))]))

(define (fire DB rule results)
  (fresh (conc prems substs)
    (== rule (cons conc prems))
    (queryo DB conc prems '() results)))

(define (fire-all DB rules learned-facts)
  (conde
   [(== rules '()) (emptyo learned-facts)]
   [(fresh (rule rest-rules rule-results rest-rules-results)
      (== rules (cons rule rest-rules))
      (fire DB rule rule-results)
      (fire-all DB rest-rules rest-rules-results)
      (uniono learned-facts rule-results rest-rules-results))]))

(define (stepo DB rules DB^)
  (fresh (learned)
   (fire-all DB rules learned)
   (uniono DB^ DB learned)))

(define (step*o DB rules final-DB)
  (conde
   [(== DB final-DB)]
   [(fresh (DB^)
      (stepo DB rules DB^)
      (step*o DB^ rules final-DB))]))

(define (deduce-all DB rules final-DB)
  (fresh ()
    (step*o DB rules final-DB)
    (stepo final-DB rules final-DB)))


;;; some examples
(define some-facts
  (list
   '(person bob)
   '(person john)
   '(loves bob john)))

(define some-rules
  (list
   '((loves 'X 'X) (person 'X))))


;;; transitive closure on graphs
(define graph-facts
  (list
   '(edge a b) '(edge b a)))

(define graph-rules
  (list
   '((path 'X 'Y) (edge 'X 'Y))
   '((path 'X 'Y) (path 'X 'Y))))

