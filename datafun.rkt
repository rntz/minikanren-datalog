#lang racket

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt")

(define (¬specialo form)
  (fresh ()
    (=/= form 'lambda)
    (=/= form 'quote)
    ;; TODO
    ))

(define (idento form) (symbolo form) (¬specialo form))

(define (evalo expr val [env '()])
  (matche expr (x body form arg arg-val env^)
    ;; variable lookup
    [expr (idento expr) (assoco expr val env)]
    ;; quoted stuff
    [`',val (absento 'closure val)]
    ;; lambda.
    [`(lambda (,x) ,body)
     (idento x)
     (== val `(closure ,x ,body ,env))]
    ;; set operations
    ;; fixed points
    ;; function application
    [`(,form ,arg)
     (¬specialo form)
     (evalo form `(closure ,x ,body ,env^) env)
     (evalo arg  arg-val env)
     (evalo body val `((,x . ,arg-val) . ,env^))]))
