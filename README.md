# Datalog in minikanren

`datalog.rkt` is an implementation of Datalog (currently, without support for
negation) in minikanren. It has many comments and two examples (at the bottom of
the file).

`defunct-datalog.rkt` is an attempted implementation that didn't work out. Not
many comments, a few examples.

`datalog-interpreter.rkt` is a Datalog-without-negation interpreter in plain old
Racket, no minikanren. Not many comments, a few examples.

# TODOs

- Implement stratified negation.

- Maybe rewrite `datalog.rkt` without all the macros, if Will or other folks
  find them hard to read.

- See if there's a way to unify `query` and `query-all`; those seem kinda
  redundant. Maybe there's a way to do the fire-all-rules-at-once thing I was
  going for in `defunct-datalog.rkt`, the way `datalog-interpreter.rkt` does?
