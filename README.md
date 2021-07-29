# Simple Elaborator

Closely follows [this paper](http://www.cse.chalmers.se/~ulfn/papers/meta-variables.pdf). It additionally implements implicit arguments, which are only touched upon in the paper.

This project is to verify the utility of the locally nameless approach in actual elaboration programs.

The tests in `Spec.hs` basically fiddles around with the `flip` function.

```
flip : {A : Set} -> (A -> A -> A) -> (A -> A -> A)
flip = \{A} -> \f -> \x -> \y -> f y x
flip' = \f -> \x -> \y -> f y x
flip'' = \f -> \x -> \y -> flip' f x y

flipGeneral : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
flipGeneral = \f -> \x -> \y -> f y x
flipGeneral' = \f -> \x -> \y -> flipGeneral f x y
flip''' = \f -> \x -> \y -> flipGeneral f x y
```
