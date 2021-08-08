module Preloaded

%default total

public export
sumSimple : (Nat -> Nat) -> Nat -> Nat
sumSimple _ Z = Z
sumSimple f (S n) = f (S n) + sumSimple f n

public export
sumAux : Nat -> (Nat -> Nat) -> Nat -> Nat
sumAux acc _ Z = acc
sumAux acc f (S n) = sumAux (f (S n) + acc) f n

public export
sumTail : (Nat -> Nat) -> Nat -> Nat
sumTail = sumAux 0
