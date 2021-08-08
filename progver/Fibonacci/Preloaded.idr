module Preloaded

%default total

public export
fib : Nat -> Nat
fib Z = Z
fib (S Z) = S Z
fib (S (S n)) = fib (S n) + fib n

public export 
fibAux : Nat -> Nat -> Nat -> Nat
fibAux a b Z = a
fibAux a b (S n) = fibAux b (a + b) n

public export
fib2 : Nat -> Nat
fib2 = fibAux 0 1

