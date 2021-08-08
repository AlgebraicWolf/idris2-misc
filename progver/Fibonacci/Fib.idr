module Fib

import Preloaded
import Data.Nat

%default total

fibAuxLemma : (a : Nat) -> (b : Nat) -> (k : Nat) -> plus (fibAux a b (S k)) (fibAux a b k) = fibAux b (a + b) (S k)
fibAuxLemma a b Z = plusCommutative _ _
fibAuxLemma a b (S k) = fibAuxLemma b (plus a b) k

fibEq : (n : Nat) -> fib n = fib2 n
fibEq Z = Refl
fibEq (S Z) = Refl
fibEq (S (S k)) = rewrite fibEq k in
                  rewrite fibEq (S k) in
                      fibAuxLemma 0 1 k

