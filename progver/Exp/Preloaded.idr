module Preloaded

%default total

||| Divides a natural number by 2 and returns
||| the quotient and the remainder as a boolean value:
||| True = remainder is 1, False = remainder is 0.
public export 
divMod2 : Nat -> (Nat, Bool)
divMod2 Z = (Z, False)
divMod2 (S Z) = (Z, True)
divMod2 (S (S n)) = case divMod2 n of (q, r) => (S q, r)

-- The first argument (k) helps Idris to prove
-- that the function terminates.
public export
powSqrAux : Nat -> Nat -> Nat -> Nat
powSqrAux Z _ _ = 1
powSqrAux _ _ Z = 1
powSqrAux (S k) b e =
      case divMod2 e of
                   (e', False) => powSqrAux k (b * b) e'
                   (e', True) => b * powSqrAux k (b * b) e'

public export 
powSqr : Nat -> Nat -> Nat
powSqr b e = powSqrAux e b e
