module Preloaded

%default total

public export
arithSum : Nat -> Nat
arithSum Z = Z
arithSum (S n) = S n + arithSum n

-- We define our own function for dividing a natural
-- number by 2. 
-- The existing Idris function divNatNZ
-- is not a good choice because it is impossible (correct
-- me if I my wrong) to prove many useful properties of
-- divNatNZ.
public export
half : Nat -> Nat
half (S (S n)) = S (half n)
half _ = Z

public export
arithFormula : Nat -> Nat
arithFormula n = half $ n * (n + 1)
