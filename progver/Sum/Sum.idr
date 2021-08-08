module Sum

import Preloaded
import Data.Nat

%default total

accElim : (acc : Nat) -> (f : Nat -> Nat) -> (n : Nat) -> sumAux acc f n = acc + sumAux 0 f n 
accElim acc f 0 = rewrite plusZeroRightNeutral acc in Refl
accElim acc f (S k) = rewrite plusZeroRightNeutral (f (S k)) in
                      rewrite accElim (f (S k)) f k in
                      rewrite plusAssociative acc (f (S k)) (sumAux 0 f k) in
                      rewrite plusCommutative acc (f (S k)) in
                              accElim (plus (f (S k)) acc) f k 

sumEq : (f : Nat -> Nat) -> (n : Nat) -> sumTail f n = sumSimple f n
sumEq f 0 = Refl
sumEq f (S k) = rewrite plusZeroRightNeutral (f (S k)) in 
                rewrite accElim (f (S k)) f k in 
                        plusConstantLeft _ _ _ $ sumEq f k 
