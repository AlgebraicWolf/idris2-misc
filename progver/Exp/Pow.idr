module Pow

import Preloaded
import Data.Nat

%default total

-- The following lemma is useful
divMod2Lemma : (n : Nat) -> n = 2 * fst (divMod2 n) + if snd (divMod2 n) then 1 else 0
divMod2Lemma Z = Refl
divMod2Lemma (S Z) = Refl
divMod2Lemma (S (S k)) = case divMod2 k of
                              (q, False) => ?wut_2
                              (q, True) => ?wut_3

powEq : (b, e : Nat) -> powSqr b e = power b e
powEq b 0 = Refl
powEq b (S k) with (divMod2 (S k))
  powEq b (S k) | (q, r) = case r of
                                False => ?powEq_rhs_2
                                True => ?powEq_rhs_3

