module ArithSeq

import Preloaded
import Data.Nat

%default total

onePlusSucc : (n : Nat) -> n + 1 = S n
onePlusSucc n = rewrite plusCommutative n 1 in Refl

halfLemma : (n : Nat) -> (m : Nat) -> half (plus n (plus n m)) = plus n (half m)
halfLemma 0 m = Refl
halfLemma (S k) m = rewrite sym (plusSuccRightSucc k (plus k m)) in
                    let indStep = halfLemma k m in eqSucc _ _ indStep

arithEq : (n : Nat) -> arithFormula n = arithSum n
arithEq 0 = Refl
arithEq (S k) = rewrite onePlusSucc k in
                rewrite multRightSuccPlus k (S k) in
                rewrite halfLemma k (mult k (S k)) in
                let indStep : (half (mult k (S k)) = arithSum k) = rewrite sym (onePlusSucc k) in arithEq k in
                    eqSucc _ _ $ plusConstantLeft _ _ _ indStep
