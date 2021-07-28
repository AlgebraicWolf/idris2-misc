Peirce : Type 
Peirce = (a : Type) -> (b : Type) -> ((a -> b) -> a) -> a

ExcludedMiddle : Type 
ExcludedMiddle = (a : Type) -> Either a (Not a)

DoubleNegationElim : Type 
DoubleNegationElim = (a : Type) -> Not (Not a) -> a 

Absurdity : Type 
Absurdity = (a : Type) -> (b : Type) -> (Not a -> Not b) -> b -> a 

DeMorganNotAndNot : Type 
DeMorganNotAndNot = (a : Type) -> (b : Type) -> Not (Not a, Not b) -> Either a b

ImpliesToOr : Type 
ImpliesToOr = (a : Type) -> (b : Type) -> (a -> b) -> Either (Not a) b

-- Unlike ImpliesToOr, inverse statement is constructive:
orToImplies : (a : Type) -> (b : Type) -> Either (Not a) b -> a -> b
orToImplies a b (Left f) y = absurd (f y) 
orToImplies a b (Right x) y = x

-- Inverse De Morgan is also constructive
deMorganOr : (a : Type) -> (b : Type) -> (Either a b -> Void) -> (a -> Void, b -> Void) 
deMorganOr a b f = (\x => f (Left x), \x => f (Right x))

%default total

magic : (a : Type) -> (Either a (Not a) -> Void) -> Either a (Not a)
magic a f = absurd (f $ Right left) where
  left : a -> Void
  left x = f $ Left x

proof1 : Peirce -> ExcludedMiddle
proof1 f a = f (Either a (Not a)) Void (magic a) 

proof2 : ExcludedMiddle -> DoubleNegationElim
proof2 f a g = case f a of
                    (Left x) => x
                    (Right x) => absurd (g x) 

proof3 : DoubleNegationElim -> Absurdity
proof3 f a b g x = f a (\t => g t x) 

proof4 : Absurdity -> DeMorganNotAndNot
proof4 f a b g = f (Either a b) ((a -> Void, b -> Void) -> Void) (\p, q => q (deMorganOr a b p)) g

proof5 : DeMorganNotAndNot -> ImpliesToOr
proof5 f a b g = f (Not a) b (\(fa, fb) => fa (fb . g))

lemma1 : ImpliesToOr -> ExcludedMiddle 
lemma1 f a = case f a a id of
                  (Left x) => Right x 
                  (Right x) => Left x 

lemma2 : ImpliesToOr -> DoubleNegationElim
lemma2 = proof2 . lemma1 

proof6 : ImpliesToOr -> Peirce
proof6 f a b g = let dn = lemma2 f 
                     in case f (a -> b) a g of
                              (Left h) => (dn a . fst) $ deMorganOr (a -> Void) b (h . (orToImplies a b))
                              (Right x) => x
