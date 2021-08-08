module Lookup

import Data.Nat

-- Consider the following type
data Lookup' : a -> List (a, b) -> Type where
  Here'  : (y : b) -> Lookup' x $ (x, y)::xys
  There' : Lookup' z xys -> Lookup' z $ (x, y)::xys

-- A term of type Lookup' x xys is a proof that there is an element in the xys
-- (which is a list of pairs) such that the first component of this element is
-- equal to x. Then the second component can be revealed using the function:

reveal' : Lookup' {b} x xys -> b
reveal' (Here' y) = y
reveal' (There' y) = reveal' y

-- If we were to try and write functions that require the compiler to infer
-- objects of type Lookup', we might notice that the compiler infers instance
-- for the leftmost pair that has the required value x:

example1 : (l : Lookup' {a = Nat} 0 $ (0, 0)::(1, 1)::(0, 2)::[]) => Integer
example1 = reveal' l -- = 0

example1_value : Lookup.example1 = 0
example1_value = ?example1_value_rhs

-- However, this is only caused by the algorithm used to infer term of Lookup
-- type, and we still can manually create other terms:

example2_1 : Lookup' {a = Nat} 0 $ (0, 1)::(1, 1)::(0, 2)::[]
example2_1 = There' (There' (Here' 2))

example2_2 : Integer
example2_2 = reveal' example2_1 -- = 2

-- Yet the observed behaviour might be useful, so we might want to design a
-- type that **guarantees** that the element is the leftmost one. Let's try to
-- do that

public export
data Lookup : a -> List (a, b) -> Type where
  -- When we attaching the element to the list it is obviously the leftmost one
  Here  : (y : b) -> Lookup x $ (x, y)::xys
  -- However, when we attach some other pair at the beginning of the list, we
  -- need to make sure that the first component of a newly attached pair is not
  -- equal to the first component of the pair Lookup is pointing to. We can
  -- achieve this by requiring uninhabitance constraint on type z = x:
  There : Lookup z xys -> Uninhabited (z = x) => Lookup z $ (x, y)::xys 

-- reveal function is implemented in the same fashion:
public export
reveal : Lookup {b} x xys -> b
reveal (Here y) = y
reveal (There y) = reveal y

-- Now we can verify that example with auto inference is still working: 
example3 : (l : Lookup {a = Nat} 0 $ (0, 0)::(1, 1)::(0, 2)::[]) => Integer
example3 = reveal l -- = 0

-- However, now we can not construct Lookup for the pair (0, 2), since the 
-- compiler can not infer Uninhabited (0 = 0) (would've been worrying if it
-- was able to)
-- example4_1 : Lookup {a = Nat} 0 $ (0, 0)::(1, 1)::(0, 2)::[]
-- example4_1 = There (There (Here 2)) -- This leads to error
