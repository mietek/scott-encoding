module BoehmBerarducci

%default total

-- NOTE: Issues with scoped implicits:
-- https://github.com/idris-lang/Idris-dev/issues/2346


NatS : Type
NatS = {A : Type} -> (A -> A) -> A -> A

unNatS : {A : Type} -> (A -> A) -> A -> NatS -> A
unNatS f a s = s f a

succS : NatS -> NatS
succS s = \f, a => f (s f a)

zeroS : NatS
zeroS = \f, a => a

fromNatS : NatS -> Nat
fromNatS s = unNatS S Z s

-- NOTE: Issue #2346 / 1
toNatS : Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS

iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

test_iterated : (n : Nat) -> iterated n S Z = n
test_iterated (S n) = rewrite test_iterated n in Refl
test_iterated Z     = Refl

-- NOTE: Issue #2346 / 1
-- test_fromNatS : (n : Nat) -> fromNatS (iterated n succS zeroS) = n
-- test_fromNatS (S n) = rewrite test_fromNatS n in Refl
-- test_fromNatS Z     = Refl

-- TODO: Unknown issue
-- test_toNatS : (n : Nat) -> toNatS n = iterated n succS zeroS
-- test_toNatS (S n) = rewrite test_toNatS n in Refl
-- test_toNatS Z = Refl


ListS : Type -> Type
ListS A = {B : Type} -> (A -> B -> B) -> B -> B

unListS : {A, B : Type} -> (A -> B -> B) -> B -> ListS A -> B
unListS f b s = s f b

consS : {A : Type} -> A -> ListS A -> ListS A
consS a s = \f, b => f a (s f b)

nilS : {A : Type} -> ListS A
nilS = \f, b => b

fromListS : {A : Type} -> ListS A -> List A
fromListS s = unListS (::) [] s

-- NOTE: Issue #2346 / 1
toListS : {A : Type} -> List A -> ListS A
toListS (a :: aa) = consS a (toListS aa)
toListS []        = nilS
