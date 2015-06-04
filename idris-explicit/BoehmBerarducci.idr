module BoehmBerarducci

%default total


NatS : Type
NatS = (A : Type) -> (A -> A) -> A -> A

unNatS : {A : Type} -> (A -> A) -> A -> NatS -> A
unNatS f a s = s _ f a

succS : NatS -> NatS
succS s = \_, f, a => f (s _ f a)

zeroS : NatS
zeroS = \_, f, a => a

fromNatS : NatS -> Nat
fromNatS s = unNatS S Z s

toNatS : Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS

iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

test_iterated : (n : Nat) -> iterated n S Z = n
test_iterated (S n) = rewrite test_iterated n in Refl
test_iterated Z     = Refl

test_fromNatS : (n : Nat) -> fromNatS (iterated n succS zeroS) = n
test_fromNatS (S n) = rewrite test_fromNatS n in Refl
test_fromNatS Z     = Refl

test_toNatS : (n : Nat) -> toNatS n = iterated n succS zeroS
test_toNatS (S n) = rewrite test_toNatS n in Refl
test_toNatS Z = Refl


ListS : Type -> Type
ListS A = (B : Type) -> (A -> B -> B) -> B -> B

unListS : {A, B : Type} -> (A -> B -> B) -> B -> ListS A -> B
unListS f b s = s _ f b

consS : {A : Type} -> A -> ListS A -> ListS A
consS a s = \_, f, b => f a (s _ f b)

nilS : {A : Type} -> ListS A
nilS = \_, f, b => b

fromListS : {A : Type} -> ListS A -> List A
fromListS s = unListS (::) [] s

toListS : {A : Type} -> List A -> ListS A
toListS (a :: aa) = consS a (toListS aa)
toListS []        = nilS
