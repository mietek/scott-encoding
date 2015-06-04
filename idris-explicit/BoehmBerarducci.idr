module BoehmBerarducci

%default total


NatQ : Type
NatQ = (A : Type) -> (A -> A) -> A -> A

unNatQ : {A : Type} -> (A -> A) -> A -> NatQ -> A
unNatQ f a q = q _ f a

succQ : NatQ -> NatQ
succQ q = \_, f, a => f (q _ f a)

zeroQ : NatQ
zeroQ = \_, f, a => a

fromNatQ : NatQ -> Nat
fromNatQ q = unNatQ S Z q

toNatQ : Nat -> NatQ
toNatQ (S n) = succQ (toNatQ n)
toNatQ Z     = zeroQ

iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

test_iterated : (n : Nat) -> iterated n S Z = n
test_iterated (S n) = rewrite test_iterated n in Refl
test_iterated Z     = Refl

test_fromNatQ : (n : Nat) -> fromNatQ (iterated n succQ zeroQ) = n
test_fromNatQ (S n) = rewrite test_fromNatQ n in Refl
test_fromNatQ Z     = Refl

test_toNatQ : (n : Nat) -> toNatQ n = iterated n succQ zeroQ
test_toNatQ (S n) = rewrite test_toNatQ n in Refl
test_toNatQ Z = Refl


ListQ : Type -> Type
ListQ A = (B : Type) -> (A -> B -> B) -> B -> B

unListQ : {A, B : Type} -> (A -> B -> B) -> B -> ListQ A -> B
unListQ f b q = q _ f b

consQ : {A : Type} -> A -> ListQ A -> ListQ A
consQ a q = \_, f, b => f a (q _ f b)

nilQ : {A : Type} -> ListQ A
nilQ = \_, f, b => b

fromListQ : {A : Type} -> ListQ A -> List A
fromListQ q = unListQ (::) [] q

toListQ : {A : Type} -> List A -> ListQ A
toListQ (a :: aa) = consQ a (toListQ aa)
toListQ []        = nilQ
