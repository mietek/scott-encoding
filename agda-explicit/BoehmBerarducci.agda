module BoehmBerarducci where

open import Data.Nat
open import Data.List


NatQ : Set₁
NatQ = (A : Set) -> (A -> A) -> A -> A

unNatQ : {A : Set} -> (A -> A) -> A -> NatQ -> A
unNatQ f a s = s _ f a

succQ : NatQ -> NatQ
succQ s = \_ f a -> f (s _ f a)

zeroQ : NatQ
zeroQ = \_ f a -> a

fromNatQ : NatQ -> ℕ
fromNatQ s = unNatQ suc zero s

toNatQ : ℕ -> NatQ
toNatQ (suc n) = succQ (toNatQ n)
toNatQ zero    = zeroQ


ListQ : Set -> Set₁
ListQ A = (B : Set) -> (A -> B -> B) -> B -> B

unListQ : {A B : Set} -> (A -> B -> B) -> B -> ListQ A -> B
unListQ f b s = s _ f b

consQ : {A : Set} -> A -> ListQ A -> ListQ A
consQ a s = \_ f b -> f a (s _ f b)

nilQ : {A : Set} -> ListQ A
nilQ = \_ f b -> b

fromListQ : {A : Set} -> ListQ A -> List A
fromListQ s = unListQ (_∷_) [] s

toListQ : {A : Set} -> List A -> ListQ A
toListQ (a ∷ aa) = consQ a (toListQ aa)
toListQ []       = nilQ
