module BoehmBerarducci where

open import Data.Nat
open import Data.List


NatQ : Set₁
NatQ = {A : Set} -> (A -> A) -> A -> A

unNatQ : {A : Set} -> (A -> A) -> A -> NatQ -> A
unNatQ f a q = q f a

succQ : NatQ -> NatQ
succQ q = \f a -> f (q f a)

zeroQ : NatQ
zeroQ = \f a -> a

fromNatQ : NatQ -> ℕ
fromNatQ q = unNatQ suc zero q

toNatQ : ℕ -> NatQ
toNatQ (suc n) = succQ (toNatQ n)
toNatQ zero    = zeroQ


ListQ : Set -> Set₁
ListQ A = {B : Set} -> (A -> B -> B) -> B -> B

unListQ : {A B : Set} -> (A -> B -> B) -> B -> ListQ A -> B
unListQ f b q = q f b

consQ : {A : Set} -> A -> ListQ A -> ListQ A
consQ a q = \f b -> f a (q f b)

nilQ : {A : Set} -> ListQ A
nilQ = \f b -> b

fromListQ : {A : Set} -> ListQ A -> List A
fromListQ q = unListQ (_∷_) [] q

toListQ : {A : Set} -> List A -> ListQ A
toListQ (a ∷ aa) = consQ a (toListQ aa)
toListQ []       = nilQ
