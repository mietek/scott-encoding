module BoehmBerarducci where

open import Data.Nat
open import Data.List


NatS : Set₁
NatS = (A : Set) -> (A -> A) -> A -> A

unNatS : {A : Set} -> (A -> A) -> A -> NatS -> A
unNatS f a s = s _ f a

succS : NatS -> NatS
succS s = \_ f a -> f (s _ f a)

zeroS : NatS
zeroS = \_ f a -> a

fromNatS : NatS -> ℕ
fromNatS s = unNatS suc zero s

toNatS : ℕ -> NatS
toNatS (suc n) = succS (toNatS n)
toNatS zero    = zeroS


ListS : Set -> Set₁
ListS A = (B : Set) -> (A -> B -> B) -> B -> B

unListS : {A B : Set} -> (A -> B -> B) -> B -> ListS A -> B
unListS f b s = s _ f b

consS : {A : Set} -> A -> ListS A -> ListS A
consS a s = \_ f b -> f a (s _ f b)

nilS : {A : Set} -> ListS A
nilS = \_ f b -> b

fromListS : {A : Set} -> ListS A -> List A
fromListS s = unListS (_∷_) [] s

toListS : {A : Set} -> List A -> ListS A
toListS (a ∷ aa) = consS a (toListS aa)
toListS []       = nilS
