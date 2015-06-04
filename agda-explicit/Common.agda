module Common where

open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Data.Product


BoolQ : Set₁
BoolQ = (A : Set) -> A -> A -> A

unBoolQ : {A : Set} -> A -> A -> BoolQ -> A
unBoolQ a a' q = q _ a a'

trueQ : BoolQ
trueQ = \_ a a' -> a

falseQ : BoolQ
falseQ = \_ a a' -> a'

fromBoolQ : BoolQ -> Bool
fromBoolQ q = unBoolQ true false q

toBoolQ : Bool -> BoolQ
toBoolQ true  = trueQ
toBoolQ false = falseQ


MaybeQ : Set -> Set₁
MaybeQ A = (B : Set) -> (A -> B) -> B -> B

unMaybeQ : {A B : Set} -> (A -> B) -> B -> MaybeQ A -> B
unMaybeQ f b q = q _ f b

justQ : {A : Set} -> A -> MaybeQ A
justQ a = \_ f b -> f a

nothingQ : {A : Set} -> MaybeQ A
nothingQ = \_ f b -> b

fromMaybeQ : {A : Set} -> MaybeQ A -> Maybe A
fromMaybeQ q = unMaybeQ just nothing q

toMaybeQ : {A : Set} -> Maybe A -> MaybeQ A
toMaybeQ (just a) = justQ a
toMaybeQ nothing  = nothingQ


EitherQ : Set -> Set -> Set₁
EitherQ A B = (C : Set) -> (A -> C) -> (B -> C) -> C

unEitherQ : {A B C : Set} -> (A -> C) -> (B -> C) -> EitherQ A B -> C
unEitherQ f g q = q _ f g

leftQ : {A B : Set} -> A -> EitherQ A B
leftQ a = \_ f g -> f a

rightQ : {A B : Set} -> B -> EitherQ A B
rightQ b = \_ f g -> g b

fromEitherQ : {A B : Set} -> EitherQ A B -> A ⊎ B
fromEitherQ q = unEitherQ inj₁ inj₂ q

toEitherQ : {A B : Set} -> A ⊎ B -> EitherQ A B
toEitherQ (inj₁ a) = leftQ a
toEitherQ (inj₂ b) = rightQ b


PairQ : Set -> Set -> Set₁
PairQ A B = (C : Set) -> (A -> B -> C) -> C

unPairQ : {A B C : Set} -> (A -> B -> C) -> PairQ A B -> C
unPairQ f q = q _ f

pairQ : {A B : Set} -> A -> B -> PairQ A B
pairQ a b = \_ f -> f a b

fromPairQ : {A B : Set} -> PairQ A B -> A × B
fromPairQ q = unPairQ (\a b -> (a , b)) q

toPairQ : {A B : Set} -> A × B -> PairQ A B
toPairQ (a , b) = pairQ a b

fstQ : {A B : Set} -> PairQ A B -> A
fstQ q = unPairQ (\a b -> a) q

sndQ : {A B : Set} -> PairQ A B -> B
sndQ q = unPairQ (\a b -> b) q
