module Common where

open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Data.Product


BoolQ : Set₁
BoolQ = {A : Set} -> A -> A -> A

unBoolQ : {A : Set} -> A -> A -> BoolQ -> A
unBoolQ a a' s = s a a'

trueQ : BoolQ
trueQ = \a a' -> a

falseQ : BoolQ
falseQ = \a a' -> a'

fromBoolQ : BoolQ -> Bool
fromBoolQ s = unBoolQ true false s

toBoolQ : Bool -> BoolQ
toBoolQ true  = trueQ
toBoolQ false = falseQ


MaybeQ : Set -> Set₁
MaybeQ A = {B : Set} -> (A -> B) -> B -> B

unMaybeQ : {A B : Set} -> (A -> B) -> B -> MaybeQ A -> B
unMaybeQ f b s = s f b

justQ : {A : Set} -> A -> MaybeQ A
justQ a = \f b -> f a

nothingQ : {A : Set} -> MaybeQ A
nothingQ = \f b -> b

fromMaybeQ : {A : Set} -> MaybeQ A -> Maybe A
fromMaybeQ s = unMaybeQ just nothing s

toMaybeQ : {A : Set} -> Maybe A -> MaybeQ A
toMaybeQ (just a) = justQ a
toMaybeQ nothing  = nothingQ


EitherQ : Set -> Set -> Set₁
EitherQ A B = {C : Set} -> (A -> C) -> (B -> C) -> C

unEitherQ : {A B C : Set} -> (A -> C) -> (B -> C) -> EitherQ A B -> C
unEitherQ f g s = s f g

leftQ : {A B : Set} -> A -> EitherQ A B
leftQ a = \f g -> f a

rightQ : {A B : Set} -> B -> EitherQ A B
rightQ b = \f g -> g b

fromEitherQ : {A B : Set} -> EitherQ A B -> A ⊎ B
fromEitherQ s = unEitherQ inj₁ inj₂ s

toEitherQ : {A B : Set} -> A ⊎ B -> EitherQ A B
toEitherQ (inj₁ a) = leftQ a
toEitherQ (inj₂ b) = rightQ b


PairQ : Set -> Set -> Set₁
PairQ A B = {C : Set} -> (A -> B -> C) -> C

unPairQ : {A B C : Set} -> (A -> B -> C) -> PairQ A B -> C
unPairQ f s = s f

pairQ : {A B : Set} -> A -> B -> PairQ A B
pairQ a b = \f -> f a b

fromPairQ : {A B : Set} -> PairQ A B -> A × B
fromPairQ s = unPairQ (\a b -> (a , b)) s

toPairQ : {A B : Set} -> A × B -> PairQ A B
toPairQ (a , b) = pairQ a b

fstQ : {A B : Set} -> PairQ A B -> A
fstQ s = unPairQ (\a b -> a) s

sndQ : {A B : Set} -> PairQ A B -> B
sndQ s = unPairQ (\a b -> b) s
