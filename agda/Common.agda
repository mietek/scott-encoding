module Common where

open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Data.Product


BoolS : Set₁
BoolS = {A : Set} -> A -> A -> A

unBoolS : {A : Set} -> A -> A -> BoolS -> A
unBoolS a a' s = s a a'

trueS : BoolS
trueS = \a a' -> a

falseS : BoolS
falseS = \a a' -> a'

fromBoolS : BoolS -> Bool
fromBoolS s = unBoolS true false s

toBoolS : Bool -> BoolS
toBoolS true  = trueS
toBoolS false = falseS


MaybeS : Set -> Set₁
MaybeS A = {B : Set} -> (A -> B) -> B -> B

unMaybeS : {A B : Set} -> (A -> B) -> B -> MaybeS A -> B
unMaybeS f b s = s f b

justS : {A : Set} -> A -> MaybeS A
justS a = \f b -> f a

nothingS : {A : Set} -> MaybeS A
nothingS = \f b -> b

fromMaybeS : {A : Set} -> MaybeS A -> Maybe A
fromMaybeS s = unMaybeS just nothing s

toMaybeS : {A : Set} -> Maybe A -> MaybeS A
toMaybeS (just a) = justS a
toMaybeS nothing  = nothingS


EitherS : Set -> Set -> Set₁
EitherS A B = {C : Set} -> (A -> C) -> (B -> C) -> C

unEitherS : {A B C : Set} -> (A -> C) -> (B -> C) -> EitherS A B -> C
unEitherS f g s = s f g

leftS : {A B : Set} -> A -> EitherS A B
leftS a = \f g -> f a

rightS : {A B : Set} -> B -> EitherS A B
rightS b = \f g -> g b

fromEitherS : {A B : Set} -> EitherS A B -> A ⊎ B
fromEitherS s = unEitherS inj₁ inj₂ s

toEitherS : {A B : Set} -> A ⊎ B -> EitherS A B
toEitherS (inj₁ a) = leftS a
toEitherS (inj₂ b) = rightS b


PairS : Set -> Set -> Set₁
PairS A B = {C : Set} -> (A -> B -> C) -> C

unPairS : {A B C : Set} -> (A -> B -> C) -> PairS A B -> C
unPairS f s = s f

pairS : {A B : Set} -> A -> B -> PairS A B
pairS a b = \f -> f a b

fromPairS : {A B : Set} -> PairS A B -> A × B
fromPairS s = unPairS (\a b -> (a , b)) s

toPairS : {A B : Set} -> A × B -> PairS A B
toPairS (a , b) = pairS a b

fstS : {A B : Set} -> PairS A B -> A
fstS s = unPairS (\a b -> a) s

sndS : {A B : Set} -> PairS A B -> B
sndS s = unPairS (\a b -> b) s
