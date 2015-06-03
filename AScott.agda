module AScott where

import Data.Bool as A
import Data.Maybe as A
import Data.Sum as A
import Data.Product as A


BoolS : Set₁
BoolS = {A : Set} -> A -> A -> A

unBoolS : {A : Set} -> A -> A -> BoolS -> A
unBoolS a a' s = s a a'

trueS : BoolS
trueS = \a a' -> a

falseS : BoolS
falseS = \a a' -> a'

fromBoolS : BoolS -> A.Bool
fromBoolS s = unBoolS A.true A.false s

toBoolS : A.Bool -> BoolS
toBoolS A.true  = trueS
toBoolS A.false = falseS


MaybeS : Set -> Set₁
MaybeS A = {B : Set} -> (A -> B) -> B -> B

unMaybeS : {A B : Set} -> (A -> B) -> B -> MaybeS A -> B
unMaybeS f b s = s f b

justS : {A : Set} -> A -> MaybeS A
justS a = \f b -> f a

nothingS : {A : Set} -> MaybeS A
nothingS = \f b -> b

fromMaybeS : {A : Set} -> MaybeS A -> A.Maybe A
fromMaybeS s = unMaybeS A.just A.nothing s

toMaybeS : {A : Set} -> A.Maybe A -> MaybeS A
toMaybeS (A.just a) = justS a
toMaybeS A.nothing  = nothingS


EitherS : Set -> Set -> Set₁
EitherS A B = {C : Set} -> (A -> C) -> (B -> C) -> C

unEitherS : {A B C : Set} -> (A -> C) -> (B -> C) -> EitherS A B -> C
unEitherS f g s = s f g

leftS : {A B : Set} -> A -> EitherS A B
leftS a = \f g -> f a

rightS : {A B : Set} -> B -> EitherS A B
rightS b = \f g -> g b

fromEitherS : {A B : Set} -> EitherS A B -> A A.⊎ B
fromEitherS s = unEitherS A.inj₁ A.inj₂ s

toEitherS : {A B : Set} -> A A.⊎ B -> EitherS A B
toEitherS (A.inj₁ a) = leftS a
toEitherS (A.inj₂ b) = rightS b


PairS : Set -> Set -> Set₁
PairS A B = {C : Set} -> (A -> B -> C) -> C

unPairS : {A B C : Set} -> (A -> B -> C) -> PairS A B -> C
unPairS f s = s f

pairS : {A B : Set} -> A -> B -> PairS A B
pairS a b = \f -> f a b


-- TODO:

-- fromPairS : {A B : Set} -> PairS A B -> A.Σ A B
-- fromPairS s = unPairS (\a b -> (a A., b)) s

-- toPairS : {A B : Set} -> A.Σ A B -> PairS A B
-- toPairS (a A., b) = pairS a b
