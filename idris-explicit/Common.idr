module Common

%default total


BoolS : Type
BoolS = (A : Type) -> A -> A -> A

unBoolS : {A : Type} -> A -> A -> BoolS -> A
unBoolS a a' s = s _ a a'

trueS : BoolS
trueS = \_, a, a' => a

falseS : BoolS
falseS = \_, a, a' => a'

fromBoolS : BoolS -> Bool
fromBoolS s = unBoolS True False s

toBoolS : Bool -> BoolS
toBoolS True  = trueS
toBoolS False = falseS

test_unBoolTrueS : unBoolS a a' trueS = a
test_unBoolTrueS = Refl

test_unBoolFalseS : unBoolS a a' falseS = a'
test_unBoolFalseS = Refl

test_fromTrueS : fromBoolS trueS = True
test_fromTrueS = Refl

test_fromFalseS : fromBoolS falseS = False
test_fromFalseS = Refl

test_toTrueS : toBoolS True = trueS
test_toTrueS = Refl

test_toFalseS : toBoolS False = falseS
test_toFalseS = Refl


MaybeS : Type -> Type
MaybeS A = (B : Type) -> (A -> B) -> B -> B

unMaybeS : {A, B : Type} -> (A -> B) -> B -> MaybeS A -> B
unMaybeS f b s = s _ f b

justS : {A : Type} -> A -> MaybeS A
justS a = \_, f, b => f a

nothingS : {A : Type} -> MaybeS A
nothingS = \_, f, b => b

fromMaybeS : {A : Type} -> MaybeS A -> Maybe A
fromMaybeS s = unMaybeS Just Nothing s

toMaybeS : {A : Type} -> Maybe A -> MaybeS A
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS

test_unMaybeJustS : unMaybeS f b (justS a) = f a
test_unMaybeJustS = Refl

test_unMaybeNothingS : unMaybeS f b nothingS = b
test_unMaybeNothingS = Refl

test_fromJustS : fromMaybeS (justS a) = Just a
test_fromJustS = Refl

test_fromNothingS : fromMaybeS nothingS = Nothing
test_fromNothingS = Refl

test_toJustS : toMaybeS (Just a) = justS a
test_toJustS = Refl

test_toNothingS : toMaybeS Nothing = nothingS
test_toNothingS = Refl


EitherS : Type -> Type -> Type
EitherS A B = (C : Type) -> (A -> C) -> (B -> C) -> C

unEitherS : {A, B, C : Type} -> (A -> C) -> (B -> C) -> EitherS A B -> C
unEitherS f g s = s _ f g

leftS : {A, B : Type} -> A -> EitherS A B
leftS a = \_, f, g => f a

rightS : {A, B : Type} -> B -> EitherS A B
rightS b = \_, f, g => g b

fromEitherS : {A, B : Type} -> EitherS A B -> Either A B
fromEitherS s = unEitherS Left Right s

toEitherS : {A, B : Type} -> Either A B -> EitherS A B
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b

test_unEitherLeftS : unEitherS f g (leftS a) = f a
test_unEitherLeftS = Refl

test_unEitherRightS : unEitherS f g (rightS b) = g b
test_unEitherRightS = Refl

test_fromLeftS : fromEitherS (leftS a) = Left a
test_fromLeftS = Refl

test_fromRightS : fromEitherS (rightS b) = Right b
test_fromRightS = Refl

test_toLeftS : toEitherS (Left a) = leftS a
test_toLeftS = Refl

test_toRightS : toEitherS (Right b) = rightS b
test_toRightS = Refl


PairS : Type -> Type -> Type
PairS A B = (C : Type) -> (A -> B -> C) -> C

unPairS : {A, B, C : Type} -> (A -> B -> C) -> PairS A B -> C
unPairS f s = s _ f

pairS : {A, B : Type} -> A -> B -> PairS A B
pairS a b = \_, f => f a b

fromPairS : {A, B : Type} -> PairS A B -> (A, B)
fromPairS s = unPairS (\a, b => (a, b)) s

toPairS : {A, B : Type} -> (A, B) -> PairS A B
toPairS (a, b) = pairS a b

fstS : {A, B : Type} -> PairS A B -> A
fstS s = unPairS (\a, b => a) s

sndS : {A, B : Type} -> PairS A B -> B
sndS s = unPairS (\a, b => b) s

test_unPairPairS : unPairS (\a, b => (a, b)) (pairS a b) = (a, b)
test_unPairPairS = Refl

test_fromPairS : fromPairS (pairS a b) = (a, b)
test_fromPairS = Refl

test_toPairS : toPairS (a, b) = pairS a b
test_toPairS = Refl

test_fstPairS : fstS (pairS a b) = a
test_fstPairS = Refl

test_sndPairS : sndS (pairS a b) = b
test_sndPairS = Refl
