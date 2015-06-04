module Common

%default total


BoolQ : Type
BoolQ = (A : Type) -> A -> A -> A

unBoolQ : {A : Type} -> A -> A -> BoolQ -> A
unBoolQ a a' q = q _ a a'

trueQ : BoolQ
trueQ = \_, a, a' => a

falseQ : BoolQ
falseQ = \_, a, a' => a'

fromBoolQ : BoolQ -> Bool
fromBoolQ q = unBoolQ True False q

toBoolQ : Bool -> BoolQ
toBoolQ True  = trueQ
toBoolQ False = falseQ

test_unBoolTrueQ : unBoolQ a a' trueQ = a
test_unBoolTrueQ = Refl

test_unBoolFalseQ : unBoolQ a a' falseQ = a'
test_unBoolFalseQ = Refl

test_fromTrueQ : fromBoolQ trueQ = True
test_fromTrueQ = Refl

test_fromFalseQ : fromBoolQ falseQ = False
test_fromFalseQ = Refl

test_toTrueQ : toBoolQ True = trueQ
test_toTrueQ = Refl

test_toFalseQ : toBoolQ False = falseQ
test_toFalseQ = Refl


MaybeQ : Type -> Type
MaybeQ A = (B : Type) -> (A -> B) -> B -> B

unMaybeQ : {A, B : Type} -> (A -> B) -> B -> MaybeQ A -> B
unMaybeQ f b q = q _ f b

justQ : {A : Type} -> A -> MaybeQ A
justQ a = \_, f, b => f a

nothingQ : {A : Type} -> MaybeQ A
nothingQ = \_, f, b => b

fromMaybeQ : {A : Type} -> MaybeQ A -> Maybe A
fromMaybeQ q = unMaybeQ Just Nothing q

toMaybeQ : {A : Type} -> Maybe A -> MaybeQ A
toMaybeQ (Just a) = justQ a
toMaybeQ Nothing  = nothingQ

test_unMaybeJustQ : unMaybeQ f b (justQ a) = f a
test_unMaybeJustQ = Refl

test_unMaybeNothingQ : unMaybeQ f b nothingQ = b
test_unMaybeNothingQ = Refl

test_fromJustQ : fromMaybeQ (justQ a) = Just a
test_fromJustQ = Refl

test_fromNothingQ : fromMaybeQ nothingQ = Nothing
test_fromNothingQ = Refl

test_toJustQ : toMaybeQ (Just a) = justQ a
test_toJustQ = Refl

test_toNothingQ : toMaybeQ Nothing = nothingQ
test_toNothingQ = Refl


EitherQ : Type -> Type -> Type
EitherQ A B = (C : Type) -> (A -> C) -> (B -> C) -> C

unEitherQ : {A, B, C : Type} -> (A -> C) -> (B -> C) -> EitherQ A B -> C
unEitherQ f g q = q _ f g

leftQ : {A, B : Type} -> A -> EitherQ A B
leftQ a = \_, f, g => f a

rightQ : {A, B : Type} -> B -> EitherQ A B
rightQ b = \_, f, g => g b

fromEitherQ : {A, B : Type} -> EitherQ A B -> Either A B
fromEitherQ q = unEitherQ Left Right q

toEitherQ : {A, B : Type} -> Either A B -> EitherQ A B
toEitherQ (Left a)  = leftQ a
toEitherQ (Right b) = rightQ b

test_unEitherLeftQ : unEitherQ f g (leftQ a) = f a
test_unEitherLeftQ = Refl

test_unEitherRightQ : unEitherQ f g (rightQ b) = g b
test_unEitherRightQ = Refl

test_fromLeftQ : fromEitherQ (leftQ a) = Left a
test_fromLeftQ = Refl

test_fromRightQ : fromEitherQ (rightQ b) = Right b
test_fromRightQ = Refl

test_toLeftQ : toEitherQ (Left a) = leftQ a
test_toLeftQ = Refl

test_toRightQ : toEitherQ (Right b) = rightQ b
test_toRightQ = Refl


PairQ : Type -> Type -> Type
PairQ A B = (C : Type) -> (A -> B -> C) -> C

unPairQ : {A, B, C : Type} -> (A -> B -> C) -> PairQ A B -> C
unPairQ f q = q _ f

pairQ : {A, B : Type} -> A -> B -> PairQ A B
pairQ a b = \_, f => f a b

fromPairQ : {A, B : Type} -> PairQ A B -> (A, B)
fromPairQ q = unPairQ (\a, b => (a, b)) q

toPairQ : {A, B : Type} -> (A, B) -> PairQ A B
toPairQ (a, b) = pairQ a b

fstQ : {A, B : Type} -> PairQ A B -> A
fstQ q = unPairQ (\a, b => a) q

sndQ : {A, B : Type} -> PairQ A B -> B
sndQ q = unPairQ (\a, b => b) q

test_unPairPairQ : unPairQ (\a, b => (a, b)) (pairQ a b) = (a, b)
test_unPairPairQ = Refl

test_fromPairQ : fromPairQ (pairQ a b) = (a, b)
test_fromPairQ = Refl

test_toPairQ : toPairQ (a, b) = pairQ a b
test_toPairQ = Refl

test_fstPairQ : fstQ (pairQ a b) = a
test_fstPairQ = Refl

test_sndPairQ : sndQ (pairQ a b) = b
test_sndPairQ = Refl
