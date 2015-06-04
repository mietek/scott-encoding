module IScottExplicit

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


NatS : Type
NatS = (A : Type) -> (A -> A) -> A -> A

unNatS : {A : Type} -> (A -> A) -> A -> NatS -> A
unNatS f a s = s _ f a

succS : NatS -> NatS
succS s = \_, f, a => f (s _ f a)

zeroS : NatS
zeroS = \_, f, a => a

fromNatS : NatS -> Nat
fromNatS s = unNatS S Z s

toNatS : Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS

iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

test_iterated : (n : Nat) -> iterated n S Z = n
test_iterated (S n) = rewrite test_iterated n in Refl
test_iterated Z     = Refl

test_fromNatS : (n : Nat) -> fromNatS (iterated n succS zeroS) = n
test_fromNatS (S n) = rewrite test_fromNatS n in Refl
test_fromNatS Z     = Refl

test_toNatS : (n : Nat) -> toNatS n = iterated n succS zeroS
test_toNatS (S n) = rewrite test_toNatS n in Refl
test_toNatS Z = Refl


ListS : Type -> Type
ListS A = (B : Type) -> (A -> B -> B) -> B -> B

unListS : {A, B : Type} -> (A -> B -> B) -> B -> ListS A -> B
unListS f b s = s _ f b

consS : {A : Type} -> A -> ListS A -> ListS A
consS a s = \_, f, b => f a (s _ f b)

nilS : {A : Type} -> ListS A
nilS = \_, f, b => b

fromListS : {A : Type} -> ListS A -> List A
fromListS s = unListS (::) [] s

toListS : {A : Type} -> List A -> ListS A
toListS (a :: aa) = consS a (toListS aa)
toListS []        = nilS
