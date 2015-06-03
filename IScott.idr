module IScott

%default total


BoolS : Type
BoolS = (a : Type) -> a -> a -> a

unBoolS : a -> a -> BoolS -> a
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


MaybeS : Type -> Type
MaybeS a = (b : Type) -> (a -> b) -> b -> b

unMaybeS : (a -> b) -> b -> MaybeS a -> b
unMaybeS f b s = s _ f b

justS : a -> MaybeS a
justS a = \_, f, b => f a

nothingS : MaybeS a
nothingS = \_, f, b => b

fromMaybeS : MaybeS a -> Maybe a
fromMaybeS s = unMaybeS Just Nothing s

toMaybeS : Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


EitherS : Type -> Type -> Type
EitherS a b = (c : Type) -> (a -> c) -> (b -> c) -> c

unEitherS : (a -> c) -> (b -> c) -> EitherS a b -> c
unEitherS f g s = s _ f g

leftS : a -> EitherS a b
leftS a = \_, f, g => f a

rightS : b -> EitherS a b
rightS b = \_, f, g => g b

fromEitherS : EitherS a b -> Either a b
fromEitherS s = unEitherS Left Right s

toEitherS : Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


PairS : Type -> Type -> Type
PairS a b = (c : Type) -> (a -> b -> c) -> c

unPairS : (a -> b -> c) -> PairS a b -> c
unPairS f s = s _ f

pairS : a -> b -> PairS a b
pairS a b = \_, f => f a b

fromPairS : PairS a b -> (a, b)
fromPairS s = unPairS (\a, b => (a, b)) s

toPairS : (a, b) -> PairS a b
toPairS (a, b) = pairS a b

firstS : PairS a b -> a
firstS s = unPairS (\a, b => a) s

secondS : PairS a b -> b
secondS s = unPairS (\a, b => b) s


NatS : Type
NatS = (a : Type) -> (a -> a) -> a -> a

unNatS : (a -> a) -> a -> NatS -> a
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


ListS : Type -> Type
ListS a = (b : Type) -> (a -> b -> b) -> b -> b

unListS : (a -> b -> b) -> b -> ListS a -> b
unListS f b s = s _ f b

consS : a -> ListS a -> ListS a
consS a s = \_, f, b => f a (s _ f b)

nilS : ListS a
nilS = \_, f, b => b

fromListS : ListS a -> List a
fromListS s = unListS (::) [] s

toListS : List a -> ListS a
toListS (a :: as) = consS a (toListS as)
toListS []        = nilS


iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

iteratedP : (n : Nat) -> iterated n S Z = n
iteratedP (S n) = rewrite iteratedP n in Refl
iteratedP Z     = Refl


unBoolTrueSP : unBoolS a a' trueS = a
unBoolTrueSP = Refl

unBoolFalseSP : unBoolS a a' falseS = a'
unBoolFalseSP = Refl

fromTrueSP : fromBoolS trueS = True
fromTrueSP = Refl

fromFalseSP : fromBoolS falseS = False
fromFalseSP = Refl

toTrueSP : toBoolS True = trueS
toTrueSP = Refl

toFalseSP : toBoolS False = falseS
toFalseSP = Refl


unMaybeJustSP : unMaybeS f b (justS a) = f a
unMaybeJustSP = Refl

unMaybeNothingSP : unMaybeS f b nothingS = b
unMaybeNothingSP = Refl

fromJustSP : fromMaybeS (justS a) = Just a
fromJustSP = Refl

fromNothingSP : fromMaybeS nothingS = Nothing
fromNothingSP = Refl

toJustSP : toMaybeS (Just a) = justS a
toJustSP = Refl

toNothingSP : toMaybeS Nothing = nothingS
toNothingSP = Refl


unEitherLeftSP : unEitherS f g (leftS a) = f a
unEitherLeftSP = Refl

unEitherRightSP : unEitherS f g (rightS b) = g b
unEitherRightSP = Refl

fromLeftSP : fromEitherS (leftS a) = Left a
fromLeftSP = Refl

fromRightSP : fromEitherS (rightS b) = Right b
fromRightSP = Refl

toLeftSP : toEitherS (Left a) = leftS a
toLeftSP = Refl

toRightSP : toEitherS (Right b) = rightS b
toRightSP = Refl


unPairPairSP : unPairS (\a, b => (a, b)) (pairS a b) = (a, b)
unPairPairSP = Refl

fromPairSP : fromPairS (pairS a b) = (a, b)
fromPairSP = Refl

toPairSP : toPairS (a, b) = pairS a b
toPairSP = Refl

firstPairSP : firstS (pairS a b) = a
firstPairSP = Refl

secondPairSP : secondS (pairS a b) = b
secondPairSP = Refl


fromNatSP : (n : Nat) -> fromNatS (iterated n succS zeroS) = n
fromNatSP (S n) = rewrite fromNatSP n in Refl
fromNatSP Z     = Refl

toNatSP : (n : Nat) -> toNatS n = iterated n succS zeroS
toNatSP (S n) = rewrite toNatSP n in Refl
toNatSP Z = Refl


-- TODO: Use a list of [0 .. n]

fromListSP : (n : Nat) -> fromListS (iterated n (consS ()) nilS) = iterated n (() ::) []
fromListSP (S n) = rewrite fromListSP n in Refl
fromListSP Z     = Refl

toListSP : (n : Nat) -> toListS (iterated n (() ::) []) = iterated n (consS ()) nilS
toListSP (S n) = rewrite toListSP n in Refl
toListSP Z     = Refl
