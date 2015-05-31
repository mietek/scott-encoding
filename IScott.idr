module IScott

%default total


BoolS : Type
BoolS = (a : Type) -> a -> a -> a

unboolS : a -> a -> BoolS -> a
unboolS a a' s = s _ a a'

trueS : BoolS
trueS = \_, a, a' => a

falseS : BoolS
falseS = \_, a, a' => a'

fromBoolS : BoolS -> Bool
fromBoolS s = unboolS True False s

toBoolS : Bool -> BoolS
toBoolS True  = trueS
toBoolS False = falseS


MaybeS : Type -> Type
MaybeS a = (b : Type) -> (a -> b) -> b -> b

unmaybeS : (a -> b) -> b -> MaybeS a -> b
unmaybeS f b s = s _ f b

justS : a -> MaybeS a
justS a = \_, f, b => f a

nothingS : MaybeS a
nothingS = \_, f, b => b

fromMaybeS : MaybeS a -> Maybe a
fromMaybeS s = unmaybeS Just Nothing s

toMaybeS : Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


EitherS : Type -> Type -> Type
EitherS a b = (c : Type) -> (a -> c) -> (b -> c) -> c

uneitherS : (a -> c) -> (b -> c) -> EitherS a b -> c
uneitherS f g s = s _ f g

leftS : a -> EitherS a b
leftS a = \_, f, g => f a

rightS : b -> EitherS a b
rightS b = \_, f, g => g b

fromEitherS : EitherS a b -> Either a b
fromEitherS s = uneitherS Left Right s

toEitherS : Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


PairS : Type -> Type -> Type
PairS a b = (c : Type) -> (a -> b -> c) -> c

unpairS : (a -> b -> c) -> PairS a b -> c
unpairS f s = s _ f

pairS : a -> b -> PairS a b
pairS a b = \_, f => f a b

fromPairS : PairS a b -> (a, b)
fromPairS s = unpairS (\a, b => (a, b)) s

toPairS : (a, b) -> PairS a b
toPairS (a, b) = pairS a b

fstS : PairS a b -> a
fstS s = unpairS (\a, b => a) s

sndS : PairS a b -> b
sndS s = unpairS (\a, b => b) s


NatS : Type
NatS = (a : Type) -> (a -> a) -> a -> a

unnatS : (a -> a) -> a -> NatS -> a
unnatS f a s = s _ f a

succS : NatS -> NatS
succS s = \_, f, a => f (s _ f a)

zeroS : NatS
zeroS = \_, f, a => a

fromNatS : NatS -> Nat
fromNatS s = unnatS S Z s

toNatS : Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS


ListS : Type -> Type
ListS a = (b : Type) -> (a -> b -> b) -> b -> b

unlistS : (a -> b -> b) -> b -> ListS a -> b
unlistS f b s = s _ f b

consS : a -> ListS a -> ListS a
consS a s = \_, f, b => f a (s _ f b)

nilS : ListS a
nilS = \_, f, b => b

fromListS : ListS a -> List a
fromListS s = unlistS (::) [] s

toListS : List a -> ListS a
toListS (a :: as) = consS a (toListS as)
toListS []        = nilS


iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a     = a

iteratedP : (n : Nat) -> iterated n S Z = n
iteratedP (S n) = rewrite iteratedP n in Refl
iteratedP Z     = Refl


unboolTrueSP : unboolS a a' trueS = a
unboolTrueSP = Refl

unboolFalseSP : unboolS a a' falseS = a'
unboolFalseSP = Refl

fromTrueSP : fromBoolS trueS = True
fromTrueSP = Refl

fromFalseSP : fromBoolS falseS = False
fromFalseSP = Refl

toTrueSP : toBoolS True = trueS
toTrueSP = Refl

toFalseSP : toBoolS False = falseS
toFalseSP = Refl


unmaybeJustSP : unmaybeS f b (justS a) = f a
unmaybeJustSP = Refl

unmaybeNothingSP : unmaybeS f b nothingS = b
unmaybeNothingSP = Refl

fromJustSP : fromMaybeS (justS a) = Just a
fromJustSP = Refl

fromNothingSP : fromMaybeS nothingS = Nothing
fromNothingSP = Refl

toJustSP : toMaybeS (Just a) = justS a
toJustSP = Refl

toNothingSP : toMaybeS Nothing = nothingS
toNothingSP = Refl


uneitherLeftSP : uneitherS f g (leftS a) = f a
uneitherLeftSP = Refl

uneitherRightSP : uneitherS f g (rightS b) = g b
uneitherRightSP = Refl

fromLeftSP : fromEitherS (leftS a) = Left a
fromLeftSP = Refl

fromRightSP : fromEitherS (rightS b) = Right b
fromRightSP = Refl

toLeftSP : toEitherS (Left a) = leftS a
toLeftSP = Refl

toRightSP : toEitherS (Right b) = rightS b
toRightSP = Refl


unpairPairSP : unpairS (\a, b => (a, b)) (pairS a b) = (a, b)
unpairPairSP = Refl

fromPairSP : fromPairS (pairS a b) = (a, b)
fromPairSP = Refl

toPairSP : toPairS (a, b) = pairS a b
toPairSP = Refl

fstPairSP : fstS (pairS a b) = a
fstPairSP = Refl

sndPairSP : sndS (pairS a b) = b
sndPairSP = Refl


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
