module IScott

%default total


iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a = a


BoolS : Type
BoolS = (a : Type) -> a -> a -> a

unboolS : a -> a -> BoolS -> a
unboolS a a' b = b _ a a'

trueS : BoolS
trueS = \_, a, a' => a

falseS : BoolS
falseS = \_, a, a' => a'

fromBoolS : BoolS -> Bool
fromBoolS = unboolS True False

toBoolS : Bool -> BoolS
toBoolS True  = trueS
toBoolS False = falseS


MaybeS : Type -> Type
MaybeS a = (b : Type) -> (a -> b) -> b -> b

unmaybeS : (a -> b) -> b -> MaybeS a -> b
unmaybeS f b m = m _ f b

justS : a -> MaybeS a
justS a = \_, f, b => f a

nothingS : MaybeS a
nothingS = \_, f, b => b

fromMaybeS : MaybeS a -> Maybe a
fromMaybeS = unmaybeS Just Nothing

toMaybeS : Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


EitherS : Type -> Type -> Type
EitherS a b = (c : Type) -> (a -> c) -> (b -> c) -> c

uneitherS : (a -> c) -> (b -> c) -> EitherS a b -> c
uneitherS f g e = e _ f g

leftS : a -> EitherS a b
leftS a = \_, f, g => f a

rightS : b -> EitherS a b
rightS b = \_, f, g => g b

fromEitherS : EitherS a b -> Either a b
fromEitherS = uneitherS Left Right

toEitherS : Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


PairS : Type -> Type -> Type
PairS a b = (c : Type) -> (a -> b -> c) -> c

unpairS : (a -> b -> c) -> PairS a b -> c
unpairS f p = p _ f

pairS : a -> b -> PairS a b
pairS a b = \_, f => f a b

fromPairS : PairS a b -> (a, b)
fromPairS = unpairS (\a, b => (a, b))

toPairS : (a, b) -> PairS a b
toPairS (a, b) = pairS a b

fstS : PairS a b -> a
fstS = unpairS (\a, b => a)

sndS : PairS a b -> b
sndS = unpairS (\a, b => b)


NatS : Type
NatS = (a : Type) -> (a -> a) -> a -> a

unnatS : (a -> a) -> a -> NatS -> a
unnatS f a n = n _ f a

succS : NatS -> NatS
succS n = \_, f, a => f (n _ f a)

zeroS : NatS
zeroS = \_, f, a => a

fromNatS : NatS -> Nat
fromNatS = unnatS S Z

toNatS : Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS


ListS : Type -> Type
ListS a = (b : Type) -> (a -> b -> b) -> b -> b

unlistS : (a -> b -> b) -> b -> ListS a -> b
unlistS f b l = l _ f b

consS : a -> ListS a -> ListS a
consS a l = \_, f, b => f a (l _ f b)

nilS : ListS a
nilS = \_, f, b => b

fromListS : ListS a -> List a
fromListS = unlistS (::) []

toListS : List a -> ListS a
toListS (a :: l) = consS a (toListS l)
toListS []       = nilS
