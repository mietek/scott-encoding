{-# LANGUAGE Rank2Types #-}

module HScott where


data Nat = S Nat | Z deriving (Eq, Show)


type BoolS = forall a. a -> a -> a

unboolS :: a -> a -> BoolS -> a
unboolS a a' b = b a a'

trueS :: BoolS
trueS = \a a' -> a

falseS :: BoolS
falseS = \a a' -> a'

fromBoolS :: BoolS -> Bool
fromBoolS = unboolS True False

toBoolS :: Bool -> BoolS
toBoolS True = trueS
toBoolS False = falseS


type MaybeS a = forall b. (a -> b) -> b -> b

unmaybeS :: (a -> b) -> b -> MaybeS a -> b
unmaybeS f b m = m f b

justS :: a -> MaybeS a
justS a = \f b -> f a

nothingS :: MaybeS a
nothingS = \f b -> b

fromMaybeS :: MaybeS a -> Maybe a
fromMaybeS = unmaybeS Just Nothing

toMaybeS :: Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


type EitherS a b = forall c. (a -> c) -> (b -> c) -> c

uneitherS :: (a -> c) -> (b -> c) -> EitherS a b -> c
uneitherS f g e = e f g

leftS :: a -> EitherS a b
leftS a = \f g -> f a

rightS :: b -> EitherS a b
rightS b = \f g -> g b

fromEitherS :: EitherS a b -> Either a b
fromEitherS = uneitherS Left Right

toEitherS :: Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


type PairS a b = forall c. (a -> b -> c) -> c

unpairS :: (a -> b -> c) -> PairS a b -> c
unpairS f p = p f

pairS :: a -> b -> PairS a b
pairS a b = \f -> f a b

fromPairS :: PairS a b -> (a, b)
fromPairS = unpairS (\a b -> (a, b))

toPairS :: (a, b) -> PairS a b
toPairS (a, b) = pairS a b

fstS :: PairS a b -> a
fstS = unpairS (\a b -> a)

sndS :: PairS a b -> b
sndS = unpairS (\a b -> b)


type NatS = forall a. (a -> a) -> a -> a

unnatS :: (a -> a) -> a -> NatS -> a
unnatS f a n = n f a

succS :: NatS -> NatS
succS n = \f a -> f (n f a)

zeroS :: NatS
zeroS = \f a -> a

fromNatS :: NatS -> Nat
fromNatS = unnatS S Z

toNatS :: Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS


type ListS a = forall b. (a -> b -> b) -> b -> b

unlistS :: (a -> b -> b) -> b -> ListS a -> b
unlistS f b l = l f b

consS :: a -> ListS a -> ListS a
consS a l = \f b -> f a (l f b)

nilS :: ListS a
nilS = \f b -> b

fromListS :: ListS a -> [a]
fromListS = unlistS (:) []

toListS :: [a] -> ListS a
toListS (a : l) = consS a (toListS l)
toListS []      = nilS
