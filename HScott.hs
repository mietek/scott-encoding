{-# LANGUAGE Rank2Types #-}

module HScott where


type BoolS = forall a. a -> a -> a

unboolS :: a -> a -> BoolS -> a
unboolS a a' s = s a a'

trueS :: BoolS
trueS = \a a' -> a

falseS :: BoolS
falseS = \a a' -> a'

fromBoolS :: BoolS -> Bool
fromBoolS s = unboolS True False s

toBoolS :: Bool -> BoolS
toBoolS True = trueS
toBoolS False = falseS


type MaybeS a = forall b. (a -> b) -> b -> b

unmaybeS :: (a -> b) -> b -> MaybeS a -> b
unmaybeS f b s = s f b

justS :: a -> MaybeS a
justS a = \f b -> f a

nothingS :: MaybeS a
nothingS = \f b -> b

fromMaybeS :: MaybeS a -> Maybe a
fromMaybeS s = unmaybeS Just Nothing s

toMaybeS :: Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


type EitherS a b = forall c. (a -> c) -> (b -> c) -> c

uneitherS :: (a -> c) -> (b -> c) -> EitherS a b -> c
uneitherS f g s = s f g

leftS :: a -> EitherS a b
leftS a = \f g -> f a

rightS :: b -> EitherS a b
rightS b = \f g -> g b

fromEitherS :: EitherS a b -> Either a b
fromEitherS s = uneitherS Left Right s

toEitherS :: Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


type PairS a b = forall c. (a -> b -> c) -> c

unpairS :: (a -> b -> c) -> PairS a b -> c
unpairS f s = s f

pairS :: a -> b -> PairS a b
pairS a b = \f -> f a b

fromPairS :: PairS a b -> (a, b)
fromPairS s = unpairS (\a b -> (a, b)) s

toPairS :: (a, b) -> PairS a b
toPairS (a, b) = pairS a b

fstS :: PairS a b -> a
fstS s = unpairS (\a b -> a) s

sndS :: PairS a b -> b
sndS s = unpairS (\a b -> b) s


type NatS = forall a. (a -> a) -> a -> a

unnatS :: (a -> a) -> a -> NatS -> a
unnatS f a s = s f a

succS :: NatS -> NatS
succS s = \f a -> f (s f a)

zeroS :: NatS
zeroS = \f a -> a

fromNatS :: NatS -> Nat
fromNatS s = unnatS S Z s

toNatS :: Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS


type ListS a = forall b. (a -> b -> b) -> b -> b

unlistS :: (a -> b -> b) -> b -> ListS a -> b
unlistS f b s = s f b

consS :: a -> ListS a -> ListS a
consS a s = \f b -> f a (s f b)

nilS :: ListS a
nilS = \f b -> b

fromListS :: ListS a -> [a]
fromListS s = unlistS (:) [] s

toListS :: [a] -> ListS a
toListS (a : as) = consS a (toListS as)
toListS []       = nilS


data Nat = S Nat | Z deriving (Eq, Show)
