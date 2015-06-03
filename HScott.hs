{-# LANGUAGE Rank2Types #-}

module HScott where


type BoolS = forall a. a -> a -> a

unBoolS :: a -> a -> BoolS -> a
unBoolS a a' s = s a a'

trueS :: BoolS
trueS = \a a' -> a

falseS :: BoolS
falseS = \a a' -> a'

fromBoolS :: BoolS -> Bool
fromBoolS s = unBoolS True False s

toBoolS :: Bool -> BoolS
toBoolS True = trueS
toBoolS False = falseS


type MaybeS a = forall b. (a -> b) -> b -> b

unMaybeS :: (a -> b) -> b -> MaybeS a -> b
unMaybeS f b s = s f b

justS :: a -> MaybeS a
justS a = \f b -> f a

nothingS :: MaybeS a
nothingS = \f b -> b

fromMaybeS :: MaybeS a -> Maybe a
fromMaybeS s = unMaybeS Just Nothing s

toMaybeS :: Maybe a -> MaybeS a
toMaybeS (Just a) = justS a
toMaybeS Nothing  = nothingS


type EitherS a b = forall c. (a -> c) -> (b -> c) -> c

unEitherS :: (a -> c) -> (b -> c) -> EitherS a b -> c
unEitherS f g s = s f g

leftS :: a -> EitherS a b
leftS a = \f g -> f a

rightS :: b -> EitherS a b
rightS b = \f g -> g b

fromEitherS :: EitherS a b -> Either a b
fromEitherS s = unEitherS Left Right s

toEitherS :: Either a b -> EitherS a b
toEitherS (Left a)  = leftS a
toEitherS (Right b) = rightS b


type PairS a b = forall c. (a -> b -> c) -> c

unPairS :: (a -> b -> c) -> PairS a b -> c
unPairS f s = s f

pairS :: a -> b -> PairS a b
pairS a b = \f -> f a b

fromPairS :: PairS a b -> (a, b)
fromPairS s = unPairS (\a b -> (a, b)) s

toPairS :: (a, b) -> PairS a b
toPairS (a, b) = pairS a b

firstS :: PairS a b -> a
firstS s = unPairS (\a b -> a) s

secondS :: PairS a b -> b
secondS s = unPairS (\a b -> b) s


data Nat = S Nat | Z deriving (Eq, Ord, Read, Show)

type NatS = forall a. (a -> a) -> a -> a

unNatS :: (a -> a) -> a -> NatS -> a
unNatS f a s = s f a

succS :: NatS -> NatS
succS s = \f a -> f (s f a)

zeroS :: NatS
zeroS = \f a -> a

fromNatS :: NatS -> Nat
fromNatS s = unNatS S Z s

toNatS :: Nat -> NatS
toNatS (S n) = succS (toNatS n)
toNatS Z     = zeroS


type ListS a = forall b. (a -> b -> b) -> b -> b

unListS :: (a -> b -> b) -> b -> ListS a -> b
unListS f b s = s f b

consS :: a -> ListS a -> ListS a
consS a s = \f b -> f a (s f b)

nilS :: ListS a
nilS = \f b -> b

fromListS :: ListS a -> [a]
fromListS s = unListS (:) [] s

toListS :: [a] -> ListS a
toListS (a : as) = consS a (toListS as)
toListS []       = nilS
