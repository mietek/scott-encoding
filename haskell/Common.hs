{-# LANGUAGE Rank2Types #-}

module Common where


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

fstS :: PairS a b -> a
fstS s = unPairS (\a b -> a) s

sndS :: PairS a b -> b
sndS s = unPairS (\a b -> b) s
