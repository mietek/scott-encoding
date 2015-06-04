{-# LANGUAGE Rank2Types #-}

module Common where


type BoolQ = forall a. a -> a -> a

unBoolQ :: a -> a -> BoolQ -> a
unBoolQ a a' q = q a a'

trueQ :: BoolQ
trueQ = \a a' -> a

falseQ :: BoolQ
falseQ = \a a' -> a'

fromBoolQ :: BoolQ -> Bool
fromBoolQ q = unBoolQ True False q

toBoolQ :: Bool -> BoolQ
toBoolQ True = trueQ
toBoolQ False = falseQ


type MaybeQ a = forall b. (a -> b) -> b -> b

unMaybeQ :: (a -> b) -> b -> MaybeQ a -> b
unMaybeQ f b q = q f b

justQ :: a -> MaybeQ a
justQ a = \f b -> f a

nothingQ :: MaybeQ a
nothingQ = \f b -> b

fromMaybeQ :: MaybeQ a -> Maybe a
fromMaybeQ q = unMaybeQ Just Nothing q

toMaybeQ :: Maybe a -> MaybeQ a
toMaybeQ (Just a) = justQ a
toMaybeQ Nothing  = nothingQ


type EitherQ a b = forall c. (a -> c) -> (b -> c) -> c

unEitherQ :: (a -> c) -> (b -> c) -> EitherQ a b -> c
unEitherQ f g q = q f g

leftQ :: a -> EitherQ a b
leftQ a = \f g -> f a

rightQ :: b -> EitherQ a b
rightQ b = \f g -> g b

fromEitherQ :: EitherQ a b -> Either a b
fromEitherQ q = unEitherQ Left Right q

toEitherQ :: Either a b -> EitherQ a b
toEitherQ (Left a)  = leftQ a
toEitherQ (Right b) = rightQ b


type PairQ a b = forall c. (a -> b -> c) -> c

unPairQ :: (a -> b -> c) -> PairQ a b -> c
unPairQ f q = q f

pairQ :: a -> b -> PairQ a b
pairQ a b = \f -> f a b

fromPairQ :: PairQ a b -> (a, b)
fromPairQ q = unPairQ (\a b -> (a, b)) q

toPairQ :: (a, b) -> PairQ a b
toPairQ (a, b) = pairQ a b

fstQ :: PairQ a b -> a
fstQ q = unPairQ (\a b -> a) q

sndQ :: PairQ a b -> b
sndQ q = unPairQ (\a b -> b) q
