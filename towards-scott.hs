{-# LANGUAGE Rank2Types #-}

module Scott where


newtype Bool_ = B (forall a. a -> a -> a)

true_ :: Bool_
true_ = B (\a a' -> a)

false_ :: Bool_
false_ = B (\a a' -> a')

if_ :: Bool_ -> a -> a -> a
if_ (B b) a a' = b a a'


newtype Maybe_ a = M (forall b. b -> (a -> b) -> b)

nothing_ :: Maybe_ a
nothing_ = M (\b f -> b)

just_ :: a -> Maybe_ a
just_ a = M (\b f -> f a)

maybe_ :: Maybe_ a -> b -> (a -> b) -> b
maybe_ (M m) b f = m b f


newtype Pair_ a b = P (forall c. (a -> b -> c) -> c)

pair_ :: a -> b -> Pair_ a b
pair_ a b = P (\f -> f a b)

fst_ :: Pair_ a b -> a
fst_ (P p) = p (\a b -> a)

snd_ :: Pair_ a b -> b
snd_ (P p) = p (\a b -> b)


newtype Nat_ = N (forall a. a -> (Nat_ -> a) -> a)

zero_ :: Nat_
zero_ = N (\a f -> a)

succ_ :: Nat_ -> Nat_
succ_ n = N (\a f -> f n)

pred_ :: Nat_ -> a -> (Nat_ -> a) -> a
pred_ (N n) a f = n a f
