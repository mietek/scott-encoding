{-# LANGUAGE Rank2Types #-}

module Scott where


newtype Bool_ = B (forall a. a -> a -> a)

true_ :: Bool_
true_ = B (\a a' -> a)

false_ :: Bool_
false_ = B (\a a' -> a')

if_ :: Bool_ -> a -> a -> a
if_ (B b) a a' = b a a'


newtype Maybe_ a = M (forall b. (a -> b) -> b -> b)

just_ :: a -> Maybe_ a
just_ a = M (\f b -> f a)

nothing_ :: Maybe_ a
nothing_ = M (\f b -> b)

maybe_ :: Maybe_ a -> (a -> b) -> b -> b
maybe_ (M m) f b = m f b


newtype Pair_ a b = P (forall c. (a -> b -> c) -> c)

pair_ :: a -> b -> Pair_ a b
pair_ a b = P (\f -> f a b)

fst_ :: Pair_ a b -> a
fst_ (P p) = p (\a b -> a)

snd_ :: Pair_ a b -> b
snd_ (P p) = p (\a b -> b)


newtype Nat_ = N (forall a. (Nat_ -> a) -> a -> a)

succ_ :: Nat_ -> Nat_
succ_ n = N (\f a -> f n)

zero_ :: Nat_
zero_ = N (\f a -> a)

pred_ :: Nat_ -> (Nat_ -> a) -> a -> a
pred_ (N n) f a = n f a
