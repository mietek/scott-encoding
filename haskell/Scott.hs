{-# LANGUAGE Rank2Types #-}

module Scott where


data Nat = S Nat | Z deriving (Eq, Ord, Read, Show)


newtype NatQ = N (forall a. (NatQ -> a) -> a -> a)

caseNatQ :: (NatQ -> a) -> a -> NatQ -> a
caseNatQ f a (N q) = q f a

foldNatQ :: (a -> a) -> a -> NatQ -> a
foldNatQ f a q = caseNatQ (\q' -> f (foldNatQ f a q')) a q

succQ :: NatQ -> NatQ
succQ q = N (\f _a -> f q)

zeroQ :: NatQ
zeroQ = N (\_f a -> a)

fromNatQ :: NatQ -> Nat
fromNatQ q = foldNatQ S Z q

toNatQ :: Nat -> NatQ
toNatQ (S n) = succQ (toNatQ n)
toNatQ Z     = zeroQ


newtype ListQ a = L (forall b. (a -> ListQ a -> b) -> b -> b)

caseListQ :: (a -> ListQ a -> b) -> b -> ListQ a -> b
caseListQ f b (L q) = q f b

foldListQ :: (a -> b -> b) -> b -> ListQ a -> b
foldListQ f b q = caseListQ (\a q' -> f a (foldListQ f b q')) b q

consQ :: a -> ListQ a -> ListQ a
consQ a q = L (\f _b -> f a q)

nilQ :: ListQ a
nilQ = L (\_f b -> b)

headQ :: (a -> b) -> b -> ListQ a -> b
headQ f b q = caseListQ (\a _q' -> f a) b q

lastQ :: (a -> b) -> b -> ListQ a -> b
lastQ f b q = caseListQ loop b q
  where
    loop a q' = caseListQ loop (f a) q'

tailQ :: ListQ a -> ListQ a
tailQ q = caseListQ (\_a q' -> q') nilQ q

initQ :: ListQ a -> ListQ a
initQ q = caseListQ loop nilQ q
  where
    loop a q' = caseListQ (\a' q'' -> consQ a (loop a' q'')) nilQ q'

fromListQ :: ListQ a -> [a]
fromListQ q = foldListQ (:) [] q

toListQ :: [a] -> ListQ a
toListQ (a : aa) = consQ a (toListQ aa)
toListQ []       = nilQ
