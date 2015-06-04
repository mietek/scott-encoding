{-# LANGUAGE Rank2Types #-}

module BoehmBerarducci where


data Nat = S Nat | Z deriving (Eq, Ord, Read, Show)


type NatQ = forall a. (a -> a) -> a -> a

foldNatQ :: (a -> a) -> a -> NatQ -> a
foldNatQ f a q = q f a

-- caseNatQ :: (NatQ -> a) -> a -> NatQ -> a
-- TODO

succQ :: NatQ -> NatQ
succQ q = \f a -> f (q f a)

zeroQ :: NatQ
zeroQ = \_f a -> a

fromNatQ :: NatQ -> Nat
fromNatQ q = foldNatQ S Z q

toNatQ :: Nat -> NatQ
toNatQ (S n) = succQ (toNatQ n)
toNatQ Z     = zeroQ


newtype ListQ a = L (forall b. (a -> b -> b) -> b -> b)

foldListQ :: (a -> b -> b) -> b -> ListQ a -> b
foldListQ f b (L q) = q f b

-- caseListQ :: (a -> ListQ a -> b) -> b -> ListQ a -> b
-- TODO

consQ :: a -> ListQ a -> ListQ a
consQ a (L q) = L (\f b -> f a (foldListQ f b (L q)))

nilQ :: ListQ a
nilQ = L (\_f b -> b)

headQ :: (a -> b) -> b -> ListQ a -> b
headQ f b q = foldListQ (\a _b' -> f a) b q

-- lastQ :: (a -> b) -> b -> ListQ a -> b
-- TODO

tailQ :: (ListQ a -> b) -> b -> ListQ a -> b
tailQ f b q = fst (foldListQ (\a (_, b') -> (b', f consQ a b')) (b, nilQ) q)

-- initQ :: ListQ a -> ListQ a
-- TODO

fromListQ :: ListQ a -> [a]
fromListQ q = foldListQ (:) [] q

toListQ :: [a] -> ListQ a
toListQ (a : aa) = consQ a (toListQ aa)
toListQ []       = nilQ
