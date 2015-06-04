{-# LANGUAGE Rank2Types #-}

module BoehmBerarducci where


data Nat = S Nat | Z deriving (Eq, Ord, Read, Show)

type NatQ = forall a. (a -> a) -> a -> a

unNatQ :: (a -> a) -> a -> NatQ -> a
unNatQ f a s = s f a

succQ :: NatQ -> NatQ
succQ s = \f a -> f (s f a)

zeroQ :: NatQ
zeroQ = \f a -> a

fromNatQ :: NatQ -> Nat
fromNatQ s = unNatQ S Z s

toNatQ :: Nat -> NatQ
toNatQ (S n) = succQ (toNatQ n)
toNatQ Z     = zeroQ


type ListQ a = forall b. (a -> b -> b) -> b -> b

unListQ :: (a -> b -> b) -> b -> ListQ a -> b
unListQ f b s = s f b

consQ :: a -> ListQ a -> ListQ a
consQ a s = \f b -> f a (s f b)

nilQ :: ListQ a
nilQ = \f b -> b

fromListQ :: ListQ a -> [a]
fromListQ s = unListQ (:) [] s

toListQ :: [a] -> ListQ a
toListQ (a : aa) = consQ a (toListQ aa)
toListQ []       = nilQ
