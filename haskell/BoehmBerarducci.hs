{-# LANGUAGE Rank2Types #-}

module BoehmBerarducci where


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
toListS (a : aa) = consS a (toListS aa)
toListS []       = nilS
