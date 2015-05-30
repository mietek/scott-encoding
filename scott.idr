module Scott

%default total

iterated : Nat -> (a -> a) -> a -> a
iterated (S k) f x = f (iterated k f x)
iterated Z f x = x


data Bool_ = B ({a : Type} -> a -> a -> a)

true_ : Bool_
true_ = B (\a, a' => a)

false_ : Bool_
false_ = B (\a, a' => a')

unbool_ : Bool_ -> a -> a -> a
unbool_ (B b) a a' = b a a'

fromBool_ : Bool_ -> Bool
fromBool_ b = unbool_ b True False

toBool_ : Bool -> Bool_
toBool_ True = true_
toBool_ False = false_

_unboolTrue : unbool_ true_ a a' = a
_unboolTrue = Refl

_unboolFalse : unbool_ false_ a a' = a'
_unboolFalse = Refl

_fromTrue : fromBool_ true_ = True
_fromTrue = Refl

_fromFalse : fromBool_ false_ = False
_fromFalse = Refl

_toTrue : toBool_ True = true_
_toTrue = Refl

_toFalse : toBool_ False = false_
_toFalse = Refl


data Maybe_ a = M ({b : Type} -> (a -> b) -> b -> b)

just_ : a -> Maybe_ a
just_ a = M (\f, b => f a)

nothing_ : Maybe_ a
nothing_ = M (\f, b => b)

unmaybe_ : Maybe_ a -> (a -> b) -> b -> b
unmaybe_ (M m) f b = m f b

fromMaybe_ : Maybe_ a -> Maybe a
fromMaybe_ m = unmaybe_ m Just Nothing

toMaybe_ : Maybe a -> Maybe_ a
toMaybe_ (Just a) = just_ a
toMaybe_ Nothing = nothing_

_unmaybeJust : unmaybe_ (just_ a) f b = f a
_unmaybeJust = Refl

_unmaybeNothing : unmaybe_ nothing_ f b = b
_unmaybeNothing = Refl

_fromJust : fromMaybe_ (just_ a) = Just a
_fromJust = Refl

_fromNothing : fromMaybe_ nothing_ = Nothing
_fromNothing = Refl

_toJust : toMaybe_ (Just a) = just_ a
_toJust = Refl

_toNothing : toMaybe_ Nothing = nothing_
_toNothing = Refl


data Pair_ a b = P ({c : Type} -> (a -> b -> c) -> c)

pair_ : a -> b -> Pair_ a b
pair_ a b = P (\f => f a b)

unpair_ : Pair_ a b -> (a -> b -> c) -> c
unpair_ (P p) f = p f

fromPair_ : Pair_ a b -> (a, b)
fromPair_ p = unpair_ p (\a, b => (a, b))

toPair_ : (a, b) -> Pair_ a b
toPair_ (a, b) = pair_ a b

fst_ : Pair_ a b -> a
fst_ p = unpair_ p (\a, b => a)

snd_ : Pair_ a b -> b
snd_ p = unpair_ p (\a, b => b)

_unpairPair : unpair_ (pair_ a b) (\a, b => (a, b)) = (a, b)
_unpairPair = Refl

_fromPair : fromPair_ (pair_ a b) = (a, b)
_fromPair = Refl

_toPair : toPair_ (a, b) = pair_ a b
_toPair = Refl

_fstPair : fst_ (pair_ a b) = a
_fstPair = Refl

_sndPair : snd_ (pair_ a b) = b
_sndPair = Refl


data Nat_ = N ({a : Type} -> (a -> a) -> a -> a)

succ_ : Nat_ -> Nat_
succ_ (N n) = N (\f, a => n f (f a))

zero_ : Nat_
zero_ = N (\f, a => a)

unnat_ : Nat_ -> (a -> a) -> a -> a
unnat_ (N n) f a = n f a

fromNat_ : Nat_ -> Nat
fromNat_ n = unnat_ n S Z

toNat_ : Nat -> Nat_
toNat_ (S n) = succ_ (toNat_ n)
toNat_ Z = zero_

-- TODO: Figure out how to use %elim to prove the following:
--
-- _fromNat : {n : Nat} -> fromNat_ (iterated n succ_ zero_) = n
-- _fromNat = Refl
--
-- _toNat : {n : Nat} -> toNat_ n = iterated n succ_ zero_
-- _toNat = Refl


data List_ a = L ({b : Type} -> (a -> b -> b) -> b -> b)

cons_ : a -> List_ a -> List_ a
cons_ a (L l) = L (\f, b => l f (f a b))

nil_ : List_ a
nil_ = L (\f, b => b)

unlist_ : List_ a -> (a -> b -> b) -> b -> b
unlist_ (L l) f b = l f b

fromList_ : List_ a -> List a
fromList_ l = unlist_ l (::) []

toList_ : List a -> List_ a
toList_ (a :: l) = cons_ a (toList_ l)
toList_ [] = nil_
