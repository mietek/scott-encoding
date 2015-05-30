-- NOTE: The commented-out types are due to:
-- https://github.com/idris-lang/Idris-dev/issues/2119

module Scott

%default total

iterated : Nat -> (a -> a) -> a -> a
iterated (S k) f x = f (iterated k f x)
iterated Z f x = x


Bool_ : Type
Bool_ = {a : Type} -> a -> a -> a

true_ : Bool_
true_ = \a, a' => a

false_ : Bool_
false_ = \a, a' => a'

unbool_ : Bool_ -> a -> a -> a
unbool_ b a a' = b a a'

fromBool_ : Bool_ -> Bool
fromBool_ b = unbool_ b True False

-- toBool_ : Bool -> Bool_
toBool_ : Bool -> a -> a -> a
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


Maybe_ : Type -> Type
Maybe_ a = {b : Type} -> (a -> b) -> b -> b

just_ : a -> Maybe_ a
just_ a = \f, b => f a

nothing_ : Maybe_ a
nothing_ = \f, b => b

unmaybe_ : Maybe_ a -> (a -> b) -> b -> b
unmaybe_ m f b = m f b

fromMaybe_ : Maybe_ a -> Maybe a
fromMaybe_ m = unmaybe_ m Just Nothing

-- toMaybe_ : Maybe a -> Maybe_ a
toMaybe_ : Maybe a -> (a -> b) -> b -> b
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


Pair_ : Type -> Type -> Type
Pair_ a b = {c : Type} -> (a -> b -> c) -> c

pair_ : a -> b -> Pair_ a b
pair_ a b = \f => f a b

unpair_ : Pair_ a b -> (a -> b -> c) -> c
unpair_ p f = p f

fromPair_ : Pair_ a b -> (a, b)
fromPair_ p = unpair_ p (\a, b => (a, b))

-- toPair_ : (a, b) -> Pair_ a b
toPair_ : (a, b) -> (a -> b -> c) -> c
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


Nat_ : Type
Nat_ = {a : Type} -> (a -> a) -> a -> a

succ_ : Nat_ -> Nat_
succ_ n = \f, a => n f (f a)

zero_ : Nat_
zero_ = \f, a => a

unnat_ : Nat_ -> (a -> a) -> a -> a
unnat_ n f a = n f a

fromNat_ : Nat_ -> Nat
fromNat_ n = unnat_ n S Z

-- toNat_ : Nat -> Nat_
toNat_ : Nat -> (a -> a) -> a -> a
toNat_ (S n) = succ_ (toNat_ n)
toNat_ Z = zero_

-- TODO: Figure out how to prove the following:
--
-- _fromNat : {n : Nat} -> fromNat_ (iterated n succ_ zero_) = n
-- _fromNat = Refl
--
-- _toNat : {n : Nat} -> toNat_ n = iterated n succ_ zero_
-- _toNat = Refl


List_ : Type -> Type
List_ a = {b : Type} -> (a -> b -> b) -> b -> b

cons_ : a -> List_ a -> List_ a
cons_ a l = \f, b => l f (f a b)

nil_ : List_ a
nil_ = \f, b => b

unlist_ : List_ a -> (a -> b -> b) -> b -> b
unlist_ l f b = l f b

fromList_ : List_ a -> List a
fromList_ l = unlist_ l (::) []

-- toList_ : List a -> List_ a
toList_ : List a -> (a -> b -> b) -> b -> b
toList_ (a :: l) = cons_ a (toList_ l)
toList_ [] = nil_
