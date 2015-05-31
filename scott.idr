module Scott

%default total

iterated : Nat -> (a -> a) -> a -> a
iterated (S n) f a = f (iterated n f a)
iterated Z f a = a

test_iterated_ : (n : Nat) -> iterated n S Z = n
test_iterated_ (S n) = rewrite test_iterated_ n in Refl
test_iterated_ Z = Refl



Bool_ : Type
Bool_ = (a : Type) -> a -> a -> a

true_ : Bool_
true_ = \_, a, a' => a

false_ : Bool_
false_ = \_, a, a' => a'

unbool_ : Bool_ -> a -> a -> a
unbool_ b a a' = b _ a a'

fromBool_ : Bool_ -> Bool
fromBool_ b = unbool_ b True False

toBool_ : Bool -> Bool_
toBool_ True = true_
toBool_ False = false_

test_unboolTrue : unbool_ true_ a a' = a
test_unboolTrue = Refl

test_unboolFalse : unbool_ false_ a a' = a'
test_unboolFalse = Refl

test_fromTrue : fromBool_ true_ = True
test_fromTrue = Refl

test_fromFalse : fromBool_ false_ = False
test_fromFalse = Refl

test_toTrue : toBool_ True = true_
test_toTrue = Refl

test_toFalse : toBool_ False = false_
test_toFalse = Refl


Maybe_ : Type -> Type
Maybe_ a = (b : Type) -> (a -> b) -> b -> b

just_ : a -> Maybe_ a
just_ a = \_, f, b => f a

nothing_ : Maybe_ a
nothing_ = \_, f, b => b

unmaybe_ : Maybe_ a -> (a -> b) -> b -> b
unmaybe_ m f b = m _ f b

fromMaybe_ : Maybe_ a -> Maybe a
fromMaybe_ m = unmaybe_ m Just Nothing

toMaybe_ : Maybe a -> Maybe_ a
toMaybe_ (Just a) = just_ a
toMaybe_ Nothing = nothing_

test_unmaybeJust_ : unmaybe_ (just_ a) f b = f a
test_unmaybeJust_ = Refl

test_unmaybeNothing_ : unmaybe_ nothing_ f b = b
test_unmaybeNothing_ = Refl

test_fromJust_ : fromMaybe_ (just_ a) = Just a
test_fromJust_ = Refl

test_fromNothing_ : fromMaybe_ nothing_ = Nothing
test_fromNothing_ = Refl

test_toJust_ : toMaybe_ (Just a) = just_ a
test_toJust_ = Refl

test_toNothing_ : toMaybe_ Nothing = nothing_
test_toNothing_ = Refl


Pair_ : Type -> Type -> Type
Pair_ a b = (c : Type) -> (a -> b -> c) -> c

pair_ : a -> b -> Pair_ a b
pair_ a b = \_, f => f a b

unpair_ : Pair_ a b -> (a -> b -> c) -> c
unpair_ p f = p _ f

fromPair_ : Pair_ a b -> (a, b)
fromPair_ p = unpair_ p (\a, b => (a, b))

toPair_ : (a, b) -> Pair_ a b
toPair_ (a, b) = pair_ a b

fst_ : Pair_ a b -> a
fst_ p = unpair_ p (\a, b => a)

snd_ : Pair_ a b -> b
snd_ p = unpair_ p (\a, b => b)

test_unpairPair_ : unpair_ (pair_ a b) (\a, b => (a, b)) = (a, b)
test_unpairPair_ = Refl

test_fromPair_ : fromPair_ (pair_ a b) = (a, b)
test_fromPair_ = Refl

test_toPair_ : toPair_ (a, b) = pair_ a b
test_toPair_ = Refl

test_fstPair_ : fst_ (pair_ a b) = a
test_fstPair_ = Refl

test_sndPair_ : snd_ (pair_ a b) = b
test_sndPair_ = Refl


Nat_ : Type
Nat_ = (a : Type) -> (a -> a) -> a -> a

succ_ : Nat_ -> Nat_
succ_ n = \_, f, a => n _ f (f a)

zero_ : Nat_
zero_ = \_, f, a => a

unnat_ : Nat_ -> (a -> a) -> a -> a
unnat_ n f a = n _ f a

fromNat_ : Nat_ -> Nat
fromNat_ n = unnat_ n S Z

toNat_ : Nat -> Nat_
toNat_ (S n) = succ_ (toNat_ n)
toNat_ Z = zero_

test_toNat_ : (n : Nat) -> toNat_ n = iterated n succ_ zero_
test_toNat_ (S n) = rewrite test_toNat_ n in Refl
test_toNat_ Z = Refl

-- TODO: Figure out how to prove the following:

-- test_fromNat_ : (n : Nat) -> fromNat_ (iterated n succ_ zero_) = n
-- test_fromNat_ (S n) = rewrite test_fromNat_ n in Refl
-- test_fromNat_ Z = Refl


List_ : Type -> Type
List_ a = (b : Type) -> (a -> b -> b) -> b -> b

cons_ : a -> List_ a -> List_ a
cons_ a l = \_, f, b => l _ f (f a b)

nil_ : List_ a
nil_ = \_, f, b => b

unlist_ : List_ a -> (a -> b -> b) -> b -> b
unlist_ l f b = l _ f b

fromList_ : List_ a -> List a
fromList_ l = unlist_ l (::) []

toList_ : List a -> List_ a
toList_ (a :: l) = cons_ a (toList_ l)
toList_ [] = nil_

test_toList_ : (n : Nat) -> toList_ (iterated n (() ::) []) = iterated n (cons_ ()) nil_
test_toList_ (S n) = rewrite test_toList_ n in Refl
test_toList_ Z = Refl

-- TODO: Figure out how to prove the following:

-- test_fromList_ : (n : Nat) -> fromList_ (iterated n (cons_ ()) nil_) = iterated n (() ::) []
-- test_fromList_ (S n) = rewrite test_fromList_ n in Refl
-- test_fromList_ Z = Refl
