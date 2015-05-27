module Scott

%default total


data Bool_ = B ({a : Type} -> a -> a -> a)

true_ : Bool_
true_ = B (\a, a' => a)

false_ : Bool_
false_ = B (\a, a' => a')

if_ : Bool_ -> a -> a -> a
if_ (B b) a a' = b a a'

_ifTrue : if_ true_ a a' = a
_ifTrue = Refl

_ifFalse : if_ false_ a a' = a'
_ifFalse = Refl


data Maybe_ a = M ({b : Type} -> (a -> b) -> b -> b)

just_ : a -> Maybe_ a
just_ a = M (\f, b => f a)

nothing_ : Maybe_ a
nothing_ = M (\f, b => b)

maybe_ : Maybe_ a -> (a -> b) -> b -> b
maybe_ (M m) f b = m f b

_maybeJust : maybe_ (just_ a) f b = f a
_maybeJust = Refl

_maybeNothing : maybe_ nothing_ f b = b
_maybeNothing = Refl


data Pair_ a b = P ({c : Type} -> (a -> b -> c) -> c)

pair_ : a -> b -> Pair_ a b
pair_ a b = P (\f => f a b)

fst_ : Pair_ a b -> a
fst_ (P p) = p (\a, b => a)

snd_ : Pair_ a b -> b
snd_ (P p) = p (\a, b => b)

_fstPair : fst_ (pair_ a b) = a
_fstPair = Refl

_sndPair : snd_ (pair_ a b) = b
_sndPair = Refl


data Nat_ = N ({a : Type} -> (Nat_ -> a) -> a -> a)

succ_ : Nat_ -> Nat_
succ_ n = N (\f, a => f n)

zero_ : Nat_
zero_ = N (\f, a => a)

pred_ : Nat_ -> (Nat_ -> a) -> a -> a
pred_ (N n) f a = n f a

_predSucc : pred_ (succ_ n) f a = f n
_predSucc = Refl

_predZero : pred_ zero_ f a = a
_predZero = Refl
