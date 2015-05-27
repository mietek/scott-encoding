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


data Maybe_ a = M ({b : Type} -> b -> (a -> b) -> b)

nothing_ : Maybe_ a
nothing_ = M (\b, f => b)

just_ : a -> Maybe_ a
just_ a = M (\b, f => f a)

maybe_ : Maybe_ a -> b -> (a -> b) -> b
maybe_ (M m) b f = m b f

_maybeNothing : maybe_ nothing_ b f = b
_maybeNothing = Refl

_maybeJust : maybe_ (just_ a) b f = f a
_maybeJust = Refl


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


data Nat_ = N ({a : Type} -> a -> (Nat_ -> a) -> a)

zero_ : Nat_
zero_ = N (\a, f => a)

succ_ : Nat_ -> Nat_
succ_ n = N (\a, f => f n)

pred_ : Nat_ -> a -> (Nat_ -> a) -> a
pred_ (N n) a f = n a f

_predZero : pred_ zero_ a f = a
_predZero = Refl

_predSucc : pred_ (succ_ n) a f = f n
_predSucc = Refl
