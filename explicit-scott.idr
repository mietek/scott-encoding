module Scott

%default total


Bool_ : Type
Bool_ = (a : Type) -> a -> a -> a

true_ : Bool_
true_ = \_, a, a' => a

false_ : Bool_
false_ = \_, a, a' => a'

if_ : Bool_ -> a -> a -> a
if_ b a a' = b _ a a'

_ifTrue : if_ true_ a a' = a
_ifTrue = Refl

_ifFalse : if_ false_ a a' = a'
_ifFalse = Refl


Maybe_ : Type -> Type
Maybe_ a = (b : Type) -> b -> (a -> b) -> b

nothing_ : Maybe_ a
nothing_ = \_, b, f => b

just_ : a -> Maybe_ a
just_ a = \_, b, f => f a

maybe_ : Maybe_ a -> b -> (a -> b) -> b
maybe_ m b f = m _ b f

_maybeNothing : maybe_ nothing_ b f = b
_maybeNothing = Refl

_maybeJust : maybe_ (just_ a) b f = f a
_maybeJust = Refl


Pair_ : Type -> Type -> Type
Pair_ a b = (c : Type) -> (a -> b -> c) -> c

pair_ : a -> b -> Pair_ a b
pair_ a b = \_, f => f a b

fst_ : Pair_ a b -> a
fst_ p = p _ (\a, b => a)

snd_ : Pair_ a b -> b
snd_ p = p _ (\a, b => b)

_fstPair : fst_ (pair_ a b) = a
_fstPair = Refl

_sndPair : snd_ (pair_ a b) = b
_sndPair = Refl


Nat_ : Type
Nat_ = (a : Type) -> a -> (Nat_ -> a) -> a

-- NOTE: For some reason, Idris does not accept the commented-out things.

-- zero_ : Nat_
zero_ : (a : Type) -> a -> (Nat_ -> a) -> a
zero_ = \_, a, f => a

-- succ_ : Nat_ -> Nat_
succ_ : Nat_ -> (a : Type) -> a -> (Nat_ -> a) -> a
succ_ n = \_, a, f => f n

-- pred_ : Nat_ -> a -> (Nat_ -> a) -> a
pred_ : ((a : Type) -> a -> (Nat_ -> a) -> a) -> a -> (Nat_ -> a) -> a
pred_ n a f = n _ a f

-- _predZero : pred_ zero_ a f = a
-- _predZero = Refl

-- _predSucc : pred_ (succ_ n) a f = f n
-- _predSucc = Refl
