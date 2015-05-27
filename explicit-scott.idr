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
Maybe_ a = (b : Type) -> (a -> b) -> b -> b

just_ : a -> Maybe_ a
just_ a = \_, f, b => f a

nothing_ : Maybe_ a
nothing_ = \_, f, b => b

maybe_ : Maybe_ a -> (a -> b) -> b -> b
maybe_ m f b = m _ f b

_maybeJust : maybe_ (just_ a) f b = f a
_maybeJust = Refl

_maybeNothing : maybe_ nothing_ f b = b
_maybeNothing = Refl


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


-- NOTE: The following is accepted, but is also wrong.

Nat_ : Type
Nat_ = (a : Type) -> (Nat_ -> a) -> a -> a

-- succ_ : Nat_ -> Nat_
succ_ : Nat_ -> (a : Type) -> (Nat_ -> a) -> a -> a
succ_ n = \_, f, a => f n

-- zero_ : Nat_
zero_ : (a : Type) -> (Nat_ -> a) -> a -> a
zero_ = \_, f, a => a

-- pred_ : Nat_ -> (Nat_ -> a) -> a -> a
pred_ : ((a : Type) -> (Nat_ -> a) -> a -> a) -> (Nat_ -> a) -> a -> a
pred_ n f a = n _ f a

-- _predSucc : pred_ (succ_ n) f a = f n
-- _predSucc = Refl

-- _predZero : pred_ zero_ f a = a
-- _predZero = Refl
