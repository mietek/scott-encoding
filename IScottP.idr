module IScottP

import IScott

%default total


iteratedP : (n : Nat) -> iterated n S Z = n
iteratedP (S n) = rewrite iteratedP n in Refl
iteratedP Z     = Refl


unboolTrueSP : unboolS a a' trueS = a
unboolTrueSP = Refl

unboolFalseSP : unboolS a a' falseS = a'
unboolFalseSP = Refl

fromTrueSP : fromBoolS trueS = True
fromTrueSP = Refl

fromFalseSP : fromBoolS falseS = False
fromFalseSP = Refl

toTrueSP : toBoolS True = trueS
toTrueSP = Refl

toFalseSP : toBoolS False = falseS
toFalseSP = Refl


unmaybeJustSP : unmaybeS f b (justS a) = f a
unmaybeJustSP = Refl

unmaybeNothingSP : unmaybeS f b nothingS = b
unmaybeNothingSP = Refl

fromJustSP : fromMaybeS (justS a) = Just a
fromJustSP = Refl

fromNothingSP : fromMaybeS nothingS = Nothing
fromNothingSP = Refl

toJustSP : toMaybeS (Just a) = justS a
toJustSP = Refl

toNothingSP : toMaybeS Nothing = nothingS
toNothingSP = Refl


uneitherLeftSP : uneitherS f g (leftS a) = f a
uneitherLeftSP = Refl

uneitherRightSP : uneitherS f g (rightS b) = g b
uneitherRightSP = Refl

fromLeftSP : fromEitherS (leftS a) = Left a
fromLeftSP = Refl

fromRightSP : fromEitherS (rightS b) = Right b
fromRightSP = Refl

toLeftSP : toEitherS (Left a) = leftS a
toLeftSP = Refl

toRightSP : toEitherS (Right b) = rightS b
toRightSP = Refl


unpairPairSP : unpairS (\a, b => (a, b)) (pairS a b) = (a, b)
unpairPairSP = Refl

fromPairSP : fromPairS (pairS a b) = (a, b)
fromPairSP = Refl

toPairSP : toPairS (a, b) = pairS a b
toPairSP = Refl

fstPairSP : fstS (pairS a b) = a
fstPairSP = Refl

sndPairSP : sndS (pairS a b) = b
sndPairSP = Refl


fromNatSP : (n : Nat) -> fromNatS (iterated n succS zeroS) = n
fromNatSP (S n) = rewrite fromNatSP n in Refl
fromNatSP Z     = Refl

toNatSP : (n : Nat) -> toNatS n = iterated n succS zeroS
toNatSP (S n) = rewrite toNatSP n in Refl
toNatSP Z = Refl


-- TODO: Use a list of [0 .. n]

fromListSP : (n : Nat) -> fromListS (iterated n (consS ()) nilS) = iterated n (() ::) []
fromListSP (S n) = rewrite fromListSP n in Refl
fromListSP Z     = Refl

toListSP : (n : Nat) -> toListS (iterated n (() ::) []) = iterated n (consS ()) nilS
toListSP (S n) = rewrite toListSP n in Refl
toListSP Z     = Refl
