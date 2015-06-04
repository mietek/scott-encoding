Section CScott.


Definition BoolS : Type :=
  forall A : Type, A -> A -> A.

Definition unBoolS {A : Type} : A -> A -> BoolS -> A :=
  fun a a' s => s _ a a'.

Definition trueS : BoolS :=
  fun _ a a' => a.

Definition falseS : BoolS :=
  fun _ a a' => a'.

Definition fromBoolS : BoolS -> bool :=
  fun s => unBoolS true false s.

Definition toBoolS : bool -> BoolS :=
  fun t => match t with
    | true  => trueS
    | false => falseS
  end.


Definition MaybeS (A : Type) : Type :=
  forall B : Type, (A -> B) -> B -> B.

Definition unMaybeS {A B : Type} : (A -> B) -> B -> MaybeS A -> B :=
  fun f b s => s _ f b.

Definition justS {A : Type} : A -> MaybeS A :=
  fun a => fun _ f b => f a.

Definition nothingS {A : Type} : MaybeS A :=
  fun _ f b => b.

Definition fromMaybeS {A : Type} : MaybeS A -> option A :=
  fun s => unMaybeS (fun a => Some a) None s.

Definition toMaybeS {A : Type} : option A -> MaybeS A :=
  fun t => match t with
    | Some a => justS a
    | None   => nothingS
  end.


Definition EitherS (A B : Type) : Type :=
  forall C : Type, (A -> C) -> (B -> C) -> C.

Definition unEitherS {A B C : Type} : (A -> C) -> (B -> C) -> EitherS A B -> C :=
  fun f g s => s _ f g.

Definition leftS {A B : Type} : A -> EitherS A B :=
  fun a => fun _ f g => f a.

Definition rightS {A B : Type} : B -> EitherS A B :=
  fun b => fun _ f g => g b.

Definition fromEitherS {A B : Type} : EitherS A B -> A + B :=
  fun s => unEitherS inl inr s.

Definition toEitherS {A B : Type} : A + B -> EitherS A B :=
  fun t => match t with
    | inl a => leftS a
    | inr b => rightS b
  end.


Definition PairS (A B : Type) : Type :=
  forall C : Type, (A -> B -> C) -> C.

Definition unPairS {A B C : Type} : (A -> B -> C) -> PairS A B -> C :=
  fun f s => s _ f.

Definition pairS {A B : Type} : A -> B -> PairS A B :=
  fun a b => fun _ f => f a b.

Definition fromPairS {A B : Type} : PairS A B -> A * B :=
  fun s => unPairS (fun a b => (a, b)) s.

Definition toPairS {A B : Type} : A * B -> PairS A B :=
  fun t => match t with
    | (a, b) => pairS a b
  end.

Definition fstS {A B : Type} : PairS A B -> A :=
  fun s => unPairS (fun a b => a) s.

Definition sndS {A B : Type} : PairS A B -> B :=
  fun s => unPairS (fun a b => b) s.


Definition NatS : Type :=
  forall A : Type, (A -> A) -> A -> A.

Definition unNatS {A : Type} : (A -> A) -> A -> NatS -> A :=
  fun f a s => s _ f a.

Definition succS : NatS -> NatS :=
  fun s => fun _ f a => f (s _ f a).

Definition zeroS : NatS :=
  fun _ f a => a.

Definition fromNatS : NatS -> nat :=
  fun s => unNatS S O s.

Definition toNatS : nat -> NatS :=
  fix aux t :=
    match t with
      | S n => succS (aux n)
      | O   => zeroS
    end.


Definition ListS (A : Type) : Type :=
  forall B : Type, (A -> B -> B) -> B -> B.

Definition unListS {A B : Type} : (A -> B -> B) -> B -> ListS A -> B :=
  fun f b s => s _ f b.

Definition consS {A : Type} : A -> ListS A -> ListS A :=
  fun a s => fun _ f b => f a (s _ f b).

Definition nilS {A : Type} : ListS A :=
  fun _ f b => b.

Definition fromListS {A : Type} : ListS A -> list A :=
  fun s => unListS (fun a xs => cons a xs) nil s.

Definition toListS {A : Type} : list A -> ListS A :=
  fix aux t :=
    match t with
      | cons a xs => consS a (aux xs)
      | nil       => nilS
    end.
