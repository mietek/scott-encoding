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
  fun t =>
    match t with
      true  => trueS
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
  fun t =>
    match t with
      Some a => justS a
    | None   => nothingS
    end.
