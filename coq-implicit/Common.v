Section Common.

(* NOTE: Issues with scoped implicits:
 * 1. "Warning: Ignoring implicit status of product binder A and following binders"
 *)


(* NOTE: Issue 1 *)
Definition BoolQ : Type :=
  forall {A : Type}, A -> A -> A.

Definition unBoolQ {A : Type} : A -> A -> BoolQ -> A :=
  fun a a' q => q _ a a'.

Definition trueQ : BoolQ :=
  fun _ a a' => a.

Definition falseQ : BoolQ :=
  fun _ a a' => a'.

Definition fromBoolQ : BoolQ -> bool :=
  fun q => unBoolQ true false q.

Definition toBoolQ : bool -> BoolQ :=
  fun t => match t with
    | true  => trueQ
    | false => falseQ
  end.


(* NOTE: Issue 1 *)
Definition MaybeQ (A : Type) : Type :=
  forall {B : Type}, (A -> B) -> B -> B.

Definition unMaybeQ {A B : Type} : (A -> B) -> B -> MaybeQ A -> B :=
  fun f b q => q _ f b.

Definition justQ {A : Type} : A -> MaybeQ A :=
  fun a => fun _ f b => f a.

Definition nothingQ {A : Type} : MaybeQ A :=
  fun _ f b => b.

Definition fromMaybeQ {A : Type} : MaybeQ A -> option A :=
  fun q => unMaybeQ (fun a => Some a) None q.

Definition toMaybeQ {A : Type} : option A -> MaybeQ A :=
  fun t => match t with
    | Some a => justQ a
    | None   => nothingQ
  end.


(* NOTE: Issue 1 *)
Definition EitherQ (A B : Type) : Type :=
  forall {C : Type}, (A -> C) -> (B -> C) -> C.

Definition unEitherQ {A B C : Type} : (A -> C) -> (B -> C) -> EitherQ A B -> C :=
  fun f g q => q _ f g.

Definition leftQ {A B : Type} : A -> EitherQ A B :=
  fun a => fun _ f g => f a.

Definition rightQ {A B : Type} : B -> EitherQ A B :=
  fun b => fun _ f g => g b.

Definition fromEitherQ {A B : Type} : EitherQ A B -> A + B :=
  fun q => unEitherQ inl inr q.

Definition toEitherQ {A B : Type} : A + B -> EitherQ A B :=
  fun t => match t with
    | inl a => leftQ a
    | inr b => rightQ b
  end.


(* NOTE: Issue 1 *)
Definition PairQ (A B : Type) : Type :=
  forall {C : Type}, (A -> B -> C) -> C.

Definition unPairQ {A B C : Type} : (A -> B -> C) -> PairQ A B -> C :=
  fun f q => q _ f.

Definition pairQ {A B : Type} : A -> B -> PairQ A B :=
  fun a b => fun _ f => f a b.

Definition fromPairQ {A B : Type} : PairQ A B -> A * B :=
  fun q => unPairQ (fun a b => (a, b)) q.

Definition toPairQ {A B : Type} : A * B -> PairQ A B :=
  fun t => match t with
    | (a, b) => pairQ a b
  end.

Definition fstQ {A B : Type} : PairQ A B -> A :=
  fun q => unPairQ (fun a b => a) q.

Definition sndQ {A B : Type} : PairQ A B -> B :=
  fun q => unPairQ (fun a b => b) q.


End Common.
