Section BoehmBerarducci.

(* NOTE: Issues with scoped implicits:
 * 1. "Warning: Ignoring implicit status of product binder A and following binders"
 *)


(* NOTE: Issue 1 *)
Definition NatQ : Type :=
  forall {A : Type}, (A -> A) -> A -> A.

Definition unNatQ {A : Type} : (A -> A) -> A -> NatQ -> A :=
  fun f a q => q _ f a.

Definition succQ : NatQ -> NatQ :=
  fun q => fun _ f a => f (q _ f a).

Definition zeroQ : NatQ :=
  fun _ f a => a.

Definition fromNatQ : NatQ -> nat :=
  fun q => unNatQ S O q.

Definition toNatQ : nat -> NatQ :=
  fix aux t :=
    match t with
      | S n => succQ (aux n)
      | O   => zeroQ
    end.


(* NOTE: Issue 1 *)
Definition ListQ (A : Type) : Type :=
  forall {B : Type}, (A -> B -> B) -> B -> B.

Definition unListQ {A B : Type} : (A -> B -> B) -> B -> ListQ A -> B :=
  fun f b q => q _ f b.

Definition consQ {A : Type} : A -> ListQ A -> ListQ A :=
  fun a q => fun _ f b => f a (q _ f b).

Definition nilQ {A : Type} : ListQ A :=
  fun _ f b => b.

Definition fromListQ {A : Type} : ListQ A -> list A :=
  fun q => unListQ (fun a xs => cons a xs) nil q.

Definition toListQ {A : Type} : list A -> ListQ A :=
  fix aux t :=
    match t with
      | cons a xs => consQ a (aux xs)
      | nil       => nilQ
    end.


End BoehmBerarducci.
