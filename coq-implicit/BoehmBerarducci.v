Section BoehmBerarducci.

(* NOTE: Issues with scoped implicits:
 * 1. "Warning: Ignoring implicit status of product binder A and following binders"
 *)


(* NOTE: Issue 1 *)
Definition NatS : Type :=
  forall {A : Type}, (A -> A) -> A -> A.

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


(* NOTE: Issue 1 *)
Definition ListS (A : Type) : Type :=
  forall {B : Type}, (A -> B -> B) -> B -> B.

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
