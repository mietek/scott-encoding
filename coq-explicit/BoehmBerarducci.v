Section BoehmBerarducci.


Definition NatQ : Type :=
  forall A : Type, (A -> A) -> A -> A.

Definition unNatQ {A : Type} : (A -> A) -> A -> NatQ -> A :=
  fun f a s => s _ f a.

Definition succQ : NatQ -> NatQ :=
  fun s => fun _ f a => f (s _ f a).

Definition zeroQ : NatQ :=
  fun _ f a => a.

Definition fromNatQ : NatQ -> nat :=
  fun s => unNatQ S O s.

Definition toNatQ : nat -> NatQ :=
  fix aux t :=
    match t with
      | S n => succQ (aux n)
      | O   => zeroQ
    end.


Definition ListQ (A : Type) : Type :=
  forall B : Type, (A -> B -> B) -> B -> B.

Definition unListQ {A B : Type} : (A -> B -> B) -> B -> ListQ A -> B :=
  fun f b s => s _ f b.

Definition consQ {A : Type} : A -> ListQ A -> ListQ A :=
  fun a s => fun _ f b => f a (s _ f b).

Definition nilQ {A : Type} : ListQ A :=
  fun _ f b => b.

Definition fromListQ {A : Type} : ListQ A -> list A :=
  fun s => unListQ (fun a xs => cons a xs) nil s.

Definition toListQ {A : Type} : list A -> ListQ A :=
  fix aux t :=
    match t with
      | cons a xs => consQ a (aux xs)
      | nil       => nilQ
    end.


End BoehmBerarducci.
