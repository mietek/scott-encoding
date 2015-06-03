Section CScott.


Definition BoolS : Type
  := forall A : Set, A -> A -> A.

Definition unBoolS : forall A : Set, A -> A -> BoolS -> A
  := fun a a' s => s a a'.
