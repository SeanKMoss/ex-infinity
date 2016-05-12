Definition jk (k:nat) (a b:nat) : Prop :=
  (a <= k /\ a = b)
  \/
  (k < a /\ b <= a).

Definition rk (k:nat) (a b:nat) : Prop :=
  (a <= k /\ a = b)
  \/
  (a = (S k) /\ S b <= a)
  \/
  (S k < a /\ S b = a).

Definition sd_coface (k:nat) (a b:nat) : Prop :=
  (a < k /\ a = b)
  \/
  (k <= a /\ S a = b).

Definition sd_codegen (k:nat) (a b:nat) : Prop :=
  (a <= k /\ a = b)
  \/
  (k < a /\ a = (S b)).

Definition comp (g f:nat->nat->Prop) (a b:nat) : Prop :=
  exists (x:nat), (f a x) /\ (g x b).
