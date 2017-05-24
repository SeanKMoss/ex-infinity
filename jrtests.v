Require Import Omega.
Require Import sflib.
Require Import jrdefs.

(* Coface maps *)
Example ex_coface_1 : (sd_coface 1 1 2).
Proof. unfold sd_coface. omega. Qed.

Example ex_coface_2 : (sd_coface 4 3 3). 
Proof. unfold sd_coface. omega. Qed.

Example ex_coface_3 : ~ (sd_coface 3 2 1).
Proof. unfold sd_coface. omega. Qed.

(* Codegeneracy maps *)
Example ex_codegen_1 : (sd_codegen 1 0 0).
Proof. unfold sd_codegen. omega. Qed.

Example ex_codegen_2 : (sd_codegen 4 6 5).
Proof. unfold sd_codegen. omega. Qed.

Example ex_codegen_3 : (sd_codegen 100 100 100).
Proof. unfold sd_codegen. omega. Qed.

Example ex_codegen_4 : ~(sd_codegen 40 40 41).
Proof. unfold sd_codegen. omega. Qed.

(* jk maps *)
Example ex_jk_1 : forall i j k, (i <= k) ->
                            jk k i j ->
                            i = j.
Proof.
  intros i j k H K. unfold jk in K. omega.
Qed.

Example ex_jk_2 : jk 10 10 10.
Proof. unfold jk. omega. Qed.

Example ex_jk_3 : jk 33 34 33.
Proof. unfold jk. omega. Qed.

Example ex_jk_4 : ~ (jk 14 3 16).
Proof. intro H. unfold jk in H. omega. Qed.

(* rk maps *)
Example ex_rk_1 : rk 5 6 2.
Proof. unfold rk. omega. Qed.

Example ex_rk_2 : rk 7 7 7.
Proof. unfold rk. omega. Qed.

Example ex_rk_3 : ~ (rk 19 3 4).
Proof. intro H. unfold rk in H. omega. Qed.

Example ex_rk_4 : forall i j j' k,
                    j <> j' ->
                    rk k i j ->
                    rk k i j' ->
                    i = (S k).
Proof.
  intros. unfold rk in H0; unfold rk in H1. omega.
Qed.

(* Composition *)
Example ex_comp_1 : comp (sd_codegen 3) (sd_coface 3) 3 3.
Proof. exists 4. unfold sd_coface. unfold sd_codegen. omega.
Qed.

Example ex_comp_2 : ~ comp (sd_codegen 5) (sd_coface 5) 1 2.
Proof. unfold comp. intro H. destruct H. 
       unfold sd_coface in H. unfold sd_codegen in H. omega.
Qed.

Example comp_assoc : forall (f g h:nat->nat->Prop),
                     forall a b,
                       comp f (comp g h) a b <-> comp (comp f g) h a b.
Proof.
  intros. split.
  Case "->". intro H. destruct H as [x]. destruct H as [H L].
    destruct H as [y]. destruct H as [H K].
    exists y. split. apply H. exists x. split. apply K. apply L.
  Case "<-". intro H. destruct H as [x]. destruct H as [H K].
    destruct K as [y]. destruct H0 as [K L]. exists y.
    split. exists x. split. apply H. apply K. apply L.
Qed.
