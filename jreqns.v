Require Export sflib.
Require Import Omega.
Require Import jrdefs.

Theorem exinf_eq_1 : forall k,
                     forall a b,
                       comp (rk k) (sd_coface (S k)) a b <-> a = b.
Proof.
  intros k a b. split; intro H.
  Case "->".
    destruct H as [x]. unfold sd_coface in H. unfold rk in H. omega.
  Case "<-".
    subst. destruct (le_lt_dec b k); unfold sd_coface; unfold rk.
    SCase "b <= k". exists b. omega.
    SCase "b > k". exists (S b). omega.
Qed.
        
Theorem exinf_eq_2 : forall i k,
                     forall a b,
                       i <= S k ->
                       (comp (jk (S k)) (comp (rk (S k)) (sd_coface i)) a b <->
                        comp (comp (jk (S k)) (comp (rk (S k)) (sd_coface i))) (jk k) a b).
Proof.
  intros i k a b H. split; intro K.
  Case "->". exists a. split. unfold jk. omega. apply K.
  Case "<-". assert (K1 := K). destruct K as [x K]. assert (K2 := K).
  destruct K as [K L]. destruct L as [y L].
    destruct L as [L M]. destruct L as [z L]. destruct L as [L1 L2].
    destruct (lt_eq_lt_dec a (S k)); try destruct s.
    SCase "a <= k". unfold jk in K. assert (N:a = x) by omega. subst. apply K2.
    SCase "a = S k". assert (N:i <= a) by omega.
      exists y. split. exists (S (S k)). split.
      unfold sd_coface. omega.
      unfold jk in K. unfold jk in M. unfold sd_coface in L1.
      unfold rk in L2. unfold rk. omega.
      apply M.
    SCase "a > S k".
      exists a. split. exists (S a). split. unfold sd_coface. omega.
      unfold rk. omega. unfold jk. right. split. apply l.
      unfold jk in K. unfold sd_coface in L1. unfold rk in L2. unfold jk in M.
      clear K1. clear K2. omega.
Qed.

Theorem exinf_eq_3 : forall i k,
                     forall a b,
                       (S (S k)) <= i ->
                       (comp (rk k) (sd_coface (S i)) a b <->
                        comp (sd_coface i) (rk k) a b).
Proof.
  intros i k a b H. split; intro K; destruct K as [x K]; destruct K as [K L].
  Case "->". destruct (lt_eq_lt_dec a (S k)); try destruct s.
    SCase "a < k+1". exists a. split. unfold rk. omega.
      unfold sd_coface. unfold sd_coface in K. unfold rk in L. omega.
    SCase "a = k+1". subst. assert (e1: x = (S k)) by
        (unfold sd_coface in K; omega).
      exists b. unfold rk in L. split. unfold rk. omega.
      unfold sd_coface. omega.
    SCase "a > k+1". destruct a as [| a']. omega.
      exists a'. split. unfold rk. omega.
      unfold sd_coface. unfold sd_coface in K. unfold rk in L. omega.
  Case "<-". destruct (le_lt_dec a i).
    SCase "a <= i". exists a. split. unfold sd_coface. omega.
      unfold rk. unfold sd_coface in L. unfold rk in K. omega.
    SCase "a > i". exists (S a). split.
      unfold sd_coface. omega. unfold rk. unfold rk in K.
      unfold sd_coface in L. omega.
Qed.

Theorem exinf_eq_4 : forall i k,
                     forall a b,
                       comp (jk k) (sd_coface i) a b <->
                       comp (comp (jk k) (sd_coface i)) (jk k) a b.
Proof.
  intros i k a b. split; intro H.
  Case "->". exists a. split. unfold jk. omega. apply H.
  Case "<-". destruct H as [x H]. destruct H as [H K]. destruct K as [y K].
    destruct K as [K L]. destruct (le_lt_dec i a).
    SCase "i <= a". exists (S a). split. unfold sd_coface. omega.
      unfold jk. unfold jk in H. unfold sd_coface in K. unfold jk in L.
      omega.
    SCase "i > a". exists a. split. unfold sd_coface. omega.
      unfold jk. unfold jk in H. unfold sd_coface in K. unfold jk in L.
      omega.
Qed.

Theorem exinf_eq_5 : forall h k,
                      forall a b,
                        h < k ->
                        (comp (jk h) (rk k) a b <->
                         comp (jk h) (sd_codegen k) a b).
Proof.
  intros h k a b J. split; intro H.
  Case "->". destruct H as [x [H K]]. destruct (le_lt_dec a k).
    SCase "a <= k". exists a. split. unfold sd_codegen. omega.
      unfold jk. unfold rk in H. unfold jk in K. omega.
    SCase "a > k". destruct a as [| a']. omega. exists a'.
      split. unfold sd_codegen. omega.
      unfold jk. unfold rk in H. unfold jk in K. omega.
  Case "<-". destruct H as [x [H K]]. destruct (lt_eq_lt_dec a (S k)); try destruct s.
    SCase "a <= k". exists a. split. unfold rk. omega.
      unfold jk. unfold sd_codegen in H. unfold jk in K. omega.
    SCase "a = k+1". exists x. split. unfold rk. unfold sd_codegen in H.
      unfold jk in K. omega.
      apply K.
    SCase "a > k+1". destruct a as [| a']. omega. exists a'. split.
      unfold rk. omega.
      unfold jk. unfold jk in K. unfold sd_codegen in H. omega.
Qed.

Theorem exinf_eq_6 : forall h k,
                     forall a b,
                       h < k ->
                       (comp (comp (jk h) (rk h)) (rk k) a b <->
                        comp (comp (jk h) (rk h)) (sd_codegen k) a b).
Proof.
  intros h k a b J. split; intro H; assert (I:=H);
                    destruct H as [x [H [y [K L]]]].
  Case "->". destruct (le_lt_dec a k).
    SCase "a <= k". exists a. split. unfold sd_codegen. omega.
      assert (e: a = x) by (unfold rk in H; omega). subst.
      exists y. split. apply K. apply L.
    SCase "a > k". destruct a as [| a']. omega. exists a'. split.
      unfold sd_codegen. omega.
      destruct (lt_eq_lt_dec a' (S h)). destruct s.
      SSCase "a' <= h". omega.
      SSCase "a' = h+1". exists y. split. unfold rk. unfold jk in L.
        unfold rk in K. unfold rk in H. omega.
        apply L.
      SSCase "a' > h+1". destruct a' as [| a'']. omega. exists a''.
        split. unfold rk. omega.
        unfold jk. unfold jk in L. unfold rk in K. unfold rk in H. omega.
  Case "<-". destruct (lt_eq_lt_dec a (S k)). destruct s.
    SCase "a <= k". exists a. split. unfold rk. omega.
      assert (e: a = x) by (unfold sd_codegen in H; omega). subst.
      exists y. split. apply K. apply L.
    SCase "a = k+1". exists x. split. unfold rk. unfold sd_codegen in H. omega.
      exists y. split. apply K. apply L.
    SCase "a > k+1". destruct a as [| a']. omega. exists a'. split.
      unfold rk. omega. destruct (lt_eq_lt_dec a' (S h)). destruct s.
      SSCase "a' <= h". exists a'. split. unfold rk. omega.
        unfold jk. unfold sd_codegen in H. unfold rk in K. unfold jk in L. omega.
      SSCase "a' = h+1". exists y. split. unfold rk. unfold sd_codegen in H.
        unfold rk in K. unfold jk in L. omega.
        apply L.
      SSCase "a' > h+1". destruct a' as [| a'']. omega. exists a''. split.
        unfold rk. omega.
        unfold jk. unfold sd_codegen in H. unfold rk in K. unfold jk in L. omega.
Qed.

Theorem exinf_eq_7 : forall k,
                     forall a b,
                       comp (comp (jk k) (rk k)) (rk k) a b <->
                       comp (comp (jk k) (rk k)) (sd_codegen (S k)) a b.
Proof.
  intros k a b. split; intro H; assert (I:=H); destruct H as [x [H L]];
                assert (J:=L); destruct L as [y [L K]].
  Case "->". destruct (lt_eq_lt_dec a (S k)). destruct s.
    SCase "a <= k". exists a. split. unfold sd_codegen. left. omega.
      exists a. split. unfold rk. omega.
      unfold jk. unfold rk in H. unfold rk in L. unfold jk in K. left. omega.
    SCase "a = k+1". exists a. split. unfold sd_codegen. omega.
      exists y. split. unfold rk. unfold rk in H. unfold rk in L. omega.
      unfold jk. unfold rk in H. unfold rk in L. unfold jk in K. omega.
    SCase "a > k+1". destruct a as [| a']. omega.
      exists a'. split. unfold sd_codegen. omega.
      destruct (le_lt_dec a' (S k)).
      SSCase "a = k+2". exists y. split. unfold rk. unfold rk in H.
        unfold rk in L. unfold jk in K. omega.
        apply K.
      SSCase "a > k+2". destruct a' as [| a'']. omega. exists a''. split.
        unfold rk. omega. unfold jk. unfold rk in H. unfold rk in L. unfold jk in K.
        omega.
  Case "<-". destruct (lt_eq_lt_dec a (S k)). destruct s.
    SCase "a <= k". exists a. split. unfold rk. omega.
      exists a. split. unfold rk. omega.
      unfold jk. unfold sd_codegen in H. unfold rk in L. unfold jk in K. omega.
    SCase "a = k+1". exists y.
      split. unfold rk. unfold sd_codegen in H. unfold rk in L. omega.
      exists y. split. unfold rk. unfold sd_codegen in H. unfold rk in L. omega.
      apply K.
    SCase "a > k+1". destruct a as [| a']. omega. exists a'. split.
      unfold rk. omega. destruct (le_lt_dec a' (S k)).
      SSCase "a = k+2". exists y.  split. unfold rk. unfold sd_codegen in H.
        unfold rk in L. unfold jk in K. omega. apply K.
      SSCase "a > k+2". destruct a' as [| a'']. omega. exists a''. split.
        unfold rk. omega.
        unfold jk. unfold sd_codegen in H. unfold rk in L. unfold jk in K. omega.
Qed.

Theorem exinf_eq_8 : forall h k,
                     forall a b,
                       h <= k ->
                       (comp (rk k) (jk h) a b <->
                        comp (jk h) (rk k) a b).
Proof.
  intros h k a b J. split; intro H; assert (I:=H); destruct H as [x [H K]].
  Case "->". destruct (lt_eq_lt_dec a (S k)). destruct s.
    SCase "a <= k". exists a. split. unfold rk. omega. unfold jk.
      unfold jk in H. unfold rk in K. omega.
    SCase "a = k+1". exists b. split. unfold rk. unfold jk in H. unfold rk in K. omega.
      unfold jk. omega.
    SCase "a > k+1". destruct a as [| a']. omega. exists a'. split.
      unfold rk. omega. unfold jk. unfold jk in H. unfold rk in K. omega.
  Case "<-". destruct (le_lt_dec a h).
    SCase "a <= h". exists a. split. unfold jk. omega. unfold rk.
      unfold rk in H. unfold jk in K. omega.
    SCase "a > h". destruct (lt_eq_lt_dec a (S k)). destruct s.
      SSCase "h < a <= k". exists b. split. unfold rk in H. unfold jk in K.
        unfold jk. omega.
        unfold rk. unfold rk in H. unfold jk in K. omega.
      SSCase "h < a = k+1". subst. assert(e:x<=k) by (unfold rk in H; omega).
        subst. assert(e1:b<=x) by (unfold jk in K; omega). exists b.
        split. unfold jk. unfold jk in K. unfold rk in H. omega.
        unfold rk. omega.
      SSCase "k+1 < a". assert (e:S x = a) by (unfold rk in H; omega). subst.
        destruct (le_lt_dec b k).
        SSSCase "b <= k". exists b. split. unfold jk. omega.
          unfold rk. omega.
        SSSCase "b > k". exists (S b). split. unfold jk. unfold jk in K.
          unfold rk in H. omega.
          unfold rk. omega.
Qed.
      
Theorem exinf_eq_9 : forall h k,
                     forall a b,
                       h <= k ->
                       (comp (comp(sd_codegen h) (jk (S k))) (rk (S k)) a b <->
                        comp (comp (jk k) (rk k)) (sd_codegen h) a b).
Proof.
  intros h k a b J. split; intro H; assert (I:=H); destruct H as [x [H K]];
                    assert (I1:=K); destruct K as [y [K L]];
                    assert (H1:=H); assert (K1:=K); assert (L1:=L).
  Case "->". unfold rk in H1. unfold jk in K1. unfold sd_codegen in L1. destruct (le_lt_dec a h).
    SCase "a <= h". exists a. split. unfold sd_codegen. omega.
      exists a. split. unfold rk. omega. unfold jk. omega.
    SCase "a > h". destruct a as [| a']. omega. exists a'. split.
      unfold sd_codegen. omega. destruct (lt_eq_lt_dec a' (S k)). destruct s.
      SSCase "h < a < k+2". exists a'. split. unfold rk. omega. unfold jk. omega.
      SSCase "h < a = k+2". exists b. split. unfold rk. omega. unfold jk. omega.
      SSCase "k+2 < a". destruct a' as [| a'']. omega. exists a''. split.
        unfold rk. omega. unfold jk. omega.
  Case "<-". unfold sd_codegen in H1. unfold rk in K1. unfold jk in L1.
    destruct (lt_eq_lt_dec a (S (S k))). destruct s.
    SCase "a < k+2". exists a. split. unfold rk. omega.
      exists a. split. unfold jk. omega. unfold sd_codegen. omega.
    SCase "a = k+2". destruct (le_lt_dec b h).
      SSCase "b <= h". exists b. split. unfold rk. omega.
        exists b. split. unfold jk. omega. unfold sd_codegen. omega.
      SSCase "b > h". exists (S b). split. unfold rk. omega.
        exists (S b). split. unfold jk. omega. unfold sd_codegen. omega.
    SCase "a > k+2". destruct a as [| a']. omega. exists a'.
      split. unfold rk. omega. destruct (le_lt_dec b h).
      SSCase "b <= h". exists b. split. unfold jk. omega. unfold sd_codegen. omega.
      SSCase "b > h". exists (S b). split. unfold jk. omega. unfold sd_codegen. omega.
Qed.

Theorem exinf_eq_10 : forall h k,
                      forall a b,
                        k <= h ->
                        (comp (comp (sd_codegen h) (jk k)) (rk k) a b <->
                         comp (comp (jk k) (rk k)) (sd_codegen (S h)) a b).
Proof.
  intros h k a b J. split; intro H; assert (I:=H); destruct H as [x [H K]];
                    assert (I1:=K); destruct K as [y [K L]];
                    assert (H1:=H); assert (K1:=K); assert (L1:=L).
  Case "->". unfold rk in H1. unfold jk in K1. unfold sd_codegen in L1.
    destruct (le_lt_dec a (S h)).
    SCase "a <= h+1". exists a. split. unfold sd_codegen. omega.
      destruct (lt_eq_lt_dec a (S k)). destruct s.
      SSCase "a <= k <= h". exists a. split. unfold rk. omega. unfold jk. omega.
      SSCase "a = k+1 <= h+1". exists b. split. unfold rk. omega. unfold jk. omega.
      SSCase "k+1 < a <= h+1". destruct a as [| a']. omega. exists a'. split.
        unfold rk. omega. unfold jk. omega.
    SCase "a > h+1". destruct a as [| a']. omega. exists a'. split.
      unfold sd_codegen. omega. destruct (lt_eq_lt_dec a' (S k)). destruct s. omega. 
      SSCase "h=k=a-2". exists b. split. unfold rk. omega. unfold jk. omega.
      SSCase "a > k+2, h+1". destruct a' as [| a'']. omega. exists a''.
        split. unfold rk. omega. unfold jk. omega.
  Case "<-". unfold sd_codegen in H1. unfold rk in K1. unfold jk in L1.
    destruct (lt_eq_lt_dec a (S k)). destruct s.
    SCase "a <= k". exists a. split. unfold rk. omega.
      exists a. split. unfold jk. omega. unfold sd_codegen. omega.
    SCase "a=k+1". destruct (le_lt_dec b h).
      SSCase "b <= h". exists b. split. unfold rk. omega.
        exists b. split. unfold jk. omega. unfold sd_codegen. omega.
      SSCase "b > h". exists (S b). split. unfold rk. omega.
        exists (S b). split. unfold jk. omega. unfold sd_codegen. omega.
    SCase "a > k+1". destruct a as [| a']. omega. exists a'.
      split. unfold rk. omega. destruct (le_lt_dec b h).
      SSCase "b <=h". exists b. split. unfold jk. omega. unfold sd_codegen. omega.
      SSCase "b > h". exists (S b). split. unfold jk. omega. unfold sd_codegen. omega.
Qed.
