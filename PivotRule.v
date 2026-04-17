Require Export HeisenbergFoundations.Normalization.

Lemma switch_overflow {X : Type} (ls : list X) (x : X) (n : nat):
  (n >= length ls)%nat -> switch ls x n = ls.
Proof. intros H.
  gen x n. induction ls; intros; simpl; auto.
  destruct n; simpl in H; try lia.
  f_equal.
  apply IHls; lia.
Qed.

Lemma length_zipWith {X Y Z} (f : X -> Y -> Z) As Bs :
  length (zipWith f As Bs) = Nat.min (length As) (length Bs).
Proof. unfold zipWith.
  unfold uncurry.
  rewrite map_length.
  rewrite combine_length.
  auto.
Qed.

Lemma nth_zipWith
  {X Y Z} (f : X -> Y -> Z)
  (As : list X) (Bs : list Y)
  (dx : X) (dy : Y) (dz : Z) (t : nat) :
  (t < Nat.min (length As) (length Bs))%nat ->
  nth t (zipWith f As Bs) dz = f (nth t As dx) (nth t Bs dy).
Proof. intros H.
  unfold zipWith.
  unfold uncurry.
  rewrite nth_indep with (d' := (fun p : X * Y=> let (x, y) := p in f x y) (dx, dy)).
  2: { rewrite map_length. rewrite combine_length. auto. }
  rewrite map_nth with (d := (dx, dy)).
  gen t Bs dx dy. induction As; intros.
  - simpl in *. lia.
  - simpl.
    destruct Bs.
    + simpl in *. lia.
    + simpl in *.
      destruct t; auto.
      assert (t < (Nat.min (length As) (length Bs)))%nat by lia.
      specialize (IHAs t Bs H0 dx dy).
      auto.
Qed.

Definition WF_T {n} (t : TType n) : Prop := length (snd t) = n.
Definition WF_L {n} (L : list (TType n)) : Prop := Forall (@WF_T n) L.

Lemma WF_defaultT_I n : WF_T (defaultT_I n).
Proof. unfold WF_T, defaultT_I. simpl. rewrite repeat_length. auto. Qed.

Lemma WF_gMulT {n} (A B : TType n) :
  WF_T A -> WF_T B -> WF_T (gMulT A B).
Proof. intros H H0.
  unfold WF_T, gMulT in *.
  simpl.
  destruct A, B.
  simpl in *.
  rewrite length_zipWith.
  rewrite H, H0.
  lia.
Qed.

Lemma WF_switch {n} (L : list (TType n)) x t :
  WF_L L -> WF_T x -> WF_L (switch L x t).
Proof. intros H H0.
  unfold WF_L, WF_T in *.
  bdestruct (t <? length L)%nat.
  2: { rewrite switch_overflow; auto. }
  rewrite switch_inc; auto.
  rewrite ! Forall_app.
  rewrite nth_inc with (n := t) (x := defaultT_I n) in H; auto.
  rewrite ! Forall_app in H.
  destruct H as [H [H' H'']].
  repeat split; auto.
Qed.

Definition entry {n} (q : nat) (t : TType n) : Pauli :=
  nth q (snd t) gI.

Definition isXY (g : Pauli) : bool :=
  match g with gX | gY => true | _ => false end.

Definition isIZ (g : Pauli) : bool :=
  match g with gI | gZ => true | _ => false end.

Lemma entry_gMulT {n} (A B : TType n) (q : nat) :
  WF_T A -> WF_T B ->
  (q < n)%nat ->
  entry q (gMulT A B) = gMul_base (entry q A) (entry q B).
Proof. intros H H0 H1.
  unfold WF_T in *.
  unfold entry.
  destruct A, B.
  simpl in *.
  setoid_rewrite nth_zipWith; auto.
  rewrite H, H0.
  lia.
Qed.
  
Lemma gMul_base_XY_elim a b :
  isXY a = true -> isXY b = true -> isXY (gMul_base a b) = false.
Proof. intros H H0.
  destruct a, b; simpl in *; auto; discriminate. Qed.

Lemma gMul_base_XY_to_IZ a b :
  isXY a = true -> isXY b = true -> isIZ (gMul_base a b) = true.
Proof. intros H H0.
  destruct a, b; simpl in *; auto; discriminate. Qed.

Lemma gMul_base_ZZ_to_I :
  gMul_base gZ gZ = gI.
Proof. auto. Qed.


Lemma loop_replaceT_XY_preserve_prefix {n}
  (q pr k : nat) :
  forall (L : list (TType n)) r,
    (r < length L - k)%nat ->
    nth r (loop_replaceT_XY n q pr k L) (defaultT_I n)
    =
    nth r L (defaultT_I n).
Proof.
  induction k as [|k IH]; intros L r Hr.
  - cbn in Hr.
    cbn [loop_replaceT_XY]. reflexivity.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    assert (Hr_lt_t : (r < t)%nat) by (subst t; exact Hr).

    destruct (Nat.eqb t pr) eqn:Htpr.
    + apply IH.
      subst t. lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g;
      try (apply IH; subst t; lia).

      * set (L1 :=
          switch L
            (gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)))
            t).

        assert (Hr1 : (r < length L1 - k)%nat).
        { unfold L1. rewrite switch_len. subst t. lia. }

        specialize (IH L1 r Hr1).
        rewrite IH. unfold L1.
        rewrite nth_switch_miss; auto; try lia.
        
      * set (L1 :=
          switch L
            (gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)))
            t).
        assert (Hr1 : (r < length L1 - k)%nat).
        { unfold L1. rewrite switch_len. subst t. lia. }
        specialize (IH L1 r Hr1).
        rewrite IH. unfold L1.
        rewrite nth_switch_miss; auto; try lia.
Qed.

Lemma loop_replaceT_XY_suffix_IZ_gen {n}
  (q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (pr < length L)%nat ->
    (q < n)%nat ->
    (k <= length L)%nat ->
    isXY (entry q (nth pr L (defaultT_I n))) = true ->
    forall r,
      (length L - k <= r < length L)%nat ->
      r <> pr ->
      isIZ (entry q (nth r (loop_replaceT_XY n q pr k L) (defaultT_I n))) = true.
Proof.
  induction k as [|k IH]; intros L HWF Hpr Hq Hk Hpiv r Hr Hneq.
  - cbn in Hr. lia.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    assert (Hr_cases : r = t \/ (r > t)%nat) by (subst t; lia).

    destruct (Nat.eqb t pr) eqn:Htpr.
    + apply Nat.eqb_eq in Htpr. subst t.
      apply (IH L); try assumption.
      * lia.
      * split; [lia | exact (proj2 Hr)].
      
    + apply Nat.eqb_neq in Htpr.

      remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * destruct Hr_cases as [Hrt | Hgt].
        -- subst r.
           
           assert (Ht_lt_start : (t < length L - k)%nat).
           { subst t. lia. }

           assert (Hnth :
             nth t (loop_replaceT_XY n q pr k L) (defaultT_I n)
             =
             nth t L (defaultT_I n)).
           { apply (loop_replaceT_XY_preserve_prefix q pr k); try assumption. }

           unfold entry, isIZ.
           rewrite Hnth.
           cbn.
           rewrite <- Hg.
           reflexivity.

        -- apply (IH L); try assumption.
           ++ lia.
           ++ split; [subst t; lia | exact (proj2 Hr)].

      * destruct Hr_cases.
        -- rewrite loop_replaceT_XY_preserve_prefix.
           2: rewrite switch_len; lia.
           subst r. rewrite nth_switch_hit; auto; try lia.
           rewrite entry_gMulT; auto.
           2-3: apply Forall_nth; auto; lia.
           rewrite gMul_base_XY_to_IZ; auto.
           unfold entry.
           rewrite <- Hg.
           simpl. auto.
        -- rewrite IH; try rewrite switch_len; auto; try lia.
           rewrite switch_inc; try lia.
           unfold WF_L in *.
           repeat rewrite Forall_app.
           remember HWF as HWF'''. clear HeqHWF'''.
           rewrite nth_inc with (ls := L) (n := t) (x := (defaultT_I n)) in HWF; try lia.
           repeat rewrite Forall_app in HWF.
           destruct HWF as [HWF [HWF' HWF'']].
           repeat split; auto.
           constructor; auto.
           apply WF_gMulT;
             apply Forall_nth;
             auto; lia.
           rewrite nth_switch_miss; auto; try lia.
      * destruct Hr_cases.
        -- rewrite loop_replaceT_XY_preserve_prefix.
           2: rewrite switch_len; lia.
           subst r. rewrite nth_switch_hit; auto; try lia.
           rewrite entry_gMulT; auto.
           2-3: apply Forall_nth; auto; lia.
           rewrite gMul_base_XY_to_IZ; auto.
           unfold entry.
           rewrite <- Hg.
           simpl. auto.
        -- rewrite IH; try rewrite switch_len; auto; try lia.
           rewrite switch_inc; try lia.
           unfold WF_L in *.
           repeat rewrite Forall_app.
           remember HWF as HWF'''. clear HeqHWF'''.
           rewrite nth_inc with (ls := L) (n := t) (x := (defaultT_I n)) in HWF; try lia.
           repeat rewrite Forall_app in HWF.
           destruct HWF as [HWF [HWF' HWF'']].
           repeat split; auto.
           constructor; auto.
           apply WF_gMulT;
             apply Forall_nth;
             auto; lia.
           rewrite nth_switch_miss; auto; try lia.
      * destruct Hr_cases.
        -- subst r. 
           rewrite loop_replaceT_XY_preserve_prefix; try lia.
           unfold isIZ, entry.
           rewrite <- Hg.
           auto.
        -- rewrite IH; auto; try lia.
Qed.

Lemma loop_replaceT_XY_clears_all_to_IZ {n}
  (L : list (TType n)) (q pr : nat) :
  WF_L L ->
  (pr < length L)%nat ->
  (q < n)%nat
 ->
  isXY (entry q (nth pr L (defaultT_I n))) = true ->
  forall r,
    (r < length L)%nat ->
    r <> pr ->
    isIZ (entry q (nth r (loop_replaceT_XY n q pr (length L) L) (defaultT_I n))) = true.
Proof.
  intros HWF Hpr Hq Hpiv r Hr Hneq.
  eapply (loop_replaceT_XY_suffix_IZ_gen q pr (length L)); eauto.
  lia.
Qed.

Lemma loop_replaceT_Z_preserve_prefix {n}
  (q pr k : nat) :
  forall (L : list (TType n)) r,
    (r < length L - k)%nat ->
    nth r (loop_replaceT_Z n q pr k L) (defaultT_I n)
    =
    nth r L (defaultT_I n).
Proof.
  induction k as [|k IH]; intros L r Hr.
  - cbn in Hr.
    cbn [loop_replaceT_Z]. reflexivity.
  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).
    assert (Hr_lt_t : (r < t)%nat) by (subst t; exact Hr).
    destruct (Nat.eqb t pr) eqn:Htpr.
    + apply IH.
      subst t. lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g;
      try (apply IH; subst t; lia).
      set (L1 :=
             switch L
               (gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)))
               t).
      assert (Hr1 : (r < length L1 - k)%nat).
      { unfold L1. rewrite switch_len. subst t. lia. }
      specialize (IH L1 r Hr1).
      rewrite IH. unfold L1.
      rewrite nth_switch_miss; auto; try lia.
Qed.

Lemma loop_replaceT_Z_suffix_Z_to_I_gen {n}
  (q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (pr < length L)%nat ->
    (q < n)%nat ->
    (k <= length L)%nat ->
    entry q (nth pr L (defaultT_I n)) = gZ ->
    forall r,
      (length L - k <= r < length L)%nat ->
      r <> pr ->
      entry q (nth r L (defaultT_I n)) = gZ ->
      entry q (nth r (loop_replaceT_Z n q pr k L) (defaultT_I n)) = gI.
Proof.
  induction k as [|k IH]; intros L HWF Hpr Hq Hk Hpiv r Hr Hneq HrZ.
  - cbn in Hr. lia.

  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    assert (Hr_cases : r = t \/ (r > t)%nat) by (subst t; lia).

    destruct (Nat.eqb t pr) eqn:Htpr.
    + apply Nat.eqb_eq in Htpr. subst t.
      eapply (IH L); try eassumption; try lia.

    + apply Nat.eqb_neq in Htpr.

      remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * destruct Hr_cases as [-> | Hgt].
        -- unfold entry in HrZ. cbn in HrZ.
           rewrite <- Hg in HrZ. discriminate.
        -- eapply (IH L); try eassumption; try lia.

      * destruct Hr_cases as [-> | Hgt].
        -- unfold entry in HrZ; cbn in HrZ; rewrite <- Hg in HrZ; discriminate.
        -- eapply (IH L); try eassumption; try lia.

      * destruct Hr_cases as [-> | Hgt].
        -- unfold entry in HrZ; cbn in HrZ; rewrite <- Hg in HrZ; discriminate.
        -- eapply (IH L); try eassumption; try lia.

      * set (L1 :=
          switch L
            (gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)))
            t).

        destruct Hr_cases as [-> | Hgt].
        -- unfold L1.
           rewrite loop_replaceT_Z_preserve_prefix;
             try rewrite switch_len; try lia.
           rewrite nth_switch_hit; try lia.

           rewrite (entry_gMulT
                     (nth pr L (defaultT_I n))
                     (nth t L (defaultT_I n))
                     q); try assumption.
           ++ rewrite Hpiv.
              unfold entry. cbn. rewrite <- Hg.
              reflexivity.
           ++ unfold WF_L in *.
             apply Forall_nth; auto; lia.
           ++ unfold WF_L in *.
             apply Forall_nth; auto; lia.
        -- eapply (IH L1); try eassumption; try lia.
           ++ unfold L1.
             rewrite switch_inc; try lia.
             unfold WF_L in *.
             repeat rewrite Forall_app.
             remember HWF as HWF'''. clear HeqHWF'''.
             rewrite nth_inc with (ls := L) (n := t) (x := (defaultT_I n)) in HWF; try lia.
             repeat rewrite Forall_app in HWF.
             destruct HWF as [HWF [HWF' HWF'']].
             repeat split; auto.
             constructor; auto.
             apply WF_gMulT;
               apply Forall_nth;
               auto; lia.
           ++ unfold L1; rewrite switch_len; exact Hpr.
           ++ unfold L1; rewrite switch_len; lia.
           ++ unfold L1, entry.
             rewrite nth_switch_miss; auto; lia.
           ++ unfold L1; rewrite switch_len.
              split; [subst t; lia | exact (proj2 Hr)].
           ++ unfold L1, entry.
             rewrite nth_switch_miss; auto; lia.
Qed.

Lemma loop_replaceT_Z_Z_to_I_allrows {n}
  (L : list (TType n)) (q pr : nat) :
  WF_L L ->
  (pr < length L)%nat ->
  (q < n)%nat ->
  entry q (nth pr L (defaultT_I n)) = gZ ->
  forall r,
    (r < length L)%nat ->
    r <> pr ->
    entry q (nth r L (defaultT_I n)) = gZ ->
    entry q (nth r (loop_replaceT_Z n q pr (length L) L) (defaultT_I n)) = gI.
Proof.
  intros HWF Hpr Hq Hpiv r Hr Hneq HrZ.
  eapply (loop_replaceT_Z_suffix_Z_to_I_gen q pr (length L)); eauto.
  lia.
Qed.


Definition noXY_except_pivot {n} (L : list (TType n)) (q pr : nat) : Prop :=
  forall r, (r < length L)%nat -> r <> pr ->
    isXY (entry q (nth r L (defaultT_I n))) = false.

Lemma loop_replaceT_Z_preserve_row_if_notZ {n}
  (q pr k : nat) :
  forall (L : list (TType n)) r,
    (k <= length L)%nat ->
    (r < length L)%nat ->
    r <> pr ->
    entry q (nth r L (defaultT_I n)) <> gZ ->
    nth r (loop_replaceT_Z n q pr k L) (defaultT_I n)
    =
    nth r L (defaultT_I n).
Proof.
  induction k as [|k IH]; intros L r Hk Hr Hrp HnotZ.
  - cbn [loop_replaceT_Z]. reflexivity.

  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htpr.
    + apply Nat.eqb_eq in Htpr.
      apply (IH L r); try assumption; lia.

    + apply Nat.eqb_neq in Htpr.

      remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.

      destruct g; try (
        apply (IH L r); try assumption; lia
      ).

      * set (L1 :=
          switch L
            (gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)))
            t).

        destruct (Nat.eq_dec r t) as [Hrt | Hrt].
        -- subst r.
           exfalso.
           apply HnotZ.
           unfold entry. cbn. now rewrite Hg.

        -- rewrite (IH L1 r); auto; try lia.
           ++ unfold L1.
             rewrite nth_switch_miss; auto; try lia.
           ++ unfold L1. rewrite switch_len. lia.
           ++ unfold L1. rewrite switch_len. exact Hr.
           ++ unfold entry.
              unfold L1.
              rewrite nth_switch_miss; auto; try lia.
Qed.

Lemma loop_replaceT_Z_preserves_I {n}
  (L : list (TType n)) (q pr : nat) :
  (pr < length L)%nat ->
  forall r, (r < length L)%nat -> r <> pr ->
    entry q (nth r L (defaultT_I n)) = gI ->
    entry q (nth r (loop_replaceT_Z n q pr (length L) L) (defaultT_I n)) = gI.
Proof.
  intros Hpr r Hr Hneq HI.
  assert (Hrow :
    nth r (loop_replaceT_Z n q pr (length L) L) (defaultT_I n)
    =
    nth r L (defaultT_I n)).
  { eapply (loop_replaceT_Z_preserve_row_if_notZ q pr (length L)); try lia.
    rewrite HI. discriminate. }
  unfold entry. now rewrite Hrow.
Qed.

Lemma loop_replaceT_Z_clears_all_to_I_under_noXY {n}
  (L : list (TType n)) (q pr : nat) :
  WF_L L ->
  (pr < length L)%nat ->
  (q < n)%nat ->
  entry q (nth pr L (defaultT_I n)) = gZ ->
  noXY_except_pivot L q pr ->
  forall r,
    (r < length L)%nat -> r <> pr ->
    entry q (nth r (loop_replaceT_Z n q pr (length L) L) (defaultT_I n)) = gI.
Proof.
  intros HWF Hpr Hq Hpiv HnoXY r Hr Hneq.
  destruct (entry q (nth r L (defaultT_I n))) eqn:Her.
  - rewrite loop_replaceT_Z_preserves_I; auto; try lia.
  - exfalso.
    specialize (HnoXY r Hr Hneq).
    cbn [isXY] in HnoXY. rewrite Her in HnoXY. discriminate.
  - exfalso.
    specialize (HnoXY r Hr Hneq).
    cbn [isXY] in HnoXY. rewrite Her in HnoXY. discriminate.
  - eapply loop_replaceT_Z_Z_to_I_allrows; eauto.
Qed.


Inductive JRet :=
| RetNone
| RetXY (pr : nat)
| RetZ  (pr : nat).

Definition JRet_ok {n}
  (q : nat) (QP : list (nat*nat)) (L : list (TType n))
  (res : JRet) (QP' : list (nat*nat)) (L' : list (TType n)) : Prop :=
  match res with
  | RetNone =>
      QP' = QP /\ L' = L

  | RetXY pr =>
      QP' = (q,pr)::QP /\
      L'  = loop_replaceT_XY n q pr (length L) L /\
      isXY (entry q (nth pr L (defaultT_I n))) = true

  | RetZ pr =>
      QP' = (q,pr)::QP /\
      L'  = loop_replaceT_Z n q pr (length L) L /\
      entry q (nth pr L (defaultT_I n)) = gZ
  end.

Definition JRet_shape_ok {n}
  (q : nat) (QP : list (nat*nat)) (L : list (TType n))
  (res : JRet) (QP' : list (nat*nat)) (L' : list (TType n)) : Prop :=
  match res with
  | RetNone =>
      QP' = QP /\ L' = L
  | RetXY pr =>
      QP' = (q,pr)::QP /\
      L'  = loop_replaceT_XY n q pr (length L) L
  | RetZ pr =>
      QP' = (q,pr)::QP /\
      L'  = loop_replaceT_Z  n q pr (length L) L
  end.

Lemma loop_j_return_QPL_classify_shape {n}
  (q : nat) (j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  loop_j_return_QPL n q j QP L Lz = (QP', L') ->
  exists res : JRet, JRet_shape_ok q QP L res QP' L'.
Proof.
  revert Lz QP' L'.
  induction j as [|j IH]; intros Lz QP' L' Hrun.
  - cbn [loop_j_return_QPL] in Hrun.
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + inversion Hrun; subst.
      exists RetNone. cbn. auto.
    + inversion Hrun; subst.
      exists (RetZ h). cbn. auto.

  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).

    destruct (existsb (fun qp : nat * nat => Nat.eqb (snd qp) t) QP) eqn:Hused.
    + eapply IH; eauto.
      subst t. rewrite Hused in Hrun. eauto.
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * eapply IH; eauto.
        subst t. rewrite Hused in Hrun. rewrite <- Hg in Hrun. eauto.
      * exists (RetXY t). cbn.
        subst t. rewrite Hused in Hrun. rewrite <- Hg in Hrun.
        inversion Hrun. subst. eauto.
      * exists (RetXY t). cbn.
        subst t. rewrite Hused in Hrun. rewrite <- Hg in Hrun.
        inversion Hrun. subst. eauto.
      * subst t. rewrite Hused in Hrun. rewrite <- Hg in Hrun.
        eapply IH; eauto.
Qed.

Lemma loop_j_return_QPL_classify_shape_with_XY {n}
  (q : nat) (j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  loop_j_return_QPL n q j QP L Lz = (QP', L') ->
  exists res : JRet,
    JRet_shape_ok q QP L res QP' L' /\
    (forall pr,
       res = RetXY pr ->
       isXY (entry q (nth pr L (defaultT_I n))) = true).
Proof.
  revert Lz QP' L'.
  induction j as [|j IH]; intros Lz QP' L' Hrun.
  - cbn [loop_j_return_QPL] in Hrun.
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + inversion Hrun; subst.
      exists RetNone. split.
      * cbn [JRet_shape_ok]. auto.
      * intros pr H. discriminate H.
    + inversion Hrun; subst.
      exists (RetZ h). split.
      * cbn [JRet_shape_ok]. auto.
      * intros pr H. discriminate H.

  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).
    destruct (existsb (fun qp : nat*nat => Nat.eqb (snd qp) t) QP) eqn:Hused.
    + subst t.
      rewrite Hused in Hrun.
      destruct (IH Lz QP' L' Hrun) as [res [Hshape Hxy]].
      exists res. split; [exact Hshape|exact Hxy].
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * subst t.
        rewrite Hused in Hrun. rewrite <- Hg in Hrun.
        destruct (IH Lz QP' L' Hrun) as [res [Hshape Hxy]].
        exists res. split; [exact Hshape|exact Hxy].

      * inversion Hrun; subst.
        exists (RetXY t). split.
        -- cbn [JRet_shape_ok]. 
           subst t.
           rewrite Hused in Hrun. rewrite <- Hg in Hrun.
           inversion Hrun. subst.
           auto.
        -- intros pr H.
           inversion H; subst pr.
           unfold entry, isXY. cbn. now rewrite <- Hg.

      * inversion Hrun; subst.
        exists (RetXY t). split.
        -- cbn [JRet_shape_ok].
           subst t.
           rewrite Hused in Hrun. rewrite <- Hg in Hrun.
           inversion Hrun. subst.
           auto.
        -- intros pr H.
           inversion H; subst pr.
           unfold entry, isXY. cbn. now rewrite <- Hg.

      * subst t.
        rewrite Hused in Hrun. rewrite <- Hg in Hrun.
        destruct (IH ((length L - S j)%nat ::Lz) QP' L' Hrun) as [res [Hshape Hxy]].
        exists res. split; [exact Hshape|exact Hxy].
Qed.

Definition isIZ_row_except_pivot {n} (q pr : nat) (L : list (TType n)) : Prop :=
  forall r, (r < length L)%nat -> r <> pr ->
    isIZ (entry q (nth r L (defaultT_I n))) = true.

Lemma loop_j_return_QPL_step_XY_only {n}
  (q : nat) (j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  length L <> 0%nat ->
  incl Lz (seq 0 (length L)) ->
  incl (map snd QP) (seq 0 (length L)) ->
  WF_L L ->
  (q < n)%nat ->
  loop_j_return_QPL n q j QP L Lz = (QP', L') ->
  exists res : JRet,
    JRet_shape_ok q QP L res QP' L' /\
    (forall pr,
       res = RetXY pr ->
       isIZ_row_except_pivot q pr L').
Proof.
  intros nonzerolen inclLzseq inclsndseq HWF Hq Hrun.
  destruct (loop_j_return_QPL_classify_shape_with_XY
              q j QP L Lz
              QP' L' Hrun)
    as [res [Hshape Hxy]].

  exists res.
  split.
  - exact Hshape.
  - intros pr Hres.
    subst res.
    cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP' HL'].
    subst QP' L'.

    assert (Hpiv : isXY (entry q (nth pr L (defaultT_I n))) = true).
    { exact (Hxy pr eq_refl). }

    unfold isIZ_row_except_pivot.
    intros r Hr Hneq.
    eapply loop_replaceT_XY_clears_all_to_IZ; eauto.
    2: rewrite loop_replaceT_XY_length in Hr; auto.
 
    pose (loop_j_return_QPL_incl_QP_seq_0_length_L n q j QP L Lz nonzerolen inclLzseq inclsndseq) as H.
    rewrite Hrun in H.
    simpl in H.
    unfold incl in H.
    assert (In pr (pr :: map snd QP)) by (left; auto).
    specialize (H pr H0).
    rewrite in_seq in H.
    lia.
Qed.



Definition Lz_ok {n} (q : nat) (L : list (TType n)) (Lz : list nat) : Prop :=
  Forall (fun pr => entry q (nth pr L (defaultT_I n)) = gZ) Lz.

Definition allI_on_qubit {n} (q : nat) (L : list (TType n)) : Prop :=
  forall r, (r < length L)%nat ->
    entry q (nth r L (defaultT_I n)) = gI.


Definition noXY_on_suffix {n} (L : list (TType n)) (q j : nat) : Prop :=
  forall r,
    (length L - j <= r < length L)%nat ->
    isXY (entry q (nth r L (defaultT_I n))) = false.

Definition is_RetXY_shape {n}
  (q : nat) (QP : list (nat*nat)) (L : list (TType n))
  (QP' : list (nat*nat)) (L' : list (TType n)) : Prop :=
  exists pr,
    QP' = (q,pr)::QP /\
    L'  = loop_replaceT_XY n q pr (length L) L.

Lemma noXY_on_suffix_S {n} (L : list (TType n)) (q j : nat) :
  isXY (entry q (nth (length L - S j)%nat L (defaultT_I n))) = false ->
  noXY_on_suffix (n:=n) L q j ->
  noXY_on_suffix (n:=n) L q (S j).
Proof.
  intros Ht Hsuf r Hr.
  assert (Hcases :
            r = (length L - S j)%nat \/
            (length L - j <= r < length L)%nat) by lia.
  destruct Hcases as [-> | Hr'].
  - exact Ht.
  - exact (Hsuf r Hr').
Qed.




Lemma loop_j_return_QPL_classify_shape_with_XY_Z_noXY_aux {n}
  (q : nat) (L : list (TType n)) :
  length L <> 0%nat ->
  forall j Lz QP' L',
    Lz_ok (n:=n) q L Lz ->
    loop_j_return_QPL n q j [] L Lz = (QP', L') ->
    exists res : JRet,
      JRet_shape_ok q [] L res QP' L' /\
      (forall pr,
         res = RetXY pr ->
         isXY (entry q (nth pr L (defaultT_I n))) = true) /\
      (forall pr,
         res = RetZ pr ->
         entry q (nth pr L (defaultT_I n)) = gZ /\
         noXY_on_suffix (n:=n) L q j).
Proof.
  intro Hlen.
  induction j as [|j IH]; intros Lz QP' L' HLzok Hrun.
  - cbn [loop_j_return_QPL] in Hrun.
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + inversion Hrun; subst.
      exists RetNone.
      split.
      * cbn [JRet_shape_ok]. auto.
      * split.
        -- intros pr H; inversion H.
        -- intros pr H; inversion H.
    + inversion Hrun; subst.
      exists (RetZ h).
      split. 
      * cbn [JRet_shape_ok]. auto.
      * split.
        -- intros pr H; inversion H.
        -- intros pr Hz.
           inversion Hz; subst pr.
           split.
           ++ unfold Lz_ok in HLzok.
              assert (Hin : In h Lz).
              { assert (Hin_rev : In h (rev Lz)) by (rewrite Hrev; left; reflexivity).
                apply in_rev in Hin_rev. exact Hin_rev. }
              remember HLzok as H'. clear HeqH'.
              rewrite Forall_forall in H'.
              specialize (H' h Hin).
              auto.
           ++ unfold noXY_on_suffix.
              intros r Hr. lia.
  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).

    cbn in Hrun.

    remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
    destruct g.
    + subst t.
      rewrite <- Hg in *.
      specialize (IH Lz QP' L' HLzok Hrun) as [res [Hshape [Hxy Hz]]].
      exists res. repeat split; try exact Hshape; try exact Hxy.
      specialize (Hz pr H) as [HzEntry Hsuf].
      auto.
      assert (Ht : isXY (entry q (nth (length L - S j) L (defaultT_I n))) = false).
      { unfold entry, isXY. cbn.
        symmetry in Hg. now rewrite Hg.
      }
      eapply noXY_on_suffix_S; auto.
      destruct (Hz pr H). auto.
    + inversion Hrun; subst.
      exists (RetXY t).
      repeat split.
      * cbn [JRet_shape_ok]. 
        subst t.
        rewrite <- Hg in *.
        inversion H0. subst.
        auto.
      * subst t. rewrite <- Hg in *.
        inversion H0. subst. auto.
      * intros pr Hz. inversion Hz.
        unfold entry.
        cbn [isXY].
        symmetry in Hg.
        rewrite Hg.
        reflexivity.
      * inversion H.
      * inversion H.
    + inversion Hrun; subst.
      exists (RetXY t).
      repeat split.
      * cbn [JRet_shape_ok]. 
        subst t.
        rewrite <- Hg in *.
        inversion H0. subst.
        auto.
      * subst t. rewrite <- Hg in *.
        inversion H0. subst. auto.
      * intros pr Hz. inversion Hz.
        unfold entry.
        cbn [isXY].
        symmetry in Hg.
        rewrite Hg.
        reflexivity.
      * inversion H.
      * inversion H.
    + assert (HLzok' : Lz_ok (n:=n) q L (t :: Lz)).
      { unfold Lz_ok in *.
        constructor.
        - unfold entry. cbn. symmetry in Hg. now rewrite Hg.
        - exact HLzok.
      }
      subst t. rewrite <- Hg in *.
      specialize (IH ((length L - S j)%nat :: Lz) QP' L' HLzok' Hrun) as [res [Hshape [Hxy Hz]]].
      exists res. repeat split; try exact Hshape; try exact Hxy.
      * destruct (Hz pr H). auto.
      * assert (Ht : isXY (entry q (nth (length L - S j)%nat L (defaultT_I n))) = false).
      { unfold entry, isXY. cbn.
        symmetry in Hg. now rewrite Hg.
      }
      eapply noXY_on_suffix_S; eauto; try lia.
      all: destruct (Hz pr H); auto.
Qed.

Lemma first_step_classify_with_XY_Z_noXY {n}
  (q : nat) (L : list (TType n)) (QP' : list (nat*nat)) (L' : list (TType n)) :
  length L <> 0%nat ->
  Lz_ok (n:=n) q L [] ->
  loop_j_return_QPL n q (length L) [] L [] = (QP', L') ->
  exists res : JRet,
    JRet_shape_ok q [] L res QP' L' /\
    (forall pr, res = RetXY pr ->
       isXY (entry q (nth pr L (defaultT_I n))) = true) /\
    (forall pr, res = RetZ pr ->
       entry q (nth pr L (defaultT_I n)) = gZ /\
       noXY_on_suffix (n:=n) L q (length L)).
Proof.
  intros Hlen HLzok0 Hrun.
  eapply (loop_j_return_QPL_classify_shape_with_XY_Z_noXY_aux q L); eauto.
Qed.


Lemma noXY_on_suffix_full_implies_noXY_except_pivot {n}
  (q pr : nat) (L : list (TType n)) :
  noXY_on_suffix (n:=n) L q (length L) ->
  noXY_except_pivot (n:=n) L q pr.
Proof.
  intro Hsuf.
  unfold noXY_except_pivot.
  intros r Hr _.
  apply (Hsuf r). split; lia.
Qed.



Definition allI_on_suffix {n} (L : list (TType n)) (q j : nat) : Prop :=
  forall r, (length L - j <= r < length L)%nat ->
    entry q (nth r L (defaultT_I n)) = gI.

Lemma allI_on_suffix_S {n} (L : list (TType n)) (q j : nat) :
  entry q (nth (length L - S j)%nat L (defaultT_I n)) = gI ->
  allI_on_suffix (n:=n) L q j ->
  allI_on_suffix (n:=n) L q (S j).
Proof.
  intros Ht Hsuf r Hr.
  assert (Hcases :
            r = (length L - S j)%nat \/
            (length L - j <= r < length L)%nat) by lia.
  destruct Hcases as [->|Hr']; auto.
Qed.

Lemma rev_eq_nil_iff_nil {A} (l : list A) :
  rev l = [] -> l = [].
Proof.
  intro H.
  apply length_zero_iff_nil.
  assert (length l = length (rev l)) by (symmetry; apply rev_length).
  rewrite H in H0. cbn in H0. exact H0.
Qed.

Lemma loop_j_return_QPL_Lz_nonempty_implies_QP_nonempty {n}
  (q : nat) (L : list (TType n)) :
  forall j Lz QP' L',
    Lz <> [] ->
    loop_j_return_QPL n q j [] L Lz = (QP', L') ->
    QP' <> [].
Proof.
  induction j as [|j IH]; intros Lz QP' L' HLz Hrun.
  - cbn [loop_j_return_QPL] in Hrun.
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + exfalso.
      apply HLz.
     apply rev_eq_nil_iff_nil in Hrev. exact Hrev.
    + inversion Hrun; subst QP'.
      discriminate.
  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).
    cbn in Hrun.

    remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
    destruct g.
    + subst t.
      rewrite <- Hg in *.
      eapply IH; eauto.
    + subst t. rewrite <- Hg in *.
      inversion Hrun; subst QP'.
      discriminate.
    + subst t. rewrite <- Hg in *.
      inversion Hrun; subst QP'.
      discriminate.
    + subst t. rewrite <- Hg in *.
      eapply IH with (Lz := (length L - S j)%nat :: Lz); eauto.
      intro; discriminate.
Qed.

Lemma allI_on_suffix_if_returns_none_aux {n}
  (q : nat) (L : list (TType n)) :
  forall j Lz QP' L',
    loop_j_return_QPL n q j [] L Lz = (QP', L') ->
    QP' = [] ->
    L' = L ->
    Lz = [] ->
    allI_on_suffix (n:=n) L q j.
Proof.
  induction j as [|j IH]; intros Lz QP' L' Hrun HQ HL HLz.
  - unfold allI_on_suffix. intros r Hr. cbn in Hr. lia.
  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).
    cbn in Hrun.

    remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
    destruct g.
    + assert (Hsuf : allI_on_suffix L q j).
      { subst t. rewrite <- Hg in *. eapply IH; eauto. }
      assert (Ht : entry q (nth t L (defaultT_I n)) = gI).
      { unfold entry. symmetry in Hg. exact Hg. }
      eapply allI_on_suffix_S; eauto.

    + subst QP' L'.
      subst t. rewrite <- Hg in *. inversion Hrun.
    + subst QP' L'. 
      subst t. rewrite <- Hg in *. inversion Hrun.
    + subst Lz.
      symmetry in Hg.
      subst t. 
      rewrite Hg in *.

      exfalso.
      assert (Hne : QP' <> []).
      { eapply (loop_j_return_QPL_Lz_nonempty_implies_QP_nonempty q L j [(length L - S j)%nat]QP' L'); eauto.
        intro; discriminate.
      }
      apply Hne. exact HQ.
Qed.


Lemma allI_on_suffix_full_implies_allI_on_qubit {n}
  (q : nat) (L : list (TType n)) :
  allI_on_suffix (n:=n) L q (length L) ->
  allI_on_qubit (n:=n) q L.
Proof.
  intro Hsuf.
  unfold allI_on_qubit.
  intros r Hr.
  apply (Hsuf r). split; lia.
Qed.


Lemma first_step_complete {n}
  (q : nat) (L : list (TType n)) (QP' : list (nat*nat)) (L' : list (TType n)) :
  length L <> 0%nat ->
  WF_L L ->
  (q < n)%nat ->
  loop_j_return_QPL n q (length L) [] L [] = (QP', L') ->
  exists res : JRet,
    JRet_shape_ok q [] L res QP' L' /\
    match res with
    | RetNone =>
        allI_on_qubit (n:=n) q L
    | RetXY pr =>
        isIZ_row_except_pivot (n:=n) q pr L'
    | RetZ pr =>
        forall r, (r < length L)%nat -> r <> pr ->
          entry q (nth r L' (defaultT_I n)) = gI
    end.
Proof.
  intros Hlen HWF Hq Hrun.

  pose (loop_j_return_QPL_classify_shape_with_XY_Z_noXY_aux
                q L Hlen (length L) [] QP' L') as H'. 
  assert (Lz_ok q L []) by (constructor; auto).
  destruct (H' H Hrun) as [res [Hshape [Hxy Hz]]].

  exists res.
  split; [exact Hshape|].

  destruct res as [|prXY|prZ].
  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst QP' L'.
    pose (allI_on_suffix_if_returns_none_aux (n:=n) q L (length L) [] [] L Hrun eq_refl eq_refl eq_refl)
      as Hsuf.
    apply allI_on_suffix_full_implies_allI_on_qubit.
    exact Hsuf.
  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst L' QP'.
    pose proof (Hxy prXY eq_refl) as HpivXY.
    unfold isIZ_row_except_pivot.
    intros r Hr Hneq.
    eapply loop_replaceT_XY_clears_all_to_IZ; eauto.
    2: rewrite loop_replaceT_XY_length in Hr; auto.
    pose (loop_j_return_QPL_incl_QP_seq_0_length_L n q (length L) [] L [] Hlen) as H''.
    simpl in H''.
    assert (incl [] (seq 0 (length L))).
    { unfold incl. intros a H0. inversion H0. }
    specialize (H'' H0 H0).
    rewrite Hrun in H''.
    simpl in H''.
    unfold incl in H''.
    assert (In prXY [prXY]) by (left; auto).
    specialize (H'' prXY H1).
    rewrite in_seq in H''.
    lia.
  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst L' QP'.
    pose proof (Hz prZ eq_refl) as [HpivZ HnoXYsuf].
    pose proof (noXY_on_suffix_full_implies_noXY_except_pivot q prZ L HnoXYsuf) as HnoXY.
    intros r Hr Hneq.
    eapply loop_replaceT_Z_clears_all_to_I_under_noXY; eauto.
    pose (loop_j_return_QPL_incl_QP_seq_0_length_L n q (length L) [] L [] Hlen) as H''.
    simpl in H''.
    assert (incl [] (seq 0 (length L))).
    { unfold incl. intros a H0. inversion H0. }
    specialize (H'' H0 H0).
    rewrite Hrun in H''.
    simpl in H''.
    unfold incl in H''.
    assert (In prZ [prZ]) by (left; auto).
    specialize (H'' prZ H1).
    rewrite in_seq in H''.
    lia.
Qed.


Definition q0_of (start n : nat) : nat :=
  nth 0 ((skipn start (List.seq 0 n)) ++ (firstn start (List.seq 0 n))) 0%nat.

Definition first_step {n} (start : nat) (L : list (TType n)) :=
  loop_j_return_QPL n (q0_of start n) (length L) [] L [].


Definition ColI_except {n} (q0 pr : nat) (L : list (TType n)) : Prop :=
  forall r, (r < length L)%nat -> r <> pr ->
    entry q0 (nth r L (defaultT_I n)) = gI.


Definition ColAllI {n} (q0 : nat) (L : list (TType n)) : Prop :=
  forall r, (r < length L)%nat ->
    entry q0 (nth r L (defaultT_I n)) = gI.

Definition ColIZ_except {n} (q0 pr : nat) (L : list (TType n)) : Prop :=
  forall r, (r < length L)%nat -> r <> pr ->
    isIZ (entry q0 (nth r L (defaultT_I n))) = true.

Inductive FirstColState (n : nat) (q0 : nat) (L : list (TType n)) : Prop :=
| FCS_None : ColAllI (n:=n) q0 L -> FirstColState n q0 L
| FCS_Z    : forall pr, ColI_except (n:=n) q0 pr L -> FirstColState n q0 L
| FCS_XY   : forall pr, ColIZ_except (n:=n) q0 pr L -> FirstColState n q0 L.

Lemma first_step_gives_FirstColState {n}
  (q0 : nat) (L : list (TType n)) (QP1 : list (nat*nat)) (L1 : list (TType n)) :
  length L <> 0%nat ->
  WF_L L ->
  (q0 < n)%nat ->
  loop_j_return_QPL n q0 (length L) [] L [] = (QP1, L1) ->
  FirstColState n q0 L1.
Proof.
  intros Hlen HWF Hq0 Hrun.
  destruct (first_step_complete q0 L QP1 L1
            Hlen HWF Hq0 Hrun)
    as [res [Hshape Hcase]].

  destruct res as [|pr|pr].
  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL1]. subst L1.
    apply FCS_None.
    unfold ColAllI.
    exact Hcase.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL1]. subst L1.
    apply (FCS_XY n q0 (loop_replaceT_XY n q0 pr (length L) L) pr).
    unfold ColIZ_except, isIZ_row_except_pivot in *.
    exact Hcase.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [_ HL1]. subst L1.
    apply (FCS_Z n q0 (loop_replaceT_Z n q0 pr (length L) L) pr).
    unfold ColI_except in *.
    rewrite loop_replaceT_Z_length.
    exact Hcase.
Qed.

Lemma gMul_base_II :
  gMul_base gI gI = gI.
Proof. reflexivity. Qed.

Lemma entry_gMulT_II {n} (q0 : nat) (A B : TType n) :
  WF_T A -> WF_T B ->
  (q0 < n)%nat ->
  entry q0 A = gI ->
  entry q0 B = gI ->
  entry q0 (gMulT A B) = gI.
Proof.
  intros HWA HWB Hq0 HA HB.
  rewrite (entry_gMulT A B q0); try assumption.
  rewrite HA, HB.
  exact gMul_base_II.
Qed.

Lemma ColAllI_switch {n} (q0 : nat) (L : list (TType n)) (x : TType n) (t : nat) :
  ColAllI (n:=n) q0 L ->
  entry q0 x = gI ->
  ColAllI (n:=n) q0 (switch L x t).
Proof.
  intros Hall Hx r Hr.
  destruct (Nat.eqb r t) eqn:Hrt.
  - apply Nat.eqb_eq in Hrt. subst r.
  rewrite nth_switch_hit; auto; try lia.
  rewrite switch_len in Hr.
  auto.
  - apply Nat.eqb_neq in Hrt.
    rewrite nth_switch_miss; auto; try lia.
    apply Hall.
    rewrite switch_len in Hr. auto.
Qed.

Lemma entry_defaultT_I {n} (q0 : nat) :
  (q0 < n)%nat ->
  entry q0 (defaultT_I n) = gI.
Proof.
  intro Hq0.
  unfold entry, defaultT_I.
  cbn.
  rewrite nth_repeat; try lia. auto.
Qed.

Lemma ColAllI_nth_any {n} (q0 r : nat) (L : list (TType n)) :
  ColAllI (n:=n) q0 L ->
  (q0 < n)%nat ->
  entry q0 (nth r L (defaultT_I n)) = gI.
Proof.
  intros Hall Hq0.
  destruct (Nat.lt_ge_cases r (length L)) as [Hr|Hr].
  - apply Hall; exact Hr.
  - rewrite nth_overflow; try lia.
    apply entry_defaultT_I; exact Hq0.
Qed.


Lemma WF_T_nth_default {n} (L : list (TType n)) (r : nat) :
  WF_L (n:=n) L ->
  WF_T (n:=n) (nth r L (defaultT_I n)).
Proof.
  intro HWF.
  destruct (Nat.lt_ge_cases r (length L)) as [Hr|Hr].
  - unfold WF_L in *.
    apply Forall_nth; auto.
  - rewrite nth_overflow; try lia.
    apply WF_defaultT_I.
Qed.


Lemma loop_replaceT_XY_preserves_ColAllI {n}
  (q0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColAllI (n:=n) q0 L ->
    ColAllI (n:=n) q0 (loop_replaceT_XY n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hall.
  - cbn [loop_replaceT_XY]. exact Hall.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * eapply IH; eauto; lia.
      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT.
           ++ subst A.
             apply WF_T_nth_default.
             auto.
           ++ subst B.
              apply WF_T_nth_default.
              auto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- apply ColAllI_switch.
           ++ exact Hall.
           ++ subst x A B.
              eapply entry_gMulT_II.
              ** apply WF_T_nth_default. auto.
              ** apply WF_T_nth_default. auto.
              ** exact Hq0.
              ** apply ColAllI_nth_any; assumption.
              ** apply ColAllI_nth_any; assumption.

      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT.
           ++ subst A.
             apply WF_T_nth_default.
             auto.
           ++ subst B.
              apply WF_T_nth_default.
              auto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- apply ColAllI_switch.
           ++ exact Hall.
           ++ subst x A B.
              eapply entry_gMulT_II.
              ** apply WF_T_nth_default. auto.
              ** apply WF_T_nth_default. auto.
              ** exact Hq0.
              ** apply ColAllI_nth_any; assumption.
              ** apply ColAllI_nth_any; assumption.
      * eapply IH; eauto; lia.
Qed.



Lemma loop_replaceT_Z_preserves_ColAllI {n}
  (q0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColAllI (n:=n) q0 L ->
    ColAllI (n:=n) q0 (loop_replaceT_Z n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hall.
  - cbn [loop_replaceT_Z]. exact Hall.

  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * eapply IH; eauto; lia.
      * eapply IH; eauto; lia.
      * eapply IH; eauto; lia.
      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT.
           ++ eapply WF_T_nth_default; eauto.
           ++ eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- apply ColAllI_switch.
           ++ exact Hall.
           ++ subst x A B.
              eapply entry_gMulT_II; try eapply WF_T_nth_default; try eauto.
              ** apply ColAllI_nth_any; eauto.
              ** apply ColAllI_nth_any; eauto.
Qed.


Lemma loop_replaceT_Z_preserves_ColI_except {n}
  (q0 pr0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColI_except (n:=n) q0 pr0 L ->
    entry q0 (nth pr L (defaultT_I n)) = gI ->
    ColI_except (n:=n) q0 pr0 (loop_replaceT_Z n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hcol HpivI.
  - cbn [loop_replaceT_Z]. exact Hcol.

  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      set (A := nth pr L (defaultT_I n)).
      set (B := nth t  L (defaultT_I n)).
      set (x := gMulT A B).
      set (L1 := switch L x t).

      eapply IH.
      * eapply WF_switch; eauto.
        unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
      * exact Hq0.
      * unfold L1. rewrite switch_len. lia.
      * unfold ColI_except in *.
        intros r Hr Hneq_pr0.
        subst L1.
        destruct (Nat.eqb r t) eqn:Hrt.
        -- apply Nat.eqb_eq in Hrt. subst r.
           subst x A B.
           rewrite nth_switch_hit. 2: rewrite switch_len in Hr; auto.
           eapply entry_gMulT_II; try eauto.
           ++ apply WF_T_nth_default; auto.
           ++ apply WF_T_nth_default; auto.
           ++ apply Hcol; auto. rewrite switch_len in Hr; auto.
        -- apply Nat.eqb_neq in Hrt.
           rewrite switch_len in Hr.
           rewrite nth_switch_miss; auto.
      * unfold L1. rewrite Nat.eqb_neq in Htp.
        rewrite nth_switch_miss; auto.
Qed.

Lemma loop_replaceT_XY_preserves_ColI_except {n}
  (q0 pr0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColI_except (n:=n) q0 pr0 L ->
    entry q0 (nth pr L (defaultT_I n)) = gI ->
    ColI_except (n:=n) q0 pr0 (loop_replaceT_XY n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hcol HpivI.
  - cbn [loop_replaceT_XY]. exact Hcol.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * eapply IH; eauto; lia.

      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- unfold ColI_except in *.
           intros r Hr Hneq_pr0.
           destruct (Nat.eqb r t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt. subst r.
              subst x A B.
              subst L1.
              rewrite nth_switch_hit; auto. 2: rewrite switch_len in Hr; auto.
              eapply entry_gMulT_II; try eauto.
              ** apply WF_T_nth_default; auto.
              ** apply WF_T_nth_default; auto.
              ** apply Hcol; auto. rewrite switch_len in Hr; auto.
           ++ apply Nat.eqb_neq in Hrt.
              subst L1.
              rewrite switch_len in Hr.
              rewrite nth_switch_miss; auto.
        --  unfold L1.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto.
      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- unfold ColI_except in *.
           intros r Hr Hneq_pr0.
           destruct (Nat.eqb r t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt. subst r.
              subst x A B.
              subst L1.
              rewrite nth_switch_hit; auto. 2: rewrite switch_len in Hr; auto.
              eapply entry_gMulT_II; try eauto.
              ** apply WF_T_nth_default; auto.
              ** apply WF_T_nth_default; auto.
              ** apply Hcol; auto. rewrite switch_len in Hr; auto.
           ++ apply Nat.eqb_neq in Hrt.
              subst L1.
              rewrite switch_len in Hr.
              rewrite nth_switch_miss; auto.
        -- unfold L1.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto.
      * eapply IH; eauto; lia.
Qed.

Lemma gMul_base_closed_IZ (a b : Pauli) :
  isIZ a = true ->
  isIZ b = true ->
  isIZ (gMul_base a b) = true.
Proof.
  destruct a, b; cbn; try discriminate; reflexivity.
Qed.

Lemma entry_gMulT_IZ_closed {n} (q0 : nat) (A B : TType n) :
  WF_T A -> WF_T B -> (q0 < n)%nat ->
  isIZ (entry q0 A) = true ->
  isIZ (entry q0 B) = true ->
  isIZ (entry q0 (gMulT A B)) = true.
Proof.
  intros HWA HWB Hq0 HA HB.
  rewrite (entry_gMulT A B q0); try assumption.
  eapply gMul_base_closed_IZ; eauto.
Qed.

Lemma loop_replaceT_Z_preserves_ColIZ_except {n}
  (q0 pr0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColIZ_except (n:=n) q0 pr0 L ->
    isIZ (entry q0 (nth pr L (defaultT_I n))) = true ->
    ColIZ_except (n:=n) q0 pr0 (loop_replaceT_Z n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hcol HpivIZ.
  - cbn [loop_replaceT_Z]. exact Hcol.

  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      set (A := nth pr L (defaultT_I n)).
      set (B := nth t  L (defaultT_I n)).
      set (x := gMulT A B).
      set (L1 := switch L x t).

      eapply IH.
      * eapply WF_switch; eauto.
        unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
      * exact Hq0.
      * unfold L1. rewrite switch_len. lia.
      * unfold ColIZ_except in *.
        intros r Hr Hneq_pr0.
        destruct (Nat.eqb r t) eqn:Hrt.
        -- apply Nat.eqb_eq in Hrt. subst r.
           subst x A B.
           subst L1.
           rewrite nth_switch_hit; auto. 2: rewrite switch_len in Hr; auto.
           eapply entry_gMulT_IZ_closed; try eauto.
           ++ apply WF_T_nth_default; auto.
           ++ apply WF_T_nth_default; auto.
           ++ apply Hcol. rewrite switch_len in Hr; auto. rewrite Nat.eqb_neq in Htp; auto.
        -- apply Nat.eqb_neq in Hrt.
           subst L1.
           rewrite switch_len in Hr.
           rewrite nth_switch_miss; auto.
      * unfold L1.
        rewrite Nat.eqb_neq in Htp.
        rewrite nth_switch_miss; auto.
Qed.


Lemma loop_replaceT_XY_preserves_ColIZ_except {n}
  (q0 pr0 q pr k : nat) :
  forall (L : list (TType n)),
    WF_L L ->
    (q0 < n)%nat ->
    (k <= length L)%nat ->
    ColIZ_except (n:=n) q0 pr0 L ->
    isIZ (entry q0 (nth pr L (defaultT_I n))) = true ->
    ColIZ_except (n:=n) q0 pr0 (loop_replaceT_XY n q pr k L).
Proof.
  induction k as [|k IH]; intros L HWF Hq0 Hk Hcol HpivIZ.
  - cbn [loop_replaceT_XY]. exact Hcol.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * eapply IH; eauto; lia.

      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- unfold ColIZ_except in *.
           intros r Hr Hneq_pr0.
           destruct (Nat.eqb r t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt. subst r.
              subst L1.
              subst x A B.
              rewrite nth_switch_hit; auto. 2: rewrite switch_len in Hr; auto.
              eapply entry_gMulT_IZ_closed; try eauto.
              ** apply WF_T_nth_default; auto.
              ** apply WF_T_nth_default; auto.
              ** apply Hcol; auto. rewrite switch_len in Hr; auto.
           ++ apply Nat.eqb_neq in Hrt.
              subst L1.
              rewrite nth_switch_miss; auto.
              apply Hcol; auto. rewrite switch_len in Hr; auto.
        -- unfold L1.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto.
      * set (A := nth pr L (defaultT_I n)).
        set (B := nth t  L (defaultT_I n)).
        set (x := gMulT A B).
        set (L1 := switch L x t).

        eapply IH.
        -- eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold L1. rewrite switch_len. lia.
        -- unfold ColIZ_except in *.
           intros r Hr Hneq_pr0.
           destruct (Nat.eqb r t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt. subst r.
              subst L1.
              subst x A B.
              rewrite nth_switch_hit; auto. 2: rewrite switch_len in Hr; auto.
              eapply entry_gMulT_IZ_closed; try eauto.
              ** apply WF_T_nth_default; auto.
              ** apply WF_T_nth_default; auto.
              ** apply Hcol; auto. rewrite switch_len in Hr; auto.
           ++ apply Nat.eqb_neq in Hrt.
              subst L1.
              rewrite nth_switch_miss; auto.
              apply Hcol; auto. rewrite switch_len in Hr; auto.
        -- unfold L1.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto.
      * eapply IH; eauto; lia.
Qed.


Lemma existsb_snd_eqb_true_iff (QP : list (nat*nat)) (t : nat) :
  existsb (fun qp => Nat.eqb (snd qp) t) QP = true <->
  In t (map snd QP).
Proof.
  induction QP as [|[a b] tl IH]; cbn.
  - split; intro H; try discriminate; contradiction.
  - split.
    + intro H.
      rewrite <- IH.
      apply Bool.orb_true_iff in H.
      destruct H as [Hb|Htl].
      * left. apply Nat.eqb_eq in Hb. subst. reflexivity.
      * right. exact Htl.
    + intro H.
      destruct H as [Hh|Htl].
      * apply Bool.orb_true_iff. left.
        apply Nat.eqb_eq. exact Hh.
      * apply Bool.orb_true_iff. right.
        rewrite IH.
        exact Htl.
Qed.

Lemma existsb_snd_eqb_false_iff (QP : list (nat*nat)) (t : nat) :
  existsb (fun qp => Nat.eqb (snd qp) t) QP = false <->
  ~ In t (map snd QP).
Proof.
  rewrite <- (existsb_snd_eqb_true_iff QP t).
  split; intro H.
  - intro Hin. rewrite Hin in H. discriminate.
  - destruct (existsb (fun qp : nat*nat => Nat.eqb (snd qp) t) QP) eqn:E; auto.
    exfalso. apply H. auto.
Qed.


Definition Lz_notin_QP (QP : list (nat*nat)) (Lz : list nat) : Prop :=
  Forall (fun t => ~ In t (map snd QP)) Lz.

Lemma Lz_notin_QP_In {QP Lz t} :
  Lz_notin_QP QP Lz ->
  In t Lz ->
  ~ In t (map snd QP).
Proof.
  unfold Lz_notin_QP.
  intros HFor Hin.
  rewrite Forall_forall in HFor.
  apply HFor; auto.
Qed.


Lemma loop_j_return_QPL_new_pivot_not_in_old {n}
  (q : nat) (j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) (pr : nat) :
  Lz_notin_QP QP Lz ->
  loop_j_return_QPL n q j QP L Lz = (QP', L') ->
  QP' = (q,pr) :: QP ->
  ~ In pr (map snd QP).
Proof.
  revert QP L Lz QP' L' pr.
  induction j as [|j IH]; intros QP L Lz QP' L' pr HLzNotin Hrun HQP'.
  - cbn [loop_j_return_QPL] in Hrun.
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + inversion Hrun; subst QP' L'.
      apply (f_equal (@length _)) in H0.
      cbn in H0. lia.

    + inversion Hrun; subst QP' L'.
      inversion H0; subst pr.

      assert (Hin : In h Lz).
      { assert (In h (rev Lz)) by (rewrite Hrev; left; reflexivity).
        apply in_rev in H. exact H.
      }
      eapply Lz_notin_QP_In; eauto.

  - cbn [loop_j_return_QPL] in Hrun.
    set (t := (length L - S j)%nat).

    destruct (existsb (fun qp : nat*nat => Nat.eqb (snd qp) t) QP) eqn:Hused.
    + subst t.
      rewrite Hused in Hrun.
      eapply IH; eauto.
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g.
      * subst t.
        rewrite Hused in Hrun.
        rewrite <- Hg in Hrun.
        eapply IH; eauto.
      * subst t.
        rewrite Hused in Hrun.
        rewrite <- Hg in Hrun.
        inversion Hrun; subst QP' L'.
        inversion H0; subst pr.
        apply (proj1 (existsb_snd_eqb_false_iff QP (length L - S j)%nat)).
        exact Hused.
      * subst t.
        rewrite Hused in Hrun.
        rewrite <- Hg in Hrun.
        inversion Hrun; subst QP' L'.
        inversion H0; subst pr.
        apply (proj1 (existsb_snd_eqb_false_iff QP (length L - S j)%nat)).
        exact Hused.
      * assert (HLzNotin' : Lz_notin_QP QP (t :: Lz)).
        { unfold Lz_notin_QP in *.
          constructor.
          - apply (proj1 (existsb_snd_eqb_false_iff QP t)).
            exact Hused.
          - exact HLzNotin.
        }
        subst t.
        rewrite Hused in Hrun.
        rewrite <- Hg in Hrun.
        eapply IH; eauto.
Qed.

Lemma loop_j_return_QPL_preserves_FirstColState {n}
  (q0 qnext j : nat)
  (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  WF_L L ->
  (q0 < n)%nat ->
  length L <> 0%nat ->
  incl Lz (seq 0 (length L)) ->
  incl (map snd QP) (seq 0 (length L)) ->
  Lz_notin_QP QP Lz ->
  FirstColState n q0 L ->
  (forall pr0, (ColI_except (n:=n) q0 pr0 L -> In pr0 (map snd QP))) ->
  (forall pr0, (ColIZ_except (n:=n) q0 pr0 L -> In pr0 (map snd QP))) ->
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  FirstColState n q0 L'.
Proof.
  intros HWF Hq0 Hlen HLz HQP HLzNotin Hstate Hpr0_in_Z Hpr0_in_XY Hrun.

  destruct (loop_j_return_QPL_classify_shape
              qnext j QP L Lz
              QP' L' Hrun)
    as [res Hshape].

  inversion Hstate as [HallI | pr0 HI | pr0 HIZ]; subst.

  - destruct res as [|prNew|prNew].
    + apply FCS_None.
      cbn [JRet_shape_ok] in Hshape. destruct Hshape as [_ HL]. subst L'. exact HallI.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [_ HL]. subst L'.
      apply FCS_None.
      eapply loop_replaceT_XY_preserves_ColAllI; eauto.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [_ HL]. subst L'.
      apply FCS_None.
      eapply loop_replaceT_Z_preserves_ColAllI; eauto.

  - destruct res as [|prNew|prNew].
    + cbn [JRet_shape_ok] in Hshape. destruct Hshape as [_ HL]. subst L'.
      apply (FCS_Z n q0 L pr0). exact HI.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [HQP' HL]. subst QP' L'.
      assert (Hnotin : ~ In prNew (map snd QP)).
      { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
      assert (Hin0 : In pr0 (map snd QP)). { apply (Hpr0_in_Z pr0 HI). }
      assert (Hneq : prNew <> pr0).
      { intro. subst. contradiction. }
      assert (HpivI : entry q0 (nth prNew L (defaultT_I n)) = gI).
      { apply HI.
        - pose (loop_j_return_QPL_incl_QP_seq_0_length_L n qnext j QP L Lz Hlen HLz HQP) as H'.
          rewrite Hrun in H'.
          simpl in H'.
          unfold incl in H'.
          assert (temp: In prNew (prNew :: map snd QP)) by (left; auto).
          specialize (H' prNew temp).
          rewrite in_seq in H'.
          lia.
        - exact Hneq.
      }
      apply (FCS_Z n q0 (loop_replaceT_XY n qnext prNew (length L) L) pr0).
      eapply loop_replaceT_XY_preserves_ColI_except; eauto; lia.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [HQP' HL]. subst QP' L'.
      assert (Hnotin : ~ In prNew (map snd QP)).
      { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
      assert (Hin0 : In pr0 (map snd QP)). { apply (Hpr0_in_Z pr0 HI). }
      assert (Hneq : prNew <> pr0).
      { intro. subst. contradiction. }
      assert (HpivI : entry q0 (nth prNew L (defaultT_I n)) = gI).
      { apply HI. 2: exact Hneq.
        pose (loop_j_return_QPL_incl_QP_seq_0_length_L n qnext j QP L Lz Hlen HLz HQP) as H'.
        rewrite Hrun in H'.
        simpl in H'.
        unfold incl in H'.
        assert (temp: In prNew (prNew :: map snd QP)) by (left; auto).
        specialize (H' prNew temp).
        rewrite in_seq in H'.
        lia.
      }
      apply (FCS_Z n q0 (loop_replaceT_Z n qnext prNew (length L) L) pr0).
      eapply loop_replaceT_Z_preserves_ColI_except; eauto; lia.

  - destruct res as [|prNew|prNew].
    + cbn [JRet_shape_ok] in Hshape. destruct Hshape as [_ HL]. subst L'.
      apply (FCS_XY n q0 L pr0). exact HIZ.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [HQP' HL]. subst QP' L'.
      assert (Hnotin : ~ In prNew (map snd QP)).
      { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
      assert (Hin0 : In pr0 (map snd QP)). { apply (Hpr0_in_XY pr0 HIZ). }
      assert (Hneq : prNew <> pr0).
      { intro. subst. contradiction. }
      assert (HpivIZ : isIZ (entry q0 (nth prNew L (defaultT_I n))) = true).
      { apply HIZ. 2: exact Hneq.
        pose (loop_j_return_QPL_incl_QP_seq_0_length_L n qnext j QP L Lz Hlen HLz HQP) as H'.
        rewrite Hrun in H'.
        simpl in H'.
        unfold incl in H'.
        assert (temp: In prNew (prNew :: map snd QP)) by (left; auto).
        specialize (H' prNew temp).
        rewrite in_seq in H'.
        lia.
      }
      apply (FCS_XY n q0 (loop_replaceT_XY n qnext prNew (length L) L) pr0).
      eapply loop_replaceT_XY_preserves_ColIZ_except; eauto; lia.

    + cbn [JRet_shape_ok] in Hshape.
      destruct Hshape as [HQP' HL]. subst QP' L'.
      assert (Hnotin : ~ In prNew (map snd QP)).
      { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
      assert (Hin0 : In pr0 (map snd QP)). { apply (Hpr0_in_XY pr0 HIZ). }
      assert (Hneq : prNew <> pr0).
      { intro. subst. contradiction. }
      assert (HpivIZ : isIZ (entry q0 (nth prNew L (defaultT_I n))) = true).
      { apply HIZ. 2: exact Hneq.
        pose (loop_j_return_QPL_incl_QP_seq_0_length_L n qnext j QP L Lz Hlen HLz HQP) as H'.
        rewrite Hrun in H'.
        simpl in H'.
        unfold incl in H'.
        assert (temp: In prNew (prNew :: map snd QP)) by (left; auto).
        specialize (H' prNew temp).
        rewrite in_seq in H'.
        lia.
      }
      apply (FCS_XY n q0 (loop_replaceT_Z n qnext prNew (length L) L) pr0).
      eapply loop_replaceT_Z_preserves_ColIZ_except; eauto; lia.
Qed.


Lemma incl_nil_seq (m : nat) : incl ([] : list nat) (seq 0 m).
Proof. intros x H. inversion H. Qed.

Lemma Lz_notin_QP_nil (QP : list (nat*nat)) : Lz_notin_QP QP [].
Proof. unfold Lz_notin_QP. constructor. Qed.

Lemma In_map_snd_cons {a b : nat} {QP : list (nat*nat)} :
  In b (map snd ((a,b)::QP)).
Proof. cbn. left. reflexivity. Qed.

Lemma In_map_fst_of_In {A B} {x : A*B} {QP : list (A*B)} :
  In x QP -> In (fst x) (map fst QP).
Proof.
  intro Hin. induction QP as [|h tl IH]; cbn in *.
  - contradiction.
  - destruct Hin as [->|Hin]; [left; reflexivity|right; auto].
Qed.

Lemma In_map_snd_of_In {A B} {x : A*B} {QP : list (A*B)} :
  In x QP -> In (snd x) (map snd QP).
Proof.
  intro Hin. induction QP as [|h tl IH]; cbn in *.
  - contradiction.
  - destruct Hin as [->|Hin]; [left; reflexivity|right; auto].
Qed.

Lemma In_map_snd_preserved_by_cons {a b : nat} {QP : list (nat*nat)} {t : nat} :
  In t (map snd QP) -> In t (map snd ((a,b)::QP)).
Proof. intro Hin. cbn. right. exact Hin. Qed.

Definition NoPair (q0 : nat) (QP : list (nat*nat)) : Prop :=
  forall pr, ~ In (q0, pr) QP.

Inductive FirstColInv (n : nat) (q0 : nat) : list (nat*nat) -> list (TType n) -> Prop :=
| InvNone QP L :
    ColAllI (n:=n) q0 L ->
    NoPair q0 QP ->
    FirstColInv n q0 QP L
| InvZ QP L pr0 :
    entry q0 (nth pr0 L (defaultT_I n)) = gZ ->
    ColI_except (n:=n) q0 pr0 L ->
    In (q0, pr0) QP ->
    FirstColInv n q0 QP L
| InvXY QP L pr0 :
    isXY (entry q0 (nth pr0 L (defaultT_I n))) = true ->
    ColIZ_except (n:=n) q0 pr0 L ->
    In (q0, pr0) QP ->
    FirstColInv n q0 QP L.




Lemma loop_j_return_QPL_preserves_NoPair {n}
  (q0 qnext j : nat)
  (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  qnext <> q0 ->
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  NoPair q0 QP ->
  NoPair q0 QP'.
Proof.
  intros Hneq Hrun Hno pr.

  destruct (loop_j_return_QPL_classify_shape
              qnext j
             QP L Lz
              QP' L' Hrun)
    as [res Hshape].

  destruct res as [|prNew|prNew];
    cbn [JRet_shape_ok] in Hshape;
    destruct Hshape as [HQP _];
    subst QP'.

  - exact (Hno pr).

  - cbn.
    intro Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      contradiction.
    + exact (Hno pr Hin).

  - cbn.
    intro Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      contradiction.
    + exact (Hno pr Hin).
Qed.



Lemma loop_replaceT_XY_preserves_pivot_row {n}
  (q pr k : nat) (L : list (TType n)) :
  nth pr (loop_replaceT_XY n q pr k L) (defaultT_I n)
  =
  nth pr L (defaultT_I n).
Proof.
  revert L.
  induction k as [|k IH]; intro L.
  - cbn [loop_replaceT_XY]. reflexivity.
  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + exact (IH L).

    + destruct (nth q (snd (nth t L (defaultT_I n))) gI) eqn:Hg;
        try exact (IH L).
      * rewrite Nat.eqb_neq in Htp.
        rewrite IH.
        rewrite nth_switch_miss; auto.
      * rewrite Nat.eqb_neq in Htp.
        rewrite IH.
        rewrite nth_switch_miss; auto.
Qed.


Lemma loop_replaceT_Z_preserves_pivot_row {n}
  (q pr k : nat) (L : list (TType n)) :
  nth pr (loop_replaceT_Z n q pr k L) (defaultT_I n)
  =
  nth pr L (defaultT_I n).
Proof.
  revert L.
  induction k as [|k IH]; intro L.
  - cbn [loop_replaceT_Z]. reflexivity.
  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + exact (IH L).
    + destruct (nth q (snd (nth t L (defaultT_I n))) gI) eqn:Hg;
        try exact (IH L).
      * rewrite Nat.eqb_neq in Htp.
        rewrite IH.
        rewrite nth_switch_miss; auto.
Qed.



Lemma first_step_gives_FirstColInv {n}
  (q0 : nat) (L : list (TType n)) (QP1 : list (nat*nat)) (L1 : list (TType n)) :
  length L <> 0%nat ->
  WF_L L ->
  (q0 < n)%nat ->
  loop_j_return_QPL n q0 (length L) [] L [] = (QP1, L1) ->
  FirstColInv n q0 QP1 L1.
Proof.
  intros Hlen HWF Hq0 Hrun.

  pose (loop_j_return_QPL_classify_shape_with_XY_Z_noXY_aux
          q0 L Hlen
          (length L) [] QP1 L1) as H'.
  assert (temp: Lz_ok q0 L []) by constructor.
  specialize (H' temp Hrun).
  destruct H' as [res [Hshape [Hxy Hz]]].

  destruct res as [|pr|pr].
  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst QP1 L1.
    apply (InvNone n q0 [] L).
    unfold ColAllI.
    
    intros r Hr.

    pose (allI_on_suffix_if_returns_none_aux q0 L
                  (length L) [] [] L
                  Hrun eq_refl eq_refl eq_refl) as HallSuf.

    unfold allI_on_suffix in HallSuf.
    apply (HallSuf r).
    split; lia.

    unfold NoPair. intros pr Hin. cbn in Hin. contradiction.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst QP1 L1.
    assert (HpivXY_L : isXY (entry q0 (nth pr L (defaultT_I n))) = true) by (apply (Hxy pr eq_refl)).

    assert (HpivXY_L1 :
      isXY (entry q0 (nth pr (loop_replaceT_XY n q0 pr (length L) L) (defaultT_I n))) = true).
    { unfold entry.
      rewrite (loop_replaceT_XY_preserves_pivot_row q0 pr (length L) L).
      exact HpivXY_L.
    }

    apply (InvXY n q0 [(q0,pr)]
                 (loop_replaceT_XY n q0 pr (length L) L) pr).
    + exact HpivXY_L1.
    + unfold ColIZ_except.
      intros r Hr Hneq.
      eapply loop_replaceT_XY_clears_all_to_IZ; eauto.
      
      2: rewrite loop_replaceT_XY_length in Hr; auto.
      pose (loop_j_return_QPL_incl_QP_seq_0_length_L n q0 (length L) [] L [] Hlen) as H'.
      simpl in H'.
      assert (temp': incl [] (seq 0 (length L))) by (apply incl_nil_l).
      specialize (H' temp' temp').
      rewrite Hrun in H'.
      simpl in H'.
      unfold incl in H'.
      assert (temp'': In pr [pr]) by (left; auto).
      specialize (H' pr temp'').
      rewrite in_seq in H'.
      lia.
    + cbn. left. reflexivity.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQP HL]. subst QP1 L1.
    destruct (Hz pr eq_refl) as [HpivZ_L HnoXYsuf].

    assert (HpivZ_L1 :
      entry q0 (nth pr (loop_replaceT_Z n q0 pr (length L) L) (defaultT_I n)) = gZ).
    { unfold entry.
      rewrite (loop_replaceT_Z_preserves_pivot_row q0 pr (length L) L).
      exact HpivZ_L.
    }

    apply (InvZ n q0 [(q0,pr)]
                (loop_replaceT_Z n q0 pr (length L) L) pr).
    + exact HpivZ_L1.
    + pose (noXY_on_suffix_full_implies_noXY_except_pivot
                    q0 pr L HnoXYsuf) as HnoXY.
      unfold ColI_except.
      intros r Hr Hneq.
      eapply loop_replaceT_Z_clears_all_to_I_under_noXY; eauto.
      2: rewrite loop_replaceT_Z_length in Hr; auto.
      pose (loop_j_return_QPL_incl_QP_seq_0_length_L n q0 (length L) [] L [] Hlen) as H'.
      simpl in H'.
      assert (temp': incl [] (seq 0 (length L))) by (apply incl_nil_l).
      specialize (H' temp' temp').
      rewrite Hrun in H'.
      simpl in H'.
      unfold incl in H'.
      assert (temp'': In pr [pr]) by (left; auto).
      specialize (H' pr temp'').
      rewrite in_seq in H'.
      lia.
    + cbn. left. reflexivity.
Qed.

Lemma gMul_base_closed_XY_under_IZ (a b : Pauli) :
  isIZ a = true ->
  isXY b = true ->
  isXY (gMul_base a b) = true.
Proof.
  destruct a, b; cbn; try discriminate; reflexivity.
Qed.

Lemma entry_gMulT_IZ_XY_closed {n} (q0 : nat) (A B : TType n) :
  WF_T A -> WF_T B -> (q0 < n)%nat ->
  isIZ (entry q0 A) = true ->
  isXY (entry q0 B) = true ->
  isXY (entry q0 (gMulT A B)) = true.
Proof.
  intros HWA HWB Hq0 HA HB.
  rewrite (entry_gMulT A B q0); try assumption.
  eapply gMul_base_closed_XY_under_IZ; eauto.
Qed.


Lemma prNew_lt_length_from_shape {n}
  (qnext prNew j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  length L <> 0%nat ->
  incl Lz (seq 0 (length L)) ->
  incl (map snd QP) (seq 0 (length L)) ->
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  QP' = (qnext, prNew) :: QP ->
  (prNew < length L)%nat.
Proof.
  intros Hlen HLz HQP Hrun HQP'.
  assert (Hincl' : incl (map snd QP') (seq 0 (length L))).
  { pose (loop_j_return_QPL_incl_QP_seq_0_length_L) as H'.
    specialize (H' n qnext j QP L Lz Hlen HLz HQP).
    rewrite Hrun in H'.
    simpl in H'. auto.
  }
  assert (Hin : In prNew (map snd QP')).
  { subst QP'. cbn. left. reflexivity. }
  apply Hincl' in Hin.
  rewrite in_seq in Hin.
  lia.
Qed.

Lemma entry_gMulT_left_I_preserves {n} (q0 : nat) (A B : TType n) :
  WF_T A -> WF_T B -> (q0 < n)%nat ->
  entry q0 A = gI ->
  entry q0 (gMulT A B) = entry q0 B.
Proof.
  intros HWA HWB Hq0 HA.
  rewrite (entry_gMulT A B q0); try assumption.
  rewrite HA.
  destruct (entry q0 B); cbn; reflexivity.
Qed.

Lemma loop_replaceT_XY_preserves_pivotZ_at_pr0 {n}
  (q0 pr0 q pr k : nat) (L : list (TType n)) :
  WF_L L ->
  (q0 < n)%nat ->
  (k <= length L)%nat ->
  entry q0 (nth pr L (defaultT_I n)) = gI ->
  entry q0 (nth pr0 L (defaultT_I n)) = gZ ->
  entry q0 (nth pr0 (loop_replaceT_XY n q pr k L) (defaultT_I n)) = gZ.
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF Hq0 Hk HpivI Hp0Z.
  - cbn [loop_replaceT_XY]. exact Hp0Z.
  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).
    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).
        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT;
             eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.
        -- unfold Ls.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto; try lia.
        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              rewrite (entry_gMulT_left_I_preserves q0
                        (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)));
                try (eapply WF_T_nth_default; eauto);
                try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
             rewrite nth_switch_miss; auto; try lia.
      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).
        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT;
             eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.
        -- unfold Ls.
           rewrite Nat.eqb_neq in Htp.
           rewrite nth_switch_miss; auto; try lia.
        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              rewrite (entry_gMulT_left_I_preserves q0
                        (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)));
                try (eapply WF_T_nth_default; eauto);
                try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
             rewrite nth_switch_miss; auto; try lia.
Qed.

Lemma loop_replaceT_Z_preserves_pivotZ_at_pr0 {n}
  (q0 pr0 q pr k : nat) (L : list (TType n)) :
  WF_L L ->
  (q0 < n)%nat ->
  (k <= length L)%nat ->
  entry q0 (nth pr L (defaultT_I n)) = gI ->
  entry q0 (nth pr0 L (defaultT_I n)) = gZ ->
  entry q0 (nth pr0 (loop_replaceT_Z n q pr k L) (defaultT_I n)) = gZ.
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF Hq0 Hk HpivI Hp0Z.
  - cbn [loop_replaceT_Z]. exact Hp0Z.
  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).
    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).
        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT;
             eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.
        -- unfold Ls.
           apply Nat.eqb_neq in Htp.
           assert (Nat.eqb pr t = false) by (apply Nat.eqb_neq; lia).
           rewrite Nat.eqb_neq in H; auto; try lia.
           rewrite nth_switch_miss; auto; try lia.
        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              rewrite (entry_gMulT_left_I_preserves q0
                        (nth pr L (defaultT_I n)) (nth t L (defaultT_I n)));
                try (eapply WF_T_nth_default; eauto);
                try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
             rewrite nth_switch_miss; auto; try lia.
Qed.


Lemma loop_replaceT_XY_preserves_pivotXY_at_pr0 {n}
  (q0 pr0 q pr k : nat) (L : list (TType n)) :
  WF_L L ->
  (q0 < n)%nat ->
  (k <= length L)%nat ->
  isIZ (entry q0 (nth pr L (defaultT_I n))) = true ->
  isXY (entry q0 (nth pr0 L (defaultT_I n))) = true ->
  isXY (entry q0 (nth pr0 (loop_replaceT_XY n q pr k L) (defaultT_I n))) = true.
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF Hq0 Hk HpivIZ Hp0XY.
  - cbn [loop_replaceT_XY]. exact Hp0XY.

  - cbn [loop_replaceT_XY].
    set (t := (length L - S k)%nat).

    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.

    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).

        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.

        -- unfold Ls.
           apply Nat.eqb_neq in Htp.  (* t <> pr *)
           assert (Nat.eqb pr t = false) by (apply Nat.eqb_neq; lia).
           rewrite Nat.eqb_neq in H.
           rewrite nth_switch_miss; auto; try lia.

        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              eapply entry_gMulT_IZ_XY_closed; try (eapply WF_T_nth_default; eauto); try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
             rewrite nth_switch_miss; auto; try lia.

      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).

        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.

        -- unfold Ls.
           apply Nat.eqb_neq in Htp.
           assert (Nat.eqb pr t = false) by (apply Nat.eqb_neq; lia).
           rewrite Nat.eqb_neq in H.
           rewrite nth_switch_miss; auto; try lia.

        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              eapply entry_gMulT_IZ_XY_closed; try (eapply WF_T_nth_default; eauto); try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
             rewrite nth_switch_miss; auto; try lia.
Qed.


Lemma loop_replaceT_Z_preserves_pivotXY_at_pr0 {n}
  (q0 pr0 q pr k : nat) (L : list (TType n)) :
  WF_L L ->
  (q0 < n)%nat ->
  (k <= length L)%nat ->
  isIZ (entry q0 (nth pr L (defaultT_I n))) = true ->
  isXY (entry q0 (nth pr0 L (defaultT_I n))) = true ->
  isXY (entry q0 (nth pr0 (loop_replaceT_Z n q pr k L) (defaultT_I n))) = true.
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF Hq0 Hk HpivIZ Hp0XY.
  - cbn [loop_replaceT_Z]. exact Hp0XY.
  - cbn [loop_replaceT_Z].
    set (t := (length L - S k)%nat).
    destruct (Nat.eqb t pr) eqn:Htp.
    + eapply IH; eauto; lia.
    + remember (nth q (snd (nth t L (defaultT_I n))) gI) as g eqn:Hg.
      destruct g; try (eapply IH; eauto; lia).
      * set (x := gMulT (nth pr L (defaultT_I n)) (nth t L (defaultT_I n))).
        set (Ls := switch L x t).

        eapply (IH Ls).
        -- unfold Ls.
           eapply WF_switch; eauto.
           unfold x. eapply WF_gMulT; eapply WF_T_nth_default; eauto.
        -- exact Hq0.
        -- unfold Ls. rewrite switch_len. lia.

        -- unfold Ls.
           apply Nat.eqb_neq in Htp.
           assert (Nat.eqb pr t = false) by (apply Nat.eqb_neq; lia).
           rewrite Nat.eqb_neq in H.
           rewrite nth_switch_miss; auto; try lia.

        -- unfold Ls.
           destruct (Nat.eqb pr0 t) eqn:Hrt.
           ++ apply Nat.eqb_eq in Hrt; subst pr0.
              rewrite nth_switch_hit; auto; try lia.
              unfold x.
              eapply entry_gMulT_IZ_XY_closed; try (eapply WF_T_nth_default; eauto); try exact Hq0; auto.
           ++ rewrite Nat.eqb_neq in Hrt.
              rewrite nth_switch_miss; auto; try lia. 
Qed.


Lemma loop_j_return_QPL_preserves_FirstColInv {n}
  (q0 qnext j : nat)
  (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  qnext <> q0 ->
  WF_L (n:=n) L ->
  (q0 < n)%nat ->
  length L <> 0%nat ->
  incl Lz (seq 0 (length L)) ->
  incl (map snd QP) (seq 0 (length L)) ->
  Lz_notin_QP QP Lz ->
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  FirstColInv n q0 QP L ->
  FirstColInv n q0 QP' L'.
Proof.
  intros Hqneq HWF Hq0 Hlen HLz HQP HLzNotin Hrun Hinv.

  destruct (loop_j_return_QPL_classify_shape
              qnext j QP L Lz
              QP' L' Hrun)
    as [res Hshape].

  destruct res as [|prNew|prNew].

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQ HL]. subst QP' L'.
    exact Hinv.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQPxy HLxy]. subst QP' L'.

    inversion Hinv as
      [QP0 L0 HallI HnoPair
      |QP0 L0 pr0 HpivZ HI Hin_pair
      |QP0 L0 pr0 HpivXY HIZ Hin_pair];
    subst QP0 L0.

    + apply (InvNone n q0
               ((qnext,prNew)::QP)
               (loop_replaceT_XY n qnext prNew (length L) L)).
      * eapply loop_replaceT_XY_preserves_ColAllI; eauto; lia.
      * eapply (loop_j_return_QPL_preserves_NoPair q0 qnext j
                 QP L Lz (( (qnext,prNew)::QP)) (loop_replaceT_XY n qnext prNew (length L) L));
          eauto.
        
    + eapply (InvZ n q0
              ((qnext,prNew)::QP)
              (loop_replaceT_XY n qnext prNew (length L) L) pr0).
      * eapply loop_replaceT_XY_preserves_pivotZ_at_pr0; eauto.

        assert (HprNew_lt : (prNew < length L)%nat).
        {
          assert (Hincl' : incl (map snd ((qnext, prNew) :: QP)) (seq 0 (length L))).
          {
            pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                          n qnext j QP L Lz
                          Hlen HLz HQP) as Hincl_res.
            rewrite Hrun in Hincl_res.
            cbn in Hincl_res.
            exact Hincl_res.
          }

          assert (Hin_prNew : In prNew (map snd ((qnext, prNew) :: QP))).
          { cbn. left. reflexivity. }

          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl' in Hin_prNew; auto).
          apply in_seq in Hin_seq.
          lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair. simpl in Hin_pair.
          exact Hin_pair.
        }

        assert (HpivI : entry q0 (nth prNew L (defaultT_I n)) = gI).
        { apply HI; [exact HprNew_lt | exact Hneq]. }

        auto.

      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          assert (Hincl_res :
            incl (map snd ((qnext, prNew) :: QP)) (seq 0 (length L))).
          {
            pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                          n qnext j QP L Lz
                          Hlen HLz HQP) as Hincl.
            rewrite Hrun in Hincl.
            cbn in Hincl.
            exact Hincl.
          }
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew) :: QP))).
          { cbn. left. reflexivity. }
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl_res in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }
        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        assert (HpivRow_I : entry q0 (nth prNew L (defaultT_I n)) = gI).
        { apply HI; [exact HprNew_lt | exact Hneq]. }
        
        assert (HI' :
          ColI_except (n:=n) q0 pr0 (loop_replaceT_XY n qnext prNew (length L) L)).
        {
          eapply loop_replaceT_XY_preserves_ColI_except; eauto; lia.
        }

        auto.

      * cbn. right. exact Hin_pair.

    + eapply (InvXY n q0
              ((qnext,prNew)::QP)
              (loop_replaceT_XY n qnext prNew (length L) L) pr0).
      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          assert (Hincl_res :
            incl (map snd ((qnext, prNew) :: QP)) (seq 0 (length L))).
          {
            pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                          n qnext j QP L Lz
                          Hlen HLz HQP) as Hincl.
            rewrite Hrun in Hincl.
            cbn in Hincl.
            exact Hincl.
          }
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew) :: QP))).
          { cbn. left. reflexivity. }
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl_res in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        assert (HpivRow_IZ : isIZ (entry q0 (nth prNew L (defaultT_I n))) = true).
        { apply HIZ; [exact HprNew_lt | exact Hneq]. }

        assert (HpivXY' :
                 isXY (entry q0 (nth pr0 (loop_replaceT_XY n qnext prNew (length L) L) (defaultT_I n))) = true).
        { eapply loop_replaceT_XY_preserves_pivotXY_at_pr0; eauto; lia. }
        
        auto.

      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                        n qnext j QP L Lz
                        Hlen HLz HQP) as Hincl.
          rewrite Hrun in Hincl. cbn in Hincl.
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew)::QP))) by (cbn; left; reflexivity).
          assert (Hin_seq : In prNew (seq 0 (length L)))by (apply Hincl in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        assert (HpivRow_IZ : isIZ (entry q0 (nth prNew L (defaultT_I n))) = true).
        { apply HIZ; [exact HprNew_lt | exact Hneq]. }
        
        eapply loop_replaceT_XY_preserves_ColIZ_except; eauto.
        
      * cbn. right. exact Hin_pair.

  - cbn [JRet_shape_ok] in Hshape.
    destruct Hshape as [HQPz HLz']. subst QP' L'.

    inversion Hinv as
      [QP0 L0 HallI HnoPair
      |QP0 L0 pr0 HpivZ HI Hin_pair
      |QP0 L0 pr0 HpivXY HIZ Hin_pair];
    subst QP0 L0.

    + apply (InvNone n q0
               ((qnext,prNew)::QP)
               (loop_replaceT_Z n qnext prNew (length L) L)).
      * eapply loop_replaceT_Z_preserves_ColAllI; eauto; lia.
      * eapply (loop_j_return_QPL_preserves_NoPair q0 qnext j
                 QP L Lz (((qnext,prNew)::QP)) (loop_replaceT_Z n qnext prNew (length L) L));
          eauto.

    + eapply (InvZ n q0
              ((qnext,prNew)::QP)
              (loop_replaceT_Z n qnext prNew (length L) L) pr0).
      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                        n qnext j QP L Lz
                        Hlen HLz HQP) as Hincl.
          rewrite Hrun in Hincl. cbn in Hincl.
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew)::QP))) by (cbn; left; reflexivity).
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        assert (HpivRow_I : entry q0 (nth prNew L (defaultT_I n)) = gI).
        { apply HI; [exact HprNew_lt | exact Hneq]. }

        eapply loop_replaceT_Z_preserves_pivotZ_at_pr0; eauto.

      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                        n qnext j QP L Lz
                        Hlen HLz HQP) as Hincl.
          rewrite Hrun in Hincl. cbn in Hincl.
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew)::QP))) by (cbn; left; reflexivity).
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        eapply loop_replaceT_Z_preserves_ColI_except; eauto.

      * cbn. right. exact Hin_pair.

    + eapply (InvXY n q0
              ((qnext,prNew)::QP)
              (loop_replaceT_Z n qnext prNew (length L) L) pr0).
      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                        n qnext j QP L Lz
                        Hlen HLz HQP) as Hincl.
          rewrite Hrun in Hincl. cbn in Hincl.
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew)::QP))) by (cbn; left; reflexivity).
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        eapply loop_replaceT_Z_preserves_pivotXY_at_pr0; eauto.
      * assert (HprNew_lt : (prNew < length L)%nat).
        {
          pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                        n qnext j QP L Lz
                        Hlen HLz HQP) as Hincl.
          rewrite Hrun in Hincl. cbn in Hincl.
          assert (Hin_prNew : In prNew (map snd ((qnext, prNew)::QP))) by (cbn; left; reflexivity).
          assert (Hin_seq : In prNew (seq 0 (length L))) by (apply Hincl in Hin_prNew; auto).
          apply in_seq in Hin_seq. lia.
        }

        assert (Hneq : prNew <> pr0).
        {
          intro E; subst prNew.
          assert (Hnotin : ~ In pr0 (map snd QP)).
          { eapply loop_j_return_QPL_new_pivot_not_in_old; eauto. }
          apply Hnotin.
          apply In_map_snd_of_In in Hin_pair.
          exact Hin_pair.
        }

        eapply loop_replaceT_Z_preserves_ColIZ_except; eauto.

      * cbn. right. exact Hin_pair.
Qed.

Lemma WF_loop_replaceT_XY {n} (q i j k : nat) (L : list (TType n)) :
  WF_L (n:=n) L ->
  WF_L (n:=n) (loop_replaceT_XY n i j k L).
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF.
  - cbn [loop_replaceT_XY]. exact HWF.
  - cbn [loop_replaceT_XY].
    destruct (Nat.eqb (length L - S k) j) eqn:Heq.
    + exact (IH L HWF).
    + destruct (nth i (snd (nth (length L - S k) L (defaultT_I n))) gI) eqn:Hg;
      try exact (IH L HWF).
      all: apply IH.
      all: eapply WF_switch; eauto.
      all: eapply WF_gMulT;
        eapply WF_T_nth_default; eauto.
Qed.

Lemma WF_loop_replaceT_Z {n} (q i j k : nat) (L : list (TType n)) :
  WF_L (n:=n) L ->
  WF_L (n:=n) (loop_replaceT_Z n i j k L).
Proof.
  revert L.
  induction k as [|k IH]; intros L HWF.
  - cbn [loop_replaceT_Z]. exact HWF.
  - cbn [loop_replaceT_Z].
    destruct (Nat.eqb (length L - S k) j) eqn:Heq.
    + exact (IH L HWF).
    + destruct (nth i (snd (nth (length L - S k) L (defaultT_I n))) gI) eqn:Hg;
      try exact (IH L HWF).
      apply IH.
      eapply WF_switch; eauto.
      eapply WF_gMulT;
        eapply WF_T_nth_default; eauto.
Qed.

Lemma WF_loop_j_return_QPL {n} (i j : nat)
  (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat) :
  WF_L (n:=n) L ->
  WF_L (n:=n) (snd (loop_j_return_QPL n i j QP L Lz)).
Proof.
  revert QP L Lz.
  induction j as [|j IH]; intros QP L Lz HWF.
  - cbn [loop_j_return_QPL].
    destruct (rev Lz) as [|h tl] eqn:Hrev.
    + exact HWF.
    + eapply WF_loop_replaceT_Z; eauto.
  - cbn [loop_j_return_QPL].
    destruct (existsb (fun qp => Nat.eqb (snd qp) (length L - S j)) QP) eqn:Hused.
    + exact (IH QP L Lz HWF).
    + destruct (nth i (snd (nth (length L - S j) L (defaultT_I n))) gI) eqn:Hg.
      * exact (IH QP L Lz HWF).
      * eapply WF_loop_replaceT_XY; eauto.
      * eapply WF_loop_replaceT_XY; eauto.
      * exact (IH QP L ((length L - S j)%nat :: Lz) HWF).
Qed.

Lemma WF_loop_normalization (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) :
  WF_L (n:=n) L ->
  WF_L (n:=n) (snd (loop_normalization lq n i QP L)).
Proof. intros H.
  gen L QP. induction i; intros.
  - simpl. auto.
  - simpl. destruct (loop_j_return_QPL n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
    eapply IHi.
    pose (WF_loop_j_return_QPL (nth (n - S i) lq 0%nat) (length L) QP L [] H) as e.
    rewrite E in e. auto.
Qed.

Lemma WF_loop_normalization_final (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) :
  length L <> 0%nat ->
  NoDup (map snd QP) ->
  incl (map snd QP) (seq 0 (length L)) ->
  WF_L (n:=n) L ->
  WF_L (n:=n) (map snd (loop_normalization_final lq n i QP L)).
Proof. intros H'' H''' H' H.
  unfold loop_normalization_final.
  destruct (loop_normalization lq n i QP L) eqn:E.
  rewrite map_app. rewrite map_map. simpl. rewrite map_rev.
  apply (WF_loop_normalization lq n i QP L) in H.
  rewrite E in H. simpl in H.
  unfold WF_L in *.
  rewrite Forall_app.
  split.
  - apply Forall_rev.
    rewrite Forall_map.
    rewrite Forall_forall in *.
    intros x H0.
    apply H.
    apply nth_In.
    rewrite <- (loop_normalization_fuel_saturated i (length L) (length L) lq n i QP L) in E; try lia.
    pose (loop_normalization_fuel_incl_QP_seq_0_length_L i (length L) (length L) lq n i QP L H'' H') as e.
    rewrite E in e. simpl in e.
    pose (loop_normalization_fuel_length i (length L) (length L) lq n i QP L H'' H''' H') as w.
    rewrite E in w. simpl in w. rewrite w.
    assert (In (snd x) (map snd l)).
    { apply In_map_snd_of_In. auto. }
    apply e in H1. rewrite in_seq in H1. lia.
  - rewrite map_snd_combine.
    + unfold lexicographic. apply Forall_rev.
      pose (TOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultT_I n))
          (filter
             (fun a : nat =>
                ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                    (map snd l)) (seq 0 (length l0))))) as e.
      rewrite Forall_forall in *.
      intros x H0.
      rewrite <- (Permutation_in' (eq_refl x) e) in H0.
      rewrite in_map_iff in H0.
      destruct H0. destruct H0.
      apply incl_filter in H1.
      apply H. rewrite <- H0.
      apply nth_In. rewrite in_seq in H1. lia.
    + unfold lexicographic. rewrite rev_length.
      rewrite repeat_length.
      pose (TOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultT_I n))
          (filter
             (fun a : nat =>
                ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                    (map snd l)) (seq 0 (length l0))))) as e.
      apply Permutation_length in e. rewrite <- e.
      rewrite map_length. lia.
Qed.

Lemma normalize_preserves_WF_L {n : nat} (q : nat) (lt : list (TType n)):
  WF_L lt -> WF_L (normalize q lt).
Proof. intros H.
  bdestruct (length lt =? 0)%nat.
  - rewrite length_zero_iff_nil in H0. subst.
    rewrite normalize_nil. auto.
  - unfold normalize, pivots_normalize.
    apply WF_loop_normalization_final; auto; simpl.
    + apply NoDup_nil.
    + unfold incl. intros. inversion H1.
Qed.

Lemma existsb_map' {A B} (f : B -> bool) (g : A -> B) (l : list A) :
  existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
  induction l as [|a l IH]; cbn; auto.
  rewrite IH; auto.
Qed.

Lemma existsb_ext' {A} (f g : A -> bool) (l : list A) :
  (forall x, f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intro Hfg.
  induction l as [|a l IH]; cbn; auto.
  now rewrite Hfg, IH.
Qed.

Lemma eq_dec_eqb (a t : nat) :
  (if Nat.eq_dec a t then true else false) = Nat.eqb a t.
Proof.
  destruct (Nat.eq_dec a t) as [->|Hneq].
  - now rewrite Nat.eqb_refl.
  - apply Nat.eqb_neq in Hneq. symmetry. exact Hneq.
Qed.

Lemma loop_j_return_QPL_allI_returns_same_aux {n}
  (q0 : nat) (QP : list (nat*nat)) (L : list (TType n)) :
  (q0 < n)%nat ->
  ColAllI (n:=n) q0 L ->
  forall j,
    (j <= length L)%nat ->
    loop_j_return_QPL n q0 j QP L [] = (QP, L).
Proof.
  intros Hq0 Hall.
  induction j as [|j IH]; intro Hjle.
  - cbn [loop_j_return_QPL].
    reflexivity.

  - cbn [loop_j_return_QPL].
    set (t := (length L - S j)%nat).

    destruct (existsb
      (fun p : nat => if Nat.eq_dec p t then true else false)
      (map snd QP)) eqn:Hex.
    + assert (Hex' : existsb (fun qp : nat * nat => Nat.eqb (snd qp) t) QP = true).
      {
        rewrite (existsb_map' (fun p : nat => if Nat.eq_dec p t then true else false) snd QP) in Hex.
        pose proof (existsb_ext'
                      (fun qp : nat * nat => if Nat.eq_dec (snd qp) t then true else false)
                      (fun qp : nat * nat => Nat.eqb (snd qp) t)
                      QP
                      (fun qp => eq_dec_eqb (snd qp) t)) as Hext.
        rewrite Hext in Hex.
        exact Hex.
      }

      rewrite Hex'.
      eapply IH; lia.

    + assert (Htlt : (t < length L)%nat).
      { subst t. lia. }

      assert (HentryI : entry q0 (nth t L (defaultT_I n)) = gI).
      { apply Hall. exact Htlt. }

      unfold entry in HentryI.

      rewrite HentryI.
      destruct (existsb (fun qp : nat * nat => (snd qp =? t)%nat) QP); eapply IH; lia.
Qed.

Lemma loop_j_return_QPL_allI_returns_same {n}
  (q0 : nat) (QP : list (nat*nat)) (L : list (TType n)) :
  (q0 < n)%nat ->
  ColAllI (n:=n) q0 L ->
  loop_j_return_QPL n q0 (length L) QP L [] = (QP, L).
Proof.
  intros Hq0 Hall.
  eapply (loop_j_return_QPL_allI_returns_same_aux q0 QP L); eauto.
Qed. 


Lemma NoDup_nth_not_in_firstn {A} (d : A) (l : list A) (k : nat) :
  NoDup l ->
  (k < length l)%nat ->
  ~ In (nth k l d) (firstn k l).
Proof.
  revert l.
  induction k as [|k IH]; intros l Hnd Hk.
  - cbn. intro Hin. contradiction.
  - destruct l as [|x xs]; cbn in *; try lia.
    inversion Hnd as [|? ? Hnotin Hnd_xs]; subst.
    intro Hin.
    cbn in Hin. destruct Hin as [Hin|Hin].
    + apply Hnotin.
      subst.
      apply nth_In. lia.
    + eapply IH; eauto; lia.
Qed.

Lemma nth_pos_neq_nth0_nat (lq : list nat) (k : nat) :
  NoDup lq ->
  (1 <= k)%nat ->
  (k < length lq)%nat ->
  nth k lq 0%nat <> nth 0 lq 0%nat.
Proof.
  intros Hnd Hk1 Hklt Heq.
  pose proof (NoDup_nth_not_in_firstn 0%nat lq k Hnd Hklt) as Hnotin.
  assert (Hin0 : In (nth 0 lq 0%nat) (firstn k lq)).
  { destruct lq as [|h tl]; cbn in *; try lia.
    destruct k; [lia|]. cbn. left. reflexivity. }
  apply Hnotin.
  now rewrite Heq.
Qed.



Lemma loop_normalization_preserves_FirstColInv_after_first {n}
  (lq : list nat) (q0 : nat) :
  NoDup lq ->
  length lq = n ->
  q0 = nth 0 lq 0%nat ->
  forall (i : nat) (QP : list (nat*nat)) (L : list (TType n)),
    (i <= n - 1)%nat ->
    WF_L (n:=n) L ->
    (q0 < n)%nat ->
    length L <> 0%nat ->
    incl (map snd QP) (seq 0 (length L)) ->
    FirstColInv n q0 QP L ->
    FirstColInv n q0 (fst (loop_normalization lq n i QP L))
                     (snd (loop_normalization lq n i QP L)).
Proof.
  intros Hnd_lq Hlq_len Hq0def.
  induction i as [|i IH]; intros QP L Hi_le HWF Hq0 Hlen HQP_in Hinv.
  - cbn [loop_normalization]. exact Hinv.
  - cbn [loop_normalization].
    set (qnext := nth (n - S i)%nat lq 0%nat).

    assert (Hqneq : qnext <> q0).
    { unfold qnext.
      assert (Hk1 : (1 <= (n - S i))%nat) by lia.
      assert (Hklt : ((n - S i) < length lq)%nat).
      { rewrite Hlq_len. lia. }
      rewrite Hq0def.
      apply (nth_pos_neq_nth0_nat lq (n - S i) Hnd_lq Hk1 Hklt).
    }

    destruct (loop_j_return_QPL n qnext (length L) QP L [])
      as [QP1 L1] eqn:Hstep.
    cbn.

    assert (Hinv1 : FirstColInv n q0 QP1 L1).
    { refine (loop_j_return_QPL_preserves_FirstColInv
                q0 qnext (length L)
                QP L []
                QP1 L1
                _ _ _ _ _ _ _ _ _).
      - exact Hqneq.
      - exact HWF.
      - exact Hq0.
      - exact Hlen.
      - apply incl_nil_l.
      - exact HQP_in.
      - unfold Lz_notin_QP. constructor.
      - exact Hstep.
      - exact Hinv.
    }

    assert (HWF1 : WF_L (n:=n) L1).
    { pose (WF_loop_j_return_QPL qnext (length L) QP L [] HWF) as e.
      rewrite Hstep in e. simpl in e. auto. }

    assert (Hlen1 : length L1 <> 0%nat).
    { rewrite <- (loop_j_return_QPL_length n qnext (length L) QP L []) in Hlen.
      rewrite Hstep in Hlen. simpl in Hlen. auto. }

    assert (HQP_in1 : incl (map snd QP1) (seq 0 (length L1))).
    { assert (Hlen_eq : length L1 = length L).
      { symmetry.
        rewrite <- (loop_j_return_QPL_length n qnext (length L) QP L []).
        rewrite Hstep. auto.
      }
      rewrite Hlen_eq.
      pose proof (loop_j_return_QPL_incl_QP_seq_0_length_L
                    n qnext (length L) QP L []
                    Hlen (incl_nil_l _) HQP_in) as Hincl.
      rewrite Hstep in Hincl. cbn in Hincl.
      exact Hincl.
    }

    apply (IH QP1 L1); try assumption.
    lia.
Qed.


Definition pivot_term {n} (q0 : nat) (lqt : list ((option nat) * TType n)) : option (TType n) :=
  match find (fun qt =>
                match fst qt with
                | Some q => Nat.eqb q0 q
                | None => false
                end) lqt with
  | None => None
  | Some qt => Some (snd qt)
  end.

Lemma pivot_term_Some_in_terms {n}
  (q0 : nat) (lqt : list ((option nat) * TType n)) (tp : TType n) :
  pivot_term (n:=n) q0 lqt = Some tp ->
  In tp (map snd lqt).
Proof.
  unfold pivot_term.
  intros Hpt.
  destruct (find
    (fun qt : option nat * TType n =>
       match fst qt with
       | Some q => Nat.eqb q0 q
       | None => false
       end) lqt) eqn:E; try discriminate.
  inversion Hpt; subst tp.
  apply find_some in E.
  destruct E as [Hin _].
  apply In_map_snd_of_In. exact Hin.
Qed.


Lemma ColI_except_pivot_unique {n}
  (q0 pr0 idx : nat) (L : list (TType n)) :
  entry q0 (nth pr0 L (defaultT_I n)) = gZ ->
  ColI_except (n:=n) q0 pr0 L ->
  (idx < length L)%nat ->
  entry q0 (nth idx L (defaultT_I n)) = gZ ->
  idx = pr0.
Proof.
  intros HpivZ Hcol Hidx Hz.
  destruct (Nat.eq_dec idx pr0) as [->|Hneq]; auto.
  pose proof (Hcol idx Hidx Hneq) as HI.
  rewrite Hz in HI. discriminate.
Qed.


Lemma isIZ_implies_notXY (p : Pauli) :
  isIZ p = true -> isXY p = false.
Proof. destruct p; cbn; intros H; try discriminate; reflexivity. Qed.

Lemma ColIZ_except_pivot_unique {n}
  (q0 pr0 idx : nat) (L : list (TType n)) :
  isXY (entry q0 (nth pr0 L (defaultT_I n))) = true ->
  ColIZ_except (n:=n) q0 pr0 L ->
  (idx < length L)%nat ->
  isXY (entry q0 (nth idx L (defaultT_I n))) = true ->
  idx = pr0.
Proof.
  intros HpivXY Hcol Hidx Hxy.
  destruct (Nat.eq_dec idx pr0) as [->|Hneq]; auto.
  pose proof (Hcol idx Hidx Hneq) as HIZ.
  pose proof (isIZ_implies_notXY _ HIZ) as HnotXY.
  rewrite Hxy in HnotXY. discriminate.
Qed.

Lemma pivot_term_None_if_no_fst {n}
  (q0 : nat) (lqt : list ((option nat) * TType n)) :
  (forall qt, In qt lqt -> fst qt = Some q0 -> False) ->
  pivot_term (n:=n) q0 lqt = None.
Proof.
  intros H. 
  unfold pivot_term.
  destruct (find
        (fun qt : option nat * TType n =>
           match fst qt with
           | Some q => (q0 =? q)%nat
           | None => false
           end) lqt) eqn:E; auto.
  apply find_some in E.
  destruct E.
  specialize (H p H0).
  destruct (fst p) eqn:E; try discriminate.
  rewrite Nat.eqb_eq in H1.
  symmetry in H1.
  subst.
  assert (Some q0 = Some q0) by reflexivity.
  specialize (H H1).
  contradiction.
Qed.

Definition FirstQubitNormalized_out {n}
  (q0 : nat) (lqt : list ((option nat) * TType n)) : Prop :=
  match pivot_search (n:=n) lqt q0, pivot_term (n:=n) q0 lqt with
  | gI, None =>
      forall t, In t (map snd lqt) -> entry q0 t = gI
  | gZ, Some tp =>
      forall t, In t (map snd lqt) -> t <> tp -> entry q0 t = gI
  | gX, Some tp =>
      forall t, In t (map snd lqt) -> t <> tp -> isIZ (entry q0 t) = true
  | gY, Some tp =>
      forall t, In t (map snd lqt) -> t <> tp -> isIZ (entry q0 t) = true
  | _, _ => False
  end.



Lemma pivot_search_of_pivot_term_None {n}
  (lqt : list ((option nat) * TType n)) (q0 : nat) :
  pivot_term (n:=n) q0 lqt = None ->
  pivot_search (n:=n) lqt q0 = gI.
Proof.
  unfold pivot_term, pivot_search.
  destruct (find
              (fun qt =>
                 match fst qt with
                 | Some q => Nat.eqb q0 q
                 | None => false
                 end) lqt) as [qt|] eqn:Hf.
  - intro Hnone. cbn in Hnone. discriminate.
  - intro. cbn. reflexivity.
Qed.

Lemma pivot_search_of_pivot_term_Some {n}
  (lqt : list ((option nat) * TType n)) (q0 : nat) (tp : TType n) :
  pivot_term (n:=n) q0 lqt = Some tp ->
  pivot_search (n:=n) lqt q0 = entry q0 tp.
Proof.
  unfold pivot_term, pivot_search, entry.
  destruct (find
              (fun qt =>
                 match fst qt with
                 | Some q => Nat.eqb q0 q
                 | None => false
                 end) lqt) as [qt|] eqn:Hf.
  - intro Hsome.
    cbn in Hsome.
    inversion Hsome; subst tp.
    reflexivity.
  - intro Hsome. cbn in Hsome. discriminate.
Qed.

Lemma pivotBlock_contains_pair {n}
  (q0 pr0 : nat) (QPf : list (nat*nat)) (Lf : list (TType n)) :
  In (q0, pr0) QPf ->
  In (Some q0, nth pr0 Lf (defaultT_I n))
     (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)).
Proof.
  intro Hin.
  apply in_map_iff.
  exists (q0, pr0).
  split; [cbn; reflexivity|].
  apply in_rev.
  rewrite rev_involutive.
  exact Hin.
Qed.

Lemma tailBlock_has_no_Some {n}
  (l : list (TType n)) (k : nat) (q0 : nat) (tp : TType n) :
  ~ In (Some q0, tp) (combine (repeat None k) l).
Proof.
  revert l.
  induction k as [|k IH]; intros l Hin.
  - cbn in Hin. contradiction.
  - destruct l as [|a tl].
    + cbn in Hin. contradiction.
    + cbn in Hin.
      destruct Hin as [Hin|Hin].
      * inversion Hin.
      * eapply IH. exact Hin.
Qed.

Lemma tail_no_Some {n}
  (q0 : nat) (tail : list ((option nat) * TType n)) :
  (forall qt, In qt tail -> fst qt = None) ->
  pivot_term (n:=n) q0 tail = None.
Proof.
  intro Hfst.
  unfold pivot_term.
  destruct (find
    (fun qt : option nat * TType n =>
       match fst qt with
       | Some q => Nat.eqb q0 q
       | None => false
       end) tail) as [qt|] eqn:Hf; auto.
  exfalso.
  apply find_some in Hf.
  destruct Hf as [Hin Hpred].
  specialize (Hfst qt Hin). cbn in Hpred.
  rewrite Hfst in Hpred. discriminate.
Qed.

Lemma pivot_term_Some_if_In_Some {n}
  (q0 : nat) (lqt : list ((option nat) * TType n)) :
  (exists tp, In (Some q0, tp) lqt) ->
  exists tp, pivot_term (n:=n) q0 lqt = Some tp.
Proof.
  intros [tp Hin].
  unfold pivot_term.
  destruct (find
    (fun qt : option nat * TType n =>
       match fst qt with
       | Some q => Nat.eqb q0 q
       | None => false
       end) lqt) as [qt|] eqn:Hf.
  - exists (snd qt). reflexivity.
  - exfalso.
    apply (find_none _ _ Hf) in Hin.
    cbn in Hin. rewrite Nat.eqb_refl in Hin. discriminate.
Qed.



Lemma In_combine_repeatNone_fst_None {A} (k : nat) (ys : list A) (oq : option nat) (t : A) :
  In (oq, t) (combine (repeat (@None nat) k) ys) ->
  oq = None.
Proof.
  revert ys.
  induction k as [|k IH]; intros ys Hin.
  - cbn in Hin. contradiction.
  - destruct ys as [|y ys].
    + cbn in Hin. contradiction.
    + cbn in Hin.
      destruct Hin as [Hin | Hin].
      * inversion Hin. reflexivity.
      * eapply IH. exact Hin.
Qed.

Lemma tailBlock_fst_None {n}
  (noP : list nat) (L0 : list (TType n)) :
  forall qt,
    In qt (combine (repeat (@None nat) (length noP))
                   (lexicographic (map (fun p => nth p L0 (defaultT_I n)) noP))) ->
    fst qt = None.
Proof.
  intros [oq t] Hin. cbn.
  eapply In_combine_repeatNone_fst_None.
  exact Hin.
Qed.

Lemma pivot_term_Some_implies_from_QP {n}
  (q0 : nat) (QP0 : list (nat*nat)) (L0 : list (TType n)) (noP : list nat) (tp : TType n) :
  pivot_term (n:=n) q0
    (map (fun qp => (Some (fst qp), nth (snd qp) L0 (defaultT_I n))) (rev QP0)
     ++ combine (repeat None (length noP))
          (lexicographic (map (fun p => nth p L0 (defaultT_I n)) noP)))
  = Some tp ->
  exists prSel,
    In (q0, prSel) QP0 /\
    tp = nth prSel L0 (defaultT_I n).
Proof.
  intro Hpt.
  unfold pivot_term in Hpt.
  destruct (find _ _) as [qt|] eqn:Hf; try discriminate.
  inversion Hpt; subst tp.
  apply find_some in Hf.
  destruct Hf as [Hinqt Hpred].

  apply in_app_iff in Hinqt.
  destruct Hinqt as [HinPiv | HinTail].

  - apply in_map_iff in HinPiv.
    destruct HinPiv as [qp [Heq HinRev]].
    subst qt.
    cbn in Hpred.
    apply Nat.eqb_eq in Hpred.
    destruct qp as [q prSel]. cbn in *. subst q.
    exists prSel.
    split.
    + apply in_rev in HinRev. exact HinRev.
    + reflexivity.

  - exfalso.
    destruct qt as [oq t].
    specialize (tailBlock_fst_None (n:=n) noP L0 (oq, t) HinTail) as Hfst.
    cbn in Hpred.
    simpl in Hfst.
    rewrite Hfst in Hpred. discriminate.
Qed.


Lemma QP_unique_fst (QP : list (nat*nat)) :
  NoDup (map fst QP) ->
  forall q0 pr1 pr2,
    In (q0, pr1) QP ->
    In (q0, pr2) QP ->
    pr1 = pr2.
Proof.
  intros Hnd q0 pr1 pr2 Hin1 Hin2.

  assert (Hf1 : In q0 (map fst QP)).
  { apply (in_map fst) in Hin1. exact Hin1. }

  assert (Hf2 : In q0 (map fst QP)).
  { apply (in_map fst) in Hin2. exact Hin2. }

  gen q0 pr1 pr2 Hin1 Hin2.
  induction QP as [|[q pr] tl IH]; intros q0 pr1 pr2 Hin1 Hin2.
  - contradiction.
  - cbn in Hnd.
    inversion Hnd as [| ? ? Hnotin Hnd_tl]; subst.
    cbn in Hin1, Hin2.
    destruct Hin1 as [Hin1|Hin1]; destruct Hin2 as [Hin2|Hin2].
    + intros. reflexivity.
    + intros Hin1 Hin0.
      inversion Hin1; inversion Hin0; subst.
      * inversion H; subst.
        inversion H0.
      * inversion H; subst.
        apply In_map_fst_of_In in H0.
        simpl in H0.
        contradiction.
      * inversion H0; subst.
        apply In_map_fst_of_In in H.
        simpl in H.
        contradiction.
      * eapply IH; eauto.
        all: apply In_map_fst_of_In in H0; auto.
    + intros Hin0 Hin2.
      inversion Hin0; inversion Hin2; subst.
      * inversion H; subst.
        inversion H0.
      * inversion H; subst.
        apply In_map_fst_of_In in H0.
        simpl in H0.
        contradiction.
      * inversion H0; subst.
        apply In_map_fst_of_In in H.
        simpl in H.
        contradiction.
      * eapply IH; eauto.
        all: apply In_map_fst_of_In in H0; auto.
    + intros Hin0 Hin3.
      inversion Hin0; inversion Hin3; subst.
      * inversion H; subst.
        inversion H0.
        auto.
      * inversion H; subst.
        apply In_map_fst_of_In in H0.
        simpl in H0.
        contradiction.
      * inversion H0; subst.
        apply In_map_fst_of_In in H.
        simpl in H.
        contradiction.
      * eapply IH; eauto.
        all: apply In_map_fst_of_In in H0; auto.
Qed.


Lemma pivot_term_eq_nth_pr0_from_inv {n}
  (q0 pr0 : nat) (QPf : list (nat*nat)) (Lf : list (TType n))
  (noP : list nat) (tp : TType n) :
  NoDup (map fst QPf) ->
  In (q0, pr0) QPf ->
  pivot_term (n:=n) q0
    (map (fun qp => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
     ++ combine (repeat None (length noP))
          (lexicographic (map (fun p => nth p Lf (defaultT_I n)) noP)))
  = Some tp ->
  tp = nth pr0 Lf (defaultT_I n).
Proof.
  intros Hnodup Hinpair Hpt.
  destruct (pivot_term_Some_implies_from_QP (n:=n) q0 QPf Lf noP tp Hpt)
    as [prSel [HinSel ->]].
  f_equal.
  eapply QP_unique_fst; eauto.
Qed.


Lemma map_fst_loop_j_return_QPL_shape {n}
  (qnext j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  map fst QP' = map fst QP \/ map fst QP' = qnext :: map fst QP.
Proof.
  intro Hrun.
  destruct (loop_j_return_QPL_classify_shape
              qnext j QP L Lz
              QP' L' Hrun)
    as [res Hshape].
  destruct res as [|prNew|prNew];
    cbn [JRet_shape_ok] in Hshape;
    destruct Hshape as [HQ _];
    subst QP'.
  - left. reflexivity.
  - right. cbn. reflexivity.
  - right. cbn. reflexivity.
Qed.



Definition FstInv {n} (lq : list nat) (i : nat) (QP : list (nat*nat)) : Prop :=
  incl (map fst QP) (firstn (n - i) lq) /\ NoDup (map fst QP).


Lemma In_firstn_mono {A} (x : A) (l : list A) (a b : nat) :
  (a <= b)%nat ->
  In x (firstn a l) ->
  In x (firstn b l).
Proof.
  revert l a b.
  induction l as [|h tl IH]; intros a b Hab Hin.
  - rewrite firstn_nil in *; auto.
  - destruct a as [|a']; destruct b as [|b'].
    + cbn in Hin. contradiction.
    + cbn in Hin. contradiction.
    + lia.
    + cbn in Hin.
      cbn.
      destruct Hin as [Hin|Hin].
      * left. exact Hin.
      * right. eapply IH. 2: eauto. lia.
Qed.

Lemma nth_in_firstn_S {A} (d : A) (l : list A) (k : nat) :
  (k < length l)%nat ->
  In (nth k l d) (firstn (S k) l).
Proof.
  revert l.
  induction k as [|k IH]; intro l; destruct l as [|h tl]; intro Hk; cbn in *.
  - lia.
  - cbn. left. reflexivity.
  - lia.
  - cbn.
    right.
    apply IH.
    lia.
Qed.

Lemma sub_succ_le (n i : nat) : (n - S i <= n - i)%nat.
Proof. lia. Qed.

Lemma succ_sub_succ_eq (n i : nat) :
  (i < n)%nat ->
  S (n - S i) = (n - i)%nat.
Proof. intros. lia. Qed.

Lemma succ_sub_succ_le (n i : nat) :
  (i < n)%nat ->
  (S (n - S i)%nat <= n - i)%nat.
Proof. intros. lia. Qed.

Lemma sub_S_lt_self (n i : nat) :
  (n > 0)%nat ->
  (n - S i < n)%nat.
Proof. intros. lia. Qed.


Lemma FstInv_step {n}
  (lq : list nat) (i : nat)
  (QP : list (nat*nat)) (L : list (TType n))
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  NoDup lq ->
  length lq = n ->
  (i < n)%nat ->
  FstInv (n:=n) lq (S i) QP ->
  loop_j_return_QPL n (nth (n - S i) lq 0%nat) (length L) QP L [] = (QP', L') ->
  FstInv (n:=n) lq i QP'.
Proof.
  intros Hnd_lq Hlqlen Hi [Hincl Hnd_fst] Hrun.
  unfold FstInv in *.

  set (qnext := nth (n - S i) lq 0%nat).

  destruct (map_fst_loop_j_return_QPL_shape (n:=n) qnext (length L) QP L [] QP' L' Hrun)
    as [Hsame | Hcons].

  - split.
    + rewrite Hsame.

      unfold incl. intros x Hin_x.
      eapply In_firstn_mono; try eassumption.
      * apply sub_succ_le.
      * apply Hincl in Hin_x. auto.
        
    + rewrite Hsame. exact Hnd_fst.

  - split.
    + rewrite Hcons.
      unfold incl. intros x Hx.
      cbn in Hx. destruct Hx.
      * assert (Hklt : (n - S i < length lq)%nat).
        { rewrite Hlqlen.
          apply sub_S_lt_self. lia.
        }

        assert (Hin_small : In (nth (n - S i) lq 0%nat) (firstn (S (n - S i)) lq)).
        { eapply nth_in_firstn_S; eauto. }

        eapply In_firstn_mono; try eassumption.
        -- apply succ_sub_succ_le; auto.
        -- subst x. subst qnext. auto. 
      * assert (Hin_pref_small : In x (firstn (n - S i) lq)).
        { apply Hincl. auto. }
        eapply In_firstn_mono; try eassumption; lia.
    + rewrite Hcons.
      constructor.
      * subst qnext.
        intro Hin_qnext.
        assert (Hin_pref : In (nth (n - S i) lq 0%nat) (firstn (n - S i) lq)).
        { apply Hincl. exact Hin_qnext. }
        assert (Hidx_lt : ((n - S i) < length lq)%nat).
        { rewrite Hlqlen. lia. }
        eapply (NoDup_nth_not_in_firstn 0%nat lq (n - S i)); eauto.
      * exact Hnd_fst.
Qed.


Lemma loop_normalization_FstInv {n}
  (lq : list nat) :
  length lq = n ->
  NoDup lq ->
  forall i (QP : list (nat*nat)) (L : list (TType n)),
    (i <= n)%nat ->
    FstInv (n:=n) lq i QP ->
    FstInv (n:=n) lq 0 (fst (loop_normalization lq n i QP L)).
Proof.
  intros Hlqlen Hnd.
  induction i as [|i IH]; intros QP L HiLe Hinv.
  - cbn [loop_normalization]. exact Hinv.
  - cbn [loop_normalization].
    set (qnext := nth (n - S i)%nat lq 0%nat).
    destruct (loop_j_return_QPL n qnext (length L) QP L []) as [QP1 L1] eqn:Hstep.
    cbn.

    assert (Hinv1 : FstInv (n:=n) lq i QP1).
    { eapply FstInv_step; eauto. }

    eapply IH; eauto; lia.
Qed.

Lemma loop_normalization_NoDup_map_fst {n}
  (lq : list nat) (L : list (TType n)) :
  length lq = n ->
  NoDup lq ->
  NoDup (map fst (fst (loop_normalization lq n n [] L))).
Proof.
  intros Hlqlen Hnd.
  assert (Hinv0 : FstInv (n:=n) lq n []).
  { unfold FstInv. split.
    - apply incl_nil_l.
    - cbn. constructor. }

  pose proof (loop_normalization_FstInv (n:=n) lq Hlqlen Hnd n [] L (le_n _) Hinv0) as HinvEnd.
  unfold FstInv in HinvEnd.
  exact (proj2 HinvEnd).
Qed.



Lemma In_lexicographic_iff {n} (Lt : list (TType n)) (t : TType n) :
  In t (lexicographic Lt) <-> In t Lt.
Proof.
  unfold lexicographic.
  split.
  - intro Hin.
    apply in_rev in Hin.
    eapply Permutation_in. 2: apply Hin.
    symmetry.
    apply TOrd.Permuted_sort.
  - intro Hin.
    rewrite <- in_rev.
    eapply Permutation_in. 2: apply Hin.
    apply TOrd.Permuted_sort.
Qed.


Lemma normalization_final_terms_from_Lf {n}
  (lq : list nat) (L0 : list (TType n)) :
  let p := loop_normalization lq n n [] L0 in
  let QP := fst p in
  let L  := snd p in
  incl (map snd QP) (seq 0 (length L)) ->
  forall t,
    In t (map snd (loop_normalization_final lq n n [] L0)) ->
    In t L.
Proof.
  intros p QP L HQP_in t Hin.
  unfold loop_normalization_final in Hin.

  destruct (loop_normalization lq n n [] L0) as [QP0 Lf] eqn:Hnorm.
  cbn in *.
  subst QP L.

  rewrite map_app in Hin.
  apply in_app_iff in Hin.
  destruct Hin as [HinPivot | HinTail].

  - rewrite map_map in HinPivot. simpl in HinPivot.

    apply in_map_iff in HinPivot.
    destruct HinPivot as [qp [Ht_eq Hqp_in]].
    subst t.

    assert (Hin_snd : In (snd qp) (map snd QP0)).
    { apply in_rev in Hqp_in.
      apply In_map_snd_of_In. exact Hqp_in.
    }

    assert (Hidx_lt : (snd qp < length Lf)%nat).
    { unfold incl in HQP_in.
      specialize (HQP_in (snd qp) Hin_snd).
      rewrite in_seq in HQP_in.
      lia.
    }

    apply nth_In. exact Hidx_lt.

  - set (noP :=
           filter (fun a : nat =>
                     negb (existsb (fun p : nat =>
                                     if Nat.eq_dec p a then true else false)
                                  (map snd QP0)))
                  (List.seq 0 (length Lf))).

    set (ys := lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP)).
    set (xs := repeat (@None nat) (length noP)).

    assert (Hmap : map snd (combine xs ys) = ys).
    { apply map_snd_combine.
      unfold xs. rewrite repeat_length.
      unfold ys, lexicographic.
      rewrite rev_length.
      assert (H': length (TOrd.sort (map (fun p0 : nat => nth p0 Lf (defaultT_I n)) noP))
              = length (map (fun p0 : nat => nth p0 Lf (defaultT_I n)) noP)).
      { apply Permutation_length.
        symmetry.
        apply TOrd.Permuted_sort. }
      rewrite H'.
      rewrite map_length. auto. }
    change (In t (map snd (combine xs ys))) in HinTail.
    rewrite Hmap in HinTail.

    apply (proj1 (In_lexicographic_iff (map (fun p => nth p Lf (defaultT_I n)) noP) t)) in HinTail.

    apply in_map_iff in HinTail.
    destruct HinTail as [idx [Ht_eq Hidx_in]].
    subst t.

    unfold noP in Hidx_in.
    apply filter_In in Hidx_in.
    destruct Hidx_in as [Hidx_in_seq _].
    assert (Hidx_lt : (idx < length Lf)%nat).
    { rewrite in_seq in Hidx_in_seq. lia. }

    apply nth_In. exact Hidx_lt.
Qed.

Lemma loop_j_return_QPL_preserves_no_pair_for_q0 {n}
  (q0 qnext j : nat) (QP : list (nat*nat)) (L : list (TType n)) (Lz : list nat)
  (QP' : list (nat*nat)) (L' : list (TType n)) :
  qnext <> q0 ->
  loop_j_return_QPL n qnext j QP L Lz = (QP', L') ->
  (forall pr, ~ In (q0, pr) QP) ->
  (forall pr, ~ In (q0, pr) QP').
Proof.
  intros Hneq Hrun Hno pr.
  destruct (loop_j_return_QPL_classify_shape
              qnext j QP L Lz
              QP' L' Hrun)
    as [res Hshape].
  destruct res as [|prNew|prNew];
    cbn [JRet_shape_ok] in Hshape;
    destruct Hshape as [HQ _];
    subst QP'.
  - apply Hno.
  - cbn. intro Hin. destruct Hin as [Hin|Hin].
    + inversion Hin; subst. contradiction.
    + eapply (Hno pr). exact Hin.
  - cbn. intro Hin. destruct Hin as [Hin|Hin].
    + inversion Hin; subst. contradiction.
    + eapply (Hno pr). exact Hin.
Qed.

Lemma nth_pos_neq_nth0 {A} (d:A) (l:list A) (k:nat) :
  NoDup l ->
  (1 <= k)%nat ->
  (k < length l)%nat ->
  nth k l d <> nth 0 l d.
Proof.
  intros Hnd Hk1 Hklt Heq.
  assert (Hnotin : ~ In (nth k l d) (firstn k l)).
  { eapply NoDup_nth_not_in_firstn; eauto. }
  assert (Hin0 : In (nth 0 l d) (firstn k l)).
  { destruct l as [|h tl]; cbn in *; try lia.
    destruct k; [lia|].
    cbn. left. reflexivity. }
  apply Hnotin.
  now rewrite Heq.
Qed.

Lemma pivot_term_not_None_if_In_pair {n}
  (q0 pr0 : nat) (QPf : list (nat*nat)) (Lf : list (TType n)) (noP : list nat) :
  In (q0, pr0) QPf ->
  pivot_term (n:=n) q0
    (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
     ++ combine (repeat (@None nat) (length noP))
          (lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP)))
  <> None.
Proof.
  intro Hin_pair.
  unfold pivot_term.
  set (pred :=
    fun qt : option nat * TType n =>
      match fst qt with
      | Some q => Nat.eqb q0 q
      | None => false
      end).

  destruct (find pred
    (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
     ++ combine (repeat (@None nat) (length noP))
          (lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP))))
    as [qt|] eqn:Hf.
  - discriminate.
  - intro Hbad.
    clear Hbad.

    assert (Hin_pivotBlock :
      In (Some q0, nth pr0 Lf (defaultT_I n))
        (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf))).
    {
      apply in_map_iff.
      exists (q0, pr0).
      split.
      - cbn. reflexivity.
      - apply in_rev. rewrite rev_involutive. exact Hin_pair.
    }

    assert (Hin_all :
      In (Some q0, nth pr0 Lf (defaultT_I n))
        (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
         ++ combine (repeat (@None nat) (length noP))
              (lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP)))).
    { apply in_app_iff. left. exact Hin_pivotBlock. }

    pose proof (find_none _ _ Hf _ Hin_all) as Hpred_false.

    unfold pred in Hpred_false. cbn in Hpred_false.
    rewrite Nat.eqb_refl in Hpred_false.
    discriminate.
Qed.



Theorem pivots_normalize_first_qubit_ok {n}
  (start : nat) (L0 : list (TType n)) :
  WF_L (n:=n) L0 ->
  length L0 <> 0%nat ->
  (start < n)%nat ->
  let lq := (skipn start (List.seq 0 n)) ++ (firstn start (List.seq 0 n)) in
  let q0 := nth 0 lq 0%nat in
  FirstQubitNormalized_out (n:=n) q0 (pivots_normalize start L0).
Proof.
  intros HWF Hlen Hstart lq q0.
  unfold pivots_normalize.

  set (lqt := loop_normalization_final lq n n [] L0).
  set (p := loop_normalization lq n n [] L0).
  set (QPf := fst p).
  set (Lf  := snd p).

  assert (Hq0 : (q0 < n)%nat).
  { subst q0 lq.
    rewrite app_nth1.
    - rewrite nth_skipn. rewrite Nat.add_0_r. rewrite seq_nth; lia.
    - rewrite skipn_length. rewrite seq_length. lia. }

  assert (Hnodup_lq : NoDup lq).
  { subst lq.
    pose proof (seq_NoDup n 0) as Hnd.
    assert (Hsplit : List.seq 0 n = firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n)).
    { symmetry. apply firstn_skipn. }
    assert (Hperm :
      Permutation (firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n))
                  (skipn start (List.seq 0 n) ++ firstn start (List.seq 0 n))).
    { apply Permutation_app_comm. }
    apply (Permutation_NoDup Hperm).
    rewrite <- Hsplit. auto. }

  set (step0 := loop_j_return_QPL n q0 (length L0) [] L0 []).
  destruct step0 as [QP1 L1] eqn:Hstep0.

  assert (Hinv1 : FirstColInv n q0 QP1 L1).
  { eapply first_step_gives_FirstColInv; eauto. }

  assert (HWF1 : WF_L (n:=n) L1).
  { subst step0.
    pose (WF_loop_j_return_QPL q0 (length L0) [] L0 []) as e.
    rewrite Hstep0 in e. simpl in e.
    apply e; auto. }

  assert (Hlen1 : length L1 <> 0%nat).
  { subst step0.
    pose (loop_j_return_QPL_length n q0 (length L0) [] L0 []) as e.
    rewrite Hstep0 in e. simpl in e. rewrite e. auto. }

  assert (Hnorm_eq :
    loop_normalization lq n n [] L0 =
    loop_normalization lq n (n - 1) QP1 L1).
  { subst step0 p QPf Lf lqt.
    replace n with (S (n - 1))%nat at 3 by lia.
    simpl.
    replace (n - S (n - 1))%nat with 0%nat by lia.
    subst q0.
    rewrite Hstep0.
    auto. }

  assert (Hlq_len : length lq = n).
  { subst lq.
    rewrite app_length, skipn_length, firstn_length, seq_length.
    lia. }

  assert (Hq0def : q0 = nth 0 lq 0%nat) by reflexivity.

  assert (Hstep_run :
           loop_j_return_QPL n q0 (length L0) [] L0 [] = (QP1, L1)).
  { subst step0. exact Hstep0. }

  assert (HQP1_in : incl (map snd QP1) (seq 0 (length L1))).
  {
    pose proof
      (loop_j_return_QPL_incl_QP_seq_0_length_L
         n q0 (length L0) [] L0 []
         Hlen (incl_nil_l _) (incl_nil_l _))
      as Hincl0.
    rewrite Hstep_run in Hincl0. cbn in Hincl0.

    assert (HlenL1eq : length L1 = length L0).
    {
      pose proof (loop_j_return_QPL_length n q0 (length L0) [] L0 []) as Hlen2.
      rewrite Hstep_run in Hlen2. cbn in Hlen2.
      exact Hlen2.
    }
    rewrite HlenL1eq.
    exact Hincl0.
  }

  assert (Hinv : FirstColInv n q0 QPf Lf). 
  {
    subst p QPf Lf.
    rewrite Hnorm_eq.

    refine (loop_normalization_preserves_FirstColInv_after_first
              lq q0
              Hnodup_lq Hlq_len Hq0def
              (n-1)%nat QP1 L1
              _ HWF1 Hq0 Hlen1 HQP1_in Hinv1).
    lia.
  }

  assert (Hincl_snd_final : incl (map snd QPf) (seq 0 (length Lf))).
  { subst p QPf Lf.
    gen L0 HWF Hlen.
    assert (Hincl_loop :
      forall i (QP : list (nat*nat)) (L : list (TType n)),
        WF_L (n:=n) L ->
        length L <> 0%nat ->
        incl (map snd QP) (seq 0 (length L)) ->
        incl (map snd (fst (loop_normalization lq n i QP L))) (seq 0 (length (snd (loop_normalization lq n i QP L))))).
    { induction i as [|i IH]; intros QP L HWFx Hlenx HinclQP.
      - cbn [loop_normalization]. exact HinclQP.
      - cbn [loop_normalization].
        set (qnext := nth (n - S i)%nat lq 0%nat).
        set (step := loop_j_return_QPL n qnext (length L) QP L []).
        destruct step as [QP1' L1'] eqn:Hstep.
        cbn.
        assert (Hincl1_lenL : incl (map snd QP1') (seq 0 (length L))).
        { subst step.
          pose (loop_j_return_QPL_incl_QP_seq_0_length_L n qnext (length L) QP L [] Hlenx (incl_nil_l (seq 0 (length L))) HinclQP) as e.
          rewrite Hstep in e. simpl in e. auto. }
        assert (HlenL1 : length L1' = length L).
        { subst step.
          pose (loop_j_return_QPL_length n qnext (length L) QP L []) as e.
          rewrite Hstep in e. simpl in e. auto. }
        assert (Hincl1 : incl (map snd QP1') (seq 0 (length L1'))).
        { rewrite HlenL1. exact Hincl1_lenL. }
        eapply IH; eauto.
        + subst step.
          pose (WF_loop_j_return_QPL qnext (length L) QP L [] HWFx) as e.
          rewrite Hstep in e. simpl in e. auto.
        + rewrite HlenL1. auto. }
    intros L0 lqt step0 Hstep0 Hnorm_eq Hstep_run Hinv_final HWF0 Hlen0.
    apply (Hincl_loop n [] L0 HWF0 Hlen0).
    cbn. apply incl_nil_l. }

  assert (Hfrom : incl (map snd lqt) Lf).
  { subst lqt.
    pose (normalization_final_terms_from_Lf lq L0) as e.
    unfold incl.
    apply e.
    subst p QPf Lf. auto. }

  unfold FirstQubitNormalized_out.

  change (skipn start (seq 0 n) ++ firstn start (seq 0 n)) with lq.
  
  destruct (pivot_term (n:=n) q0 lqt) as [tp|] eqn:Hpt.

  - pose proof (pivot_search_of_pivot_term_Some (n:=n) lqt q0 tp Hpt) as Hpiv.
    
    fold lqt.
    
    rewrite Hpiv.
    rewrite Hpt.

    subst lqt.
    unfold loop_normalization_final.
    destruct (loop_normalization lq n n [] L0) as [QP0 L0'] eqn:Hnorm in *.
    subst p QPf Lf.

    set (noP :=
      filter
        (fun a : nat =>
           negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                         (map snd QP0)))
        (seq 0 (length L0'))).

    destruct (entry q0 tp) eqn:Hentry; cbn.

    + assert (Hlqt :
               loop_normalization_final lq n n [] L0 =
                 map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                   ++ combine (repeat (@None nat) (length noP))
                   (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP))).
      {
        unfold loop_normalization_final.
        rewrite Hnorm.
        cbn.
        fold noP.
        reflexivity.
      }

      assert (Hpt' :
               pivot_term (n:=n) q0
                 (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                    ++ combine (repeat (@None nat) (length noP))
                    (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP)))
               = Some tp).
      {
        rewrite <- Hlqt.
        exact Hpt.
      }

      pose proof (pivot_term_Some_implies_from_QP
                    q0 QP0 L0' noP tp Hpt')
        as HfromQP.

      destruct HfromQP as [prSel [Hin_pair Htp_prSel]].

      assert (Hnodup_fst_QP0 : NoDup (map fst QP0)).
      {
        pose proof (loop_normalization_NoDup_map_fst lq L0 Hlq_len Hnodup_lq) as Hnd.
        rewrite Hnorm in Hnd. cbn in Hnd. exact Hnd.
      }

      inversion Hinv as
        [QPn Ln HallI
        |QPz Lz pr0 HpivZ HI Hin_pair'
        |QPxy Lxy pr0 HpivXY HIZ Hin_pair'];
        try subst.

      * unfold NoPair in H.
        specialize (H prSel).
        apply (H Hin_pair).

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair' Hpt').
        }

        assert (Hz : entry q0 tp = gZ).
        {
          rewrite Htp_eq.
          exact HpivZ.
        }

        rewrite Hentry in Hz.
        discriminate.
       
      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair' Hpt').
        }

        assert (Hxy_tp : isXY (entry q0 tp) = true).
        {
          rewrite Htp_eq.
          exact HpivXY.
        }

        rewrite Hentry in Hxy_tp.
        cbn in Hxy_tp.
        discriminate.

    + assert (Hlqt :
               loop_normalization_final lq n n [] L0 =
                 map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                   ++ combine (repeat (@None nat) (length noP))
                   (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP))).
      {
        unfold loop_normalization_final.
        rewrite Hnorm.
        cbn.
        fold noP.
        reflexivity.
      }

      assert (Hpt' :
               pivot_term (n:=n) q0
                 (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                    ++ combine (repeat (@None nat) (length noP))
                    (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP)))
               = Some tp).
      {
        rewrite <- Hlqt.
        exact Hpt.
      }

      assert (Hnodup_fst_QP0 : NoDup (map fst QP0)).
      {
        pose proof (loop_normalization_NoDup_map_fst lq L0 Hlq_len Hnodup_lq) as Hnd.
        rewrite Hnorm in Hnd. cbn in Hnd.
        exact Hnd.
      }

      inversion Hinv as
        [QPn Ln HallI HnoPair
        |QPz Lz pr0 HpivZ HI Hin_pair0
        |QPxy Lxy pr0 HpivXY HIZ Hin_pair0];
        try subst.

      * assert (HinOut_tp : In tp (map snd (loop_normalization_final lq n n [] L0))).
        { apply pivot_term_Some_in_terms with (q0:=q0); exact Hpt. }
        assert (HinLf_tp : In tp L0').
        { apply Hfrom. exact HinOut_tp. }
        destruct (In_nth L0' tp (defaultT_I n) HinLf_tp) as [idx [Hlt Hnth]].
        specialize (HallI idx Hlt).
        simpl in *.
        rewrite Hnth in HallI.
        rewrite Hentry in HallI.
        discriminate.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }
        assert (Hz_tp : entry q0 tp = gZ).
        { rewrite Htp_eq. exact HpivZ. }
        rewrite Hentry in Hz_tp. discriminate.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }

        intros t HinT HneqTp.

        assert (HinT_final : In t (map snd (loop_normalization_final lq n n [] L0))).
        {
          rewrite Hlqt.
          exact HinT.
        }

        assert (HinLf_t : In t L0').
        { apply Hfrom. exact HinT_final. }

        destruct (In_nth L0' t (defaultT_I n) HinLf_t) as [idx [Hidx_lt Hidx_nth]].

        assert (Hidx_neq : idx <> pr0).
        {
          intro E; subst idx.
          apply HneqTp.
          rewrite Htp_eq.
          symmetry. exact Hidx_nth.
        }

        specialize (HIZ idx Hidx_lt Hidx_neq).
        simpl in *.
        rewrite Hidx_nth in HIZ.
        exact HIZ.

    + assert (Hlqt :
               loop_normalization_final lq n n [] L0 =
                 map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                   ++ combine (repeat (@None nat) (length noP))
                   (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP))).
      {
        unfold loop_normalization_final.
        rewrite Hnorm.
        cbn.
        fold noP.
        reflexivity.
      }

      assert (Hpt' :
               pivot_term (n:=n) q0
                 (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                    ++ combine (repeat (@None nat) (length noP))
                    (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP)))
               = Some tp).
      {
        rewrite <- Hlqt.
        exact Hpt.
      }

      assert (Hnodup_fst_QP0 : NoDup (map fst QP0)).
      {
        pose proof (loop_normalization_NoDup_map_fst lq L0 Hlq_len Hnodup_lq) as Hnd.
        rewrite Hnorm in Hnd. cbn in Hnd.
        exact Hnd.
      }

      inversion Hinv as
        [QPn Ln HallI HnoPair
        |QPz Lz pr0 HpivZ HI Hin_pair0
        |QPxy Lxy pr0 HpivXY HIZ Hin_pair0];
        try subst.

      * assert (HinOut_tp : In tp (map snd (loop_normalization_final lq n n [] L0))).
        { apply pivot_term_Some_in_terms with (q0:=q0); exact Hpt. }
        assert (HinLf_tp : In tp L0').
        { apply Hfrom. exact HinOut_tp. }
        destruct (In_nth L0' tp (defaultT_I n) HinLf_tp) as [idx [Hlt Hnth]].
        specialize (HallI idx Hlt).
        simpl in *.
        rewrite Hnth in HallI.
        rewrite Hentry in HallI.
        discriminate.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }
        assert (Hz_tp : entry q0 tp = gZ).
        { rewrite Htp_eq. exact HpivZ. }
        rewrite Hentry in Hz_tp. discriminate.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }

        intros t HinT HneqTp.

        assert (HinT_final : In t (map snd (loop_normalization_final lq n n [] L0))).
        {
          rewrite Hlqt.
          exact HinT.
        }

        assert (HinLf_t : In t L0').
        { apply Hfrom. exact HinT_final. }

        destruct (In_nth L0' t (defaultT_I n) HinLf_t) as [idx [Hidx_lt Hidx_nth]].

        assert (Hidx_neq : idx <> pr0).
        {
          intro E; subst idx.
          apply HneqTp.
          rewrite Htp_eq.
          symmetry. exact Hidx_nth.
        }

        specialize (HIZ idx Hidx_lt Hidx_neq).
        simpl in *.
        rewrite Hidx_nth in HIZ.
        exact HIZ.

    + assert (Hlqt :
               loop_normalization_final lq n n [] L0 =
                 map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                   ++ combine (repeat (@None nat) (length noP))
                   (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP))).
      {
        unfold loop_normalization_final.
        rewrite Hnorm.
        cbn.
        fold noP.
        reflexivity.
      }

      assert (Hpt' :
               pivot_term (n:=n) q0
                 (map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) L0' (defaultT_I n))) (rev QP0)
                    ++ combine (repeat (@None nat) (length noP))
                    (lexicographic (map (fun p : nat => nth p L0' (defaultT_I n)) noP)))
               = Some tp).
      {
        rewrite <- Hlqt.
        exact Hpt.
      }

      assert (Hnodup_fst_QP0 : NoDup (map fst QP0)).
      {
        pose proof (loop_normalization_NoDup_map_fst lq L0 Hlq_len Hnodup_lq) as Hnd.
        rewrite Hnorm in Hnd. cbn in Hnd.
        exact Hnd.
      }

      inversion Hinv as
        [QPn Ln HallI HnoPair
        |QPz Lz pr0 HpivZ HI Hin_pair0
        |QPxy Lxy pr0 HpivXY HIZ Hin_pair0];
        try subst.

      * assert (HinOut_tp : In tp (map snd (loop_normalization_final lq n n [] L0))).
        { apply pivot_term_Some_in_terms with (q0:=q0); exact Hpt. }
        assert (HinLf_tp : In tp L0').
        { apply Hfrom. exact HinOut_tp. }
        destruct (In_nth L0' tp (defaultT_I n) HinLf_tp) as [idx [Hlt Hnth]].
        specialize (HallI idx Hlt).
        simpl in *.
        rewrite Hnth in HallI.
        rewrite Hentry in HallI.
        discriminate.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }

        intros t HinT HneqTp.

        assert (HinT_final : In t (map snd (loop_normalization_final lq n n [] L0))).
        { rewrite Hlqt. exact HinT. }

        assert (HinLf_t : In t L0').
        { apply Hfrom. exact HinT_final. }

        destruct (In_nth L0' t (defaultT_I n) HinLf_t) as [idx [Hidx_lt Hidx_nth]].

        assert (Hidx_neq : idx <> pr0).
        { intro E; subst idx.
          apply HneqTp.
          rewrite Htp_eq.
          symmetry. exact Hidx_nth.
        }

        specialize (HI idx Hidx_lt Hidx_neq).
        simpl in *.
        rewrite Hidx_nth in HI.
        exact HI.

      * assert (Htp_eq : tp = nth pr0 L0' (defaultT_I n)).
        {
          refine (pivot_term_eq_nth_pr0_from_inv
                    q0 pr0
                    QP0 L0' noP tp
                    Hnodup_fst_QP0 Hin_pair0 Hpt').
        }
        assert (Hxy_tp : isXY (entry q0 tp) = true).
        { rewrite Htp_eq. exact HpivXY. }
        rewrite Hentry in Hxy_tp.
        cbn in Hxy_tp.
        discriminate.

  -  pose proof (pivot_search_of_pivot_term_None (n:=n) lqt q0 Hpt) as Hpiv.
    fold lqt.
    rewrite Hpiv.
    rewrite Hpt.
    intros t HinOut.
    assert (HinLf : In t Lf).
    { apply Hfrom. exact HinOut. }
    destruct (In_nth Lf t (defaultT_I n) HinLf) as [idx [Hlt Hnth]].
    
    inversion Hinv as
      [QPn Ln HallI HnoPair
      |QPz Lz pr0 HpivZ HI Hin_pair
      |QPxy Lxy pr0 HpivXY HIZ Hin_pair];
      try subst.
    + rewrite <- Hnth.
      exact (HallI idx Hlt).

    + subst lqt.
      unfold loop_normalization_final in Hpt.
      destruct (loop_normalization lq n n [] L0) as [QP0 L0'] eqn:Hnorm in *.
      subst p QPf Lf.
      set (noP :=
             filter
               (fun a : nat =>
                  negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP0)))
               (seq 0 (length L0'))).
      cbn in Hpt. fold noP in Hpt.

      pose proof (pivot_term_not_None_if_In_pair (n:=n) q0 pr0 QP0 L0' noP Hin_pair) as HnotNone.
      
      apply HnotNone in Hpt.
      contradiction.

    + subst lqt.
      unfold loop_normalization_final in Hpt.
      destruct (loop_normalization lq n n [] L0) as [QP0 L0'] eqn:Hnorm in *.
      subst p QPf Lf.
      set (noP :=
             filter
               (fun a : nat =>
                  negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP0)))
               (seq 0 (length L0'))).
      cbn in Hpt. fold noP in Hpt.

      pose proof (pivot_term_not_None_if_In_pair (n:=n) q0 pr0 QP0 L0' noP Hin_pair) as HnotNone.
      apply HnotNone in Hpt.
      contradiction.
Qed. 

Lemma isIZ_gX_false : isIZ gX = false. Proof. cbn. reflexivity. Qed.
Lemma isIZ_gY_false : isIZ gY = false. Proof. cbn. reflexivity. Qed.

Lemma existsb_eq_dec_true_of_In (a : nat) (l : list nat) :
  In a l ->
  existsb (fun p : nat => if Nat.eq_dec p a then true else false) l = true.
Proof.
  induction l as [|x xs IH]; intro Hin.
  - contradiction.
  - cbn in Hin.
    cbn.
    destruct Hin as [Hin|Hin].
    + subst x.
      destruct (Nat.eq_dec a a) as [_|H]; [reflexivity|contradiction].
    + destruct (Nat.eq_dec x a) as [_|_].
      * reflexivity.
      * exact (IH Hin).
Qed.

Lemma In_noP_notIn_map_snd {n}
  (QP : list (nat*nat)) (L : list (TType n)) (a : nat) :
  let noP :=
    filter
      (fun x : nat =>
         negb
           (existsb (fun p : nat => if Nat.eq_dec p x then true else false)
                    (map snd QP)))
      (seq 0 (length L)) in
  In a noP ->
  ~ In a (map snd QP).
Proof.
  intro noP.
  intro Hin_noP.
  intro Hin_map.

  unfold noP in Hin_noP.
  apply filter_In in Hin_noP.
  destruct Hin_noP as [_ Hcond].
  apply Bool.negb_true_iff in Hcond.

  pose proof (existsb_eq_dec_true_of_In a (map snd QP) Hin_map) as Htrue.
  rewrite Htrue in Hcond.
  discriminate.
Qed.

Lemma NoDup_map_snd_unique_q (QP : list (nat*nat)) :
  NoDup (map snd QP) ->
  forall q1 q2 pr,
    In (q1, pr) QP ->
    In (q2, pr) QP ->
    q1 = q2.
Proof.
  intro Hnd.
  induction QP as [|[q pr0] tl IH]; intros q1 q2 pr Hin1 Hin2.
  - contradiction.
  - cbn in Hnd.
    inversion Hnd as [|x xs Hnotin Hnd_tl]; subst.
    cbn in Hin1, Hin2.
    destruct Hin1 as [Hin1|Hin1];
    destruct Hin2 as [Hin2|Hin2].

    + inversion Hin1; inversion Hin2; subst. reflexivity.

    + inversion Hin1; subst.
      exfalso.
      apply Hnotin.
      rewrite in_map_iff.
      exists (q2,pr).
      split; auto.

    + inversion Hin2; subst.
      exfalso.
      apply Hnotin.
      rewrite in_map_iff.
      exists (q1,pr).
      split; auto.

    + eapply IH; eauto.
Qed.

Lemma Permutation_lexicographic {n} (Lt : list (TType n)) :
  Permutation Lt (lexicographic Lt).
Proof.
  unfold lexicographic.
  pose proof (TOrd.Permuted_sort Lt) as Hperm.
  pose proof (Permutation_rev (TOrd.sort Lt)) as Hrev.
  exact (Permutation_trans Hperm Hrev).
Qed.

Definition drop_q {n} (q : nat) (p : option nat * TType n) : bool :=
  match fst p with
  | Some j => negb (Nat.eqb q j)
  | None => true
  end.
 

Lemma XY_pivot_term_not_in_filtered_snd {n}
  (q : nat)
  (QPf : list (nat*nat)) (Lf : list (TType n))
  (t : TType n) :
  let noP := (filter (fun x : nat => negb (existsb (fun p : nat => if Nat.eq_dec p x then true else false) (map snd QPf))) (List.seq 0 (length Lf))) in
  let out :=
    map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
    ++ combine (repeat (@None nat) (length noP))
         (lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP))
  in
  NoDup (map snd QPf) ->
  incl (map snd QPf) (seq 0 (length Lf)) ->
  (exists pr0,
      isXY (entry q (nth pr0 Lf (defaultT_I n))) = true /\
      ColIZ_except (n:=n) q pr0 Lf /\
      In (q, pr0) QPf) ->
  pivot_term (n:=n) q out = Some t ->
  (pivot_search (n:=n) out q = gX \/ pivot_search (n:=n) out q = gY) ->
  ~ In t (map snd (filter (drop_q (n:=n) q) out)).
Proof.
  intros noP out Hnd_snd Hincl_snd [pr0 [Hxy [Hcol Hin_qpr0]]] Hpt Hps.
  intro Hin.

  pose proof (pivot_search_of_pivot_term_Some (n:=n) out q t Hpt) as HpivEq.
  assert (HentryXY : entry q t = gX \/ entry q t = gY).
  { rewrite HpivEq in Hps. exact Hps. }

  apply in_map_iff in Hin.
  destruct Hin as [p [Hsnd HinF]].
  apply filter_In in HinF.
  destruct HinF as [HinOut Hdrop].

  apply in_app_iff in HinOut.
  destruct HinOut as [HinPiv | HinTail].

  - apply in_map_iff in HinPiv.
    destruct HinPiv as [qp [Hp HinRev]].
    subst p.
    destruct qp as [q' idx]. cbn in *.
    unfold drop_q in Hdrop. cbn in Hdrop.
    apply Bool.negb_true_iff in Hdrop.
    apply Nat.eqb_neq in Hdrop.
    assert (Hqneq : q' <> q).
    { intro E; subst q'. contradiction. }

    assert (Hnth_idx : nth idx Lf (defaultT_I n) = t).
    { exact Hsnd. }

    assert (Hidx_neq : idx <> pr0).
    {
      intro E; subst idx.
      assert (Hin_QPf : In (q', pr0) QPf).
      { apply in_rev in HinRev. exact HinRev. }
      assert (Heq : q' = q).
      { apply (NoDup_map_snd_unique_q QPf Hnd_snd q' q pr0 Hin_QPf Hin_qpr0). }
      subst q'.
      contradiction.
    }

    assert (Hidx_lt : (idx < length Lf)%nat).
    {
      assert (Hin_QPf : In (q', idx) QPf).
      { apply in_rev in HinRev. exact HinRev. }
      assert (Hin_idx_map : In idx (map snd QPf)).
      { apply In_map_snd_of_In in Hin_QPf. auto. }
      assert (Hin_seq : In idx (seq 0 (length Lf))). { apply Hincl_snd in Hin_idx_map. auto. }
      apply in_seq in Hin_seq. lia.
    }

    specialize (Hcol idx Hidx_lt Hidx_neq).
    rewrite Hnth_idx in Hcol.

    destruct HentryXY as [Hx|Hy].
    + rewrite Hx in Hcol. cbn in Hcol. discriminate.
    + rewrite Hy in Hcol. cbn in Hcol. discriminate.

  - assert (Hin_lex :
      In t (lexicographic (map (fun p0 : nat => nth p0 Lf (defaultT_I n)) noP))).
    { destruct p as [oq tp0]. cbn in Hsnd. subst tp0.
      assert (oq = None).
      {
        eapply In_combine_repeatNone_fst_None.
        exact HinTail.
      }
      subst oq.
      clear Hdrop.
      revert HinTail.
      set (ys := lexicographic (map (fun p0 : nat => nth p0 Lf (defaultT_I n)) noP)).
      intros HinTail'.
      revert ys HinTail'.
      induction (repeat (@None nat) (length noP)) as [|h rs IH]; intros ys HinTail'.
      - cbn in HinTail'. contradiction.
      - destruct ys as [|y ys'].
        + cbn in HinTail'. contradiction.
        + cbn in HinTail'.
          destruct HinTail' as [Hhd|Htl].
          * inversion Hhd. subst. left. reflexivity.
          * right. apply in_combine_r in Htl. auto.
    }

    pose proof (proj1 (In_lexicographic_iff (n:=n) (map (fun p0 => nth p0 Lf (defaultT_I n)) noP) t)) as Hlex_to_map.
    assert (Hin_map : In t (map (fun p0 : nat => nth p0 Lf (defaultT_I n)) noP)).
    { apply Hlex_to_map. exact Hin_lex. }

    apply in_map_iff in Hin_map.
    destruct Hin_map as [idx [Hnth Hin_idx_noP]].

    assert (Hidx_neq : idx <> pr0).
    {
      intro E; subst idx.
      assert (Hin_pr0_map : In pr0 (map snd QPf)).
      { apply In_map_snd_of_In in Hin_qpr0. auto. }
      pose proof (In_noP_notIn_map_snd (n:=n) QPf Lf pr0) as HnoP.
      cbn in HnoP.
      specialize (HnoP Hin_idx_noP).
      apply (HnoP Hin_pr0_map).
    }

    assert (Hidx_lt : (idx < length Lf)%nat).
    {
      unfold noP in Hin_idx_noP.
      apply filter_In in Hin_idx_noP.
      destruct Hin_idx_noP as [Hin_seq _].
      apply in_seq in Hin_seq. lia.
    }

    specialize (Hcol idx Hidx_lt Hidx_neq).
    rewrite Hnth in Hcol.

    destruct HentryXY as [Hx|Hy].
    + rewrite Hx in Hcol. cbn in Hcol. discriminate.
    + rewrite Hy in Hcol. cbn in Hcol. discriminate.
Qed.


Lemma pivots_normalize_yields_FirstColInv {n}
  (start : nat) (L0 : list (TType n)) :
  WF_L (n:=n) L0 ->
  length L0 <> 0%nat ->
  (start < n)%nat ->
  let lq := (skipn start (List.seq 0 n)) ++ (firstn start (List.seq 0 n)) in
  let q0 := nth 0 lq 0%nat in
  FirstColInv n q0 (fst (loop_normalization lq n n [] L0))
                     (snd (loop_normalization lq n n [] L0)).
Proof.
  intros HWF0 Hlen0 Hstart lq q0.

  assert (Hq0 : (q0 < n)%nat).
  { subst q0 lq.
    rewrite app_nth1.
    - rewrite nth_skipn. rewrite Nat.add_0_r. rewrite seq_nth; lia.
    - rewrite skipn_length. rewrite seq_length. lia. }

  assert (Hnodup_lq : NoDup lq).
  { subst lq.
    pose proof (seq_NoDup n 0) as Hnd.
    assert (Hsplit : List.seq 0 n = firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n)).
    { symmetry. apply firstn_skipn. }
    assert (Hperm :
      Permutation (firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n))
                  (skipn start (List.seq 0 n) ++ firstn start (List.seq 0 n))).
    { apply Permutation_app_comm. }
    apply (Permutation_NoDup Hperm).
    rewrite <- Hsplit.
    exact Hnd. }

  assert (Hlq_len : length lq = n).
  { subst lq.
    rewrite app_length, skipn_length, firstn_length, seq_length.
    lia. }

  assert (Hq0def : q0 = nth 0 lq 0%nat) by reflexivity.

  destruct n as [|n']; [lia|].

  cbn [loop_normalization].
  replace (S n' - S n')%nat with 0%nat by lia.
  rewrite <- Hq0def.

  destruct (loop_j_return_QPL (S n') q0 (length L0) [] L0 [])
    as [QP1 L1] eqn:Hstep_run.
  cbn.

  assert (Hinv1 : FirstColInv (S n') q0 QP1 L1).
  { refine (@first_step_gives_FirstColInv (S n') q0 L0 QP1 L1 _ _ _ _).
    - exact Hlen0.
    - exact HWF0.
    - exact Hq0.
    - exact Hstep_run. }

  assert (HWF1 : WF_L (n:=S n') L1).
  { pose proof (WF_loop_j_return_QPL (n:=S n') q0 (length L0) [] L0 []) as Hwfstep.
    specialize (Hwfstep HWF0).
    rewrite Hstep_run in Hwfstep.
    cbn in Hwfstep.
    exact Hwfstep. }

  assert (Hlen1 : length L1 <> 0%nat).
  { pose proof (@loop_j_return_QPL_length (S n') q0 (length L0) [] L0 []) as HlenEq.
    rewrite Hstep_run in HlenEq.
    cbn in HlenEq.
    rewrite HlenEq.
    exact Hlen0. }

  assert (HQP1_in : incl (map snd QP1) (seq 0 (length L1))).
  { pose proof (@loop_j_return_QPL_length (S n') q0 (length L0) [] L0 []) as HlenEq.
    rewrite Hstep_run in HlenEq. cbn in HlenEq.
    pose proof (@loop_j_return_QPL_incl_QP_seq_0_length_L
                  (S n') q0 (length L0) [] L0 []
                  Hlen0 (incl_nil_l _) (incl_nil_l _)) as Hincl.
    rewrite Hstep_run in Hincl. cbn in Hincl.
    rewrite HlenEq.
    exact Hincl. }

  refine (@loop_normalization_preserves_FirstColInv_after_first
            (S n') (lq) (q0)
            Hnodup_lq _ _ n' QP1 L1 _ HWF1 Hq0 Hlen1 HQP1_in Hinv1).
  - exact Hlq_len.
  - exact Hq0def.
  - lia.
Qed.

Lemma pivots_normalize_XY_pivot_term_not_in_filtered_snd {n}
  (start : nat) (L0 : list (TType n)) :
  WF_L (n:=n) L0 ->
  length L0 <> 0%nat ->
  (start < n)%nat ->
  forall t : TType n,
    pivot_term (n:=n) start (pivots_normalize start L0) = Some t ->
    (pivot_search (n:=n) (pivots_normalize start L0) start = gX \/
     pivot_search (n:=n) (pivots_normalize start L0) start = gY) ->
    ~ In t (map snd (filter (drop_q (n:=n) start) (pivots_normalize start L0))).
Proof.
  intros HWF Hlen Hstart t Hpt Hps.

  set (lq := (skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n))).
  set (q0 := nth 0 lq 0%nat).

  assert (q0start: q0 = start).
  { subst q0 lq.
    rewrite app_nth1. rewrite nth_skipn. rewrite Nat.add_0_r. rewrite seq_nth. lia. lia.
    rewrite skipn_length. rewrite seq_length. lia. }

  unfold pivots_normalize in *.
  unfold loop_normalization_final in *.

  destruct (loop_normalization lq n n [] L0) as [QPf Lf] eqn:Hnorm.
  cbn in *.

  set (noP :=
    filter
      (fun a : nat =>
         negb
           (existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                    (map snd QPf)))
      (List.seq 0 (length Lf))).

  set (out :=
    map (fun qp : nat*nat => (Some (fst qp), nth (snd qp) Lf (defaultT_I n))) (rev QPf)
    ++ combine (repeat (@None nat) (length noP))
         (lexicographic (map (fun p : nat => nth p Lf (defaultT_I n)) noP))).

  unfold pivots_normalize in Hpt.
  unfold loop_normalization_final in Hpt.
  fold lq in Hpt.
  rewrite Hnorm in Hpt.
  cbn in Hpt.
  fold noP in Hpt.

  fold out in Hpt.

  unfold pivots_normalize in Hps.
  unfold loop_normalization_final in Hps.
  fold lq in Hps.
  rewrite Hnorm in Hps.
  cbn in Hps.
  fold noP in Hps.

  fold out in Hps.

  unfold pivots_normalize.
  unfold loop_normalization_final.
  fold lq.
  rewrite Hnorm.
  cbn.
  fold noP.

  fold out.

  assert (Hnd_snd : NoDup (map snd QPf)).
  { pose (loop_normalization_NoDup_map_snd lq n n [] L0) as e.
    rewrite Hnorm in e. simpl in e. apply e. apply NoDup_nil. }

  assert (Hincl_snd : incl (map snd QPf) (seq 0 (length Lf))).
  { pose proof
      (loop_normalization_incl_map_snd_seq lq n n [] L0
         Hlen (incl_nil_l _)) as Hincl0.
    rewrite Hnorm in Hincl0. cbn in Hincl0.
    pose proof (loop_normalization_length lq n n [] L0) as HlenLf.
    rewrite Hnorm in HlenLf. cbn in HlenLf.
    rewrite HlenLf; auto.
    apply NoDup_nil. apply incl_nil_l. }

  assert (Hlq_len : length lq = n).
  { subst lq.
    rewrite app_length, skipn_length, firstn_length, seq_length.
    lia. }

  assert (Hnodup_lq : NoDup lq).
  { subst lq.
    pose proof (seq_NoDup n 0) as Hnd.
    assert (Hsplit : List.seq 0 n = firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n)).
    { symmetry. apply firstn_skipn. }
    assert (Hperm :
      Permutation (firstn start (List.seq 0 n) ++ skipn start (List.seq 0 n))
                  (skipn start (List.seq 0 n) ++ firstn start (List.seq 0 n))).
    { apply Permutation_app_comm. }
    apply (Permutation_NoDup Hperm).
    rewrite <- Hsplit.
    exact Hnd. }

  assert (Hnd_fst_QPf : NoDup (map fst QPf)).
  { pose proof (loop_normalization_NoDup_map_fst lq L0 Hlq_len Hnodup_lq) as Hnd.
    rewrite Hnorm in Hnd. cbn in Hnd.
    exact Hnd. }

  pose proof (pivots_normalize_yields_FirstColInv (n:=n) start L0 HWF Hlen Hstart) as Hinv.
  cbn in Hinv. fold lq q0 in Hinv.
  rewrite Hnorm in Hinv. cbn in Hinv.

  assert (Hex_pr0 :
    exists pr0,
      isXY (entry q0 (nth pr0 Lf (defaultT_I n))) = true /\
      ColIZ_except (n:=n) q0 pr0 Lf /\
      In (q0, pr0) QPf).
  {
    inversion Hinv as
      [QPn Ln HallI HnoPair
      |QPz Lz pr0 HpivZ HI Hin_pair
      |QPxy Lxy pr0 HpivXY HIZ Hin_pair];
    try subst.

    - pose proof (pivot_term_Some_implies_from_QP (n:=n) q0 QPf Lf noP t) as HfromQP.
      rewrite q0start in *. fold out in HfromQP. specialize (HfromQP Hpt).
      destruct HfromQP as [prSel [Hin_qprSel _]].
      unfold NoPair in HnoPair.
      specialize (HnoPair prSel).
      exfalso. exact (HnoPair Hin_qprSel).

    - assert (Ht_eq : t = nth pr0 Lf (defaultT_I n)).
      { refine (pivot_term_eq_nth_pr0_from_inv
                  q0 pr0
                  QPf Lf noP t
                  Hnd_fst_QPf Hin_pair _). 
        rewrite q0start in *. fold out. auto. }

      pose proof (pivot_search_of_pivot_term_Some (n:=n) out q0 t) as HpivEq.
      rewrite q0start in HpivEq. specialize (HpivEq Hpt).
      assert (HentryXY : entry q0 t = gX \/ entry q0 t = gY).
      { rewrite HpivEq in Hps. rewrite q0start in *. exact Hps. }

      assert (Hz : entry q0 t = gZ).
      { rewrite Ht_eq. exact HpivZ. }

      exfalso.
      destruct HentryXY as [Hx|Hy].
      + rewrite Hx in Hz. discriminate.
      + rewrite Hy in Hz. discriminate.

    - exists pr0. split; [exact HpivXY|]. split; [exact HIZ|]. exact Hin_pair.
  }

  subst out.
  refine (XY_pivot_term_not_in_filtered_snd
            start QPf Lf t
            _ _ _ _ _).
  - exact Hnd_snd.
  - exact Hincl_snd.
  - rewrite q0start in *. exact Hex_pr0.
  - exact Hpt.
  - exact Hps.
Qed.
