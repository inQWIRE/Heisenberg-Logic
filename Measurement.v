Require Import stdpp.gmap.

Require Export HeisenbergFoundations.HoareHeisenbergLogic.
Require Import HeisenbergFoundations.PivotRule.

Local Open Scope stdpp_scope.


Lemma PauliMult_listT_chain_preserves_length {n : nat} {Lt1 Lt2 : list (TType n)}:
  PauliMult_listT_chain Lt1 Lt2 -> length Lt1 = length Lt2.
Proof. intros H. induction H.
  - rewrite H; auto.
  - inversion H; auto.
  - rewrite IHPauliMult_listT_chain1, IHPauliMult_listT_chain2; auto.
Qed.

Lemma filter_true [A : Type] (l : list A):
  (filter (λ _ : A, true) l) = l.
Proof. induction l; auto. simpl. f_equal. auto. Qed.

Lemma map_nth_seq [A : Type] (l : list A) (d : A):
  (map (λ i : nat, nth i l d) (List.seq 0 (length l))) = l.
Proof. apply nth_ext with (d := (λ i : nat, nth i l d) (s (length l))) (d' := d).
  rewrite map_length. rewrite seq_length. reflexivity.
  intros n H.
  rewrite map_nth with (d := s (length l)).
  rewrite seq_nth.
  f_equal.
  rewrite map_length in H. rewrite seq_length in H.
  assumption.
Qed.

Lemma WF_L_n_nonzero_implies_Forall_proper_length_TType {n : nat} {lt : list (TType n)}:
  WF_L lt -> n <> 0%nat -> Forall proper_length_TType lt.
Proof. intros H H0.
    unfold WF_L in *. unfold PivotRule.WF_T in *. unfold proper_length_TType in *.
    rewrite Forall_forall in *.
    intros; split; auto.
Qed.

Lemma Forall_vecSatisfies_normalize {n : nat} (q : nat) (lt : list (TType n)) (v : Vector (2 ^ n)):
  WF_L lt -> WF_Matrix v ->
  Forall (fun t : TType n => vecSatisfies v (translate t)) lt ->
  Forall (fun t : TType n => vecSatisfies v (translate t)) (normalize q lt).
Proof. intros H WFv.
  bdestruct (length lt =? 0)%nat.
  rewrite length_zero_iff_nil in H0.
  subst. rewrite normalize_nil. auto.
  bdestruct (n =? 0)%nat.
  subst. intros. unfold WF_L, PivotRule.WF_T in H. rewrite Forall_forall in *. intros x H2.
  unfold normalize, pivots_normalize, loop_normalization_final in *. simpl in *.
  rewrite filter_true in H2. rewrite map_nth_seq in H2.
  rewrite map_snd_combine in H2. unfold lexicographic in H2. rewrite <- in_rev in H2.
  pose (TOrd.Permuted_sort lt) as e. rewrite <- (Permutation_in' (eq_refl x) e) in H2.
  specialize (H1 x H2). assumption.
  rewrite repeat_length. rewrite seq_length. unfold lexicographic. rewrite rev_length.
  pose (TOrd.Permuted_sort lt) as e. apply Permutation_length in e. assumption.
  pose (WF_L_n_nonzero_implies_Forall_proper_length_TType H H1) as e.
  remember e as temp. clear e Heqtemp H H1.
  rename temp into H.
  destruct (normalize_PauliMult_listT_chain_Permutation q lt H0) as [[lt' [H1 H2]]].
  remember H2 as H2'. clear HeqH2'.
  remember H2 as H2''. clear HeqH2''.
  eapply Permutation_Forall in H2'.
  apply Permutation_sym in H2''.
  eapply Permutation_Forall in H2''.
  assert (H3: Forall (fun t : TType n => vecSatisfies v (translate t)) (normalize q lt) <->
            Forall (fun t : TType n => vecSatisfies v (translate t)) lt') by (split; intros; auto).
  rewrite H3.
  clear - H0 H H1 WFv.
  induction H1.
  - rewrite H1; auto.
  - remember H1 as H1'. clear HeqH1'.
    inversion H1.
    pose (PauliMult_listT_preserves_proper_length_TType Lt1 Lt2 H1' H) as H5.
    pose (PauliMultLeft Lt1 Lt2 (map TtoA Lt1) (map TtoA Lt2) H H5 H2 H0 H4) as H6.
    assert (temp1: map TtoA Lt1 = map TtoA Lt1) by reflexivity.
    assert (temp2: map TtoA Lt2 = map TtoA Lt2) by reflexivity.
    specialize (H6 temp1 temp2).
    pose (interpret_implies (⋂ map TtoA Lt1)%P (⋂ map TtoA Lt2)%P H6 v) as H7.
    simpl in H7.
    assert (temp3: WF_Matrix v /\
              Forall (fun a0 : AType n => vecSatisfies v (translateA a0)) (map TtoA Lt1) <->
              Forall (fun t : TType n => vecSatisfies v (translate t)) Lt1).
    { split; intros H9.
      - destruct H9.
        rewrite Forall_forall in *. intros x H10.
        unfold TtoA in *.
        specialize (H9 [x]).
        assert (H11: In [x] (map (fun t : TType n => [t]) Lt1)).
        { rewrite in_map_iff. exists x. split; auto. }
        specialize (H9 H11).
        unfold translateA in H9.
        simpl in H9. rewrite Mplus_0_l in H9. auto.
      - split; auto.
        rewrite Forall_forall in *. intros x H10.
        unfold TtoA in *.
        specialize (H9 (AtoT x)).
        unfold AtoT in *.
        destruct x.
        rewrite in_map_iff in H10.
        destruct H10. destruct H8. discriminate.
        rewrite in_map_iff in H10.
        destruct H10. destruct H8.
        destruct x; try discriminate.
        inversion H8. subst.
        simpl in *.
        specialize (H9 H10).
        unfold translateA.
        simpl. rewrite Mplus_0_l. auto. }
    assert (temp4: WF_Matrix v /\
              Forall (fun a0 : AType n => vecSatisfies v (translateA a0)) (map TtoA Lt2) <->
              Forall (fun t : TType n => vecSatisfies v (translate t)) Lt2).
    { split; intros H9.
      - destruct H9.
        rewrite Forall_forall in *. intros x H10.
        unfold TtoA in *.
        specialize (H9 [x]).
        assert (H11: In [x] (map (fun t : TType n => [t]) Lt2)).
        { rewrite in_map_iff. exists x. split; auto. }
        specialize (H9 H11).
        unfold translateA in H9.
        simpl in H9. rewrite Mplus_0_l in H9. auto.
      - split; auto.
        rewrite Forall_forall in *. intros x H10.
        unfold TtoA in *.
        specialize (H9 (AtoT x)).
        unfold AtoT in *.
        destruct x.
        rewrite in_map_iff in H10.
        destruct H10. destruct H8. discriminate.
        rewrite in_map_iff in H10.
        destruct H10. destruct H8.
        destruct x; try discriminate.
        inversion H8. subst.
        simpl in *.
        specialize (H9 H10).
        unfold translateA.
        simpl. rewrite Mplus_0_l. auto. }
    rewrite temp3, temp4 in H7. auto.
  - remember H1_ as H1_'. clear HeqH1_'. remember H1_0 as H1_0'. clear HeqH1_0'.
    apply PauliMult_listT_chain_preserves_length in H1_, H1_0.
    intros. apply IHPauliMult_listT_chain2; auto. lia.
    eapply PauliMult_listT_chain_preserves_proper_length_TType; eauto.
Qed.


Definition Zprojector_plus (prg_len bit : nat) :=
  if bit <? prg_len
  then (1 / C2) .* (I (2 ^ prg_len)%nat .+ (prog_simpl_app prg_len σz bit))
  else I (2 ^ prg_len).

Definition Zprojector_minus (prg_len bit : nat) :=
  if bit <? prg_len
  then (1 / C2) .* (I (2 ^ prg_len)%nat .+ (-C1) .* (prog_simpl_app prg_len σz bit))
  else Zero.


Lemma WF_Matrix_Zprojector_plus  (prg_len bit : nat):
  WF_Matrix (Zprojector_plus prg_len bit).
Proof. unfold Zprojector_plus.
  bdestruct_all; auto with wf_db.
Qed.

Lemma WF_Matrix_Zprojector_minus  (prg_len bit : nat):
  WF_Matrix (Zprojector_minus prg_len bit).
Proof. unfold Zprojector_minus.
  bdestruct_all; auto with wf_db.
Qed.

#[export] Hint Resolve WF_Matrix_Zprojector_plus WF_Matrix_Zprojector_minus : wf_db.

Lemma switch_overflow {X : Type} (ls : list X) (x : X) (n : nat):
  (n >= length ls)%nat -> switch ls x n = ls.
Proof. intros H.
  gen x n. induction ls; intros; simpl; auto.
  destruct n; simpl in H; try lia.
  f_equal.
  apply IHls; lia.
Qed.

Lemma big_kron_repeat_I (n : nat):
  big_kron (repeat (I 2) n) = I (2 ^ n).
Proof. induction n; auto.
   replace (⨂ repeat (I 2) (s n)) with (I 2 ⊗ (⨂ repeat (I 2) n)) by (simpl; auto).
   assert (2 ^ (s n) = 2 * 2 ^ n)%nat.
   { setoid_rewrite <- Nat.add_1_l at 3.
     rewrite Nat.pow_add_r. simpl. auto. }
   rewrite H. rewrite <- id_kron. rewrite ! repeat_length. f_equal. auto.
Qed.

Lemma prog_simpl_app_z_mult_twice_id (n i : nat):
  (prog_simpl_app n σz i) × (prog_simpl_app n σz i) = I (2 ^ n).
Proof. unfold prog_simpl_app. bdestruct_all.
  - setoid_rewrite kron_mixed_product'; auto.
    setoid_rewrite kron_mixed_product'; auto.
    pose σz_unitary as H'. unfold WF_Unitary in H'.
    destruct H' as [H0 H1].
    rewrite σz_hermitian_rw in H1.
    rewrite H1.
    rewrite ! Mmult_1_l; auto with wf_db.
    rewrite ! id_kron. f_equal.
    setoid_rewrite <- Nat.pow_1_r at 8.
    rewrite <- ! Nat.pow_add_r. f_equal. lia.
    all: setoid_rewrite <- Nat.pow_1_r at 13;
      rewrite <- ! Nat.pow_add_r; f_equal; lia.
  - rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma big_kron_map_translate_P_switch_gZ_prog_simpl_app_z (n i : nat):
⨂ map translate_P (switch (repeat gI n) gZ i) = prog_simpl_app n σz i.
Proof. unfold prog_simpl_app. bdestruct_all.
  - rewrite switch_inc.
    2: rewrite repeat_length; auto.
    rewrite ! map_app.
    rewrite big_kron_app.
    2: { intros i0.
         rewrite <- firstn_map.
         rewrite map_repeat.
         simpl.
         rewrite firstn_repeat.
         minmax_breakdown.
         bdestruct (i0 <? i)%nat.
         - rewrite nth_indep with (d' := I 2); try rewrite repeat_length; auto.
           rewrite nth_repeat. auto with wf_db.
         - rewrite nth_overflow; try rewrite repeat_length; auto with wf_db. }
    2: { intros i0.
         bdestruct (i0 <? n - i)%nat.
         - apply Forall_nth.
           2: { rewrite app_length. rewrite ! map_length.
                rewrite skipn_length. rewrite repeat_length. simpl. lia. }
           rewrite Forall_app. split.
           + simpl. constructor; auto with wf_db.
           + rewrite <- skipn_map.
             rewrite map_repeat.
             replace (translate_P gI) with (I 2) by auto.
             rewrite skipn_repeat.
             rewrite Forall_forall.
             intros x H1.
             apply repeat_spec in H1.
             subst. auto with wf_db.
         - rewrite nth_overflow.
           2: { rewrite app_length. rewrite ! map_length.
                rewrite skipn_length. rewrite repeat_length. simpl. lia. }
           auto with wf_db. }
    rewrite big_kron_app.
    2: { intros i0. simpl. destruct i0; auto with wf_db.
         destruct i0; auto with wf_db. }
    2: {intros i0. rewrite <- skipn_map. rewrite map_repeat.
        replace (translate_P gI) with (I 2) by auto.
        rewrite skipn_repeat.
        bdestruct (i0 <? n - s i)%nat.
        - rewrite nth_indep with (d' := I 2); try rewrite repeat_length; auto.
          rewrite nth_repeat; auto with wf_db.
        - rewrite nth_overflow; try rewrite repeat_length; auto with wf_db. }
    setoid_rewrite <- kron_assoc'; auto.
    2: { rewrite <- firstn_map. rewrite map_repeat.
         replace (translate_P gI) with (I 2) by auto.
         rewrite firstn_repeat. minmax_breakdown.
         apply WF_big_kron'.
         intros A H0. apply repeat_spec in H0. subst. auto with wf_db. }
    2: { simpl. auto with wf_db. }
    2: { rewrite <- skipn_map. rewrite map_repeat.
         replace (translate_P gI) with (I 2) by auto.
         rewrite skipn_repeat.
         apply WF_big_kron'.
         intros A H0. apply repeat_spec in H0. subst. auto with wf_db. }
    rewrite ! map_length. rewrite ! firstn_length. rewrite ! skipn_length. rewrite ! repeat_length. minmax_breakdown.
    f_equal.
    f_equal. lia. f_equal. lia.
    f_equal.
    + rewrite <- firstn_map. rewrite map_repeat.
      replace (translate_P gI) with (I 2) by auto.
      rewrite firstn_repeat. minmax_breakdown.
      rewrite big_kron_repeat_I. auto.
    + simpl. rewrite kron_1_r. auto.
    + rewrite skipn_repeat. rewrite map_repeat.
      replace (translate_P gI) with (I 2) by auto.
      rewrite big_kron_repeat_I. f_equal. f_equal. lia.
  - rewrite switch_overflow; try rewrite repeat_length; auto.
    rewrite map_repeat.
    replace (translate_P gI) with (I 2) by auto.
    rewrite big_kron_repeat_I. auto.
Qed.

Lemma translate_switch_gZ_prog_simpl_app_z_plus (n i : nat):
  translate (C1, switch (repeat gI n) gZ i) = prog_simpl_app n σz i.
Proof. pose (big_kron_map_translate_P_switch_gZ_prog_simpl_app_z n i) as H.
  unfold translate in *. simpl in *.
  rewrite Mscale_1_l. auto.
Qed.

Lemma translate_switch_gZ_prog_simpl_app_z_minus (n i : nat):
  translate (- C1, switch (repeat gI n) gZ i) = - C1 .* (prog_simpl_app n σz i).
Proof. pose (big_kron_map_translate_P_switch_gZ_prog_simpl_app_z n i) as H.
  unfold translate in *. simpl in *.
  rewrite ! map_length. rewrite ! switch_len. rewrite ! repeat_length. f_equal.
  auto.
Qed.

Lemma Zi_Zprojector_plus_eigenvector {n} (i : nat) (v : Vector (2 ^ n)%nat) :
  translate (C1, switch (repeat gI n) gZ i) × (Zprojector_plus n i × v) = (Zprojector_plus n i × v).
Proof. rewrite translate_switch_gZ_prog_simpl_app_z_plus.
  unfold Zprojector_plus. bdestruct_all.
  - rewrite Mscale_mult_dist_l. rewrite Mscale_mult_dist_r. f_equal.
    rewrite <- Mmult_assoc.
    rewrite Mmult_plus_distr_l.
    rewrite prog_simpl_app_z_mult_twice_id.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite Mplus_comm at 1.
    auto.
  - unfold prog_simpl_app. bdestruct_all.
    rewrite <- Mmult_assoc. rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma Zi_Zprojector_minus_eigenvector {n} (i : nat) (v : Vector (2 ^ n)%nat) :
  translate (- C1, switch (repeat gI n) gZ i) × (Zprojector_minus n i × v) = (Zprojector_minus n i × v).
Proof. rewrite translate_switch_gZ_prog_simpl_app_z_minus.
  unfold Zprojector_minus. bdestruct_all.
  - setoid_rewrite Mscale_mult_dist_l at 2. rewrite Mscale_mult_dist_r. rewrite ! Mscale_mult_dist_l. f_equal.
    rewrite <- Mmult_assoc.
    rewrite Mmult_plus_distr_l.
    rewrite Mscale_mult_dist_r.
    rewrite prog_simpl_app_z_mult_twice_id.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite <- Mscale_mult_dist_l. rewrite Mscale_plus_distr_r.
    rewrite Mplus_comm at 1.
    rewrite Mscale_assoc.
    replace (- C1 * - C1) with C1 by lca.
    rewrite Mscale_1_l.
    auto.
  - unfold prog_simpl_app. bdestruct_all.
    rewrite Mmult_0_l. rewrite Mmult_0_r. auto.
Qed.

Lemma length_cons {A} (a : A) l : length (a :: l) = Datatypes.S (length l).
Proof. reflexivity. Qed.

Lemma translate_Zprojector_plus_eigenvector_IZ {n : nat} (q : nat) (t : TType n) (v : Vector (2 ^ n)):
  (q < n)%nat -> PivotRule.WF_T t -> isIZ (entry q t) = true -> translate t × v = v ->
  translate t × (Zprojector_plus n q × v) = Zprojector_plus n q × v.
Proof. intros H H0 H1 H2.
  unfold Zprojector_plus.
  unfold prog_simpl_app.
  unfold translate in *.
  unfold PivotRule.WF_T in *.
  rewrite ! map_length in *. rewrite ! H0 in *.
  setoid_rewrite Mscale_mult_dist_l in H2.
  rewrite <- H2 at 2.
  setoid_rewrite Mscale_mult_dist_l.
  setoid_rewrite Mscale_mult_dist_r.
  f_equal.
  bdestruct_all.
  setoid_rewrite Mscale_mult_dist_l.
  setoid_rewrite Mscale_mult_dist_r.
  f_equal.
  rewrite <- ! Mmult_assoc.
  f_equal.
  assert (I (2 ^ n) .+ I (2 ^ q) ⊗ σz ⊗ I (2 ^ (n - q - 1))
          = I (2 ^ q) ⊗ (I (2 ^ 1) .+ σz) ⊗ I (2 ^ (n - q - 1))).
  { assert (I (2 ^ n) = I (2 ^ q) ⊗ I (2 ^ 1) ⊗ I (2 ^ (n - q - 1))).
    { rewrite ! id_kron. f_equal. rewrite <- ! Nat.pow_add_r. f_equal. lia. }
    rewrite H4.
    rewrite kron_assoc. 2-4: auto with wf_db.
    rewrite kron_assoc. 2-4: auto with wf_db.
    setoid_rewrite <- kron_plus_distr_l.
    setoid_rewrite <- kron_plus_distr_r.
    rewrite <- kron_assoc. 2-4: auto with wf_db.
    reflexivity. }
  rewrite H4.
  rewrite (nth_inc q (snd t) gI); try lia.
  rewrite ! map_app.
  rewrite ! big_kron_app.
  all: try apply WF_Matrix_nth_Pauli.
  2: rewrite <- map_app; apply WF_Matrix_nth_Pauli.
  rewrite ! kron_assoc. 2-4: auto with wf_db.
  rewrite ! app_length. rewrite ! map_length. rewrite ! firstn_length. minmax_breakdown. rewrite ! skipn_length. rewrite ! H0. rewrite ! length_cons. rewrite <- ! Nat.pow_add_r.
  setoid_rewrite kron_mixed_product'; try (try rewrite <- Nat.pow_add_r; f_equal; try setoid_rewrite length_nil; lia).
  rewrite Mmult_1_r.
  2: { pose (WF_Matrix_Big_Pauli (take q t.2)) as e.
       rewrite ! map_length in e. rewrite ! firstn_length in e. minmax_breakdown_context.
       apply e. }
  rewrite Mmult_1_l.
  2: { pose (WF_Matrix_Big_Pauli (take q t.2)) as e.
       rewrite ! map_length in e. rewrite ! firstn_length in e. minmax_breakdown_context.
       apply e. }
  f_equal. f_equal. simpl. lia. f_equal. simpl. lia.
  setoid_rewrite kron_mixed_product'; try (try rewrite <- Nat.pow_add_r; f_equal; try setoid_rewrite length_nil; lia).
  f_equal. f_equal. lia. f_equal. lia.
  simpl. unfold isIZ, entry in H1. destruct (nth q t.2 gI); try discriminate; simpl; lma'.
  rewrite Mmult_1_l.
  2: { pose (WF_Matrix_Big_Pauli (drop (s q) t.2)) as e.
       rewrite ! map_length in e. rewrite ! skipn_length in e. rewrite ! H0 in e.
       replace (n - q - 1)%nat with (n - s q)%nat by lia.
       apply e. }
  rewrite <- Mmult_1_r.
  2: { pose (WF_Matrix_Big_Pauli (drop (s q) t.2)) as e.
       rewrite ! map_length in e. rewrite ! skipn_length in e. rewrite ! H0 in e.
       replace (n - q - 1)%nat with (n - s q)%nat by lia.
       apply e. }
  replace (n - q - 1)%nat with (n - s q)%nat by lia.
  reflexivity.
  all: rewrite <- ?Nat.pow_add_r.
  all: f_equal; cbn; lia.
Qed.

Lemma translate_Zprojector_minus_eigenvector_IZ {n : nat} (q : nat) (t : TType n) (v : Vector (2 ^ n)):
  (q < n)%nat -> PivotRule.WF_T t -> isIZ (entry q t) = true -> translate t × v = v ->
  translate t × (Zprojector_minus n q × v) = Zprojector_minus n q × v.
Proof. intros H H0 H1 H2.
  unfold Zprojector_minus.
  unfold prog_simpl_app.
  unfold translate in *.
  unfold PivotRule.WF_T in *.
  rewrite ! map_length in *. rewrite ! H0 in *.
  setoid_rewrite Mscale_mult_dist_l in H2.
  rewrite <- H2 at 2.
  setoid_rewrite Mscale_mult_dist_l.
  setoid_rewrite Mscale_mult_dist_r.
  f_equal.
  bdestruct_all.
  setoid_rewrite Mscale_mult_dist_l.
  setoid_rewrite Mscale_mult_dist_r.
  f_equal.
  rewrite <- ! Mmult_assoc.
  f_equal.
  assert (temp: (@Matrix.scale (Nat.pow (Datatypes.S (Datatypes.S O)) n)
             (Nat.pow (Datatypes.S (Datatypes.S O)) n)
             (Copp (RtoC (IZR (Zpos xH))))
             (@kron
                (Init.Nat.mul (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)))
                (Init.Nat.mul (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)))
                (Nat.pow (Datatypes.S (Datatypes.S O))
                   (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O)))
                (Nat.pow (Datatypes.S (Datatypes.S O))
                   (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O)))
                (@kron (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)) (Datatypes.S (Datatypes.S O))
                   (I (Nat.pow (Datatypes.S (Datatypes.S O)) q)) σz)
                (I
                   (Nat.pow (Datatypes.S (Datatypes.S O))
                      (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O))))))
          = (@kron
                (Init.Nat.mul (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)))
                (Init.Nat.mul (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)))
                (Nat.pow (Datatypes.S (Datatypes.S O))
                   (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O)))
                (Nat.pow (Datatypes.S (Datatypes.S O))
                   (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O)))
                (@kron (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Nat.pow (Datatypes.S (Datatypes.S O)) q)
                   (Datatypes.S (Datatypes.S O)) (Datatypes.S (Datatypes.S O))
                   (I (Nat.pow (Datatypes.S (Datatypes.S O)) q)) (
                     (@Matrix.scale (Datatypes.S (Datatypes.S O))
                        (Datatypes.S (Datatypes.S O))
                        (Copp (RtoC (IZR (Zpos xH)))) σz)))
                (I
                   (Nat.pow (Datatypes.S (Datatypes.S O))
                      (Init.Nat.sub (Init.Nat.sub n q) (Datatypes.S O)))))).
  { distribute_scale. reflexivity. }
  rewrite temp.
  assert ((I (2 ^ n) .+ I (2 ^ q) ⊗ (- C1 .* σz) ⊗ I (2 ^ (n - q - 1)))
          = I (2 ^ q) ⊗ (I (2 ^ 1) .+ (- C1 .* σz)) ⊗ I (2 ^ (n - q - 1))).
  { assert (I (2 ^ n) = I (2 ^ q) ⊗ I (2 ^ 1) ⊗ I (2 ^ (n - q - 1))).
    { rewrite ! id_kron. f_equal. rewrite <- ! Nat.pow_add_r. f_equal. lia. }
    rewrite H4.
    rewrite kron_assoc. 2-4: auto with wf_db.
    rewrite kron_assoc. 2-4: auto with wf_db.
    setoid_rewrite <- kron_plus_distr_l.
    setoid_rewrite <- kron_plus_distr_r.
    rewrite <- kron_assoc. 2-4: auto with wf_db.
    reflexivity. }
  rewrite H4.
  rewrite (nth_inc q (snd t) gI); try lia.
  rewrite ! map_app.
  rewrite ! big_kron_app.
  all: try apply WF_Matrix_nth_Pauli.
  2: rewrite <- map_app; apply WF_Matrix_nth_Pauli.
  rewrite ! kron_assoc. 2-4: auto with wf_db.
  rewrite ! app_length. rewrite ! map_length. rewrite ! firstn_length. minmax_breakdown. rewrite ! skipn_length. rewrite ! H0. rewrite ! length_cons. rewrite <- ! Nat.pow_add_r.
  setoid_rewrite kron_mixed_product'; try (try rewrite <- Nat.pow_add_r; f_equal; try setoid_rewrite length_nil; lia).
  rewrite Mmult_1_r.
  2: { pose (WF_Matrix_Big_Pauli (take q t.2)) as e.
       rewrite ! map_length in e. rewrite ! firstn_length in e. minmax_breakdown_context.
       apply e. }
  rewrite Mmult_1_l.
  2: { pose (WF_Matrix_Big_Pauli (take q t.2)) as e.
       rewrite ! map_length in e. rewrite ! firstn_length in e. minmax_breakdown_context.
       apply e. }
  f_equal. f_equal. simpl. lia. f_equal. simpl. lia.
  setoid_rewrite kron_mixed_product'; try (try rewrite <- Nat.pow_add_r; f_equal; try setoid_rewrite length_nil; lia).
  f_equal. f_equal. lia. f_equal. lia.
  simpl. unfold isIZ, entry in H1. destruct (nth q t.2 gI); try discriminate; simpl; lma'.
  rewrite Mmult_1_l.
  2: { pose (WF_Matrix_Big_Pauli (drop (s q) t.2)) as e.
       rewrite ! map_length in e. rewrite ! skipn_length in e. rewrite ! H0 in e.
       replace (n - q - 1)%nat with (n - s q)%nat by lia.
       apply e. }
  rewrite <- Mmult_1_r.
  2: { pose (WF_Matrix_Big_Pauli (drop (s q) t.2)) as e.
       rewrite ! map_length in e. rewrite ! skipn_length in e. rewrite ! H0 in e.
       replace (n - q - 1)%nat with (n - s q)%nat by lia.
       apply e. }
  replace (n - q - 1)%nat with (n - s q)%nat by lia.
  reflexivity.
  all: rewrite <- ?Nat.pow_add_r.
  all: f_equal; cbn; lia.
Qed.


(** partial function from nat to option bool **)
Definition creg := gmap nat bool.
Check {[2%nat := true]} : creg.


Inductive cpred :=
| TRUE
| FALSE
| REG (n : nat) (b : bool)
| AND (a b : cpred)
| OR (a b : cpred)
| NOT (a : cpred).


Fixpoint translate_cpred (p : cpred) (r : creg) : bool :=
  match p with
  | TRUE => true
  | FALSE => false
  | REG n b =>
    from_option (λ rn, eqb rn b) false (r !! n) (* true if register n stores b, false otherwise *)
  | AND a b =>
    translate_cpred a r && translate_cpred b r
  | OR a b =>
    translate_cpred a r || translate_cpred b r
  | NOT a =>
    ¬ translate_cpred a r
  end.


Definition cqstate n := (creg * (Vector (2 ^ n)))%type.
Definition cqlist n := list (cqstate n).


Inductive mprog :=
| U (p : prog)
| MEAS (q : nat) (i : nat)
| ITE (c : cpred) (p1 p2 : prog)
| mseq (mp1 mp2 : mprog).

Coercion U : prog >-> mprog.

Infix ";;;" := mseq (at level 51, right associativity).



(* Restrict for q < n for all cases *)
Fixpoint apply_mprog {n} (mp : mprog) (cqs : cqlist n) {struct mp} : cqlist n :=
  match mp with
  | U p => map (fun cq => (fst cq, Mmult (translate_prog n p) (snd cq))) cqs
  | MEAS q i =>
      if (q <? n) then
        flat_map
          (fun cq => [
               (<[i := true]> (fst cq), Mmult (Zprojector_plus n q) (snd cq)); (** Zero vec introduction? **)
               (<[i := false]> (fst cq), Mmult (Zprojector_minus n q) (snd cq)) (** Zero vec introduction? **)
          ]) cqs
      else cqs
  | ITE c p1 p2 =>
      map (fun cq =>
          (fst cq, Mmult (translate_prog n
            (if translate_cpred c cq.1 then p1 else p2)) (snd cq))
        ) cqs
  | mseq mp1 mp2 => apply_mprog mp2 (apply_mprog mp1 cqs)
  end.

Lemma apply_mprog_nil {n} (mp : mprog):
  @apply_mprog n mp [] = [].
Proof. induction mp; simpl; auto. bdestruct_all; auto.
  rewrite IHmp1. rewrite IHmp2. auto.
Qed.

Lemma apply_mprog_app {n} (mp : mprog) (cql1 cql2 : cqlist n):
  apply_mprog mp (cql1 ++ cql2) = (apply_mprog mp cql1) ++ (apply_mprog mp cql2).
Proof. gen cql1 cql2. induction mp; intros.
  - simpl. rewrite map_app. auto.
  - simpl.
    bdestruct_all; auto.
    rewrite flat_map_app. auto.
  - simpl. rewrite map_app. auto.
  - simpl. rewrite IHmp1. rewrite IHmp2. auto.
Qed.

Lemma apply_mprog_cons {n} (mp : mprog) (cq : cqstate n) (cql : cqlist n):
  apply_mprog mp (cq :: cql) = (apply_mprog mp [cq]) ++ (apply_mprog mp cql).
Proof. rewrite cons_conc. rewrite apply_mprog_app. auto. Qed.

Lemma apply_mprog_seq {n} (mp1 mp2 : mprog) (cql1 : cqlist n) (cq2 cq3 : cqstate n):
 In cq2 (apply_mprog mp1 cql1) -> In cq3 (apply_mprog mp2 [cq2]) ->
 In cq3 (apply_mprog (mp1;;; mp2) cql1).
Proof.  intros H H0.
   simpl.
   apply (@In_nth (cqstate n) _ _ (empty:creg,Zero)) in H.
   destruct H as [m [mbound mth]].
   rewrite (@nth_inc (cqstate n) m (apply_mprog mp1 cql1) (empty:creg,Zero)); auto.
   rewrite ! apply_mprog_app.
   rewrite ! in_app_iff.
   right. left. rewrite <- mth in H0. auto.
Qed.

Lemma apply_mprog_inv {n} (mp : mprog) (cql : cqlist n) (cq' : cqstate n):
  In cq' (apply_mprog mp cql) -> exists cq, In cq cql /\ In cq' (apply_mprog mp [cq]).
Proof. intros H.
  gen cq' cql. induction mp; intros.
  - simpl in *.
    rewrite in_map_iff in H.
    destruct H as [x [xcq' inx]].
    exists x. auto.
  - simpl in *.
    bdestruct_all. 2: { exists cq'. split; simpl; auto. }
    rewrite in_flat_map in H.
    destruct H as [x [xcq' inx]].
    exists x. auto.
  - cbn in *.
    apply in_map_iff in H as (cq & Hcqeq & Hcq).
    exists cq.
    split; [easy|].
    now left.
  - simpl in *.
    specialize (IHmp2 cq' (apply_mprog mp1 cql) H).
    destruct IHmp2 as [cq1 [incq1 incq']].
    specialize (IHmp1 cq1 cql incq1).
    destruct IHmp1 as [cq [incq incq1']].
    exists cq. split; auto.
    apply apply_mprog_seq with (cq2 := cq1); auto.
Qed.

Lemma apply_mprog_seq_inv {n} (mp1 mp2 : mprog) (cql1 : cqlist n) (cq3 : cqstate n):
   In cq3 (apply_mprog (mp1;;; mp2) cql1) ->
   exists cq2, In cq2 (apply_mprog mp1 cql1) /\ In cq3 (apply_mprog mp2 [cq2]).
Proof. intros H.
  apply apply_mprog_inv.
  auto.
Qed.

Lemma apply_mprog_preserves_Forall_WF_Matrix {n} (mp : mprog) (cql : cqlist n):
  Forall (fun cq => WF_Matrix (snd cq)) cql -> Forall (fun cq => WF_Matrix (snd cq)) (apply_mprog mp cql).
Proof. intros H.
  gen cql. induction mp; intros.
  - induction cql.
    + rewrite apply_mprog_nil. auto.
    + rewrite apply_mprog_cons.
      rewrite Forall_cons_iff in H.
      destruct H.
      rewrite Forall_app.
      split; auto.
      simpl. constructor.
      * simpl. auto with wf_db.
      * constructor.
  - induction cql.
    + rewrite apply_mprog_nil. auto.
    + rewrite apply_mprog_cons.
      rewrite Forall_cons_iff in H.
      destruct H.
      rewrite Forall_app.
      split; auto.
      simpl.
      bdestruct_all. 2:{ constructor; auto. }
      constructor.
      * simpl. auto with wf_db.
      * constructor.
        -- simpl. auto with wf_db.
        -- constructor.
  - cbn.
    rewrite Forall_map.
    eapply list.Forall_impl; [eassumption|].
    intros [].
    cbn.
    now auto with wf_db.
  - simpl. auto.
Qed.

Lemma apply_mprog_preserves_WF_Matrix {n} (mp : mprog) (cq cq' : cqstate n):
 WF_Matrix (snd cq) -> In cq' (apply_mprog mp [cq]) -> WF_Matrix (snd cq').
Proof. intros H H0.
  assert (Forall (fun cq => WF_Matrix (snd cq)) [cq]).
  { constructor; auto. }
  apply apply_mprog_preserves_Forall_WF_Matrix with (mp := mp) in H1.
  inversion H1.
  - rewrite <- H3 in H0. inversion H0.
  - rewrite <- H2 in H0.
    destruct H0; subst; auto.
    rewrite Forall_forall in H4.
    apply H4; auto.
Qed.

Lemma apply_mprog_preserves_snd_Zero {n} (mp : mprog) (cql : cqlist n):
  Forall (fun cq => (snd cq) = Zero) cql -> Forall (fun cq => (snd cq) = Zero) (apply_mprog mp cql).
Proof. intros H.
  gen mp. induction cql; intros.
  - rewrite apply_mprog_nil. constructor.
  - rewrite apply_mprog_cons.
    rewrite Forall_app.
    rewrite Forall_cons_iff in H.
    destruct H.
    split; auto.
    rewrite Forall_forall.
    intros x H1.
    clear IHcql H0 cql.
    gen x a. induction mp; intros;
      simpl in *.
    + rewrite kill_false in H1.
      rewrite H in H1.
      rewrite Mmult_0_r in H1.
      destruct x.
      inversion H1; subst; simpl; auto.
    + destruct (q <? n).
      * destruct H1.
        -- destruct x.
           inversion H0; subst; simpl.
           setoid_rewrite H.
           rewrite Mmult_0_r. auto.
        -- destruct H0.
           ++ inversion H0; subst; simpl.
              setoid_rewrite H.
              rewrite Mmult_0_r. auto.
           ++ inversion H0.
      * destruct H1; subst; auto. inversion H0.
    + destruct H1 as [<-|[]].
      cbn.
      rewrite H.
      now rewrite Mmult_0_r.
    + apply apply_mprog_seq_inv in H1.
      destruct H1 as [cq [incq inx]].
      apply IHmp1 in incq; auto.
      apply IHmp2 in inx; auto.
Qed.


Definition Mbranch n := (cpred * (list (TType n)))%type.
Definition MPredicate n := list (Mbranch n).


Definition cqSatisfiesMbranch {n} (cq : cqstate n) (b : Mbranch n) (H : WF_Matrix (snd cq)) : Prop :=
  if Mat_eq_dec (2 ^ n) (1%nat) (snd cq) (Zero) H (WF_Zero (2 ^ n) 1%nat)
  then True
  else match translate_cpred (fst b) (fst cq) with
          | true => Forall (fun t : TType n => vecSatisfies (snd cq) (translate t)) (snd b)
          | _ => False
          end.


Definition Mtriple {n} (A : MPredicate n) (mp : mprog) (B : MPredicate n) :=
  forall a, In a A -> forall cq (H : WF_Matrix (snd cq)), cqSatisfiesMbranch cq a H -> forall cq', In cq' (apply_mprog mp [cq]) ->
   exists b, In b B /\ exists (H0 : WF_Matrix (snd cq')), cqSatisfiesMbranch cq' b H0.

Notation "{{{ A }}} g {{{ B }}}" := (Mtriple A g B) (at level 70, no associativity).




Lemma MSEQ_RULE {n} (A B C : MPredicate n) (mp1 mp2 : mprog):
  Mtriple A mp1 B -> Mtriple B mp2 C -> Mtriple A (mp1 ;;; mp2) C.
Proof. intros H H0.
  unfold Mtriple in *.
  intros a H1 cq H2 H3 cq' H4.
  apply apply_mprog_seq_inv in H4.
  destruct H4 as [cq0 [incq0 incq']].
  specialize (H a H1 cq H2 H3 cq0 incq0).
  destruct H as [b [inb [WFcq0 cqSatcq0]]].
  specialize (H0 b inb cq0 WFcq0 cqSatcq0 cq' incq').
  destruct H0 as [c [inc [WFcq' cqSatc]]].
  exists c. split; auto. exists WFcq'. auto.
Qed.

Lemma PERM_POST {n} (A B B' : MPredicate n) (mp : mprog):
  Permutation B B' -> Mtriple A mp B -> Mtriple A mp B'.
Proof. intros H H0.
  unfold Mtriple in *.
  intros a H1 cq H2 H3 cq' H4.
  specialize (H0 a H1 cq H2 H3 cq' H4).
  destruct H0 as [b [inb [WFcq' cqSatb]]].
  apply (Permutation_in b H) in inb.
  exists b. split; auto. exists WFcq'. auto.
Qed.

Lemma PERM_POST_IFF {n} (A B B' : MPredicate n) (mp : mprog):
  Permutation B B' -> (Mtriple A mp B <-> Mtriple A mp B').
Proof. intros H. split; intros H0.
  - apply (PERM_POST A B B' mp H H0).
  - apply Permutation_sym in H. apply (PERM_POST A B' B mp H H0).
Qed.

Lemma PERM_PRE {n} (A A' B : MPredicate n) (mp : mprog):
  Permutation A A' -> Mtriple A mp B -> Mtriple A' mp B.
Proof. intros H H0.
  unfold Mtriple in *.
  intros a H1 cq H2 H3 cq' H4.
  apply Permutation_sym in H.
  apply (Permutation_in a H) in H1.
  specialize (H0 a H1 cq H2 H3 cq' H4).
  auto.
Qed.

Lemma PERM_PRE_IFF {n} (A A' B : MPredicate n) (mp : mprog):
  Permutation A A' -> (Mtriple A mp B <-> Mtriple A' mp B).
Proof. intros H. split; intros H0.
  - apply (PERM_PRE A A' B mp H H0).
  - apply Permutation_sym in H. apply (PERM_PRE A' A B mp H H0).
Qed.


Lemma CUP_RULE {n} (A B A' B' : MPredicate n) (mp : mprog):
  Mtriple A mp B -> Mtriple A' mp B' -> Mtriple (A ++ A') mp (B ++ B').
Proof. intros H H0.
  unfold Mtriple in *.
  intros a H1 cq H2 H3 cq' H4.
  rewrite in_app_iff in H1.
  destruct H1.
  - specialize (H a H1 cq H2 H3 cq' H4).
    destruct H as [b [inb [WFcq' cqSatcq']]].
    exists b.
    split.
    + rewrite in_app_iff. left. auto.
    + exists WFcq'. auto.
  - specialize (H0 a H1 cq H2 H3 cq' H4).
    destruct H0 as [b [inb [WFcq' cqSatcq']]].
    exists b.
    split.
    + rewrite in_app_iff. right. auto.
    + exists WFcq'. auto.
Qed.

Lemma CUP_CONS_RULE {n} (a : Mbranch n) (B A' B' : MPredicate n) (mp : mprog):
  Mtriple [a] mp B -> Mtriple A' mp B' -> Mtriple (a :: A') mp (B ++ B').
Proof. intros H H0.
  rewrite cons_conc.
  apply (CUP_RULE [a] B A' B' mp H H0).
Qed.


Lemma ITE_RULE {n} (lt : list (TType n)) (C : cpred) (Q : MPredicate n) (p1 p2 : prog) (A : cpred):
  {{{ [ (AND A C, lt) ] }}} p1 {{{ Q }}} ->
  {{{ [ (AND A (NOT C), lt) ] }}} p2 {{{ Q }}} ->
  {{{ [ (A, lt) ] }}} (ITE C p1 p2) {{{ Q }}}.
Proof. intros H H0.
  unfold Mtriple in *.
  intros a H1 cq H2 H3 cq' H4.
  destruct H1. 2: inversion H1. subst.
  unfold cqSatisfiesMbranch in H3.
  destruct (Mat_eq_dec (2 ^ n) 1 (snd cq) Zero H2 (WF_Zero (2 ^ n) 1)) eqn:E.
  - simpl in H4.
    assert (snd cq' = Zero).
    { destruct H4 as [H4|[]].
      subst cq'.
      rewrite e.
      apply Mmult_0_r. }
    destruct (translate_cpred C (fst cq)) eqn:E'.
      * assert (In (AND A C, lt) [(AND A C, lt)]).
        { left. auto. }
        assert (cqSatisfiesMbranch cq (AND A C, lt) H2).
        { unfold cqSatisfiesMbranch.
          rewrite E. auto. }
        specialize (H (AND A C, lt) H5 cq H2 H6 cq' H4).
        auto.
      *assert (In (AND A (NOT C), lt) [(AND A (NOT C), lt)]).
        { left. auto. }
        assert (cqSatisfiesMbranch cq (AND A (NOT C), lt) H2).
        { unfold cqSatisfiesMbranch.
          rewrite E. auto. }
        specialize (H0 (AND A (NOT C), lt) H5 cq H2 H6 cq' H4).
        auto.
  - simpl in H3.
    destruct (translate_cpred A (fst cq)) eqn:E';
    try destruct b; try contradiction.
    simpl in H4.
    destruct (translate_cpred C (fst cq)) eqn:E''.
    + assert (In (AND A C, lt) [(AND A C, lt)]).
      { left. auto. }
      specialize (H (AND A C, lt) H1 cq H2).
      assert (cqSatisfiesMbranch cq (AND A C, lt) H2).
      { unfold cqSatisfiesMbranch.
        rewrite E. simpl.
        rewrite E'.
        rewrite E''.
        simpl. auto. }
      specialize (H H5 cq' H4).
      auto.
    + assert (In (AND A (NOT C), lt) [(AND A (NOT C), lt)]).
      { left. auto. }
      specialize (H0 (AND A (NOT C), lt) H1 cq H2).
      assert (cqSatisfiesMbranch cq (AND A (NOT C), lt) H2).
      { unfold cqSatisfiesMbranch.
        rewrite E. simpl.
        rewrite E'.
        rewrite E''.
        simpl. auto. }
      specialize (H0 H5 cq' H4).
      auto.
Qed.


Definition apply_MEAS {n} (i : nat) (b : bool) (lt : list (TType n)) : list (TType n) :=
  let LQT := pivots_normalize i lt in
  if b then
  match pivot_search LQT i with
  | gX | gY => (C1, (switch (repeat gI n) gZ i)) :: (map snd (filter (fun p =>
                                                                      match fst p with
                                                                      | Some j => negb (Nat.eqb i j)
                                                                      | None => true
                                                                      end) LQT))
  | gZ | gI => (C1, (switch (repeat gI n) gZ i)) :: (map snd LQT)
  end
  else match pivot_search LQT i with
  | gX | gY => (- C1, (switch (repeat gI n) gZ i)) :: (map snd (filter (fun p =>
                                                                      match fst p with
                                                                      | Some j => negb (Nat.eqb i j)
                                                                      | None => true
                                                                      end) LQT))
  | gZ | gI => (- C1, (switch (repeat gI n) gZ i)) :: (map snd LQT)
  end.




Inductive does_not_appear (i : nat) : cpred -> Prop :=
| dna_TRUE : does_not_appear i TRUE
| dna_FALSE : does_not_appear i FALSE
| dna_REG : forall (j : nat) b, (i <> j) -> does_not_appear i (REG j b)
| dna_AND : forall (c1 c2 : cpred),
    does_not_appear i c1 -> does_not_appear i c2
    -> does_not_appear i (AND c1 c2)
| dna_OR : forall (c1 c2 : cpred),
    does_not_appear i c1 -> does_not_appear i c2
    -> does_not_appear i (OR c1 c2)
| dna_NOT : forall (c : cpred), does_not_appear i c
                           -> does_not_appear i (NOT c).



Lemma does_not_appear_preserves_translate_cpred (i : nat) (b : bool) (c : cpred) (m : creg):
  does_not_appear i c ->
  translate_cpred c (m : creg) = translate_cpred c (<[i:=b]> m : creg).
Proof. intros H.
  induction H; auto; simpl.
  - setoid_rewrite lookup_insert_ne; auto.
  - rewrite <- IHdoes_not_appear1, <- IHdoes_not_appear2. auto.
  - rewrite <- IHdoes_not_appear1, <- IHdoes_not_appear2. auto.
  - rewrite <- IHdoes_not_appear. auto.
Qed.

Lemma pivots_normalize_nil start {n} :
  @pivots_normalize start n [] = [].
Proof.
  unfold pivots_normalize.
  remember (_ ++ _) as l eqn:Hl.
  clear Hl.
  assert (Hnil : forall m, (loop_normalization l m n [] []) = ([],[])). 1:{
    revert l; induction n; intros l m; [done|].
    cbn.
    done.
  }
  unfold loop_normalization_final.
  rewrite Hnil.
  done.
Qed.

Definition apply_MEAS' {n} i b (lt : list (TType n)) :=
  match lt with
  | [] => []
  | _ => apply_MEAS i b lt
  end.

Lemma apply_MEAS'_eq {n} i b (lt : list (TType n)) :
  apply_MEAS' i b lt =
  if decide (length lt = 0%nat) then
    []
  else apply_MEAS i b lt.
Proof.
  destruct lt; done.
Qed.

Lemma Forall_vecSatisfies_Zprojector_plus_apply_MEAS'_true (n : nat) (lt : list (TType n)) (q : nat) (H : (q <? n) = true) (WF_L_lt : WF_L lt) (cq : creg * Vector (2 ^ n)) (H2 : WF_Matrix cq.2) (E : cq.2 ≠ Zero) (H3 : Forall (λ t : TType n, vecSatisfies cq.2 (translate t)) lt) (H' : (q < n)%nat) (H1 : WF_Matrix (Zprojector_plus n q × cq.2)) (E' : Zprojector_plus n q × cq.2 ≠ Zero) :
  Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
    (apply_MEAS' q true lt).
Proof.
  rewrite apply_MEAS'_eq.
  case_decide as len_lt.
  1:{
    constructor.
  }
  simpl.
        pose (pivots_normalize_first_qubit_ok q lt WF_L_lt len_lt H') as G.
        unfold FirstQubitNormalized_out in G.
        assert (temp: nth 0 (drop q (List.seq 0 n) ++ take q (List.seq 0 n)) 0%nat = q).
        { rewrite app_nth1. rewrite nth_skipn. rewrite Nat.add_0_r. rewrite seq_nth. lia. lia.
          rewrite skipn_length. rewrite seq_length. lia. }
        rewrite ! temp in G.
        destruct (pivot_search (pivots_normalize q lt) q) eqn:G';
          destruct (pivot_term q (pivots_normalize q lt)) eqn:G'';
          try contradiction.
        -- apply Forall_cons.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_plus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              specialize (H3 x H4). specialize (G x H4). unfold entry in G.
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_plus_eigenvector_IZ; auto; try lia.
              apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H4). auto.
              unfold isIZ, entry. rewrite G; auto.
              unfold vecSatisfies in H3. destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- assert (temp': pivot_search (pivots_normalize q lt) q = gX
     ∨ pivot_search (pivots_normalize q lt) q = gY) by auto.
          pose (pivots_normalize_XY_pivot_term_not_in_filtered_snd q lt WF_L_lt len_lt H' t G'' temp') as e.
          fold (@drop_q n q).
          constructor.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_plus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              assert (H5: In x (normalize q lt)).
              { unfold normalize. rewrite in_map_iff in *. setoid_rewrite filter_In in H4.
                destruct H4 as [x0 [x02x [inx0 drop_qqx0]]].
                exists x0. auto. }
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_plus_eigenvector_IZ; auto; try lia.
              clear e. apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H5). auto.
              apply G; auto. intro. subst. contradiction.
              unfold vecSatisfies in H3. specialize (H3 x H5). destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- assert (temp': pivot_search (pivots_normalize q lt) q = gX
     ∨ pivot_search (pivots_normalize q lt) q = gY) by auto.
          pose (pivots_normalize_XY_pivot_term_not_in_filtered_snd q lt WF_L_lt len_lt H' t G'' temp') as e.
          fold (@drop_q n q).
          constructor.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_plus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              assert (H5: In x (normalize q lt)).
              { unfold normalize. rewrite in_map_iff in *. setoid_rewrite filter_In in H4.
                destruct H4 as [x0 [x02x [inx0 drop_qqx0]]].
                exists x0. auto. }
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_plus_eigenvector_IZ; auto; try lia.
              clear e. apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H5). auto.
              apply G; auto. intro. subst. contradiction.
              unfold vecSatisfies in H3. specialize (H3 x H5). destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- apply Forall_cons.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_plus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              specialize (H3 x H4). specialize (G x H4). unfold entry in G.
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_plus_eigenvector_IZ; auto; try lia.
              apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H4). auto.
              unfold isIZ, entry.
              destruct (Classical_Prop.classic (x = t)).
              subst. unfold pivot_search, pivot_term in *.
              destruct (find
                          (λ qt : option nat * TType n,
                              match qt.1 with
                              | Some q0 => (q =? q0)%nat
                              | None => false
                              end) (pivots_normalize q lt)) eqn:E''; try discriminate.
              inversion G''. rewrite G'. auto.
              rewrite G; auto.
              unfold vecSatisfies in H3. destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
Qed.

Lemma Forall_vecSatisfies_Zprojector_minus_apply_MEAS'_false (n : nat) (lt : list (TType n)) (q : nat) (H : (q <? n) = true) (WF_L_lt : WF_L lt) (cq : creg * Vector (2 ^ n)) (H2 : WF_Matrix cq.2) (E : cq.2 ≠ Zero) (H3 : Forall (λ t : TType n, vecSatisfies cq.2 (translate t)) lt) (H' : (q < n)%nat) (H1 : WF_Matrix (Zprojector_minus n q × cq.2)) (E' : Zprojector_minus n q × cq.2 ≠ Zero) :
  Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t))
    (apply_MEAS' q false lt).
Proof.
  rewrite apply_MEAS'_eq.
  case_decide as len_lt.
  1:{
    constructor.
  }
  simpl.
        pose (pivots_normalize_first_qubit_ok q lt WF_L_lt len_lt H') as G.
        unfold FirstQubitNormalized_out in G.
        assert (temp: nth 0 (drop q (List.seq 0 n) ++ take q (List.seq 0 n)) 0%nat = q).
        { rewrite app_nth1. rewrite nth_skipn. rewrite Nat.add_0_r. rewrite seq_nth. lia. lia.
          rewrite skipn_length. rewrite seq_length. lia. }
        rewrite ! temp in G.
        destruct (pivot_search (pivots_normalize q lt) q) eqn:G';
          destruct (pivot_term q (pivots_normalize q lt)) eqn:G'';
          try contradiction.
        -- apply Forall_cons.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_minus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              specialize (H3 x H4). specialize (G x H4). unfold entry in G.
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_minus_eigenvector_IZ; auto; try lia.
              apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H4). auto.
              unfold isIZ, entry. rewrite G; auto.
              unfold vecSatisfies in H3. destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- assert (temp': pivot_search (pivots_normalize q lt) q = gX
     ∨ pivot_search (pivots_normalize q lt) q = gY) by auto.
          pose (pivots_normalize_XY_pivot_term_not_in_filtered_snd q lt WF_L_lt len_lt H' t G'' temp') as e.
          fold (@drop_q n q).
          constructor.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_minus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              assert (H5: In x (normalize q lt)).
              { unfold normalize. rewrite in_map_iff in *. setoid_rewrite filter_In in H4.
                destruct H4 as [x0 [x02x [inx0 drop_qqx0]]].
                exists x0. auto. }
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_minus_eigenvector_IZ; auto; try lia.
              clear e. apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H5). auto.
              apply G; auto. intro. subst. contradiction.
              unfold vecSatisfies in H3. specialize (H3 x H5). destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- assert (temp': pivot_search (pivots_normalize q lt) q = gX
     ∨ pivot_search (pivots_normalize q lt) q = gY) by auto.
          pose (pivots_normalize_XY_pivot_term_not_in_filtered_snd q lt WF_L_lt len_lt H' t G'' temp') as e.
          fold (@drop_q n q).
          constructor.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_minus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              assert (H5: In x (normalize q lt)).
              { unfold normalize. rewrite in_map_iff in *. setoid_rewrite filter_In in H4.
                destruct H4 as [x0 [x02x [inx0 drop_qqx0]]].
                exists x0. auto. }
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_minus_eigenvector_IZ; auto; try lia.
              clear e. apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H5). auto.
              apply G; auto. intro. subst. contradiction.
              unfold vecSatisfies in H3. specialize (H3 x H5). destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
        -- apply Forall_cons.
           ++ unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l. apply Zi_Zprojector_minus_eigenvector.
           ++ apply (Forall_vecSatisfies_normalize q lt cq.2 WF_L_lt H2) in H3.
              rewrite Forall_forall in *. intros x H4.
              specialize (H3 x H4). specialize (G x H4). unfold entry in G.
              unfold vecSatisfies. split; auto with wf_db.
              unfold Eigenvectors.Eigenpair. simpl. rewrite Mscale_1_l.
              apply translate_Zprojector_minus_eigenvector_IZ; auto; try lia.
              apply normalize_preserves_WF_L with (q := q) in WF_L_lt.
              unfold WF_L in *.
              rewrite Forall_forall in WF_L_lt.
              specialize (WF_L_lt x H4). auto.
              unfold isIZ, entry.
              destruct (Classical_Prop.classic (x = t)).
              subst. unfold pivot_search, pivot_term in *.
              destruct (find
                          (λ qt : option nat * TType n,
                              match qt.1 with
                              | Some q0 => (q =? q0)%nat
                              | None => false
                              end) (pivots_normalize q lt)) eqn:E''; try discriminate.
              inversion G''. rewrite G'. auto.
              rewrite G; auto.
              unfold vecSatisfies in H3. destruct H3.
              unfold Eigenvectors.Eigenpair in H3. simpl in H3.
              rewrite Mscale_1_l in H3. auto.
Qed.


Lemma MEAS_RULE {n} (A : cpred) (lt : list (TType n)) (q i : nat):
(q < n)%nat -> WF_L lt → does_not_appear i A ->

{{{
[

(A, lt)

]
 }}} MEAS q i {{{
[

(AND A (REG i true), apply_MEAS' q true lt);

(AND A (REG i false), apply_MEAS' q false lt)

]
 }}}.
Proof. unfold Mtriple.
  intros H WF_L_lt H0 a H1 cq H2 H3 cq' H4.
  remember H as H'. clear HeqH'.
  unfold In in H1.
  unfold In.
  simpl in H4.
  rewrite kill_false in H1.
  symmetry in H1. subst.
  rewrite <- Nat.ltb_lt in H.
  rewrite H in H4.
  setoid_rewrite kill_false.
  destruct H4.
  - symmetry in H1.
    subst.
    exists (AND A (REG i true), apply_MEAS' q true lt).
    split; auto.
    simpl (<[i:=true]> cq.1, Zprojector_plus n q × cq.2).2.
    assert (WF_Matrix (Zprojector_plus n q × cq.2)) by auto with wf_db.
    exists H1.
    unfold cqSatisfiesMbranch in *.
    simpl in H3.
    simpl ((<[i:=true]> cq.1, Zprojector_plus n q × cq.2).2).
    simpl ((AND A (REG i true), apply_MEAS' q true lt).1).
    simpl ((<[i:=true]> cq.1, Zprojector_plus n q × cq.2).1).
    replace ((AND A (REG i true), apply_MEAS' q true lt).2) with (apply_MEAS' q true lt) by auto.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H2 (WF_Zero (2 ^ n) 1)) as [E | E].
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_plus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      rewrite E in E'. rewrite Mmult_0_r in E'. contradiction.
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_plus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      induction H0; simpl in H3.
      * assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        simpl (translate_cpred (AND TRUE (REG i true)) (<[i:=true]> cq.1)).
        rewrite H0.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS'_true; eauto.
      * contradiction.
      * simpl (translate_cpred (AND (REG j b) (REG i true)) (<[i:=true]> cq.1)).
        assert (<[i:=true]> cq.1 !! j = cq.1 !! j).
        { setoid_rewrite lookup_insert_ne; auto. }

        rewrite H4.
        destruct (cq.1 !! j) eqn:E''; try contradiction.
        assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H5.
        rewrite andb_true_r.
        destruct (from_option _ false _); [|auto].
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS'_true; eauto.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        simpl in H3.
        now apply IHdoes_not_appear1.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        assert (<[i:=true]> cq.1 !! i = Some true) as Hcqi.
        { setoid_rewrite lookup_insert. auto. }
        rewrite Hcqi in *.
        change (from_option _ _ (Some true)) with true in *.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction;
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction;
        cbn [orb andb] in *; auto.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        assert (<[i:=true]> cq.1 !! i = Some true) as Hcqi.
        { setoid_rewrite lookup_insert. auto. }
        rewrite Hcqi in *.
        destruct (translate_cpred c cq.1) eqn:E''; try contradiction.
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS'_true; eauto.
  - destruct H1. 2: inversion H1.
    symmetry in H1.
    subst.
    exists (AND A (REG i false), apply_MEAS' q false lt).
    split; auto.
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).2).
    assert (WF_Matrix (Zprojector_minus n q × cq.2)) by auto with wf_db.
    exists H1.
    unfold cqSatisfiesMbranch in *.
    simpl in H3.
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).2).
    simpl ((AND A (REG i false), apply_MEAS' q false lt).1).
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).1).
    replace ((AND A (REG i false), apply_MEAS' q false lt).2) with (apply_MEAS' q false lt) by auto.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H2 (WF_Zero (2 ^ n) 1)) as [E | E].
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_minus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      rewrite E in E'. rewrite Mmult_0_r in E'. contradiction.
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_minus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      induction H0; simpl in H3.
      * simpl (translate_cpred (AND TRUE (REG i false)) (<[i:=false]> cq.1)).
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0.
        replace (if ¬ false
                 then Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS' q false lt)
                 else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS' q false lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS'_false; eauto.
      * contradiction.
      * simpl (translate_cpred _ _) in *.
        assert (<[i:=false]> cq.1 !! j = cq.1 !! j).
        { setoid_rewrite lookup_insert_ne; auto. }
        rewrite H4.
        destruct (cq.1 !! j) eqn:E''; try contradiction.
        assert (<[i:=false]> cq.1 !! i = Some false) as ->.
        { setoid_rewrite lookup_insert. auto. }
        rewrite andb_true_r.
        destruct (from_option _ false _); [|auto].
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS'_false; eauto.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        simpl in H3.
        now apply IHdoes_not_appear1.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        assert (<[i:=false]> cq.1 !! i = Some false) as Hcqi.
        { setoid_rewrite lookup_insert. auto. }
        rewrite Hcqi in *.
        change (from_option _ false _) with true in *.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction;
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction;
        cbn [orb andb] in *; auto.
      * simpl (translate_cpred _ _) in *.
        rewrite <- ! does_not_appear_preserves_translate_cpred in * by auto.
        assert (<[i:=false]> cq.1 !! i = Some false) as Hcqi.
        { setoid_rewrite lookup_insert. auto. }
        rewrite Hcqi in *.
        destruct (translate_cpred c cq.1) eqn:E''; try contradiction.
        clear - n lt q H WF_L_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS'_false; eauto.
Qed.

Lemma triple_RULE {n : nat} (lt lt' : list (TType n)) (cp : cpred) (g : prog) :
  {{ Cap (map TtoA lt) }} g {{ Cap (map TtoA lt') }} ->
  {{{ [ (cp, lt) ] }}} U g {{{ [ (cp, lt')] }}}.
Proof. intros H.
  unfold triple, Mtriple in *.
  intros a H0 cq H1 H2 cq' H3.
  inversion H0.
  2: { inversion H4. }
  symmetry in H4. subst.
  clear H0.
  simpl in *.
  rewrite kill_false in H3.
  symmetry in H3.
  subst.
  exists (cp, lt').
  split. left; auto.
  simpl in *.
  assert (WF_Matrix (translate_prog n g × cq.2)).
  { auto with wf_db. }
  exists H0.
  unfold cqSatisfiesMbranch in *.
  simpl in *.
  specialize (H cq.2).
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H1 (WF_Zero (2 ^ n) 1)) eqn:E;
    destruct (Mat_eq_dec (2 ^ n) 1 (translate_prog n g × cq.2) Zero H0 (WF_Zero (2 ^ n) 1));
    auto.
  rewrite e, Mmult_0_r in n0; contradiction.
  destruct (translate_cpred cp cq.1) eqn:E'; auto.
  assert (WF_Matrix cq.2
          ∧ Forall (λ a0 : AType n, vecSatisfies cq.2 (translateA a0)) (map TtoA lt)).
  { split; auto.
    rewrite Forall_forall in *.
    intros a H3.
    unfold translateA.
    rewrite in_map_iff in H3.
    destruct H3 as [t [H3 H4]].
    symmetry in H3. subst.
    specialize (H2 t H4).
    simpl. rewrite Mplus_0_l. auto. }
  destruct (H H3).
  unfold translateA in H5.
  rewrite Forall_map in H5.
  unfold TtoA in H5.
  simpl in H5.
  setoid_rewrite Mplus_0_l in H5.
  auto.
Qed.

Lemma TRIPLE_RULE {n : nat} (lt lt' : list (TType n)) (cp : cpred) (g : prog) (Q : Predicate n) (la : list (AType n)) :
  {{ Cap (map TtoA lt) }} g {{ Q }} ->
  Q = Cap la ->
  repeat 1%nat (length la) = map length la ->
  lt' = map AtoT la ->
  {{{ [ (cp, lt) ] }}} U g {{{ [ (cp, lt')] }}}.
Proof. intros H H0 H1 H2.
  subst.
  apply triple_RULE.
  assert (map TtoA (map AtoT la) = la).
  { unfold TtoA, AtoT.
    rewrite map_map.
    apply nth_ext with (d := [hd (defaultT_I n) (defaultA_I n)]) (d' := (defaultA_I n)).
    - rewrite map_length. auto.
    - intros n0 H0.
      rewrite map_length in H0.
      rewrite map_nth with (d := (defaultA_I n)).
      destruct (nth n0 la (defaultA_I n)) eqn:E.
      + assert (length (nth n0 la (defaultA_I n)) = 1%nat).
        { rewrite <- map_nth.
          setoid_rewrite <- H1.
          rewrite nth_repeat.
          auto. }
        rewrite E in H2.
        discriminate.
      + simpl in *.
        destruct a; auto.
        assert (length (nth n0 la (defaultA_I n)) = 1%nat).
        { rewrite <- map_nth.
          setoid_rewrite <- H1.
          rewrite nth_repeat.
          auto. }
        rewrite E in H2.
        discriminate. }
  rewrite H0. auto.
Qed.


Lemma cqSatisfiesMbranch_TRUE_weakening {n : nat} (cq : cqstate n) (cp : cpred) (lt : list (TType n)) (H : WF_Matrix cq.2) :
  cqSatisfiesMbranch cq (cp, lt) H -> cqSatisfiesMbranch cq (TRUE, lt) H.
Proof. intros H0.
  unfold cqSatisfiesMbranch in *.
  simpl in *.
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H (WF_Zero (2 ^ n) 1)); auto.
  destruct (translate_cpred cp cq.1); try contradiction; auto.
Qed.

Lemma TRUE_POST_WEAKENING_RULE {n : nat} (mp : mprog) (P Q Q' : MPredicate n) :
  {{{ P }}} mp {{{ Q }}} -> Q' = map (fun x => (TRUE, x.2)) Q ->
  {{{ P }}} mp {{{ Q' }}}.
Proof. intros H H0.
  subst.
  unfold Mtriple in *.
  intros a H0 cq H1 H2 cq' H3.
  destruct (H a H0 cq H1 H2 cq' H3) as [[cp lt] [H4 [H5 H6]]].
  exists (TRUE, lt).
  split.
  rewrite in_map_iff.
  exists (cp, lt); auto.
  exists H5.
  eapply cqSatisfiesMbranch_TRUE_weakening; eauto.
Qed.

Lemma DELETE_REDUNDANCY_RULE {n : nat} (mp : mprog) (P Q : MPredicate n) (x : Mbranch n) :
  {{{ P }}} mp {{{ Q }}} -> hd_error Q = Some x -> Q = repeat x (length Q) ->
  {{{ P }}} mp {{{ [x] }}}.
Proof. intros H H0 H1.
  rewrite H1 in H.
  unfold Mtriple in *.
  intros a H2 cq H3 H4 cq' H5.
  destruct (H a H2 cq H3 H4 cq' H5) as [b [inb [H6 H7]]].
  apply repeat_spec in inb. subst.
  exists x. split. constructor; auto.
  exists H6; auto.
Qed.

Lemma FINALIZE_RULE {n : nat} (mp : mprog) (P Q : MPredicate n) (x : Mbranch n) (lt : list (TType n)) :
  {{{ P }}} mp {{{ Q }}} -> hd_error Q = Some x -> lt = x.2 ->
  map snd Q = repeat lt (length Q) ->
  {{{ P }}} mp {{{ [(TRUE, lt)] }}}.
Proof. intros H H0 H1 H2.
  subst.
  eapply DELETE_REDUNDANCY_RULE.
  eapply TRUE_POST_WEAKENING_RULE.
  apply H.
  auto.
  destruct Q; simpl in *; try discriminate.
  inversion H0; subst; auto.
  rewrite map_length.
  eapply nth_ext.
  rewrite repeat_length, map_length; auto.
  intros n0 H1.
  rewrite map_length in H1.
  rewrite nth_repeat.
  erewrite map_nth.
  f_equal.
  erewrite <- map_nth.
  rewrite H2.
  rewrite nth_repeat.
  auto.
Qed.

Definition equiv_cpred (p p' : cpred) : Prop :=
  (forall (r : creg), translate_cpred p r = translate_cpred p' r).

Lemma equiv_cpred_refl (p : cpred) :
  equiv_cpred p p.
Proof.
  unfold equiv_cpred.
  auto.
Qed.

Lemma equiv_cpred_sym (p p' : cpred) :
  equiv_cpred p p' -> equiv_cpred p' p.
Proof.
  unfold equiv_cpred.
  intros.
  auto.
Qed.

Lemma equiv_cpred_trans (p p' p'' : cpred) :
  equiv_cpred p p' -> equiv_cpred p' p'' -> equiv_cpred p p''.
Proof.
  unfold equiv_cpred.
  intros.
  rewrite H.
  auto.
Qed.

Add Parametric Relation : cpred equiv_cpred
  reflexivity proved by equiv_cpred_refl
  symmetry proved by equiv_cpred_sym
  transitivity proved by equiv_cpred_trans
  as equiv_cpred_setoid.

Definition equiv_cpred_cqSatisfiesMbranch (p p' : cpred) : Prop :=
  (forall {n : nat} (cq : cqstate n) (H : WF_Matrix (snd cq)) (lt : list (TType n)), cqSatisfiesMbranch cq (p, lt) H <-> cqSatisfiesMbranch cq (p', lt) H).

Lemma equiv_cpred_cqSatisfiesMbranch_refl (p : cpred) :
  equiv_cpred_cqSatisfiesMbranch p p.
Proof.
  unfold equiv_cpred_cqSatisfiesMbranch.
  auto.
Qed.

Lemma equiv_cpred_cqSatisfiesMbranch_sym (p p' : cpred) :
  equiv_cpred_cqSatisfiesMbranch p p' -> equiv_cpred_cqSatisfiesMbranch p' p.
Proof.
  unfold equiv_cpred_cqSatisfiesMbranch.
  intros.
  rewrite H.
  auto.
Qed.

Lemma equiv_cpred_cqSatisfiesMbranch_trans (p p' p'' : cpred) :
  equiv_cpred_cqSatisfiesMbranch p p' -> equiv_cpred_cqSatisfiesMbranch p' p'' -> equiv_cpred_cqSatisfiesMbranch p p''.
Proof.
  unfold equiv_cpred_cqSatisfiesMbranch.
  intros.
  rewrite H.
  auto.
Qed.

Add Parametric Relation : cpred equiv_cpred_cqSatisfiesMbranch
  reflexivity proved by equiv_cpred_cqSatisfiesMbranch_refl
  symmetry proved by equiv_cpred_cqSatisfiesMbranch_sym
  transitivity proved by equiv_cpred_cqSatisfiesMbranch_trans
  as equiv_cpred_cqSatisfiesMbranch_setoid.

Lemma cpred_reduce (p p' : cpred) :
  equiv_cpred p p' ->
  equiv_cpred_cqSatisfiesMbranch p p'.
Proof. intros;
  unfold equiv_cpred, equiv_cpred_cqSatisfiesMbranch in *;
  unfold cqSatisfiesMbranch in *;
  simpl in *;
  intros; try rewrite H; auto.
Qed.


#[export] Instance AND_proper : Proper (equiv_cpred ==> equiv_cpred ==> equiv_cpred) AND.
Proof.
  intros c c' Hc d d' Hd m.
  cbn.
  now rewrite <- Hc, <- Hd.
Qed.

#[export] Instance OR_proper : Proper (equiv_cpred ==> equiv_cpred ==> equiv_cpred) OR.
Proof.
  intros c c' Hc d d' Hd m.
  cbn.
  now rewrite <- Hc, <- Hd.
Qed.

#[export] Instance NOT_proper : Proper (equiv_cpred ==> equiv_cpred) NOT.
Proof.
  intros c c' Hc m.
  cbn.
  now rewrite <- Hc.
Qed.

#[export] Instance Equiv_cpred : Equiv cpred := equiv_cpred.

Declare Scope cpred_scope.
Delimit Scope cpred_scope with cpred.
Bind Scope cpred_scope with cpred.

Notation "b && c" := (AND b%cpred c%cpred) : cpred_scope.
Notation "b || c" := (OR b%cpred c%cpred) : cpred_scope.
Notation "¬ b" := (NOT b%cpred) : cpred_scope.
Notation " n ↦ b " := (REG n%nat b%bool) (at level 20) : cpred_scope.

Local Open Scope cpred_scope.

Lemma AND_FALSE_l c : equiv_cpred (AND FALSE c) FALSE.
Proof.
  done.
Qed.

Lemma AND_FALSE_r c : equiv_cpred (AND c FALSE) FALSE.
Proof.
  hnf.
  cbn.
  intros; apply andb_false_r.
Qed.

Lemma AND_TRUE_l c : equiv_cpred (AND TRUE c) c.
Proof.
  done.
Qed.

Lemma AND_TRUE_r c : equiv_cpred (AND c TRUE) c.
Proof.
  hnf.
  cbn.
  intros; apply andb_true_r.
Qed.

Lemma OR_FALSE_l c : equiv_cpred (OR FALSE c) c.
Proof.
  done.
Qed.

Lemma OR_FALSE_r c : equiv_cpred (OR c FALSE) c.
Proof.
  hnf.
  cbn.
  intros; apply orb_false_r.
Qed.

Lemma OR_TRUE_l c : equiv_cpred (OR TRUE c) TRUE.
Proof.
  done.
Qed.

Lemma OR_TRUE_r c : equiv_cpred (OR c TRUE) TRUE.
Proof.
  hnf.
  cbn.
  intros; apply orb_true_r.
Qed.

Lemma AND_OR_l c d e : (c || d) && e ≡ c && e || d && e.
Proof.
  intros m; apply andb_orb_distrib_l.
Qed.

Lemma AND_OR_r c d e : c && (d || e) ≡ c && d || c && e.
Proof.
  intros m; apply andb_orb_distrib_r.
Qed.

#[export] Instance AND_assoc : Assoc (≡) AND.
Proof.
  intros ? ? ? m; apply andb_assoc.
Qed.

#[export] Instance OR_assoc : Assoc (≡) OR.
Proof.
  intros ? ? ? m; apply orb_assoc.
Qed.

Fixpoint ANDS (cs : list cpred) : cpred :=
  match cs with
  | [] => TRUE
  | c :: cs => c && ANDS cs
  end.

Fixpoint ORS (cs : list cpred) : cpred :=
  match cs with
  | [] => FALSE
  | c :: cs => c || ORS cs
  end.

Lemma ANDS_app cs ds : ANDS (cs ++ ds) ≡ ANDS cs && ANDS ds.
Proof.
  induction cs.
  - now rewrite AND_TRUE_l.
  - cbn.
    rewrite IHcs.
    now rewrite (assoc _).
Qed.

Lemma ORS_app cs ds : ORS (cs ++ ds) ≡ ORS cs || ORS ds.
Proof.
  induction cs.
  - now rewrite OR_FALSE_l.
  - cbn.
    rewrite IHcs.
    now rewrite (assoc _).
Qed.

Lemma NOT_AND c d : (¬ (c && d)) ≡ ((¬ c) || ¬ d).
Proof.
  intros m.
  cbn.
  apply negb_andb.
Qed.

Lemma NOT_OR c d : (¬ (c || d)) ≡ ((¬ c) && ¬ d).
Proof.
  intros m.
  cbn.
  apply negb_orb.
Qed.

Lemma NOT_ANDS cs : (¬ ANDS cs) ≡ ORS (NOT <$> cs).
Proof.
  induction cs.
  - cbn.
    done.
  - cbn.
    rewrite NOT_AND, IHcs.
    done.
Qed.

Lemma NOT_ORS cs : (¬ ORS cs) ≡ ANDS (NOT <$> cs).
Proof.
  induction cs.
  - cbn.
    done.
  - cbn.
    rewrite NOT_OR, IHcs.
    done.
Qed.

Lemma NOT_NOT c : NOT (NOT c) ≡ c.
Proof.
  intros m; apply negb_involutive.
Qed.

#[export] Instance ANDS_proper : Proper (Forall2 (≡) ==> (≡)) ANDS.
Proof.
  intros cs ds Heq.
  induction Heq; [done|].
  cbn.
  f_equiv; auto.
Qed.

#[export] Instance ORS_proper : Proper (Forall2 (≡) ==> (≡)) ORS.
Proof.
  intros cs ds Heq.
  induction Heq; [done|].
  cbn.
  f_equiv; auto.
Qed.

#[export] Instance AND_comm : Comm (≡) AND.
Proof.
  intros c d m; cbn; Btauto.btauto.
Qed.

#[export] Instance OR_comm : Comm (≡) OR.
Proof.
  intros c d m; cbn; Btauto.btauto.
Qed.


#[export] Instance AND_idemp : IdemP (≡) AND.
Proof.
  intros c m; cbn; Btauto.btauto.
Qed.

#[export] Instance OR_idemp : IdemP (≡) OR.
Proof.
  intros c m; cbn; Btauto.btauto.
Qed.

Ltac bsolve_setup :=
  (repeat intros ?);
  cbn.

Ltac bsolve_case :=
  (repeat destruct (_ !! _));
  cbn;
  unfold eqb.

Ltac bsolve_solve :=
  Btauto.btauto.

Ltac bsolve :=
  bsolve_setup; bsolve_case; bsolve_solve.


Lemma ORS_fmap_AND_l {A} (f : A -> cpred) (c : cpred) (l : list A) :
  ORS ((λ a, c && f a) <$> l) ≡ c && ORS (f <$> l).
Proof.
  induction l; [bsolve|].
  cbn.
  rewrite IHl.
  bsolve.
Qed.

Definition IMPL (c d : cpred) :=
  NOT c || d.

Definition IFF (c d : cpred) :=
  IMPL c d && IMPL d c.

#[export] Instance IMPL_proper : Proper ((≡) ==> (≡) ==> (≡)) IMPL.
Proof.
  unfold IMPL.
  solve_proper.
Qed.

#[export] Instance IFF_proper : Proper ((≡) ==> (≡) ==> (≡)) IFF.
Proof.
  unfold IFF.
  solve_proper.
Qed.

Lemma IMPL_correct' c d r : translate_cpred (IMPL c d) r <->
  (translate_cpred c r -> translate_cpred d r).
Proof.
  cbn.
  rewrite 3 Is_true_true.
  split.
  - intros Hcd Hc.
    rewrite Hc in Hcd.
    rewrite <- Hcd.
    Btauto.btauto.
  - intros Hcd.
    destruct (translate_cpred c r); [|done].
    cbn.
    auto.
Qed.

Lemma IFF_correct' c d r : translate_cpred (IFF c d) r ->
  translate_cpred c r <-> translate_cpred d r.
Proof.
  cbn.
  rewrite andb_True.
  intros []; split; now apply IMPL_correct'.
Qed.

Lemma IFF_correct c d : IFF c d ≡ TRUE <-> c ≡ d.
Proof.
  split; [|intros ->; bsolve].
  intros Hcd m.
  apply Bool.eq_iff_eq_true.
  rewrite <- 2 Is_true_true.
  apply IFF_correct'.
  rewrite Hcd.
  done.
Qed.

Lemma ORS_permutation cs ds : cs ≡ₚ ds -> ORS cs ≡ ORS ds.
Proof.
  intros Hcd.
  induction Hcd; cbn; repeat_on_hyps ltac:(fun H => rewrite H); done || bsolve.
Qed.

Lemma ORS_correct' cs r : translate_cpred (ORS cs) r <-> Exists (λ c, translate_cpred c r) cs.
Proof.
  induction cs.
  - easy.
  - cbn.
    rewrite orb_True.
    rewrite Exists_cons.
    now f_equiv.
Qed.


Lemma ORS_seteq cs ds : (forall c, c ∈ cs <-> c ∈ ds) -> ORS cs ≡ ORS ds.
Proof.
  intros Hcd r.
  apply Bool.eq_iff_eq_true.
  rewrite <- 2 Is_true_true.
  rewrite 2 ORS_correct'.
  rewrite 2 list.Exists_exists.
  naive_solver.
Qed.

Lemma ORS_subset cs ds : cs ⊆ ds -> IMPL (ORS cs) (ORS ds) ≡ TRUE.
Proof.
  intros Hcd r.
  apply Bool.eq_iff_eq_true.
  rewrite <- 2 Is_true_true.
  rewrite IMPL_correct', 2 ORS_correct'.
  split; [done|].
  intros _.
  rewrite 2 list.Exists_exists.
  naive_solver.
Qed.

Lemma AND_TRUE c d : c && d ≡ TRUE <-> c ≡ TRUE /\ d ≡ TRUE.
Proof.
  split; [|intros [-> ->]; bsolve].
  intros Hcd.
  split; intros m;
  specialize (Hcd m); cbn in *;
  rewrite andb_true_iff in Hcd;
  easy.
Qed.

Section btauto.

Import btauto.Algebra btauto.Reflect.

Definition bcons (b : bool) (p : positive) :=
  if b then xI p else xO p.

Declare Scope formula_scope.
Delimit Scope formula_scope with formula.
Bind Scope formula_scope with formula.

Notation "a && b" := (formula_cnj a%formula b%formula) : formula_scope.
Notation "a || b" := (formula_dsj a%formula b%formula) : formula_scope.
Notation "a ⊗ b" := (formula_xor a%formula b%formula) : formula_scope.
Notation "a ? b : c" := (formula_ifb a%formula b%formula c%formula)
  (at level 60) : formula_scope.
Notation "¬ a" := (formula_neg a%formula) : formula_scope.
Notation "# a" := (formula_var a%positive) (at level 20) : formula_scope.

Definition formula_impl (a b : formula) : formula :=
  (¬ a) || b.

Notation "a -> b" := (formula_impl a%formula b%formula) : formula_scope.
Notation "⊤" := (formula_top) : formula_scope.
Notation "⊥" := (formula_btm) : formula_scope.

Definition list_index `{EqDecision A} (a : A) (l : list A) : option nat :=
  fst <$> list_find (.= a) l.

Lemma list_index_spec `{EqDecision A} (a : A) l i :
  list_index a l = Some i <->
  l !! i = Some a /\ a ∉ take i l.
Proof.
  unfold list_index.
  revert i; induction l as [|a' l IHl]; intros i; [easy|].
  cbn.
  case_decide as Ha'.
  - subst.
    cbn.
    destruct i; [easy|].
    split; [easy|].
    cbn.
    intros [_ HF]; exfalso; apply HF; constructor.
  - rewrite <- option_fmap_compose.
    unfold compose; simpl.
    setoid_rewrite (option_fmap_compose fst s).
    rewrite fmap_Some.
    setoid_rewrite IHl.
    clear IHl.
    split.
    + intros (i' & (Hli' & Ha) & ->).
      cbn.
      rewrite not_elem_of_cons.
      easy.
    + destruct i as [|i']; [cbn; intros []; congruence|].
      cbn.
      rewrite not_elem_of_cons.
      intros [? [? ?]].
      eauto.
Qed.

Lemma list_index_is_Some `{EqDecision A} (a : A) l : a ∈ l ->
  is_Some (list_index a l).
Proof.
  unfold list_index.
  rewrite fmap_is_Some.
  intros Ha.
  now apply (list_find_elem_of _ _ _ Ha).
Qed.

Fixpoint cpred_formula (vars : list nat) (c : cpred) : formula :=
  match c with
  | TRUE => ⊤
  | FALSE => ⊥
  | REG n b => # (bcons b (default xH (Pos.of_succ_nat <$> list_index n vars)))
  | AND a b => cpred_formula vars a && cpred_formula vars b
  | OR a b => cpred_formula vars a || cpred_formula vars b
  | NOT a => ¬ cpred_formula vars a
  end.

Definition cpred_vars_facts (vars : list nat) : formula :=
  foldr formula_cnj formula_top (imap (λ i _,
    ¬ (# (xI (Pos.of_succ_nat i)) && # xO (Pos.of_succ_nat i)))%formula vars).

Definition cpred_sat_formula (vars : list nat) (c : cpred) : formula :=
  cpred_vars_facts vars -> cpred_formula vars c.


Definition cpred_vars_state (vars : list nat) (m : creg) : list bool :=
  (false ::.) $
  concat ((λ n,
    [bool_decide (m !! n = Some false);bool_decide (m !! n = Some true)])
    <$> vars).

Lemma nat_mod_2_eq_oddb n :
  n mod 2 = Nat.b2n (Nat.odd n).
Proof.
  unfold Nat.odd.
  rewrite Modulus.even_eqb.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hnmod.
  destruct (n mod 2) as [|[|]]; [done..|lia].
Qed.

Lemma lookup_cpred_vars_state_aux vars m i b :
  cpred_vars_state vars m !! (s (2 * i + Nat.b2n b)) =
  n ← vars !! i;
  Some (bool_decide (m !! n = Some b)).
Proof.
  revert i b.
  induction vars as [|v vars IHvars]; [easy|].
  intros i b.
  destruct i as [|i]; [now destruct b|].
  cbn.
  setoid_rewrite lookup_cons_ne_0; [|lia].
  replace (pred _) with (2 * i + Nat.b2n b)%nat by lia.
  apply IHvars.
Qed.

Lemma list_nth_lookup {A} (p : positive) (l : list A) (d : A) :
  list_nth p l d = default d (l !! (pred (Pos.to_nat p))).
Proof.
  unfold list_nth.
  revert l;
  induction p using Pos.peano_rect; intros l.
  - destruct l; done.
  - rewrite Pos.peano_rect_succ.
    destruct l.
    + done.
    + rewrite IHp.
      rewrite lookup_cons_ne_0 by lia.
      do 2 f_equal; lia.
Qed.


Lemma list_nth_cpred_vars_state_aux vars m p d :
  list_nth p (cpred_vars_state vars m) d =
  default d (match p with
    | xH => Some false
    | xI p => n ← vars !! (pred (Pos.to_nat p));
      Some (bool_decide ((m !! n) = Some true))
    | xO p => n ← vars !! (pred (Pos.to_nat p));
      Some (bool_decide ((m !! n) = Some false))
    end).
Proof.
  rewrite list_nth_lookup.
  destruct p.
  - replace (pred (Pos.to_nat p~1)) with (s (2 * pred (Pos.to_nat p) + Nat.b2n true)) by (cbn; lia).
    rewrite lookup_cpred_vars_state_aux.
    done.
  - replace (pred (Pos.to_nat p~0)) with (s (2 * pred (Pos.to_nat p) + Nat.b2n false)) by (cbn; lia).
    rewrite lookup_cpred_vars_state_aux.
    done.
  - done.
Qed.

Fixpoint cpred_supp (c : cpred) : gset nat :=
  match c with
  | TRUE | FALSE => ∅
  | REG n _ => {[n]}
  | AND c d => cpred_supp c ∪ cpred_supp d
  | OR c d => cpred_supp c ∪ cpred_supp d
  | NOT c => cpred_supp c
  end.

Lemma formula_eval_cpred vars m c :
  set_Forall (.∈ vars) (cpred_supp c) ->
  formula_eval (cpred_vars_state vars m) (cpred_formula vars c) =
  translate_cpred c m.
Proof.
  induction c as [| | n b | a IHa b IHb | a IHa b IHb | a IHa ].
  - done.
  - done.
  - cbn.
    rewrite set_Forall_singleton.
    intros Hn.
    apply list_index_is_Some in Hn as (i & Hi).
    apply list_index_spec in Hi as Hi'.
    destruct Hi' as [Hi' _].
    rewrite Hi.
    cbn.
    rewrite list_nth_lookup.
    replace (pred _) with (s (2 * i + Nat.b2n b))%nat by (destruct b; cbn; lia).
    rewrite lookup_cpred_vars_state_aux.
    rewrite Hi'.
    cbn.
    destruct (m !! n) as [[]|]; destruct b; reflexivity.
  - cbn.
    intros Hsupp.
    now rewrite IHa, IHb by set_solver + Hsupp.
  - cbn.
    intros Hsupp.
    now rewrite IHa, IHb by set_solver + Hsupp.
  - cbn.
    now intros ->%IHa.
Qed.

Lemma cpred_btauto_helper_lemma (c d : cpred) :
  let vars := elements (cpred_supp c ∪ cpred_supp d) in
  reduce (poly_add (poly_of_formula (cpred_formula vars c))
    (poly_of_formula (cpred_formula vars d))) = Cst false ->
  c ≡ d.
Proof.
  intros vars Heq m.
  apply (reduce_poly_of_formula_sound_alt (cpred_vars_state vars m)) in Heq.
  now rewrite 2 formula_eval_cpred in Heq by set_solver +.
Qed.


Lemma formula_eval_cpred_vars_facts vars' vars m :
  formula_eval (cpred_vars_state vars' m) (cpred_vars_facts vars) =
  true.
Proof.
  unfold cpred_vars_facts.
  change (imap ?f) with (imap (f ∘ Nat.add 0)).
  generalize O as n.
  induction vars as [|v vars IHvars]; [done|].
  intros n.
  cbn [imap foldr formula_eval cpred_vars_state compose].
  rewrite (imap_ext _ ((λ i _ : nat,
             (¬ # (Pos.of_succ_nat i)~1 &&
                # (Pos.of_succ_nat i)~0)%formula) ∘ Nat.add (s n))) by
    (intros; cbn; do 3 f_equal; lia).
  rewrite IHvars.
  rewrite 2 list_nth_cpred_vars_state_aux.
  destruct (vars' !! _); [|done].
  cbn.
  destruct (m !! _) as [[]|]; done.
Qed.


Definition cpred_is_tauto (c : cpred) : bool :=
  let vars := elements (cpred_supp c) in
  match reduce (poly_add (poly_of_formula (formula_impl (cpred_vars_facts vars) (cpred_formula vars c)))
    (poly_of_formula formula_top)) with
  | Cst false => true
  | _ => false
  end.

Lemma cpred_is_tauto_correct c :
  cpred_is_tauto c ->
  c ≡ TRUE.
Proof.
  unfold cpred_is_tauto.
  case_match eqn:Hred; [|easy].
  case_match; [done|].
  intros _.
  intros m.
  apply (reduce_poly_of_formula_sound_alt (cpred_vars_state (elements (cpred_supp c)) m)) in Hred.
  cbn in Hred.
  rewrite formula_eval_cpred in Hred by set_solver +.
  rewrite formula_eval_cpred_vars_facts in Hred.
  done.
Qed.

Definition cpred_is_equiv (c d : cpred) : bool :=
  cpred_is_tauto (IFF c d).

Lemma cpred_is_equiv_correct c d :
  cpred_is_equiv c d ->
  c ≡ d.
Proof.
  intros Hcd.
  apply IFF_correct.
  now apply cpred_is_tauto_correct.
Qed.



End btauto.

Ltac bsolve_btauto :=
  intros; match goal with
    | |- ?R ?c TRUE =>
      refine (cpred_is_tauto_correct c _);
      vm_compute;
      exact Logic.I
    | |- ?R ?c ?d =>
      refine (cpred_is_equiv_correct c d _);
      vm_compute;
      exact Logic.I
    end.






(*

Inductive Forall2' {A B} (P : A -> B -> Prop) (Q : A -> Prop) (R : B -> Prop) :
  list A -> list B -> Prop :=
  (* | Forall2'_nil : Forall2' P Q R [] [] *)
  | Forall2'_left l : Forall Q l -> Forall2' P Q R l []
  | Forall2'_right l' : Forall R l' -> Forall2' P Q R [] l'
  | Forall2'_conj a b l l' : P a b -> Forall2' P Q R l l' -> Forall2' P Q R (a :: l) (b :: l').

Fixpoint forall2'_fun {A B} (P : A -> B -> Prop) (Q : A -> Prop) (R : B -> Prop)
  (l : list A) (l' : list B) : Prop :=
  match l with
  | [] => Forall R l'
  | a :: l =>
    match l' with
    | [] => Forall Q (a :: l)
    | b :: l' => P a b /\ forall2'_fun P Q R l l'
    end
  end.

Lemma forall2'_fun_correct {A B} (P : A -> B -> Prop) (Q : A -> Prop) (R : B -> Prop)
  (l : list A) (l' : list B) :
  forall2'_fun P Q R l l' <-> Forall2' P Q R l l'.
Proof.
  split.
  - revert l'; induction l as [|a l IHl]; intros l'; [now constructor|].
    destruct l' as [|b l']; [now constructor|].
    cbn.
    intros []; constructor; auto.
  - intros Hll'.
    induction Hll'.
    + destruct l; [constructor|].
      done.
    + done.
    + done.
Qed.

#[export] Instance forall2'_fun_dec {A B} (P : A -> B -> Prop) (Q : A -> Prop) (R : B -> Prop)
 `{HP : forall a b, Decision (P a b), HQ : forall a, Decision (Q a),
  HR : forall b, Decision (R b)} :
  forall l l', Decision (forall2'_fun P Q R l l') :=
  fix go l l' :=
  match l with
  | [] => decide (Forall R l')
  | a :: l =>
    match l' with
    | [] => decide (Forall Q (a :: l))
    | b :: l' =>
      and_dec (HP a b) (go l l')
    end
  end.

#[export] Instance Forall2'_dec {A B} (P : A -> B -> Prop) (Q : A -> Prop) (R : B -> Prop)
 `{HP : forall a b, Decision (P a b), HQ : forall a, Decision (Q a),
  HR : forall b, Decision (R b)} :
  forall l l', Decision (Forall2' P Q R l l').
  refine (fun l l' => cast_if (forall2'_fun_dec P Q R l l'));
  abstract (now rewrite <- forall2'_fun_correct).
Defined.

#[export] Instance Forall2'_symm {A} (R : relation A) (P : A -> Prop)
  {HR : Symmetric R} : Symmetric (Forall2' R P P).
Proof.
  intros a b Hab.
  induction Hab.
  - now constructor.
  - now constructor.
  - constructor; [now symmetry|].
    easy.
Qed.

(*
Lemma Forall2'_trans {A} (R : relation A) (P : A -> Prop)
  {HR : Transitive R} : (forall a b, P a -> P b -> R a b) ->
    Transitive (Forall2' R P P).
Proof.
  intros HP a b c Hab Hbc.
  induction Hab as [l Hl| |].
  - rewrite <- forall2'_fun_correct in Hbc.
    cbn in Hbc.
    revert c Hbc.
    induction Hl; [now constructor|].
    intros c Hc.
    destruct Hc.
    + now do 2 constructor.
    + constructor; auto.
  - induction Hbc.
    + now do 2 constructor.
    + now constructor.
    +

  - constructor; [now symmetry|].
    easy.
Qed. *)


(* TODO: Type of regpred specifying info one can have about a reg *)

Inductive regpred :=
  | RPtop
  | RPtrue
  | RPfalse
  | RPnone
  | RPNtrue
  | RPNfalse
  | RPNnone
  | RPbot.


Definition rp_cpred n (r : regpred) : cpred :=
  match r with
  | RPtop => TRUE
  | RPtrue => REG n true
  | RPfalse => REG n false
  | RPnone => ¬ (REG n true || REG n false)
  | RPNtrue => ¬ (n ↦ true)
  | RPNfalse => ¬ (n ↦ false)
  | RPNnone => REG n true || REG n false
  | RPbot => FALSE
  end.

Definition rp_neg (r : regpred) : regpred :=
  match r with
  | RPtop => RPbot
  | RPtrue => RPNtrue
  | RPfalse => RPNfalse
  | RPnone => RPNnone
  | RPNtrue => RPtrue
  | RPNfalse => RPfalse
  | RPNnone => RPnone
  | RPbot => RPtop
  end.

Lemma rp_neg_correct r n :
  rp_cpred n (rp_neg r) ≡ ¬ rp_cpred n r.
Proof.
  destruct r; cbn; bsolve.
Qed.

Definition rp_or (r r' : regpred) : regpred :=
  match r, r' with
  | RPtop, _ => RPtop
  | RPbot, r' => r'
  | _, RPtop => RPtop
  | r, RPbot => r
  | RPtrue, RPtrue => RPtrue
  | RPNtrue, RPNtrue => RPNtrue
  | RPtrue, RPNtrue => RPtop
  | RPNtrue, RPtrue => RPtop

  | RPfalse, RPfalse => RPfalse
  | RPNfalse, RPNfalse => RPNfalse
  | RPfalse, RPNfalse => RPtop
  | RPNfalse, RPfalse => RPtop

  | RPnone, RPnone => RPnone
  | RPNnone, RPNnone => RPNnone
  | RPnone, RPNnone => RPtop
  | RPNnone, RPnone => RPtop

  | RPtrue, RPfalse => RPNnone
  | RPtrue, RPnone => RPNfalse
  | RPtrue, RPNfalse => RPNfalse
  | RPtrue, RPNnone => RPNnone

  | RPfalse, RPtrue => RPNnone
  | RPfalse, RPnone => RPNtrue
  | RPfalse, RPNtrue => RPNtrue
  | RPfalse, RPNnone => RPNnone

  | RPnone, RPtrue => RPNfalse
  | RPnone, RPfalse => RPNtrue
  | RPnone, RPNtrue => RPNtrue
  | RPnone, RPNfalse => RPNfalse

  | RPNtrue, RPfalse => RPNtrue
  | RPNtrue, RPnone => RPNtrue
  | RPNtrue, RPNfalse => RPtop
  | RPNtrue, RPNnone => RPtop

  | RPNfalse, RPtrue => RPNfalse
  | RPNfalse, RPnone => RPNfalse
  | RPNfalse, RPNtrue => RPtop
  | RPNfalse, RPNnone => RPtop

  | RPNnone, RPtrue => RPNnone
  | RPNnone, RPfalse => RPNnone
  | RPNnone, RPNtrue => RPtop
  | RPNnone, RPNfalse => RPtop
  end.

Lemma rp_or_correct r r' n :
  rp_cpred n (rp_or r r') ≡
  rp_cpred n r || rp_cpred n r'.
Proof.
  destruct r, r'; cbn; bsolve.
Qed.

Definition rp_and (r r' : regpred) : regpred :=
  match r, r' with
  | RPtop, r' => r'
  | RPbot, _ => RPbot
  | r, RPtop => r
  | _, RPbot => RPbot
  | RPtrue, RPtrue => RPtrue
  | RPNtrue, RPNtrue => RPNtrue
  | RPtrue, RPNtrue => RPbot
  | RPNtrue, RPtrue => RPbot

  | RPfalse, RPfalse => RPfalse
  | RPNfalse, RPNfalse => RPNfalse
  | RPfalse, RPNfalse => RPbot
  | RPNfalse, RPfalse => RPbot

  | RPnone, RPnone => RPnone
  | RPNnone, RPNnone => RPNnone
  | RPnone, RPNnone => RPbot
  | RPNnone, RPnone => RPbot

  | RPtrue, RPfalse => RPbot
  | RPtrue, RPnone => RPbot
  | RPtrue, RPNfalse => RPtrue
  | RPtrue, RPNnone => RPtrue

  | RPfalse, RPtrue => RPbot
  | RPfalse, RPnone => RPbot
  | RPfalse, RPNtrue => RPfalse
  | RPfalse, RPNnone => RPfalse

  | RPnone, RPtrue => RPbot
  | RPnone, RPfalse => RPbot
  | RPnone, RPNtrue => RPnone
  | RPnone, RPNfalse => RPnone

  | RPNtrue, RPfalse => RPfalse
  | RPNtrue, RPnone => RPnone
  | RPNtrue, RPNfalse => RPnone
  | RPNtrue, RPNnone => RPfalse

  | RPNfalse, RPtrue => RPtrue
  | RPNfalse, RPnone => RPnone
  | RPNfalse, RPNtrue => RPnone
  | RPNfalse, RPNnone => RPtrue

  | RPNnone, RPtrue => RPtrue
  | RPNnone, RPfalse => RPfalse
  | RPNnone, RPNtrue => RPfalse
  | RPNnone, RPNfalse => RPtrue
  end.

Lemma rp_and_correct r r' n :
  rp_cpred n (rp_and r r') ≡
  rp_cpred n r && rp_cpred n r'.
Proof.
  destruct r, r'; cbn; bsolve.
Qed.


Definition rp_impl (r r' : regpred) : bool :=
  match r, r' with
  | _, RPtop => true
  | RPtop, _ => false
  | RPbot, _ => true
  | _, RPbot => false
  | RPtrue, RPtrue => true
  | RPtrue, RPNfalse => true
  | RPtrue, RPNnone => true
  | RPtrue, _ => false

  | RPfalse, RPfalse => true
  | RPfalse, RPNtrue => true
  | RPfalse, RPNnone => true
  | RPfalse, _ => false

  | RPnone, RPnone => true
  | RPnone, RPNtrue => true
  | RPnone, RPNfalse => true
  | RPnone, _ => false

  | RPNtrue, RPNtrue => true
  | RPNtrue, _ => false

  | RPNfalse, RPNfalse => true
  | RPNfalse, _ => false

  | RPNnone, RPNnone => true
  | RPNnone, _ => false
  end.

Lemma rp_impl_correct n r r' :
  rp_impl r r' <-> IMPL (rp_cpred n r) (rp_cpred n r') ≡ TRUE.
Proof.
  Local Ltac contra_with c :=
    intros Heq;
    specialize (Heq c);
    cbn in Heq;
    unfold creg in Heq;
    rewrite ?(lookup_singleton), ?lookup_empty in Heq;
    easy.

  destruct r, r'; cbn;
  try first [split; [|intros _; exact Logic.I]; bsolve|split; [intros []|]];
  first [contra_with ({[n := false]} : creg)|
  contra_with ({[n := true]} : creg)| contra_with (∅ : creg)].
Qed.



#[export] Instance regpred_dec : EqDecision regpred.
Proof.
  intros ? ?.
  hnf.
  decide equality.
Defined.

Notation regcnj := (list regpred).

#[export] Instance cpred_Top : Top cpred := TRUE.
#[export] Instance cpred_Bot : Bottom cpred := FALSE.

Fixpoint rc_cpred_aux (k : nat) (rc : regcnj) : cpred :=
  match rc with
  | [] => ⊤
  | r :: rc => rp_cpred k r && rc_cpred_aux (s k) rc
  end.

Lemma rc_cpred_aux_alt k rc : rc_cpred_aux k rc =
  ANDS (imap (rp_cpred ∘ Nat.add k) rc).
Proof.
  revert k; induction rc; intros k; [easy|].
  cbn.
  rewrite Nat.add_0_r.
  f_equal.
  rewrite IHrc.
  f_equal.
  apply imap_ext; intros; cbn; f_equal; lia.
Qed.

Definition rc_cpred rc :=
  rc_cpred_aux 0 rc.

Definition rc_equiv rc rc' :=
  Forall2' eq (.= RPtop) (.= RPtop) rc rc'.

Lemma rc_cpred_aux_all_top k rc : Forall (.= RPtop) rc ->
  rc_cpred_aux k rc ≡ TRUE.
Proof.
  intros Hrc.
  revert k; induction Hrc as [|_ rc -> _ IHrc]; [easy|]; intros k.
  cbn.
  now rewrite IHrc, AND_TRUE_l.
Qed.

Lemma rc_equiv_correct_aux k rc rc' :
  rc_equiv rc rc' -> rc_cpred_aux k rc ≡ rc_cpred_aux k rc'.
Proof.
  intros Heq.
  revert k; induction Heq; intros k.
  - cbn.
    now rewrite rc_cpred_aux_all_top by done.
  - cbn.
    now rewrite rc_cpred_aux_all_top by done.
  - cbn.
    subst.
    f_equiv; apply IHHeq.
Qed.

#[export] Instance rp_or_comm : Comm eq rp_or.
Proof.
  intros [] []; reflexivity.
Qed.

#[export] Instance rp_and_comm : Comm eq rp_and.
Proof.
  intros [] []; reflexivity.
Qed.

#[export] Instance rp_or_assoc : Assoc eq rp_or.
Proof.
  intros [] [] []; reflexivity.
Qed.

#[export] Instance rp_and_assoc : Assoc eq rp_and.
Proof.
  intros [] [] []; reflexivity.
Qed.

Fixpoint rc_and (rc rc' : regcnj) : regcnj :=
  match rc with
  | [] => rc'
  | r :: rc =>
    match rc' with
    | [] => r :: rc
    | r' :: rc' => rp_and r r' :: rc_and rc rc'
    end
  end.

Lemma rc_and_nil_r rc : rc_and rc [] = rc.
Proof.
  now destruct rc.
Qed.

#[export] Instance rc_and_comm : Comm eq rc_and.
Proof.
  intros rc.
  induction rc; intros rc'.
  - cbn.
    now rewrite rc_and_nil_r.
  - destruct rc'; [done|].
    cbn.
    f_equal.
    + apply (comm _).
    + auto.
Qed.

Lemma rc_and_correct_aux k rc rc' : rc_cpred_aux k (rc_and rc rc') ≡
  rc_cpred_aux k rc && rc_cpred_aux k rc'.
Proof.
  revert k rc'; induction rc as [|r rc IHrc]; [intros k rc'|intros k [|r' rc']].
  - cbn.
    now rewrite AND_TRUE_l.
  - cbn.
    now rewrite AND_TRUE_r.
  - cbn.
    rewrite IHrc.
    rewrite rp_and_correct.
    bsolve.
Qed.


Lemma rc_and_correct rc rc' : rc_cpred (rc_and rc rc') ≡
  rc_cpred rc && rc_cpred rc'.
Proof.
  apply rc_and_correct_aux.
Qed.




Fixpoint rc_or (rc rc' : regcnj) : option regcnj :=
  match rc with
  | [] => if decide (Forall (.= RPtop) rc') then Some [] else None
  | r :: rc =>
    match rc' with
    | [] => if decide (Forall (.= RPtop) (r :: rc)) then Some [] else None
    | r' :: rc' =>
      if decide (r = r') then
        (r::.) <$> rc_or rc rc'
      else
        if decide (rc_equiv rc rc') then
          Some (rp_or r r' :: rc)
        else
          None
    end
  end.

Lemma rc_or_correct_aux k rc rc' rco :
  rc_or rc rc' = Some rco ->
  rc_cpred_aux k rco ≡ rc_cpred_aux k rc || rc_cpred_aux k rc'.
Proof.
  revert k rc' rco; induction rc as [|r rc IHrc]; intros k rc' rco;
    [|destruct rc' as [|r' rc']].
  - cbn.
    case_decide; [|easy].
    intros [= <-].
    cbn.
    now rewrite rc_cpred_aux_all_top by done.
  - cbn -[rc_cpred_aux].
    case_decide; [|easy].
    intros [= <-].
    now rewrite (rc_cpred_aux_all_top _ (_::_)) by done.
  - cbn.
    case_decide as Hrr'; [|case_decide as Hrcrc'].
    + subst.
      rewrite <- AND_OR_r.
      rewrite fmap_Some.
      intros (rco' & Hrco' & ->).
      cbn.
      f_equiv.
      now apply IHrc.
    + intros [= <-].
      rewrite <- (rc_equiv_correct_aux _ _ _ Hrcrc').
      rewrite <- AND_OR_l.
      cbn.
      rewrite rp_or_correct.
      done.
    + easy.
Qed.

Notation regdc := (list regcnj).

Fixpoint rdc_cpred_aux k (rcs : regdc) : cpred :=
  match rcs with
  | [] => ⊥
  | rc :: rcs => rc_cpred_aux k rc || rdc_cpred_aux k rcs
  end.

Definition rdc_cpred rcs := rdc_cpred_aux 0 rcs.

Lemma rdc_cpred_aux_alt k rcs :
  rdc_cpred_aux k rcs = ORS (rc_cpred_aux k <$> rcs).
Proof.
  induction rcs; cbn; [done| congruence].
Qed.

Lemma rdc_cpred_aux_app k rcs rcs' :
  rdc_cpred_aux k (rcs ++ rcs') ≡ rdc_cpred_aux k rcs || rdc_cpred_aux k rcs'.
Proof.
  now rewrite 3 rdc_cpred_aux_alt, fmap_app, ORS_app.
Qed.

Fixpoint rc_or_into (rc : regcnj) (rcs : regdc) : regdc :=
  match rcs with
  | [] => [rc]
  | rc' :: rcs =>
    match rc_or rc rc' with
    | Some rco => rco :: rcs
    | None => rc' :: rc_or_into rc rcs
    end
  end.

Lemma rc_or_into_correct_aux k rc rcs :
  rdc_cpred_aux k (rc_or_into rc rcs) ≡ rdc_cpred_aux k (rc :: rcs).
Proof.
  induction rcs as [|rc' rcs IHrcs]; [done|].
  cbn.
  destruct (rc_or _ _) as [rco|] eqn:Hrco.
  - apply (rc_or_correct_aux k) in Hrco.
    cbn.
    rewrite Hrco.
    bsolve.
  - cbn.
    rewrite IHrcs.
    bsolve.
Qed.

Definition rdc_or (rcs rcs' : regdc) : regdc :=
  foldr rc_or_into rcs' rcs.

Lemma rdc_or_correct_aux k rcs rcs' :
  rdc_cpred_aux k (rdc_or rcs rcs') ≡ rdc_cpred_aux k rcs || rdc_cpred_aux k rcs'.
Proof.
  unfold rdc_or.
  induction rcs; cbn; [easy|].
  rewrite rc_or_into_correct_aux.
  cbn; rewrite IHrcs.
  bsolve.
Qed.

Lemma rc_cpred_aux_exists_bot k rc : Exists (.= RPbot) rc ->
  rc_cpred_aux k rc ≡ FALSE.
Proof.
  intros Hex.
  revert k; induction Hex; intros k.
  - cbn.
    subst.
    easy.
  - cbn.
    rewrite IHHex.
    bsolve.
Qed.

Definition rdc_clean (rcs : regdc) : regdc :=
  base.filter (λ rc, ~ Exists (.= RPbot) rc) rcs.

Lemma rdc_clean_correct_aux k rcs : rdc_cpred_aux k (rdc_clean rcs) ≡ rdc_cpred_aux k rcs.
Proof.
  induction rcs; [done|].
  cbn.
  case_decide as Hex.
  - cbn.
    f_equiv.
    apply IHrcs.
  - rewrite (rc_cpred_aux_exists_bot _ _ Hex).
    apply IHrcs.
Qed.

Fixpoint rdc_and (rcs rcs' : regdc) : regdc :=
  match rcs with
  | [] => []
  | rc :: rcs =>
    rdc_or (rdc_clean (rc_and rc <$> rcs'))
    (rdc_and rcs rcs')
  end.

Lemma rdc_and_correct_aux k rcs rcs' :
  rdc_cpred_aux k (rdc_and rcs rcs') ≡
  rdc_cpred_aux k rcs && rdc_cpred_aux k rcs'.
Proof.
  revert rcs'; induction rcs as [|rc rcs IHrcs]; intros rcs'; [easy|].
  cbn.
  rewrite rdc_or_correct_aux, rdc_clean_correct_aux.
  rewrite IHrcs.
  rewrite AND_OR_l.
  f_equiv.
  clear.
  induction rcs' as [|rc' rcs' IHrcs']; [bsolve|].
  cbn.
  rewrite IHrcs'.
  rewrite rc_and_correct_aux.
  bsolve.
Qed.

Definition rdc_ands (rdcs : list regdc) : regdc :=
  foldr rdc_and [[]] rdcs.

Lemma rdc_ands_correct_aux k rdcs :
  rdc_cpred_aux k (rdc_ands rdcs) ≡
  ANDS (rdc_cpred_aux k <$> rdcs).
Proof.
  unfold rdc_ands.
  induction rdcs; [easy|].
  cbn.
  rewrite rdc_and_correct_aux, IHrdcs.
  done.
Qed.

Lemma rdc_cpred_aux_cons_top k rdc :
  rdc_cpred_aux k (cons RPtop <$> rdc) ≡ rdc_cpred_aux (s k) rdc.
Proof.
  induction rdc; [done|].
  cbn.
  rewrite IHrdc.
  bsolve.
Qed.

Fixpoint rc_not (rc : regcnj) : regdc :=
  match rc with
  | [] => []
  | r :: rc =>
    rc_or_into ([rp_neg r])
      ((RPtop ::.) <$> rc_not rc)
  end.

Lemma rc_not_correct_aux k rc :
  rdc_cpred_aux k (rc_not rc) ≡ ¬ rc_cpred_aux k rc.
Proof.
  revert k; induction rc as [|r rc IHrc]; intros k; [easy|].
  cbn.
  rewrite rc_or_into_correct_aux.
  cbn.
  rewrite rdc_cpred_aux_cons_top.
  rewrite IHrc.
  rewrite rp_neg_correct.
  bsolve.
Qed.


Definition rdc_not (rcs : regdc) : regdc :=
  rdc_ands (rc_not <$> rcs).

Lemma rdc_not_correct_aux k rcs :
  rdc_cpred_aux k (rdc_not rcs) ≡ ¬ rdc_cpred_aux k rcs.
Proof.
  unfold rdc_not.
  rewrite rdc_ands_correct_aux.
  rewrite rdc_cpred_aux_alt.
  rewrite NOT_ORS.
  apply ANDS_proper.
  apply Forall2_fmap, Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros rc _.
  now rewrite rc_not_correct_aux.
Qed.

Fixpoint cpred_rdc (c : cpred) : regdc :=
  match c with
  | TRUE => [[]]
  | FALSE => []
  | REG n b => [replicate n RPtop ++ [if b then RPtrue else RPfalse]]
  | AND a b => rdc_and (cpred_rdc a) (cpred_rdc b)
  | OR a b => rdc_or (cpred_rdc a) (cpred_rdc b)
  | NOT a => rdc_not (cpred_rdc a)
  end.

Lemma rc_cpred_aux_replicate k n rc :
  rc_cpred_aux k (replicate n RPtop ++ rc) ≡
  rc_cpred_aux (k + n) rc.
Proof.
  revert k; induction n; intros k.
  - cbn.
    now rewrite Nat.add_0_r.
  - cbn.
    rewrite AND_TRUE_l.
    rewrite IHn.
    f_equiv; lia.
Qed.

Lemma cpred_rdc_correct c : rdc_cpred (cpred_rdc c) ≡ c.
Proof.
  induction c.
  - done.
  - done.
  - cbn.
    rewrite rc_cpred_aux_replicate.
    cbn.
    destruct b; cbn; bsolve.
  - cbn.
    rewrite rdc_and_correct_aux.
    f_equiv; easy.
  - cbn.
    rewrite rdc_or_correct_aux.
    f_equiv; easy.
  - cbn.
    rewrite rdc_not_correct_aux.
    f_equiv.
    apply IHc.
Qed.

Lemma rp_impl_defn r r' : rp_impl r r' =
  bool_decide (rp_or (rp_neg r) r' = RPtop).
Proof.
  destruct r, r'; reflexivity.
Qed.





Definition cpred_vars_facts' (vars : list nat) : formula :=
  ANDS (imap (λ i _,
    ¬ (# (xI (Pos.of_succ_nat i)) && # xO (Pos.of_succ_nat i)))%formula vars).
*)

(*
Definition dnf_cpred0 n (c : option (option bool)) : cpred :=
  match c with
  | None => TRUE
  | Some None => NOT (REG n true || REG n false)
  | Some (Some b) => REG n b
  end.


Definition dnf_cpred1_aux k (c : list (option (option bool))) : cpred :=
  ANDS (imap (dnf_cpred0 ∘ Nat.add k) c).

Definition dnf_cpred_aux k (c : list (list (option (option bool)))) : cpred :=
  ORS (dnf_cpred1_aux k <$> c).
Definition dnf_cpred1 (c : list (option (option bool))) : cpred :=
  ANDS (imap dnf_cpred0 c).

Definition dnf_cpred (c : list (list (option (option bool)))) : cpred :=
  ORS (dnf_cpred1 <$> c).

Definition dnf_and0 (c d : option (option bool)) : option (option (option bool)) :=
  match c, d with
  | None, None => Some None
  | Some c, None => Some (Some c)
  | None, Some d => Some (Some d)
  | Some c, Some d => _ ← guard (c = d); Some (Some c)
  end.

Fixpoint dnf_and1 (cs ds : list (option (option bool))) : option (list (option (option bool))) :=
  match cs with
  | [] => Some ds
  | c :: cs =>
    match ds with
    | [] => Some (c :: cs)
    | d :: ds =>
      c' ← dnf_and0 c d;
      (c'::.) <$> dnf_and1 cs ds
    end
  end.

Definition dnf_and (cs ds : list (list (option (option bool)))) : list (list (option (option bool))) :=
  omap (uncurry dnf_and1) (list_prod cs ds).

Definition dnf_ands cs := foldr dnf_and [[]] cs.

Definition dnf_not0 (cs : option (option bool)) : list (list (option (option bool))) :=
  match cs with
  | None => []
  | Some None => [[Some (Some true)]; [Some (Some false)]]
  | Some (Some true) => [[Some (Some false)]; [Some None]]
  | Some (Some false) => [[Some (Some true)]; [Some None]]
  end.

Fixpoint dnf_not1 (cs : list (option (option bool))) : list (list (option (option bool))) :=
  match cs with
  | [] => []
  | c :: cs =>
    dnf_not0 c ++
    ((None::.) <$>
      (dnf_not1 cs))
  end.


Definition dnf_not (cs : list (list (option (option bool)))) : list (list (option (option bool))) :=
  dnf_ands (dnf_not1 <$> cs).


Fixpoint cpred_dnf (c : cpred) : list (list (option (option bool))) :=
  match c with
  | TRUE => [[]]
  | FALSE => []
  | REG n b => [replicate n None ++ [Some (Some b)]]
  | AND a b => dnf_and (cpred_dnf a) (cpred_dnf b)
  | OR a b =>
    cpred_dnf a ++ cpred_dnf b
  | NOT a =>
    dnf_not (cpred_dnf a)
  end. (* match c with
  | TRUE => Some [[(true, None)]]
  | FALSE => Some [[(false, None)]]
  | EMPTY => None
  | REG n => Some [[(true, Some n)]]
  | AND a b =>
    intersection_with (λ ds es, Some $ app <$>  ds es) (cpred_dnf a) (cpred_dnf b)
  | OR a b =>
    intersection_with (λ ds es, Some (ds ++ es)) (cpred_dnf a) (cpred_dnf b)
  | NOT a =>
    (fmap (fmap (prod_map negb id)) <$> cpred_dnf a)
  end. *)

Lemma dnf_cpred0_and_dnf_cpred0 n c d :
  dnf_cpred0 n c && dnf_cpred0 n d ≡
  from_option (dnf_cpred0 n) FALSE (dnf_and0 c d).
Proof.
  destruct c as [c|], d as [d|]; [|try destruct c; try destruct d; cbn; intros m;
    cbn; try destruct (m !! n); Btauto.btauto..].
  cbn.
  case_guard as Hcd.
  - subst.
    apply (idemp _).
  - destruct c as [c|], d as [d|]; try congruence;
    (try destruct c; try destruct d); try congruence; cbn;
    intros m;
    cbn; try destruct (m !! n); unfold eqb; cbn; Btauto.btauto.
Qed.

Lemma dnf_cpred_and1_aux k c d :
  equiv_cpred (from_option (dnf_cpred1_aux k) FALSE (dnf_and1 c d))
  (dnf_cpred1_aux k c && dnf_cpred1_aux k d).
Proof.
  revert k d; induction c as [|c cs IHcs]; intros k d.
  - cbn.
    now rewrite AND_TRUE_l.
  - destruct d as [|d ds]; [cbn; now rewrite AND_TRUE_r|].
    cbn.
    rewrite <- (AND_assoc _ _ (_ && _)).
    rewrite (AND_comm (ANDS _) (_ && _)).
    rewrite 2 (AND_assoc _).
    rewrite dnf_cpred0_and_dnf_cpred0.
    destruct (dnf_and0 c d) as [c'|].
    2:{
      cbn.
      now rewrite AND_FALSE_l.
    }
    cbn.
    specialize (IHcs (s k) ds).
    cbv zeta in IHcs.
    unfold compose in *.
    rewrite 2 (imap_ext (λ x, dnf_cpred0 (k + s x)) (λ x, dnf_cpred0 (s k + x))) by now intros; f_equal; lia.
    rewrite <- (AND_assoc _).
    rewrite (AND_comm (ANDS _)).
    rewrite <- IHcs.
    destruct (dnf_and1 cs ds) as [cs'|].
    2:{
      cbn.
      now rewrite AND_FALSE_r.
    }
    cbn.
    f_equiv.
    f_equiv.
    unfold dnf_cpred1_aux.
    erewrite imap_ext; [reflexivity|].
    intros; cbn; f_equal; lia.
Qed.

Lemma dnf_cpred_and1 c d : equiv_cpred (from_option dnf_cpred1 FALSE (dnf_and1 c d))
  (dnf_cpred1 c && dnf_cpred1 d).
Proof.
  rewrite (dnf_cpred_and1_aux 0 c d).
  done.
Qed.

Lemma dnf_cpred_and c d : equiv_cpred (dnf_cpred (dnf_and c d)) (dnf_cpred c && dnf_cpred d).
Proof.
  unfold dnf_cpred, dnf_and.
  revert d;
  induction c as [|a1 c IHc]; intros d.
  * cbn.
    now rewrite AND_FALSE_l.
  * cbn.
    rewrite AND_OR_l.
    rewrite omap_app, fmap_app.
    rewrite ORS_app.
    rewrite IHc.
    f_equiv.
    clear IHc.
    induction d; [cbn; now rewrite AND_FALSE_r|].
    cbn -[omap].
    cbn [omap list_omap uncurry].
    rewrite AND_OR_r.
    rewrite <- dnf_cpred_and1.
    destruct (dnf_and1 _ _) as [a'|].
    2:{
      cbn.
      rewrite OR_FALSE_l.
      apply IHd.
    }
    cbn.
    f_equiv.
    apply IHd.
Qed.

Lemma dnf_cpred_ands cs : equiv_cpred (dnf_cpred (dnf_ands cs)) (ANDS (dnf_cpred <$> cs)).
Proof.
  induction cs; [done|].
  cbn -[dnf_and dnf_cpred].
  rewrite dnf_cpred_and, IHcs.
  done.
Qed.

Lemma dnf_cpred_not0 k c : ORS (dnf_cpred1_aux k <$> dnf_not0 c) ≡ (¬ dnf_cpred0 k c).
Proof.
  destruct c as [[[]|]|];
  [cbn;
  rewrite Nat.add_0_r;
  intros m; cbn; destruct (m !! k); unfold eqb; cbn; Btauto.btauto..|].
  cbn.
  intros m; cbn; Btauto.btauto.
Qed.


Lemma dnf_cpred1_aux_S k c : dnf_cpred1_aux (s k) c =
  ANDS (imap (dnf_cpred0 ∘ Nat.add k ∘ s)%prg c).
Proof.
  unfold dnf_cpred1_aux.
  f_equal.
  apply imap_ext.
  intros; cbn; f_equal; lia.
Qed.

Lemma dnf_cpred_not1_aux k cnj : dnf_cpred_aux k (dnf_not1 cnj) ≡ (¬ dnf_cpred1_aux k cnj).
Proof.
  unfold dnf_cpred1_aux.
  rewrite NOT_ANDS.
  revert k;
  induction cnj as [|c cnj IHcnj]; intros k; [done|].
  cbn.
  specialize (IHcnj (s k)).
  cbn in IHcnj.
  replace (s (k + 0)) with (k + 1)%nat in IHcnj by lia.
  erewrite imap_ext, <- IHcnj; [|now intros; cbn; f_equal; lia].
  clear IHcnj.
  (* remember (match cnj with | [] => dnf_not0 c' | _ :: _ => _ end) as rest eqn:Hrest. *)
  (* clear Hrest. *)
  (* clear. *)
  rewrite Nat.add_0_r.
  rewrite <- dnf_cpred_not0.
  rewrite fmap_app.
  rewrite ORS_app.
  f_equiv.
  unfold dnf_cpred_aux.
  f_equiv.
  rewrite <- list_fmap_compose.
  apply Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros x _.
  cbn.
  rewrite dnf_cpred1_aux_S.
  rewrite AND_TRUE_l.
  done.
Qed.

Lemma dnf_cpred_not c : equiv_cpred (dnf_cpred (dnf_not c)) (¬ dnf_cpred c).
Proof.
  unfold dnf_not.
  rewrite dnf_cpred_ands.
  unfold dnf_cpred at 2.
  rewrite NOT_ORS.
  f_equiv.
  rewrite <- 2 list_fmap_compose.
  apply Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros cnj _.
  cbn.
  apply (dnf_cpred_not1_aux 0).
Qed.

Lemma dnf_cpred1_reg_aux k n b :
  dnf_cpred1_aux k (replicate n None ++ [Some (Some b)]) ≡ REG (k + n) b.
Proof.
  revert k; induction n as [|n IHn]; intros k.
  - cbn.
    apply AND_TRUE_r.
  - cbn.
    rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- IHn.
    rewrite dnf_cpred1_aux_S.
    rewrite AND_TRUE_l.
    done.
Qed.

Lemma dnf_cpred1_reg n b :
  dnf_cpred1 (replicate n None ++ [Some (Some b)]) ≡ REG n b.
Proof.
  apply (dnf_cpred1_reg_aux 0).
Qed.

Lemma dnf_cpred_dnf (c : cpred) : equiv_cpred (dnf_cpred (cpred_dnf c)) c.
Proof.
  induction c.
  - done.
  - done.
  - cbn.
    rewrite OR_FALSE_r.
    apply dnf_cpred1_reg.
  - rewrite <- IHc1, <- IHc2 at 2.
    apply dnf_cpred_and.
  - cbn.
    rewrite fmap_app, ORS_app.
    f_equiv; assumption.
  - cbn [cpred_dnf].
    rewrite dnf_cpred_not.
    now f_equiv.
Qed.


Fixpoint norm_dnf1 (cs : list (option (option bool))) : option (list (option (option bool))) :=
  match cs with
  | [] => None
  | Some c :: cs => Some (Some c :: default [] (norm_dnf1 cs))
  | None :: cs => (None ::.) <$> norm_dnf1 cs
  end.

Fixpoint norm_dnf_aux (cs : list (list (option (option bool)))) :=
  match cs with
  | [] => Some []
  | c :: cs =>
    match norm_dnf1 c with
    | None => None
    | Some c' => (c' ::.) <$> norm_dnf_aux cs
    end
  end.

Definition norm_dnf cs :=
  default [[]] (norm_dnf_aux cs).

Lemma dnf_cpred1_norm_dnf1_aux k cs :
  dnf_cpred1_aux k (default [] (norm_dnf1 cs)) ≡
  dnf_cpred1_aux k cs.
Proof.
  revert k; induction cs as [|c cs IHcs]; intros k; [done|].
  destruct c as [c|].
  - cbn.
    f_equiv.
    rewrite <- 2 dnf_cpred1_aux_S.
    apply IHcs.
  - cbn.
    rewrite AND_TRUE_l.
    rewrite <- dnf_cpred1_aux_S, <- IHcs.
    destruct (norm_dnf1 cs); cbn; [rewrite <- dnf_cpred1_aux_S, AND_TRUE_l|];
    done.
Qed.


Lemma dnf_cpred1_norm_dnf1 cs :
  dnf_cpred1 (default [] (norm_dnf1 cs)) ≡
  dnf_cpred1 cs.
Proof.
  apply (dnf_cpred1_norm_dnf1_aux 0).
Qed.

Lemma dnf_cpred_norm_dnf cs :
  dnf_cpred (norm_dnf cs) ≡ dnf_cpred cs.
Proof.
  unfold dnf_cpred, norm_dnf.
  induction cs; [done|].
  cbn -[dnf_cpred].
  rewrite <- dnf_cpred1_norm_dnf1, <- IHcs.
  case_match.
  - cbn -[dnf_cpred1].
    destruct (norm_dnf_aux _); bsolve.
  - bsolve.
Qed.

Lemma norm_dnf1_None c :
  norm_dnf1 c = None <-> Forall (not ∘ is_Some) c.
Proof.
  induction c as [|c cs IHcs]; [easy|].
  cbn.
  rewrite list.Forall_cons.
  destruct c; [naive_solver|].
  rewrite fmap_None.
  rewrite IHcs.
  split; [|easy].
  split; [|easy].
  now intros [].
Qed.


Lemma dnf_cpred1_aux_TRUE_iff k ds :
  dnf_cpred1_aux k ds ≡ TRUE <-> Forall (not ∘ is_Some) ds.
Proof.
  revert k; induction ds as [|d ds IHds]; intros k; [easy|].
  rewrite list.Forall_cons.
  cbn.
  rewrite <- dnf_cpred1_aux_S.
  rewrite AND_TRUE.
  f_equiv; [|auto].
  destruct d; [|split; [now intros _ [_ [=]]|easy]].
  split; [|naive_solver].
  intros HF.
  exfalso.
  specialize (HF (match o with | Some _ => ∅ | None => {[k := true]} end)).
  revert HF.
  rewrite Nat.add_0_r.
  destruct o; cbn.
  - now setoid_rewrite lookup_empty.
  - setoid_rewrite lookup_insert.
    done.
Qed.

Lemma does_not_appear_preserves_translate_cpred' i c m :
  does_not_appear i c ->
  translate_cpred c m = translate_cpred c (delete i m).
Proof.
  intros Hc.
  induction Hc; cbn; try congruence.
  setoid_rewrite lookup_delete_ne; done.
Qed.

Lemma translate_cpred_dnf_cpred0 n b r :
  translate_cpred (dnf_cpred0 n b) r <->
  from_option (r !! n =.) True b.
Proof.
  destruct b; [|done].
  cbn.
  destruct o as [[]|]; [
    split; [cbn;destruct (r !! n) as [[]|]; cbn; done|cbn; intros ->;done]..|].
  split; [|cbn; intros ->; done].
  cbn.
  destruct (r !! n) as [[]|]; done.
Qed.

(*
Lemma cpred_supp_disj_AND_inj c c' d d' :
  cpred_supp c ∪ cpred_supp c' ## cpred_supp d ∪ cpred_supp d' ->
  c && d ≡ c' && d' ->
  (* ¬ (d ≡ FALSE) *)
  c ≡ c' /\ d ≡ d'. *)

(* Lemma dnf_cpred0_AND_does_not_appear_equiv_iff
  n b b' c d : does_not_appear n c -> does_not_appear n b ->
  dnf_cpred0 n b && c ≡ dnf_cpred0 n b' && d <->
  b = b' /\  *)


(* Lemma REG_AND_dnf_cpred1_aux_equiv_iff *)

(* Lemma norm_dnf1_proper_equiv_aux k cs ds :
  dnf_cpred1_aux k cs ≡ dnf_cpred1_aux k ds ->
  norm_dnf1 cs = norm_dnf1 ds.
Proof.
  revert k ds;
  induction cs as [|c cs IHcs]; intros k ds.
  - cbn.
    intros Hds%symmetry.
    rewrite dnf_cpred1_aux_TRUE_iff in Hds.
    symmetry.
    now apply norm_dnf1_None.
  - destruct ds as [|d ds].
    + rewrite dnf_cpred1_aux_TRUE_iff.
      now rewrite norm_dnf1_None.
    + destruct c as [c|], d as [d|].
      * cbn -[dnf_cpred0].
        rewrite  *)



Definition cpred_impl (c d : cpred) : bool :=
  bool_decide (norm_dnf (cpred_dnf c) ⊆ norm_dnf (cpred_dnf d)).

Lemma list_fmap_subseteq_1 {A B} (f : A -> B) (l l' : list A) :
  l ⊆ l' -> f <$> l ⊆ f <$> l'.
Proof.
  set_solver.
Qed.

Lemma cpred_impl_correct c d : cpred_impl c d ->
  IMPL c d ≡ TRUE.
Proof.
  intros Hcd%bool_decide_spec.
  rewrite <- (dnf_cpred_dnf c), <- (dnf_cpred_dnf d).
  rewrite <- (dnf_cpred_norm_dnf (cpred_dnf c)), <- (dnf_cpred_norm_dnf (cpred_dnf d)).
  apply ORS_subset.
  now apply list_fmap_subseteq_1.
Qed.

#[export] Instance option_relation_dec {A B} (P : A -> B -> Prop)
  (Q : A -> Prop) (R : B -> Prop)
  `{HP : forall a b, Decision (P a b), HQ : forall a, Decision (Q a),
  HR : forall b, Decision (R b)} :
  RelDecision (option_relation P Q R) :=
  fun a b =>
  match a, b with
  | Some a, Some b => _
  | Some a, None => _
  | None, Some b => _
  | None, None => _
  end.



Lemma dnf_cpred0_impl k c c' :
  option_relation eq (λ _, True) (λ _, False) c c' ->
  IMPL (dnf_cpred0 k c) (dnf_cpred0 k c') ≡ TRUE.
Proof.
  destruct c as [c|], c' as [c'|]; cbn; try easy; [intros ->|]; bsolve.
Qed.


Definition cpred_impl' (c d : cpred) : bool :=
  bool_decide (Forall (λ cnj, Exists (λ cnj',
    Forall2' (option_relation eq (λ _, True) (λ _, False))
    (λ _, True) (λ _, False) cnj cnj')
    (norm_dnf (cpred_dnf d)))
    (norm_dnf (cpred_dnf c))).



Lemma dnf_cpred1_aux_impl k cnj cnj' :
  Forall2' (option_relation eq (λ _, True) (λ _, False))
    (λ _, True) (λ _, False) cnj cnj' ->
  IMPL (dnf_cpred1_aux k cnj) (dnf_cpred1_aux k cnj') ≡ TRUE.
Proof.
  intros Hcnj.
  revert k;
  induction Hcnj as [cnj Hcnj|cnj' Hcnj'|c c' cnj cnj' Hc Hcnj IHcnj]; intros k.
  - bsolve.
  - induction Hcnj'; easy.
  - cbn.
    rewrite <- 2 dnf_cpred1_aux_S.
    apply (dnf_cpred0_impl k) in Hc.
    rewrite Nat.add_0_r.
    intros m.
    rewrite <- Is_true_true.
    rewrite IMPL_correct'.
    cbn.
    rewrite 2 andb_True.
    intros [Hcm Hcnjm].
    split.
    + specialize (Hc m).
      rewrite <- Is_true_true, IMPL_correct' in Hc.
      auto.
    + specialize (IHcnj (s k) m).
      rewrite <- Is_true_true, IMPL_correct' in IHcnj.
      auto.
Qed.



Lemma cpred_impl'_correct c d : cpred_impl' c d ->
  IMPL c d ≡ TRUE.
Proof.
  intros Hcd%bool_decide_spec.
  rewrite <- (dnf_cpred_dnf c), <- (dnf_cpred_dnf d).
  rewrite <- (dnf_cpred_norm_dnf (cpred_dnf c)), <- (dnf_cpred_norm_dnf (cpred_dnf d)).
  intros m.
  rewrite <- Is_true_true.
  apply IMPL_correct'.
  unfold dnf_cpred.
  rewrite 2 ORS_correct'.
  rewrite 2 list.Exists_exists.
  intros (_ & (x & -> & Hcx)%elem_of_list_fmap & Hxm).
  rewrite list.Forall_forall in Hcd.
  specialize (Hcd _ Hcx).
  rewrite list.Exists_exists in Hcd.
  destruct Hcd as (y & Hy & Hxy).
  exists (dnf_cpred1 y).
  split; [now apply elem_of_list_fmap_1|].
  revert Hxm.
  apply IMPL_correct'.
  rewrite (dnf_cpred1_aux_impl 0); done.
Qed.

Definition cpred_dec (c d : cpred) : bool :=
  cpred_impl' c d && cpred_impl' d c.

Lemma cpred_dec_correct c d : cpred_dec c d ->
  c ≡ d.
Proof.
  intros Hcd%andb_True.
  apply IFF_correct, AND_TRUE.
  split; now apply cpred_impl'_correct.
Qed.
*)





Lemma SIMPLIFY_CPRED_PRE_RULE (B : cpred) {A : cpred} {n : nat} {lt : list (TType n)} {mp : mprog} {Q : MPredicate n} :
  equiv_cpred A B ->
  {{{ [ (A, lt) ] }}} mp {{{ Q }}}
  <-> {{{ [ (B, lt) ] }}} mp {{{ Q }}}.
Proof. intros; split; intros; unfold Mtriple in *; intros.
  - destruct a.
    inversion H1.
    symmetry in H5.
    inversion H5.
    subst.
    symmetry in H.
    pose (cpred_reduce B A H) as H6.
    unfold equiv_cpred_cqSatisfiesMbranch in H6.
    rewrite H6 in H3.
    assert (In (A, lt) [(A, lt)]).
    { simpl. auto. }
    specialize (H0 (A, lt) H7 cq H2 H3 cq' H4).
    auto.
    inversion H5.
  - destruct a.
    inversion H1.
    symmetry in H5.
    inversion H5.
    subst.
    pose (cpred_reduce A B H) as H6.
    unfold equiv_cpred_cqSatisfiesMbranch in H6.
    rewrite H6 in H3.
    assert (In (B, lt) [(B, lt)]).
    { simpl. auto. }
    specialize (H0 (B, lt) H7 cq H2 H3 cq' H4).
    auto.
    inversion H5.
Qed.

Lemma KILL_AND_REPEAT_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
      {{{ [ (AND (AND A B) B, lt) ] }}} mp {{{ Q }}}
      <-> {{{ [ (AND A B, lt) ] }}} mp {{{ Q }}}.
Proof. apply SIMPLIFY_CPRED_PRE_RULE.
  bsolve.
Qed.

Lemma KILL_FALSE_RULE {n : nat} (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  {{{ [ (FALSE, lt) ] }}} mp {{{ Q }}}.
Proof. unfold Mtriple.
  intros a H cq H0 H1 cq' H2.
  inversion H.
  2: { inversion H3. }
  symmetry in H3.
  subst.
  unfold cqSatisfiesMbranch in H1.
  simpl in H1.
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H0
          (WF_Zero (2 ^ n) 1)) eqn:E; try contradiction.
  pose (apply_mprog_preserves_snd_Zero mp [cq]) as H3.
  assert (Forall (λ cq : creg * Vector (2 ^ n),
          cq.2 = Zero) [cq]).
  { constructor; auto. }
  apply H3 in H4.
  rewrite Forall_forall in H4.
  specialize (H4 cq' H2 ).
  unfold cqSatisfiesMbranch.
  assert (H5: WF_Matrix (snd cq')).
  { eapply apply_mprog_preserves_WF_Matrix.
    apply H0. apply H2. }
  destruct Q; try contradiction.
  exists m.
  split; simpl; auto.
  exists H5.
  destruct (Mat_eq_dec (2 ^ n) 1 cq'.2 Zero H5
     (WF_Zero (2 ^ n) 1)); auto; contradiction.
Qed.

Lemma KILL_FALSE_RULE' {n : nat} (lt : list (TType n)) (mp : mprog) :
  {{{ [ (FALSE, lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_FALSE_RULE. intros. discriminate. Qed.

Lemma KILL_FALSE_RULE'' {n : nat} (mp : mprog) :
  @Mtriple n [ (FALSE,[]) ] mp [(FALSE,[])].
Proof. apply KILL_FALSE_RULE'. Qed.

Lemma KILL_AND_FALSE_R_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  {{{ [ (AND A FALSE, lt) ] }}} mp {{{ Q }}}.
Proof. unfold Mtriple.
  intros a H cq H0 H1 cq' H2.
  inversion H.
  2: { inversion H3. }
  symmetry in H3.
  subst.
  unfold cqSatisfiesMbranch in H1.
  simpl in H1.
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H0
          (WF_Zero (2 ^ n) 1)) eqn:E; try contradiction.
  pose (apply_mprog_preserves_snd_Zero mp [cq]) as H3.
  assert (Forall (λ cq : creg * Vector (2 ^ n),
          cq.2 = Zero) [cq]).
  { constructor; auto. }
  apply H3 in H4.
  rewrite Forall_forall in H4.
  specialize (H4 cq' H2 ).
  unfold cqSatisfiesMbranch.
  assert (H5: WF_Matrix (snd cq')).
  { eapply apply_mprog_preserves_WF_Matrix.
    apply H0. apply H2. }
  destruct Q; try contradiction.
  exists m.
  split; simpl; auto.
  exists H5.
  destruct (Mat_eq_dec (2 ^ n) 1 cq'.2 Zero H5
     (WF_Zero (2 ^ n) 1)); auto; contradiction.
  rewrite andb_false_r in *.
  easy.
Qed.

Lemma KILL_AND_FALSE_R_RULE' {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) :
  {{{ [ (AND A FALSE, lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_AND_FALSE_R_RULE. intro. discriminate. Qed.

Lemma KILL_AND_TF_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
      {{{ [ (AND (AND A B) (NOT B), lt) ] }}} mp {{{ Q }}}.
Proof. apply SIMPLIFY_CPRED_PRE_RULE with FALSE.
  - bsolve.
  - now apply KILL_FALSE_RULE.
Qed.

Lemma KILL_AND_TF_R_RULE' {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) :
      {{{ [ (AND (AND A B) (NOT B), lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_AND_TF_R_RULE. intro. discriminate. Qed.

Lemma KILL_AND_FT_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n)  (H' : Q <> []) :
      {{{ [ (AND (AND A (NOT B)) B, lt) ] }}} mp {{{ Q }}}.
Proof. apply SIMPLIFY_CPRED_PRE_RULE with FALSE.
  - bsolve.
  - now apply KILL_FALSE_RULE.
Qed.

Lemma KILL_AND_FT_R_RULE' {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) :
      {{{ [ (AND (AND A (NOT B)) B, lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_AND_FT_R_RULE. intro. discriminate. Qed.

Lemma REMOVE_LAST_pI_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
  lt <> [] ->
  last lt (defaultT_I n) = (C1, (repeat gI n)) ->
      {{{ [ (A, lt ) ] }}} mp {{{ Q }}} <->
        {{{ [ (A, removelast lt ) ] }}} mp {{{ Q }}}.
Proof. intros H H0.
  split; intros.
  - unfold Mtriple in *.
    intros a H2 cq H3 H4 cq' H5.
    unfold cqSatisfiesMbranch in *.
    inversion H2. 2: { inversion H6. }
    symmetry in H6.
    subst.
    specialize (H1 (A, lt)).
    assert (In (A, lt) [(A, lt)]).
    { simpl; auto. }
    specialize (H1 H6 cq H3).
    simpl in *.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H3
          (WF_Zero (2 ^ n) 1)).
    assert True by auto.
    specialize (H1 H7 cq' H5).
    destruct H1 as [b [inb [H' H'']]].
    exists b. split; auto.
    exists H'.
    destruct (Mat_eq_dec (2 ^ n) 1 cq'.2 Zero H'
     (WF_Zero (2 ^ n) 1)); auto.
    destruct (translate_cpred A cq.1) eqn:E; try contradiction.
    (* destruct b; try contradiction. *)
    assert (Forall
         (λ t : TType n,
            vecSatisfies cq.2 (translate t))
         lt).
    { rewrite @app_removelast_last with (d := (defaultT_I n)) (l := lt); auto.
      rewrite Forall_app.
      split; auto.
      constructor; auto.
      rewrite H0.
      fold (defaultT_I n).
      rewrite translate_defaultT_I.
      apply vecSatisfies_I; auto. }
    auto.
  - unfold Mtriple in *.
    intros a H2 cq H3 H4 cq' H5.
    unfold cqSatisfiesMbranch in *.
    inversion H2. 2: { inversion H6. }
    symmetry in H6.
    subst.
    specialize (H1 (A, removelast lt)).
    assert (In (A, removelast lt) [(A, removelast lt)]).
    { simpl; auto. }
    specialize (H1 H6 cq H3).
    simpl in *.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H3
          (WF_Zero (2 ^ n) 1)).
    assert True by auto.
    specialize (H1 H7 cq' H5).
    destruct H1 as [b [inb [H' H'']]].
    exists b. split; auto.
    exists H'.
    destruct (Mat_eq_dec (2 ^ n) 1 cq'.2 Zero H'
     (WF_Zero (2 ^ n) 1)); auto.
    destruct (translate_cpred A cq.1) eqn:E; try contradiction.
    (* destruct b; try contradiction. *)
    rewrite @app_removelast_last with (d := (defaultT_I n)) (l := lt) in H4; auto.
    rewrite Forall_app in H4.
    destruct H4.
    auto.
Qed.

Lemma REMOVE_LAST_mI_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  n <> 0%nat ->
  lt <> [] ->
  last lt (defaultT_I n) = (- C1, (repeat gI n)) ->
  {{{ [ (A, lt ) ] }}} mp {{{ Q }}}.
Proof. intros H'' H H0.
  unfold Mtriple in *.
  intros a H2 cq H3 H4 cq' H5.
  unfold cqSatisfiesMbranch in *.
  inversion H2. 2: { inversion H1. }
  symmetry in H1.
  subst.
  simpl in *.
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H3
          (WF_Zero (2 ^ n) 1)).
  - pose (apply_mprog_preserves_snd_Zero mp [cq]) as H6.
    assert (Forall (λ cq : creg * Vector (2 ^ n),
                  cq.2 = Zero) [cq]).
    { constructor; auto. }
    apply H6 in H1.
    rewrite Forall_forall in H1.
    specialize (H1 cq' H5).
    assert (H7: WF_Matrix (snd cq')).
    { eapply apply_mprog_preserves_WF_Matrix.
      apply H3. apply H5. }
    destruct Q; try contradiction.
    exists m.
    split; simpl; auto.
    exists H7.
    destruct (Mat_eq_dec (2 ^ n) 1 cq'.2 Zero H7
     (WF_Zero (2 ^ n) 1)); auto; contradiction.
  - destruct (translate_cpred A cq.1) eqn:E; try contradiction.
    (* destruct b; try contradiction. *)
    rewrite @app_removelast_last with (d := (defaultT_I n)) (l := lt) in H4; auto.
    rewrite Forall_app in H4.
    destruct H4.
    inversion H4; subst.
    rewrite H0 in H8.
    unfold vecSatisfies in H8.
    destruct H8.
    unfold Eigenvectors.Eigenpair in H7.
    simpl in H7.
    rewrite Mscale_1_l in H7.
    assert (@translate n (- C1, repeat gI n) = translate (gScaleT (- C1) (defaultT_I n))).
    { unfold translate, defaultT_I, gScaleT.
      simpl. f_equal. lca. }
    rewrite H8 in H7.
    rewrite translate_gScaleT in H7.
    rewrite translate_defaultT_I in H7.
    rewrite Mscale_mult_dist_l in H7.
    rewrite Mmult_1_l in H7.
    assert (cq.2 = Zero).
    { apply Mplus_inj_l with (m := cq.2) in H7.
      assert (cq.2 .+ - C1 .* cq.2 = Zero) by lma'.
      rewrite H10 in H7.
      assert (cq.2 .+ cq.2 = C2 .* cq.2) by lma'.
      rewrite H11 in H7.
      rewrite <- Mscale_0_r with (c := C2) in H7.
      apply Mscale_inj with (c := / C2) in H7.
      rewrite ! Mscale_assoc in H7.
      replace (/ C2 * C2) with C1 in H7 by lca.
      rewrite ! Mscale_1_l in H7.
      auto. }
    contradiction.
    auto.
    apply proper_length_TType_defaultT_I.
    auto.
Qed.

Lemma REMOVE_LAST_mI_RULE' {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) :
  n <> 0%nat ->
  lt <> [] ->
  last lt (defaultT_I n) = (- C1, (repeat gI n)) ->
  {{{ [ (A, lt ) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply REMOVE_LAST_mI_RULE. intros. discriminate. Qed.

Lemma NORMALIZE_RULE {n : nat} (i : nat) (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
  WF_L lt ->
  {{{ [(A,normalize i lt)] }}} mp {{{ Q }}} ->
  {{{ [(A,lt)] }}} mp {{{ Q }}}.
Proof. intros WFLlt H. unfold Mtriple in *.
  intros a H0 cq H1 H2 cq' H3.
  unfold cqSatisfiesMbranch in *.
  specialize (H (A, normalize i lt)).
  assert (In (A, normalize i lt) [(A, normalize i lt)]) by (simpl; auto).
  specialize (H H4 cq H1).
  simpl in *.
  rewrite kill_false in H0.
  symmetry in H0. subst.
  simpl in *.
  assert (if Mat_eq_dec (2 ^ n) 1 cq.2 Zero H1 (WF_Zero (2 ^ n) 1)
       then True
       else
        match translate_cpred A cq.1 with
        | true =>
            Forall (λ t : TType n, vecSatisfies cq.2 (translate t))
              (normalize i lt)
        | _ => False
        end).
  { destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H1 (WF_Zero (2 ^ n) 1)); auto.
    destruct (translate_cpred A cq.1); try contradiction.
    (* destruct b; try contradiction. *)
    apply Forall_vecSatisfies_normalize; auto. }
  specialize (H H0 cq' H3); auto.
Qed.


Lemma ITE_TRUE_RULE {n} (lt : list (TType n)) (C : cpred) (Q : MPredicate n) (p1 p2 : prog) (A : cpred) :
  IMPL A C ≡ TRUE ->
  {{{ [ (A, lt) ] }}} p1 {{{ Q }}} ->
  (* {{{ [ (FALSE, lt) ] }}} p2 {{{ Q }}} -> *)
  {{{ [ (A, lt) ] }}} (ITE C p1 p2) {{{ Q }}}.
Proof.
  intros HAC HA.
  apply ITE_RULE.
  - apply SIMPLIFY_CPRED_PRE_RULE with A; [|done].
    unfold IMPL in HAC.
    rewrite <- (AND_TRUE_l A) at 2.
    rewrite <- HAC.
    bsolve.
  - apply SIMPLIFY_CPRED_PRE_RULE with FALSE.
    + rewrite <- (AND_TRUE_l (_ && _)).
      rewrite <- HAC.
      bsolve.
    + intros b [<-|[]].
      intros cq Hcq.
      specialize (HA (A, lt) ltac:(now left) cq Hcq).
      unfold cqSatisfiesMbranch in HA |- *.
      cbn.
      destruct (Mat_eq_dec _ _ _ _) as [Hcq0|]; [intros _|intros []].
      intros cq' [<-|[]].
      cbn in HA.
      specialize (HA Logic.I _ (or_introl eq_refl)) as (b & Hb & HQb).
      exists b.
      split; [easy|].
      cbn.
      rewrite Hcq0.
      rewrite Mmult_0_r.
      exists (WF_Zero _ _).
      destruct (Mat_eq_dec _ _ _ _ _ _); [|easy].
      easy.
Qed.

Lemma ITE_FALSE_RULE {n} (lt : list (TType n)) (C : cpred) (Q : MPredicate n) (p1 p2 : prog) (A : cpred) :
  IMPL A (¬ C) ≡ TRUE ->
  {{{ [ (A, lt) ] }}} p2 {{{ Q }}} ->
  (* {{{ [ (FALSE, lt) ] }}} p2 {{{ Q }}} -> *)
  {{{ [ (A, lt) ] }}} (ITE C p1 p2) {{{ Q }}}.
Proof.
  intros HAC HA.
  apply ITE_RULE.
  - apply SIMPLIFY_CPRED_PRE_RULE with FALSE.
    + rewrite <- (AND_TRUE_l (_ && _)).
      rewrite <- HAC.
      bsolve.
    + intros b [<-|[]].
      intros cq Hcq.
      specialize (HA (A, lt) ltac:(now left) cq Hcq).
      unfold cqSatisfiesMbranch in HA |- *.
      cbn.
      destruct (Mat_eq_dec _ _ _ _) as [Hcq0|]; [intros _|intros []].
      intros cq' [<-|[]].
      cbn in HA.
      specialize (HA Logic.I _ (or_introl eq_refl)) as (b & Hb & HQb).
      exists b.
      split; [easy|].
      cbn.
      rewrite Hcq0.
      rewrite Mmult_0_r.
      exists (WF_Zero _ _).
      destruct (Mat_eq_dec _ _ _ _ _ _); [|easy].
      easy.
  - apply SIMPLIFY_CPRED_PRE_RULE with A; [|done].
    unfold IMPL in HAC.
    rewrite <- (AND_TRUE_l A) at 2.
    rewrite <- HAC.
    bsolve.
Qed.

Lemma JOIN_RULE {n} (lt lt' : list (TType n)) (A A' : cpred)
  (Q : MPredicate n) (p : mprog) :
  {{{[(A, lt)] }}} p {{{Q}}} ->
  {{{[(A', lt')] }}} p {{{Q}}} ->
  {{{[(A,lt); (A',lt')] }}} p {{{Q}}}.
Proof.
  unfold Mtriple.
  naive_solver.
Qed.

(* Lemma ITE_JOIN_RULE {n} (lt : list (TType n)) (C : cpred)
  (Q : MPredicate n) (p1 p2 : prog) (A : cpred) :
  {{{ [ (A && C, lt) ] }}} p1 {{{ Q }}} ->
  {{{ [ (A && ¬ C, lt) ] }}} p2 {{{ Q }}} ->
  {{{ [ (A, lt) ] }}} (ITE C p1 p2) {{{ Q }}}.
Proof.
  intros Hp1 Hp2.
  ITE_RULE *)


(*
Inductive cpred :=
| TRUE
| FALSE
| EMPTY
| REG (n : nat)
| AND (a b : cpred)
| OR (a b : cpred)
| NOT (a : cpred).

Inductive mprog :=
| U (p : prog)
| MEAS (q : nat) (i : nat)
| ITE (c : cpred) (p1 p2 : prog)
| mseq (mp1 mp2 : mprog).

Coercion U : prog >-> mprog.

Definition Mbranch n := (cpred * (list (TType n)))%type.
Definition MPredicate n := list (Mbranch n).

Definition cqSatisfiesMbranch {n} (cq : cqstate n) (b : Mbranch n) (H : WF_Matrix (snd cq)) : Prop :=
  if Mat_eq_dec (2 ^ n) (1%nat) (snd cq) (Zero) H (WF_Zero (2 ^ n) 1%nat)
  then True
  else match translate_cpred (fst b) (fst cq) with
          | Some true => Forall (fun t : TType n => vecSatisfies (snd cq) (translate t)) (snd b)
          | _ => False
          end.

Definition Mtriple {n} (A : MPredicate n) (mp : mprog) (B : MPredicate n) :=
  forall a, In a A -> forall cq (H : WF_Matrix (snd cq)), cqSatisfiesMbranch cq a H -> forall cq', In cq' (apply_mprog mp [cq]) ->
   exists b, In b B /\ exists (H0 : WF_Matrix (snd cq')), cqSatisfiesMbranch cq' b H0.

Lemma MSEQ_RULE {n} (A B C : MPredicate n) (mp1 mp2 : mprog):
  Mtriple A mp1 B -> Mtriple B mp2 C -> Mtriple A (mp1 ;;; mp2) C.

Lemma CUP_RULE {n} (A B A' B' : MPredicate n) (mp : mprog):
  Mtriple A mp B -> Mtriple A' mp B' -> Mtriple (A ++ A') mp (B ++ B').

Lemma CUP_CONS_RULE {n} (a : Mbranch n) (B A' B' : MPredicate n) (mp : mprog):
  Mtriple [a] mp B -> Mtriple A' mp B' -> Mtriple (a :: A') mp (B ++ B').

Lemma ITE_RULE {n} (lt : list (TType n)) (C : cpred) (Q : MPredicate n) (p1 p2 : prog) (A : cpred):
  {{{ [ (AND A C, lt) ] }}} p1 {{{ Q }}} ->
  {{{ [ (AND A (NOT C), lt) ] }}} p2 {{{ Q }}} ->
  {{{ [ (A, lt) ] }}} (ITE C p1 p2) {{{ Q }}}.

Lemma MEAS_RULE {n} (A : cpred) (lt : list (TType n)) (q i : nat):
(q < n)%nat -> WF_L lt → length lt ≠ 0%nat -> does_not_appear i A ->
{{{ [(A, lt)] }}} MEAS q i {{{ [
(AND A (REG i), apply_MEAS q true lt);
(AND A (REG i false), apply_MEAS q false lt)] }}}.

Lemma TRIPLE_RULE {n : nat} (lt lt' : list (TType n)) (cp : cpred) (g : prog) (Q : Predicate n) (la : list (AType n)) :
  {{ Cap (map TtoA lt) }} g {{ Q }} ->
  Q = Cap la ->
  repeat 1%nat (length la) = map length la ->
  lt' = map AtoT la ->
  {{{ [ (cp, lt) ] }}} U g {{{ [ (cp, lt')] }}}.

Lemma FINALIZE_RULE {n : nat} (mp : mprog) (P Q : MPredicate n) (x : Mbranch n) (lt : list (TType n)) :
  {{{ P }}} mp {{{ Q }}} -> hd_error Q = Some x -> lt = x.2 ->
  map snd Q = repeat lt (length Q) ->
  {{{ P }}} mp {{{ [(TRUE, lt)] }}}.

Lemma SIMPLIFY_CPRED_PRE_RULE (B : cpred) {A : cpred} {n : nat} {lt : list (TType n)} {mp : mprog} {Q : MPredicate n} :
  equiv_cpred A B ->
  {{{ [ (A, lt) ] }}} mp {{{ Q }}}
  <-> {{{ [ (B, lt) ] }}} mp {{{ Q }}}.

Lemma KILL_AND_REPEAT_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
      {{{ [ (AND (AND A B) B, lt) ] }}} mp {{{ Q }}}
      <-> {{{ [ (AND A B, lt) ] }}} mp {{{ Q }}}.

Lemma KILL_FALSE_RULE {n : nat} (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  {{{ [ (FALSE, lt) ] }}} mp {{{ Q }}}.

Lemma KILL_AND_FALSE_R_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  {{{ [ (AND A FALSE, lt) ] }}} mp {{{ Q }}}.

Lemma KILL_AND_TF_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
      {{{ [ (AND (AND A B) (NOT B), lt) ] }}} mp {{{ Q }}}.

Lemma KILL_AND_FT_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n)  (H' : Q <> []) :
      {{{ [ (AND (AND A (NOT B)) B, lt) ] }}} mp {{{ Q }}}.

Lemma REMOVE_LAST_pI_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
  lt <> [] ->
  last lt (defaultT_I n) = (C1, (repeat gI n)) ->
      {{{ [ (A, lt ) ] }}} mp {{{ Q }}} <->
        {{{ [ (A, removelast lt ) ] }}} mp {{{ Q }}}.

Lemma REMOVE_LAST_mI_RULE {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
  n <> 0%nat ->
  lt <> [] ->
  last lt (defaultT_I n) = (- C1, (repeat gI n)) ->
  {{{ [ (A, lt ) ] }}} mp {{{ Q }}}.

Lemma NORMALIZE_RULE {n : nat} (i : nat) (A : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) :
  WF_L lt ->
  {{{ [(A,normalize i lt)] }}} mp {{{ Q }}} ->
  {{{ [(A,lt)] }}} mp {{{ Q }}}.
*)

(* Lemma Mtriple_nonempty_postcond {n} (A B : MPredicate n) (mp : mprog) :
  {{{A}}} mp {{{B}}} -> A <> [] -> B <> [].
Proof.
  intros HAB HA ->.
  destruct A as [|a A]; [easy|].
  clear HA.
  specialize (HAB a ltac:(now left)). *)



Require Export HeisenbergFoundations.ReflexiveAutomation.

Ltac finalize :=
  eapply FINALIZE_RULE.

Ltac mseq :=
  eapply MSEQ_RULE.

Ltac triple :=
eapply TRIPLE_RULE;
    [simpl; solvePlaceholder_refl_internal
    | f_equal
    | auto
    | auto].

Ltac meas :=
eapply MEAS_RULE;
  [ lia
  | repeat (constructor; auto)
  (* | simpl; lia *)
  | repeat (constructor; auto)].

Ltac branch :=
  match goal with
  | |- {{{ [_] }}} _ {{{ _ }}} => idtac
  | |- {{{ _ :: _ }}} _ {{{ _ }}} =>
      eapply CUP_CONS_RULE;
      [idtac | try branch]
  end.

Ltac simplify :=
  unfold apply_MEAS, AtoT;
  repeat match goal with
    | |- context [ pivots_normalize _ ?a ] =>
        rewrite ! (parse_norm_eq _ a _);
        rewrite <- !TTypeBtoTType_respects_pivots_normalizeB
    | |- context [ normalize _ ?a ] =>
        rewrite ! (parse_norm_eq _ a _);
        rewrite <- !TTypeBtoTType_respects_normalize
    end;
  lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt
           Q2R IZR QC2C Cexp PI sin cos atype_eq Copp
           triple pred_eq Mtriple].

Ltac ite :=
  eapply ITE_RULE.

Ltac kill_rep :=
  repeat erewrite KILL_AND_REPEAT_R_RULE.

Ltac kill_f :=
  repeat
    first [eapply KILL_FALSE_RULE;
           first [intro; discriminate | shelve]
          | eapply KILL_AND_FALSE_R_RULE;
           first [intro; discriminate | shelve]
          | eapply KILL_AND_TF_R_RULE;
            first [intro; discriminate | shelve]
          | eapply KILL_AND_FT_R_RULE;
            first [intro; discriminate | shelve]].

Ltac kill_f_r :=
  try apply KILL_AND_FALSE_R_RULE'.

Ltac kill_i :=
  repeat
    (repeat (erewrite REMOVE_LAST_pI_RULE;
             [simpl | intro; discriminate | reflexivity]);
     repeat (eapply REMOVE_LAST_mI_RULE';
             [ lia
             | intro; discriminate
             | reflexivity])).

Ltac kill := repeat (try apply KILL_FALSE_RULE'; kill_rep; kill_i; kill_f).

Ltac mseqs :=
  repeat tryif mseq then [> mseqs; idtac | idtac] else idtac.

Ltac normal i :=
  eapply (NORMALIZE_RULE i);
  [ repeat constructor; simpl; lia | simplify ].

Ltac cpred_iff cpred :=
  erewrite (SIMPLIFY_CPRED_PRE_RULE cpred).

Ltac mstep :=
  simplify; branch; kill; try (normal 0%nat);
  match goal with
  | |- {{{ _ }}} ITE _ _ _ {{{ _ }}} => ite; mstep
  | |- {{{ _ }}} MEAS _ _ {{{ _ }}} => meas
  | |- {{{ _ }}} U _ {{{ _ }}} => triple
  end.

Ltac msolve := tryif mseq then [> repeat msolve | idtac] else mstep.





(*** Steane7 QEC Example ***)

Ltac bsolve_slow :=
  let r := fresh "r" in
  intros r; simpl;
  destruct
    (r !! 0%nat)%stdpp as [b0|],
    (r !! 1%nat)%stdpp as [b1|],
    (r !! 2%nat)%stdpp as [b2|],
    (r !! 3%nat)%stdpp as [b3|],
    (r !! 4%nat)%stdpp as [b4|],
    (r !! 5%nat)%stdpp as [b5|];
  try reflexivity;
  destruct b0, b1, b2, b3, b4, b5;
  reflexivity.

Ltac bsolve_concrete :=
  bsolve_btauto.
  (* (apply cpred_dec_correct; vm_compute; done). *)
  (* || tryif bsolve_slow then match goal with |- ?G => gfail 1000 "DIDN'T SOLVE" G end else fail. *)

Ltac steane7_true cpred :=
cpred_iff cpred;
[triple
| bsolve_concrete].

Ltac steane7_false cpred :=
cpred_iff (AND cpred FALSE);
[kill
| bsolve_concrete].

Ltac steane7_correction_step cpred := simplify; branch; try (ite; first [steane7_true cpred | steane7_false cpred]).

Ltac steane7_correction cpred :=
  mseq;
  [ do 7 (mseq; [steane7_correction_step cpred; kill | idtac]);
    steane7_correction_step cpred; kill
  | idtac];
  do 7 (mseq; [steane7_correction_step cpred; kill | idtac]);
  steane7_correction_step cpred; kill_f.


Definition g1 : TType 8 := (C1, [gI; gI; gI; gX; gX; gX; gX; gI]).
Definition g2 : TType 8 := (C1, [gI; gX; gX; gI; gI; gX; gX; gI]).
Definition g3 : TType 8 := (C1, [gX; gI; gX; gI; gX; gI; gX; gI]).
Definition g4 : TType 8 := (C1, [gI; gI; gI; gZ; gZ; gZ; gZ; gI]).
Definition g5 : TType 8 := (C1, [gI; gZ; gZ; gI; gI; gZ; gZ; gI]).
Definition g6 : TType 8 := (C1, [gZ; gI; gZ; gI; gZ; gI; gZ; gI]).
Definition Xbar : TType 8 := (C1, [gX; gX; gX; gX; gX; gX; gX; gI]).
Definition Zbar : TType 8 := (C1, [gZ; gZ; gZ; gZ; gZ; gZ; gZ; gI]).
Definition Zanc : TType 8 := (C1, [gI; gI; gI; gI; gI; gI; gI; gZ]).
Definition ZL : list (TType 8) := [g1; g2; g3; g4; g5; g6; Zbar; Zanc].
Definition XL : list (TType 8) := [g1; g2; g3; g4; g5; g6; Xbar; Zanc].

Definition Steane7 q0 q1 q2 q3 q4 q5 q6 : prog :=
(H q4 ;; H q5 ;; H q6 ;;
CNOT q0 q1 ;; CNOT q0 q2 ;;
CNOT q6 q0 ;; CNOT q6 q1 ;; CNOT q6 q3 ;;
CNOT q5 q0 ;; CNOT q5 q2 ;; CNOT q5 q3 ;;
CNOT q4 q1 ;; CNOT q4 q2 ;; CNOT q4 q3)%pg.

Definition synd_s1z_0 : mprog :=
U (CNOT 0 7 ;; CNOT 2 7 ;; CNOT 4 7 ;; CNOT 6 7)%pg ;;; MEAS 7 0 ;;; ITE (REG 0 true) (Id 7) (X 7).

Definition synd_s2z_1 : mprog :=
U (CNOT 1 7 ;; CNOT 2 7 ;; CNOT 5 7 ;; CNOT 6 7)%pg ;;; MEAS 7 1 ;;; ITE (REG 1 true) (Id 7) (X 7).

Definition synd_s3z_2 : mprog :=
U (CNOT 3 7 ;; CNOT 4 7 ;; CNOT 5 7 ;; CNOT 6 7)%pg ;;; MEAS 7 2 ;;; ITE (REG 2 true) (Id 7) (X 7).

Definition synd_s1x_3 : mprog :=
U (H 7 ;; CNOT 7 0 ;; CNOT 7 2 ;; CNOT 7 4 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 3 ;;; ITE (REG 3 true) (Id 7) (X 7).

Definition synd_s2x_4 : mprog :=
U (H 7 ;; CNOT 7 1 ;; CNOT 7 2 ;; CNOT 7 5 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 4 ;;; ITE (REG 4 true) (Id 7) (X 7).

Definition synd_s3x_5 : mprog :=
U (H 7 ;; CNOT 7 3 ;; CNOT 7 4 ;; CNOT 7 5 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 5 ;;; ITE (REG 5 true) (Id 7) (X 7).

Definition correctX : mprog :=
ITE (AND (AND (REG 2 true) (REG 1 true)) (REG 0 true)) (Id 7) (Id 7) ;;;
ITE (AND (AND (REG 2 true) (REG 1 true)) (REG 0 false)) (X 0) (Id 7) ;;;
ITE (AND (AND (REG 2 true) (REG 1 false)) (REG 0 true)) (X 1) (Id 7) ;;;
ITE (AND (AND (REG 2 true) (REG 1 false)) (REG 0 false)) (X 2) (Id 7) ;;;
ITE (AND (AND (REG 2 false) (REG 1 true)) (REG 0 true)) (X 3) (Id 7) ;;;
ITE (AND (AND (REG 2 false) (REG 1 true)) (REG 0 false)) (X 4) (Id 7) ;;;
ITE (AND (AND (REG 2 false) (REG 1 false)) (REG 0 true)) (X 5) (Id 7) ;;;
ITE (AND (AND (REG 2 false) (REG 1 false)) (REG 0 false)) (X 6) (Id 7).

Definition correctZ : mprog :=
ITE (AND (AND (REG 5 true) (REG 4 true)) (REG 3 true)) (Id 7) (Id 7) ;;;
ITE (AND (AND (REG 5 true) (REG 4 true)) (REG 3 false)) (Z 0) (Id 7) ;;;
ITE (AND (AND (REG 5 true) (REG 4 false)) (REG 3 true)) (Z 1) (Id 7) ;;;
ITE (AND (AND (REG 5 true) (REG 4 false)) (REG 3 false)) (Z 2) (Id 7) ;;;
ITE (AND (AND (REG 5 false) (REG 4 true)) (REG 3 true)) (Z 3) (Id 7) ;;;
ITE (AND (AND (REG 5 false) (REG 4 true)) (REG 3 false)) (Z 4) (Id 7) ;;;
ITE (AND (AND (REG 5 false) (REG 4 false)) (REG 3 true)) (Z 5) (Id 7) ;;;
ITE (AND (AND (REG 5 false) (REG 4 false)) (REG 3 false)) (Z 6) (Id 7).

Lemma CUP_RULE_FALSE_R {n} (A B A' : MPredicate n) mp :
  {{{A}}} mp {{{B}}} ->
  {{{A'}}} mp {{{ [] }}} ->
  {{{A ++ A'}}} mp {{{B}}}.
Proof.
  intros HAB HA'.
  rewrite <- (app_nil_r B).
  now apply CUP_RULE.
Qed.

Lemma CUP_RULE_FALSE_L {n} (A B A' : MPredicate n) mp :
  {{{A}}} mp {{{ [] }}} ->
  {{{A'}}} mp {{{ B }}} ->
  {{{A ++ A'}}} mp {{{B}}}.
Proof.
  intros HAB HA'.
  now apply (CUP_RULE A [] A' B).
Qed.

Example Steane7QEC_Id :
{{{
[
(TRUE,
[
(C1, [gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gZ; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gZ; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gZ; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gI; gZ])
]
)
]
}}}
(U (Steane7 0 1 2 3 4 5 6)) ;;; (U (Id 7)) ;;;
synd_s1z_0 ;;; synd_s2z_1 ;;; synd_s3z_2 ;;; synd_s1x_3 ;;; synd_s2x_4 ;;; synd_s3x_5 ;;;
correctX ;;; correctZ
{{{ [(TRUE, normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])] }}}.
Proof.
finalize.
do 8 msolve.
cbn.
branch.

steane7_correction
(TRUE && REG 0 true && REG 1 true && REG 2 true &&
      REG 3 true && REG 4 true && REG 5 true)%cpred.

(*** Copy Paste cpred ***)
(* steane7_correction (AND
         (AND (AND (AND (AND (AND TRUE (REG 0 true)) (REG 1 true)) (REG 2 true)) (REG 3 true)) (REG 4 true))
         (REG 5 true)). *)



Unshelve.
all: try apply ([(TRUE,normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])]).
1,2,3,4,5,6:kill.
f_equal.
solveNormalize; reflexivity.
solveNormalize; reflexivity.
all: try (intro; discriminate).
Qed.


Ltac eval_meas :=
  match goal with
  | |- context G [@apply_MEAS ?n ?i ?b ?lt] =>

    let x := fresh "x" in
    evar (x : list (TType n));
    replace (@apply_MEAS n i b lt) with x by (validate_red; Csimpl; unfold x; reflexivity);
    subst x
  | |- context G [@apply_MEAS' ?n ?i ?b ?lt] =>

    let x := fresh "x" in
    evar (x : list (TType n));
    replace (@apply_MEAS' n i b lt) with x by (validate_red; Csimpl; unfold x; reflexivity);
    subst x
  end.

Lemma translate_prog_id n i :
  translate_prog n (Id i) = I _.
Proof.
  cbn.
  unfold prog_simpl_app.
  bdestruct (i <? n).
  - restore_dims.
    rewrite 2 kron_mixed_product.
    rewrite MmultHH.
    rewrite 2 Mmult_1_r by auto_wf.
    rewrite 2 id_kron.
    f_equal; unify_pows_two.
  - now rewrite Mmult_1_r by auto_wf.
Qed.

Lemma ID_RULE {n} (P : Predicate n) i :
  {{ P }} Id i {{ P }}.
Proof.
  intros v.
  rewrite translate_prog_id.
  intros Hv.
  apply vecSatisfiesP_implies_WF_Matrix in Hv as Hv'.
  now rewrite Mmult_1_l by auto_wf.
Qed.

Fixpoint does_not_appear_bool (i : nat) (c : cpred) : bool :=
  match c with
  | TRUE | FALSE => true
  | REG n _ => negb (Nat.eqb n i)
  | OR a b | AND a b => does_not_appear_bool i a && does_not_appear_bool i b
  | NOT a => does_not_appear_bool i a
  end.

Lemma does_not_appear_bool_correct i c :
  does_not_appear_bool i c <-> does_not_appear i c.
Proof.
  split.
  - induction c; cbn; [auto using does_not_appear.. | | |auto using dna_NOT].
    + rewrite negb_True, Is_true_true, Nat.eqb_eq.
      now intros; apply dna_REG.
    + rewrite andb_True.
      intros []; auto using dna_AND.
    + rewrite andb_True.
      intros []; auto using dna_OR.
  - intros Hic.
    induction Hic; cbn; try easy.
    + now rewrite negb_True, Is_true_true, Nat.eqb_eq.
    + now apply andb_True.
    + now apply andb_True.
Qed.

#[export] Instance does_not_appear_dec i c : Decision (does_not_appear i c).
  refine (match does_not_appear_bool i c as b return
    (b <-> _) -> _ with
  | true => fun Hiff => left _
  | false => fun Hiff => right _
  end (does_not_appear_bool_correct i c));
  abstract (now rewrite <- Hiff).
Defined.

Fixpoint obind_list {A B} (f : A -> option (list B)) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l => intersection_with (λ a b, Some (a ++ b)) (f a) (obind_list f l)
  end.

Definition compute_meas_MPC {n} q i (b : Mbranch n) : option (MPredicate n) :=
  if does_not_appear_bool i b.1 then
    Some ([ (b.1 && i ↦ true, apply_MEAS' q true b.2);
      (b.1 && i ↦ false, apply_MEAS' q false b.2)])%cpred
  else None.

Lemma compute_meas_MPC_correct {n} q i (b : Mbranch n) P :
  (q < n)%nat -> WF_L b.2 ->
  compute_meas_MPC q i b = Some P ->
  {{{ [b] }}} MEAS q i {{{ P }}}.
Proof.
  intros Hq Hb2.
  pose proof (does_not_appear_bool_correct i b.1) as Hb%proj1.
  unfold compute_meas_MPC.
  case_match; [|done].
  intros [= <-].
  destruct b.
  cbn.
  apply MEAS_RULE; auto.
Qed.


(* Lemma triple_RULE' {n : nat} (lt lt' : AType n) (cp : cpred) (g : prog) :
  {{ lt }} g {{ lt' }} ->
  {{{ [ (cp, lt) ] }}} U g {{{ [ (cp, lt')] }}}.
Proof. intros Hg.
  unfold triple, Mtriple in *.
  intros _ [<- |[]].
  intros cq HcqWF Hcq.
  intros _ [<- |[]].
  eexists.
  split; [left; reflexivity|].
  cbn.
  unshelve eexists; [auto_wf|].
  unfold cqSatisfiesMbranch in *.
  destruct (Mat_eq_dec _ _ _ _ _ _) as [Hcq0|Htrans] in Hcq.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in HF.
    rewrite Hcq0 in HF.
    rewrite Mmult_0_r in HF.
    easy.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in *.
    case_match; [|easy].
    vecSatisfies translateA
    rewrite Forall_forall in *.
    naive_solver


  exists ltac:(auto_wf).

  intros a H0 cq H1 H2 cq' H3.
  inversion H0.
  2: { inversion H4. }
  symmetry in H4. subst.
  clear H0.
  simpl in *.
  rewrite kill_false in H3.
  symmetry in H3.
  subst.
  exists (cp, lt').
  split. left; auto.
  simpl in *.
  assert (WF_Matrix (translate_prog n g × cq.2)).
  { auto with wf_db. }
  exists H0.
  unfold cqSatisfiesMbranch in *.
  simpl in *.
  specialize (H cq.2).
  destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H1 (WF_Zero (2 ^ n) 1)) eqn:E;
    destruct (Mat_eq_dec (2 ^ n) 1 (translate_prog n g × cq.2) Zero H0 (WF_Zero (2 ^ n) 1));
    auto.
  rewrite e, Mmult_0_r in n0; contradiction.
  destruct (translate_cpred cp cq.1) eqn:E'; auto.
  assert (WF_Matrix cq.2
          ∧ Forall (λ a0 : AType n, vecSatisfies cq.2 (translateA a0)) (map TtoA lt)).
  { split; auto.
    rewrite Forall_forall in *.
    intros a H3.
    unfold translateA.
    rewrite in_map_iff in H3.
    destruct H3 as [t [H3 H4]].
    symmetry in H3. subst.
    specialize (H2 t H4).
    simpl. rewrite Mplus_0_l. auto. }
  destruct (H H3).
  unfold translateA in H5.
  rewrite Forall_map in H5.
  unfold TtoA in H5.
  simpl in H5.
  setoid_rewrite Mplus_0_l in H5.
  auto.
Qed. *)
(*
Lemma triple_RULE' {n : nat} (lt : list (TType n)) (lt' : list (AType n)) (cp : cpred) (g : prog) :
  lt' <> [] ->
  {{ Cap (map TtoA lt) }} g {{ Cap ( lt'(*  ≫= flat_map TtoA *)) }} ->
  {{{ [ (cp, lt) ] }}} U g {{{  pair cp <$> lt' }}}.
Proof.
  intros Hlt' Hg.
  unfold triple, Mtriple in *.
  intros _ [<- |[]] cq HcqWF Hcq _ [<- |[]].
  destruct lt' as [|lb lt']; [easy|]; clear Hlt'.
  cbn.
  eexists.
  split; [left; reflexivity|].
  unshelve eexists; [auto_wf|].
  unfold cqSatisfiesMbranch in *.
  destruct (Mat_eq_dec _ _ _ _ _ _) as [Hcq0|Htrans] in Hcq.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in HF.
    rewrite Hcq0 in HF.
    rewrite Mmult_0_r in HF.
    easy.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in *.
    case_match; [|easy].
    specialize (Hg cq.2).
    unshelve epose proof (Hg _) as Hg.
    1:{
      split; [auto_wf|].
      rewrite Forall_map.
      cbn.
      revert Hcq.
      apply Forall_impl.
      intros a.
      now rewrite Mplus_0_l.
    }
    rewrite Forall_fmap in Hg.
    destruct Hg as [_ [Hall _]%Forall_app].
    rewrite Forall_flat_map in Hall.
    revert Hall.
    apply Forall_impl.
    intros a.
    unfold TtoA.
    rewrite Forall_singleton.
    cbn.
    now rewrite Mplus_0_l.
Qed. *)

Lemma triple_RULE' {n : nat} (lt : list (TType n)) (lt' : list (AType n)) (cp : cpred) (g : prog) :
  lt' <> [] ->
  {{ Cap (map TtoA lt) }} g {{ Cap (TtoA <$> mbind (M:=list) (flat_map TtoA) lt'(*  ≫= flat_map TtoA *)) }} ->
  {{{ [ (cp, lt) ] }}} U g {{{  pair cp <$> lt' }}}.
Proof.
  intros Hlt' Hg.
  unfold triple, Mtriple in *.
  intros _ [<- |[]] cq HcqWF Hcq _ [<- |[]].
  destruct lt' as [|lb lt']; [easy|]; clear Hlt'.
  cbn.
  eexists.
  split; [left; reflexivity|].
  unshelve eexists; [auto_wf|].
  unfold cqSatisfiesMbranch in *.
  destruct (Mat_eq_dec _ _ _ _ _ _) as [Hcq0|Htrans] in Hcq.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in HF.
    rewrite Hcq0 in HF.
    rewrite Mmult_0_r in HF.
    easy.
  - destruct (Mat_eq_dec _ _ _ _ _ _) as [|HF]; [easy|].
    cbn in *.
    case_match; [|easy].
    specialize (Hg cq.2).
    unshelve epose proof (Hg _) as Hg.
    1:{
      split; [auto_wf|].
      rewrite Forall_map.
      cbn.
      revert Hcq.
      apply Forall_impl.
      intros a.
      now rewrite Mplus_0_l.
    }
    rewrite Forall_fmap in Hg.
    destruct Hg as [_ [Hall _]%Forall_app].
    rewrite Forall_flat_map in Hall.
    revert Hall.
    apply Forall_impl.
    intros a.
    unfold TtoA.
    rewrite Forall_singleton.
    cbn.
    now rewrite Mplus_0_l.
Qed.

Definition oAtoT {n} (A : AType n) : option (TType n) :=
  match A with
  | [t] => Some t
  | _ => None
  end.
(*
Definition compute_U_MPC {n} (p : prog) (P : MPredicate n) : option (MPredicate n) :=
  obind_list (λ '(c, a),
    fmap (M:=option) (λ t, [(c, TtoA t)]) $ oAtoT (prog_A p a))%prg P.

Lemma intersection_with_Some {A} (f : A -> A -> option A) (ma mb : option A) c :
  intersection_with f ma mb = Some c <->
  exists a b, ma = Some a /\ mb = Some b /\ f a b = Some c.
Proof.
  destruct ma, mb; cbn; naive_solver.
Qed.

Lemma oAtoT_Some {n} (a : AType n) t :
  oAtoT a = Some t <-> a = [t].
Proof.
  destruct a as [|? []]; naive_solver.
Qed.

Lemma compute_U_MPC_correct {n} (p : prog) (P : MPredicate n) :
  prog_bound n p -> Forall WF_AType' P.*2 ->
  forall Q,
  compute_U_MPC p P = Some Q ->
  {{{ P }}} p {{{ Q }}}.
Proof.
  intros Hp HP.
  rewrite Forall_fmap in HP.
  unfold compute_U_MPC.
  induction HP as [|[c A] P HA HP IHP]; [easy|].
  intros Q.
  cbn.
  rewrite intersection_with_Some.
  intros (Qa & QP & (t & Ht%oAtoT_Some & ->)%fmap_Some & HQP & [= <-]).

  eapply (CUP_CONS_RULE _ [_]), IHP.
  - apply triple_RULE.
    apply CAP
  WF_AType'
  easy.
  apply triple_RULE.
  cbn in HA.

  prog_A
  apply prog_A_correct.
    hnf. naive_solver.

Definition compute_U_MPC {n} (p : prog) (P : MPredicate n) : MPredicate n :=
  mbind (M:=list) (λ b, (b.1,.) <$> (
    (prog_A p) <$> (TtoA <$> b.2))) P.

Lemma compute_U_MPC_correct {n} (p : prog) (P : MPredicate n) :
  prog_bound n p -> Forall WF_AType' P.*2 ->
  {{{ P }}} p {{{ compute_U_MPC p P }}}.
Proof.
  intros Hp HP.
  rewrite Forall_fmap in HP.
  unfold compute_U_MPC.
  induction HP as [|[c A] P HA HP IHP]; [easy|].
  cbn.
  eapply CUP_CONS_RULE, IHP.
  apply triple_RULE'.
  WF_AType'
  easy.
  apply triple_RULE.
  cbn in HA.

  prog_A
  apply prog_A_correct.
    hnf. naive_solver.

Fixpoint compute_MPC {n} (p : mprog) (P : MPredicate n) {struct p} : option (MPredicate n) :=
  match p with
  | U p' => Some (compute_U_MPC p' P)
  | MEAS q i => obind_list (compute_meas_MPC q i) P
  | ITE c p1 p2 =>
    Some ((compute_U_MPC p1 (prod_map (λ a, AND a c) Datatypes.id <$> P)) ++
      (compute_U_MPC p2 (prod_map (λ a, AND a (NOT c)) Datatypes.id <$> P)))
  | mseq mp1 mp2 => compute_MPC mp1 P ≫= compute_MPC mp2
  end. *)

Lemma filter_nil_iff {A} {P : A -> Prop} {HP : forall a, Decision (P a)} l :
  base.filter P l = nil <-> Forall (λ a, ~ P a) l.
Proof.
  induction l; [easy|].
  cbn.
  rewrite list.Forall_cons.
  case_decide; [naive_solver|].
  naive_solver.
Qed.

Lemma filter_nil_neg_iff {A} {P : A -> Prop} {HP : forall a, Decision (P a)} l :
  base.filter (λ a, ~ P a) l = nil <-> Forall (λ a, P a) l.
Proof.
  induction l; [easy|].
  cbn.
  rewrite list.Forall_cons.
  case_decide; [naive_solver|].
  naive_solver.
Qed.

Lemma KILL_FALSES_PRE_RULE {n} (P Q : MPredicate n) (p : mprog) l :
  base.filter (λ c_a, ~ (cpred_is_equiv c_a.1 FALSE)) P = l ->
  {{{from_option (λ _, l) [(FALSE, [])] (hd_error l)}}} p {{{Q}}} ->
  {{{P}}} p {{{Q}}}.
Proof.
  intros Hl HPQ.
  intros b Hb cq HcqWF Hcq cq' Hcq'.
  apply elem_of_list_In in Hb as Hb_elem.
  apply elem_of_list_In in Hcq' as Hcq'_elem.
  unfold cqSatisfiesMbranch in Hcq.
  specialize (fun a Ha => HPQ a Ha cq HcqWF).
  unfold cqSatisfiesMbranch at 1 in HPQ.

  destruct (Mat_eq_dec _ _ _ _ _ _) as [Hcq0|Hcqn0].
  1:{
    destruct l as [|a l].
    - cbn in *.
      specialize (HPQ _ ltac:(now left)).
      specialize (HPQ Logic.I cq' Hcq').
      easy.
    - cbn in *.
      specialize (HPQ _ ltac:(now left)).
      specialize (HPQ Logic.I cq' Hcq').
      easy.
  }
  destruct_decide (decide (l = [])) as Hlnil.
  1:{
    induction (eq_sym Hlnil).
    cbn in *.
    clear HPQ.
    apply filter_nil_neg_iff in Hl.
    rewrite list.Forall_forall in Hl.
    apply Hl in Hb_elem.
    apply cpred_is_equiv_correct in Hb_elem.
    specialize (Hb_elem cq.1).
    rewrite Hb_elem in Hcq.
    easy.
  }
  replace (from_option _ _ _) with l in HPQ by now destruct l.

  subst l.
  specialize (HPQ b).
  rewrite <- elem_of_list_In in HPQ.
  rewrite elem_of_list_filter in HPQ.
  destruct (translate_cpred b.1 cq.1) eqn:Hbcq; [|easy].

  assert (HnF : ¬ cpred_is_equiv b.1 FALSE). 1:{
    intros Himpl%cpred_is_equiv_correct.
    specialize (Himpl cq.1).
    now rewrite Hbcq in Himpl.
  }
  specialize (HPQ (conj HnF Hb_elem)).
  specialize (HPQ Hcq _ Hcq').
  easy.
Qed.


Lemma KILL_FALSES_PRE_RULE' {n} (P Q : MPredicate n) (p : mprog) l :
  filter (λ c_a, negb (cpred_is_equiv c_a.1 FALSE)) P = l ->
  {{{from_option (λ _, l) [(FALSE, [])] (hd_error l)}}} p {{{Q}}} ->
  {{{P}}} p {{{Q}}}.
Proof.
  intros Hl.
  apply KILL_FALSES_PRE_RULE.
  subst l.
  induction P; [done|].
  cbn.
  rewrite decide_bool_decide.
  destruct (cpred_is_equiv a.1 FALSE); cbn; f_equal; easy.
Qed.


Tactic Notation "vm_eval" uconstr(pat) :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in *;
  vm_compute in Hx;
  subst x.

Ltac elim_falses :=
  cbn;
  eapply KILL_FALSES_PRE_RULE';
  [cbn [filter];
  repeat vm_eval (¬ (cpred_is_equiv _ _)); reflexivity|cbn].

Ltac ite ::=
  first [
    apply ITE_TRUE_RULE; [bsolve_btauto|]|
    apply ITE_FALSE_RULE; [bsolve_btauto|] |
    eapply ITE_RULE
  ].


Example Steane7QEC_Z0 :
{{{
[
(TRUE,
[
(C1, [gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gZ; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gZ; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gZ; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gI; gZ])
]
)
]
}}}
(U (Steane7 0 1 2 3 4 5 6)) ;;; (U (Z 0)) ;;;
synd_s1z_0 ;;; synd_s2z_1 ;;; synd_s3z_2 ;;; synd_s1x_3 ;;; synd_s2x_4 ;;; synd_s3x_5 ;;;
correctX ;;; correctZ
{{{ [(TRUE, normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])] }}}.
Proof.
finalize.
repeat (msolve; elim_falses).
all: solveNormalize; reflexivity.
Qed.

Example Steane7QEC_X1 :
{{{
[
(TRUE,
[
(C1, [gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gZ; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gZ; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gZ; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gI; gZ])
]
)
]
}}}
(U (Steane7 0 1 2 3 4 5 6)) ;;; (U (X 1)) ;;;
synd_s1z_0 ;;; synd_s2z_1 ;;; synd_s3z_2 ;;; synd_s1x_3 ;;; synd_s2x_4 ;;; synd_s3x_5 ;;;
correctX ;;; correctZ
{{{ [(TRUE, normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])] }}}.
Proof.

finalize.
repeat (msolve; elim_falses).
all: solveNormalize; reflexivity.
Qed.


Example Steane7QEC_Y2 :
{{{
[
(TRUE,
[
(C1, [gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gZ; gI; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gZ; gI; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gZ; gI; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gI; gZ])
]
)
]
}}}
(U (Steane7 0 1 2 3 4 5 6)) ;;; (U (Y 2)) ;;;
synd_s1z_0 ;;; synd_s2z_1 ;;; synd_s3z_2 ;;; synd_s1x_3 ;;; synd_s2x_4 ;;; synd_s3x_5 ;;;
correctX ;;; correctZ
{{{ [(TRUE, normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])] }}}.
Proof.
  
finalize.
repeat (msolve; elim_falses).
all: solveNormalize; reflexivity.
Qed.


