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
Qed.


(** partial function from nat to option bool **)
Definition creg := gmap nat bool.
Check {[2%nat := true]} : creg.


Inductive cpred :=
| TRUE
| FALSE
| EMPTY
| REG (n : nat)
| AND (a b : cpred)
| OR (a b : cpred)
| NOT (a : cpred).

Fixpoint translate_cpred (p : cpred) (r : creg) : option bool :=
  match p with
  | TRUE => Some true
  | FALSE => Some false
  | EMPTY => None
  | REG n => r !! n
  | AND a b => 
      match translate_cpred a r, translate_cpred b r with
      | Some b1, Some b2 => Some (andb b1 b2)
      | _, _ => None
      end
  | OR a b =>
      match translate_cpred a r, translate_cpred b r with
      | Some b1, Some b2 => Some (orb b1 b2)
      | _, _ => None
      end
  | NOT a => 
      match translate_cpred a r with
      | Some b => Some (negb b)
      | None => None
      end
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
      flat_map 
        (fun cq =>
           match translate_cpred c (fst cq) with
           | Some true => [(fst cq, Mmult (translate_prog n p1) (snd cq))]
           | Some false => [(fst cq, Mmult (translate_prog n p2) (snd cq))]
           | None => []
           end
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
  - simpl. rewrite flat_map_app. auto.
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
  - simpl in *. setoid_rewrite app_nil_r.
    rewrite in_flat_map in H.
    destruct H as [x [xcq' inx]].
    exists x. auto.
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
  - induction cql.
    + rewrite apply_mprog_nil. auto.
    + rewrite apply_mprog_cons.
      rewrite Forall_cons_iff in H.
      destruct H.
      rewrite Forall_app.
      split; auto.
      simpl.
      rewrite app_nil_r.
      destruct (translate_cpred c (fst a)) eqn:E; try destruct u; try destruct o; auto.
      destruct b; auto.
      * constructor; simpl; auto with wf_db.
      * constructor; simpl; auto with wf_db.
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
    + rewrite app_nil_r in H1.
      destruct (translate_cpred c (fst a)) eqn:E; try destruct u; try destruct o; auto.
      * destruct b.
        -- destruct H1.
           ++ rewrite H in H0. rewrite <- H0. simpl. rewrite Mmult_0_r. auto.
           ++ inversion H0.
        -- destruct H1.
           ++ rewrite H in H0. rewrite <- H0. simpl. rewrite Mmult_0_r. auto.
           ++ inversion H0.
      * inversion H1.
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
          | Some true => Forall (fun t : TType n => vecSatisfies (snd cq) (translate t)) (snd b)
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
    rewrite app_nil_r in H4.
    assert (snd cq' = Zero).
    { destruct (translate_cpred C (fst cq)) eqn:E'.
      - destruct b.
        + destruct H4. 2: inversion H1.
          rewrite e in H1.
          rewrite <- H1.
          simpl. rewrite Mmult_0_r. auto.
        + destruct H4. 2: inversion H1.
          rewrite e in H1.
          rewrite <- H1.
          simpl. rewrite Mmult_0_r. auto.
      - inversion H4. }
    destruct (translate_cpred C (fst cq)) eqn:E'.
    + destruct b.
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
    + inversion H4.
  - simpl in H3.
    destruct (translate_cpred A (fst cq)) eqn:E';
    try destruct b; try contradiction.
    simpl in H4.
    rewrite app_nil_r in H4.
    destruct (translate_cpred C (fst cq)) eqn:E''.
    destruct b.
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
    + inversion H4.
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
| dna_EMPTY : does_not_appear i EMPTY
| dna_REG : forall (j : nat), (i <> j) -> does_not_appear i (REG j)
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



Lemma Forall_vecSatisfies_Zprojector_plus_apply_MEAS_true (n : nat) (lt : list (TType n)) (q : nat) (H : (q <? n) = true) (WF_L_lt : WF_L lt) (len_lt : length lt ≠ 0%nat) (cq : creg * Vector (2 ^ n)) (H2 : WF_Matrix cq.2) (E : cq.2 ≠ Zero) (H3 : Forall (λ t : TType n, vecSatisfies cq.2 (translate t)) lt) (H' : (q < n)%nat) (H1 : WF_Matrix (Zprojector_plus n q × cq.2)) (E' : Zprojector_plus n q × cq.2 ≠ Zero) :
  Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
    (apply_MEAS q true lt).
Proof.         simpl.
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

Lemma Forall_vecSatisfies_Zprojector_minus_apply_MEAS_false (n : nat) (lt : list (TType n)) (q : nat) (H : (q <? n) = true) (WF_L_lt : WF_L lt) (len_lt : length lt ≠ 0%nat) (cq : creg * Vector (2 ^ n)) (H2 : WF_Matrix cq.2) (E : cq.2 ≠ Zero) (H3 : Forall (λ t : TType n, vecSatisfies cq.2 (translate t)) lt) (H' : (q < n)%nat) (H1 : WF_Matrix (Zprojector_minus n q × cq.2)) (E' : Zprojector_minus n q × cq.2 ≠ Zero) :
  Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t))
    (apply_MEAS q false lt).
Proof.         simpl.
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
(q < n)%nat -> WF_L lt → length lt ≠ 0%nat -> does_not_appear i A -> 

{{{
[

(A, lt)

]
 }}} MEAS q i {{{
[

(AND A (REG i), apply_MEAS q true lt);

(AND A (NOT (REG i)), apply_MEAS q false lt)

]
 }}}.
Proof. unfold Mtriple.
  intros H WF_L_lt len_lt H0 a H1 cq H2 H3 cq' H4.
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
    exists (AND A (REG i), apply_MEAS q true lt).
    split; auto.
    simpl (<[i:=true]> cq.1, Zprojector_plus n q × cq.2).2.
    assert (WF_Matrix (Zprojector_plus n q × cq.2)) by auto with wf_db.
    exists H1.
    unfold cqSatisfiesMbranch in *.
    simpl in H3.
    simpl ((<[i:=true]> cq.1, Zprojector_plus n q × cq.2).2).
    simpl ((AND A (REG i), apply_MEAS q true lt).1).
    simpl ((<[i:=true]> cq.1, Zprojector_plus n q × cq.2).1).
    replace ((AND A (REG i), apply_MEAS q true lt).2) with (apply_MEAS q true lt) by auto.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H2 (WF_Zero (2 ^ n) 1)) as [E | E].
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_plus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      rewrite E in E'. rewrite Mmult_0_r in E'. contradiction.
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_plus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      induction H0; simpl in H3.
      * assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        simpl (translate_cpred (AND TRUE (REG i)) (<[i:=true]> cq.1)).   
        rewrite H0.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS_true; eauto.
      * contradiction.
      * contradiction.
      * simpl (translate_cpred (AND (REG j) (REG i)) (<[i:=true]> cq.1)).
        assert (<[i:=true]> cq.1 !! j = cq.1 !! j).
        { setoid_rewrite lookup_insert_ne; auto. }
        rewrite H4.
        destruct (cq.1 !! j) eqn:E''; try contradiction.
        destruct b; try contradiction.
        assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H5.
        replace (if true && true
                 then
                   Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
                     (apply_MEAS q true lt)
                 else False)
                  with
                  (Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
                     (apply_MEAS q true lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS_true; eauto.
      * simpl (translate_cpred (AND (AND c1 c2) (REG i)) (<[i:=true]> cq.1)).
        rewrite <- ! does_not_appear_preserves_translate_cpred; auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        destruct b, b0; try contradiction.
        simpl in H3.
        specialize (IHdoes_not_appear1 H3).
        specialize (IHdoes_not_appear2 H3).
        simpl (translate_cpred (AND c1 (REG i)) (<[i:=true]> cq.1)) in IHdoes_not_appear1.
        simpl (translate_cpred (AND c2 (REG i)) (<[i:=true]> cq.1)) in IHdoes_not_appear2.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear1; auto.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear2; auto.
        rewrite E'' in IHdoes_not_appear1.
        rewrite E''' in IHdoes_not_appear2.
        assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0 in IHdoes_not_appear1, IHdoes_not_appear2.
        replace (if true && true
                 then Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t)) (apply_MEAS 0 true lt)
                 else False)
          with
          (Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t)) (apply_MEAS 0 true lt))
          in IHdoes_not_appear1, IHdoes_not_appear2
          by auto.
        rewrite H0.
        replace (if true && true && true
                 then Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t)) (apply_MEAS 0 true lt)
                 else False)
                  with
                  (Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t)) (apply_MEAS 0 true lt))
          by auto.
        auto.
      * simpl (translate_cpred (AND (OR c1 c2) (REG i)) (<[i:=true]> cq.1)).
        simpl (translate_cpred (AND c1 (REG i)) (<[i:=true]> cq.1)) in IHdoes_not_appear1.
        simpl (translate_cpred (AND c2 (REG i)) (<[i:=true]> cq.1)) in IHdoes_not_appear2.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear1; auto.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear2; auto.
        rewrite <- does_not_appear_preserves_translate_cpred; auto.
        rewrite <- does_not_appear_preserves_translate_cpred; auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0 in *.
        rewrite andb_true_r in *.
        destruct (b || b0) eqn:E''''; try contradiction.
        destruct b, b0; try contradiction; simpl in H3;
          try specialize (IHdoes_not_appear1 H3);
          try specialize (IHdoes_not_appear2 H3);
          auto.
        simpl in E''''; discriminate.
      * simpl (translate_cpred (AND (NOT c) (REG i)) (<[i:=true]> cq.1)).
        simpl (translate_cpred (AND c (REG i)) (<[i:=true]> cq.1)) in IHdoes_not_appear.
        rewrite <- does_not_appear_preserves_translate_cpred in *; auto.
        destruct (translate_cpred c cq.1) eqn:E''; try contradiction.
        destruct b; try contradiction.
        simpl in H3.
        assert (<[i:=true]> cq.1 !! i = Some true).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H4 in *.
        replace (if (¬ false) && true
                 then
                   Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
                     (apply_MEAS q true lt)
                 else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_plus n q × cq.2) (translate t))
                     (apply_MEAS q true lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_plus_apply_MEAS_true; eauto.
  - destruct H1. 2: inversion H1.
    symmetry in H1.
    subst.
    exists (AND A (NOT (REG i)), apply_MEAS q false lt).
    split; auto.
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).2).
    assert (WF_Matrix (Zprojector_minus n q × cq.2)) by auto with wf_db.
    exists H1.
    unfold cqSatisfiesMbranch in *.
    simpl in H3.
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).2).
    simpl ((AND A (NOT (REG i)), apply_MEAS q false lt).1).
    simpl ((<[i:=false]> cq.1, Zprojector_minus n q × cq.2).1).
    replace ((AND A (NOT (REG i)), apply_MEAS q false lt).2) with (apply_MEAS q false lt) by auto.
    destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H2 (WF_Zero (2 ^ n) 1)) as [E | E].
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_minus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      rewrite E in E'. rewrite Mmult_0_r in E'. contradiction.
    + destruct (Mat_eq_dec (2 ^ n) 1 (Zprojector_minus n q × cq.2) Zero H1 (WF_Zero (2 ^ n) 1)) as [E' | E']; auto.
      induction H0; simpl in H3.
      * simpl (translate_cpred (AND TRUE (NOT (REG i))) (<[i:=false]> cq.1)).
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0.
        replace (if ¬ false
                 then Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt)
                 else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS_false; eauto.
      * contradiction.
      * contradiction.
      * simpl (translate_cpred (AND (REG j) (NOT (REG i))) (<[i:=false]> cq.1)).
        assert (<[i:=false]> cq.1 !! j = cq.1 !! j).
        { setoid_rewrite lookup_insert_ne; auto. }
        rewrite H4.
        destruct (cq.1 !! j) eqn:E''; try contradiction.
        destruct b; try contradiction.
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H5.
        replace (if true && (¬ false)
                 then Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt)
                 else False)
                  with
                  (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS_false; eauto.
      * simpl (translate_cpred (AND (AND c1 c2) (NOT (REG i))) (<[i:=false]> cq.1)).
        rewrite <- ! does_not_appear_preserves_translate_cpred; auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        destruct b, b0; try contradiction.
        simpl in H3.
        specialize (IHdoes_not_appear1 H3).
        specialize (IHdoes_not_appear2 H3).
        simpl (translate_cpred (AND c1 (NOT (REG i))) (<[i:=false]> cq.1)) in IHdoes_not_appear1.
        simpl (translate_cpred (AND c2 (NOT (REG i))) (<[i:=false]> cq.1)) in IHdoes_not_appear2.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear1; auto.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear2; auto.
        rewrite E'' in IHdoes_not_appear1.
        rewrite E''' in IHdoes_not_appear2.
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0 in IHdoes_not_appear1, IHdoes_not_appear2.
        replace (if true && (¬ false)
                       then
                        Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t))
                          (apply_MEAS 0 false lt)
                       else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS 0 false lt))
          in IHdoes_not_appear1, IHdoes_not_appear2
          by auto.
        rewrite H0.
        replace (if true && true && (¬ false)
                  then Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS 0 false lt)
                  else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS 0 false lt))
          by auto.
        auto.
      * simpl (translate_cpred (AND (OR c1 c2) (NOT (REG i))) (<[i:=false]> cq.1)).
        simpl (translate_cpred (AND c1 (NOT (REG i))) (<[i:=false]> cq.1)) in IHdoes_not_appear1.
        simpl (translate_cpred (AND c2 (NOT (REG i))) (<[i:=false]> cq.1)) in IHdoes_not_appear2.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear1; auto.
        rewrite <- does_not_appear_preserves_translate_cpred in IHdoes_not_appear2; auto.
        rewrite <- does_not_appear_preserves_translate_cpred; auto.
        rewrite <- does_not_appear_preserves_translate_cpred; auto.
        destruct (translate_cpred c1 cq.1) eqn:E''; try contradiction.
        destruct (translate_cpred c2 cq.1) eqn:E'''; try contradiction.
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H0 in *.
        rewrite andb_true_r in *.
        destruct (b || b0) eqn:E''''; try contradiction.
        destruct b, b0; try contradiction; simpl in H3;
          try specialize (IHdoes_not_appear1 H3);
          try specialize (IHdoes_not_appear2 H3);
          auto.
        simpl in E''''; discriminate.
      * simpl (translate_cpred (AND (NOT c) (NOT (REG i))) (<[i:=false]> cq.1)).
        simpl (translate_cpred (AND c (NOT (REG i))) (<[i:=false]> cq.1)) in IHdoes_not_appear.
        rewrite <- does_not_appear_preserves_translate_cpred in *; auto.
        destruct (translate_cpred c cq.1) eqn:E''; try contradiction.
        destruct b; try contradiction.
        simpl in H3.
        assert (<[i:=false]> cq.1 !! i = Some false).
        { setoid_rewrite lookup_insert. auto. }
        rewrite H4 in *.
        replace (if (¬ false) && (¬ false)
                then Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt)
                else False)
          with (Forall (λ t : TType n, vecSatisfies (Zprojector_minus n q × cq.2) (translate t)) (apply_MEAS q false lt))
          by auto.
(** Hard Part : quantum predicate **)
        clear - n lt q H WF_L_lt len_lt cq H2 E H3 H' H1 E'.
        eapply Forall_vecSatisfies_Zprojector_minus_apply_MEAS_false; eauto.
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
  destruct b; auto.
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
  destruct (translate_cpred cp cq.1); try contradiction.
  destruct b; try contradiction; auto.
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
  unfold equiv_cpred.
  intros r.
  simpl.
  destruct (translate_cpred A r) eqn:E; auto.
  destruct (translate_cpred B r) eqn:E'; auto.
  destruct b, b0; auto.
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
  
  destruct (translate_cpred A cq.1) eqn:E'; try contradiction.
  rewrite andb_false_r in H1.
  contradiction.
Qed.

Lemma KILL_AND_FALSE_R_RULE' {n : nat} (A : cpred) (lt : list (TType n)) (mp : mprog) :
  {{{ [ (AND A FALSE, lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_AND_FALSE_R_RULE. intro. discriminate. Qed.

Lemma KILL_AND_TF_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n) (H' : Q <> []) :
      {{{ [ (AND (AND A B) (NOT B), lt) ] }}} mp {{{ Q }}}.
Proof. eapply SIMPLIFY_CPRED_PRE_RULE.
  Unshelve.
  3: apply (AND (AND A B) FALSE).
  unfold equiv_cpred.
  intros r.
  simpl.
  destruct (translate_cpred A r) eqn:E; auto.
  destruct (translate_cpred B r) eqn:E'; auto.
  destruct b, b0; auto.
  apply KILL_AND_FALSE_R_RULE; auto.
Qed.

Lemma KILL_AND_TF_R_RULE' {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) :
      {{{ [ (AND (AND A B) (NOT B), lt) ] }}} mp {{{ [(FALSE,[])] }}}.
Proof. apply KILL_AND_TF_R_RULE. intro. discriminate. Qed.

Lemma KILL_AND_FT_R_RULE {n : nat} (A B : cpred) (lt : list (TType n)) (mp : mprog) (Q : MPredicate n)  (H' : Q <> []) :
      {{{ [ (AND (AND A (NOT B)) B, lt) ] }}} mp {{{ Q }}}.
Proof. eapply SIMPLIFY_CPRED_PRE_RULE.
  Unshelve.
  3: apply (AND (AND A B) FALSE).
  unfold equiv_cpred.
  intros r.
  simpl.
  destruct (translate_cpred A r) eqn:E; auto.
  destruct (translate_cpred B r) eqn:E'; auto.
  destruct b, b0; auto.
  apply KILL_AND_FALSE_R_RULE; auto.
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
    destruct b; try contradiction.
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
    destruct b; try contradiction.
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
    destruct b; try contradiction.
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
        | Some true =>
            Forall (λ t : TType n, vecSatisfies cq.2 (translate t))
              (normalize i lt)
        | _ => False
        end).
  { destruct (Mat_eq_dec (2 ^ n) 1 cq.2 Zero H1 (WF_Zero (2 ^ n) 1)); auto.
    destruct (translate_cpred A cq.1); try contradiction.
    destruct b; try contradiction.
    apply Forall_vecSatisfies_normalize; auto. }
  specialize (H H0 cq' H3); auto.
Qed.

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
(AND A (NOT (REG i)), apply_MEAS q false lt)] }}}.

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
  | simpl; lia 
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

Ltac steane7_true cpred :=
cpred_iff cpred;
[triple
| intros r; simpl;
destruct 
  (r !! 0%nat)%stdpp as [b0|], 
  (r !! 1%nat)%stdpp as [b1|],
  (r !! 2%nat)%stdpp as [b2|],
  (r !! 3%nat)%stdpp as [b3|],
  (r !! 4%nat)%stdpp as [b4|],
  (r !! 5%nat)%stdpp as [b5|];
try reflexivity;
destruct b0, b1, b2, b3, b4, b5;
reflexivity].

Ltac steane7_false cpred :=
cpred_iff (AND cpred FALSE);
[kill 
| intros r; simpl;
destruct 
  (r !! 0%nat)%stdpp as [b0|], 
  (r !! 1%nat)%stdpp as [b1|],
  (r !! 2%nat)%stdpp as [b2|],
  (r !! 3%nat)%stdpp as [b3|],
  (r !! 4%nat)%stdpp as [b4|],
  (r !! 5%nat)%stdpp as [b5|];
try reflexivity;
destruct b0, b1, b2, b3, b4, b5;
reflexivity].

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
U (CNOT 0 7 ;; CNOT 2 7 ;; CNOT 4 7 ;; CNOT 6 7)%pg ;;; MEAS 7 0 ;;; ITE (REG 0) (Id 7) (X 7).

Definition synd_s2z_1 : mprog := 
U (CNOT 1 7 ;; CNOT 2 7 ;; CNOT 5 7 ;; CNOT 6 7)%pg ;;; MEAS 7 1 ;;; ITE (REG 1) (Id 7) (X 7).

Definition synd_s3z_2 : mprog := 
U (CNOT 3 7 ;; CNOT 4 7 ;; CNOT 5 7 ;; CNOT 6 7)%pg ;;; MEAS 7 2 ;;; ITE (REG 2) (Id 7) (X 7).

Definition synd_s1x_3 : mprog := 
U (H 7 ;; CNOT 7 0 ;; CNOT 7 2 ;; CNOT 7 4 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 3 ;;; ITE (REG 3) (Id 7) (X 7).

Definition synd_s2x_4 : mprog := 
U (H 7 ;; CNOT 7 1 ;; CNOT 7 2 ;; CNOT 7 5 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 4 ;;; ITE (REG 4) (Id 7) (X 7).

Definition synd_s3x_5 : mprog := 
U (H 7 ;; CNOT 7 3 ;; CNOT 7 4 ;; CNOT 7 5 ;; CNOT 7 6 ;; H 7)%pg ;;; MEAS 7 5 ;;; ITE (REG 5) (Id 7) (X 7).

Definition correctX : mprog :=
ITE (AND (AND (REG 2) (REG 1)) (REG 0)) (Id 7) (Id 7) ;;;
ITE (AND (AND (REG 2) (REG 1)) (NOT (REG 0))) (X 0) (Id 7) ;;;
ITE (AND (AND (REG 2) (NOT (REG 1))) (REG 0)) (X 1) (Id 7) ;;;
ITE (AND (AND (REG 2) (NOT (REG 1))) (NOT (REG 0))) (X 2) (Id 7) ;;;
ITE (AND (AND (NOT (REG 2)) (REG 1)) (REG 0)) (X 3) (Id 7) ;;;
ITE (AND (AND (NOT (REG 2)) (REG 1)) (NOT (REG 0))) (X 4) (Id 7) ;;;
ITE (AND (AND (NOT (REG 2)) (NOT (REG 1))) (REG 0)) (X 5) (Id 7) ;;;
ITE (AND (AND (NOT (REG 2)) (NOT (REG 1))) (NOT (REG 0))) (X 6) (Id 7).

Definition correctZ : mprog :=
ITE (AND (AND (REG 5) (REG 4)) (REG 3)) (Id 7) (Id 7) ;;;
ITE (AND (AND (REG 5) (REG 4)) (NOT (REG 3))) (Z 0) (Id 7) ;;;
ITE (AND (AND (REG 5) (NOT (REG 4))) (REG 3)) (Z 1) (Id 7) ;;;
ITE (AND (AND (REG 5) (NOT (REG 4))) (NOT (REG 3))) (Z 2) (Id 7) ;;;
ITE (AND (AND (NOT (REG 5)) (REG 4)) (REG 3)) (Z 3) (Id 7) ;;;
ITE (AND (AND (NOT (REG 5)) (REG 4)) (NOT (REG 3))) (Z 4) (Id 7) ;;;
ITE (AND (AND (NOT (REG 5)) (NOT (REG 4))) (REG 3)) (Z 5) (Id 7) ;;;
ITE (AND (AND (NOT (REG 5)) (NOT (REG 4))) (NOT (REG 3))) (Z 6) (Id 7).


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
(*** Copy Paste cpred ***)
steane7_correction (AND
         (AND (AND (AND (AND (AND TRUE (REG 0)) (REG 1)) (REG 2)) (REG 3)) (REG 4))
         (REG 5)).
simpl.
Unshelve.
all: try apply ([(TRUE,normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])]).
f_equal.
solveNormalize; reflexivity.
solveNormalize; reflexivity.
all: try (intro; discriminate).
Qed.

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
do 8 msolve.
(*** Copy Paste cpred ***)
steane7_correction (AND
         (AND (AND (AND (AND (AND TRUE (REG 0)) (REG 1)) (REG 2)) (NOT (REG 3)))
            (REG 4)) (REG 5)).
simpl.
Unshelve.
all: try apply ([(TRUE,normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])]).
f_equal.
solveNormalize; reflexivity.
solveNormalize; reflexivity.
all: try (intro; discriminate).
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
do 8 msolve.
(*** Copy Paste cpred ***)
steane7_correction (AND
         (AND (AND (AND (AND (AND TRUE (REG 0)) (NOT (REG 1))) (REG 2)) (REG 3))
            (REG 4)) (REG 5)).
simpl.
Unshelve.
all: try apply ([(TRUE,normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])]).
f_equal.
solveNormalize; reflexivity.
solveNormalize; reflexivity.
all: try (intro; discriminate).
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
do 8 msolve.
(*** Copy Paste cpred ***)
steane7_correction (AND
         (AND
            (AND (AND (AND (AND TRUE (NOT (REG 0))) (NOT (REG 1))) (REG 2))
               (NOT (REG 3))) (NOT (REG 4))) (REG 5)).
simpl.
Unshelve.
all: try apply ([(TRUE,normalize 0%nat [g1; g2; g3; g4; g5; g6; Zbar; Zanc])]).
f_equal.
solveNormalize; reflexivity.
solveNormalize; reflexivity.
all: try (intro; discriminate).
Qed.


