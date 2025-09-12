Require Import QuantumLib.Eigenvectors.
Require Import HeisenbergFoundations.LinAlg.
Require Import HeisenbergFoundations.F2Math.
Require Export HeisenbergFoundations.Normalization.
Require Export HeisenbergFoundations.Separability.


Local Open Scope Predicate_scope.

(*********************)
(* defining programs *)
(*********************)

Inductive prog :=
| H (n : nat)
| S (n : nat)
| T (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).

(* denote successor as s instead of S since it overlaps with the S gate *)
Notation s := Datatypes.S.

(*** I & Paulis can be derived ***)

Infix ";;" := seq (at level 51, right associativity).

Fixpoint translate_prog (prg_len : nat) (p : prog) : Square (2^prg_len) :=
  match p with 
  | H n => (prog_simpl_app prg_len hadamard n)
  | S n => (prog_simpl_app prg_len Sgate n)
  | T n => (prog_simpl_app prg_len Tgate n)
  | CNOT n1 n2 => (prog_ctrl_app prg_len σx n1 n2)
  | seq p1 p2 => (translate_prog prg_len p2) × (translate_prog prg_len p1)
  end.

Lemma unit_prog : forall (prg_len : nat) (p : prog), 
  WF_Unitary (translate_prog prg_len p).
Proof. intros. induction p as [ | | | | ];
       try (apply unit_prog_simpl_app; auto with unit_db);
       try (apply unit_prog_ctrl_app; auto with unit_db);
       simpl. apply Mmult_unitary; easy.
Qed.


Lemma WF_Matrix_translate_prog : forall (n : nat) (p : prog),
    WF_Matrix (translate_prog n p).
Proof.
  intros n p.
  induction p; simpl.
  all : unfold prog_simpl_app; unfold prog_ctrl_app;
    try bdestruct_all; simpl; auto 15 with wf_db.
Qed.

#[export] Hint Resolve unit_prog : unit_db.
#[export] Hint Resolve WF_Matrix_translate_prog : wf_db.



Definition simpl_prog_H (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = H n).

Definition simpl_prog_S (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = S n).

Definition simpl_prog_T (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = T n).
        
Definition simpl_prog (p : nat -> prog) : Prop := 
  simpl_prog_H p \/ simpl_prog_S p \/ simpl_prog_T p.

Definition simpl_prog' (p : prog) : Prop := 
  match p with
  | H _ => True
  | S _ => True
  | T _ => True
  | _ => False
  end.

Definition ctrl_prog (p : nat -> nat -> prog) : Prop := 
  (forall (n m : nat), p n m = CNOT n m).

Definition ctrl_prog' (p : prog) : Prop :=
  match p with 
  | CNOT _ _ => True 
  | _ => False
  end.




(*****************************************)
(* Defining Eigenvector Semantics *)
(*****************************************)


Definition vecSatisfies {n} (v : Vector n) (U : Square n) : Prop :=
  WF_Matrix v /\ Eigenpair U (v, C1).

Fixpoint vecSatisfiesP {n} (v : Vector (2 ^ n)) (P : Predicate n) {struct P} : Prop :=
  match P with
  | AtoPred s0 => vecSatisfies v (translateA s0)
  | Cap la => WF_Matrix v /\ Forall (fun a0 : AType n => vecSatisfies v (translateA a0)) la
  | Sep Ln_LLT_Perm => WF_Matrix v /\
       Forall (fun T => 
       vecSatisfies v (
                         (perm_to_matrix n (perm_inv n (to_fun 0%nat (snd Ln_LLT_Perm)))) × 
                         translate T
                         × (perm_to_matrix n (perm_inv n (to_fun 0%nat (snd Ln_LLT_Perm)))) †
             ))
        (DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm)))
  | Cup A B => (vecSatisfiesP v A) \/ (vecSatisfiesP v B)
  | Err => False
  end.

Lemma WFA_excluded_middle_semantics : forall {n : nat} (v : Vector (2 ^ n)) (A : AType n),
    WF_AType A -> (vecSatisfiesP v A /\ vecSatisfiesP v (- A)) -> v = Zero.
Proof. intros n v A H0. intro H1. destruct H1. simpl in *.
  destruct H1, H2.
  unfold Eigenpair in *. simpl in *. rewrite Mscale_1_l in *.
  rewrite translateA_gScaleA in H4.
  rewrite Mscale_mult_dist_l in H4.
  rewrite H3 in H4.
  symmetry in H4.
  rewrite <- Mplus_zero_iff_equals_minus in H4; auto.
  replace (v .+ v) with (C2 .* v) in H4 by lma'.
  replace Zero with (C2 .* @Zero (2 ^ n) 1%nat) in H4 by lma'.
  apply Mscale_cancel in H4; auto; try nonzero.
  inversion H0.
  apply restricted_addition_syntactic_implies_proper_length_AType in H5; auto.
Qed.

Lemma vecSatisfies_Zero_r : forall {n : nat} (v : Vector n),
    vecSatisfies v Zero -> v = Zero.
Proof. intros n v H0.
  unfold vecSatisfies in H0.
  destruct H0.
  unfold Eigenpair in H1.
  simpl in H1.
  rewrite Mscale_1_l, Mmult_0_l in H1; subst; auto.
Qed.

Lemma vecSatisfies_Zero_l : forall {n : nat} (A : Square n), vecSatisfies Zero A.
Proof. intros n A.
  unfold vecSatisfies.
  split; auto with wf_db.
  unfold Eigenpair; simpl.
  rewrite Mmult_0_r.
  rewrite Mscale_0_r.
  auto.
Qed.

Lemma vecSatisfies_I : forall {n : nat} (v : Vector n), 
    WF_Matrix v -> vecSatisfies v (I n).
Proof. intros n v.
  unfold vecSatisfies.
  split; auto.
  unfold Eigenpair.
  simpl.
  rewrite Mscale_1_l, Mmult_1_l; auto.
Qed.

Lemma vecSatisfiesP_implies_WF_Matrix : forall {n : nat} (v : Vector (2 ^ n)%nat) (P : Predicate n), vecSatisfiesP v P -> WF_Matrix v.
Proof. intros n v P H0. 
    induction P.
    - simpl in H0. unfold vecSatisfies in H0.
      destruct H0; auto.
    - destruct H0. auto.
    - inversion H0; auto.
    - inversion H0; auto.
    - inversion H0.
Qed.

Lemma vecSatisfiesP_defaultP_I : forall {n : nat} (v : Vector (2 ^ n)),
    WF_Matrix v -> vecSatisfiesP v (defaultP_I n).
Proof. intros n v H0. unfold defaultP_I. simpl.
  unfold translateA; simpl.
  rewrite Mplus_0_l.
  rewrite translate_defaultT_I.
  apply vecSatisfies_I; auto.
Qed.



(** ** Separability Proof ** **)

Lemma vecSatisfiesP_iff_stabilizeByListT : forall {n : nat} (Lt : list (TType n)),
(forall v : Vector (2 ^ n)%nat, 
    vecSatisfiesP v (Cap (map TtoA Lt)) <->
      stabilizeByListT (fun v => WF_Matrix v) Lt v).
Proof. intros n Lt v.
  unfold vecSatisfiesP, stabilizeByListT.
  split; intros H; destruct H; split; auto; try rewrite <- Forall_forall in *;
    induction Lt; auto; simpl; constructor; simpl in *; 
    rewrite Forall_cons_iff in H1; destruct H1; auto; clear IHLt.
  - unfold vecSatisfies in H1. destruct H1. unfold Eigenpair in H3. simpl in H3. 
    rewrite Mscale_1_l in H3. unfold translateA in H3. simpl in H3. rewrite Mplus_0_l in H3.
    auto.
  - unfold vecSatisfies. split; auto. unfold Eigenpair. simpl. 
    rewrite Mscale_1_l. unfold translateA. simpl. rewrite Mplus_0_l.
    auto.
 Qed.


(*** This is only for +1 eigenstates*)
Lemma separability_proof_left :
  forall (n m : nat) (Lt : list (TType n)),
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat ->
    Lt <> [] -> Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt ->
    commutingListT Lt -> length Lt = n -> 
    (forall v : Vector (2 ^ (n + m))%nat,
      (exists w : Vector (2 ^ n)%nat, WF_Matrix w /\ (exists u : Vector (2 ^ m)%nat, WF_Matrix u /\
        vecSatisfiesP w (Cap (map TtoA Lt)) /\ v = w ⊗ u)) <->
        vecSatisfiesP v (Cap (map (uncurry gTensorA)
                                (combine 
                                   (map TtoA Lt) 
                                   (map TtoA (repeat (defaultT_I m) (length Lt))))))).
Proof. intros n m Lt H0 H1 H2 H3 H4 H5 H6 v.
  split; intros.
  - destruct H7 as [w [WFw [u [WFu [vecSatisfiesPw vwu]]]]].
    rewrite vwu.
    simpl. split; auto with wf_db.
    clear - vecSatisfiesPw WFw WFu H3.
    induction Lt; auto.
    simpl in *. destruct vecSatisfiesPw. 
    rewrite Forall_cons_iff in *. destruct H1, H3.
    assert (H5 := conj H0 H2).
    specialize (IHLt H4 H5).
    constructor; auto.
    unfold uncurry. simpl.
    unfold translateA in *. simpl in *. rewrite Mplus_0_l in *.
    unfold vecSatisfies in *.
    destruct H1. split; auto with wf_db.
    unfold Eigenpair in *. simpl in *.
    rewrite Mscale_1_l in *.
    rewrite translate_gTensorT.
    + rewrite translate_defaultT_I. setoid_rewrite kron_mixed_product'; auto.
      2-3: rewrite Nat.pow_add_r; auto.
      rewrite Mmult_1_l; auto. f_equal; auto.
    + destruct H3. auto.
    + unfold defaultT_I. simpl. rewrite repeat_length. auto.
  - assert (H8 : forall A B : Prop, ~ (A /\ B) <-> (A -> ~ B)).
    { intros A B. split; intros.
      - apply Classical_Prop.not_and_or in H8. destruct H8; auto.
      - apply Classical_Prop.or_not_and. destruct (Classical_Prop.classic A); auto. }
    assert (H9 : ((forall w : Vector (2 ^ n)%nat, WF_Matrix w ->  
                           (forall u : Vector (2 ^ m)%nat, WF_Matrix u ->
                                   vecSatisfiesP w (Cap (map TtoA Lt)) ->
                                          ~ v = w ⊗ u)) -> False) <->
                   (exists w : Vector (2 ^ n),
                       WF_Matrix w /\
                         (exists u : Vector (2 ^ m),
                             WF_Matrix u /\
                               vecSatisfiesP w (Cap (map TtoA Lt)) /\ 
                               v = w ⊗ u))).
    { split; intros. 
      - apply Classical_Prop.NNPP. intro.
        contradict H9.
        intros w H9 u H11 H12. 
        apply Classical_Pred_Type.not_ex_all_not with (n := w) in H10.
        rewrite H8 in H10. specialize (H10 H9).
         apply Classical_Pred_Type.not_ex_all_not with (n := u) in H10.
         rewrite H8 in H10. specialize (H10 H11).
         apply Classical_Prop.not_and_or in H10.
         destruct H10; auto.
      - destruct H9 as [w [WFw [u [WFu [vecSatisfiesPw vwu]]]]].
        apply (H10 w WFw u WFu vecSatisfiesPw vwu). }
    rewrite <- H9. clear H8 H9.
    intros H8.
    assert (WF_Matrix v).
    { destruct H7; auto. }
    destruct (SVD v H9) as [U [L [V [WFUU [WFUV [WFDL [WFNL AULVd]]]]]]].
    bdestruct (m =? 0)%nat.
    + subst.
      assert (@eq (list (AType (n + 0))) (map (uncurry gTensorA)
               (combine (map TtoA Lt)
                  (map TtoA (repeat (defaultT_I 0) (length Lt)))))
                (map TtoA Lt)).
      { unfold defaultT_I. simpl. rewrite map_repeat.
        apply nth_ext with (d := (uncurry gTensorA) (([defaultT_I n]), ([(C1,[])]))) (d' := defaultT_I (n + 0)).
        * rewrite ! map_length. rewrite combine_length. rewrite repeat_length, map_length.
          minmax_breakdown. auto.
        * intros n0 H10. rewrite ! map_nth.
          rewrite combine_nth.
          2: rewrite map_length, repeat_length; auto.
          rewrite map_nth with (d := defaultT_I n).
          rewrite nth_repeat.
          unfold uncurry.
          simpl. unfold TtoA. do 2 f_equal.
          unfold gTensorT. replace (n + 0)%nat with n by lia.
          destruct (nth n0 Lt (defaultT_I n)). rewrite Cmult_1_r, app_nil_r. auto. }
      rewrite H10 in H7. 
      assert (n + 0 = n)%nat by lia.
      rewrite H11 in *.
      replace (2 ^ n)%nat with (2 ^ (n + 0))%nat in * by (rewrite Nat.add_0_r; auto).
      specialize (H8 (U × L × (V) †) H9 (I 1) WF_I1 H7).
      rewrite kron_1_r in H8. contradiction.
    + assert (v = (V 0%nat 0%nat)^* .* (U × L)).
      { rewrite AULVd.
        unfold Mmult, Matrix.scale, adjoint. simpl.
        prep_matrix_equality. destruct WFUV.
        bdestruct (y =? 0)%nat.
        - subst. lca.
        - rewrite H11 at 1; auto; try lia. rewrite Cconj_0, Cmult_0_r, Cplus_0_l.
          assert (Σ (fun y0 : nat => U x y0 * L y0 y) (2 ^ (n + m)) = C0).
          { destruct WFDL.
            rewrite big_sum_0_bounded; auto; intros.
            rewrite H14; auto; try lia; try lca. }
          rewrite H14. lca. }
      assert ((2 ^ (n + m)) = (2 ^ n) * (2 ^ m))%nat by apply Nat.pow_add_r.

      simpl in H7. destruct H7.

      rewrite matrix_span_as_get_col_sum in H11.
      2: destruct WFDL; auto.

      assert ( fold_right Mplus Zero
                 (map (fun i : nat => L i 0%nat .* get_col U i)
                    (List.seq 0 (2 ^ (n + m)))) = 
                 fold_right Mplus Zero
                         (map (fun M => M)   
                   (map (fun i : nat => L i 0%nat .* get_col U i)
                      (List.seq 0 (2 ^ (n + m))))))
      by (rewrite map_map; auto).
      rewrite H14 in H11.
      rewrite <- fold_right_Mplus_Zero_Mscale_distr with (c := (V 0%nat 0%nat) ^* ) in H11.
      rewrite map_map in H11.
      assert ((map (fun i : nat => (V 0%nat 0%nat) ^* .* (L i 0%nat .* get_col U i))
             (List.seq 0 (2 ^ (n + m)))) =
                (map (fun i : nat => 
                        fold_right Mplus Zero
                          (map
                             (fun j : nat =>
                                (V 0%nat 0%nat) ^* * (L i 0%nat) * (U j i) .* 
                                                               (@e_i (2 ^ n)%nat (j / (2 ^ m)%nat) ⊗ @e_i (2 ^ m)%nat (j mod (2 ^ m)%nat)))
                          (List.seq 0 (2 ^ (n + m)))))
                  (List.seq 0 (2 ^ (n + m))))).
      { apply map_ext_Forall. rewrite Forall_forall. intros x H15.  rewrite in_seq in H15.
        rewrite (vector_as_e_i_sum (get_col U x)) at 1.
        assert ((map (fun i : nat => get_col U x i 0%nat .* @ e_i (2 ^ (n + m))  i)
              (List.seq 0 (2 ^ (n + m)))) = 
                  (map (fun M => M) (map (fun i : nat => get_col U x i 0%nat .* e_i i)
              (List.seq 0 (2 ^ (n + m)))))) by (rewrite map_map; auto).
        rewrite H16.
        rewrite Mscale_assoc.
        rewrite <- fold_right_Mplus_Zero_Mscale_distr.
        rewrite ! map_map.
        f_equal.
        apply map_ext_Forall. rewrite Forall_forall. intros x0 H17. rewrite in_seq in H17.
        rewrite ! H12.
        rewrite e_i_kron_inv; auto; try lia.
        rewrite ! Mscale_assoc. f_equal.
        destruct WFUU. auto with wf_db. }
      rewrite H15 in H11.
      rewrite fold_right_Mplus_Zero_double_swap 
        with (F := (fun i j : nat =>
                     (V 0%nat 0%nat) ^* * L i 0%nat * U j i .* (e_i (j / 2 ^ m) ⊗ e_i (j mod 2 ^ m))))
        in H11.
      assert ((fun j : nat =>
              fold_right Mplus Zero
                (map
                   (fun i : nat =>
                    (V 0%nat 0%nat) ^* * L i 0%nat * U j i
                    .* (@e_i (2 ^ n)%nat (j / 2 ^ m) ⊗ @e_i (2 ^ m)%nat (j mod 2 ^ m)))
                   (List.seq 0 (2 ^ (n + m))))) =
                (fun j : nat =>
              (fold_right Cplus C0
                (map
                   (fun i : nat =>
                    (V 0%nat 0%nat) ^* * L i 0%nat * U j i)
                   (List.seq 0 (2 ^ (n + m))))) .* (e_i (j / 2 ^ m) ⊗ e_i (j mod 2 ^ m)))).
      { apply functional_extensionality. intros x.
        rewrite fold_right_Mplus_Zero_collect_scalar. auto. }
      rewrite H16 in H11.
      clear H14 H15 H16.

      assert (forall k : nat, (k < length Lt)%nat -> translate (gTensorT (nth k Lt (defaultT_I n)) (defaultT_I m)) × v = v).
      { rewrite Forall_map in H13.
        rewrite Forall_forall in H13.
        intros k H14. specialize (H13 (nth k (combine (map TtoA Lt)
             (map TtoA (repeat (defaultT_I m) (length Lt)))) ([defaultT_I n],[defaultT_I m] ))).  
        assert (In
          (nth k
             (combine (map TtoA Lt)
                (map TtoA
                   (repeat (defaultT_I m) (length Lt))))
             ([defaultT_I n], [defaultT_I m]))
          (combine (map TtoA Lt)
             (map TtoA (repeat (defaultT_I m) (length Lt))))).
        { apply nth_In. rewrite combine_length, ! map_length, repeat_length. 
          minmax_breakdown. auto. }
        specialize (H13 H15). clear H15.
        rewrite combine_nth in H13.
        rewrite map_nth with (d := defaultT_I n) in H13.
        rewrite map_nth with (d := defaultT_I m) in H13.
        rewrite nth_repeat in H13.
        unfold uncurry. simpl in H13. 
        2 : rewrite ! map_length, repeat_length; auto.
        unfold translateA in H13. simpl in H13. rewrite Mplus_0_l in H13.
        unfold vecSatisfies in H13. destruct H13. unfold Eigenpair in H15. simpl in H15.
        rewrite Mscale_1_l in H15. auto. }
      
      setoid_rewrite translate_gTensorT in H14.
      2: { bdestruct (k <? length Lt)%nat.
           rewrite Forall_nth in H3. specialize (H3 k (defaultT_I n) H15).
           destruct H3. auto. rewrite nth_overflow; try lia. unfold defaultT_I. simpl. 
           rewrite repeat_length. auto. }
      2: { unfold defaultT_I. simpl. rewrite repeat_length. auto. }

      rewrite translate_defaultT_I in H14.
      rewrite H11 in H14. rewrite ! H12 in H14.
      setoid_rewrite <- fold_right_Mplus_Zero_map_Mmult_distr in H14.
      setoid_rewrite map_map in H14.

      assert (forall k : nat, (fun x : nat =>
              translate (nth k Lt (defaultT_I n)) ⊗ I (2 ^ m)
              × (fold_right Cplus 0
                   (map (fun i : nat => (V 0%nat 0%nat) ^* * L i 0%nat * U x i)
                      (List.seq 0 (2 ^ n * 2 ^ m)))
                 .* (e_i (x / 2 ^ m) ⊗ e_i (x mod 2 ^ m)))) =
                         (fun x : nat =>
              fold_right Cplus 0
    (map (fun i : nat => (V 0%nat 0%nat) ^* * L i 0%nat * U x i)
       (List.seq 0 (2 ^ n * 2 ^ m)))
  .* (translate (nth k Lt (defaultT_I n)) × e_i (x / 2 ^ m)
      ⊗ (e_i (x mod 2 ^ m))))).
      { intro. apply functional_extensionality. intro. rewrite Mscale_mult_dist_r. 
        rewrite kron_mixed_product. rewrite Mmult_1_l; auto with wf_db. }
      setoid_rewrite H15 in H14. clear H15.
      setoid_rewrite fold_right_Mplus_Zero_big_sum in H14.
      
      assert (forall k : nat, (fun i : nat =>
           fold_right Cplus 0
             (map (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0)
                (List.seq 0 (2 ^ n * 2 ^ m)))
           .* (translate (nth k Lt (defaultT_I n)) × @e_i (2 ^ n)%nat (i / 2 ^ m)
               ⊗ @e_i (2 ^ m)%nat (i mod 2 ^ m))) =
                (fun i : nat =>
           (big_sum (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0) (2 ^ n * 2 ^ m))
           .* (translate (nth k Lt (defaultT_I n)) × e_i (i / 2 ^ m)
               ⊗ e_i (i mod 2 ^ m)))).
      { intro. apply functional_extensionality. intro.
        rewrite fold_right_Cplus_C0_big_sum. auto. }
      setoid_rewrite H15 in H14. clear H15.

      assert ((fun i : nat =>
           fold_right Cplus 0
             (map (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0)
                (List.seq 0 (2 ^ n * 2 ^ m)))
           .* (@e_i (2 ^ n)%nat (i / 2 ^ m) ⊗ @e_i (2 ^ m)%nat (i mod 2 ^ m))) = 
                (fun i : nat =>
           (big_sum (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0) (2 ^ n * 2 ^ m))
             .* (e_i (i / 2 ^ m) ⊗ e_i (i mod 2 ^ m)))).
      { apply functional_extensionality. intro.
        rewrite fold_right_Cplus_C0_big_sum. auto. }
      setoid_rewrite H15 in H14. clear H15.
      
     setoid_rewrite <- fold_right_Mplus_Zero_big_sum in H14.
     setoid_rewrite fold_right_Mplus_Zero_scaled_vector_sum in H14.
     
     2: { rewrite Forall_forall. intros x H15. apply WF_kron; auto with wf_db.
          apply WF_mult; auto with wf_db. bdestruct (k <? length Lt)%nat.
          apply WF_translate. rewrite Forall_nth in H3. apply H3; auto.
          rewrite nth_overflow; auto. rewrite translate_defaultT_I. auto with wf_db. }

     2: { rewrite Forall_forall. intros x H15. apply WF_kron; auto with wf_db. }

     assert (forall k : nat, (k < length Lt)%nat -> @Mmult (2 ^ n * 2 ^ m)%nat (2 ^ n * 2 ^ m)%nat 1%nat
         (fun r c : nat =>
         ((translate (nth k Lt (defaultT_I n)) .+ (- C1)%C .* (I (2^n)%nat)) × @e_i (2^n)%nat (c / 2 ^ m) ⊗ @e_i (2^m)%nat (c mod 2 ^ m))
           r 0%nat) 
         (fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0) = Zero).
     { intros k H15. specialize (H14 k H15).
       prep_matrix_equality. 
       apply f_equal_inv with (x := x) in H14.
       apply f_equal_inv with (x := y) in H14.
       unfold Mmult at 1 in H14. unfold Mmult at 2 in H14.
       unfold Mmult at 1. unfold Zero.
       apply Cplus_inv_r with (c :=
          (@Mmult (2 ^ n * 2 ^ m)%nat (2 ^ n * 2 ^ m)%nat 1%nat
            (fun r c : nat => (@e_i (2^n)%nat (c / 2 ^ m) ⊗ @e_i (2^m)%nat (c mod 2 ^ m)) r 0%nat)
              (fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0)) x y).
       unfold Mmult at 2. unfold Mmult at 2. rewrite Cplus_0_l.
       rewrite <- H14 at 2.
       rewrite <- @big_sum_plus with (H0 := C_is_group).
       apply big_sum_eq_bounded. intros x0 H16. 
       rewrite <- ! Cmult_plus_distr_r. f_equal. unfold Mplus, Matrix.scale, Mmult.
       unfold kron. simpl. rewrite <- ! Cmult_plus_distr_r. f_equal.
       unfold I. bdestruct_all.
       - replace (2 ^ n)%nat with ((x / 2 ^ m) + 1 + ((2 ^ n) - (Datatypes.S (x / 2 ^ m))))%nat by lia.
         rewrite ! big_sum_sum; simpl. rewrite ! Cplus_0_l.
         rewrite ! andb_true_r. rewrite ! Nat.add_0_r. bdestruct_all.
         rewrite Cmult_1_r. rewrite Cmult_plus_distr_r.
         rewrite <- ! Cplus_assoc. setoid_rewrite Cplus_comm at 5.
         
         assert (Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat y0 +
      (- C1) * (if (x / 2 ^ m =? y0)%nat && true then C1 else 0)) *
     @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) y0 0%nat) (x / 2 ^ m) +
  (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat (x / 2 ^ m)%nat *
   @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
   (- C1 * @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
    (@e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
     Σ
       (fun x1 : nat =>
        (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat
           (x / 2 ^ m + 1 + x1)%nat +
         (- C1) * (if (x / 2 ^ m =? x / 2 ^ m + 1 + x1)%nat && true then C1 else 0)) *
        @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m + 1 + x1)%nat 0%nat) 
       (2 ^ n - s (x / 2 ^ m)))))  =
                   Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat y0 +
      (- C1) * (if (x / 2 ^ m =? y0)%nat && true then C1 else 0)) *
     @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) y0 0%nat) (x / 2 ^ m) +
  (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat (x / 2 ^ m)%nat *
   @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
   (- C1 * @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
    (@e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat)) +
     Σ
       (fun x1 : nat =>
        (translate (nth k Lt (defaultT_I n)) (x / 2 ^ m)%nat
           (x / 2 ^ m + 1 + x1)%nat +
         (- C1) * (if (x / 2 ^ m =? x / 2 ^ m + 1 + x1)%nat && true then C1 else 0)) *
        @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m + 1 + x1)%nat 0%nat) 
       (2 ^ n - s (x / 2 ^ m)))) by (rewrite ! Cplus_assoc; auto). 
         rewrite H19. clear H19.
         assert (- C1 * @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat +
                   @e_i ((((x / 2 ^ m) + 1) + (2 ^ n - Datatypes.S (x / 2 ^ m))))%nat (x0 / 2 ^ m) (x / 2 ^ m)%nat 0%nat = C0) by lca.
         rewrite H19. clear H19. rewrite Cplus_0_r.
         f_equal.
         + apply big_sum_eq_bounded. intros x1 H19. 
           bdestruct_all; simpl; auto; try lia; try lca. 
         + f_equal. apply big_sum_eq_bounded. intros x1 H19. 
           bdestruct_all; simpl; auto; try lia; try lca. 
       - assert (WF_Matrix (@e_i (2^n)%nat (x0 / 2 ^ m))) by auto with wf_db.
         rewrite H18; try lia. rewrite Cplus_0_r.
         apply big_sum_eq_bounded. intros x1 H19.
         bdestruct_all. simpl. rewrite Cmult_0_r, Cplus_0_r. auto.
       - apply C_is_comm_group. }
     
     assert (forall r : nat, Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0) (2 ^ n * 2 ^ m) =
                        (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U r 0%nat).
     { intros r. destruct WFDL.
       rewrite big_sum_unique with (k := (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U r 0%nat); auto.
       exists 0%nat. repeat split; auto. rewrite <- H12.
       assert (0 < 2 ^ (n + m))%nat.
       { assert (0 ^ (n + m) = 0)%nat. { apply Nat.pow_0_l; lia. }
         rewrite <- H18 at 1.
         apply Nat.pow_lt_mono_l; lia. }
       auto.
       intros x' H18 H19.
       rewrite H17; try lia; lca. }

     assert ((fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0) =
               (fun r c : nat =>
           if (c =? 0)%nat
           then
            (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U ((2^m * (r / 2^m) + r mod 2^m)%nat) 0%nat
           else 0)).
     { prep_matrix_equality. bdestruct_all; try rewrite H16; auto.
       rewrite <- Nat.div_mod_eq. auto. }
     rewrite H17 in H15.

     assert ((2 ^ n * 2 ^ m) = (2 ^ m * 2 ^ n))%nat by (apply Nat.mul_comm).

     unfold Mmult in H15 at 1.

assert (forall k : nat,
(fun x z : nat =>
         Σ
           (fun y : nat =>
            ((translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n))
             × @e_i (2^n)%nat (y / 2 ^ m) ⊗ @e_i (2^m)%nat (y mod 2 ^ m)) x 0%nat *
            (if (z =? 0)%nat
             then
              (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
              U (2 ^ m * (y / 2 ^ m) + y mod 2 ^ m)%nat 0%nat
             else 0)) (2 ^ n * 2 ^ m)) =
  (fun x y : nat =>
         if (y =? 0)%nat then
(@big_sum (Matrix (2 ^ n * 2 ^ m) 1%nat) (M_is_monoid (2 ^ n * 2 ^ m) 1%nat)
    (fun y0 : nat =>
     (@kron (2^n)%nat 1%nat (2^m)%nat 1%nat 
       (fun r c : nat =>
       (Σ
       (fun x0 : nat =>
        ((translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) × @e_i (2^n)%nat x0)
          r c  *
        ((V 0%nat 0%nat) ^* * L 0%nat 0%nat * U (2 ^ m * x0 + y0)%nat 0%nat)) (2 ^ n)))
       
       (@e_i (2^m)%nat y0))
) 

(2 ^ m)) x 0%nat

else C0

)).
{ intros k. prep_matrix_equality. bdestruct_all; subst.
  rewrite Msum_Csum.
     rewrite ! H18.
     rewrite <- big_sum_double_sum
with 
(f := (fun i j : nat =>
     ((translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) × e_i (i)
      ⊗ e_i (j)) x 0%nat *
     ( (*if (y =? 0)%nat
      then *)
       (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
       U (2 ^ m * (i) + j)%nat 0%nat
      (* else 0 *)))).
     unfold kron. simpl.
     rewrite big_sum_swap_order at 1.
     apply big_sum_eq_bounded. intros x0 H19.
     rewrite @big_sum_mult_r with (H2 := C_is_ring).
     apply big_sum_eq_bounded. intros x1 H20. simpl.
     lca. 
     rewrite big_sum_0_bounded; auto; intros; lca. }
setoid_rewrite H19 in H15. clear H19.

assert (@Zero (2 ^ n * 2 ^ m)%nat 1%nat =
          (fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum (Vector (2^n * 2^m)%nat) (M_is_monoid (2^n * 2^m)%nat 1%nat)
            (fun y0 : nat =>
             (@Zero (2^n)%nat 1%nat) ⊗ @e_i (2^m)%nat y0) (2 ^ m) x 0%nat
         else 0)).
{ prep_matrix_equality. unfold Zero.
  bdestruct_all; simpl; subst.
  rewrite big_sum_0_bounded; auto; intros.
  rewrite kron_0_l. lma'. auto. }
rewrite H19 in H15.

assert (forall k : nat, (k < length Lt)%nat -> 
                 forall i, (0 <= i < 2^m)%nat ->
              (fun r c : nat =>
              Σ
                (fun x0 : nat =>
                 ((translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n))
                  × e_i x0) r c *
                 ((V 0%nat 0%nat) ^* * L 0%nat 0%nat *
                  U (2 ^ m * x0 + i)%nat 0%nat)) (2 ^ n)) =
                @Zero (2^n)%nat 1%nat).
{ intros k H20 i H21.
  apply @delete_right_kron_from_vector
          with (j := (2^m)%nat) (k := (2^m)%nat)
          (A_i := (fun y0 : nat =>
             (fun r c : nat =>
              Σ
                (fun x0 : nat =>
                 ((translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n))
                  × e_i x0) r c *
                 ((V 0%nat 0%nat) ^* * L 0%nat 0%nat *
                  U (2 ^ m * x0 + y0)%nat 0%nat)) (2 ^ n))))
               (B_i := (fun y0 : nat => @Zero (2^n)%nat 1%nat)); auto; try lia.
  - rewrite Forall_forall. intros x H22. rewrite in_seq in H22.
    unfold WF_Matrix. intros x0 y H23.
    destruct H23.
    + rewrite big_sum_0_bounded; auto; intros. unfold Mmult.
      rewrite big_sum_0_bounded; intros; try lca.
      assert (WF_Matrix (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n))).
      { apply WF_plus; auto with wf_db. apply WF_translate.
        rewrite Forall_nth in H3. apply H3; lia. }
      rewrite H26; try lia; lca.
    + rewrite big_sum_0_bounded; auto; intros. unfold Mmult.
      pose (@WF_e_i (2^n)%nat x1) as WFei.
      rewrite big_sum_0_bounded; intros; try lca.
      rewrite WFei; try lia; lca.
  - rewrite Forall_forall. intros x H22. auto with wf_db. }
unfold Mmult in H20.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        @eq (Vector (2^n)%nat)
        (fun r c : nat =>
         Σ
           (fun x0 : nat =>
            Σ
              (fun y : nat =>
               (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) r y *
               @e_i (2^n)%nat x0 y c) (2 ^ n) *
            ((V 0%nat 0%nat) ^* * L 0%nat 0%nat * U (2 ^ m * x0 + i)%nat 0%nat))
           (2 ^ n))
        (@Matrix.scale (2^n)%nat 1%nat
        ((V 0%nat 0%nat) ^* * L 0%nat 0%nat)
        (fun r c : nat =>
         Σ
           (fun x0 : nat =>
            Σ
              (fun y : nat =>
               (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) r y *
               @e_i (2^n)%nat x0 y c) (2 ^ n) *
            (U (2 ^ m * x0 + i)%nat 0%nat))
           (2 ^ n)))).
{ intros k H21 i H22.
  prep_matrix_equality. unfold Matrix.scale.
  rewrite @big_sum_mult_l with (H2 := C_is_ring).
  apply big_sum_eq_bounded; intros. simpl. lca. }

  assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        (V 0%nat 0%nat) ^* * L 0%nat 0%nat
        .* (fun r c : nat =>
            Σ
              (fun x0 : nat =>
               Σ
                 (fun y : nat =>
                  (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) r y *
                  @e_i (2^n)%nat x0 y c) (2 ^ n) * U (2 ^ m * x0 + i)%nat 0%nat) 
              (2 ^ n)) = @Zero (2^n)%nat 1%nat).
{ intros k H22 i H23. specialize (H20 k H22 i H23).  specialize (H21 k H22 i H23).
  rewrite <- H21. rewrite H20. auto. }
clear H20 H21.

assert (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (@Zero (2^n)%nat 1%nat) = (@Zero (2^n)%nat 1%nat)).
{ rewrite Mscale_0_r. auto. }
setoid_rewrite <- H20 in H22.

assert ((V 0%nat 0%nat) <> C0). 
{ intro. assert (V = Zero).
  { prep_matrix_equality. unfold Zero. destruct WFUV.
    bdestruct (x =? 0)%nat; bdestruct (y =? 0)%nat; subst; auto; rewrite H23; auto; try lia. }
  destruct WFUV. rewrite H23 in H25. rewrite Mmult_0_r in H25.
  contradict_matrix_equalities. }
assert ((V 0%nat 0%nat) ^* <> C0).
{ apply Cconj_neq_0; auto. }
assert (L 0%nat 0%nat <> C0).
{ intro. assert (L = Zero).
  { prep_matrix_equality. unfold Zero. destruct WFDL.
    bdestruct (x =? 0)%nat; bdestruct (y =? 0)%nat; subst; auto.
    rewrite H25; auto; lia. }
  rewrite H25 in AULVd. rewrite Mmult_0_r, Mmult_0_l in AULVd.
  subst.
  assert (WF_Matrix (@Zero (2^n)%nat 1%nat)) as zero2n by auto with wf_db.
  assert (WF_Matrix (@Zero (2^m)%nat 1%nat)) as zero2m by auto with wf_db.
  assert (vecSatisfiesP (@Zero (2^n)%nat 1%nat) (Cap (map TtoA Lt))).
  { unfold vecSatisfiesP. split; auto with wf_db.
    unfold vecSatisfies. unfold Eigenpair. simpl.
    rewrite Forall_forall. intros x H25.
    split; auto with wf_db. rewrite Mmult_0_r, Mscale_0_r. auto. }
  specialize (H8 (@Zero (2^n)%nat 1%nat) zero2n (@Zero (2^m)%nat 1%nat) zero2m H25).
  rewrite kron_0_l in H8. contradiction. } 
remember H24 as Lnonzero. clear HeqLnonzero.
assert ((V 0%nat 0%nat) ^* * L 0%nat 0%nat <> C0).
{ intro. apply Cmult_integral in H25. destruct H25; contradiction. }
clear H20 H21 H23 H24.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        (fun r c : nat =>
            Σ
              (fun x0 : nat =>
               Σ
                 (fun y : nat =>
                  (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) r y *
                  @e_i (2^n)%nat x0 y c) (2 ^ n) * U (2 ^ m * x0 + i)%nat 0%nat) 
              (2 ^ n)) = (@Zero (2^n)%nat 1%nat)).
{ intros. specialize (H22 k H20 i H21). apply Mscale_cancel in H22; auto. }

clear H22 H25.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        (fun r c : nat =>
           (if (c =? 0)%nat then
            Σ
              (fun y : nat =>
               (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) r y * U (2 ^ m * y + i)%nat 0%nat) 
           (2 ^ n) else C0)) = @Zero (2^n)%nat 1%nat).
{ intros k H21 i H22.
  specialize (H20 k H21 i H22).
  rewrite <- H20.
  prep_matrix_equality. bdestruct_all; subst.
  - apply big_sum_eq_bounded; intros. f_equal.
    unfold e_i. simpl. symmetry. apply big_sum_unique. exists x0.
    repeat split; auto. bdestruct (x0 =? x0)%nat; bdestruct (x0 <? 2^n)%nat; try lia. simpl. lca.
    intros x' H24 H25. bdestruct (x' =? x0)%nat; bdestruct (x' <? 2^n)%nat; try lia. simpl. lca.
  - rewrite big_sum_0_bounded; auto; intros.
    assert (Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n)) x y0 * @e_i (2^n)%nat x0 y0 y)
    (2 ^ n) = C0).
    { rewrite big_sum_0_bounded; auto; intros.
      rewrite (@WF_e_i (2^n)%nat x0); try lca; try lia. }
    rewrite H25. lca. }

clear H20.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        @Mmult (2^n)%nat (2^n)%nat 1%nat
          (translate (nth k Lt (defaultT_I n)) .+ - C1 .* I (2 ^ n))
        (fun r c : nat =>
         if (c =? 0)%nat
         then U (2 ^ m * r + i)%nat 0%nat
         else 0) = @Zero (2^n)%nat 1%nat).
{ intros k H20 i H22.
  unfold Mmult. specialize (H21 k H20 i H22).
  rewrite <- H21. prep_matrix_equality.
  bdestruct_all; subst; auto.
  rewrite big_sum_0_bounded; auto; intros. lca. }

assert (forall i j : nat, (i <> 0)%nat \/ (j <> 0)%nat -> L i j = C0).
{ intros i j H22. destruct WFDL. destruct H22.
  - bdestruct (j =? 0)%nat; subst.
    + apply H24. lia.
    + rewrite H23; auto; lia.
  - rewrite H23; auto; lia. }

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
       @eq (Vector (2^n)%nat)
        (@Mmult (2^n)%nat (2^n)%nat 1%nat (translate (nth k Lt (defaultT_I n))) 
              (fun r c : nat => if (c =? 0)%nat then U (2 ^ m * r + i)%nat 0%nat else 0))
        (fun r c : nat => if (c =? 0)%nat then U (2 ^ m * r + i)%nat 0%nat else 0)).
{ intros k H23 i H24.
  specialize (H20 k H23 i H24).
  setoid_rewrite <- Mplus_0_r at 5.
  rewrite <- H20.
  setoid_rewrite <- Mmult_1_l at 6.
  rewrite <- Mmult_plus_distr_r.
  f_equal. setoid_rewrite Mplus_comm at 2.
  rewrite <- Mplus_assoc.
  setoid_rewrite <- Mplus_0_l at 1. f_equal.
  lma'.
  unfold WF_Matrix. intros x y H25.
  bdestruct_all; simpl; subst; auto.
  destruct WFUU.
  rewrite H26; auto. rewrite H12. nia. }

assert (forall i : nat,
        (0 <= i < 2 ^ m)%nat ->
        @vecSatisfiesP n
          (fun r c : nat => if (c =? 0)%nat then U (2 ^ m * r + i)%nat 0%nat else 0)
          (Cap (map TtoA Lt))).
{ intros i H24. unfold vecSatisfiesP. split.
  - unfold WF_Matrix. intros.
    bdestruct_all; simpl; subst; auto.
    destruct WFUU.
    rewrite H26; auto. rewrite H12. nia. 
  - rewrite Forall_forall. intros x H25.
    apply In_nth with (d := defaultT_I n) in H25.
    destruct H25 as [k [kbound kth]]. subst.
    rewrite map_nth with (d := defaultT_I n).
    simpl. unfold translateA. simpl. rewrite Mplus_0_l.
    unfold vecSatisfies.
    split. 
    + unfold WF_Matrix. intros.
      bdestruct_all; simpl; subst; auto.
      destruct WFUU.
      rewrite H26; auto. rewrite H12. nia.
    + unfold Eigenpair. simpl. rewrite Mscale_1_l.
      apply H23; auto. rewrite map_length in kbound; auto. }

setoid_rewrite vecSatisfiesP_iff_stabilizeByListT in H24.
setoid_rewrite vecSatisfiesP_iff_stabilizeByListT in H8.

assert (@CM.dimension (2^n)%nat (stabilizeByListT (fun v => WF_Matrix v) Lt) 1%nat).
{ assert (@CM.subspace (2 ^ n)%nat (stabilizeByListT (fun v => WF_Matrix v) Lt)).
  { apply stabilizeByListT_is_subspace. apply CM.totalspace_is_subspace. }
  destruct (CM.exists_dimension H25) as [dim [isdim dimbound]].
  assert (length Lt <= n)%nat by lia.
  pose (dimension_stabilizeByListT dim Lt H0 H1 H2 H3 H4 H5 H26 isdim) as E.
  rewrite H6 in E. replace (n - n)%nat with 0%nat in E by lia.
 rewrite Nat.pow_0_r in E. subst. auto. }

unfold CM.dimension in H25.
destruct H25 as [B [WFB basisB]].
pose (CM.subspace_is_basis_span basisB) as E.

assert (@CM.WF_GenMatrix (2^n)%nat (2^m)%nat 
            (fun r c : nat => if (r <? 2^n)%nat && (c <? 2^m)%nat 
                          then U (2 ^ m * r + c)%nat 0%nat else C0)).
  { unfold CM.WF_GenMatrix. intros. bdestruct_all; simpl; auto. }

assert (exists A : Matrix 1 (2^m)%nat, WF_Matrix A /\
           @Mmult (2^n)%nat 1%nat (2^m)%nat B A = 
             (fun r c : nat => if (r <? 2^n)%nat && (c <? 2^m)%nat 
                          then U (2 ^ m * r + c)%nat 0%nat else C0)).
{pose (CM.collect_columns_in_span H25 WFB) as E'.
  assert (forall i : nat,
      (i < 2 ^ m)%nat ->
      CM.span B
        (@CM.get_col (2^n)%nat (2^m)%nat 
           (fun r c : nat =>
            if (r <? 2 ^ n) && (c <? 2 ^ m) then U (2 ^ m * r + c)%nat 0%nat else C0)
           i)).
  { intros i H26.
    assert ((@CM.get_col (2^n)%nat (2^m)%nat 
       (fun r c : nat =>
        if (r <? 2 ^ n) && (c <? 2 ^ m) then U (2 ^ m * r + c)%nat 0%nat else C0) i) =
              (fun r c : nat => if (c =? 0)%nat then U (2 ^ m * r + i)%nat 0%nat else C0)).
    { unfold CM.get_col. prep_matrix_equality. bdestruct_all; simpl; auto; subst. 
      destruct WFUU. rewrite H29; auto; nia. }
    rewrite H27, <- E. apply H24. lia. }
  specialize (E' H26).
  destruct E' as [A [WFA BA]].
  exists A. auto. }
destruct H26 as [A [WFA BA]].
destruct WFUU.
assert (WF_Matrix (get_col U 0%nat)) by auto with wf_db.
rewrite H12 in H28.
pose (collect_kron1 B A (get_col U 0%nat) WFB WFA H28) as E'.
unfold get_col in E'. simpl in E'. specialize (E' BA).
replace (fun x y : nat => if (y =? 0)%nat then U x 0%nat else 0) with (get_col U 0%nat) in E' by (unfold get_col; simpl; auto).
assert (stabilizeByListT (fun v : Vector (2 ^ n) => WF_Matrix v) Lt B).
{ rewrite E. unfold CM.span. exists (I 1). split. apply CM.WF_I1. lma'. }
assert (v = ((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (get_col U 0%nat)).
{ rewrite AULVd.
  unfold adjoint, Mmult, Matrix.scale, get_col.
  prep_matrix_equality.
  apply big_sum_unique.
  exists 0%nat. repeat split; simpl; auto; try lia.
  bdestruct_all; subst; simpl. 
  - rewrite <- Cmult_assoc. setoid_rewrite Cmult_comm at 3. f_equal.
    apply big_sum_unique. exists 0%nat. rewrite H12. repeat split; try lca.
    + assert (1 < 2 ^ m)%nat. { apply Nat.pow_gt_1; try lia. }
      assert (1 < 2 ^ n)%nat. { apply Nat.pow_gt_1; try lia. }
      lia.
    + intros x' H30 H31. rewrite H22; try lca; lia.
  - destruct WFUV. rewrite H31; try lia. lca. }
rewrite E' in H30.
setoid_rewrite <- Mscale_kron_dist_r in H30.
assert (WF_Matrix (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (A ⊤))) by auto with wf_db.
specialize (H8 B WFB (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (A ⊤)) H31 H29).
contradiction.
Qed.


Lemma separability_proof_right :
  forall (n m : nat) (Lt : list (TType m)),
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> m <> 0%nat ->
    Lt <> [] -> Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt ->
    commutingListT Lt -> length Lt = m -> 
    (forall v : Vector (2 ^ (n + m))%nat,
      (exists w : Vector (2 ^ n)%nat, WF_Matrix w /\ (exists u : Vector (2 ^ m)%nat, WF_Matrix u /\
        vecSatisfiesP u (Cap (map TtoA Lt)) /\ v = w ⊗ u)) <->
        vecSatisfiesP v (Cap (map (uncurry gTensorA)
                                (combine 
                                   (map TtoA (repeat (defaultT_I n) (length Lt)))
                                   (map TtoA Lt))))).
Proof. intros n m Lt H0 H1 H2 H3 H4 H5 H6 v.
  split; intros.
  - destruct H7 as [w [WFw [u [WFu [vecSatisfiesPu vwu]]]]].
    rewrite vwu.
    simpl. split; auto with wf_db.
    clear - vecSatisfiesPu WFw WFu H3.
    induction Lt; auto.
    simpl in *. destruct vecSatisfiesPu. 
    rewrite Forall_cons_iff in *. destruct H1, H3.
    assert (H5 := conj H0 H2).
    specialize (IHLt H4 H5).
    constructor; auto.
    unfold uncurry. simpl.
    unfold translateA in *. simpl in *. rewrite Mplus_0_l in *.
    unfold vecSatisfies in *.
    destruct H1. split; auto with wf_db.
    unfold Eigenpair in *. simpl in *.
    rewrite Mscale_1_l in *.
    assert (H' : (let (c2, g7) := a in (C1 * c2, repeat gI n ++ g7)) =
              gTensorT (defaultT_I n) a) by auto.
    setoid_rewrite H'.
    rewrite translate_gTensorT.
    + rewrite translate_defaultT_I. setoid_rewrite kron_mixed_product'; auto.
      2-3: rewrite Nat.pow_add_r; auto.
      rewrite Mmult_1_l; auto. f_equal; auto.
    + unfold defaultT_I. simpl. rewrite repeat_length. auto.
    + destruct H3. auto.
  - assert (H8 : forall A B : Prop, ~ (A /\ B) <-> (A -> ~ B)).
    { intros A B. split; intros.
      - apply Classical_Prop.not_and_or in H8. destruct H8; auto.
      - apply Classical_Prop.or_not_and. destruct (Classical_Prop.classic A); auto. }
    assert (H9 : ((forall w : Vector (2 ^ n)%nat, WF_Matrix w ->  
                           (forall u : Vector (2 ^ m)%nat, WF_Matrix u ->
                                   vecSatisfiesP u (Cap (map TtoA Lt)) ->
                                          ~ v = w ⊗ u)) -> False) <->
                   (exists w : Vector (2 ^ n),
                       WF_Matrix w /\
                         (exists u : Vector (2 ^ m),
                             WF_Matrix u /\
                               vecSatisfiesP u (Cap (map TtoA Lt)) /\ 
                               v = w ⊗ u))).
    { split; intros. 
      - apply Classical_Prop.NNPP. intro.
        contradict H9.
        intros w H9 u H11 H12. 
        apply Classical_Pred_Type.not_ex_all_not with (n := w) in H10.
        rewrite H8 in H10. specialize (H10 H9).
         apply Classical_Pred_Type.not_ex_all_not with (n := u) in H10.
         rewrite H8 in H10. specialize (H10 H11).
         apply Classical_Prop.not_and_or in H10.
         destruct H10; auto.
      - destruct H9 as [w [WFw [u [WFu [vecSatisfiesPw vwu]]]]].
        apply (H10 w WFw u WFu vecSatisfiesPw vwu). }
    rewrite <- H9. clear H8 H9.
    intros H8.
    assert (WF_Matrix v).
    { destruct H7; auto. }
    destruct (SVD v H9) as [U [L [V [WFUU [WFUV [WFDL [WFNL AULVd]]]]]]].
    bdestruct (n =? 0)%nat.
    + subst.
      assert (@eq (list (AType (0 + m))) (map (uncurry gTensorA)
               (combine (map TtoA (repeat (defaultT_I 0) (length Lt)))
                  (map TtoA Lt)))
                (map TtoA Lt)).
      { unfold defaultT_I. simpl. rewrite map_repeat.
        apply nth_ext with (d := (uncurry (@gTensorA 0%nat m)) (([(C1,[])]), ([defaultT_I m]))) (d' := defaultT_I (0 + m)).
        * rewrite ! map_length. rewrite combine_length. rewrite repeat_length, map_length.
          minmax_breakdown. auto.
        * intros n0 H10. rewrite ! map_nth.
          rewrite combine_nth.
          2: rewrite map_length, repeat_length; auto.
          rewrite map_nth with (d := defaultT_I m).
          rewrite nth_repeat.
          unfold uncurry.
          simpl. unfold TtoA.
          destruct (nth n0 Lt (defaultT_I m)).
           do 2 f_equal. lca. }
      rewrite H10 in H7. 
      assert (0 + m = m)%nat by lia.
      rewrite H11 in *.
      replace (2 ^ m)%nat with (2 ^ (0 + m))%nat in * by (rewrite Nat.add_0_l; auto).
      specialize (H8 (I 1) WF_I1 (U × L × (V) †) H9 H7).
      rewrite kron_1_l in H8; auto.
    + assert (v = (V 0%nat 0%nat)^* .* (U × L)).
      { rewrite AULVd.
        unfold Mmult, Matrix.scale, adjoint. simpl.
        prep_matrix_equality. destruct WFUV.
        bdestruct (y =? 0)%nat.
        - subst. lca.
        - rewrite H11 at 1; auto; try lia. rewrite Cconj_0, Cmult_0_r, Cplus_0_l.
          assert (Σ (fun y0 : nat => U x y0 * L y0 y) (2 ^ (n + m)) = C0).
          { destruct WFDL.
            rewrite big_sum_0_bounded; auto; intros.
            rewrite H14; auto; try lia; try lca. }
          rewrite H14. lca. }
      assert ((2 ^ (n + m)) = (2 ^ n) * (2 ^ m))%nat by apply Nat.pow_add_r.

      simpl in H7. destruct H7.

      rewrite matrix_span_as_get_col_sum in H11.
      2: destruct WFDL; auto.

      assert ( fold_right Mplus Zero
                 (map (fun i : nat => L i 0%nat .* get_col U i)
                    (List.seq 0 (2 ^ (n + m)))) = 
                 fold_right Mplus Zero
                         (map (fun M => M)   
                   (map (fun i : nat => L i 0%nat .* get_col U i)
                      (List.seq 0 (2 ^ (n + m))))))
      by (rewrite map_map; auto).
      rewrite H14 in H11.
      rewrite <- fold_right_Mplus_Zero_Mscale_distr with (c := (V 0%nat 0%nat) ^* ) in H11.
      rewrite map_map in H11.
      assert ((map (fun i : nat => (V 0%nat 0%nat) ^* .* (L i 0%nat .* get_col U i))
             (List.seq 0 (2 ^ (n + m)))) =
                (map (fun i : nat => 
                        fold_right Mplus Zero
                          (map
                             (fun j : nat =>
                                (V 0%nat 0%nat) ^* * (L i 0%nat) * (U j i) .* 
                                                               (@e_i (2 ^ n)%nat (j / (2 ^ m)%nat) ⊗ @e_i (2 ^ m)%nat (j mod (2 ^ m)%nat)))
                          (List.seq 0 (2 ^ (n + m)))))
                  (List.seq 0 (2 ^ (n + m))))).
      { apply map_ext_Forall. rewrite Forall_forall. intros x H15.  rewrite in_seq in H15.
        rewrite (vector_as_e_i_sum (get_col U x)) at 1.
        assert ((map (fun i : nat => get_col U x i 0%nat .* @ e_i (2 ^ (n + m))  i)
              (List.seq 0 (2 ^ (n + m)))) = 
                  (map (fun M => M) (map (fun i : nat => get_col U x i 0%nat .* e_i i)
              (List.seq 0 (2 ^ (n + m)))))) by (rewrite map_map; auto).
        rewrite H16.
        rewrite Mscale_assoc.
        rewrite <- fold_right_Mplus_Zero_Mscale_distr.
        rewrite ! map_map.
        f_equal.
        apply map_ext_Forall. rewrite Forall_forall. intros x0 H17. rewrite in_seq in H17.
        rewrite ! H12.
        rewrite e_i_kron_inv; auto; try lia.
        rewrite ! Mscale_assoc. f_equal.
        destruct WFUU. auto with wf_db. }
      rewrite H15 in H11.
      rewrite fold_right_Mplus_Zero_double_swap 
        with (F := (fun i j : nat =>
                     (V 0%nat 0%nat) ^* * L i 0%nat * U j i .* (e_i (j / 2 ^ m) ⊗ e_i (j mod 2 ^ m))))
        in H11.
      assert ((fun j : nat =>
              fold_right Mplus Zero
                (map
                   (fun i : nat =>
                    (V 0%nat 0%nat) ^* * L i 0%nat * U j i
                    .* (@e_i (2 ^ n)%nat (j / 2 ^ m) ⊗ @e_i (2 ^ m)%nat (j mod 2 ^ m)))
                   (List.seq 0 (2 ^ (n + m))))) =
                (fun j : nat =>
              (fold_right Cplus C0
                (map
                   (fun i : nat =>
                    (V 0%nat 0%nat) ^* * L i 0%nat * U j i)
                   (List.seq 0 (2 ^ (n + m))))) .* (e_i (j / 2 ^ m) ⊗ e_i (j mod 2 ^ m)))).
      { apply functional_extensionality. intros x.
        rewrite fold_right_Mplus_Zero_collect_scalar. auto. }
      rewrite H16 in H11.
      clear H14 H15 H16.

      assert (forall k : nat, (k < length Lt)%nat -> (translate (gTensorT (defaultT_I n) (nth k Lt (defaultT_I m)))) × v = v).
      { rewrite Forall_map in H13.
        rewrite Forall_forall in H13.
        intros k H14. specialize (H13 (nth k (combine 
             (map TtoA (repeat (defaultT_I n) (length Lt)))
             (map TtoA Lt)) ([defaultT_I n],[defaultT_I m] ))).  
        assert (In
          (nth k
             (combine 
                (map TtoA
                   (repeat (defaultT_I n) (length Lt)))
                (map TtoA Lt))
             ([defaultT_I n], [defaultT_I m]))
          (combine (map TtoA (repeat (defaultT_I n) (length Lt)))
               (map TtoA Lt))).
        { apply nth_In. rewrite combine_length, ! map_length, repeat_length. 
          minmax_breakdown. auto. }
        specialize (H13 H15). clear H15.
        rewrite combine_nth in H13.
        rewrite map_nth with (d := defaultT_I n) in H13.
        rewrite map_nth with (d := defaultT_I m) in H13.
        rewrite nth_repeat in H13.
        unfold uncurry. simpl in H13. 
        2 : rewrite ! map_length, repeat_length; auto.
        unfold translateA in H13. simpl in H13. rewrite Mplus_0_l in H13.
        unfold vecSatisfies in H13. destruct H13. unfold Eigenpair in H15. simpl in H15.
        rewrite Mscale_1_l in H15. auto. }
      
      setoid_rewrite translate_gTensorT in H14.
      2: { unfold defaultT_I. simpl. rewrite repeat_length. auto. }
      2: { bdestruct (k <? length Lt)%nat.
           rewrite Forall_nth in H3. specialize (H3 k (defaultT_I m) H15).
           destruct H3. auto. rewrite nth_overflow; try lia. unfold defaultT_I. simpl. 
           rewrite repeat_length. auto. }

      rewrite translate_defaultT_I in H14.
      rewrite H11 in H14. rewrite ! H12 in H14.
      setoid_rewrite <- fold_right_Mplus_Zero_map_Mmult_distr in H14.
      setoid_rewrite map_map in H14.

      assert (forall k : nat, (fun x : nat =>
              I (2 ^ n) ⊗ translate (nth k Lt (defaultT_I m))
              × (fold_right Cplus 0
                   (map (fun i : nat => (V 0%nat 0%nat) ^* * L i 0%nat * U x i)
                      (List.seq 0 (2 ^ n * 2 ^ m)))
                 .* (e_i (x / 2 ^ m) ⊗ e_i (x mod 2 ^ m)))) =
                         (fun x : nat =>
              fold_right Cplus 0
    (map (fun i : nat => (V 0%nat 0%nat) ^* * L i 0%nat * U x i)
       (List.seq 0 (2 ^ n * 2 ^ m)))
  .* (e_i (x / 2 ^ m)
      ⊗ (translate (nth k Lt (defaultT_I m)) × e_i (x mod 2 ^ m))))).
      { intro. apply functional_extensionality. intro. rewrite Mscale_mult_dist_r. 
        rewrite kron_mixed_product. rewrite Mmult_1_l; auto with wf_db. }
      setoid_rewrite H15 in H14. clear H15.
      setoid_rewrite fold_right_Mplus_Zero_big_sum in H14.
      
      assert (forall k : nat, (fun i : nat =>
           fold_right Cplus 0
             (map (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0)
                (List.seq 0 (2 ^ n * 2 ^ m)))
           .* (@e_i (2 ^ n)%nat (i / 2 ^ m)
               ⊗ (translate (nth k Lt (defaultT_I m)) × @e_i (2 ^ m)%nat (i mod 2 ^ m)))) =
                (fun i : nat =>
           (big_sum (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0) (2 ^ n * 2 ^ m))
           .* (e_i (i / 2 ^ m)
               ⊗ (translate (nth k Lt (defaultT_I m)) × e_i (i mod 2 ^ m))))).
      { intro. apply functional_extensionality. intro.
        rewrite fold_right_Cplus_C0_big_sum. rewrite Nat.mul_1_l. auto. }
      rewrite ! Nat.mul_1_l in H15. setoid_rewrite H15 in H14. clear H15.

      assert ((fun i : nat =>
           fold_right Cplus 0
             (map (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0)
                (List.seq 0 (2 ^ n * 2 ^ m)))
           .* (@e_i (2 ^ n)%nat (i / 2 ^ m) ⊗ @e_i (2 ^ m)%nat (i mod 2 ^ m))) = 
                (fun i : nat =>
           (big_sum (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U i i0) (2 ^ n * 2 ^ m))
             .* (e_i (i / 2 ^ m) ⊗ e_i (i mod 2 ^ m)))).
      { apply functional_extensionality. intro.
        rewrite fold_right_Cplus_C0_big_sum. auto. }
      setoid_rewrite H15 in H14. clear H15.
      
     setoid_rewrite <- fold_right_Mplus_Zero_big_sum in H14.
     setoid_rewrite fold_right_Mplus_Zero_scaled_vector_sum in H14.

     2: { rewrite Forall_forall. intros x H15. apply WF_kron; auto with wf_db.
          apply WF_mult; auto with wf_db. bdestruct (k <? length Lt)%nat.
          apply WF_translate. rewrite Forall_nth in H3. apply H3; auto.
          rewrite nth_overflow; auto. rewrite translate_defaultT_I. auto with wf_db. }
     
     2: { rewrite Forall_forall. intros x H15. apply WF_kron; auto with wf_db. }

     assert (forall k : nat, (k < length Lt)%nat -> @Mmult (2 ^ n * 2 ^ m)%nat (2 ^ n * 2 ^ m)%nat 1%nat
         (fun r c : nat =>
         (@e_i (2^n)%nat (c / 2 ^ m) ⊗ ((translate (nth k Lt (defaultT_I m)) .+ (- C1)%C .* (I (2^m)%nat)) × @e_i (2^m)%nat (c mod 2 ^ m)))
           r 0%nat) 
         (fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0) = Zero).
     { intros k H15. specialize (H14 k H15).
       prep_matrix_equality. 
       apply f_equal_inv with (x := x) in H14.
       apply f_equal_inv with (x := y) in H14.
       unfold Mmult at 1 in H14. unfold Mmult at 2 in H14.
       unfold Mmult at 1. unfold Zero.
       apply Cplus_inv_r with (c :=
          (@Mmult (2 ^ n * 2 ^ m)%nat (2 ^ n * 2 ^ m)%nat 1%nat
            (fun r c : nat => (@e_i (2^n)%nat (c / 2 ^ m) ⊗ @e_i (2^m)%nat (c mod 2 ^ m)) r 0%nat)
              (fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0)) x y).
       unfold Mmult at 2. unfold Mmult at 2. rewrite Cplus_0_l.
       rewrite <- H14 at 2.
       rewrite <- @big_sum_plus with (H0 := C_is_group).
       apply big_sum_eq_bounded. intros x0 H16. 
       rewrite <- ! Cmult_plus_distr_r. f_equal. unfold Mplus, Matrix.scale, Mmult.
       unfold kron. simpl. rewrite <- ! Cmult_plus_distr_l. f_equal.
       unfold I. bdestruct_all.
       - replace (2 ^ m)%nat with ((x mod 2 ^ m) + 1 + ((2 ^ m) - (Datatypes.S (x mod 2 ^ m))))%nat by lia.
         rewrite ! big_sum_sum; simpl. rewrite ! Cplus_0_l.
         rewrite ! andb_true_r. rewrite ! Nat.add_0_r. 
         replace (x mod 2 ^ m + 1 + (2 ^ m - s (x mod 2 ^ m)))%nat with (2 ^ m)%nat by lia.
         bdestruct_all.
         rewrite Cmult_1_r. rewrite Cmult_plus_distr_r.
         rewrite <- ! Cplus_assoc. setoid_rewrite Cplus_comm at 5.

         assert (Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m) y0 +
      - C1 * (if (x mod 2 ^ m =? y0)%nat && true then C1 else 0)) *
     @e_i (2 ^ m)%nat (x0 mod 2 ^ m) y0 0%nat) (x mod 2 ^ m) +
  (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m) (x mod 2 ^ m) *
   @e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
   (- C1 * @e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
    (@e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
     Σ
       (fun x1 : nat =>
        (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m)
           (x mod 2 ^ m + 1 + x1)%nat +
         - C1 *
         (if (x mod 2 ^ m =? x mod 2 ^ m + 1 + x1)%nat && true then C1 else 0)) *
        @e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m + 1 + x1)%nat 0%nat)
       (2 ^ m - s (x mod 2 ^ m))))) = 
Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m) y0 +
      - C1 * (if (x mod 2 ^ m =? y0)%nat && true then C1 else 0)) *
     e_i (x0 mod 2 ^ m) y0 0%nat) (x mod 2 ^ m) +
  (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m) (x mod 2 ^ m) *
   e_i (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
   (- C1 * e_i (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
    (e_i (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat)) +
     Σ
       (fun x1 : nat =>
        (translate (nth k Lt (defaultT_I m)) (x mod 2 ^ m)
           (x mod 2 ^ m + 1 + x1)%nat +
         - C1 *
         (if (x mod 2 ^ m =? x mod 2 ^ m + 1 + x1)%nat && true then C1 else 0)) *
        e_i (x0 mod 2 ^ m) (x mod 2 ^ m + 1 + x1)%nat 0%nat)
       (2 ^ m - s (x mod 2 ^ m)))) by (rewrite ! Cplus_assoc; auto). 
         rewrite H19. clear H19.
         assert (- C1 * @e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat +
    @e_i (2 ^ m)%nat (x0 mod 2 ^ m) (x mod 2 ^ m) 0%nat = C0) by lca.
         rewrite H19. clear H19. rewrite Cplus_0_r.
         f_equal.
         + apply big_sum_eq_bounded. intros x1 H19. 
           bdestruct_all; simpl; auto; try lia; try lca. 
         + f_equal. apply big_sum_eq_bounded. intros x1 H19. 
           bdestruct_all; simpl; auto; try lia; try lca.
       - assert (WF_Matrix (@e_i (2^m)%nat (x0 mod 2 ^ m))) by auto with wf_db.
         rewrite H18; try lia. rewrite Cplus_0_r.
         apply big_sum_eq_bounded. intros x1 H19.
         bdestruct_all. simpl. rewrite Cmult_0_r, Cplus_0_r. auto.
       - apply C_is_comm_group. }
     
     assert (forall r : nat, Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0) (2 ^ n * 2 ^ m) =
                        (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U r 0%nat).
     { intros r. destruct WFDL.
       rewrite big_sum_unique with (k := (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U r 0%nat); auto.
       exists 0%nat. repeat split; auto. rewrite <- H12.
       assert (0 < 2 ^ (n + m))%nat.
       { assert (0 ^ (n + m) = 0)%nat. { apply Nat.pow_0_l; lia. }
         rewrite <- H18 at 1.
         apply Nat.pow_lt_mono_l; lia. }
       auto.
       intros x' H18 H19.
       rewrite H17; try lia; lca. }

     assert ((fun r c : nat =>
           if (c =? 0)%nat
           then
            Σ (fun i0 : nat => (V 0%nat 0%nat) ^* * L i0 0%nat * U r i0)
              (2 ^ n * 2 ^ m)
           else 0) =
               (fun r c : nat =>
           if (c =? 0)%nat
           then
            (V 0%nat 0%nat) ^* * L 0%nat 0%nat * U ((2^m * (r / 2^m) + r mod 2^m)%nat) 0%nat
           else 0)).
     { prep_matrix_equality. bdestruct_all; try rewrite H16; auto.
       rewrite <- Nat.div_mod_eq. auto. }
     rewrite H17 in H15.

     assert ((2 ^ n * 2 ^ m) = (2 ^ m * 2 ^ n))%nat by (apply Nat.mul_comm).

     unfold Mmult in H15 at 1.

assert (forall k : nat,
(fun x z : nat =>
         Σ
           (fun y : nat =>
            (@e_i (2^n)%nat (y / 2 ^ m) ⊗ ((translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) × @e_i (2^m)%nat (y mod 2 ^ m))) x 0%nat *
            (if (z =? 0)%nat
             then
              (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
              U (2 ^ m * (y / 2 ^ m) + y mod 2 ^ m)%nat 0%nat
             else 0)) (2 ^ n * 2 ^ m)) =


  (fun x y : nat =>
         if (y =? 0)%nat then
(@big_sum (Matrix (2 ^ n * 2 ^ m) 1%nat) (M_is_monoid (2 ^ n * 2 ^ m) 1%nat)


(fun x0 : nat =>
     (@kron (2^n)%nat 1%nat (2^m)%nat 1%nat 
        (@e_i (2^n)%nat x0)
(fun r c : nat =>

       (Σ
       (fun y0 : nat =>
        
((V 0%nat 0%nat) ^* * L 0%nat 0%nat * U (2 ^ m * x0 + y0)%nat 0%nat) *
(((translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) × @e_i (2^m)%nat y0) r c)

) (2 ^ m)))
       )
)

(2 ^ n)) x 0%nat

else C0

)).
{ intros k. prep_matrix_equality. bdestruct_all; subst.
  rewrite Msum_Csum.
     rewrite ! H18.
     rewrite <- big_sum_double_sum
with 
(f := (fun i j : nat =>
     ( e_i (i)
      ⊗ ((translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) × e_i (j))) x 0%nat *
     ( (*if (y =? 0)%nat
      then *)
       (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
       U (2 ^ m * (i) + j)%nat 0%nat
      (* else 0 *)))).
     unfold kron. simpl.
     apply big_sum_eq_bounded. intros x0 H19.
     rewrite @big_sum_mult_l with (H2 := C_is_ring).
     apply big_sum_eq_bounded. intros x1 H20. simpl. 
     lca. 
     rewrite big_sum_0_bounded; auto; intros; lca. }
setoid_rewrite H19 in H15. clear H19.

assert (@Zero (2 ^ n * 2 ^ m)%nat 1%nat =
          (fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum (Vector (2^n * 2^m)%nat) (M_is_monoid (2^n * 2^m)%nat 1%nat)
            (fun x0 : nat =>
             (@e_i (2^n)%nat x0) ⊗ @Zero (2^m)%nat 1%nat) (2 ^ n) x 0%nat
         else 0)).
{ prep_matrix_equality. unfold Zero.
  bdestruct_all; simpl; subst.
  rewrite big_sum_0_bounded; auto; intros.
  rewrite kron_0_r. lma'. auto. }
rewrite H19 in H15.

assert (forall k : nat, (k < length Lt)%nat -> 
                 forall i, (0 <= i < 2^n)%nat ->
             (fun r c : nat =>
                Σ
                  (fun y0 : nat =>
                   (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
                   U (2 ^ m * i + y0)%nat 0%nat *
                   ((translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m))
                    × e_i y0) r c) (2 ^ m)) =
                @Zero (2^m)%nat 1%nat).
{ intros k H20 i H21.
  apply @delete_left_kron_from_vector
          with (j := (2^n)%nat) (k := (2^n)%nat)
          (A_i := (fun x0 : nat =>
              (fun r c : nat =>
                Σ
                  (fun y0 : nat =>
                   (V 0%nat 0%nat) ^* * L 0%nat 0%nat *
                   U (2 ^ m * x0 + y0)%nat 0%nat *
                   ((translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m))
                    × e_i y0) r c) (2 ^ m))))
               (B_i := (fun x0 : nat => @Zero (2^m)%nat 1%nat)); auto; try lia.
  - intro. rewrite Nat.pow_eq_0_iff in H22. destruct H22. lia.
  - rewrite Forall_forall. intros x H22. rewrite in_seq in H22.
    unfold WF_Matrix. intros x0 y H23.
    destruct H23.
    + rewrite big_sum_0_bounded; auto; intros. unfold Mmult.
      rewrite big_sum_0_bounded; intros; try lca.
      assert (WF_Matrix (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m))).
      { apply WF_plus; auto with wf_db. apply WF_translate.
        rewrite Forall_nth in H3. apply H3; lia. }
      rewrite H26; try lia; lca.
    + rewrite big_sum_0_bounded; auto; intros. unfold Mmult.
      pose (@WF_e_i (2^m)%nat x1) as WFei.
      rewrite big_sum_0_bounded; intros; try lca.
      rewrite WFei; try lia; lca.
  - rewrite Forall_forall. intros x H22. auto with wf_db. }

unfold Mmult in H20.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        @eq (Vector (2^m)%nat)
        (fun r c : nat =>
         Σ
           (fun y0 : nat =>
              ((V 0%nat 0%nat) ^* * L 0%nat 0%nat * U (2 ^ m * i + y0)%nat 0%nat) *
            Σ
              (fun y : nat =>
               (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) r y *
               @e_i (2^m)%nat y0 y c) (2 ^ m))
           (2 ^ m))
        (@Matrix.scale (2^m)%nat 1%nat
        ((V 0%nat 0%nat) ^* * L 0%nat 0%nat)
        (fun r c : nat =>
         Σ
           (fun y0 : nat =>
              (U (2 ^ m * i + y0)%nat 0%nat) *
            Σ
              (fun y : nat =>
               (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) r y *
               @e_i (2^m)%nat y0 y c) (2 ^ m))
           (2 ^ m)))).
{ intros k H21 i H22.
  prep_matrix_equality. unfold Matrix.scale.
  rewrite @big_sum_mult_l with (H2 := C_is_ring).
  apply big_sum_eq_bounded; intros. simpl. lca. }

  assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        (V 0%nat 0%nat) ^* * L 0%nat 0%nat
        .* (fun r c : nat =>
            Σ
              (fun y0 : nat =>
                 (U (2 ^ m * i + y0)%nat 0%nat) *
               Σ
                 (fun y : nat =>
                  (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) r y *
                  @e_i (2^m)%nat y0 y c) (2 ^ m)) 
              (2 ^ m)) = @Zero (2^m)%nat 1%nat).
{ intros k H22 i H23. specialize (H20 k H22 i H23).  specialize (H21 k H22 i H23).
  rewrite <- H21. rewrite H20. auto. }
clear H20 H21.

assert (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (@Zero (2^m)%nat 1%nat) = (@Zero (2^m)%nat 1%nat)).
{ rewrite Mscale_0_r. auto. }
setoid_rewrite <- H20 in H22.

assert ((V 0%nat 0%nat) <> C0). 
{ intro. assert (V = Zero).
  { prep_matrix_equality. unfold Zero. destruct WFUV.
    bdestruct (x =? 0)%nat; bdestruct (y =? 0)%nat; subst; auto; rewrite H23; auto; try lia. }
  destruct WFUV. rewrite H23 in H25. rewrite Mmult_0_r in H25.
  contradict_matrix_equalities. }
assert ((V 0%nat 0%nat) ^* <> C0).
{ apply Cconj_neq_0; auto. }
assert (L 0%nat 0%nat <> C0).
{ intro. assert (L = Zero).
  { prep_matrix_equality. unfold Zero. destruct WFDL.
    bdestruct (x =? 0)%nat; bdestruct (y =? 0)%nat; subst; auto.
    rewrite H25; auto; lia. }
  rewrite H25 in AULVd. rewrite Mmult_0_r, Mmult_0_l in AULVd.
  subst.
  assert (WF_Matrix (@Zero (2^n)%nat 1%nat)) as zero2n by auto with wf_db.
  assert (WF_Matrix (@Zero (2^m)%nat 1%nat)) as zero2m by auto with wf_db.
  assert (vecSatisfiesP (@Zero (2^m)%nat 1%nat) (Cap (map TtoA Lt))).
  { unfold vecSatisfiesP. split; auto with wf_db.
    unfold vecSatisfies. unfold Eigenpair. simpl.
    rewrite Forall_forall. intros x H25.
    split; auto with wf_db. rewrite Mmult_0_r, Mscale_0_r. auto. }
  specialize (H8 (@Zero (2^n)%nat 1%nat) zero2n (@Zero (2^m)%nat 1%nat) zero2m H25).
  rewrite kron_0_l in H8. contradiction. } 
remember H24 as Lnonzero. clear HeqLnonzero.
assert ((V 0%nat 0%nat) ^* * L 0%nat 0%nat <> C0).
{ intro. apply Cmult_integral in H25. destruct H25; contradiction. }
clear H20 H21 H23 H24.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        (fun r c : nat =>
            Σ
              (fun y0 : nat =>
                 (U (2 ^ m * i + y0)%nat 0%nat) *
               Σ
                 (fun y : nat =>
                  (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) r y *
                  @e_i (2^m)%nat y0 y c) (2 ^ m)) 
              (2 ^ m)) = (@Zero (2^m)%nat 1%nat)).
{ intros. specialize (H22 k H20 i H21). apply Mscale_cancel in H22; auto. }

clear H22 H25.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        (fun r c : nat =>
           (if (c =? 0)%nat then
            Σ
              (fun y : nat => 
                 (U (2 ^ m * i + y)%nat 0%nat) *
               (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) r y) 
           (2 ^ m) else C0)) = @Zero (2^m)%nat 1%nat).
{ intros k H21 i H22.
  specialize (H20 k H21 i H22).
  rewrite <- H20.
  prep_matrix_equality. bdestruct_all; subst.
  - apply big_sum_eq_bounded; intros. f_equal.
    unfold e_i. simpl. symmetry. apply big_sum_unique. exists x0.
    repeat split; auto. bdestruct (x0 =? x0)%nat; bdestruct (x0 <? 2^m)%nat; try lia. simpl. lca.
    intros x' H24 H25. bdestruct (x' =? x0)%nat; bdestruct (x' <? 2^m)%nat; try lia. simpl. lca.
  - rewrite big_sum_0_bounded; auto; intros.
    assert (Σ
    (fun y0 : nat =>
     (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m)) x y0 * @e_i (2^m)%nat x0 y0 y)
    (2 ^ m) = C0).
    { rewrite big_sum_0_bounded; auto; intros.
      rewrite (@WF_e_i (2^m)%nat x0); try lca; try lia. }
    rewrite H25. lca. }

clear H20.

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        @Mmult (2^m)%nat (2^m)%nat 1%nat
          (translate (nth k Lt (defaultT_I m)) .+ - C1 .* I (2 ^ m))
        (fun r c : nat =>
         if (c =? 0)%nat && (r <? 2 ^ m)%nat
         then U (2 ^ m * i + r)%nat 0%nat
         else 0) = @Zero (2^m)%nat 1%nat).
{ intros k H20 i H22.
  unfold Mmult. specialize (H21 k H20 i H22).
  rewrite <- H21. prep_matrix_equality.
  bdestruct_all; subst; auto.
  apply big_sum_eq_bounded; intros; simpl; bdestruct_all; auto; lca.
  rewrite big_sum_0_bounded; intros; bdestruct_all; auto; lca. }

assert (forall i j : nat, (i <> 0)%nat \/ (j <> 0)%nat -> L i j = C0).
{ intros i j H22. destruct WFDL. destruct H22.
  - bdestruct (j =? 0)%nat; subst.
    + apply H24. lia.
    + rewrite H23; auto; lia.
  - rewrite H23; auto; lia. }

assert (forall k : nat,
        (k < length Lt)%nat ->
        forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
       @eq (Vector (2^m)%nat)
        (@Mmult (2^m)%nat (2^m)%nat 1%nat (translate (nth k Lt (defaultT_I m))) 
              (fun r c : nat => if (c =? 0)%nat && (r <? 2 ^ m)%nat then U (2 ^ m * i + r)%nat 0%nat else 0))
        (fun r c : nat => if (c =? 0)%nat && (r <? 2 ^ m)%nat then U (2 ^ m * i + r)%nat 0%nat else 0)).
{ intros k H23 i H24.
  specialize (H20 k H23 i H24).
  setoid_rewrite <- Mplus_0_r at 5.
  rewrite <- H20.
  setoid_rewrite <- Mmult_1_l at 6.
  rewrite <- Mmult_plus_distr_r.
  f_equal. setoid_rewrite Mplus_comm at 2.
  rewrite <- Mplus_assoc.
  setoid_rewrite <- Mplus_0_l at 1. f_equal.
  lma'.
  unfold WF_Matrix. intros x y H25.
  bdestruct_all; simpl; subst; auto. }

assert (forall i : nat,
        (0 <= i < 2 ^ n)%nat ->
        @vecSatisfiesP m
          (fun r c : nat => if (c =? 0)%nat && (r <? 2 ^ m)%nat then U (2 ^ m * i + r)%nat 0%nat else 0)
          (Cap (map TtoA Lt))).
{ intros i H24. unfold vecSatisfiesP. split.
  - unfold WF_Matrix. intros.
    bdestruct_all; simpl; subst; auto.
  - rewrite Forall_forall. intros x H25.
    apply In_nth with (d := defaultT_I m) in H25.
    destruct H25 as [k [kbound kth]]. subst.
    rewrite map_nth with (d := defaultT_I m).
    simpl. unfold translateA. simpl. rewrite Mplus_0_l.
    unfold vecSatisfies.
    split. 
    + unfold WF_Matrix. intros.
      bdestruct_all; simpl; subst; auto.
    + unfold Eigenpair. simpl. rewrite Mscale_1_l.
      apply H23; auto. rewrite map_length in kbound; auto. }

setoid_rewrite vecSatisfiesP_iff_stabilizeByListT in H24.
setoid_rewrite vecSatisfiesP_iff_stabilizeByListT in H8.

assert (@CM.dimension (2^m)%nat (stabilizeByListT (fun v => WF_Matrix v) Lt) 1%nat).
{ assert (@CM.subspace (2 ^ m)%nat (stabilizeByListT (fun v => WF_Matrix v) Lt)).
  { apply stabilizeByListT_is_subspace. apply CM.totalspace_is_subspace. }
  destruct (CM.exists_dimension H25) as [dim [isdim dimbound]].
  assert (length Lt <= m)%nat by lia.
  pose (dimension_stabilizeByListT dim Lt H0 H1 H2 H3 H4 H5 H26 isdim) as E.
  rewrite H6 in E. replace (m - m)%nat with 0%nat in E by lia.
 rewrite Nat.pow_0_r in E. subst. auto. }

unfold CM.dimension in H25.
destruct H25 as [B [WFB basisB]].
pose (CM.subspace_is_basis_span basisB) as E.

assert (@CM.WF_GenMatrix (2^m)%nat (2^n)%nat 
            (fun r c : nat => if (r <? 2^m)%nat && (c <? 2^n)%nat 
                          then U (2 ^ m * c + r)%nat 0%nat else C0)).
  { unfold CM.WF_GenMatrix. intros. bdestruct_all; simpl; auto. }

assert (exists A : Matrix 1 (2^n)%nat, WF_Matrix A /\
           @Mmult (2^m)%nat 1%nat (2^n)%nat B A = 
             (fun r c : nat => if (r <? 2^m)%nat && (c <? 2^n)%nat 
                          then U (2 ^ m * c + r)%nat 0%nat else C0)).
{pose (CM.collect_columns_in_span H25 WFB) as E'.
  assert (forall i : nat,
      (i < 2 ^ n)%nat ->
      CM.span B
        (@CM.get_col (2^m)%nat (2^n)%nat 
           (fun r c : nat =>
            if (r <? 2 ^ m) && (c <? 2 ^ n) then U (2 ^ m * c + r)%nat 0%nat else C0)
           i)).
  { intros i H26.
    assert ((@CM.get_col (2^m)%nat (2^n)%nat 
       (fun r c : nat =>
        if (r <? 2 ^ m) && (c <? 2 ^ n) then U (2 ^ m * c + r)%nat 0%nat else C0) i) =
              (fun r c : nat => if (c =? 0)%nat && (r <? 2 ^ m) then U (2 ^ m * i + r)%nat 0%nat else C0)).
    { unfold CM.get_col. prep_matrix_equality. bdestruct_all; simpl; auto; subst. }
    rewrite H27, <- E. apply H24. lia. }
  specialize (E' H26).
  destruct E' as [A [WFA BA]].
  exists A. auto. }
destruct H26 as [A [WFA BA]].
destruct WFUU.
assert (WF_Matrix (get_col U 0%nat)) by auto with wf_db.
rewrite H12 in H28.
pose (collect_kron2 B A (get_col U 0%nat) WFB WFA H28) as E'.
unfold get_col in E'. simpl in E'. specialize (E' BA).
replace (fun x y : nat => if (y =? 0)%nat then U x 0%nat else 0) with (get_col U 0%nat) in E' by (unfold get_col; simpl; auto).
assert (stabilizeByListT (fun v : Vector (2 ^ m) => WF_Matrix v) Lt B).
{ rewrite E. unfold CM.span. exists (I 1). split. apply CM.WF_I1. lma'. }
assert (v = ((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (get_col U 0%nat)).
{ rewrite AULVd.
  unfold adjoint, Mmult, Matrix.scale, get_col.
  prep_matrix_equality.
  apply big_sum_unique.
  exists 0%nat. repeat split; simpl; auto; try lia.
  bdestruct_all; subst; simpl. 
  - rewrite <- Cmult_assoc. setoid_rewrite Cmult_comm at 3. f_equal.
    apply big_sum_unique. exists 0%nat. rewrite H12. repeat split; try lca.
    + assert (1 < 2 ^ m)%nat. { apply Nat.pow_gt_1; try lia. }
      assert (1 < 2 ^ n)%nat. { apply Nat.pow_gt_1; try lia. }
      lia.
    + intros x' H30 H31. rewrite H22; try lca; lia.
  - destruct WFUV. rewrite H31; try lia. lca. }
rewrite E' in H30.
setoid_rewrite <- Mscale_kron_dist_r in H30.
assert (WF_Matrix (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (A ⊤))) by auto with wf_db.
specialize (H8 (((V 0%nat 0%nat) ^* * L 0%nat 0%nat) .* (A ⊤)) H31 B WFB H29).
rewrite Mscale_kron_dist_r in H30. rewrite <- Mscale_kron_dist_l in H30.
contradiction.
Qed.


Lemma separability_proof2 :
  forall (n m : nat) (Lt1 : list (TType n)) (Lt2 : list (TType m)),
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt1)) -> n <> 0%nat ->
    Lt1 <> [] -> Forall proper_length_TType Lt1 -> Forall coef_plus_minus_1 Lt1 ->
    commutingListT Lt1 -> length Lt1 = n -> 
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt2)) -> m <> 0%nat ->
    Lt2 <> [] -> Forall proper_length_TType Lt2 -> Forall coef_plus_minus_1 Lt2 ->
    commutingListT Lt2 -> length Lt2 = m -> 
    (forall v : Vector (2 ^ (n + m))%nat,
      (exists w : Vector (2 ^ n)%nat, WF_Matrix w /\ (exists u : Vector (2 ^ m)%nat, WF_Matrix u /\
        vecSatisfiesP w (Cap (map TtoA Lt1)) /\ vecSatisfiesP u (Cap (map TtoA Lt2)) 
                                                                      /\ v = w ⊗ u)) <->
        vecSatisfiesP v (Cap ((map (uncurry gTensorA)
                                (combine 
                                   (map TtoA Lt1) 
                                   (map TtoA (repeat (defaultT_I m) (length Lt1))))) ++ 
                           (map (uncurry gTensorA)
                              (combine 
                                 (map TtoA (repeat (defaultT_I n) (length Lt2)))
                                 (map TtoA Lt2)))))).
Proof. intros n m Lt1 Lt2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 v.
  pose (separability_proof_left n m Lt1 H0 H1 H2 H3 H4 H5 H6 v) as E.
  pose (separability_proof_right n m Lt2 H7 H8 H9 H10 H11 H12 H13 v) as E'.
  simpl in *. rewrite Forall_app. 
  split; intros.
  - destruct H14 as [w [WFw [u [WFu [[WFw' Forallw] [[WFu' Forallu] vwu]]]]]].
    assert (exists w : Vector (2 ^ n),
        WF_Matrix w /\
        (exists u : Vector (2 ^ m),
           WF_Matrix u /\
           (WF_Matrix w /\
            Forall (fun a0 : AType n => vecSatisfies w (translateA a0))
              (map TtoA Lt1)) /\ v = w ⊗ u)).
    { exists w. split; auto. exists u. auto. }
    rewrite E in H14.
    destruct H14 as [WFv Forallv1].
    assert (exists w : Vector (2 ^ n),
        WF_Matrix w /\
        (exists u : Vector (2 ^ m),
           WF_Matrix u /\
           (WF_Matrix u /\
            Forall (fun a0 : AType m => vecSatisfies u (translateA a0))
              (map TtoA Lt2)) /\ v = w ⊗ u)).
    { exists w. split; auto. exists u. auto. }
    rewrite E' in H14.
    destruct H14 as [WFv' Forallv2].
    repeat split; auto.
  - destruct H14 as [WFv [Forallv1 Forallv2]].
    assert (WF_Matrix v /\
     Forall (fun a0 : AType (n + m) => vecSatisfies v (translateA a0))
       (map (uncurry gTensorA)
          (combine (map TtoA Lt1) (map TtoA (repeat (defaultT_I m) (length Lt1)))))) by auto.
    rewrite <- E in H14.
    assert (WF_Matrix v /\
     Forall (fun a0 : AType (n + m) => vecSatisfies v (translateA a0))
       (map (uncurry gTensorA)
          (combine (map TtoA (repeat (defaultT_I n) (length Lt2))) (map TtoA Lt2)))) by auto.
    rewrite <- E' in H15.
    destruct H14 as [w [WFw [u [WFu [[WF_w Forallw] vwu]]]]].
    destruct H15 as [w' [WFw' [u' [WFu' [[WF_u' Forallu'] vw'u']]]]].
    assert (w ⊗ u = w' ⊗ u') by (rewrite vwu in vw'u'; auto).
    destruct (Classical_Prop.classic (v = Zero)).
    + rewrite H15 in *. 
      exists Zero. split; auto with wf_db.
      exists Zero. split; auto with wf_db.
      repeat split; auto with wf_db.
      * rewrite Forall_forall. intros.
        apply vecSatisfies_Zero_l.
      * rewrite Forall_forall. intros.
        apply vecSatisfies_Zero_l.
      * rewrite kron_0_l. auto.
    + rewrite vwu in H15.
      destruct (tensor_nonzero_exists w w' u u' WFw WFu WFw' WFu' H15 H14)
        as [c1 [c2 [c1mult [c2mult c1c2]]]].
      exists w. split; auto with wf_db.
      exists u. repeat split; auto with wf_db.
      rewrite c2mult.
      rewrite Forall_forall. intros x H16.
      rewrite Forall_forall in Forallu'.
      specialize (Forallu' x H16).
      unfold vecSatisfies in *.
      destruct Forallu'.
      split; auto with wf_db.
      unfold Eigenpair in *.
      simpl in *.
      rewrite Mscale_1_l in *.
      rewrite Mscale_mult_dist_r.
      rewrite H18; auto.
Qed.


Inductive separability_precondition {n : nat} (lt : list (TType n)) : Prop :=
| SepPrecond : linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 lt)) -> n <> 0%nat ->
    lt <> [] -> Forall proper_length_TType lt -> Forall coef_plus_minus_1 lt ->
    commutingListT lt -> length lt = n -> separability_precondition lt.

Lemma map_combine_TtoA : forall {n m : nat} (Lt1 : list (TType n)) (Lt2 : list (TType m)),
    length Lt1 = length Lt2 ->
    map (uncurry gTensorA) (combine (map TtoA Lt1) (map TtoA Lt2)) =
      map TtoA (map (uncurry gTensorT) (combine Lt1 Lt2)).
Proof. intros n m Lt1 Lt2 H.
  rewrite map_map. unfold TtoA.
  apply nth_ext with (d := (uncurry gTensorA) ([defaultT_I n], [defaultT_I m]))
                     (d' := (fun x : TType n * TType m => [uncurry gTensorT x]) (defaultT_I n, defaultT_I m)).
  rewrite ! map_length, ! combine_length, ! map_length; auto.
  intros n0 H0.
  rewrite map_nth with (d := ([defaultT_I n], [defaultT_I m])).
  rewrite map_nth with (d := (defaultT_I n, defaultT_I m)).
  rewrite ! combine_nth; try rewrite ! map_length; auto.
  rewrite map_nth with (d := defaultT_I n).
  rewrite map_nth with (d := defaultT_I m).
  unfold uncurry. simpl; auto.
Qed.


Lemma separability_proof2' :
  forall (n m : nat) (Lt1 : list (TType n)) (Lt2 : list (TType m)),
    separability_precondition Lt1 -> separability_precondition Lt2 ->
    (forall v : Vector (2 ^ (n + m))%nat,
      (exists w : Vector (2 ^ n)%nat, WF_Matrix w /\ (exists u : Vector (2 ^ m)%nat, WF_Matrix u /\
        vecSatisfiesP w (Cap (map TtoA Lt1)) /\ vecSatisfiesP u (Cap (map TtoA Lt2)) 
                                                                      /\ v = w ⊗ u)) <->
        vecSatisfiesP v (Cap (map TtoA (DiagonalTwice Lt1 Lt2)))).
Proof. intros n m Lt1 Lt2 H0 H1 v.
  unfold DiagonalTwice, ExtendQubitsToLeft, ExtendQubitsToRight.
  rewrite map_app. rewrite <- ! map_combine_TtoA.
  2-3: rewrite repeat_length; auto.
  inversion H0. inversion H1.
  apply separability_proof2; auto.
Qed.




Lemma separability_precondition_DiagonalTwice_inv : 
  forall {n m : nat} (Lt1 : list (TType n)) (Lt2 : list (TType m)),
    separability_precondition (DiagonalTwice Lt1 Lt2) ->
    n <> 0%nat -> m <> 0%nat -> Lt1 <> [] -> Lt2 <> [] -> length Lt1 = n -> length Lt2 = m ->
    separability_precondition Lt1 /\ separability_precondition Lt2.
Proof. intros n m Lt1 Lt2 H0 H1 H2 H3 H4 H5 H6. 
  split.
  - unfold DiagonalTwice in H0.
    unfold ExtendQubitsToRight, ExtendQubitsToLeft in H0.
    inversion H0. clear H0.
    constructor; auto.
    + assert (properLt1 : Forall proper_length_TType Lt1).
      {  rewrite Forall_app in H10. destruct H10.
         rewrite Forall_forall in H0.
         rewrite Forall_forall. intros x H14.
         specialize (H0 ((uncurry gTensorT) (x, defaultT_I m))).
         assert (In (uncurry gTensorT (x, defaultT_I m))
                   (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
         { rewrite in_map_iff. exists (x, defaultT_I m). split; auto.
           apply In_nth with (d := defaultT_I n) in H14.
           destruct H14 as [n0 [n0bound nthn0]].
           assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
           { rewrite repeat_length; auto. }
           rewrite repeat_nth in H14.
           specialize (H14 n0).
           rewrite <- nthn0 at 1. rewrite <- H14 at 1.
           rewrite <- combine_nth.
           apply nth_In.
           rewrite combine_length, repeat_length.
           minmax_breakdown. auto.
           rewrite repeat_length. auto. }
         specialize (H0 H15).
         unfold uncurry in H0. simpl in H0.
         destruct H0. unfold defaultT_I in H16.
         destruct x. simpl in H16. rewrite app_length in H16.
         rewrite repeat_length in H16.
         constructor; simpl; auto. lia. }
      assert (properLt2 : Forall proper_length_TType Lt2).
      { rewrite Forall_app in H10. destruct H10.
        rewrite Forall_forall in H10.
        rewrite Forall_forall. intros x H14.
        specialize (H10 ((uncurry gTensorT) (defaultT_I n, x))).
        assert (In (uncurry gTensorT (defaultT_I n, x))
                  (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
        { rewrite in_map_iff. exists (defaultT_I n, x). split; auto.
          apply In_nth with (d := defaultT_I m) in H14.
          destruct H14 as [n0 [n0bound nthn0]].
          assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
          { rewrite repeat_length; auto. }
          rewrite repeat_nth in H14.
          specialize (H14 n0).
          rewrite <- nthn0 at 1. rewrite <- H14 at 1.
          rewrite <- combine_nth.
          apply nth_In.
          rewrite combine_length, repeat_length.
          minmax_breakdown. auto.
          rewrite repeat_length. auto. }
        specialize (H10 H15).
        unfold uncurry in H10. simpl in H10.
        destruct H10. unfold defaultT_I in H16.
        destruct x. simpl in H16. rewrite app_length in H16.
        rewrite repeat_length in H16.
        constructor; simpl; auto. lia. }
      rewrite Forall_app in H10. destruct H10.
      apply linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_app_split in H7;
        auto.
      destruct H7.
      apply @linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_ExtendQubitsToRight with (m := m); auto.
    + rewrite Forall_app in H10. destruct H10.
      rewrite Forall_forall in H0.
      rewrite Forall_forall. intros x H14.
      specialize (H0 ((uncurry gTensorT) (x, defaultT_I m))).
      assert (In (uncurry gTensorT (x, defaultT_I m))
         (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
      { rewrite in_map_iff. exists (x, defaultT_I m). split; auto.
        apply In_nth with (d := defaultT_I n) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H0 H15).
      unfold uncurry in H0. simpl in H0.
      destruct H0. unfold defaultT_I in H16.
      destruct x. simpl in H16. rewrite app_length in H16.
      rewrite repeat_length in H16.
      constructor; simpl; auto. lia.
    + rewrite Forall_app in H11. destruct H11.
      rewrite Forall_forall in H0.
      rewrite Forall_forall. intros x H14.
      specialize (H0 ((uncurry gTensorT) (x, defaultT_I m))).
      assert (In (uncurry gTensorT (x, defaultT_I m))
         (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
      { rewrite in_map_iff. exists (x, defaultT_I m). split; auto.
        apply In_nth with (d := defaultT_I n) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H0 H15).
      unfold uncurry in H0. simpl in H0.
      destruct H0. 
      unfold defaultT_I in H0. destruct x. simpl in H0. rewrite Cmult_1_r in H0. left; auto.
      unfold defaultT_I in H0. destruct x. simpl in H0. rewrite Cmult_1_r in H0. right; auto.
    + assert (H' : Forall proper_length_TType Lt1).
      { rewrite Forall_app in H10. destruct H10.
        rewrite Forall_forall in H0.
        rewrite Forall_forall. intros x H14.
        specialize (H0 ((uncurry gTensorT) (x, defaultT_I m))).
        assert (In (uncurry gTensorT (x, defaultT_I m))
                  (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
        { rewrite in_map_iff. exists (x, defaultT_I m). split; auto.
          apply In_nth with (d := defaultT_I n) in H14.
          destruct H14 as [n0 [n0bound nthn0]].
          assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
          { rewrite repeat_length; auto. }
          rewrite repeat_nth in H14.
          specialize (H14 n0).
          rewrite <- nthn0 at 1. rewrite <- H14 at 1.
          rewrite <- combine_nth.
          apply nth_In.
          rewrite combine_length, repeat_length.
          minmax_breakdown. auto.
          rewrite repeat_length. auto. }
        specialize (H0 H15).
        unfold uncurry in H0. simpl in H0.
        destruct H0. unfold defaultT_I in H16.
        destruct x. simpl in H16. rewrite app_length in H16.
        rewrite repeat_length in H16.
        constructor; simpl; auto. lia. }
      apply commutingListT_app in H12. destruct H12.
      unfold commutingListT in H0.
      unfold commutingListT. intros t1 t2 H14 H15. 
      specialize (H0 ((uncurry gTensorT) (t1, defaultT_I m)) ((uncurry gTensorT) (t2, defaultT_I m))).
      assert (In (uncurry gTensorT (t1, defaultT_I m))
         (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
      { rewrite in_map_iff. exists (t1, defaultT_I m). split; auto.
        apply In_nth with (d := defaultT_I n) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      assert (In (uncurry gTensorT (t2, defaultT_I m))
         (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
      { rewrite in_map_iff. exists (t2, defaultT_I m). split; auto.
        apply In_nth with (d := defaultT_I n) in H15.
        destruct H15 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H15.
        specialize (H15 n0).
        rewrite <- nthn0 at 1. rewrite <- H15 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H0 H16 H17).
      unfold uncurry in H0. simpl in H0.
      rewrite Forall_forall in H'.
      apply @commute_T_gTensorT_defaultT_I_right with (m := m); auto.
  - unfold DiagonalTwice in H0.
    unfold ExtendQubitsToRight, ExtendQubitsToLeft in H0.
    inversion H0. clear H0.
    constructor; auto.
    + assert (properLt1 : Forall proper_length_TType Lt1).
      {  rewrite Forall_app in H10. destruct H10.
         rewrite Forall_forall in H0.
         rewrite Forall_forall. intros x H14.
         specialize (H0 ((uncurry gTensorT) (x, defaultT_I m))).
         assert (In (uncurry gTensorT (x, defaultT_I m))
                   (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1))))).
         { rewrite in_map_iff. exists (x, defaultT_I m). split; auto.
           apply In_nth with (d := defaultT_I n) in H14.
           destruct H14 as [n0 [n0bound nthn0]].
           assert ((repeat (defaultT_I m) (length Lt1)) = (repeat (defaultT_I m) (length (repeat (defaultT_I m) (length Lt1))))).
           { rewrite repeat_length; auto. }
           rewrite repeat_nth in H14.
           specialize (H14 n0).
           rewrite <- nthn0 at 1. rewrite <- H14 at 1.
           rewrite <- combine_nth.
           apply nth_In.
           rewrite combine_length, repeat_length.
           minmax_breakdown. auto.
           rewrite repeat_length. auto. }
         specialize (H0 H15).
         unfold uncurry in H0. simpl in H0.
         destruct H0. unfold defaultT_I in H16.
         destruct x. simpl in H16. rewrite app_length in H16.
         rewrite repeat_length in H16.
         constructor; simpl; auto. lia. }
      assert (properLt2 : Forall proper_length_TType Lt2).
      { rewrite Forall_app in H10. destruct H10.
        rewrite Forall_forall in H10.
        rewrite Forall_forall. intros x H14.
        specialize (H10 ((uncurry gTensorT) (defaultT_I n, x))).
        assert (In (uncurry gTensorT (defaultT_I n, x))
                  (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
        { rewrite in_map_iff. exists (defaultT_I n, x). split; auto.
          apply In_nth with (d := defaultT_I m) in H14.
          destruct H14 as [n0 [n0bound nthn0]].
          assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
          { rewrite repeat_length; auto. }
          rewrite repeat_nth in H14.
          specialize (H14 n0).
          rewrite <- nthn0 at 1. rewrite <- H14 at 1.
          rewrite <- combine_nth.
          apply nth_In.
          rewrite combine_length, repeat_length.
          minmax_breakdown. auto.
          rewrite repeat_length. auto. }
        specialize (H10 H15).
        unfold uncurry in H10. simpl in H10.
        destruct H10. unfold defaultT_I in H16.
        destruct x. simpl in H16. rewrite app_length in H16.
        rewrite repeat_length in H16.
        constructor; simpl; auto. lia. }
      rewrite Forall_app in H10. destruct H10.
      apply linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_app_split in H7;
        auto.
      destruct H7.
      apply @linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_ExtendQubitsToLeft with (n := n); auto.
    + rewrite Forall_app in H10. destruct H10.
      rewrite Forall_forall in H10.
      rewrite Forall_forall. intros x H14.
      specialize (H10 ((uncurry gTensorT) (defaultT_I n, x))).
      assert (In (uncurry gTensorT (defaultT_I n, x))
         (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
      { rewrite in_map_iff. exists (defaultT_I n, x). split; auto.
        apply In_nth with (d := defaultT_I m) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H10 H15).
      unfold uncurry in H10. simpl in H10.
      destruct H10. unfold defaultT_I in H16.
      destruct x. simpl in H16. rewrite app_length in H16.
      rewrite repeat_length in H16.
      constructor; simpl; auto. lia.
    + rewrite Forall_app in H11. destruct H11.
      rewrite Forall_forall in H11.
      rewrite Forall_forall. intros x H14.
      specialize (H11 ((uncurry gTensorT) (defaultT_I n, x))).
      assert (In (uncurry gTensorT (defaultT_I n, x))
         (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
      { rewrite in_map_iff. exists (defaultT_I n, x). split; auto.
        apply In_nth with (d := defaultT_I m) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H11 H15).
      unfold uncurry in H11. simpl in H11.
      destruct H11. 
      unfold defaultT_I in H11. destruct x. simpl in H11. rewrite Cmult_1_l in H11. left; auto.
      unfold defaultT_I in H11. destruct x. simpl in H11. rewrite Cmult_1_l in H11. right; auto.
    + assert (H' : Forall proper_length_TType Lt2).
      { rewrite Forall_app in H10. destruct H10.
        rewrite Forall_forall in H10.
        rewrite Forall_forall. intros x H14.
        specialize (H10 ((uncurry gTensorT) (defaultT_I n, x))).
        assert (In (uncurry gTensorT (defaultT_I n, x))
                  (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
        { rewrite in_map_iff. exists (defaultT_I n, x). split; auto.
          apply In_nth with (d := defaultT_I m) in H14.
          destruct H14 as [n0 [n0bound nthn0]].
          assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
          { rewrite repeat_length; auto. }
          rewrite repeat_nth in H14.
          specialize (H14 n0).
          rewrite <- nthn0 at 1. rewrite <- H14 at 1.
          rewrite <- combine_nth.
          apply nth_In.
          rewrite combine_length, repeat_length.
          minmax_breakdown. auto.
          rewrite repeat_length. auto. }
        specialize (H10 H15).
        unfold uncurry in H10. simpl in H10.
        destruct H10. unfold defaultT_I in H16.
        destruct x. simpl in H16. rewrite app_length in H16.
        rewrite repeat_length in H16.
        constructor; simpl; auto. lia. }
      apply commutingListT_app in H12. destruct H12.
      unfold commutingListT in H12.
      unfold commutingListT. intros t1 t2 H14 H15. 
      specialize (H12 ((uncurry gTensorT) (defaultT_I n, t1)) ((uncurry gTensorT) (defaultT_I n, t2))).
      assert (In (uncurry gTensorT (defaultT_I n, t1))
         (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
      { rewrite in_map_iff. exists (defaultT_I n, t1). split; auto.
        apply In_nth with (d := defaultT_I m) in H14.
        destruct H14 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H14.
        specialize (H14 n0).
        rewrite <- nthn0 at 1. rewrite <- H14 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      assert (In (uncurry gTensorT (defaultT_I n, t2))
         (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2))).
      { rewrite in_map_iff. exists (defaultT_I n, t2). split; auto.
        apply In_nth with (d := defaultT_I m) in H15.
        destruct H15 as [n0 [n0bound nthn0]].
        assert ((repeat (defaultT_I n) (length Lt2)) = (repeat (defaultT_I n) (length (repeat (defaultT_I n) (length Lt2))))).
        { rewrite repeat_length; auto. }
        rewrite repeat_nth in H15.
        specialize (H15 n0).
        rewrite <- nthn0 at 1. rewrite <- H15 at 1.
        rewrite <- combine_nth.
        apply nth_In.
        rewrite combine_length, repeat_length.
        minmax_breakdown. auto.
        rewrite repeat_length. auto. }
      specialize (H12 H16 H17).
      unfold uncurry in H12. simpl in H12.
      rewrite Forall_forall in H'.
      apply @commute_T_gTensorT_defaultT_I_left with (n := n); auto.
Qed.



Lemma separability_proof_n :
  forall (Ln : list nat) (LLT : list (list TTypes)),
    LLT <> [] -> length Ln = length LLT -> 
    Forall (fun n => n <> 0%nat) Ln -> Forall (fun LT => LT <> []) LLT ->
    Forall2 (fun n LT => length LT = n) Ln LLT ->
    separability_precondition (DiagonalQubits Ln LLT) ->
    (forall v : Vector (2 ^ (fold_right Nat.add 0%nat Ln)),
        (exists Lnw : list {n : nat & Vector (2 ^ n)},
            map (@projT1 nat (fun n : nat => Vector (2 ^ n))) Lnw = Ln /\
              Forall (fun nw => @WF_Matrix (2^(projT1 nw))%nat 1%nat (projT2 nw)) Lnw /\
              Forall2 
                (fun nw LT => vecSatisfiesP (projT2 nw) (Cap (map TtoA (map (AssignT (projT1 nw)) LT)))) Lnw LLT /\ 
              v = big_kron_sigT_Vector Lnw) <->
          vecSatisfiesP v (Cap (map TtoA (DiagonalQubits Ln LLT)))).
Proof. intros Ln LLT H0 H1 H2 H3 lenLT H4 v. 
  gen Ln. induction LLT as [| t LLT]; intros; try contradiction.
  destruct Ln; try discriminate.
  destruct (Classical_Prop.classic (LLT = [])).
  - subst. clear H0. destruct Ln; try discriminate. clear H1.
    clear IHLLT. inversion H3; subst. clear H3 H6. 
    inversion H2; subst. clear H2 H6.
    simpl in *. unfold DiagonalTwice in H4.
    rewrite ExtendQubitsToRight_zero, ExtendQubitsToLeft_nil in H4.
    rewrite app_nil_r in H4.
    split; intros.
    + destruct H0 as [Lnw [H1 [H2 [H6 H7]]]].
      destruct Lnw as [| nw]. inversion H1.
      simpl in *. inversion H1. subst. destruct Lnw; try discriminate.
      clear H9. clear H1. inversion H2; subst. clear H2 H8.
      inversion H6; subst. clear H6 H10. destruct H8.
      destruct nw as [n w]. simpl in *.
      replace (n + 0)%nat with n in * by lia.
      split; auto with wf_db. rewrite kron_1_r.
      unfold DiagonalTwice.
      rewrite ExtendQubitsToRight_zero, ExtendQubitsToLeft_nil.
      rewrite app_nil_r. auto.
    + destruct H0.
      unfold DiagonalTwice in H1.
      rewrite ExtendQubitsToRight_zero, ExtendQubitsToLeft_nil in H1.
      rewrite app_nil_r in H1.
      exists [existT (fun n => Vector (2 ^ n)%nat) n v].
      simpl in *. 
      repeat split; repeat constructor; simpl; replace (n + 0)%nat with n in * by lia; auto.
      rewrite kron_1_r. auto.
  - clear H0.
    simpl in H1. apply Nat.succ_inj in H1.
    rewrite Forall_cons_iff in H2. destruct H2.
    rewrite Forall_cons_iff in H3. destruct H3.
    inversion lenLT; subst. clear lenLT. rename H12 into lenLT.
    simpl in H4.
    apply separability_precondition_DiagonalTwice_inv in H4.
    destruct H4.
    specialize (IHLLT H5 H6 Ln H1 H2 lenLT H7).
    2: auto.
    2: { assert (Ln <> []).
         { intro. subst. contradict H5. rewrite <- length_zero_iff_nil. auto. }
         apply fold_right_add_nonzero; auto. }
    2: { intro. contradict H3. apply map_eq_nil in H7. auto. }
    2: { destruct LLT; try contradiction. destruct Ln; try discriminate.
         simpl. unfold DiagonalTwice. unfold ExtendQubitsToRight, ExtendQubitsToLeft.
         intro.
         assert (length (@nil (TType (Nat.add n (@fold_right nat nat Nat.add O Ln)))) <> 0%nat).
         { rewrite <- H7.
           rewrite ! app_length, ! map_length, ! combine_length, ! repeat_length, ! map_length.
           minmax_breakdown.
           rewrite Forall_cons_iff in H6. destruct H6.
           intro. contradict H6. rewrite <- length_zero_iff_nil. lia. }
         simpl in H8. contradiction. }
    2: { rewrite map_length. auto. }
    2: { apply DiagonalQubits_length; auto. }
    split; intros.
    + destruct H8 as [Lnw [H9 [H10 [H11 H12]]]].
      destruct Lnw as [| nw Lnw]; try discriminate.
      rewrite Forall_cons_iff in H10. destruct H10.
      inversion H11; subst. destruct nw as [m w]. clear H11.
      inversion H9. subst m. clear H9. rewrite ! H13 in *.
      simpl in *. destruct H16.
      split. 
      * apply WF_kron; auto. rewrite ! H13. rewrite Nat.pow_add_r; auto.
        auto with wf_db.
      * assert (Forall
    (fun a0 : AType (length t + fold_right Nat.add 0%nat Ln) =>
     vecSatisfies (w ⊗ big_kron_sigT_Vector Lnw) (translateA a0))
    (map TtoA (DiagonalTwice (map (AssignT (length t)) t) (DiagonalQubits Ln LLT))) <->
                  vecSatisfiesP (w ⊗ big_kron_sigT_Vector Lnw) 
                                (Cap (map TtoA (DiagonalTwice (map (AssignT (length t)) t) (DiagonalQubits Ln LLT))))).
        { simpl. split; intros; try split.
          - apply WF_kron; auto. rewrite ! H13. rewrite Nat.pow_add_r; auto.
            auto with wf_db.
          - rewrite ! H13 in *. rewrite Nat.pow_add_r in *. auto.
          - destruct H12. rewrite ! H13 in *. rewrite Nat.pow_add_r in *. auto. }
         rewrite ! H13 in *. rewrite Nat.pow_add_r in *. rewrite H12. clear H12.
        rewrite <- separability_proof2'; auto.
        specialize (IHLLT (big_kron_sigT_Vector Lnw)).
        assert (exists Lnw0 : list {n : nat & Vector (2 ^ n)},
             map (projT1 (P:=fun n : nat => Vector (2 ^ n))) Lnw0 = Ln /\
             Forall (fun nw : {n : nat & Vector (2 ^ n)} => WF_Matrix (projT2 nw))
               Lnw0 /\
             Forall2
               (fun (nw : {n : nat & Vector (2 ^ n)}) (LT : list TTypes) =>
                WF_Matrix (projT2 nw) /\
                Forall
                  (fun a0 : AType (projT1 nw) =>
                   vecSatisfies (projT2 nw) (translateA a0))
                  (map TtoA (map (AssignT (projT1 nw)) LT))) Lnw0 LLT /\
             big_kron_sigT_Vector Lnw = big_kron_sigT_Vector Lnw0).
        { exists Lnw. repeat split; auto. }
        rewrite IHLLT in H12.
        destruct H12.
        exists w. split; auto. exists (big_kron_sigT_Vector Lnw). repeat split; auto.
    + simpl in H8. destruct H8.
      assert (vecSatisfiesP v
                (Cap (map TtoA (DiagonalTwice (map (AssignT (length t)) t) (DiagonalQubits Ln LLT))))) by (simpl; auto).
      rewrite <- separability_proof2'
        with (Lt1 := map (AssignT (length t)) t)
             (Lt2 := DiagonalQubits Ln LLT)
        in H10; auto.
      destruct H10 as [w [H10 [u [H11 [H12 [H13 H14]]]]]].
      specialize (IHLLT u).
      remember H13 as H13'. clear HeqH13'.
      rewrite <- IHLLT in H13'.
      destruct H13' as [Lnw [H15 [H16 [H17 H18]]]].
      exists ((existT (fun n => Vector (2 ^ n)%nat) (length t) w) :: Lnw). repeat split; simpl; auto.
      rewrite ! H15 in *. auto.
      subst. auto.
Qed.


Lemma vecSatisfiesP_DiagonalQubits_CapSep : 
  forall (Ln Perm : list nat) (LLT : list (list TTypes)) (v : Vector (2 ^ (fold_right Nat.add 0%nat Ln))),
    Permutation (List.seq 0%nat (fold_right Nat.add 0%nat Ln)) Perm ->
     vecSatisfiesP v (Cap (map TtoA (DiagonalQubits Ln LLT))) -> 
    vecSatisfiesP ((perm_to_matrix (fold_right Nat.add 0%nat Ln) (perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))) × v) (Sep (Ln, LLT, Perm)). 
Proof. intros Ln Perm LLT v PermPerm H0. 
  destruct H0.
  split; auto with wf_db.
  rewrite Forall_forall in *.
  intros x H2. simpl in H2.
  assert (In (TtoA x) (map TtoA (DiagonalQubits Ln LLT))).
  { rewrite in_map_iff. exists x. auto. }
  specialize (H1 (TtoA x) H3).
  unfold TtoA, translateA in H1.
  simpl in H1. rewrite Mplus_0_l in H1.
  unfold vecSatisfies in *.
  destruct H1.
  split; auto with wf_db.
  unfold Eigenpair in *. simpl in *. rewrite Mscale_1_l in *.
  rewrite ! Mmult_assoc.
  f_equal.
  setoid_rewrite <- Mmult_assoc at 2.
  pose (perm_to_matrix_unitary (fold_right Nat.add 0%nat Ln) (perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))) as U.
  assert (permutation (fold_right Nat.add 0%nat Ln)
            (perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))).
  { apply perm_inv_permutation. 
    apply Permutation_sym in PermPerm.
    apply Permutation_permutation_seq; auto. }
  specialize (U H5).
  destruct U.
  rewrite H7, Mmult_1_l; auto.
Qed.


Lemma vecSatisfiesP_DiagonalQubits_SepCap : 
  forall (Ln_LLT_Perm : (list nat) * (list (list TTypes)) * (list nat)) (v : Vector (2 ^ (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))))),
    Forall proper_length_TType (DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm))) ->
    Permutation (List.seq 0%nat (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm)))) (snd Ln_LLT_Perm) ->
    vecSatisfiesP v (Sep Ln_LLT_Perm) ->
    vecSatisfiesP ((perm_to_matrix (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) (perm_inv (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) (to_fun 0%nat (snd Ln_LLT_Perm))))† × v) (Cap (map TtoA (DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm))))).
Proof. intros Ln_LLT_Perm v H0 H1 H2.
  simpl in *. destruct H2.
  split; auto with wf_db.
  rewrite Forall_forall in *.
  intros x H4.
  rewrite in_map_iff in H4.
  destruct H4 as [x0 [x0x inx0]].
  specialize (H3 x0 inx0).
  unfold vecSatisfies in *.
  destruct H3.
  split; auto with wf_db.
  unfold Eigenpair in *. simpl in *.
  rewrite Mscale_1_l in *.
  subst. unfold TtoA, translateA in *. simpl in *.
  rewrite Mplus_0_l.
  apply (Mmult_inj_l (adjoint
           (perm_to_matrix (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm)))
              (perm_inv (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm)))
                 (to_fun 0%nat (snd Ln_LLT_Perm)))))) in H4.
  rewrite <- ! Mmult_assoc in H4. rewrite <- ! Mmult_assoc.
  pose (perm_to_matrix_unitary (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) (perm_inv (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) (to_fun 0%nat (snd Ln_LLT_Perm)))) as U.
  assert (permutation (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm)))
            (perm_inv (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) (to_fun 0%nat (snd Ln_LLT_Perm)))).
  { apply perm_inv_permutation. 
    apply Permutation_sym in H1.
    apply Permutation_permutation_seq; auto. }
  specialize (U H5).
  destruct U.
  rewrite H7 in H4.
  rewrite Mmult_1_l in H4; auto.
  apply WF_translate.
  apply H0; auto.
Qed.





(** ** Hoare triples ** **)

Definition triple {n} (A : Predicate n) (g : prog) (B : Predicate n) :=
  forall (v : Vector (2 ^ n)), vecSatisfiesP v A -> vecSatisfiesP ((translate_prog n g) × v) B.

Notation "{{ A }} g {{ B }}" := (triple A g B) (at level 70, no associativity).


Lemma Eigenvector_Heisenberg_semantics {n} (a b : AType n) (g : prog) :
  proper_length_AType_nil a -> proper_length_AType_nil b ->
  WF_Unitary (translateA a) -> (translateA a) † = translateA a -> trace (translateA a) = 0 ->
  WF_Unitary (translateA b) -> (translateA b) † = translateA b -> trace (translateA b) = 0 ->
   {{ a }} g {{ b }} ->
  ((translate_prog n g) × translateA a = translateA b × (translate_prog n g)).
Proof. intros Pa Pb Ua Ha Ta Ub Hb Tb Triple.
  unfold triple in Triple.
  unfold vecSatisfiesP in Triple.

  assert (WFU_g : WF_Unitary (translate_prog n g)).
  { apply unit_prog. }
  
  specialize (Unitary_Hermitian_trace_zero_index_split (translateA a) Ua Ha Ta);
    intros [plus1idxA [minus1idxA [UA [DA [PermA [equal_len_A [WFDDA [WFUUA [SpecA [traceDA0 [Eigen_plus1_A Eigen_minus1_A]]]]]]]]]]].
 
  specialize (Unitary_Hermitian_trace_zero_index_split (translateA b) Ub Hb Tb);
    intros [plus1idxB [minus1idxB [UB [DB [PermB [equal_len_B [WFDDB [WFUUB [SpecB [traceDB0 [Eigen_plus1_B Eigen_minus1_B]]]]]]]]]]].


  assert (plusA_Eigen : forall x : nat, In x plus1idxA -> Eigenpair (translateA b) (translate_prog n g × UA × e_i x, C1)).
  { intros.
    specialize (Eigen_plus1_A x H0).
    unfold vecSatisfies in Triple.
     assert (WF_Matrix (UA × e_i x) /\ Eigenpair (translateA a) (UA × e_i x, C1)).
    { destruct WFUUA. split; auto with wf_db. }
    specialize (Triple (UA × e_i x) H1).
    destruct Triple.
    rewrite Mmult_assoc.
    easy. }

  assert (total_length_idxA : length (plus1idxA ++ minus1idxA) = (2 ^ n)%nat).
  { apply Permutation_length in PermA.
    rewrite seq_length in PermA.
    assumption. }

  assert (total_length_idxB : length (plus1idxB ++ minus1idxB) = (2 ^ n)%nat).
  { apply Permutation_length in PermB.
    rewrite seq_length in PermB.
    assumption. }

  assert (spans_whole_space_A : forall (v : Vector n),
             @WF_Matrix (2 ^ n) 1 v ->
             v = matrix_column_choose
                   (plus1idxA ++ minus1idxA)
                   UA
                   × (vector_row_choose
                        (plus1idxA ++ minus1idxA)
                        ((UA)† × v))).
  { intros.
    destruct WFUUA as [WFUA UUA].
    rewrite matrix_column_choose_vector_row_choose_original.
    - apply Minv_flip in UUA; auto with wf_db.
      rewrite <- Mmult_assoc.
      rewrite UUA.
      rewrite Mmult_1_l; auto with wf_db.
    - auto with wf_db.
    - apply Permutation_sym; auto. }
  
  assert (spans_whole_space_B : forall (v : Vector n),
             @WF_Matrix (2 ^ n) 1 v ->
             v = matrix_column_choose
                   (plus1idxA ++ minus1idxA)
                   (translate_prog n g × UA)
                   × (vector_row_choose
                        (plus1idxA ++ minus1idxA)
                        ((translate_prog n g × UA)† × v))).
  { intros.
    rewrite matrix_column_choose_vector_row_choose_original.
    - rewrite Mmult_adjoint.
      assert ((@Mmult (Nat.pow (Datatypes.S (Datatypes.S O)) n)
       (Nat.pow (Datatypes.S (Datatypes.S O)) n) (Datatypes.S O)
       (@Mmult (Nat.pow (Datatypes.S (Datatypes.S O)) n)
          (Nat.pow (Datatypes.S (Datatypes.S O)) n)
          (Nat.pow (Datatypes.S (Datatypes.S O)) n) (translate_prog n g) UA)
       (@Mmult (Nat.pow (Datatypes.S (Datatypes.S O)) n)
          (Nat.pow (Datatypes.S (Datatypes.S O)) n) (Datatypes.S O)
          (@Mmult (Nat.pow (Datatypes.S (Datatypes.S O)) n)
             (Nat.pow (Datatypes.S (Datatypes.S O)) n)
             (Nat.pow (Datatypes.S (Datatypes.S O)) n)
             (@adjoint (Nat.pow (Datatypes.S (Datatypes.S O)) n)
                (Nat.pow (Datatypes.S (Datatypes.S O)) n) UA)
             (@adjoint (Nat.pow (Datatypes.S (Datatypes.S O)) n)
                (Nat.pow (Datatypes.S (Datatypes.S O)) n) 
                (translate_prog n g))) v)) =
                (translate_prog n g × (UA × (UA) †) × (translate_prog n g) †) × v).
      { rewrite ! Mmult_assoc. easy. }
      rewrite H1.
      destruct WFUUA as [WFUA UUA].
      destruct WFU_g as [WF_g U_g].
      apply Minv_flip in UUA; auto with wf_db.
      rewrite UUA.
      rewrite Mmult_1_r; auto with wf_db.
      apply Minv_flip in U_g; auto with wf_db.
      rewrite U_g.
      rewrite Mmult_1_l; auto with wf_db.
    - destruct WFUUA as [WFUA UUA].
      destruct WFU_g as [WF_g U_g].
      auto with wf_db.
    - apply Permutation_sym in PermA. easy. }
  
  assert (spans_whole_space_idxB : forall (v : Vector n),
             @WF_Matrix (2 ^ n) 1 v ->
             v = matrix_column_choose
                   (plus1idxB ++ minus1idxB)
                   UB
                   × (vector_row_choose
                        (plus1idxB ++ minus1idxB)
                        ((UB)† × v))).
  { intros.
    destruct WFUUB as [WFUB UUB].
    rewrite matrix_column_choose_vector_row_choose_original.
    - apply Minv_flip in UUB; auto with wf_db.
      rewrite <- Mmult_assoc.
      rewrite UUB.
      rewrite Mmult_1_l; auto with wf_db.
    - auto with wf_db.
    - apply Permutation_sym; auto. }
  assert (half_length_idxA : length (minus1idxA) = (2 ^ (n-1))%nat).
  { rewrite app_length in total_length_idxA.
    rewrite equal_len_A in total_length_idxA.
    assert (H' : (2 ^ n = 2 * (2 ^ (n - 1)))%nat).
    { setoid_rewrite <- Nat.pow_1_r at 7.
      rewrite <- Nat.pow_add_r.
      assert (H' : (1 + (n - 1) = n)%nat).
      { simpl.
        rewrite Nat.sub_1_r.
        rewrite Nat.succ_pred; try easy.
        destruct Pa as [ | t a Pt Pa].
        - unfold translateA in Ua. simpl in Ua.
          apply zero_not_unitary in Ua. contradiction.
        - destruct Pt as [n_nonzero length_snd_t_is_n].
          replace (1 + (n - 1))%nat with ((n - 1) + 1)%nat by lia.
          assumption. }
      rewrite H'. reflexivity. }
    rewrite H' in total_length_idxA.
    lia. }

  assert (half_length_idxB : length (minus1idxB) = (2 ^ (n-1))%nat).
  { rewrite app_length in total_length_idxB.
    rewrite equal_len_B in total_length_idxB.
    assert (H' : (2 ^ n = 2 * (2 ^ (n - 1)))%nat).
    { setoid_rewrite <- Nat.pow_1_r at 7.
      rewrite <- Nat.pow_add_r.
      assert (H' : (1 + (n - 1) = n)%nat).
      { simpl.
        rewrite Nat.sub_1_r.
        rewrite Nat.succ_pred; try easy.
        destruct Pb as [ | t b Pt Pb].
        - unfold translateA in Ub. simpl in Ub.
          apply zero_not_unitary in Ub. contradiction.
        - destruct Pt as [n_nonzero length_snd_t_is_n].
          replace (1 + (n - 1))%nat with ((n - 1) + 1)%nat by lia.
          assumption. }
      rewrite H'. reflexivity. }
    rewrite H' in total_length_idxB.
    lia. }

  assert (NoDup_plus1_minus1_idxA : NoDup (plus1idxA ++ minus1idxA)).
  { apply Permutation_NoDup with (l := List.seq 0 (2 ^ n)).
    - apply Permutation_sym; trivial.
    - apply seq_NoDup. }

  assert (NoDup_plus1_idxA : NoDup plus1idxA).
  { apply NoDup_app_remove_r in NoDup_plus1_minus1_idxA; trivial. }

  assert (NoDup_minus1_idxA : NoDup minus1idxA).
  { apply NoDup_app_remove_l in NoDup_plus1_minus1_idxA; trivial. }

  assert (NoDup_plus1_minus1_idxB : NoDup (plus1idxB ++ minus1idxB)).
  { apply Permutation_NoDup with (l := List.seq 0 (2 ^ n)).
    - apply Permutation_sym; trivial.
    - apply seq_NoDup. }

  assert (NoDup_plus1_idxB : NoDup plus1idxB).
  { apply NoDup_app_remove_r in NoDup_plus1_minus1_idxB; trivial. }

  assert (NoDup_minus1_idxB : NoDup minus1idxB).
  { apply NoDup_app_remove_l in NoDup_plus1_minus1_idxB; trivial. }

  assert (spans_whole_space_Eigen_A : forall v : Vector (2 ^ n)%nat, WF_Matrix v ->
           exists w1 w2 : Vector (2 ^ n)%nat, WF_Matrix w1 /\ WF_Matrix w2 /\
             (translateA a) × w1 = w1 /\ (translateA a) × w2 = (Copp C1) .* w2 /\
               v = w1 .+ w2).
  { intros.
    apply eigenpair_to_selective_diagonal'' in Eigen_plus1_A.
    apply eigenpair_to_selective_diagonal'' in Eigen_minus1_A.
    specialize (spans_whole_space_A v H0).

    rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_A.
    rewrite selective_diagonal_app_split in spans_whole_space_A.
    rewrite ! Mmult_plus_distr_l, ! Mmult_plus_distr_r in spans_whole_space_A.
    rewrite Mscale_1_l in Eigen_plus1_A.
    apply @Mmult_inj_r with (k := 1%nat) (m := v) in Eigen_plus1_A.
    rewrite <- ! Mmult_assoc in spans_whole_space_A.
    exists (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v).
    exists (UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v).
    rewrite <- ! Mmult_assoc.
    rewrite Eigen_plus1_A.
    rewrite Eigen_minus1_A.
    split; auto with wf_db.
    split; auto with wf_db.
    split; trivial.
    split; distribute_scale; trivial.
    all : auto with wf_db. }

  assert (spans_whole_space_Eigen_B : forall v : Vector (2 ^ n)%nat, WF_Matrix v ->
           exists w1 w2 : Vector (2 ^ n)%nat, WF_Matrix w1 /\ WF_Matrix w2 /\
             (translateA b) × w1 = w1 /\ (translateA b) × w2 = (Copp C1) .* w2 /\
               v = w1 .+ w2).
  { intros.
    apply eigenpair_to_selective_diagonal'' in Eigen_plus1_B.
    apply eigenpair_to_selective_diagonal'' in Eigen_minus1_B.
    specialize (spans_whole_space_idxB v H0).

    rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_idxB.
    rewrite selective_diagonal_app_split in spans_whole_space_idxB.
    rewrite ! Mmult_plus_distr_l, ! Mmult_plus_distr_r in spans_whole_space_idxB.
    rewrite Mscale_1_l in Eigen_plus1_B.
    apply @Mmult_inj_r with (k := 1%nat) (m := v) in Eigen_plus1_B.
    rewrite <- ! Mmult_assoc in spans_whole_space_idxB.
    exists (UB × selective_diagonal (2 ^ n) plus1idxB × (UB) † × v).
    exists (UB × selective_diagonal (2 ^ n) minus1idxB × (UB) † × v).
    rewrite <- ! Mmult_assoc.
    rewrite Eigen_plus1_B.
    rewrite Eigen_minus1_B.
    split; auto with wf_db.
    split; auto with wf_db.
    split; trivial.
    split; distribute_scale; trivial.
    all : auto with wf_db. }


  assert (plus1space_orth_is_minus1space_A : forall v : Vector (2 ^ n),
             WF_Matrix v -> 
             ((forall w : Vector (2 ^ n), WF_Matrix w -> (translateA a) × w = w ->
                                    inner_product w v = 0) <->
              (translateA a) × v = (Copp C1) .* v)).
  { intros.
    split; intros.
    - specialize (spans_whole_space_Eigen_A v H0).
      destruct spans_whole_space_Eigen_A as [w1 [w2 [H2 [H3 [H4 [H5 H6]]]]]].
      specialize (H1 w1 H2 H4).
      rewrite H6 in H1.
      rewrite inner_product_plus_r in H1.
      assert (inner_product w1 w2 = 0).
      { apply Hermitian_different_eigenvalue_orthogonal_eigenvector
          with (M := translateA a) (c1 := C1) (c2 := Copp C1); auto with wf_db.
        + intro. inversion H7. lra.
        + rewrite Mscale_1_l. assumption. }
      rewrite H7 in H1.
      rewrite Cplus_0_r in H1.
      rewrite inner_product_zero_iff_zero in H1.
      rewrite H1 in H6.
      rewrite Mplus_0_l in H6.
      rewrite H6.
      all: assumption.
    - apply Hermitian_different_eigenvalue_orthogonal_eigenvector
        with (M := translateA a) (c1 := C1) (c2 := Copp C1); auto with wf_db.
      + intro. inversion H4. lra.
      + rewrite Mscale_1_l. assumption. }
  
  assert (plus1space_orth_is_minus1space_B : forall v : Vector (2 ^ n),
             WF_Matrix v -> 
             ((forall w : Vector (2 ^ n), WF_Matrix w -> (translateA b) × w = w ->
                                    inner_product w v = 0) <->
              (translateA b) × v = (Copp C1) .* v)).
  { intros.
    split; intros.
    - specialize (spans_whole_space_Eigen_B v H0).
      destruct spans_whole_space_Eigen_B as [w1 [w2 [H2 [H3 [H4 [H5 H6]]]]]].
      specialize (H1 w1 H2 H4).
      rewrite H6 in H1.
      rewrite inner_product_plus_r in H1.
      assert (inner_product w1 w2 = 0).
      { apply Hermitian_different_eigenvalue_orthogonal_eigenvector
          with (M := translateA b) (c1 := C1) (c2 := Copp C1); auto with wf_db.
        + intro. inversion H7. lra.
        + rewrite Mscale_1_l. assumption. }
      rewrite H7 in H1.
      rewrite Cplus_0_r in H1.
      rewrite inner_product_zero_iff_zero in H1.
      rewrite H1 in H6.
      rewrite Mplus_0_l in H6.
      rewrite H6.
      all: assumption.
    - apply Hermitian_different_eigenvalue_orthogonal_eigenvector
        with (M := translateA b) (c1 := C1) (c2 := Copp C1); auto with wf_db.
      + intro. inversion H4. lra.
      + rewrite Mscale_1_l. assumption. }

  assert (spans_plus_one_space_idxB : forall (v : Vector (2 ^ n)),
             Eigenpair (translateA b) (v, C1) -> @WF_Matrix (2^n)%nat 1 v ->  
             v = matrix_column_choose plus1idxB UB
                   × (vector_row_choose plus1idxB ((UB)† × v))).
  { intros. unfold Eigenpair in *; simpl in *.
    rewrite matrix_column_choose_vector_row_choose_selective_diagonal.
    apply eigenpair_to_selective_diagonal' in Eigen_plus1_B.
    apply eigenpair_to_selective_diagonal' in Eigen_minus1_B.
    specialize (spans_whole_space_idxB v H1).
    setoid_rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_idxB.
    setoid_rewrite selective_diagonal_app_split in spans_whole_space_idxB.
    setoid_rewrite Mmult_plus_distr_l in spans_whole_space_idxB.
    setoid_rewrite Mmult_plus_distr_r in spans_whole_space_idxB.
    remember spans_whole_space_idxB as spans_whole_space_idxB'.
    clear Heqspans_whole_space_idxB'.
    apply @Mmult_inj_l with (m := translateA b) (i := (2 ^ n)%nat) (j := (2 ^ n)%nat) in spans_whole_space_idxB'.
    rewrite H0 in spans_whole_space_idxB'.
    rewrite Mmult_plus_distr_l in spans_whole_space_idxB'.
    rewrite <- ! Mmult_assoc in spans_whole_space_idxB'.
    rewrite Eigen_plus1_B in spans_whole_space_idxB'.
    rewrite Eigen_minus1_B in spans_whole_space_idxB'.
    apply (Mplus_double_side spans_whole_space_idxB) in spans_whole_space_idxB'.
    assert (v .+ C1 .* v = C2 .* v). { lma'. }
    assert (UB × selective_diagonal (2 ^ n) plus1idxB × ((UB) † × v)
              .+ UB × selective_diagonal (2 ^ n) minus1idxB × ((UB) † × v)
              .+ (C1 .* UB × selective_diagonal (2 ^ n) plus1idxB × (UB) † × v
                    .+ - C1 .* UB × selective_diagonal (2 ^ n) minus1idxB × (UB) † × v) =
              C2 .* (UB × selective_diagonal (2 ^ n) plus1idxB × (UB) † × v)).
    { assert (forall (v1 v2 : Vector (2 ^ n)%nat), WF_Matrix v1 -> WF_Matrix v2 -> v1 .+ v2 .+ (C1 .* v1 .+ (- C1)%C .* v2) = C2 .* v1).
      { intros. lma'. }
      rewrite <- ! Mmult_assoc.
      distribute_scale.
      apply H3.
      1-2: auto with wf_db. }
    setoid_rewrite H2 in spans_whole_space_idxB'.
    setoid_rewrite H3 in spans_whole_space_idxB'.
    apply (Mscale_cancel v (UB × selective_diagonal (2 ^ n) plus1idxB × (UB) † × v) C2) in spans_whole_space_idxB'.
    rewrite <- Mmult_assoc.
    all : auto with wf_db.
    nonzero. }

  assert (spans_minus_one_space_idxB : forall (v : Vector (2 ^ n)),
             Eigenpair (translateA b) (v, Copp C1) -> @WF_Matrix (2^n)%nat 1 v ->  
             v = matrix_column_choose minus1idxB UB
                   × (vector_row_choose minus1idxB ((UB)† × v))).
  { intros. unfold Eigenpair in *; simpl in *.
    rewrite matrix_column_choose_vector_row_choose_selective_diagonal.
    apply eigenpair_to_selective_diagonal' in Eigen_plus1_B.
    apply eigenpair_to_selective_diagonal' in Eigen_minus1_B.
    specialize (spans_whole_space_idxB v H1).
    setoid_rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_idxB.
    setoid_rewrite selective_diagonal_app_split in spans_whole_space_idxB.
    setoid_rewrite Mmult_plus_distr_l in spans_whole_space_idxB.
    setoid_rewrite Mmult_plus_distr_r in spans_whole_space_idxB.
    remember spans_whole_space_idxB as spans_whole_space_idxB'.
    clear Heqspans_whole_space_idxB'.
    apply @Mmult_inj_l with (m := translateA b) (i := (2 ^ n)%nat) (j := (2 ^ n)%nat) in spans_whole_space_idxB'.
    rewrite H0 in spans_whole_space_idxB'.
    rewrite Mmult_plus_distr_l in spans_whole_space_idxB'.
    rewrite <- ! Mmult_assoc in spans_whole_space_idxB'.
    rewrite Eigen_plus1_B in spans_whole_space_idxB'.
    rewrite Eigen_minus1_B in spans_whole_space_idxB'.
    apply Mscale_inj with (c := (- C1)%C) in spans_whole_space_idxB'.
    apply (Mplus_double_side spans_whole_space_idxB) in spans_whole_space_idxB'.
    assert (v .+ - C1 .* (- C1 .* v) = C2 .* v). { lma'. }
    assert (UB × selective_diagonal (2 ^ n) plus1idxB × ((UB) † × v)
              .+ UB × selective_diagonal (2 ^ n) minus1idxB × ((UB) † × v)
              .+ - C1 .* (C1 .* UB × selective_diagonal (2 ^ n) plus1idxB × (UB) † × v
                            .+ - C1 .* UB × selective_diagonal (2 ^ n) minus1idxB × (UB) † × v) =
              C2 .* (UB × selective_diagonal (2 ^ n) minus1idxB × (UB) † × v)).
    { assert (forall (v1 v2 : Vector (2 ^ n)%nat), WF_Matrix v1 -> WF_Matrix v2 -> v1 .+ v2 .+ (- C1)%C .* (C1 .* v1 .+ (- C1)%C .* v2) = C2 .* v2).
      { intros. lma'. }
      rewrite <- ! Mmult_assoc.
      distribute_scale.
      apply H3.
      1-2: auto with wf_db. }
    setoid_rewrite H2 in spans_whole_space_idxB'.
    setoid_rewrite H3 in spans_whole_space_idxB'.
    apply (Mscale_cancel v (UB × selective_diagonal (2 ^ n) minus1idxB × (UB) † × v) C2) in spans_whole_space_idxB'.
    rewrite <- Mmult_assoc.
    all : auto with wf_db.
    nonzero. }

  assert (lin_indep_plus1idxA : linearly_independent (matrix_column_choose plus1idxA (translate_prog n g × UA))).
  { apply @lin_indep_smash with (n2 := (2 ^ (n - 1))%nat) (A2 := matrix_column_choose minus1idxA (translate_prog n g × UA)).
    setoid_rewrite <- matrix_column_choose_app_smash; auto with wf_db.
    unfold linearly_independent.
    intros a0 H0 H1.
    rewrite matrix_column_choose_pop_square in H1; auto with wf_db.
    unfold WF_Unitary in WFU_g.
    destruct WFU_g as [WF_g left_cancel_g].
    apply @Mmult_inj_l with (i := (2 ^ n)%nat) (j := (2 ^ n)%nat) (m := (translate_prog n g) †) in H1.
    rewrite ! app_length, ! equal_len_A, ! half_length_idxA in H1.
    assert (n <> 0%nat).
    { destruct Pa.
      - unfold translateA, translate in Ua. simpl in Ua.
        unfold WF_Unitary in Ua. destruct Ua as [WFz ZeqI].
        rewrite Mmult_0_r in ZeqI.
        do 2 apply f_equal_inv with (x := 0%nat) in ZeqI.
        unfold Zero, I in ZeqI. simpl in ZeqI.
        assert (2 ^ n <> 0)%nat.
        { intro. rewrite Nat.pow_eq_0_iff in H2. destruct H2. lia. }
        assert (0 < 2 ^ n)%nat by lia.
        rewrite <- Nat.ltb_lt in H3.
        rewrite H3 in ZeqI.
        inversion ZeqI.
        lra.
      - destruct H2. auto. }
    replace (2 ^ (n - 1) + 2 ^ (n - 1))%nat with (2 ^ n)%nat in H1
        by (replace (2 ^ (n - 1) + 2 ^ (n - 1))%nat with (2 ^ (s (n - 1)))%nat by (simpl; lia);
            replace (s (n - 1)) with n by lia; reflexivity).
    rewrite <- ! Mmult_assoc in H1.
    rewrite left_cancel_g in H1.
    rewrite Mmult_0_r, Mmult_1_l in H1.
    2 : { pose ( WF_Matrix_matrix_column_choose_indices_list (plus1idxA ++ minus1idxA) UA).
          assert (WF_Matrix UA) by auto with wf_db.
          apply w in H3.
          rewrite total_length_idxA in H3.
          apply H3. }
    unfold matrix_column_choose in H1.
    pose (permutation_preserves_map_get_vec_matrix UA PermA) as p.
    destruct (permutation_list_vector_to_matrix_times_vector p a0) as [b0 [WFb0 [Heq Perm_a0b0]]].
    - assert ((@length nat plus1idxA + 2 ^ (n - 1))%nat =
                (@length (Vector (2 ^ n))
                   (@map nat (Vector (2 ^ n)) (fun i : nat => @get_col (2 ^ n) (2 ^ n) UA i)
                      (plus1idxA ++ minus1idxA)))).
      { rewrite map_length, app_length.
        rewrite ! equal_len_A, half_length_idxA.
        reflexivity. }
      rewrite <- H3.
      apply H0.
    - rewrite ! map_length, total_length_idxA in Heq.
      rewrite H1 in Heq.
      symmetry in Heq.
      destruct WFUUA as [WFUA UAinv].
      pose (matrix_column_choose_original UA WFUA) as e.
      unfold matrix_column_choose in e.
      rewrite e in Heq.
      rewrite seq_length in Heq.
      apply (Mmult_inj_l UA†) in Heq.
      rewrite <- Mmult_assoc in Heq.
      rewrite UAinv in Heq.
      rewrite Mmult_1_l, Mmult_0_r in Heq.
      2 : rewrite map_length, seq_length in WFb0; apply WFb0.
      rewrite Heq in Perm_a0b0.
      assert ((fun i : nat => @Zero (2 ^ n)%nat 1%nat i 0%nat) = (fun _ : nat => C0)) by auto.
      rewrite H3 in Perm_a0b0.
      rewrite
        ! map_length,
        seq_length,
        total_length_idxA,
        map_const_repeat
        in Perm_a0b0.
      rewrite <- map_length with (f := (fun i : nat => a0 i 0%nat)) in Perm_a0b0.
      rewrite permutation_repeat_nth in Perm_a0b0.
      rewrite <- zero_all_zero; auto.
      intros i0 H4.
      specialize (Perm_a0b0 i0).
      rewrite equal_len_A, half_length_idxA in H4.
      replace (2 ^ (n - 1))%nat with ((2 ^ (n - 1)) * 1)%nat in H4 by lia.
      rewrite <- Nat.mul_add_distr_l in H4.
      replace (1 + 1)%nat with 2%nat in H4 by lia.
      setoid_rewrite <- Nat.pow_1_r in H4 at 11.
      rewrite <- Nat.pow_add_r in H4.
      replace (n - 1 + 1)%nat with n in H4 by lia.
      rewrite (nth_indep (map (fun i : nat => a0 i 0%nat) (List.seq 0 (2 ^ n)))
                 C0 (a0 0%nat 0%nat)) in Perm_a0b0.
      2 : rewrite map_length, seq_length; apply H4.
      rewrite (map_nth (fun i : nat => a0 i 0%nat) (List.seq 0 (2 ^ n))) in Perm_a0b0.
      rewrite seq_nth in Perm_a0b0; auto. }

  (* We define the span of UB with indices in plus1idxB as
Splus1idxB : Vector (2^n) -> Prop
Splus1idxB (v : Vector (2^n)) := span (matrix_column_choose plus1idxB UB) v
where we can use "span_is_subspace" to show (subspace Splus1idxB). *)
  pose (span (matrix_column_choose plus1idxB UB)) as Splus1idxB.
  assert (subspace_Splus1idxB : subspace Splus1idxB)
    by (apply span_is_subspace; auto with wf_db).

  (* We define the +1 eigenspace of Q as
Splus1B : Vector (2^n) -> Prop
Splus1B (v : Vector (2^n)) := WF_Matrix v /\ v = translateA b × v
where we need to show (subspace Splus1B). *)
  pose (fun (v : Vector (2 ^ n)%nat) => WF_Matrix v /\ v = translateA b × v) as Splus1B.
  assert (subspace_Splus1B : subspace Splus1B).
  { unfold subspace, Splus1B.
    repeat (split; intros);
      repeat match goal with [H : ?A /\ ?B |- _] => destruct H; auto with wf_db end.
    - rewrite Mmult_0_r; auto.
    - rewrite Mmult_plus_distr_l, <- H2, <- H3; auto.
    - rewrite Mscale_mult_dist_r, <- H1; auto. }

  (*  We define the span of { U v1, U v2, ..., U vn } as
Splus1gA : Vector (2^n) -> Prop
Splus1gA (v : Vector (2^n)) := span ((translate_prog n g) × (matrix_column_choose plus1idxA UA)) v
where we can use "span_is_subspace" to show (subspace Splus1gA). *)
  pose (span ((translate_prog n g) × (matrix_column_choose plus1idxA UA))) as Splus1gA.
  assert (subspace_Splus1gA : subspace Splus1gA)
    by (apply span_is_subspace; auto with wf_db).

  (* << Eigen_plus1_B >> shows that Splus1idxB is a subspace of Splus1B. *)
  assert (forall (v : Vector (2 ^ n)%nat), Splus1idxB v -> Splus1B v).
  { intros v H0.
    remember H0 as H0'. clear HeqH0'.
    unfold Splus1B. unfold Splus1idxB in H0'.
    remember subspace_Splus1idxB as subspace_Splus1idxB'.
    unfold subspace in subspace_Splus1idxB'. clear Heqsubspace_Splus1idxB'.
    destruct subspace_Splus1idxB'
      as [WF_Splus1idxB [Splus1idxB_Zero [Splus1idxB_plus Splus1idxB_scale]]].
    specialize (WF_Splus1idxB v H0).
    split; auto.
    destruct WFUUB as [WFUB UBinv].
    pose (eigenpair_to_selective_diagonal' plus1idxB C1 (translateA b) UB
            WFUB Eigen_plus1_B) as e.
    unfold span in H0'.
    rewrite equal_len_B, half_length_idxB in H0'.
    destruct H0' as [w [WFw eqw]].
    pose (vector_row_choose_inverse (2 ^ n)%nat plus1idxB) as e0.
    rewrite equal_len_B, half_length_idxB in e0.
    assert (incl_plus1idxB_seq : incl plus1idxB (List.seq 0 (2 ^ n))).
    { apply Permutation_incl in PermB.
      apply incl_app_inv in PermB.
      destruct PermB; auto. }
    destruct (e0 w NoDup_plus1_idxB incl_plus1idxB_seq WFw) as [w' [WFw' He0]].
    apply (@Mmult_inj_r (2 ^ n)%nat (2 ^ n)%nat 1%nat w') in e.
    rewrite Mscale_1_l in e.
    replace (translateA b × UB × selective_diagonal (2 ^ n) plus1idxB × w')
      with (translateA b × (UB × selective_diagonal (2 ^ n) plus1idxB × w'))
      in e
        by (rewrite ! Mmult_assoc; reflexivity).
    rewrite <- ! (matrix_column_choose_vector_row_choose_selective_diagonal plus1idxB UB w' NoDup_plus1_idxB WFUB WFw') in e.
    rewrite <- ! He0, ! equal_len_B, ! half_length_idxB in e.
    rewrite <- ! eqw in e.
    auto. }
(* <<spans_plus_one_space_idxB>> shows that Splus1B is a subspace of Splus1idxB. *)
  assert (forall (v : Vector (2 ^ n)%nat), Splus1B v -> Splus1idxB v).
  { intros v H1.
    remember H1 as H1'. clear HeqH1'.
    unfold Splus1B in H1'. unfold Splus1idxB.
    destruct H1' as [WFv H1'].
    unfold span.
    assert (Eigenpair (translateA b) (v, C1)).
    { unfold Eigenpair.
      simpl.
      rewrite Mscale_1_l.
      auto. }
    pose (spans_plus_one_space_idxB v H2 WFv) as v_spaned.
    exists (vector_row_choose plus1idxB ((UB) † × v)).
    split; auto with wf_db. }
  (* Use "matrix_column_choose_app_smash", "lin_indep_smash", " matrix_column_choose_vector_row_choose_original"  to show (matrix_column_choose plus1idxB UB) is linearly independent.  *)
  assert (linearly_independent (matrix_column_choose plus1idxB UB)).
  { apply @lin_indep_smash with (A2 := matrix_column_choose minus1idxB UB) (n2 :=  length minus1idxB).
    setoid_rewrite <- matrix_column_choose_app_smash; auto with wf_db.
    unfold linearly_independent.
    rewrite <- ! app_length.
    intros a0 H2 H3.
    destruct (vector_row_choose_inverse (2 ^ n) (plus1idxB ++ minus1idxB) a0)
      as [w [WFw eqw]]; auto with wf_db.
    1 : apply Permutation_incl; auto.
    rewrite eqw in H3.
    rewrite matrix_column_choose_vector_row_choose_original in H3;
      auto with wf_db.
    2: apply Permutation_sym; auto.
    assert (linearly_independent UB)
      by (apply WF_Unitary_implies_linearly_independent; auto).
    unfold linearly_independent in H4.
    specialize (H4 w WFw H3).
    rewrite H4 in eqw.
    rewrite vector_row_choose_Zero in eqw; auto. }
  (* Then we have (basis Splus1idxB (matrix_column_choose plus1idxB UB)). *)
  assert (basis Splus1idxB (matrix_column_choose plus1idxB UB)).
  { unfold basis.
    repeat (split; auto with wf_db).
    intros i0 H3.
    unfold Splus1idxB.
    apply span_get_vec; auto with wf_db. }
  (* Thus, (dimension Splus1idxB (length plus1idxB)). *)
  assert (dimension Splus1idxB (length plus1idxB)).
  { unfold dimension.
    exists (matrix_column_choose plus1idxB UB).
    split; auto with wf_db. }
  (* Therefore (forall v, Splus1B v <-> Splus1idxB v) and (dimension Splus1B (length plus1idxB)). *)
  assert (forall v, Splus1B v <-> Splus1idxB v) by (intros; split; auto).
  assert (basis Splus1B (matrix_column_choose plus1idxB UB))
    by (rewrite (equivalent_subspace_basis H5); auto).
  assert (dimension Splus1B (length plus1idxB)).
  { unfold dimension.
    exists (matrix_column_choose plus1idxB UB).
    split; auto with wf_db. }
  (* <<plusA_Eigen>> shows that Splus1gA is a subspace of Splus1B *)
  assert (forall v, Splus1gA v -> Splus1B v).
  { intros v H8. 
    unfold Splus1gA in H8.
    unfold Splus1B.
    split;
      try apply @span_WF_Matrix with
      (M := translate_prog n g × matrix_column_choose plus1idxA UA)
      (m := length plus1idxA);
      auto with wf_db.
    apply eigenpair_to_selective_diagonal' in plusA_Eigen; auto with wf_db.
    rewrite Mscale_1_l in plusA_Eigen.
    unfold span in H8.
    destruct H8 as [w [WFw eqw]].
    assert (incl_plus1idxA_seq : incl plus1idxA (List.seq 0%nat (2 ^ n))).
    { apply Permutation_incl in PermA.
      apply incl_app_inv in PermA.
      destruct PermA; auto. }
    destruct (vector_row_choose_inverse (2 ^ n)%nat plus1idxA w NoDup_plus1_idxA
                 incl_plus1idxA_seq WFw)
      as [w0 [WFw0 eqw0]].
    rewrite eqw0 in eqw.
    rewrite Mmult_assoc in eqw.
    rewrite matrix_column_choose_vector_row_choose_selective_diagonal in eqw;
      auto with wf_db.
    rewrite ! eqw, <- ! Mmult_assoc.
    rewrite <- ! Mmult_assoc in plusA_Eigen.
    rewrite plusA_Eigen.
    reflexivity. }
  (* Using "matrix_column_choose_app_smash", "lin_indep_smash", " matrix_column_choose_vector_row_choose_original", we can show (linearly_independent (translate_prog n g × matrix_column_choose plus1idxA UA)). *)
  assert (linearly_independent (translate_prog n g × matrix_column_choose plus1idxA UA)).
  { assert (invertible (translate_prog n g)) by (apply WF_Unitary_implies_invertible; auto).
    rewrite left_invertible_linearly_independent; auto with wf_db.
    apply @lin_indep_smash with
      (n2 := length minus1idxA)
      (A2 := matrix_column_choose minus1idxA UA).
    rewrite <- matrix_column_choose_app_smash; auto with wf_db.
    unfold linearly_independent.
    rewrite <- ! app_length.
    intros a0 H10 H11.
    assert (incl_plusminus1idxA_seq : incl (plus1idxA ++ minus1idxA) (List.seq 0 (2 ^ n))).
    { apply Permutation_incl in PermA; auto. }
    destruct (vector_row_choose_inverse (2 ^ n)%nat (plus1idxA ++ minus1idxA) a0 NoDup_plus1_minus1_idxA incl_plusminus1idxA_seq H10)
      as [w [WFw eqw]].
    rewrite eqw in H11.
    rewrite matrix_column_choose_vector_row_choose_original in H11;
      auto with wf_db.
    2 : apply Permutation_sym; auto.
    assert (linearly_independent UA)
      by (apply WF_Unitary_implies_linearly_independent; auto).
    unfold linearly_independent in H12.
    specialize (H12 w WFw H11).
    rewrite H12 in eqw.
    rewrite vector_row_choose_Zero in eqw.
    auto with wf_db. }
    (* Then, by the definition of Splus1gA, we have (basis Splus1gA (translate_prog n g × matrix_column_choose plus1idxA UA)). *)
  assert (basis Splus1gA (translate_prog n g × matrix_column_choose plus1idxA UA)).
  { unfold basis.
    repeat (split; auto with wf_db).
    intros i0 H10.
    unfold Splus1gA.
    apply span_get_vec; auto with wf_db. }
  (* Thus, (dimension Splus1gA (length plus1idxB)). *)
  assert (dimension Splus1gA (length plus1idxB)).
  { unfold dimension.
    rewrite equal_len_B, half_length_idxB, <- half_length_idxA, <- equal_len_A.
    exists (translate_prog n g × matrix_column_choose plus1idxA UA).
    split; auto with wf_db. }
  (* We can show by using "equal_dimension_lin_indep_basis" that a basis of Splus1gA is also a  basis of Splus1B.
   Hence { U v1, U v2, ..., U vn } forms a basis for the +1 eigenspace of Q. *)
  assert (basis Splus1B (translate_prog n g × matrix_column_choose plus1idxA UA)).
  { apply equal_dimension_lin_indep_basis; auto with wf_db.
    1 : rewrite equal_len_A, half_length_idxA, <- half_length_idxB, <- equal_len_B; auto.
    intros i0 H12.
    unfold Splus1B; split; auto with wf_db.
    (** we need a lemma for get_vec_mult with non-square matrices **)
    (* Use "get_vec_matrix_column_choose", "nth_In", and "plusA_Eigen" *)
    rewrite get_vec_mult_matrix with (A := translateA b).
    rewrite <- ! Mmult_assoc.
    rewrite <- ! matrix_column_choose_pop_square; auto with wf_db.
    rewrite ! get_vec_matrix_column_choose with (d := 0%nat); try lia; auto with wf_db.
    pose (@nth_In nat i0 plus1idxA 0%nat) as H13.
    specialize (H13 H12).
    apply plusA_Eigen in H13.
    unfold Eigenpair in H13; simpl in H13.
    rewrite Mscale_1_l, <- ! Mmult_assoc, ! e_i_get_vec in H13; auto with wf_db. }
  (* Then, by "subspace_is_basis_span", (forall v, Splus1gA v <-> Splus1B v). *)
  assert (forall v, Splus1gA v <-> Splus1B v).
  { intros; split; auto; intros.
    unfold Splus1gA.
    rewrite <- @subspace_is_basis_span with (P := Splus1B); auto. }

  assert (spans_plus_one_space_B : forall (u : Vector (2 ^ n)),
             Eigenpair (translateA b) (u, C1) -> @WF_Matrix (2^n)%nat 1 u ->  
             u = matrix_column_choose
                   plus1idxA
                   (translate_prog n g × UA)
                   × (vector_row_choose plus1idxA ((translate_prog n g × UA)† × u))).
  { intros u H14 H15.
    assert (Splus1B u).
    { unfold Splus1B.
      unfold Eigenpair in H14; simpl in H14.
      rewrite Mscale_1_l in H14.
      split; auto. }
    rewrite <- H13 in H16.
    unfold Splus1gA, span in H16.
    destruct H16 as [v [WFv eqv]].
    assert (forall i j : nat, In i minus1idxA -> In j plus1idxA ->
                       (get_vec i UA)† × (get_vec j UA) = Zero).
    { intros i0 j H16 H17.
      assert (@WF_Matrix 1%nat 1%nat (adjoint (get_vec i0 UA) × get_vec j UA))
        by auto with wf_db.
      unfold WF_Matrix in H18.
      prep_matrix_equality.
      bdestruct (x <? 1%nat).
      - bdestruct (y <? 1%nat).
        + replace x with 0%nat by lia.
          replace y with 0%nat by lia.
          replace ((adjoint (get_vec i0 UA) × get_vec j UA) 0%nat 0%nat)
            with (inner_product (get_vec i0 UA) (get_vec j UA))
            by (unfold inner_product; easy).
          rewrite unitary_columns_inner_product; auto.
          assert (~ In j minus1idxA)
            by (apply NoDup_app_in_neg_r with (list1 := plus1idxA) (list2 := minus1idxA); auto).
          bdestruct (i0 =? j)%nat.
          rewrite H22 in H16; contradiction.
          unfold I.
          bdestruct_all; simpl; lca.
        + rewrite H18; auto; lia.
      - rewrite H18; auto; lia. }
    assert (forall i : nat, In i minus1idxA ->
                     (get_vec i UA)† × matrix_column_choose plus1idxA UA = Zero).
    { intros i0 H17.
      apply det_by_get_vec_matrix.
      intros i1.
      rewrite <- get_vec_mult_matrix.
      replace (get_vec i1 Zero) with (@Zero 1%nat 1%nat) by lma'.
      bdestruct (i1 <? length plus1idxA).
      - rewrite get_vec_matrix_column_choose with (d := 0%nat); try lia; auto with wf_db.
        pose (@nth_In nat i1 plus1idxA 0%nat H18) as H19.
        specialize (H16 i0 (nth i1 plus1idxA 0%nat) H17 H19); auto.
      - assert (WF_Matrix (matrix_column_choose plus1idxA UA)) by auto with wf_db.
        prep_matrix_equality.
        unfold adjoint, Mmult; simpl.
        assert ((fun y0 : nat =>
                   (get_vec i0 UA y0 x) ^* *
                     get_vec i1 (matrix_column_choose plus1idxA UA) y0 y)
                = (fun _ : nat => C0)).
        { apply functional_extensionality. intros x0.
          unfold get_vec.
          bdestruct_all; try lca.
          rewrite H19; try lia.
          lca. }
        rewrite H20.
        replace (@Zero 1%nat 1%nat x y) with C0 by lca.
        rewrite big_sum_0_bounded; auto. }
    assert (forall i : nat, In i minus1idxA -> (translate_prog n g × get_vec i UA)† × u = Zero).
    { intros i0 H18.
      rewrite eqv.
      rewrite Mmult_adjoint.
      replace (adjoint (get_vec i0 UA) × adjoint (translate_prog n g)
                 × (translate_prog n g × matrix_column_choose plus1idxA UA × v))
        with (adjoint (get_vec i0 UA) ×
                (adjoint (translate_prog n g) × translate_prog n g) ×
                matrix_column_choose plus1idxA UA × v)
        by (rewrite ! Mmult_assoc; reflexivity).
      destruct WFU_g as [WF_g unitary_g].
      rewrite unitary_g, Mmult_1_r; auto with wf_db.
      rewrite H17; auto.
      rewrite Mmult_0_l; reflexivity. }
    assert (translate_prog n g × UA × (adjoint (translate_prog n g × UA) × u) = u).
    { rewrite Mmult_adjoint.
      replace (translate_prog n g × UA × ((UA) † × adjoint (translate_prog n g) × u))
        with ((translate_prog n g × (UA × (UA) †) × adjoint (translate_prog n g)) × u)
        by (rewrite ! Mmult_assoc; reflexivity).
      destruct WFUUA as [WFUA unitary_UA].
      apply Minv_flip in unitary_UA; auto with wf_db.
      rewrite unitary_UA, Mmult_1_r; auto with wf_db.
      destruct WFU_g as [WF_g unitary_g].
      apply Minv_flip in unitary_g; auto with wf_db.
      rewrite unitary_g, Mmult_1_l; auto with wf_db. }
    assert (forall i : nat, In i minus1idxA -> (adjoint (translate_prog n g × UA) × u) i 0%nat = C0).
    { intros i0 H20.
      rewrite <- inner_product_vector_with_standard_basis.
      unfold inner_product.
      rewrite <- unitary_adjoint_on_column_vector with (U := UA); auto with wf_db.
      setoid_rewrite <- Mmult_1_r at 2; auto with wf_db.
      destruct WFU_g as [WF_g unitary_g].
      rewrite <- unitary_g.
      rewrite <- ! Mmult_assoc.
      rewrite <- Mmult_adjoint.
      rewrite ! Mmult_assoc in H19.
      rewrite ! Mmult_assoc.
      setoid_rewrite H19; try apply H20.
      rewrite H18; auto.
      pose (Permutation_incl nat (plus1idxA ++ minus1idxA) (List.seq 0 (2 ^ n)) PermA)
        as incl_list.
      apply incl_app_inv in incl_list.
      destruct incl_list as [incl_list_plus incl_list_minus].
      apply incl_list_minus in H20.
      rewrite in_seq in H20.
      lia. }
    assert (vector_row_choose minus1idxA (adjoint (translate_prog n g × UA) × u) = Zero).
    { unfold vector_row_choose.
      prep_matrix_equality.
      assert (WF_Matrix (adjoint (translate_prog n g × UA) × u)) by auto with wf_db.
      bdestruct (y <? 1)%nat.
      - replace y with 0%nat by lia.
        bdestruct (x <? length minus1idxA).
        + rewrite (H20 (nth x minus1idxA (2 ^ n)%nat)
                     (@nth_In nat x minus1idxA (2 ^ n)%nat H23)).
          lca.
        + rewrite nth_overflow; auto.
      - rewrite H21; auto; try lia. }
    assert (linearly_independent
              (translate_prog n g × matrix_column_choose plus1idxA UA))
      by (rewrite <- matrix_column_choose_pop_square; auto with wf_db).
    rewrite Mmult_assoc in H19.
    rewrite <- matrix_column_choose_vector_row_choose_original
      with (indices_list := plus1idxA ++ minus1idxA)
           (M := UA)
           (v := (adjoint (translate_prog n g × UA) × u))
      in H19; auto with wf_db.
    2 : apply Permutation_sym; auto.
    rewrite matrix_column_choose_vector_row_choose_app_split in H19;
      auto with wf_db.
    rewrite H21, Mmult_0_r, Mplus_0_r in H19.
    assert ((translate_prog n g × matrix_column_choose plus1idxA UA) ×
              (v .+ (Copp C1) .* (vector_row_choose plus1idxA (adjoint (translate_prog n g × UA) × u))) = Zero).
    { assert (forall (n m : nat) (M : Matrix n m) (v w : Vector m),
                 WF_Matrix M -> WF_Matrix v -> WF_Matrix w ->
                 M × v = M × w -> M × (v .+ (Copp C1) .* w) = Zero).
      { intros n0 m M v0 w H23 H24 H25 H26. 
        rewrite Mmult_plus_distr_l.
        distribute_scale.
        rewrite H26.
        lma'. }
      apply H23;
        try apply WF_Matrix_vector_row_choose_indices_list; auto with wf_db.
      rewrite <- eqv.
      rewrite Mmult_assoc; auto. }
    unfold linearly_independent in H22.
    apply H22 in H23.
    2 : apply WF_plus; 
    try apply WF_scale;
    try apply WF_Matrix_vector_row_choose_indices_list;
    auto with wf_db.
    assert (forall (n : nat) (v w : Vector n),
               WF_Matrix v -> WF_Matrix w ->
               v .+ (Copp C1) .* w = Zero -> v = w).
    { intros n0 v0 w H24 H25 H26.
      apply Mplus_inj_r with (m := w) in H26.
      rewrite Mplus_assoc in H26.
      rewrite Mplus_opp_l, Mplus_0_l, Mplus_0_r in H26; auto. }
    apply H24 in H23;
      try apply WF_Matrix_vector_row_choose_indices_list; auto with wf_db.
    rewrite H23 in eqv.
    rewrite matrix_column_choose_pop_square; auto with wf_db. }                                               

  assert (minusA_Eigen: forall x : nat, In x minus1idxA -> Eigenpair (translateA b) (translate_prog n g × UA × e_i x, Copp C1)).
  { intros x H14. 
    unfold Eigenpair in *; simpl in *.
    pose (NoDup_app_in_neg_l nat x plus1idxA minus1idxA NoDup_plus1_minus1_idxA H14).

    specialize (Eigen_minus1_A x H14).
    
    rewrite <- plus1space_orth_is_minus1space_B.
    intros w H15 H16. 

    setoid_rewrite Mscale_1_l in spans_plus_one_space_B.
    specialize (spans_plus_one_space_B w H16 H15).

    rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_plus_one_space_B.
    
    unfold inner_product.
    rewrite spans_plus_one_space_B.

    distribute_adjoint.
     rewrite ! adjoint_involutive. 
    replace (((w) † × (translate_prog n g × UA)
                × ((selective_diagonal (2 ^ n) plus1idxA) † × ((UA) † × (translate_prog n g) †))
                × (translate_prog n g × UA × e_i x)))
      with (w † × (translate_prog n g) × UA
              × (selective_diagonal (2 ^ n) plus1idxA) † × (UA † × ((translate_prog n g) †
                                                                      × (translate_prog n g)) × UA) × e_i x)
      by (rewrite <- ! Mmult_assoc; reflexivity). 
    destruct WFUUA as [WFUA UUA].
    destruct WFU_g as [WF_g U_g].
    rewrite U_g.
    rewrite Mmult_1_r.
    rewrite UUA.
    rewrite Mmult_1_r.
    rewrite selective_diagonal_hermitian.
    
    rewrite ! Mmult_assoc.
    rewrite selective_diagonal_e_i_zero.
    rewrite ! Mmult_0_r.
    lca.
    all : auto with wf_db. }

  assert (Eigen_plus1_A_inv : forall v : Vector (2 ^ n),
             Eigenpair (translateA a) (v, C1) ->
             WF_Matrix v ->
             v = matrix_column_choose plus1idxA UA ×
                      vector_row_choose plus1idxA (UA † × v)).
  { intros v H14 H15. 

    unfold Eigenpair in *; simpl in *.

    rewrite matrix_column_choose_vector_row_choose_selective_diagonal.
    
    rewrite <- ! Mmult_assoc.

    specialize (spans_whole_space_A v H15).
    rewrite matrix_column_choose_vector_row_choose_app_split in spans_whole_space_A.
    setoid_rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_A. 
    rewrite <- ! Mmult_assoc in spans_whole_space_A.



    apply eigenpair_to_selective_diagonal'' in Eigen_plus1_A.
    apply eigenpair_to_selective_diagonal'' in Eigen_minus1_A.

    remember spans_whole_space_A as spans_whole_space_A'.
    clear Heqspans_whole_space_A'.
    apply @Mmult_inj_l with (i := (2 ^ n)%nat) (j := (2 ^ n)%nat) (k := 1%nat) (m := translateA a) in spans_whole_space_A.

    rewrite Mmult_plus_distr_l with (A := translateA a) (B := UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v) (C := UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v) in spans_whole_space_A.

    rewrite <- ! Mmult_assoc in spans_whole_space_A.

    rewrite Eigen_minus1_A, Eigen_plus1_A in spans_whole_space_A.
    rewrite Mscale_1_l in H14, spans_whole_space_A.
    rewrite H14 in spans_whole_space_A.

    pose (@Mplus_double_side ((2 ^ n)%nat) (1%nat) (v)
                                 (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
                                          .+ - C1 .* UA × selective_diagonal (2 ^ n) minus1idxA
                                                 × (UA) † × v)
                                 (v)
                                 (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
                                    .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v)
                                 (spans_whole_space_A)
                                 (spans_whole_space_A')).
    replace (v .+ v) with (C2 .* v) in e by lma'.

    assert ((UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
      .+ - C1 .* UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v
      .+ (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
            .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v))
      = (C2 .* (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v))).
    { rewrite <- Mplus_assoc. distribute_scale.
      assert (forall n (v1 v2 : Vector n), WF_Matrix v1 -> WF_Matrix v2 -> v1 .+ -C1 .* v2 .+ v1 .+ v2 = C2 .* v1).
      { intros. lma'. }
      rewrite H16 with (v1 := UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
                      (v2 := UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v).
      all: auto with wf_db. }

    rewrite H16 in e.
    apply Mscale_cancel with (c := C2) in e.
    assumption.
    nonzero.
    all: auto with wf_db. }

  
    assert (Eigen_minus1_A_inv : forall v : Vector (2 ^ n),
               Eigenpair (translateA a) (v, (- C1)%C) ->
               WF_Matrix v ->
               (v = matrix_column_choose minus1idxA UA ×
                      vector_row_choose minus1idxA (UA † × v))).
  { intros v H14 H15. 

    unfold Eigenpair in *; simpl in *.

    rewrite matrix_column_choose_vector_row_choose_selective_diagonal.
    rewrite <- ! Mmult_assoc.

    specialize (spans_whole_space_A v H15).
    rewrite matrix_column_choose_vector_row_choose_app_split in spans_whole_space_A.
    setoid_rewrite matrix_column_choose_vector_row_choose_selective_diagonal in spans_whole_space_A.
    rewrite <- ! Mmult_assoc in spans_whole_space_A.



    apply eigenpair_to_selective_diagonal'' in Eigen_plus1_A.
    apply eigenpair_to_selective_diagonal'' in Eigen_minus1_A.

    remember spans_whole_space_A as spans_whole_space_A'.
    clear Heqspans_whole_space_A'.
    apply @Mmult_inj_l with (i := (2 ^ n)%nat) (j := (2 ^ n)%nat) (k := 1%nat) (m := translateA a) in spans_whole_space_A.

    rewrite Mmult_plus_distr_l with (A := translateA a) (B := UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v) (C := UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v) in spans_whole_space_A.

    rewrite <- ! Mmult_assoc in spans_whole_space_A.

    rewrite Eigen_minus1_A, Eigen_plus1_A in spans_whole_space_A.
    rewrite Mscale_1_l in spans_whole_space_A.
    rewrite H14 in spans_whole_space_A.

    apply @Mscale_inj with (m := (2 ^ n)%nat) (n := 1%nat) (A := - C1 .* v)
                             (B := UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
                                    .+ - C1 .* UA × selective_diagonal (2 ^ n) minus1idxA
                                           × (UA) † × v)
                             (c := (- C1)%C) in spans_whole_space_A.

    rewrite Mscale_plus_distr_r in spans_whole_space_A.

    replace (- C1 .* (- C1 .* v)) with v in spans_whole_space_A by lma'.
    assert (- C1 .* (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
                .+ - C1 .* (- C1 .* UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v)
                     = - C1 .* (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
                           .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v).
    { distribute_scale. lma'; auto 10 with wf_db. }
    rewrite H16 in spans_whole_space_A.
    
    pose (@Mplus_double_side ((2 ^ n)%nat) (1%nat) (v)
            (- C1 .* (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
                 .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v)
            (v)
            (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
               .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v)
            (spans_whole_space_A)
            (spans_whole_space_A')).
    replace (v .+ v) with (C2 .* v) in e by lma'.

    assert (- C1 .* (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
      .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v
      .+ (UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v
          .+ UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v)
           = (C2 .* (UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v))).
    { rewrite <- Mplus_assoc. distribute_scale.
      assert (forall n (v1 v2 : Vector n), WF_Matrix v1 -> WF_Matrix v2 -> -C1 .* v1 .+ v2 .+ v1 .+ v2 = C2 .* v2).
      { intros. lma'. }
      rewrite H17 with (v1 := UA × selective_diagonal (2 ^ n) plus1idxA × (UA) † × v)
                      (v2 := UA × selective_diagonal (2 ^ n) minus1idxA × (UA) † × v).
      all: auto with wf_db. }

    rewrite H17 in e.
    apply Mscale_cancel with (c := C2) in e.
    assumption.
    nonzero.
    all: auto with wf_db. }
  
   
  unfold Eigenpair in plusA_Eigen, minusA_Eigen; simpl in *.

  assert (H': eq_eigs (translateA a) ((translate_prog n g)† × (translateA b) × (translate_prog n g))).
  { unfold eq_eigs. intros p H14 H15.  destruct p. simpl in *.
    destruct (Mat_eq_dec (2 ^ n)%nat 1%nat m Zero); auto with wf_db.
    - rewrite e.
      unfold Eigenpair. simpl.
      rewrite ! Mmult_0_r, Mscale_0_r; auto.
    - specialize (Unitary_Hermitian_eigenvalue_plusminus1 (translateA a) m c Ua H14 n0 Ha H15);
        intro Unitary_Hermitian_eigenvalue_plusminus1.
      
      destruct Unitary_Hermitian_eigenvalue_plusminus1 as [H16 | H16]; rewrite H16 in *.
      + specialize (Eigen_plus1_A_inv m H15).
        apply eigenpair_to_selective_diagonal in plusA_Eigen.
        rewrite matrix_column_choose_vector_row_choose_selective_diagonal in Eigen_plus1_A_inv.
        rewrite Eigen_plus1_A_inv.
        apply @Mmult_inj_l with (i := (2 ^ n)%nat) (m := (translate_prog n g) †) in plusA_Eigen.
        rewrite <- ! Mmult_assoc in plusA_Eigen.
        rewrite ! Mscale_mult_dist_r  in plusA_Eigen.
        rewrite ! Mscale_mult_dist_l in plusA_Eigen.
        destruct WFU_g as [WF_g U_g].
        rewrite U_g in plusA_Eigen.
        rewrite Mmult_1_l in plusA_Eigen.
        unfold Eigenpair.
        simpl.
        rewrite <- ! Mmult_assoc.
        rewrite plusA_Eigen.
        distribute_scale.
        reflexivity.
        all: auto with wf_db.
      + specialize (Eigen_minus1_A_inv m  H15).
        apply eigenpair_to_selective_diagonal in minusA_Eigen.
        rewrite matrix_column_choose_vector_row_choose_selective_diagonal in Eigen_minus1_A_inv.
        rewrite Eigen_minus1_A_inv.
        apply @Mmult_inj_l with (i := (2 ^ n)%nat) (m := (translate_prog n g) †) in minusA_Eigen.
        rewrite <- ! Mmult_assoc in minusA_Eigen.
        rewrite ! Mscale_mult_dist_r  in minusA_Eigen.
        rewrite ! Mscale_mult_dist_l in minusA_Eigen.
        destruct WFU_g as [WF_g U_g].
        rewrite U_g in minusA_Eigen.
        rewrite Mmult_1_l in minusA_Eigen.
        unfold Eigenpair.
        simpl.
        rewrite <- ! Mmult_assoc.
        rewrite minusA_Eigen.
        distribute_scale.
        reflexivity.
        all: auto with wf_db. }

  apply eq_eigs_implies_eq_unit in H'.
  apply @Mmult_inj_l with (i := (2 ^ n)%nat) (m := translate_prog n g) in H'.
  rewrite <- ! Mmult_assoc in H'.
  destruct WFU_g as [WF_g U_g].
  apply Minv_flip in U_g.
  rewrite U_g in H'.
  rewrite Mmult_1_l in H'.
  assumption.
  all: auto with wf_db.
  auto with unit_db.
Qed.

Lemma Eigenvector_Heisenberg_semantics' {n} (a b : AType n) (g : prog) :
  WF_AType a -> WF_AType b -> {{ a }} g {{ b }} ->
  ((translate_prog n g) × translateA a = translateA b × (translate_prog n g)).
Proof. intros H0 H1 H2.
  apply Eigenvector_Heisenberg_semantics.
  1 - 2 : apply proper_length_AType_implies_proper_length_AType_nil;
  apply restricted_addition_semantic_implies_proper_length_AType.
  3, 6 : apply restricted_addition_semantic_implies_Unitary.
  5, 7 : apply restricted_addition_semantic_implies_Hermitian.
  7, 8 : apply restricted_addition_semantic_implies_trace_zero.
  1 - 8 : apply restricted_addition_syntactic_implies_semantic.
  all : inversion H0; inversion H1; auto.
Qed.
  
Lemma Heisenberg_Eigenvector_semantics {n} (a b : AType n) (g : prog) : 
  ((translate_prog n g) × translateA a = translateA b × (translate_prog n g)) ->
  {{ a }} g {{ b }}.
Proof. 
  intros H0 v H1.
  unfold vecSatisfiesP in *.
  unfold vecSatisfies in *.
  simpl in *.
  destruct H1.
  split.
  - auto with wf_db.
  - unfold Eigenpair in *. simpl in *.
    rewrite <- Mmult_assoc.
    rewrite <- H0.
    rewrite Mmult_assoc.
    setoid_rewrite H2.
    distribute_scale.
    reflexivity.
Qed.


(** ** generalized implication rule ** **)

Lemma generalized_implies : forall (n : nat) (a a' b b' : Predicate n) (g : prog),
    {{ a }} g {{ b }} ->
    (forall v, vecSatisfiesP v a' -> vecSatisfiesP v a) ->
    (forall v, vecSatisfiesP v b -> vecSatisfiesP v b') ->
    {{ a' }} g {{ b' }}.
Proof. intros. intro. auto. Qed.



(** ** implication rules ** **)

Reserved Infix "⇒" (at level 65, no associativity).

Inductive implies {n} : Predicate n -> Predicate n -> Prop :=
| ID_implies : forall (A : Predicate n), A ⇒ A
| CapElim : forall (La La' : list (AType n)), incl La La' -> Cap La' ⇒ Cap La
| CupIntro : forall (A B : Predicate n), (A) ⇒ (Cup A B)
| CupComm : forall (A B : Predicate n), (Cup A B) ⇒ (Cup B A)
| CupAssoc1 : forall (A B C : Predicate n), (Cup A (Cup B C)) ⇒ (Cup (Cup A B) C)
| CupAssoc2 : forall (A B C : Predicate n), (Cup (Cup A B) C) ⇒ (Cup A (Cup B C))
| PauliMultLeft : forall (Lt1 Lt2 : list (TType n)) (La1 La2 : list (AType n)),
    Forall proper_length_TType Lt1 -> Forall proper_length_TType Lt2 ->
    length Lt1 = length Lt2 -> length Lt1 <> 0%nat ->
    (exists j k : nat, (j <> k) /\ (j < length Lt1)%nat /\ (k < length Lt1)%nat /\
                  (Lt2 = (switch Lt1 
                            (gMulT (nth j Lt1 (defaultT_I n)) (nth k Lt1 (defaultT_I n))) k))) ->
    La1 = map TtoA Lt1 -> La2 = map TtoA Lt2 ->
    Cap La1 ⇒ Cap La2
| PauliMultLeft_inv : forall (Lt1 Lt2 : list (TType n)) (La1 La2 : list (AType n)),
    Forall proper_length_TType Lt1 -> Forall proper_length_TType Lt2 ->
    Forall coef_plus_minus_1 Lt1 ->
    length Lt1 = length Lt2 -> length Lt1 <> 0%nat ->
    (exists j k : nat, (j <> k) /\ (j < length Lt1)%nat /\ (k < length Lt1)%nat /\
                  (Lt2 = (switch Lt1 
                            (gMulT (nth j Lt1 (defaultT_I n)) (nth k Lt1 (defaultT_I n))) k))) ->
    La1 = map TtoA Lt1 -> La2 = map TtoA Lt2 ->
    Cap La2 ⇒ Cap La1
| AddComm : forall (A B : Predicate n), (A +' B) ⇒ (B +' A)
| AddAssoc1 : forall (A B C : Predicate n), ((A +' B) +' C) ⇒ (A +' (B +' C))
| AddAssoc2 : forall (A B C : Predicate n), (A +' (B +' C)) ⇒ ((A +' B) +' C)
| AddZeroElim : forall (A B C : Predicate n), (A +' ((C0 ·' C) *' B)) ⇒ (A) 
| SeptoCap : forall (la : list (AType n)) (Ln_LLT_Perm : (list nat) * (list (list TTypes)) * (list nat)),
    n = (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) ->
    Forall proper_length_TType (DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm))) ->
    Permutation (List.seq 0%nat n) (snd Ln_LLT_Perm) ->
    la = (map (fun t : TType (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) => 
                 TtoA (
(fst t, (collect_fun n ((to_fun gI (snd t)) ∘ (perm_inv n (to_fun 0%nat (snd Ln_LLT_Perm))))%prg))
)
)
(DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm)))
) ->
    Sep Ln_LLT_Perm ⇒ Cap la
| CaptoSep : forall (la : list (AType n)) (Ln_LLT_Perm : (list nat) * (list (list TTypes)) * (list nat)),
    n = (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) ->
    Forall proper_length_TType (DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm))) ->
    Permutation (List.seq 0%nat n) (snd Ln_LLT_Perm) ->
    la = (map (fun t : TType (fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm))) => 
                 TtoA (
(fst t, (collect_fun n ((to_fun gI (snd t)) ∘ (perm_inv n (to_fun 0%nat (snd Ln_LLT_Perm))))%prg))
)
)
(DiagonalQubits (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm)))
) ->
Cap la ⇒ Sep Ln_LLT_Perm

where "x ⇒ y" := (implies x y).




(** A ∩ B => A ∩ AB **)
Lemma PauliMultLeft_simpl : forall {n : nat} (v : Vector (2 ^ n)) (T1 T2 : TType n),
    proper_length_TType T1 -> proper_length_TType T2 ->
    vecSatisfiesP v T1 -> vecSatisfiesP v T2 -> vecSatisfiesP v (gMulT T1 T2).
Proof. intros n v T1 T2 H0 H1 H2 H3.
  simpl in *.
  unfold translateA in *. simpl in *.
  rewrite Mplus_0_l in *.
  destruct H2, H3; simpl in *.
  destruct T1. destruct T2.
  setoid_rewrite translate_gMulT.
  unfold translate in *. simpl in *.
  rewrite <- Mscale_assoc.
  rewrite <- Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  rewrite map_length.
  split; auto.
  unfold Eigenpair in *.
  simpl in *.
  rewrite Mscale_1_l in *.
  destruct H0, H1; simpl in *.
  rewrite H6 in *.
  setoid_rewrite Mmult_assoc.
  setoid_rewrite H5.
  setoid_rewrite H4.
  reflexivity.
  destruct H0, H1; simpl in *.
  subst.
  assumption.
Qed.

(** A ∩ AB => A ∩ B **)
Lemma PauliMultLeft_inv_simpl : forall {n : nat} (v : Vector (2 ^ n)) (T1 T2 : TType n),
    proper_length_TType T1 -> proper_length_TType T2 ->
    (fst T1 = C1 \/ fst T1 = Copp C1) ->
    vecSatisfiesP v T1 -> vecSatisfiesP v (gMulT T1 T2) -> vecSatisfiesP v T2.
Proof. intros n v T1 T2 H0 H1 H2 H3 H4. 
  simpl in *.
  unfold translateA in *. simpl in *.
  rewrite Mplus_0_l in *.
  destruct H3, H4.
  split; auto.
  unfold Eigenpair in *. simpl in *.
  rewrite Mscale_1_l in *.
  rewrite translate_gMulT_split in H6.
  apply @Mmult_inj_l with (i:= (2^n)%nat) (m:= translate T1) in H6.
  rewrite <- ! Mmult_assoc in H6.
  rewrite translate_mult_inv in H6.
  rewrite Mmult_1_l in H6.
  rewrite H5 in H6; easy.
  apply WF_translate.
  all : auto; destruct H0, H1; auto.
Qed.


(** *** prove that the semantics are actually implications *** **)
Lemma interpret_implies {n} (A B : Predicate n) :
  A ⇒ B -> (forall v : Vector (2 ^ n), vecSatisfiesP v A -> vecSatisfiesP v B).
Proof.
  intros H0 v H1.
  induction H0.
  - auto.
  - inversion H1. constructor; auto.
    apply (incl_Forall H0); auto.
  - constructor; auto.
  - destruct H1; [right | left]; auto.
  - destruct H1 as [H' | [H' | H']]; 
      [left; left | left; right | right]; auto.
  - destruct H1 as [[H' | H'] | H']; 
      [left | right; left | right; right]; auto.
  - subst.
    simpl in *.
    destruct H1.
    split; auto.
    rewrite Forall_map.
    rewrite Forall_map in H6.
    simpl in *.
    destruct H5 as [j [k [H5 [H7 [H8 H9]]]]].
    rewrite Forall_nth in H6.
    rewrite Forall_nth.
    intros i d H10.
    rewrite H9.
    bdestruct (i =? j)%nat.
    + subst. 
      rewrite nth_switch_miss; auto.
    + bdestruct (i =? k)%nat.
      * subst.
        rewrite nth_switch_hit; auto.
        apply PauliMultLeft_simpl; simpl;
        try apply H6; auto; apply Forall_nth; auto.
      * rewrite nth_switch_miss; auto.
        assert (length Lt2 = length Lt1).
        { rewrite H9. rewrite switch_len; auto. }
        apply H6; rewrite <- H13; auto.
  - subst.
    assert (PauliMult_listT Lt1 Lt2).
    { constructor; auto. }
    apply PauliMult_listT_swap in H7; auto.
    inversion H7.
    simpl in *.
    destruct H1.
    split; auto.
    rewrite Forall_map.
    rewrite Forall_map in H11.
    simpl in *.
    destruct H10 as [j [k [H10 [H12 [H13 H14]]]]].
    rewrite Forall_nth in H11.
    rewrite Forall_nth.
    intros i d H15.
    rewrite H14.
    bdestruct (i =? j)%nat.
    + subst. 
      rewrite nth_switch_miss; auto.
    + bdestruct (i =? k)%nat.
      * subst.
        rewrite nth_switch_hit; auto.
        apply PauliMultLeft_simpl; simpl;
        try apply H11; auto; apply Forall_nth; auto.
      * rewrite nth_switch_miss; auto.
        assert (length Lt2 = length Lt1).
        { rewrite H14. rewrite switch_len; auto. }
        apply H11; rewrite H18; auto.
  - destruct A, B; try easy.
    simpl in *.
    unfold translateA in *.
    unfold gAddA in *.
    rewrite map_app in *.
    rewrite fold_left_Mplus_app_Zero in *.
    rewrite Mplus_comm.
    assumption.
  - destruct A, B, C; try easy.
    simpl in *.
    unfold gAddA in *.
    rewrite app_assoc.
    assumption.
  - destruct A, B, C; try easy.
    simpl in *.
    unfold gAddA in *.
    rewrite <- app_assoc.
    assumption.
  - destruct A, B, C; try easy.
    simpl in *.
    unfold gAddA in *.
    unfold translateA in *.
    rewrite map_app in H1.
    rewrite fold_left_Mplus_app_Zero in H1.
    assert (fold_left Mplus (map translate (gMulA (gScaleA C0 a1) a0)) Zero = Zero).
    { clear H1. clear a.
      unfold gScaleA in *.
      unfold gScaleT in *.
      induction a1.
      - easy.
      - simpl.
        rewrite map_app.
        rewrite map_map.
        rewrite fold_left_Mplus_app_Zero.
        rewrite IHa1.
        rewrite Mplus_0_r.
        destruct a.
        rewrite Cmult_0_l.
        clear IHa1.
        induction a0.
        + easy.
        + simpl in *. rewrite fold_left_Mplus.
          rewrite IHa0.
          rewrite Mplus_0_l.
          destruct a.
          unfold translate.
          simpl.
          rewrite ! Cmult_0_l.
          rewrite Mscale_0_l.
          reflexivity. }
    rewrite H0 in H1.
    rewrite Mplus_0_r in H1.
    assumption.
  - subst.
    destruct Ln_LLT_Perm as [[Ln LLT] Perm].
    simpl in *. destruct H1; split; auto.
    rewrite Forall_forall in *.
    intros a H4.
    rewrite in_map_iff in H4.
    destruct H4 as [t [H4 H5]].
    specialize (H1 t H5).
    rewrite <- H4.
    unfold TtoA, translateA in *.
    simpl in *.
    rewrite Mplus_0_l.
    unfold translate in *. simpl in *.
    assert (map translate_P
             (collect_fun (fold_right Nat.add 0%nat Ln)
                (to_fun gI (snd t)
                 ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg) =
              (collect_fun (fold_right Nat.add 0%nat Ln)
                           (to_fun (translate_P gI) (map translate_P (snd t)) ∘
                                   perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)).
    { rewrite collect_fun_to_fun_map. auto. }
    rewrite H6. simpl.
    assert (length (map translate_P (snd t)) = (fold_right Nat.add 0%nat Ln)).
    { specialize (H2 t H5). destruct H2. rewrite map_length. auto. }
    assert ((fst t
     .* (⨂ collect_fun (fold_right Nat.add 0%nat Ln)
             (to_fun (I 2) (map translate_P (snd t))
              ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)) =
              (fst t
     .* (⨂ collect_fun (length (map translate_P (snd t)))
             (to_fun (I 2) (map translate_P (snd t))
              ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg))).
    { rewrite H7. auto. }
    setoid_rewrite H8.
    rewrite <- permute_kron_inv.
    rewrite H7.
    rewrite map_length, collect_fun_length in *.
    rewrite <- Mscale_mult_dist_l. rewrite <- Mscale_mult_dist_r.
    apply H1.
    rewrite Forall_forall. intros x H9.
    rewrite in_map_iff in H9.
    destruct H9 as [P [tPx inx]].
    rewrite <- tPx. destruct P; simpl; auto with wf_db.
    rewrite map_length in *. rewrite H7.
    apply perm_inv_permutation.
    apply Permutation_permutation_seq.
    apply Permutation_sym; auto.
  - subst.
    destruct Ln_LLT_Perm as [[Ln LLT] Perm].
    simpl in *. destruct H1; split; auto.
    rewrite Forall_forall in *.
    intros t H4.
    specialize (H2 t H4).
    unfold TtoA, translateA in *.
    specialize (H1
                  [(fst t,
               collect_fun (fold_right Nat.add 0%nat Ln)
                 (to_fun gI (snd t)
                  ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)]
               ).
    assert (In
         [(fst t,
           collect_fun (fold_right Nat.add 0%nat Ln)
             (to_fun gI (snd t)
              ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)]
         (map
            (fun t : TType (fold_right Nat.add 0%nat Ln) =>
             [(fst t,
               collect_fun (fold_right Nat.add 0%nat Ln)
                 (to_fun gI (snd t)
                  ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)])
            (DiagonalQubits Ln LLT))).
    { rewrite in_map_iff. exists t. split; auto. }
    specialize (H1 H5).
    simpl in H1.
    rewrite Mplus_0_l in H1.
    unfold translate in *. simpl in *.
    rewrite collect_fun_to_fun_map in H1.
    simpl in *.
    assert (length (map translate_P (snd t)) = (fold_right Nat.add 0%nat Ln)).
    { rewrite map_length. destruct H2. auto. }
    assert ((fst t
          .* (⨂ collect_fun (fold_right Nat.add 0%nat Ln)
                  (to_fun (I 2) (map translate_P (snd t))
                   ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg)) =
              (fst t
          .* (⨂ collect_fun (length (map translate_P (snd t)))
                  (to_fun (I 2) (map translate_P (snd t))
                   ∘ perm_inv (fold_right Nat.add 0%nat Ln) (to_fun 0%nat Perm))%prg))).
    { rewrite H6. auto. }
    setoid_rewrite H7 in H1.
    rewrite <- permute_kron_inv in H1.
    rewrite H6 in H1.
    rewrite map_length, collect_fun_length in *.
    rewrite <- Mscale_mult_dist_l in H1. rewrite <- Mscale_mult_dist_r in H1.
    apply H1.
    rewrite Forall_forall. intros x H8.
    rewrite in_map_iff in H8.
    destruct H8 as [P [tPx inx]].
    rewrite <- tPx. destruct P; simpl; auto with wf_db.
    rewrite map_length in *. rewrite H6.
    apply perm_inv_permutation.
    apply Permutation_permutation_seq.
    apply Permutation_sym; auto.
Qed.


(** ** rules ** **)

Lemma CONS : forall {n : nat} (A B : Predicate n) {A' B' : Predicate n} {g : prog},
    A' ⇒ A -> B ⇒ B' -> {{ A }} g {{ B }} -> {{ A' }} g {{ B' }}.
Proof. intros n A B A' B' g H0 H1 H2. 
  unfold triple in *.
  intros v H3.
  apply (interpret_implies B B' H1 (translate_prog n g × v)).
  apply H2.
  apply (interpret_implies A' A H0 v).
  assumption.
Qed.


(*** Normalization is admissible ***)
Lemma normalization_admissible :
  forall {n : nat} (P : Predicate n) (U : prog) (Lt : list (TType n)),
    Forall proper_length_TType Lt ->
    {{P}} U {{Cap (map TtoA Lt)}} ->
    {{P}} U {{Cap (map TtoA (normalize Lt))}}.
Proof. intros n P U Lt ForallPLT H0.
  bdestruct (length Lt =? 0)%nat.
  - rewrite length_zero_iff_nil in H1.
    subst. rewrite normalize_nil. auto.
  - destruct (normalize_PauliMult_listT_chain_Permutation n Lt H1) as [[Lt' [H2 H3]]].
    apply CONS with (A := P) (B := Cap (map TtoA Lt')).
    apply ID_implies. apply CapElim.
    apply Permutation_sym in H3.
    apply Permutation_incl in H3. 
    apply incl_map. auto.
    clear H1 H3.
    induction H2; subst; auto. 
    + inversion H1.
      apply CONS with (A := P) (B := Cap (map TtoA Lt1)); auto.
      apply ID_implies.
      apply PauliMultLeft with (Lt1 := Lt1) (Lt2 := Lt2); auto.
      apply PauliMult_listT_preserves_proper_length_TType with (Lt1 := Lt1); auto.
    + apply IHPauliMult_listT_chain2.
      apply PauliMult_listT_chain_preserves_proper_length_TType with (Lt1 := Lt1); auto.
      apply IHPauliMult_listT_chain1; auto.
Qed.

Lemma normalization_admissible' :
  forall {n : nat} (P : Predicate n) (U : prog) (Lt : list (TType n)),
    Forall WF_TType Lt ->
    {{P}} U {{Cap (map TtoA Lt)}} ->
    {{P}} U {{Cap (map TtoA (normalize Lt))}}.
Proof. intros n P U Lt H0 H1.
  apply normalization_admissible; auto.
  apply Forall_impl with (P := WF_TType); auto.
  intros a H2.
  inversion H2; auto.
Qed.


Local Open Scope nat_scope.


Lemma SEQ : forall {n} {A : Predicate n} (B : Predicate n) {C : Predicate n} {g1 g2 : prog},
    {{ A }} g1 {{ B }} -> {{ B }} g2 {{ C }} ->  {{ A }} g1 ;; g2 {{ C }}.
Proof.
  intros n A B C g1 g2 H0 H1.
  unfold triple in *.
  intros v H2.
  specialize (H0 v).
  specialize (H1 (translate_prog n g1 × v)).
  apply H0 in H2.
  apply H1 in H2.
  simpl.
  rewrite Mmult_assoc.
  assumption.
Qed.



Lemma CAP : forall {n : nat} {La La' : list (AType n)} {g : prog},
    length La = length La' ->
    Forall (fun p : (AType n)*(AType n) => {{ fst p }} g {{ snd p }}) (combine La La') ->
    {{ Cap La }} g {{ Cap La' }}.
Proof. intros n La La' g H0 H1.
  unfold triple in *.
  intros v H2.
  destruct H2.
  gen La'. induction H3; intros.
  - simpl in *.
    split; auto with wf_db.
    symmetry in H0.
    rewrite length_zero_iff_nil in H0.
    subst; auto.
  - destruct La'. 
    + simpl; split; auto with wf_db.
    + simpl in *. 
      split; auto with wf_db.
      inversion H4; subst; clear H4.
      simpl in *. constructor. 
      * apply H7; auto. 
      * apply IHForall; auto.
Qed.

Lemma CAP' : forall {n : nat} {La La' : list (AType n)} {g : prog},
    Forall2 (fun a b : AType n => {{ a }} g {{ b }}) La La' ->
    {{ Cap La }} g {{ Cap La' }}.
Proof. intros n La La' g H0.
  apply CAP.
  apply Forall2_length in H0; auto.
  induction H0; auto.
  simpl.
  rewrite Forall_cons_iff.
  simpl; split; auto.
Qed.

Lemma CUP : forall {n : nat} {A A' B B' : Predicate n} {g : prog},
    {{ A }} g {{ A' }} -> {{ B }} g {{ B' }} -> {{ A ⊍ B }} g {{ A' ⊍ B' }}.
Proof. intros n A A' B B' g H0 H1.
  unfold triple in *.
  intros v H2.
  destruct H2.
  - specialize (H0 v H2).
    simpl. left. auto.
  - specialize (H1 v H2).
    simpl. right. auto.
Qed.


(** The SCALE, MUL, ADD rules can be replaced by the POLY / LINCOMB rule **)
Lemma SCALE : forall {n : nat} (c : Coef) (a a' : AType n) (g : prog),
    WF_AType a -> WF_AType a' ->
    {{ AtoPred a }} g {{ AtoPred a' }} -> {{ scale c (AtoPred a) }} g {{ scale c (AtoPred a') }}.
Proof. intros n c a a' g H0 H1 H2.
  apply Heisenberg_Eigenvector_semantics.
  pose (WF_AType_implies_proper_length_AType a H0).
  pose (WF_AType_implies_proper_length_AType a' H1).
  rewrite (translateA_gScaleA c a p).
  rewrite (translateA_gScaleA c a' p0).
  distribute_scale.
  f_equal.
  inversion H0. inversion H1. subst.
  apply Eigenvector_Heisenberg_semantics in H2;
    try apply proper_length_AType_implies_proper_length_AType_nil;
    try apply restricted_addition_semantic_implies_Unitary;
    try apply restricted_addition_semantic_implies_Hermitian;
    try apply restricted_addition_semantic_implies_trace_zero;
    try apply restricted_addition_syntactic_implies_semantic;
    try apply restricted_addition_syntactic_implies_proper_length_AType;
    auto.
Qed.

Lemma SCALE' : forall {n : nat} (c : Coef) (a a' : AType n) {a0 a0' : AType n} {g : prog},
    WF_AType a -> WF_AType a' -> a0 = gScaleA c a -> a0' = gScaleA c a' ->
    {{ AtoPred a }} g {{ AtoPred a' }} -> {{ AtoPred a0 }} g {{ AtoPred a0' }}.
Proof. intros n c a a' a0 a0' g H0 H1 H2 H3 H4.
  subst. apply SCALE; auto.
Qed.

Lemma UNFLIP : forall {n : nat} (a a' : AType n) {a0 a0' : AType n} {g : prog},
    WF_AType a -> WF_AType a' -> a0 = gScaleA (- C1)%C a -> a0' = gScaleA (- C1)%C a' -> {{ AtoPred a }} g {{ AtoPred a' }} -> {{ AtoPred a0 }} g {{ AtoPred a0' }}.
Proof. intros n c a a' a0 a0' g H0 H1 H2 H3 H4.
  subst. apply SCALE; auto.
Qed.

Lemma FLIP : forall {n : nat} (a a' : AType n) {a0 a0' : AType n} {g : prog},
    WF_AType a -> WF_AType a' -> a = gScaleA (- C1)%C a0 -> a' = gScaleA (- C1)%C a0' -> {{ AtoPred a }} g {{ AtoPred a' }} -> {{ AtoPred a0 }} g {{ AtoPred a0' }}.
Proof. intros n a a' a0 a0' g H0 H1 H2 H3 H4.
  subst. eapply UNFLIP. Unshelve. 
  6 : apply (gScaleA (- C1)%C a0). 6 : apply (gScaleA (- C1)%C a0').
  all : auto.
  - unfold gScaleA. rewrite map_map.
    assert ((fun x : TType n => gScaleT (- C1)%C (gScaleT (- C1)%C x)) = fun x => x).
    + apply functional_extensionality. intros x.
      rewrite gScaleT_merge. replace (- C1 * - C1)%C with C1 by lca.
      rewrite gScaleT_1. auto.
    + rewrite H2. rewrite map_id. auto.
  - unfold gScaleA. rewrite map_map.
    assert ((fun x : TType n => gScaleT (- C1)%C (gScaleT (- C1)%C x)) = fun x => x).
    + apply functional_extensionality. intros x.
      rewrite gScaleT_merge. replace (- C1 * - C1)%C with C1 by lca.
      rewrite gScaleT_1. auto.
    + rewrite H2. rewrite map_id. auto.
Qed.

Lemma MUL : forall {n : nat} (a b a' b' : AType n) (g : prog),
    WF_AType a -> WF_AType a' -> WF_AType b -> WF_AType b' ->
    {{ AtoPred a }} g {{ AtoPred b }} -> {{ AtoPred a' }} g {{ AtoPred b' }} -> {{ mul (AtoPred a) (AtoPred a') }} g {{ mul (AtoPred b) (AtoPred b') }}.
Proof. intros n a b a' b' g H0 H1 H2 H3 H4 H5. 
  apply Heisenberg_Eigenvector_semantics.
  inversion H0. inversion H1. inversion H2. inversion H3. subst.
  repeat (rewrite translateA_Mmult;
          try apply restricted_addition_syntactic_implies_proper_length_AType;
          auto).
  apply Eigenvector_Heisenberg_semantics in H4;
    try apply proper_length_AType_implies_proper_length_AType_nil;
    try apply restricted_addition_semantic_implies_Unitary;
    try apply restricted_addition_semantic_implies_Hermitian;
    try apply restricted_addition_semantic_implies_trace_zero;
    try apply restricted_addition_syntactic_implies_semantic;
    try apply restricted_addition_syntactic_implies_proper_length_AType;
    auto.
  apply Eigenvector_Heisenberg_semantics in H5;
    try apply proper_length_AType_implies_proper_length_AType_nil;
    try apply restricted_addition_semantic_implies_Unitary;
    try apply restricted_addition_semantic_implies_Hermitian;
    try apply restricted_addition_semantic_implies_trace_zero;
    try apply restricted_addition_syntactic_implies_semantic;
    try apply restricted_addition_syntactic_implies_proper_length_AType;
    auto.
  rewrite <- Mmult_assoc, H4, Mmult_assoc, H5, Mmult_assoc; auto.
Qed.

Lemma MUL' : forall {n : nat} (a b a' b' : AType n) {a0 b0 : AType n} {g : prog},
    WF_AType a -> WF_AType a' -> WF_AType b -> WF_AType b' ->
    a0 = gMulA a a' -> b0 = gMulA b b' ->
    {{ AtoPred a }} g {{ AtoPred b }} -> {{ AtoPred a' }} g {{ AtoPred b' }} ->
    {{ AtoPred a0 }} g {{ AtoPred b0 }}.
Proof. intros n a b a' b' a0 b0 g H0 H1 H2 H3 H4 H5 H6 H7.
  subst. apply MUL; auto.
Qed.

Lemma MUL_T_anticomm : forall {n : nat} (t0 t1 t2 t3 : TType n) {t t' : TType n} {g : prog},
    anticommute_TType t0 t2 -> WF_TType t0 -> WF_TType t2 ->
    anticommute_TType t1 t3 -> WF_TType t1 -> WF_TType t3 ->
    t = (gScaleT Ci (gMulT t0 t2)) -> t' = (gScaleT Ci (gMulT t1 t3)) ->
    {{ AtoPred [t0] }} g {{ AtoPred [t1] }} -> {{ AtoPred [t2] }} g {{ AtoPred [t3] }} ->
    {{ AtoPred [t] }} g {{ AtoPred [t'] }}.
Proof. intros n t0 t1 t2 t3 t t' g H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
  subst.
  replace ([gScaleT Ci (gMulT t0 t2)])
    with (gScaleA Ci (gMulA [t0] [t2]))
    by auto.
  replace ([gScaleT Ci (gMulT t1 t3)])
    with (gScaleA Ci (gMulA [t1] [t3]))
    by auto.
  apply Heisenberg_Eigenvector_semantics.
  rewrite ! translateA_gScaleA.
  rewrite ! translateA_Mmult.
  apply Eigenvector_Heisenberg_semantics' in H8, H9.
  distribute_scale.
  f_equal.
  rewrite <- Mmult_assoc.
  rewrite H8.
  rewrite Mmult_assoc.
  rewrite H9.
  rewrite Mmult_assoc.
  easy.
  all : constructor;
  repeat match goal with
         | |- restricted_addition_syntactic _ => constructor; auto
         | |- proper_length_TType (gMulT _ _) => apply proper_length_TType_gMulT
         | [H' : WF_TType _ |- proper_length_TType _] => inversion H'; subst; clear H'; auto
         end.
Qed.
  
Lemma WF_MUL_T_anticomm : forall {n : nat} (t t' : TType n) {t0 : TType n},
    anticommute_TType t t' -> WF_TType t -> WF_TType t' ->
    t0 = (gScaleT Ci (gMulT t t')) -> WF_AType [t0].
Proof. intros n t t' t0 H0 H1 H2 H3.
  do 2 constructor. subst. apply WF_TType_mul_anticommute; auto.
Qed.

Lemma MUL_T_comm : forall {n : nat} (t0 t1 t2 t3 : TType n) {t t' : TType n} {g : prog},
    commute_TType t0 t2 -> snd t0 <> snd t2 -> WF_TType t0 -> WF_TType t2 ->
    commute_TType t1 t3 -> snd t1 <> snd t3 -> WF_TType t1 -> WF_TType t3 ->
    t = (gMulT t0 t2) -> t' = (gMulT t1 t3) ->
    {{ AtoPred [t0] }} g {{ AtoPred [t1] }} -> {{ AtoPred [t2] }} g {{ AtoPred [t3] }} ->
    {{ AtoPred [t] }} g {{ AtoPred [t'] }}.
Proof. intros n t0 t1 t2 t3 t t' g H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. 
  subst.
  replace ([gMulT t0 t2])
    with (gMulA [t0] [t2])
    by auto.
  replace ([gMulT t1 t3])
    with (gMulA [t1] [t3])
    by auto.
  apply Heisenberg_Eigenvector_semantics.
  rewrite ! translateA_Mmult.
  apply Eigenvector_Heisenberg_semantics' in H10, H11.
  rewrite <- Mmult_assoc.
  rewrite H10.
  rewrite Mmult_assoc.
  rewrite H11.
  rewrite Mmult_assoc.
  easy.
  all : constructor;
  repeat match goal with
         | |- restricted_addition_syntactic _ => constructor; auto
         | |- proper_length_TType (gMulT _ _) => apply proper_length_TType_gMulT
         | [H' : WF_TType _ |- proper_length_TType _] => inversion H'; subst; clear H'; auto
         end.
Qed.
    
Lemma WF_MUL_T_comm : forall {n : nat} (t t' : TType n) {t0 : TType n},
    commute_TType t t' -> snd t <> snd t' -> WF_TType t -> WF_TType t' ->
    t0 = (gMulT t t') -> WF_AType [t0].
Proof. intros n t t' t0 H0 H1 H2 H3 H4.
  do 2 constructor. subst. apply WF_TType_mul_commute'; auto.
Qed.

Lemma ADD : forall {n : nat} (a a' b b' : AType n) (g : prog),
    WF_AType a -> WF_AType a' -> WF_AType b -> WF_AType b' ->
    {{ AtoPred a }} g {{ AtoPred b }} -> {{ AtoPred a' }} g {{ AtoPred b' }} -> {{ add (AtoPred a) (AtoPred a') }} g {{ add (AtoPred b) (AtoPred b') }}.
Proof. intros n a b a' b' g H0 H1 H2 H3 H4 H5. 
  apply Heisenberg_Eigenvector_semantics.
  inversion H0. inversion H1. inversion H2. inversion H3. subst.
  repeat (rewrite translateA_Add;
          try apply restricted_addition_syntactic_implies_proper_length_AType;
          auto).
  apply Eigenvector_Heisenberg_semantics in H4;
    try apply proper_length_AType_implies_proper_length_AType_nil;
    try apply restricted_addition_semantic_implies_Unitary;
    try apply restricted_addition_semantic_implies_Hermitian;
    try apply restricted_addition_semantic_implies_trace_zero;
    try apply restricted_addition_syntactic_implies_semantic;
    try apply restricted_addition_syntactic_implies_proper_length_AType;
    auto.
  apply Eigenvector_Heisenberg_semantics in H5;
    try apply proper_length_AType_implies_proper_length_AType_nil;
    try apply restricted_addition_semantic_implies_Unitary;
    try apply restricted_addition_semantic_implies_Hermitian;
    try apply restricted_addition_semantic_implies_trace_zero;
    try apply restricted_addition_syntactic_implies_semantic;
    try apply restricted_addition_syntactic_implies_proper_length_AType;
    auto.
  rewrite Mmult_plus_distr_l, Mmult_plus_distr_r, H4, H5; auto.
Qed.

Lemma ADD' : forall {n : nat} (a a' b b' : AType n) {a0 b0 : AType n} {g : prog},
    WF_AType a -> WF_AType a' -> WF_AType b -> WF_AType b' ->
    a0 = gAddA a a' -> b0 = gAddA b b' ->
    {{ AtoPred a }} g {{ AtoPred b }} -> {{ AtoPred a' }} g {{ AtoPred b' }} -> {{ AtoPred a0 }} g {{ AtoPred b0 }}.
Proof. intros n a a' b b' a0 b0 g H0 H1 H2 H3 H4 H5 H6 H7.
  subst. apply ADD; auto.
  Qed.




Definition HoareTriple (n : nat) :=
  { t : AType n * prog * AType n | (uncurry (uncurry (fun A g B => @triple n (AtoPred A) g (AtoPred B)))) t}.
Definition packHT {n : nat} 
  (pr : AType n) (g : prog) (po : AType n) (pf : @triple n (AtoPred pr) g (AtoPred po)) : HoareTriple n :=
    (exist (uncurry (uncurry (fun A g B => @triple n (AtoPred A) g (AtoPred B)))) (pr, g, po) pf).
Definition precond {n : nat} (ht : HoareTriple n) : AType n := fst (fst (proj1_sig ht)).
Definition circuit {n : nat} (ht : HoareTriple n) : prog := snd (fst (proj1_sig ht)).
Definition postcond {n : nat} (ht : HoareTriple n) : AType n := snd (proj1_sig ht).
Definition validation {n : nat} (ht : HoareTriple n) := proj2_sig ht.

Lemma precond_packHT : 
  forall {n : nat} (pr : AType n) (g : prog) (po : AType n) (pf : @triple n (AtoPred pr) g (AtoPred po)),
    precond (packHT pr g po pf) = pr.
Proof. intros n pr g po pf. auto. Qed.

Lemma circuit_packHT : 
  forall {n : nat} (pr : AType n) (g : prog) (po : AType n) (pf : @triple n (AtoPred pr) g (AtoPred po)),
    circuit (packHT pr g po pf) = g.
Proof. intros n pr g po pf. auto. Qed.

Lemma postcond_packHT : 
  forall {n : nat} (pr : AType n) (g : prog) (po : AType n) (pf : @triple n (AtoPred pr) g (AtoPred po)),
    postcond (packHT pr g po pf) = po.
Proof. intros n pr g po pf. auto. Qed.

Lemma validation_packHT : 
  forall {n : nat} (pr : AType n) (g : prog) (po : AType n) (pf : @triple n (AtoPred pr) g (AtoPred po)),
    validation (packHT pr g po pf) = pf.
Proof. intros n pr g po pf. auto. Qed.

Definition lincombCA {n : nat} (Lc : list C) (La : list (AType n)) : AType n :=
  fold_right (@app (TType n)) [] (zipWith gScaleA Lc La).

Lemma lincombCA_cons : forall {n : nat} (Lc : list C) (La : list (AType n)) (c : C) (a : AType n),
    lincombCA (c :: Lc) (a :: La) = (gScaleA c a) ++ lincombCA Lc La.
Proof. intros n Lc La c a.
    unfold lincombCA.
    rewrite ! zipWith_cons.
    rewrite cons_conc.
    rewrite ! fold_right_app.
    simpl. easy.
Qed.

Lemma LINCOMB :
  forall {n : nat} (g : prog) (Lc : list C) (Lht : list (HoareTriple n)),
    length Lc = length Lht -> Lht <> [] -> Forall (fun ht => WF_AType (precond ht)) Lht ->
    Forall (fun ht => WF_AType (postcond ht)) Lht -> Forall (fun ht => circuit ht = g) Lht ->
    {{ AtoPred (lincombCA Lc (map precond Lht)) }} g {{ AtoPred (lincombCA Lc (map postcond Lht)) }}.
Proof. intros n g Lc Lht H0 H1 H2 H3 H4.
  apply Heisenberg_Eigenvector_semantics.
  gen Lc.
  induction Lht; intros; try contradiction.
  destruct Lc; try discriminate.
  destruct (Nat.eq_dec (length Lht) 0%nat) as [E | E].
  - clear IHLht.
    rewrite length_zero_iff_nil in E.
    subst.
    simpl in H0.
    inversion H0.
    rewrite length_zero_iff_nil in H6.
    subst.
    clear H0. clear H1.
    inversion H4; subst; clear H4.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.
    clear H5. clear H6. clear H7.
    unfold lincombCA, precond, postcond, circuit in *.
    unfold "`" in *.
    destruct a as [[[pr pg] po] pf].
    simpl in *.
    rewrite ! app_nil_r.
    unfold uncurry in *; simpl in *.
    apply Eigenvector_Heisenberg_semantics' in pf; auto.
    apply WF_AType_implies_proper_length_AType in H3, H4.
    rewrite ! translateA_gScaleA; auto.
    distribute_scale.
    f_equal.
    apply pf.
  - pose (length_zero_iff_nil Lht) as E'.
    apply not_iff_compat in E'.
    rewrite E' in E.
    simpl in *.
    rewrite ! lincombCA_cons.
    rewrite ! translateA_app.
    rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
    inversion H0; clear H0.
    assert (Forall (fun ht : HoareTriple n => WF_AType (precond ht)) Lht)
      by (inversion H2; subst; auto).
    assert (Forall (fun ht : HoareTriple n => WF_AType (postcond ht)) Lht)
      by (inversion H3; subst; auto).
    assert (Forall (fun ht : HoareTriple n => circuit ht = g) Lht)
      by (inversion H4; subst; auto).
    specialize (IHLht E H0 H5 H7 Lc H6).
    rewrite IHLht.
    f_equal.
    assert (WF_AType (precond a))
      by (inversion H2; subst; auto).
    assert (WF_AType (postcond a))
      by (inversion H3; subst; auto).
    assert (circuit a = g)
      by (inversion H4; subst; auto).
    clear H1. clear H2. clear H3. clear H4.
    destruct a as [[[pr pg] po] pf].
    unfold precond, postcond, circuit, uncurry in *.
    simpl in *.
    apply Eigenvector_Heisenberg_semantics' in pf; auto.
    apply WF_AType_implies_proper_length_AType in H8, H9.
    rewrite ! translateA_gScaleA; auto.
    distribute_scale.
    f_equal.
    subst.
    apply pf.
Qed.

Lemma LINCOMB' :
  forall {n : nat} {g : prog} {pr po : AType n} (Lc : list C) (Lpr Lpo : list (AType n))
     (Lht : list (HoareTriple n)),
    length Lc = length Lpr -> length Lpr = length Lpo -> Lc <> [] -> 
    Forall WF_AType Lpr -> Forall WF_AType Lpo -> Forall (fun ht => circuit ht = g) Lht ->
    map precond Lht = Lpr -> map postcond Lht = Lpo ->
    pr = lincombCA Lc Lpr -> po = lincombCA Lc Lpo ->
    {{ AtoPred pr }} g {{ AtoPred po }}.
Proof. intros n g pr po Lc Lpr Lpo Lht H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  subst. apply LINCOMB; rewrite ! map_length in *; auto.
  - intro; subst; simpl in *. rewrite length_zero_iff_nil in H0; auto.
  - rewrite <- Forall_map; auto.
  - rewrite <- Forall_map; auto.
Qed.


Lemma prog_simpl_inc_reduce : forall (p : nat -> prog) (prg_len bit : nat),
  simpl_prog p -> bit < prg_len ->
  translate_prog prg_len (p bit) = 
  (Matrix.I (2^bit)) ⊗ translate_prog 1 (p 0) ⊗ (Matrix.I (2^(prg_len - bit - 1))).
Proof. intros p prg_len bit H0 H1. 
       destruct H0; [ | destruct H0];
         do 2 (rewrite H0); 
         simpl;
         unfold prog_simpl_app;
         bdestruct_all;
         rewrite Nat.sub_0_r, Nat.sub_diag, 
                 Nat.pow_0_r, kron_1_l, kron_1_r; auto with wf_db.
Qed.


Lemma prog_ctrl_reduce : forall (prg_len ctrl targ : nat),
  translate_prog (s prg_len) (CNOT (s ctrl) (s targ)) = 
  (Matrix.I 2) ⊗ translate_prog prg_len (CNOT ctrl targ).
Proof. intros.    
       unfold translate_prog, prog_ctrl_app.
       bdestruct_all; simpl.
       all : try (rewrite id_kron, Nat.add_0_r, double_mult; easy).
       - replace (2 ^ ctrl + (2 ^ ctrl + 0)) with (2 * 2^ctrl) by lia. 
         rewrite <- id_kron.
         repeat rewrite kron_assoc; auto with wf_db.  
         repeat rewrite Nat.add_0_r. repeat rewrite double_mult.
         replace 2 with (2^1) by easy. 
         repeat rewrite <- Nat.pow_add_r. 
         replace (ctrl + ((1 + (targ - ctrl)) + (prg_len - targ - 1))) with prg_len by lia; 
         easy. 
       - replace (2 ^ targ + (2 ^ targ + 0)) with (2 * 2^targ) by lia. 
         rewrite <- id_kron.
         repeat rewrite kron_assoc; auto with wf_db.  
         repeat rewrite Nat.add_0_r. repeat rewrite double_mult.
         replace 2 with (2^1) by easy. 
         repeat rewrite <- Nat.pow_add_r. 
         replace (targ + (((ctrl - targ) + 1) + (prg_len - ctrl - 1))) with prg_len by lia;
         easy. 
Qed.

Lemma prog_ctrl_reduce' : forall (prg_len ctrl targ : nat),
    prog_ctrl_app (s prg_len) σx (s ctrl) (s targ) =
      (Matrix.I 2) ⊗ prog_ctrl_app prg_len σx ctrl targ.
Proof. intros prg_len ctrl targ.
  pose (prog_ctrl_reduce prg_len ctrl targ) as H0.
  unfold translate_prog in H0; auto.
Qed.


Lemma TEN1 : forall (bit : nat) (pm c : Coef) (l : list Pauli) (A : Pauli) (U : nat -> prog),
    bit < length l -> simpl_prog U -> not_gI (nth bit l gI) -> not_gI A ->
    pm = C1 \/ pm = (- C1)%C ->
    @triple 1 ( AtoPred [ (C1, [nth bit l gI]) ] ) (U 0) ( AtoPred [ (pm, [A]) ] ) ->
    @triple (length l) ( AtoPred [(c, l)] ) (U bit) ( AtoPred [((c * pm)%C, switch l A bit)] ).
Proof. intros bit pm c l A U i_lessthan_n simpl_prog_U notgInth notgIA pm_1 H0.
  apply Heisenberg_Eigenvector_semantics.
  apply Eigenvector_Heisenberg_semantics in H0.

  unfold translateA. simpl. rewrite ! Mplus_0_l.
  unfold translateA in H0. simpl in H0. rewrite ! Mplus_0_l in H0.
  unfold translate in H0. simpl in H0. rewrite ! kron_1_r in H0.
  rewrite ! Mscale_1_l in H0.
  rewrite prog_simpl_inc_reduce. unfold translate. simpl.
  rewrite ! map_length, ! switch_map, ! switch_len.
  rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
  rewrite <- Mscale_assoc. apply Mscale_inj.
  
  rewrite (switch_inc bit (map translate_P l) (translate_P A)).
  replace (big_kron (map translate_P l))
    with (big_kron (map translate_P (firstn bit l ++ [nth bit l gI] ++ skipn (s bit) l)))
    by (rewrite <- (nth_inc bit l gI); try rewrite length_l_is_n; auto).
  
  rewrite ! map_app, firstn_map, skipn_map.
  replace (map translate_P [nth bit l gI]) with ([translate_P (nth bit l gI)]) by auto.
  rewrite ! big_kron_split.
  setoid_rewrite <- kron_assoc.

  rewrite ! map_length, ! firstn_length.
  replace (Init.Nat.min bit (length l)) with bit by lia.
  
  repeat setoid_rewrite kron_mixed_product'.

  setoid_rewrite <- Mscale_kron_dist_l.
  setoid_rewrite <- Mscale_kron_dist_r.

  all : intros; auto with wf_db unit_db.
 
  f_equal.

  all : try setoid_rewrite map_length; try setoid_rewrite firstn_length; try setoid_rewrite skipn_length.

  all : replace ((length l) - bit - 1) with ((length l) - s bit) by lia; auto.

  f_equal.

  rewrite Mmult_1_l, Mmult_1_r; auto with wf_db.

  1-2 :pose (WF_Matrix_Big_Pauli (firstn bit l)) as w;
  rewrite ! map_length, ! firstn_length in w;
  replace (Init.Nat.min bit (length l)) with bit in w by lia;
  apply w.

  simpl. setoid_rewrite kron_1_r. rewrite <- Mscale_mult_dist_l. assumption.

  setoid_rewrite Mmult_1_l. setoid_rewrite <- Mmult_1_r at 1.
  rewrite map_length, skipn_length.
  f_equal.

  all : try setoid_rewrite map_length; try setoid_rewrite skipn_length; auto with wf_db.

  1-2 :pose (WF_Matrix_Big_Pauli (skipn (s bit) l)) as w;
  rewrite ! map_length, ! skipn_length in w;
  replace (Init.Nat.min bit (length l)) with bit in w by lia.
  replace (((fix length (l : list (Square 2)) : nat := match l with
                                                   | [] => 0
                                                   | _ :: l' => s (length l')
                                                   end)
          (@map Pauli (Square 2) translate_P (@skipn Pauli (s bit) l))))
    with ((length l) - s bit)
    by (setoid_rewrite map_length; rewrite skipn_length; auto).
  apply w.

  all : replace ((fix pow (n m : nat) {struct m} : nat := match m with
                                           | 0 => 1
                                           | s m0 => n * pow n m0
                                           end) 2 ((length l) - s bit))
    with (2 ^ ((length l) - s bit))
    by (unfold pow; auto).
  
  1-3 : setoid_rewrite <- Nat.pow_1_r at 13;
    rewrite <- ! Nat.pow_add_r;
  replace (bit + 1 + ((length l) - s bit)) with (length l) by lia;
  auto.

                                                                 1-2 : simpl; auto with wf_db.
  
  all : try (inversion H1;
             [rewrite <- H2; auto with wf_db | inversion H2]);
    try (rewrite in_map_iff in H1;
         destruct H1 as [x [H1 H2]];
         rewrite <- H1;
         auto with wf_db);
    try (rewrite in_app_iff in H1;
         destruct H1;
         [inversion H1;
          [rewrite <- H2; auto with wf_db | inversion H2] | rewrite in_map_iff in H1;
                                                           destruct H1 as [x [H1 H2]];
                                                           rewrite <- H1;
                                                           auto with wf_db]).
  
  all : try (repeat constructor; intro; lia).
  
  4-6 : destruct pm_1 as [pm_1 | pm_1]; try rewrite ! pm_1.

  all : unfold translateA; simpl; try rewrite Mplus_0_l;
  unfold translate; simpl; try rewrite Mscale_1_l;
  try rewrite kron_1_r; 
  try apply scale_unitary; try lca;
  auto with unit_db.

  1,3-4 : try (rewrite Mscale_adj; f_equal);
  destruct (nth bit l gI); destruct A; simpl;
  try apply I_hermitian; try apply σx_hermitian;
  try apply σy_hermitian; try apply σz_hermitian;
  try lca.

  1 : unfold not_gI in notgInth;
    destruct notgInth as [H1 | [H1 | H1]];
    rewrite H1; unfold trace; simpl; try lca.
  
  all : unfold not_gI in notgIA;
  destruct notgIA as [H1 | [H1 | H1]];
    rewrite H1; unfold trace; simpl; lca.
Qed.

Lemma TEN1' : forall {bit len : nat} (pm : Coef) {c c' : Coef} {l l' : list Pauli} (A A' : Pauli) {U : nat -> prog},
    bit < len -> simpl_prog U -> not_gI A' -> not_gI A -> pm = C1 \/ pm = (- C1)%C ->
    @triple 1 ( AtoPred [ (C1, [A]) ] ) (U 0) ( AtoPred [ (pm, [A']) ] ) ->
    len = length l -> A = nth bit l gI -> l' = switch l A' bit -> c' = (pm * c)%C ->
    @triple len ( AtoPred [(c, l)] ) (U bit) ( AtoPred [(c', l')] ).
Proof. intros bit len pm c c' l l' A A' U H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
  rewrite Cmult_comm in H9.
  subst. apply TEN1; auto.
Qed.

Lemma WF_TEN1 : forall (bit len : nat) (c : Coef) (l : list Pauli),
    bit < len -> not_gI (nth bit l gI) -> len = length l -> c = C1 \/ c = (- C1)%C ->
    @WF_TType len (c, l).
Proof. intros bit len c l H0 H1 H2 H3.
  subst. constructor; simpl; auto.
  - constructor; simpl; auto; lia.
  - destruct H1 as [H' | [H' | H']];
      rewrite nth_inc with (ls := l) (x := gI) (n := bit); auto;
      apply trace_zero_syntax_R;
      apply trace_zero_syntax_L;
      rewrite H'; constructor.
Qed.
  
Lemma WF_TEN2 : forall (bit len : nat) (c : Coef) (l : list Pauli) (A : Pauli),
    bit < len -> not_gI A -> len = length l -> c = C1 \/ c = (- C1)%C ->
    @WF_TType len (c%C, switch l A bit).
Proof. intros bit len c l A H0 H1 H2 H3.
  subst. constructor; simpl; auto.
  - constructor; simpl; try lia.
    rewrite switch_len; auto.
  - destruct H1 as [H' | [H' | H']];
      rewrite switch_inc with (ls := l) (x := A) (n := bit); auto;
      apply trace_zero_syntax_R;
      apply trace_zero_syntax_L;
      rewrite H'; constructor.
Qed.

Lemma TEN_ID : forall (bit : nat) (c : Coef) (l : list Pauli) (U : nat -> prog),
    bit < length l -> simpl_prog U -> nth bit l gI = gI ->
    @triple (length l) ( AtoPred [(c, l)] ) (U bit) ( AtoPred [(c, l)] ).
Proof. intros bit c l U H0 H1 H2.
  apply Heisenberg_Eigenvector_semantics.
  unfold translateA. simpl. rewrite ! Mplus_0_l.

  rewrite prog_simpl_inc_reduce. unfold translate. simpl.
  rewrite ! map_length.
  rewrite Mscale_mult_dist_r, Mscale_mult_dist_l.
  apply Mscale_inj.

  replace (big_kron (map translate_P l))
    with (big_kron (map translate_P (firstn bit l ++ [nth bit l gI] ++ skipn (s bit) l)))
    by (rewrite <- (nth_inc bit l gI); try rewrite length_l_is_n; auto).
  rewrite ! H2.
  
  rewrite ! map_app.
  replace (map translate_P [gI]) with ([translate_P gI]) by auto.
  rewrite ! big_kron_split.
  setoid_rewrite <- kron_assoc.

  rewrite ! map_length, ! firstn_length.
  replace (Init.Nat.min bit (length l)) with bit by lia.
  
  repeat setoid_rewrite kron_mixed_product'.

  all : intros; auto with wf_db unit_db.
 
  f_equal.

  all : try setoid_rewrite map_length; try setoid_rewrite firstn_length; try setoid_rewrite skipn_length.

  all : replace ((length l) - bit - 1) with ((length l) - s bit) by lia; auto.

  f_equal.

  rewrite Mmult_1_l, Mmult_1_r; auto with wf_db.

  1-2 :pose (WF_Matrix_Big_Pauli (firstn bit l)) as w;
  rewrite ! map_length, ! firstn_length in w;
  replace (Init.Nat.min bit (length l)) with bit in w by lia;
  apply w.

  simpl. setoid_rewrite kron_1_r. rewrite Mmult_1_l. rewrite Mmult_1_r. reflexivity.

  1 - 2 : replace 2%nat with (2 ^ 1)%nat by (simpl; lia);
  apply WF_Matrix_translate_prog.

  setoid_rewrite Mmult_1_l. setoid_rewrite <- Mmult_1_r at 1.
  rewrite map_length, skipn_length.
  f_equal.

  all : try setoid_rewrite map_length; try setoid_rewrite skipn_length; auto with wf_db.

  pose (WF_Matrix_Big_Pauli (skipn (s bit) l)) as w;
  rewrite ! map_length, ! skipn_length in w;
  replace (Init.Nat.min bit (length l)) with bit in w by lia.
  replace (((fix length (l : list (Square 2)) : nat := match l with
                                                   | [] => 0
                                                   | _ :: l' => s (length l')
                                                   end)
          (@map Pauli (Square 2) translate_P (@skipn Pauli (s bit) l))))
    with ((length l) - s bit)
    by (setoid_rewrite map_length; rewrite skipn_length; auto).
  apply w.

  all : replace ((fix pow (n m : nat) {struct m} : nat := match m with
                                           | 0 => 1
                                           | s m0 => n * pow n m0
                                           end) 2 ((length l) - s bit))
    with (2 ^ ((length l) - s bit))
    by (unfold pow; auto).
  
  1-3 : setoid_rewrite <- Nat.pow_1_r at 13;
    rewrite <- ! Nat.pow_add_r;
  replace (bit + 1 + ((length l) - s bit)) with (length l) by lia;
  auto.

  all : simpl; auto with wf_db.
  all : try (inversion H3; try inversion H4; subst; clear H3; auto with wf_db).
  all : try (rewrite in_map_iff in H3;
             destruct H3 as [x [H' H'']];
             subst; auto with wf_db).
  all : rewrite app_nil_l in H4;
    rewrite in_map_iff in H4;
    destruct H4 as [x [H' H'']];
    subst; auto with wf_db.
Qed.

Lemma TEN_ID' : forall {bit len : nat} {c c' : Coef} {l l' : list Pauli} {U : nat -> prog},
    bit < len -> len = length l -> simpl_prog U -> nth bit l gI = gI -> l = l' -> c = c' ->
    @triple (len) ( AtoPred [(c, l)] ) (U bit) ( AtoPred [(c', l')] ).
Proof. intros bit len c c' l l' U H0 H1 H2 H3 H4 H5.
  subst; apply TEN_ID; auto.
Qed.

Lemma TEN2_helper1_helper1 : forall (prg_len ctrl targ : nat),
    targ < prg_len -> ctrl < targ -> 
    prog_ctrl_app prg_len σx ctrl targ
    = (I (2^ctrl)) ⊗ prog_ctrl_app (prg_len - ctrl) σx 0 (targ - ctrl).
Proof. intros prg_len ctrl targ targ_bounded ctrl_less_targ.
  gen prg_len targ.
  induction ctrl.
  - intros prg_len targ targ_bounded ctrl_less_targ. 
    simpl.
    replace (prg_len - 0) with prg_len by lia.
    replace (targ - 0) with targ by lia.
    rewrite kron_1_l; auto with wf_db.
  - intros prg_len targ targ_bounded ctrl_less_targ.
    assert (prog_ctrl_app prg_len σx (s ctrl) targ = prog_ctrl_app (s (prg_len - 1)) σx (s ctrl) (s (targ - 1))).
    { replace (s (prg_len - 1)) with prg_len by lia.
      replace (s (targ - 1)) with targ by lia. reflexivity. }
    rewrite H0.
    rewrite prog_ctrl_reduce'.
    rewrite IHctrl; try lia.
    replace (prg_len - 1 - ctrl) with (prg_len - s ctrl) by lia.
    replace (targ - 1 - ctrl) with (targ - s ctrl) by lia.
    replace (2 ^ s ctrl) with (2 * 2 ^ ctrl) by auto.
    rewrite <- id_kron.
    rewrite kron_assoc; auto with wf_db.
    f_equal.
    1 - 2 : rewrite <- Nat.pow_add_r;
    replace (ctrl + (prg_len - s ctrl)) with (prg_len - 1) by lia; auto.
Qed.

Lemma TEN2_helper1_helper2_helper_helper : forall (d : nat),
    (d > 0)%nat ->
    prog_ctrl_app (s d) σx 0 (d) =
      (∣0⟩⟨0∣ ⊗ (I (2 ^ (d - 1)) ⊗ I 2) .+ ∣1⟩⟨1∣ ⊗ (I (2 ^ (d - 1)) ⊗ σx)).
Proof. intros d H0.
  unfold prog_ctrl_app.
  bdestruct_all; simpl.
  rewrite kron_1_l; auto with wf_db.
  replace (d - 0) with d by lia.
  setoid_rewrite <- kron_1_r at 18.
  replace (2 ^ (match d with
                | 0 => s d
                | s l => d - l
                end - 1))
    with 1
    by (destruct d; try contradiction; replace (s d - d - 1) with 0 by lia; auto).
  rewrite ! kron_1_r.
  f_equal.
  4 : rewrite <- kron_assoc; auto with wf_db.
  3 : f_equal.
  5 : rewrite id_kron.
  1 - 5 : replace (2 ^ d) with (2 ^ (d - 1) * 2); auto;
  setoid_rewrite <- Nat.pow_1_r at 10;
  rewrite <- Nat.pow_add_r;
  replace (d - 1 + 1) with d  by lia; auto.
Qed.

Lemma TEN2_helper1_helper2_helper : forall (d a : nat),
    (d > 0)%nat ->
    prog_ctrl_app (a + s d) σx 0 (d) =
      (∣0⟩⟨0∣ ⊗ (I (2 ^ (d - 1)) ⊗ I 2) .+ ∣1⟩⟨1∣ ⊗ (I (2 ^ (d - 1)) ⊗ σx)) ⊗ (I (2 ^ a)).
Proof. intros d a H0.
  destruct a.
  - simpl. replace (d + 0) with d by lia.
    rewrite kron_1_r.
    apply TEN2_helper1_helper2_helper_helper; auto.
  - unfold prog_ctrl_app.
    bdestruct_all.
    simpl.
    rewrite kron_1_l; auto with wf_db.
    replace (d - 0) with d by lia.
    rewrite id_kron.
    replace (2 ^ (d - 1) * 2) with (2 ^ d)
      by (assert (TEMP : d = d - 1 + 1) by lia;
          rewrite TEMP at 1;
          rewrite Nat.pow_add_r;
          auto).
    replace (match d with
             | 0 => s (a + s d)
             | s l => a + s d - l
             end - 1)
      with (a + 1)
      by (destruct d; lia).
    replace (2 ^ a + (2 ^ a + 0))
      with (2 ^ (a + 1))
      by (rewrite Nat.pow_add_r; simpl; lia). 
    f_equal; try lia.
    f_equal.
    setoid_rewrite kron_assoc; auto with wf_db.
    f_equal;
      replace (2 ^ (d - 1) * 2) with (2 ^ d)
      by (assert (TEMP : d = d - 1 + 1) by lia;
          rewrite TEMP at 1;
          rewrite Nat.pow_add_r;
          auto);
      reflexivity.
Qed.

Lemma TEN2_helper1_helper2 : forall (prg_len ctrl targ : nat),
    targ < prg_len -> ctrl < targ -> 
    prog_ctrl_app (prg_len - ctrl) σx 0 (targ - ctrl)
    = (∣0⟩⟨0∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ σx) ⊗
        (I (2^(prg_len - targ - 1))).
Proof. intros prg_len ctrl targ H0 H1.
  pose (TEN2_helper1_helper2_helper (targ - ctrl) (prg_len - targ - 1))
    as H2.
  assert (H3 : targ - ctrl > 0) by lia.
  specialize (H2 H3).
  replace (prg_len - targ - 1 + s (targ - ctrl)) with (prg_len - ctrl) in H2 by lia.
  rewrite H2.
  f_equal; auto with wf_db.
  f_equal; auto with wf_db;
    rewrite kron_assoc;
    auto with wf_db.
Qed.
  
Lemma TEN2_helper1 : forall (prg_len ctrl targ : nat),
    targ < prg_len -> ctrl < targ -> 
    prog_ctrl_app prg_len σx ctrl targ
    = (I (2^ctrl)) ⊗
                    ( ∣0⟩⟨0∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ I 2 .+
                      ∣1⟩⟨1∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ σx) ⊗
                                                                                 (I (2^(prg_len - targ - 1))).
Proof. intros prg_len ctrl targ targ_bounded ctrl_less_targ.
  rewrite TEN2_helper1_helper1; auto.
  rewrite ! kron_assoc; auto with wf_db.
  f_equal.
  1 - 2 : replace (prg_len - ctrl) with (1 + (targ - ctrl - 1) + 1 + (prg_len - targ -1)) by lia;
  rewrite ! Nat.pow_add_r; auto.
  rewrite TEN2_helper1_helper2; try lia.
  f_equal; auto with wf_db.
  f_equal; auto with wf_db;
    setoid_rewrite kron_assoc;
    auto with wf_db.
Qed.

Lemma TEN2_helper2_helper : forall (ctrl targ : nat) (l : list Pauli),
    targ > ctrl ->
    l = (firstn ctrl l) ++
          (firstn 1 (skipn ctrl l)) ++
          (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l)) ++
          (firstn 1 (skipn targ l)) ++
          (skipn (targ + 1) l).
Proof. intros ctrl targ l H0.
  rewrite <- firstn_skipn with (n := ctrl) (l := l) at 1.
  f_equal.
  rewrite <- firstn_skipn with (n := 1) (l := skipn ctrl l) at 1.
  f_equal.
  rewrite skipn_skipn.
  replace (1 + ctrl) with (ctrl + 1) by lia.
  rewrite <- firstn_skipn with (n := (targ - ctrl - 1)) (l := skipn (ctrl + 1) l) at 1.
  f_equal.
  rewrite skipn_skipn.
  replace (targ - ctrl - 1 + (ctrl + 1)) with targ by lia.
  rewrite <- firstn_skipn with (n := 1) (l := (skipn targ l)) at 1.
  f_equal.
  rewrite skipn_skipn.
  replace (1 + targ) with (targ + 1) by lia.
  reflexivity.
Qed.

Lemma TEN2_helper2 : forall (ctrl targ : nat) (l : list Pauli),
    targ > ctrl ->
    (⨂ map translate_P l) =
      (⨂ map translate_P (firstn ctrl l))
        ⊗ (⨂ map translate_P (firstn 1 (skipn ctrl l)))
        ⊗ (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l)))
        ⊗ (⨂ map translate_P (firstn 1 (skipn targ l)))
        ⊗ (⨂ map translate_P (skipn (targ + 1) l)).
Proof. intros ctrl targ l H0. 
  rewrite TEN2_helper2_helper with (ctrl := ctrl) (targ := targ) (l := l); auto.
  rewrite ! (map_app translate_P). rewrite ! app_assoc.
  repeat (try rewrite big_kron_app; 
          try rewrite <- ! app_assoc; 
          intros; auto with wf_db;
          try rewrite ! app_assoc).
  rewrite <- ! app_assoc.
  rewrite <- TEN2_helper2_helper with (ctrl := ctrl) (targ := targ) (l := l); auto.
  all: rewrite <- ! (map_app translate_P); apply WF_Matrix_nth_Pauli.
Qed.

Lemma switch_inc2: forall {X : Type} (n m : nat) (ls : list X) (x y : X),
    n < length ls -> m < n ->
    (switch (switch ls x n) y m) = firstn m ls ++ [y] ++
                                     firstn (n - m - 1) (skipn (s m) ls) ++ [x] ++
                                     skipn (s n) ls.
Proof. intros X n m ls x y H0 H1.
  assert (m < length (switch ls x n)) by (rewrite switch_len; lia).
  rewrite (switch_inc m (switch ls x n) y H2).
  rewrite (switch_inc n ls x H0).
  setoid_rewrite <- firstn_skipn with (n := m) (l := ls) at 1.
  assert (n = (length (firstn m ls)) + (n - m)) by (rewrite firstn_length_le; lia).
  setoid_rewrite H3 at 1.
  rewrite firstn_app_2 with (n := (n - m)) (l1 := firstn m ls) (l2 := skipn m ls).
  rewrite <- app_assoc.
  rewrite firstn_app with (n := m) (l1 := firstn m ls).
  replace (m - length (firstn m ls)) with 0%nat by (rewrite firstn_length; lia).
  replace (firstn 0%nat (firstn (n - m) (skipn m ls) ++ [x] ++ skipn (s n) ls)) with (@nil X)
    by auto.
  rewrite app_nil_r.
  rewrite firstn_firstn.
  replace (Init.Nat.min m m) with m by lia.
  do 2 f_equal.
  rewrite skipn_app with (n := s m) (l1 := firstn n ls).
  rewrite firstn_skipn_comm with (m := n - m - 1) (n := s m) (l := ls).
  replace (s m + (n - m - 1)) with n by lia.
  f_equal.
  rewrite firstn_length.
  replace (Init.Nat.min n (length ls)) with n by lia.
  replace (s m - n) with 0%nat by lia.
  rewrite skipn_O.
  reflexivity.
Qed.

Lemma TEN2_helper3 : forall (ctrl targ : nat) (l : list Pauli) (A B : Pauli),
    targ > ctrl -> length l > targ ->
    (⨂ map translate_P (switch (switch l A ctrl) B targ)) =
      (⨂ map translate_P (firstn ctrl l))
        ⊗ (⨂ map translate_P [A])
        ⊗ (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l)))
        ⊗ (⨂ map translate_P [B])
        ⊗ (⨂ map translate_P (skipn (targ + 1) l)).
Proof. intros ctrl targ l A B H0 H1.
  rewrite switch_switch_diff; try lia.
  rewrite switch_inc2 with (ls := l) (x := B) (n := targ) (y := A) (m := ctrl); auto.
  rewrite ! map_app. 
  rewrite ! app_assoc.
  rewrite ! big_kron_app; auto with wf_db.
  replace (s ctrl) with (ctrl + 1)%nat by lia.
  replace (s targ) with (targ + 1)%nat by lia.
  easy.
  all: intros; rewrite <- ! (map_app translate_P); apply WF_Matrix_nth_Pauli.
Qed.

Lemma TEN2_helper4_helper1 : forall (prg_len ctrl targ : nat),
    ctrl < prg_len -> targ < ctrl ->
    prog_ctrl_app prg_len σx ctrl targ =
      I (2 ^ targ) ⊗ prog_ctrl_app (prg_len - targ) σx (ctrl - targ) 0.
Proof. intros prg_len ctrl targ H0 H1.
  gen prg_len ctrl.
  induction targ.
  - intros prg_len ctrl H0 H1.
    replace (prg_len - 0) with prg_len by lia.
    replace (ctrl - 0) with ctrl by lia.
    unfold prog_ctrl_app.
    bdestruct_all.
    simpl.
    repeat rewrite ! kron_1_l; auto with wf_db.
    apply WF_kron; auto with wf_db.
    replace (ctrl - 0) with ctrl by lia.
    rewrite ! Nat.add_0_r.
    apply WF_plus; auto with wf_db.
  - intros prg_len ctrl H0 H1.
    destruct ctrl; try lia.
    apply PeanoNat.lt_S_n in H1.
    destruct prg_len; try lia.
    apply PeanoNat.lt_S_n in H0.
    rewrite prog_ctrl_reduce'.
    rewrite IHtarg; try lia.
    replace (s targ) with (1 + targ) by lia.
    rewrite Nat.pow_add_r.
    rewrite <- id_kron.
    replace (2 ^ 1) with 2 by auto.
    rewrite kron_assoc; auto with wf_db.
    f_equal.
    1 - 2 : rewrite <- Nat.pow_add_r;
    f_equal; lia.
Qed.

Lemma TEN2_helper4_helper2_helper_helper : forall (d : nat),
    d > 0 ->
    prog_ctrl_app (s d) σx d 0 =
      I 2 ⊗ I (2 ^ (d - 1)) ⊗ ∣0⟩⟨0∣ .+ σx ⊗ I (2 ^ (d - 1)) ⊗ ∣1⟩⟨1∣ .
Proof. intros d H0.
  unfold prog_ctrl_app.
  bdestruct_all.
  replace (s d - d - 1) with 0%nat by lia.
  simpl.
  rewrite kron_1_l, kron_1_r; auto with wf_db.
  rewrite ! id_kron.
  replace (2 * 2 ^ (d - 1)) with (2 ^ 1 * 2 ^ (d - 1)) by auto.
  rewrite <- Nat.pow_add_r.
  replace (d - 0) with d by lia.
  replace (1 + (d - 1)) with d by lia.
  reflexivity.
Qed. 

Lemma TEN2_helper4_helper2_helper : forall (d a : nat),
    d > 0 ->
    prog_ctrl_app (a + s d) σx d 0 =
      (I 2 ⊗ I (2 ^ (d - 1)) ⊗ ∣0⟩⟨0∣ .+ σx ⊗ I (2 ^ (d - 1)) ⊗ ∣1⟩⟨1∣) ⊗ I (2 ^ a).
Proof. intros d a H0.
  destruct a.
  - simpl. rewrite kron_1_r.
    apply (TEN2_helper4_helper2_helper_helper d H0).
  - unfold prog_ctrl_app.
    bdestruct_all.
    simpl.
    rewrite kron_1_l; auto with wf_db.
    replace (d - 0) with d by lia.
    rewrite id_kron.
    replace (2 ^ (d - 1) * 2) with (2 ^ d)
      by (assert (TEMP : d = d - 1 + 1) by lia;
          rewrite TEMP at 1;
          rewrite Nat.pow_add_r;
          auto).
    replace (match d with
             | 0 => s (a + s d)
             | s l => a + s d - l
             end - 1)
      with (a + 1)
      by (destruct d; lia).
    replace (2 ^ a + (2 ^ a + 0))
      with (2 ^ (a + 1))
      by (rewrite Nat.pow_add_r; simpl; lia).
    replace (2 * 2 ^ (d - 1)) with (2 ^ 1 * 2 ^ (d - 1)) by auto.
    rewrite <- Nat.pow_add_r.
    replace (1 + (d - 1)) with d by lia.
    reflexivity.
Qed.

Lemma TEN2_helper4_helper2 : forall (prg_len ctrl targ : nat),
    ctrl < prg_len ->
    targ < ctrl ->
    prog_ctrl_app (prg_len - targ) σx (ctrl - targ) 0 =
      (I 2 ⊗ I (2 ^ (ctrl - targ - 1)) ⊗ ∣0⟩⟨0∣
   .+ σx ⊗ I (2 ^ (ctrl - targ - 1)) ⊗ ∣1⟩⟨1∣) ⊗ I (2 ^ (prg_len - ctrl - 1)).
Proof. intros prg_len ctrl targ H0 H1.
  replace (prg_len - targ) with ((prg_len - ctrl - 1) + s (ctrl - targ)) by lia.
  apply TEN2_helper4_helper2_helper; lia.
Qed.

Lemma TEN2_helper4 : forall (prg_len ctrl targ : nat),
    ctrl < prg_len ->
    targ < ctrl ->
    prog_ctrl_app prg_len σx ctrl targ =
      I (2 ^ targ)
        ⊗ (I 2 ⊗ I (2 ^ (ctrl - targ - 1)) ⊗ ∣0⟩⟨0∣
         .+ σx ⊗ I (2 ^ (ctrl - targ - 1)) ⊗ ∣1⟩⟨1∣) ⊗ I (2 ^ (prg_len - ctrl - 1)).
Proof. intros prg_len ctrl targ H0 H1.
  rewrite TEN2_helper4_helper1; try lia.
  rewrite kron_assoc; auto with wf_db.
  f_equal;
    try (ring_simplify; replace 4%nat with (2 ^ 2) by auto;
         repeat rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite TEN2_helper4_helper2; auto; lia.
Qed.


Lemma TEN2 : forall (l : list Pauli) (ctrl targ : nat) (pm c : Coef) (A B : Pauli),
    ctrl < length l -> targ < length l -> ctrl <> targ ->
    not_gI (nth ctrl l gI) \/ not_gI (nth targ l gI) -> not_gI A \/ not_gI B ->
    pm = C1 \/ pm = (- C1)%C ->
    @triple 2 (AtoPred [(C1, [nth ctrl l gI; nth targ l gI])]) (CNOT 0 1) (AtoPred [(pm, [A; B])])  ->
    @triple (length l)
      (AtoPred [(c, l)])
      (CNOT ctrl targ)
      (AtoPred [((c * pm)%C, switch (switch l A ctrl) B targ)]).
Proof. intros l ctrl targ pm c A B ctrl_bounded targ_bounded ctrl_targ_different not_both_gI_ctrl_targ not_both_gI_A_B pm_1 H0.
  apply Heisenberg_Eigenvector_semantics.
  apply Eigenvector_Heisenberg_semantics in H0.

    unfold translateA, translate in H0; simpl in H0.
    rewrite ! Mplus_0_l, ! Mscale_1_l, ! kron_1_r in H0.
    setoid_rewrite <- Mscale_kron_dist_r in H0.

    unfold prog_ctrl_app in H0.
    simpl in H0.
    rewrite ! kron_1_l, ! kron_1_r in H0.
    setoid_rewrite CX_is_CNOT in H0.

    unfold translateA, translate; simpl.
    rewrite ! Mplus_0_l.

    rewrite ! map_length, ! switch_len.
    rewrite Mscale_mult_dist_r,  Mscale_mult_dist_l.
    rewrite <- Mscale_assoc.
    apply Mscale_inj.

    bdestruct (ctrl <? targ).
    2 : shelve.
    rename H1 into ctrl_lt_targ.
    
    rewrite TEN2_helper1.
    rewrite TEN2_helper2 with (ctrl := ctrl) (targ := targ).
    rewrite TEN2_helper3 with (ctrl := ctrl) (targ := targ).


    rewrite ! map_length.
    rewrite ! firstn_length.
    rewrite ! skipn_length.
    minmax_breakdown.
    rewrite ! Nat.sub_add_distr.
    replace (⨂ map translate_P [A])
      with (translate_P A) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [B])
      with (translate_P B) by (simpl; rewrite kron_1_r; auto).
    replace (length [A]) with 1 by auto.
    replace (length [B]) with 1 by auto.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.


    setoid_rewrite <- Mscale_mult_dist_l with (x := pm).
    setoid_rewrite <- Mscale_kron_dist_l with (x := pm).
    setoid_rewrite <- Mscale_kron_dist_r with (x := pm).


    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal.
    
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.

    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal; try lia.
    
    setoid_rewrite kron_assoc at 1; auto with wf_db.
    setoid_rewrite kron_assoc at 2; auto with wf_db.
    replace (I (2 ^ (targ - ctrl - 1)) ⊗ I 2) with (I (2 * (2 ^ (targ - ctrl - 1))))
      by (rewrite id_kron; f_equal; lia).
    
    rewrite ! firstn1_singleton with (d := gI).
    rewrite ! hd_skipn_nth.

    replace (⨂ map translate_P [nth ctrl l gI])
      with (translate_P (nth ctrl l gI)) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [nth targ l gI])
      with (translate_P (nth targ l gI)) by (simpl; rewrite kron_1_r; auto).

    minmax_breakdown.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.

    setoid_rewrite <- kron_assoc at 1; auto with wf_db.
    setoid_rewrite <- kron_assoc at 1; auto with wf_db.


    replace 
      (Init.Nat.mul (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)) 2)
      with
      (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)))
      by lia.

    replace 
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      with
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      by lia.
    
    replace
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      with
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      by lia.

    eapply @cnot_conv_inc with (n := (targ - ctrl - 1))
                               (a := translate_P (nth ctrl l gI))
                               (b := translate_P (nth targ l gI))
                               (a' := translate_P A) (b' := pm .* (translate_P B))
                               (C := (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l))))
                               (C' := (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l)))).


  all : repeat (try rewrite ! map_length; try rewrite ! firstn_length;
                try rewrite ! skipn_length; minmax_breakdown;
                minmax_breakdown_context;
                repeat rewrite ! Nat.sub_add_distr;
                auto;
                match goal with
                | |- skipn _ _ <> [] => intro H'; apply skipn_nil_length in H'; lia
                | |- (_ <> _)%nat => try (intro; lia)
                | |- trace_zero_syntax _ => simpl;
                                          try (destruct not_both_gI_ctrl_targ
                                              as [[not_gI | [not_gI | not_gI]]  | [not_gI | [not_gI | not_gI]]];
                                               rewrite not_gI);
                                          try (destruct not_both_gI_A_B
                                              as [[not_gI | [not_gI | not_gI]]  | [not_gI | [not_gI | not_gI]]];
                                               rewrite ! not_gI);
                                          match goal with
                                          | |- trace_zero_syntax [?x; ?y] =>
                                              replace [x; y] with ([x] ++ [y]) by auto
                                          end;
                                          try (apply trace_zero_syntax_L; constructor);
                                          try (apply trace_zero_syntax_R; constructor)
                | |- proper_length_AType_nil _ => repeat constructor; try (intro; lia) 
                | |- WF_Unitary _ =>
                    apply restricted_addition_semantic_implies_Unitary;
                    do 2 constructor; simpl; auto
                | |- adjoint _ = _ =>
                    apply restricted_addition_semantic_implies_Hermitian;
                    do 2 constructor ; simpl; auto
                | |- trace _ = _ =>
                    apply restricted_addition_semantic_implies_trace_zero;
                    do 2 constructor; simpl; auto
                | |- _ > _ => try lia
                | |- _ < _ => try lia
                | |- WF_Matrix (_ ⊗ _) => apply WF_kron
                | |- WF_Matrix (⨂ ?l) =>
                    let WF := fresh "WF" in
                    pose (WF_big_kron' 2 2 l) as WF;
                    repeat rewrite ! map_length in WF;
                    repeat rewrite ! firstn_length in WF;
                    repeat rewrite ! skipn_length in WF;
                    minmax_breakdown_context;
                    repeat rewrite ! Nat.sub_add_distr in WF;
                    apply WF;
                    let A' := fresh "A'" in
                    let H' := fresh "H'" in
                    intros A' H';
                    rewrite in_map_iff in H';
                    let x' := fresh "x'" in
                    let H'1 := fresh "H'1" in
                    let H'2 := fresh "H'2" in
                    destruct H' as [x' [H'1 H'2]];
                    rewrite <- H'1;
                    auto with wf_db
                | |- WF_Matrix _ => auto with wf_db
                | |- proper_length_TType _ => split; simpl; auto; try (intro; lia)
                | |- context[(2*?n)%nat] => 
                    replace (2*n)%nat with (2^1 * n)%nat 
                    by (simpl; auto)
                | |- context[(?n*2)%nat] => 
                    replace (n*2)%nat with (n * 2^1)%nat 
                    by (simpl; auto)
                | |- (2 ^ _ = 2 ^ _)%nat =>  f_equal; simpl; try lia
                | |- coef_plus_minus_1 _ => 
                    unfold coef_plus_minus_1; simpl; try (left; easy); try (right; easy)
                | |- _ => try rewrite ! Nat.mul_1_l; try rewrite ! Nat.mul_1_r;
                        repeat setoid_rewrite <- Nat.pow_add_r
                end).

  Unshelve.
  
  rewrite Mscale_kron_dist_r in H0.
  rewrite <- Mscale_kron_dist_l in H0.
  
  assert (targ_lt_ctrl : targ < ctrl) by lia.
  clear H1.

  rewrite TEN2_helper4; try lia.
  rewrite TEN2_helper2 with (ctrl := targ) (targ := ctrl); auto with wf_db.
  rewrite switch_switch_diff; try lia.
  rewrite TEN2_helper3 with (ctrl := targ) (targ := ctrl); auto with wf_db.


    rewrite ! map_length.
    rewrite ! firstn_length.
    rewrite ! skipn_length.
    minmax_breakdown.
    rewrite ! Nat.sub_add_distr.
    replace (⨂ map translate_P [A])
      with (translate_P A) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [B])
      with (translate_P B) by (simpl; rewrite kron_1_r; auto).
    replace (length [A]) with 1 by auto.
    replace (length [B]) with 1 by auto.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.


    setoid_rewrite <- Mscale_mult_dist_l with (x := pm).
    setoid_rewrite <- Mscale_kron_dist_l with (x := pm).
    setoid_rewrite <- Mscale_kron_dist_r with (x := pm).


    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal.
    
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.

    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal; try lia.
    
    replace (I 2 ⊗ I (2 ^ (ctrl - targ - 1)) ) with (I (2 * (2 ^ (ctrl - targ - 1))))
      by (rewrite id_kron; f_equal; lia).
    
    rewrite ! firstn1_singleton with (d := gI).
    rewrite ! hd_skipn_nth.

    replace (⨂ map translate_P [nth ctrl l gI])
      with (translate_P (nth ctrl l gI)) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [nth targ l gI])
      with (translate_P (nth targ l gI)) by (simpl; rewrite kron_1_r; auto).

    minmax_breakdown.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.

    setoid_rewrite <- kron_assoc at 1; auto with wf_db.
    setoid_rewrite <- kron_assoc at 1; auto with wf_db.


    replace 
      (Init.Nat.mul (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)) 2)
      with
      (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)))
      by lia.

    replace 
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      with
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      by lia.
    
    replace
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      with
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      by lia.

    apply cnot_conv in H0.
    eapply @notc_conv_inc with (n := (ctrl - targ - 1))
                               (a := translate_P (nth targ l gI))
                               (b := translate_P (nth ctrl l gI))
                               (a' := translate_P B) (b' := pm .* (translate_P A))
                               (C := (⨂ map translate_P (firstn (ctrl - targ - 1) (skipn (targ + 1) l))))
                               (C' := (⨂ map translate_P (firstn (ctrl - targ - 1) (skipn (targ + 1) l)))).

  all : repeat (try rewrite ! map_length; try rewrite ! firstn_length;
                try rewrite ! skipn_length; minmax_breakdown;
                minmax_breakdown_context;
                repeat rewrite ! Nat.sub_add_distr;
                auto;
                match goal with
                | |- skipn _ _ <> [] => intro H'; apply skipn_nil_length in H'; lia
                | |- (_ <> _)%nat => try (intro; lia)
                | |- trace_zero_syntax _ => simpl;
                                          try (destruct not_both_gI_ctrl_targ
                                              as [[not_gI | [not_gI | not_gI]]  | [not_gI | [not_gI | not_gI]]];
                                               rewrite not_gI);
                                          try (destruct not_both_gI_A_B
                                              as [[not_gI | [not_gI | not_gI]]  | [not_gI | [not_gI | not_gI]]];
                                               rewrite ! not_gI);
                                          match goal with
                                          | |- trace_zero_syntax [?x; ?y] =>
                                              replace [x; y] with ([x] ++ [y]) by auto
                                          end;
                                          try (apply trace_zero_syntax_L; constructor);
                                          try (apply trace_zero_syntax_R; constructor)
                | |- proper_length_AType_nil _ _ => repeat constructor; try (intro; lia) 
                | |- WF_Unitary _ =>
                    apply restricted_addition_semantic_implies_Unitary;
                    do 2 constructor; simpl; auto
                | |- adjoint _ = _ =>
                    apply restricted_addition_semantic_implies_Hermitian;
                    do 2 constructor ; simpl; auto
                | |- trace _ = _ =>
                    apply restricted_addition_semantic_implies_trace_zero;
                    do 2 constructor; simpl; auto
                | |- _ > _ => try lia
                | |- _ < _ => try lia
                | |- WF_Matrix (_ ⊗ _) => apply WF_kron
                | |- WF_Matrix (⨂ ?l) =>
                    let WF := fresh "WF" in
                    pose (WF_big_kron' 2 2 l) as WF;
                    repeat rewrite ! map_length in WF;
                    repeat rewrite ! firstn_length in WF;
                    repeat rewrite ! skipn_length in WF;
                    minmax_breakdown_context;
                    repeat rewrite ! Nat.sub_add_distr in WF;
                    apply WF;
                    let A' := fresh "A'" in
                    let H' := fresh "H'" in
                    intros A' H';
                    rewrite in_map_iff in H';
                    let x' := fresh "x'" in
                    let H'1 := fresh "H'1" in
                    let H'2 := fresh "H'2" in
                    destruct H' as [x' [H'1 H'2]];
                    rewrite <- H'1;
                    auto with wf_db
                | |- WF_Matrix _ => auto with wf_db
                | |- proper_length_TType _ _ => split; simpl; auto; try (intro; lia)
                | |- context[(2*?n)%nat] => 
                    replace (2*n)%nat with (2^1 * n)%nat 
                    by (simpl; auto)
                | |- context[(?n*2)%nat] => 
                    replace (n*2)%nat with (n * 2^1)%nat 
                    by (simpl; auto)
                | |- (2 ^ _ = 2 ^ _)%nat =>  f_equal; simpl; try lia
                | |- _ => try rewrite ! Nat.mul_1_l; try rewrite ! Nat.mul_1_r;
                        repeat setoid_rewrite <- Nat.pow_add_r
                end).
Qed.


Lemma TEN2' : forall {l l' : list Pauli} {len ctrl targ : nat} (pm : Coef) {c c' : Coef} (A B A' B' : Pauli),
    ctrl < len -> targ < len -> ctrl <> targ ->
    not_gI A \/ not_gI B -> not_gI A' \/ not_gI B' -> len = length l ->
    A = nth ctrl l gI -> B = nth targ l gI -> l' = switch (switch l A' ctrl) B' targ ->
    pm = C1 \/ pm = (- C1)%C -> c' = (pm * c)%C ->
    @triple 2  (AtoPred [(C1, [A; B])]) (CNOT 0 1) (AtoPred [(pm, [A'; B'])])  ->
    @triple len (AtoPred [(c, l)]) (CNOT ctrl targ) (AtoPred [(c', l')]).
Proof. intros l l' len ctrl targ pm c c' A B A' B' H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. 
  rewrite Cmult_comm in H10.
  subst. apply TEN2; auto.
Qed.

Lemma WF_TEN3 : forall (l : list Pauli) (ctrl targ len : nat) (A B : Pauli) (c : Coef),
    ctrl < len -> targ < len -> ctrl <> targ -> len = length l -> c = C1 \/ c = (- C1)%C ->
    not_gI (nth ctrl l gI) \/ not_gI (nth targ l gI) ->
    @WF_TType len (c, l).
Proof. intros l ctrl targ len A B c H0 H1 H2 H3 H4 H5. 
  destruct H5.
  - apply (WF_TEN1 ctrl len c l H0 H5 H3 H4).
  - apply (WF_TEN1 targ len c l H1 H5 H3 H4).
Qed. 

Lemma WF_TEN4 : forall (l : list Pauli) (ctrl targ len : nat) (A B : Pauli) (c : Coef),
    ctrl < len -> targ < len -> ctrl <> targ -> len = length l -> c = C1 \/ c = (- C1)%C ->
    not_gI A \/ not_gI B ->
    @WF_TType (len) (c, switch (switch l A ctrl) B targ).
Proof. intros l ctrl targ len A B c H0 H1 H2 H3 H4 H5.
  destruct H5; [rewrite switch_switch_diff; auto | idtac];
    apply WF_TEN2;
    try rewrite switch_len;
    auto.
Qed.

Lemma TEN_ID2 : forall (l : list Pauli) (ctrl targ : nat) (c : Coef),
    ctrl < length l -> targ < length l -> ctrl <> targ -> nth ctrl l gI = gI -> nth targ l gI = gI ->
    @triple (length l) (AtoPred [(c, l)]) (CNOT ctrl targ) (AtoPred [(c, l)]).
Proof. intros l ctrl targ c H0 H1 H2 H3 H4.
  apply Heisenberg_Eigenvector_semantics.
  unfold translateA, translate; simpl.
  rewrite ! Mplus_0_l.

  rewrite ! map_length.
  rewrite Mscale_mult_dist_r,  Mscale_mult_dist_l.
  apply Mscale_inj.

  bdestruct (ctrl <? targ).
  2 : shelve.
  
  rewrite TEN2_helper1.
  rewrite TEN2_helper2 with (ctrl := ctrl) (targ := targ).



    rewrite ! map_length.
    rewrite ! firstn_length.
    rewrite ! skipn_length.
    minmax_breakdown.
    rewrite ! Nat.sub_add_distr.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.


    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal.
    
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.

    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal; try lia.
    
    setoid_rewrite kron_assoc at 1; auto with wf_db.
    setoid_rewrite kron_assoc at 2; auto with wf_db.
    replace (I (2 ^ (targ - ctrl - 1)) ⊗ I 2) with (I (2 * (2 ^ (targ - ctrl - 1))))
      by (rewrite id_kron; f_equal; lia).
    
    rewrite ! firstn1_singleton with (d := gI).
    rewrite ! hd_skipn_nth.

    replace (⨂ map translate_P [nth ctrl l gI])
      with (translate_P (nth ctrl l gI)) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [nth targ l gI])
      with (translate_P (nth targ l gI)) by (simpl; rewrite kron_1_r; auto).

    minmax_breakdown.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.

    setoid_rewrite <- kron_assoc at 1; auto with wf_db.
    setoid_rewrite <- kron_assoc at 1; auto with wf_db.



    replace 
      (Init.Nat.mul (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)) 2)
      with
      (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)))
      by lia.

    replace 
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      with
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      by lia.
    
    replace
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      with
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      by lia.


    rewrite H3. rewrite H4.

    eapply @cnot_conv_inc with (n := (targ - ctrl - 1))
                               (a := translate_P gI)
                               (b := translate_P gI)
                               (a' := translate_P gI) (b' := translate_P gI)
                               (C := (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l))))
                               (C' := (⨂ map translate_P (firstn (targ - ctrl - 1) (skipn (ctrl + 1) l)))).


  all : repeat (try rewrite ! map_length; try rewrite ! firstn_length;
                try rewrite ! skipn_length; minmax_breakdown;
                repeat rewrite ! Nat.sub_add_distr;
                match goal with
                | |- skipn _ _ <> [] => intro H'; apply skipn_nil_length in H'; lia
                | |- (_ <> _)%nat => try (intro; lia)
                | |- WF_Matrix (_ ⊗ _) => apply WF_kron
                | |- WF_Matrix (⨂ ?l) =>
                    let WF := fresh "WF" in
                    pose (WF_big_kron' 2 2 l) as WF;
                    repeat rewrite ! map_length in WF;
                    repeat rewrite ! firstn_length in WF;
                    repeat rewrite ! skipn_length in WF;
                    minmax_breakdown_context;
                    repeat rewrite ! Nat.sub_add_distr in WF;
                    apply WF;
                    let A' := fresh "A'" in
                    let H' := fresh "H'" in
                    intros A' H';
                    rewrite in_map_iff in H';
                    let x' := fresh "x'" in
                    let H'1 := fresh "H'1" in
                    let H'2 := fresh "H'2" in
                    destruct H' as [x' [H'1 H'2]];
                    rewrite <- H'1;
                    auto with wf_db
                | |- WF_Matrix _ => auto with wf_db
                | |- _ => simpl; ring_simplify; auto;
                        replace 4%nat with (2^2)%nat by auto;
                        repeat setoid_rewrite <- Nat.pow_add_r;
                        try match goal with
                        | |- (2 ^ _ = 2 ^ _)%nat =>  f_equal
                        end;
                        repeat rewrite ! Nat.sub_add_distr;
                        try lia
                end).
  simpl. rewrite id_kron. lma'.
  f_equal.



  Unshelve.
  
  rewrite TEN2_helper4; try lia.
  rewrite TEN2_helper2 with (ctrl := targ) (targ := ctrl); auto with wf_db; try lia.
  


    rewrite ! map_length.
    rewrite ! firstn_length.
    rewrite ! skipn_length.
    minmax_breakdown.
    rewrite ! Nat.sub_add_distr.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.


    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal.
    
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.
    setoid_rewrite kron_assoc at 3; auto with wf_db.

    setoid_rewrite kron_mixed_product'.
    rewrite Mmult_1_l.
    rewrite Mmult_1_r.
    f_equal; try lia.
    
    replace (I 2 ⊗ I (2 ^ (ctrl - targ - 1)) ) with (I (2 * (2 ^ (ctrl - targ - 1))))
      by (rewrite id_kron; f_equal; lia).
    
    rewrite ! firstn1_singleton with (d := gI).
    rewrite ! hd_skipn_nth.

    replace (⨂ map translate_P [nth ctrl l gI])
      with (translate_P (nth ctrl l gI)) by (simpl; rewrite kron_1_r; auto).
    replace (⨂ map translate_P [nth targ l gI])
      with (translate_P (nth targ l gI)) by (simpl; rewrite kron_1_r; auto).

    minmax_breakdown.
    replace (2 ^ 1)%nat with 2 by auto.
    rewrite ! Nat.mul_assoc.

    setoid_rewrite <- kron_assoc at 1; auto with wf_db.
    setoid_rewrite <- kron_assoc at 1; auto with wf_db.


    replace 
      (Init.Nat.mul (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)) 2)
      with
      (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1)))
      by lia.

    replace 
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      with
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      by lia.
    
    replace
      (Init.Nat.mul 2 (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))))
      with
      (Init.Nat.mul (Init.Nat.mul 2 (Nat.pow 2 (Init.Nat.sub (Init.Nat.sub targ ctrl) 1))) 2)
      by lia.

    rewrite H3. rewrite H4.
    eapply @notc_conv_inc with (n := (ctrl - targ - 1))
                               (a := translate_P gI)
                               (b := translate_P gI)
                               (a' := translate_P gI) (b' := translate_P gI)
                               (C := (⨂ map translate_P (firstn (ctrl - targ - 1) (skipn (targ + 1) l))))
                               (C' := (⨂ map translate_P (firstn (ctrl - targ - 1) (skipn (targ + 1) l)))).

  all : repeat (try rewrite ! map_length; try rewrite ! firstn_length;
                try rewrite ! skipn_length; minmax_breakdown;
                repeat rewrite ! Nat.sub_add_distr;
                match goal with
                | |- skipn _ _ <> [] => intro H'; apply skipn_nil_length in H'; lia
                | |- (_ <> _)%nat => try (intro; lia)
                | |- WF_Matrix (_ ⊗ _) => apply WF_kron
                | |- WF_Matrix (⨂ ?l) =>
                    let WF := fresh "WF" in
                    pose (WF_big_kron' 2 2 l) as WF;
                    repeat rewrite ! map_length in WF;
                    repeat rewrite ! firstn_length in WF;
                    repeat rewrite ! skipn_length in WF;
                    minmax_breakdown_context;
                    repeat rewrite ! Nat.sub_add_distr in WF;
                    apply WF;
                    let A' := fresh "A'" in
                    let H' := fresh "H'" in
                    intros A' H';
                    rewrite in_map_iff in H';
                    let x' := fresh "x'" in
                    let H'1 := fresh "H'1" in
                    let H'2 := fresh "H'2" in
                    destruct H' as [x' [H'1 H'2]];
                    rewrite <- H'1;
                    auto with wf_db
                | |- WF_Matrix _ => auto with wf_db
                | |- _ => simpl; ring_simplify; auto;
                        replace 4%nat with (2^2)%nat by auto;
                        repeat setoid_rewrite <- Nat.pow_add_r;
                        try match goal with
                        | |- (2 ^ _ = 2 ^ _)%nat =>  f_equal
                        end;
                        repeat rewrite ! Nat.sub_add_distr;
                        try lia
                end).
  simpl. rewrite id_kron. lma'.
  f_equal.
Qed.

Lemma TEN_ID2' : forall {ctrl targ len : nat} {c c' : Coef} {l l' : list Pauli},
    ctrl < len -> targ < len -> ctrl <> targ -> len = length l-> 
    nth ctrl l gI = gI -> nth targ l gI = gI -> c = c' -> l = l' ->
    @triple len (AtoPred [(c, l)]) (CNOT ctrl targ) (AtoPred [(c', l')]).
Proof. intros ctrl targ len c c' l l' H0 H1 H2 H3 H4 H5 H6 H7. 
  subst; apply TEN_ID2; auto.
Qed.

Lemma TEN3 : forall (bit : nat) (pm c : Coef) (l : list Pauli) (A B : Pauli),
    bit < length l -> not_gI (nth bit l gI) -> not_gI A -> not_gI B -> anticommute_Pauli A B ->
    pm = C1 \/ pm = (- C1)%C ->
@triple 1 (AtoPred [(C1, [nth bit l gI])]) (T 0) (AtoPred [((C1/√2)%C, [A]); (((C1/√2) * pm)%C, [B])]) ->
@triple (length l) (AtoPred [(c, l)]) (T bit) (AtoPred [(((C1/√2)*c)%C, switch l A bit); (((C1/√2)*(c * pm))%C, switch l B bit)]).
Proof. intros bit pm c l A B H0 H1 H2 H3 H4 H5 H6. 
  apply Heisenberg_Eigenvector_semantics.
  apply Eigenvector_Heisenberg_semantics in H6.

  unfold translateA, translate in H6; simpl in H6.
  rewrite ! Mplus_0_l, ! Mscale_1_l, ! kron_1_r in H6.

  unfold prog_simpl_app in H6.
  simpl in H6.
  rewrite ! kron_1_l, ! kron_1_r in H6; auto with wf_db.
  rewrite <- Mscale_assoc in H6.
  rewrite <- Mscale_plus_distr_r in H6.
  rewrite  Mscale_mult_dist_l in H6.

  unfold translateA, translate; simpl.
  rewrite ! Mplus_0_l.

  rewrite ! map_length, ! switch_len.
  rewrite Mscale_mult_dist_r.
  rewrite <- ! Mscale_assoc.
  rewrite <- ! Mscale_plus_distr_r.
  rewrite  ! Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  replace (C1 / √ 2 * c)%C with (c * (C1 / √ 2))%C by lca.
  rewrite <- Mscale_assoc.
  apply Mscale_inj.

  unfold prog_simpl_app.
  bdestruct_all.

  replace (⨂ map translate_P l)
    with (⨂ map translate_P (firstn bit l ++ [nth bit l gI] ++ skipn (s bit) l))
    by (rewrite <- (nth_inc bit l gI); auto).
  rewrite ! switch_inc.
  replace (s bit) with (bit + 1) by lia.
  rewrite ! map_app.
  rewrite ! big_kron_app;
    try (intros; auto with wf_db).
  setoid_rewrite <- Mscale_kron_dist_r with (x := pm).
  setoid_rewrite <- Mscale_kron_dist_l with (x := pm).
  setoid_rewrite <- kron_plus_distr_l.
  setoid_rewrite <- kron_plus_distr_r.
  
  setoid_rewrite <- Mscale_mult_dist_l.
  setoid_rewrite <- Mscale_kron_dist_r.
  setoid_rewrite <- Mscale_kron_dist_l.

  repeat setoid_rewrite <- kron_assoc;
    replace ((fix pow (n m : nat) {struct m} : nat :=
                match m with
                | 0 => 1
                | s m0 => n * pow n m0
                end) 2
               ((fix length (l0 : list (Square 2)) : nat :=
                   match l0 with
                   | [] => 0
                   | _ :: l' => s (length l')
                   end) (map translate_P (skipn (bit + 1) l))))
    with (2 ^ (length (map translate_P (skipn (bit + 1) l))))
    by auto.
  
  rewrite ! map_length.
  rewrite ! firstn_length.
  minmax_breakdown.

  setoid_rewrite kron_mixed_product';
    repeat match goal with
      | |- context [2 * ?x] => replace (2 * x) with (2 ^ 1 * x) by (auto; lia)
      end;
    try rewrite <- ! Nat.pow_add_r;
    try match goal with
      | |- 2 ^ _ = 2 ^ _ => f_equal
      end;
    try lia;
    
    try setoid_rewrite map_length;
    try setoid_rewrite firstn_length;
    minmax_breakdown;
    try setoid_rewrite skipn_length;
    try setoid_rewrite Nat.sub_add_distr;
    try ring_simplify; auto; try lia.

  setoid_rewrite kron_mixed_product'; auto; try lia.

  minmax_breakdown.
  rewrite skipn_length.
  
  setoid_rewrite Mmult_1_l.
  rewrite Nat.sub_add_distr.
  setoid_rewrite Mmult_1_r.
  
  do 2 f_equal; try lia.
  simpl. rewrite ! kron_1_r.
  rewrite Mscale_mult_dist_l.
  all : destruct H5; subst;
    auto with wf_db;
    try apply WF_scale;
    try apply WF_plus;
    try rewrite ! Nat.sub_add_distr.
  all : try apply WF_scale;
    try match goal with
      | |- WF_Matrix (⨂ map translate_P ?l) =>
          pose (WF_big_kron' 2 2) as WF;
          specialize (WF (map translate_P l));
          rewrite map_length in WF;
          try rewrite ! firstn_length in WF;
          try rewrite ! skipn_length in WF;
          minmax_breakdown_context;
          try rewrite ! Nat.sub_add_distr in WF;
          apply WF; intros M inM;
          rewrite in_map_iff in inM;
          destruct inM as [X [XM inX]];
          rewrite <- XM;
          auto with wf_db
      end;
    try destruct i; simpl; auto with wf_db;
    replace 2 with (2 ^ 1)%nat by auto;
    repeat match goal with
      | |- coef_plus_minus_1 _ =>
          unfold coef_plus_minus_1; simpl
      | |- C1 = C1 \/ _ => left; reflexivity
      | |- _ \/ (- C1)%C = (- C1)%C => right; reflexivity
      | |- proper_length_TType _ => split; auto; try lia
      | |- trace_zero_syntax _ => simpl;
                                try (destruct H1
                                    as [not_gI | [not_gI | not_gI]];
                                     rewrite ! not_gI);
                                try (destruct H2
                                    as [not_gI | [not_gI | not_gI]];
                                     destruct H3
                                       as [not_gI' | [not_gI' | not_gI']];
                                     try rewrite ! not_gI; try rewrite ! not_gI');
                                constructor
      | |- proper_length_AType_nil _ => repeat constructor; try (intro; lia)
      | |- WF_Unitary _ =>
          apply restricted_addition_semantic_implies_Unitary
      | |- adjoint _ = _ =>
          apply restricted_addition_semantic_implies_Hermitian
      | |- trace _ = _ =>
          apply restricted_addition_semantic_implies_trace_zero
      | |- restricted_addition_semantic [_] => do 2 constructor; simpl
      | |- restricted_addition_semantic [_; _] =>
          replace [((C1 / √ 2)%C, [A]); ((C1 / √ 2 * C1)%C, [B])]
          with (@gScaleA 1 (C1 / √ 2)%C ([(C1,[A])] ++ [(C1,[B])]))
          by (unfold gScaleA; simpl; rewrite ! Cmult_1_r; auto);
          replace [((C1 / √ 2)%C, [A]); ((C1 / √ 2 * - C1)%C, [B])]
            with (@gScaleA 1 (C1 / √ 2)%C ([(C1,[A])] ++ [((- C1)%C,[B])]))
            by (unfold gScaleA; simpl; rewrite ! Cmult_1_r; auto);
          constructor
      end;
    unfold anticommute_AType_semantic, translateA, translate;
    simpl; rewrite ! Mplus_0_l; rewrite ! kron_1_r; repeat rewrite ! Mscale_1_l; auto;
    distribute_scale; rewrite H4; lma'.
Qed.

Lemma TEN3' : forall {bit len : nat} (pm : Coef) {c c0 c1 : Coef} {l la lb : list Pauli} (P A B : Pauli),
    bit < len -> not_gI P -> not_gI A -> not_gI B -> anticommute_Pauli A B ->
    pm = C1 \/ pm = (- C1)%C -> len = length l -> P = nth bit l gI ->
    la = switch l A bit -> lb = switch l B bit ->
    c0 = ((C1/√2)*c)%C -> c1 = (pm * c * (C1/√2))%C ->
    @triple 1 (AtoPred [(C1, [P])]) (T 0) (AtoPred [((C1/√2)%C, [A]); (((C1/√2) * pm)%C, [B])]) ->
    @triple len (AtoPred [(c, l)]) (T bit) (AtoPred [(c0, la); (c1, lb)]).
Proof. intros bit len pm c c0 c1 l la lb A B P H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  assert (pm * c * (C1/√2) = (C1/√2)*(c * pm))%C by lca. rewrite H13 in H11.
  subst. apply TEN3; auto.
Qed.

Lemma TEN3'' :
  forall {bit n : nat} (pm : Coef) {c : Coef} {l : list Pauli} (P A B : Pauli)
    {t0 t1 : TType 1} {t2 t3 : TType n},
    bit < n -> not_gI P -> not_gI A -> not_gI B -> anticommute_Pauli A B ->
    pm = C1 \/ pm = (- C1)%C -> n = length l -> P = nth bit l gI ->
    t0 = ((C1/√2)%C, [A]) -> t1 = (((C1/√2) * pm)%C, [B]) ->
    t2 = (((C1/√2)*c)%C, switch l A bit) -> t3 = (((C1/√2)*(c * pm))%C, switch l B bit) ->
    @triple 1 (AtoPred [(C1, [P])]) (T 0) (AtoPred [t0; t1]) ->
    @triple n (AtoPred [(c, l)]) (T bit) (AtoPred [t2; t3]).
Proof. intros bit n pm c l A B P t0 t1 t2 t3 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  subst. apply TEN3; auto.
Qed.

Lemma TEN3''' :
  forall {bit n : nat} (pm : Coef) {c : Coef} {l : list Pauli} (P A B : Pauli)
    {a : AType 1} {a' : AType n},
    bit < n -> not_gI P -> not_gI A -> not_gI B -> anticommute_Pauli A B ->
    pm = C1 \/ pm = (- C1)%C -> n = length l -> P = nth bit l gI ->
    a = [((C1/√2)%C, [A]); (((C1/√2) * pm)%C, [B])] ->
    a' = [(((C1/√2)*c)%C, switch l A bit); (((C1/√2)*(c * pm))%C, switch l B bit)] ->
    @triple 1 (AtoPred [(C1, [P])]) (T 0) (AtoPred a) ->
    @triple n (AtoPred [(c, l)]) (T bit) (AtoPred a').
Proof. intros bit n pm c l A B P a a' H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  subst. apply TEN3; auto.
Qed.

Lemma WF_TEN5 : forall (bit len : nat) (pm c : Coef) (l : list Pauli) (A B : Pauli),
    bit < len -> not_gI A -> not_gI B -> anticommute_Pauli A B ->
    pm = C1 \/ pm = (- C1)%C -> len = length l -> c = C1 \/ c = (- C1)%C ->
    @WF_AType len [(((C1/√2)*c)%C, switch l A bit); (((C1/√2)*(c * pm))%C, switch l B bit)].
Proof. intros bit len pm c l A B H0 H1 H2 H3 H4 H5 H6. 
  replace [((C1 / √ 2 * c)%C, switch l A bit); ((C1 / √ 2 * (c * pm))%C, switch l B bit)]
    with (@gScaleA len (C1 / √ 2)%C ([(c,switch l A bit)] ++ [((c * pm)%C,switch l B bit)]))
    by (unfold gScaleA; auto).
  do 2 constructor.
  1 - 2 : constructor.
  - apply WF_TEN2; auto.
  - destruct H1;
      destruct H4 as [H4 | H4];
      rewrite H4;
      destruct H6 as [H6 | H6];
      rewrite H6;
      try rewrite Cmult_1_l;
      try rewrite Cmult_1_r;
      replace ((- C1)%C * (- C1)%C)%C with C1 by lca;
      apply WF_TEN2; auto.
  - subst; simpl.
    repeat (constructor; auto).
    rewrite ! switch_inc; auto.
    unfold cBigMul.
    setoid_rewrite <- zipWith_app_product with (n := bit) at 1.
    setoid_rewrite <- zipWith_app_product with (n := 1) at 1.
    setoid_rewrite <- zipWith_app_product with (n := bit) at 1.
    setoid_rewrite <- zipWith_app_product with (n := 1) at 1.
    rewrite ! fold_left_Cmult_app.
    replace (fold_left Cmult (zipWith gMul_Coef [A] [B]) C1)
      with (gMul_Coef A B)
      by (simpl; unfold uncurry; rewrite Cmult_1_l; auto).
    replace (fold_left Cmult (zipWith gMul_Coef [B] [A]) C1)
      with (gMul_Coef B A)
      by (simpl; unfold uncurry; rewrite Cmult_1_l; auto).
    rewrite Copp_mult_distr_r.
    rewrite Copp_mult_distr_l.
    do 2 f_equal.
    destruct H1 as [EA | [EA | EA]];
      destruct H2 as [EB | [EB | EB]];
      rewrite EA; rewrite EB;
      unfold gMul_Coef; simpl; try lca.
    1 - 3 : unfold anticommute_Pauli in H3;
    rewrite EA in H3; rewrite EB in H3;
    unfold translate_P in H3;
    rewrite Mscale_mult_dist_l in H3;
    try rewrite ! XtimesXid in H3;
    try rewrite ! YtimesYid in H3;
    try rewrite ! ZtimesZid in H3;
    contradict_matrix_equalities.
    all : try rewrite firstn_length;
      simpl; minmax_breakdown; auto.
Qed.


Lemma triple_A_eq : forall {n : nat} {pre  post : AType n} (pre' post' : AType n) {g : prog},
    pre' = pre -> post' = post ->
    {{ AtoPred pre' }} g {{ AtoPred post' }} -> {{ AtoPred pre }} g {{ AtoPred post }}.
Proof. intros n pre post pre' post' g H0 H1 H2.  
  subst. auto.
Qed.

Lemma triple_A_reorder_L : forall {n : nat} {a b : AType n} (a' : AType n) {g : prog},
    WF_AType a -> WF_AType b -> WF_AType a' ->
    translateA a' = translateA a -> {{ AtoPred a' }} g {{ AtoPred b }} -> {{ AtoPred a }} g {{ AtoPred b }}.
Proof. intros n a b a' g H0 H1 H2 H3 H4. 
  apply Heisenberg_Eigenvector_semantics.
  rewrite <- H3.
  apply Eigenvector_Heisenberg_semantics'; auto.
Qed.

Lemma triple_A_reorder_R : forall {n : nat} {a b : AType n} (b' : AType n) {g : prog},
    WF_AType a -> WF_AType b -> WF_AType b' ->
    translateA b' = translateA b -> {{ AtoPred a }} g {{ AtoPred b' }} -> {{ AtoPred a }} g {{ AtoPred b }}.
Proof. intros n a b b' g H0 H1 H2 H3 H4. 
  apply Heisenberg_Eigenvector_semantics.
  rewrite <- H3.
  apply Eigenvector_Heisenberg_semantics'; auto.
Qed.


Ltac trace_zero_auto listP :=
  match listP with
  | gI :: ?t => replace (gI :: t) with ([gI] ++ t) by auto;
              apply trace_zero_syntax_R; trace_zero_auto t
  | gX :: ?t => replace (gX :: t) with ([gX] ++ t) by auto;
              apply trace_zero_syntax_L; apply trace_zero_syntax_X
  | gY :: ?t => replace (gY :: t) with ([gY] ++ t) by auto;
              apply trace_zero_syntax_L; apply trace_zero_syntax_Y
  | gZ :: ?t => replace (gZ :: t) with ([gZ] ++ t) by auto;
              apply trace_zero_syntax_L; apply trace_zero_syntax_Z
  | nil => idtac
  end.


Ltac WF_auto :=
  repeat (match goal with
   | |- Forall2 _ [] [] => constructor
   | |- Forall2 _ _ [] => try constructor
   | |- Forall2 _ [] _ => try constructor
   | |- Forall WF_AType _ => constructor
   | |- Forall (fun ht : HoareTriple _ => circuit ht = _) _ =>
          constructor; try (rewrite circuit_packHT)
   | |- context [lincombCA _ _] => unfold lincombCA; repeat (simpl; repeat rewrite Cmult_assoc; try rewrite Cmult_neg1_mult; try rewrite Copp_involutive; Csimpl)
   | |- context [cBigMul (zipWith gMul_Coef _ _)] => 
       unfold cBigMul, zipWith, gMul_Coef, uncurry; simpl; Csimpl
    | |- WF_AType
          (gScaleA
             (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH))))))
             [?a; ?b]) =>
        auto with wf_db; constructor; replace [a; b] with 
           ([a] ++ [b]) by (simpl; auto); do 2 constructor
    | |- @WF_AType ?n [
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * ?c1)%C, ?l1);
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * ?c2)%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c1)%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c2)%C, l2)
          ] = (@gScaleA n
                     (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH))))))
                     [(c1, l1); (c2, l2)]))
      by (simpl; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l1);
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)
          ] = (@gScaleA n
                     (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH))))))
                     [(C1, l1); (C1, l2)]))
          by (simpl; rewrite ! Cmult_1_r; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * ?c1)%C, ?l1);
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c1)%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)
          ] = (@gScaleA n
                     (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH))))))
                     [(c1, l1); (C1, l2)]))
      by (simpl; rewrite ! Cmult_1_r; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l1);
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * ?c2)%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c2)%C, l2)
          ] = (@gScaleA n
                     (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH))))))
                     [(C1, l1); (c2, l2)]))
      by (simpl; rewrite Cmult_1_r; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            ((?c1 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l1);
            ((?c2 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              ((c1 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
              ((c2 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)
          ] = [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c1)%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c2)%C, l2)])
      by (rewrite Cmult_comm; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            ((?c1 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l1);
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              ((c1 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)
          ] = [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c1)%C, l1);
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)])
      by (rewrite Cmult_comm; auto); setoid_rewrite Htemp
    | |- @WF_AType ?n [
            (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l1);
            ((?c2 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, ?l2)
          ] =>
        auto with wf_db;
        let Htemp := fresh "Htemp" in
        assert (Htemp : [
              (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
              ((c2 * (Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l2)
          ] = [
                (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))))%C, l1);
                (((Cdiv (RtoC (IZR (Zpos xH))) (RtoC (sqrt (IZR (Zpos (xO xH)))))) * c2)%C, l2)])
          by (rewrite Cmult_comm; auto); setoid_rewrite Htemp
   | |- WF_AType (gScaleA _ [_]) => auto with wf_db; simpl
   | |- WF_AType [_] => auto with wf_db; do 2 constructor; simpl
   | |- WF_TType _ => auto with wf_db; constructor; simpl
   | |- proper_length_TType _ => constructor; simpl; try lia
   | |- coef_plus_minus_1 _ => unfold coef_plus_minus_1; simpl
   | |- _ <> C0 => try nonzero;
                let Htemp := fresh "Htemp" in
                intro Htemp;
                inversion Htemp; subst; clear Htemp;
                try lra
   | |- _ <> _ => let Htemp := fresh "Htemp" in
               intro Htemp;
               inversion Htemp; subst; clear Htemp;
               try lra
   | |- _ = C1 \/ _ = (- C1)%C => try (left; lca); try (right; lca)
   | |- C1 = _ => try lca
   | |- (- C1)%C = _ => try lca
   | |- trace_zero_syntax ?l => trace_zero_auto l
   | |- {{ AtoPred [(?c, _)] }} _ {{ AtoPred [(?c', _)] }} => 
       auto with ht_db; simpl; auto with ht_db; field_simplify c c'; Csimpl; auto with ht_db
   | |- {{ _ }} _ {{ AtoPred [(?c, _)] }} => 
       auto with ht_db; simpl; auto with ht_db; field_simplify c; Csimpl; auto with ht_db
   | |- {{ AtoPred [(?c, _)] }} ?g {{ _ }} => 
       match g with
       | T _ => auto with ht_db; simpl; auto with ht_db; Csimpl; auto with ht_db
       | _ => auto with ht_db; simpl; auto with ht_db; field_simplify c; Csimpl; auto with ht_db
       end
   | |- {{_}} _ {{_}} => repeat (simpl; auto with ht_db; repeat rewrite Cmult_assoc; try rewrite Cmult_neg1_mult; try rewrite Copp_involutive; Csimpl)
   | |- simpl_prog _ => try (left; easy); try (right; left; easy); try (right; right; easy)
   | |- _ /\ _ => split
   | |- _ \/ False => left
   | |- False \/ _ => right
   | |- not_gI _ => try (left; easy);
                           try (right; left; easy);
                           try (right; right; easy)
   | |- not_gI _ \/ not_gI _ =>
       try (left; left; easy);
       try (left; right; left; easy);
       try (left; right; right; easy);
       try (right; left; easy);
       try (right; right; left; easy);
       try (right; right; right; easy)
   | |- anticommute_AType_syntactic [] _ => simpl
   | |- anticommute_TType_AType _ _ => simpl
   | |- context [translateA _] =>
       simpl; unfold translateA;
       simpl; unfold translate;
       simpl; matrix_compute
   | |- anticommute_Pauli _ _ => unfold anticommute_Pauli; simpl; matrix_compute
   | |- _ < _ => simpl; auto; try lia
   | |- _ > _ => simpl; auto; try lia
   | |- _ = _ => repeat (simpl; auto; try field_simplify; try nonzero; try lca; f_equal)
   | |- _ => simpl
   end; auto).


(** Well-formedness for Pauli X, Y, Z **)

Lemma WF_TType_X : @WF_TType 1 tX. Proof. WF_auto. Qed.
Lemma WF_TType_Y : @WF_TType 1 tY. Proof. WF_auto. Qed.
Lemma WF_TType_Z : @WF_TType 1 tZ. Proof. WF_auto. Qed.
Lemma WF_TType_mX : @WF_TType 1 (mtX). Proof. WF_auto. Qed.
Lemma WF_TType_mY : @WF_TType 1 (mtY). Proof. WF_auto. Qed.
Lemma WF_TType_mZ : @WF_TType 1 (mtZ). Proof. WF_auto. Qed.
Lemma WF_AType_X : @WF_AType 1 aX. Proof. WF_auto. Qed.
Lemma WF_AType_Y : @WF_AType 1 aY. Proof. WF_auto. Qed.
Lemma WF_AType_Z : @WF_AType 1 aZ. Proof. WF_auto. Qed.
Lemma WF_AType_mX : @WF_AType 1 (maX). Proof. simpl. WF_auto. Qed.
Lemma WF_AType_mY : @WF_AType 1 (maY). Proof. WF_auto. Qed.
Lemma WF_AType_mZ : @WF_AType 1 (maZ). Proof. WF_auto. Qed.

#[export] Hint Resolve WF_TType_X WF_TType_Y WF_TType_Z WF_TType_mX WF_TType_mY WF_TType_mZ WF_AType_X WF_AType_Y WF_AType_Z WF_AType_mX WF_AType_mY WF_AType_mZ : wf_db.


(*** Core rules : use lma'
Non-core rules : use inference rules and core rules ***)

(** Core Rules **)

Lemma XHZ : {{ pX }} H 0 {{ pZ }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'; apply WF_mult; auto with wf_db;
    apply WF_Matrix_translateA;
    repeat apply proper_length_AType_gScaleA;
    repeat constructor;
    intro; lia.
Qed.

Lemma ZHX : {{ pZ }} H 0 {{ pX }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'; apply WF_mult; auto with wf_db;
    apply WF_Matrix_translateA;
    repeat apply proper_length_AType_gScaleA;
    repeat constructor;
    intro; lia.
Qed.

Lemma XSY : {{ pX }} S 0 {{ pY }}.
Proof. apply Heisenberg_Eigenvector_semantics; lma'; 
  unfold prog_simpl_app, translateA, translate, translate_P, Sgate;
    matrix_compute.
Qed.

Lemma ZSZ : {{ pZ }} S 0 {{ pZ }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'; apply WF_mult; auto with wf_db;
    apply WF_Matrix_translateA;
    repeat apply proper_length_AType_gScaleA;
    repeat constructor;
    intro; lia.
Qed.

Lemma ZTZ : {{ pZ }} T 0 {{ pZ }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'; apply WF_mult; auto with wf_db;
    apply WF_Matrix_translateA;
    repeat apply proper_length_AType_gScaleA;
    repeat constructor;
    intro; lia.
Qed.

Lemma XTXY2 : {{ pX }} T 0 {{ pXY2 }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'.
  
  1 : apply WF_mult; auto with wf_db;
  apply WF_Matrix_translateA;
  repeat apply proper_length_AType_gScaleA;
  repeat constructor;
  intro; lia.
  
  1 - 2 : unfold prog_simpl_app, translateA, translate, translate_P;
  matrix_compute.
Qed.
  
Lemma XTX2Y2 : {{ pX }} T 0 {{ pX2Y2 }}.
Proof. pose XTXY2 as H0.
  unfold gScaleA in H0.
  simpl in H0.
  rewrite ! Cmult_1_r in H0.
  assumption.
Qed.

Lemma YTYmX2 : {{ pY }} T 0 {{ pYmX2 }}.
Proof. apply Heisenberg_Eigenvector_semantics;
    lma'.
  
  1 : apply WF_mult; auto with wf_db;
  apply WF_Matrix_translateA;
  repeat apply proper_length_AType_gScaleA;
  repeat constructor;
  intro; lia.
  
  1 - 2 : unfold prog_simpl_app, translateA, translate, translate_P;
  matrix_compute.
Qed.

Lemma YTY2mX2 : {{ pY }} T 0 {{ pY2mX2 }}.
Proof. pose YTYmX2 as H0.
  unfold gScaleA in H0.
  simpl in H0.
  rewrite ! Cmult_1_r in H0.
  assumption.
Qed.
  
Lemma XICNOTXX : {{ pXI }} CNOT 0 1 {{ pXX }}.
Proof. apply Heisenberg_Eigenvector_semantics. simpl.
  unfold prog_ctrl_app, translateA, translate, translate_P. simpl.
  rewrite ! kron_1_l, ! kron_1_r, ! Mscale_1_l, ! Mplus_0_l;
    auto with wf_db.
  matrix_compute.
Qed.

Lemma IXCNOTIX : {{ pIX }} CNOT 0 1 {{ pIX }}.
Proof. apply Heisenberg_Eigenvector_semantics. simpl.
  unfold prog_ctrl_app, translateA, translate, translate_P. simpl.
  rewrite ! kron_1_l, ! kron_1_r, ! Mscale_1_l, ! Mplus_0_l;
    auto with wf_db.
  matrix_compute.
Qed.

Lemma ZICNOTZI : {{ pZI }} CNOT 0 1 {{ pZI }}.
Proof. apply Heisenberg_Eigenvector_semantics. simpl.
  unfold prog_ctrl_app, translateA, translate, translate_P. simpl.
  rewrite ! kron_1_l, ! kron_1_r, ! Mscale_1_l, ! Mplus_0_l;
    auto with wf_db.
  matrix_compute.
Qed.

Lemma IZCNOTZZ : {{ pIZ }} CNOT 0 1 {{ pZZ }}.
Proof. apply Heisenberg_Eigenvector_semantics. simpl.
  unfold prog_ctrl_app, translateA, translate, translate_P. simpl.
  rewrite ! kron_1_l, ! kron_1_r, ! Mscale_1_l, ! Mplus_0_l;
    auto with wf_db.
  matrix_compute.
Qed.

#[export] Hint Resolve XHZ ZHX XSY ZSZ ZTZ XTXY2 XTX2Y2 YTYmX2 YTY2mX2 XICNOTXX IXCNOTIX ZICNOTZI IZCNOTZZ : ht_db.


Tactic Notation "MUL_T_anticomm_auto"
  constr(pre1_T) constr(pre2_T) constr(post1_T) constr(post2_T) :=
  simpl;
  apply MUL_T_anticomm with (t0 := pre1_T) (t2 := pre2_T) (t1 := post1_T) (t3 := post2_T);
  WF_auto.

Tactic Notation "MUL_T_comm_auto"
  constr(pre1_T) constr(pre2_T) constr(post1_T) constr(post2_T) :=
  simpl;
  apply MUL_T_comm with (t0 := pre1_T) (t2 := pre2_T) (t1 := post1_T) (t3 := post2_T);
  WF_auto.

(** non-core triples **)

Lemma IHI : {{ pI }} H 0 {{ pI }}.
Proof. apply Heisenberg_Eigenvector_semantics.
  unfold translateA; simpl;
    unfold translate; simpl;
    rewrite Mplus_0_l, Mscale_1_l, kron_1_r;
    rewrite Mmult_1_l; try rewrite Mmult_1_r;
    replace 2%nat with (2 ^ 1)%nat by auto;
    auto with wf_db.
Qed.

Lemma ISI : {{ pI }} S 0 {{ pI }}.
Proof. apply Heisenberg_Eigenvector_semantics.
  unfold translateA; simpl;
    unfold translate; simpl;
    rewrite Mplus_0_l, Mscale_1_l, kron_1_r;
    rewrite Mmult_1_l; try rewrite Mmult_1_r;
    replace 2%nat with (2 ^ 1)%nat by auto;
    auto with wf_db.
Qed.

Lemma ITI : {{ pI }} T 0 {{ pI }}.
Proof. apply Heisenberg_Eigenvector_semantics.
  unfold translateA; simpl;
    unfold translate; simpl;
    rewrite Mplus_0_l, Mscale_1_l, kron_1_r;
    rewrite Mmult_1_l; try rewrite Mmult_1_r;
    replace 2%nat with (2 ^ 1)%nat by auto;
    auto with wf_db.
Qed.

Lemma IICNOTII : {{ pII }} CNOT 0 1 {{ pII }}.
Proof. apply Heisenberg_Eigenvector_semantics.
  unfold translateA; simpl;
    unfold translate; simpl;
    rewrite Mplus_0_l, Mscale_1_l, kron_1_r, ! id_kron;
    rewrite Mmult_1_l; try rewrite Mmult_1_r;
    auto; simpl; replace 4%nat with (2 ^ 2)%nat by auto;
    auto with wf_db.
Qed.

Lemma XTYX2 : {{ pX }} T 0 {{ pYX2 }}.
Proof. apply (triple_A_reorder_R aXY2); WF_auto. Qed.

Lemma XTY2X2 : {{ pX }} T 0 {{ pY2X2 }}.
Proof. apply (triple_A_reorder_R aX2Y2); WF_auto. Qed.

Lemma YTmXY2 : {{ pY }} T 0 {{ pmXY2 }}.
Proof. apply (triple_A_reorder_R aYmX2); WF_auto. Qed.

Lemma YTmX2Y2 : {{ pY }} T 0 {{ pmX2Y2 }}.
Proof. apply (triple_A_reorder_R aY2mX2); WF_auto. Qed.

Lemma YHmY : {{ pY }} H 0 {{ mpY }}.
Proof. MUL_T_anticomm_auto tX tZ tZ tX. Qed.

Lemma YSmX : {{ pY }} S 0 {{ mpX }}.
Proof. MUL_T_anticomm_auto tX tZ tY tZ. Qed.

Lemma XXCNOTXI : {{ pXX }} CNOT 0 1 {{ pXI }}.
Proof. MUL_T_comm_auto tXI tIX tXX tIX. Qed.

Lemma ZZCNOTIZ : {{ pZZ }} CNOT 0 1 {{ pIZ }}.
Proof. MUL_T_comm_auto tZI tIZ tZI tZZ. Qed.

Lemma YICNOTYX : {{ pYI }} CNOT 0 1 {{ pYX }}.
Proof. MUL_T_anticomm_auto tXI tZI tXX tZI. Qed.

Lemma IYCNOTZY : {{ pIY }} CNOT 0 1 {{ pZY }}.
Proof. MUL_T_anticomm_auto tIX tIZ tIX tZZ. Qed.

#[export] Hint Resolve IHI ISI ITI IICNOTII XTYX2 XTY2X2 YTmXY2 YTmX2Y2 YHmY YSmX XXCNOTXI ZZCNOTIZ YICNOTYX IYCNOTZY : ht_db.

Lemma YYCNOTmXZ : {{ pYY }} CNOT 0 1 {{ mpXZ }}.
Proof. MUL_T_comm_auto tYI tIY tYX tZY. Qed.

Lemma XYCNOTYZ : {{ pXY }} CNOT 0 1 {{ pYZ }}.
Proof. MUL_T_comm_auto tXI tIY tXX tZY. Qed.

Lemma XZCNOTYY : {{ pXZ }} CNOT 0 1 {{ mpYY }}.
Proof. MUL_T_comm_auto tXI tIZ tXX tZZ. Qed.

Lemma YXCNOTYI : {{ pYX }} CNOT 0 1 {{ pYI }}.
Proof. MUL_T_comm_auto tYI tIX tYX tIX. Qed.

Lemma YZCNOTXY : {{ pYZ }} CNOT 0 1 {{ pXY }}.
Proof. MUL_T_comm_auto tYI tIZ tYX tZZ. Qed.

Lemma ZXCNOTZX : {{ pZX }} CNOT 0 1 {{ pZX }}.
Proof. MUL_T_comm_auto tZI tIX tZI tIX. Qed.

Lemma ZYCNOTIY : {{ pZY }} CNOT 0 1 {{ pIY }}.
Proof. MUL_T_comm_auto tZI tIY tZI tZY. Qed.

#[export] Hint Resolve YYCNOTmXZ XYCNOTYZ XZCNOTYY YXCNOTYI YZCNOTXY ZXCNOTZX ZYCNOTIY : ht_db.


Definition Z (n : nat) := S n ;; S n.

Lemma ZZZ : {{ pZ }} Z 0 {{ pZ }}.
Proof. 
  eapply SEQ; auto with ht_db. 
Qed.

Lemma XZmX : {{ pX }} Z 0 {{ mpX }}.
Proof. 
  eapply SEQ; auto with ht_db. 
Qed.

Lemma YZmY : {{ pY }} Z 0 {{ mpY }}.
Proof. 
  eapply SEQ; auto with ht_db. 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

#[export] Hint Resolve ZZZ XZmX YZmY : ht_db.

Definition X (n : nat) := H n ;; Z n ;; H n.

Lemma XXX : {{ pX }} X 0 {{ pX }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db). 
Qed.

Lemma ZXmZ : {{ pZ }} X 0 {{ mpZ }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db). 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

Lemma YXmY : {{ pY }} X 0 {{ mpY }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db). 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

#[export] Hint Resolve XXX ZXmZ YXmY : ht_db.

Definition Y (n : nat) := S n ;; X n ;; Z n ;; S n.

Lemma XYmX : {{ pX }} Y 0 {{ mpX }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db). 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

Lemma ZYmZ : {{ pZ }} Y 0 {{ mpZ }}.
Proof. 
  apply SEQ with (B := pZ); auto with ht_db;
    apply SEQ with (B := mpZ); auto with ht_db.
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
  eapply SEQ; auto with ht_db. 
Qed.

Lemma YYY : {{ pY }} Y 0 {{ pY }}.
Proof. 
  apply SEQ with (B := mpX); auto with ht_db;
    apply SEQ with (B := mpX); auto with ht_db.
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
  eapply SEQ; auto with ht_db. 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

#[export] Hint Resolve XYmX ZYmZ YYY : ht_db. 

Definition Td (n : nat) := Z n ;; S n ;; T n.

Lemma ZTdZ : {{ pZ }} Td 0 {{ pZ }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db). 
Qed.

Lemma XTdXmY2 : {{ pX }} Td 0 {{ - pYmX2 }}.
Proof. 
  apply SEQ with (B := mpX); auto with ht_db;
    apply SEQ with (B := mpY); auto with ht_db. 
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
  eapply UNFLIP; auto with ht_db; do 2 WF_auto. 
Qed.

Lemma YTdXY2 : {{ pY }} Td 0 {{ pXY2 }}.
Proof. 
  repeat (eapply SEQ; auto with ht_db).
  eapply FLIP; auto with ht_db; do 2 WF_auto. 
Qed.

#[export] Hint Resolve ZTdZ XTdXmY2 YTdXY2 : ht_db. 

