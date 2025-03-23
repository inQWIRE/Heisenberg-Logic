Require Import QuantumLib.Eigenvectors.
Require Import HeisenbergFoundations.Preamble.



(* spectral decomposition *)
Definition WF_Spectral {n : nat} (A : Square n) : Prop :=
  WF_Matrix A /\ (exists (U D: Square n), 
    WF_Diagonal D /\ WF_Unitary U /\ D = U † × A × U).

Theorem unit_implies_spectral : forall {n} (A : Square n),
  WF_Unitary A -> WF_Spectral A.
Proof. intros n A H.
  unfold WF_Spectral.
  unfold WF_Unitary in H.
  destruct H.
  split; auto.
  assert (A † × A = A × A†).
  { rewrite H0. symmetry. apply Minv_flip; auto with wf_db. }
  destruct (Spectral_Theorem A H H1) as [U [WFUU WFDUdAU]].
  exists U. exists (U † × A × U).
  auto.
Qed.

Lemma spectral_eigenpairs_transfer : forall {n} (A D U : Square n),
WF_Matrix A -> WF_Diagonal D -> WF_Unitary U ->
  A = U × D × U† ->
  (forall x, (x < n)%nat -> Eigenpair A (U × (e_i x), D x x)).
Proof. intros n A D U H H0 H1 H2 x H3. destruct H1.
  apply (diagble_eigenpairs_transfer A D (U†) U); auto with wf_db.
  Qed.

Lemma big_sum_double_sum_comm : forall (f : nat -> nat -> C) (n m : nat),
    big_sum (fun x => (big_sum (fun y => f x y) n)) m = big_sum (fun y => (big_sum (fun x => f x y) m)) n.
Proof. induction n as [| n'].
  - setoid_rewrite big_sum_0_bounded; easy.
  - intros.
    destruct m as [| m'].
    + setoid_rewrite big_sum_0_bounded; easy.
    + rewrite 2 big_sum_extend_double.
      rewrite IHn'.
      lca.
Qed.

Lemma trace_cyclic : forall {n m : nat} (A : Matrix n m) (B : Matrix m n),
    trace (A × B) = trace (B × A).
Proof. intros.
  unfold trace, Mmult.
  rewrite big_sum_double_sum_comm.
  f_equal.
  apply functional_extensionality.
  intros.
  f_equal.
  apply functional_extensionality.
  intros.
  lca.
Qed.

Lemma hermitian_implies_real_diagonals : forall {n : nat} (A : Square n),
    A † = A -> (forall (i : nat), (i < n)%nat -> snd (A i i) = 0%R).
Proof. intros.
  unfold adjoint in H.
  apply equal_f with (x := i) in H.
  apply equal_f with (x := i) in H.
  unfold Cconj in H.
  destruct (A i i).
  inversion H.
  simpl in *.
  lra.
Qed.



Lemma Unitary_Hermitian_trace_zero_eigenvalues_plus_minus_1 : forall {n} (A : Square n),
  WF_Unitary A -> A † = A -> trace A = 0 ->
  (exists U D, WF_Diagonal D /\ WF_Unitary U /\ A = U × D × U† /\ trace D = C0 /\
  (forall x, (x < n)%nat -> Eigenpair A (U × (e_i x), D x x) /\ (D x x = C1 \/ D x x = (Copp C1)))).
Proof. intros n A WFUA HA TA.
  remember WFUA as WFSA. clear HeqWFSA.
  apply unit_implies_spectral in WFSA.
  destruct WFSA as [WFA [U [D [WFDD [WFUU H]]]]].
  remember H as  H'. clear HeqH'.
  remember WFUU as WFUU'. clear HeqWFUU'.
  destruct WFUU as [WFU UU].
  apply (@Mmult_inj_l n n n U) in H.
  rewrite <- ! Mmult_assoc in H.
  remember UU as UU'. clear HeqUU'.
  apply Minv_flip in UU'; auto with wf_db.
  rewrite UU' in H.
  rewrite Mmult_1_l in H; auto.
  apply (@Mmult_inj_r n n n (U†)) in H.
  setoid_rewrite Mmult_assoc in H at 2.
  rewrite UU' in H.
  rewrite Mmult_1_r in H; auto.
  remember WFDD as WFDD'. clear HeqWFDD'.
  destruct WFDD as [WFD DD].
  (exists U, D). repeat (split; auto).
  rewrite <- H in TA.
  rewrite trace_cyclic in TA.
  rewrite <- Mmult_assoc in TA.
  rewrite UU in TA.
  rewrite Mmult_1_l in TA; auto with wf_db.
  apply spectral_eigenpairs_transfer; auto.
  remember H' as H''. clear HeqH''.
  apply (@Mmult_inj_r n n n D) in H'.
  rewrite H'' in H' at 3.
  repeat setoid_rewrite <- Mmult_assoc in H'.
  setoid_rewrite Mmult_assoc in H' at 3.
  rewrite UU' in H'.
  rewrite Mmult_1_r in H'; auto with wf_db.
  destruct WFUA as [_ UA].
  rewrite HA in UA.
  setoid_rewrite Mmult_assoc in H' at 2.
  rewrite UA in H'.
  rewrite Mmult_1_r in H'; auto with wf_db.
  rewrite UU in H'.
  do 2 apply equal_f with (x := x) in H'.
  unfold I in H'.
  destruct (blt_reflect x n); try contradiction.
  destruct (beq_reflect x x); try contradiction.
  simpl in H'.
  unfold Mmult in H'.
  assert (H1 : (D x x) * (D x x) = C1).
  { rewrite <- H'. symmetry. apply big_sum_unique.
    (exists x). repeat (split; auto).
    intros.
    rewrite DD; auto.
    rewrite Cmult_0_l.
    reflexivity. }
  assert (H2 : D † = D).
  { rewrite ! H''.
    rewrite ! Mmult_adjoint.
    rewrite adjoint_involutive.
    rewrite HA.
    rewrite ! Mmult_assoc.
    reflexivity. }
  apply hermitian_implies_real_diagonals with (i := x) in H2; auto.
  destruct (D x x).
  simpl in H2.
  subst.
  unfold Cmult, C1 in H1.
  simpl in H1.
  inversion H1.
  autorewrite with R_db in *.
  clear H3.
  assert (r = 1 \/ r = -1).
  { nra. }
  destruct H.
  left. subst. lca.
  right. subst. lca.
Qed.






Module my_H.
  Definition H := I.
End my_H.

Import my_H.

(* denote successor as s instead of S since it overlaps with the S gate *)
Notation s := Datatypes.S.






Lemma Unitary_Hermitian_trace_zero_index_split : forall {n} (A : Square n),
    WF_Unitary A -> A † = A -> trace A = 0 ->
    (exists l1 l2 U D, Permutation (l1 ++ l2) (List.seq 0 n) /\
                    length l1 = length l2 /\ 
                    WF_Diagonal D /\ WF_Unitary U /\
                    A = U × D × U† /\ trace D = 0 /\
                    (forall x, In x l1 -> Eigenpair A (U × (e_i x), C1)) /\
                    (forall x, In x l2 -> Eigenpair A (U × (e_i x), Copp C1))).
Proof. intros n A WFUA HA TRA.
  specialize (Unitary_Hermitian_trace_zero_eigenvalues_plus_minus_1 A WFUA HA TRA); intros [U [D [WDDD [WFUU [SPECA [TRD0 EigenA_plus_minus_1]]]]]].

  assert (EigenA :  forall x : nat, (x < n)%nat -> Eigenpair A (U × e_i x, D x x)).
  { intros x H0.
    specialize (EigenA_plus_minus_1 x H0).
    destruct EigenA_plus_minus_1.
    assumption. }
  assert (plus_minus_1 :  forall x : nat, (x < n)%nat -> (D x x = C1 \/ D x x = (- C1)%C)).
  { intros x H0.
    specialize (EigenA_plus_minus_1 x H0).
    destruct EigenA_plus_minus_1.
    assumption. }
  
  assert (EigenA_in_seq : forall x:nat, In x (List.seq 0 n) -> Eigenpair A (U × e_i x, D x x)).
  { intros x H0.
    assert (x < n)%nat.
    { rewrite in_seq in H0. lia. }
    specialize (EigenA x H1).
    easy. }
  assert (plus_minus_1_in_seq : forall x:nat, In x (List.seq 0 n) -> D x x = C1 \/ D x x = (Copp C1)).
  { intros x H0.
    assert (x < n)%nat.
    { rewrite in_seq in H0. lia. }
    specialize (plus_minus_1 x H1).
    easy. }
  
  pose (plus1list_idx := filter (fun x:nat => Ceqb (D x x) C1) (List.seq 0 n)).
  pose (minus1list_idx := filter (fun x:nat => Ceqb (D x x) (Copp C1)) (List.seq 0 n)).
  pose (minus1list_idx_orth := filter (fun x:nat => negb (Ceqb (D x x) C1)) (List.seq 0 n)).

  pose (orth := seq_matrix_filter_disjoint2_is_orth n C1 (Copp C1) D).
  assert (plus_minus_1_different : C1 <> Copp C1).
  { intro. inversion H0. lra. }
  specialize (orth plus_minus_1_in_seq plus_minus_1_different).
  assert (minus1list_idx_orth_equal : minus1list_idx=minus1list_idx_orth).
  { apply orth. }

  pose (listD := map (fun x:nat => D x x) (List.seq 0 n)).
  pose (list_sum := fold_left Cplus listD C0).
  assert (trace_is_sum : list_sum = trace D).
  { clear -list_sum. 
    induction n.
    - simpl in *. easy.
    - unfold trace in *. simpl. rewrite <- IHn.
      unfold list_sum, listD.
      rewrite Cplus_comm.
      rewrite <- fold_left_Cplus.
      assert (H0: List.seq 0 (s n) = List.seq 0 n ++ [n]).
      { clear -n. pose list_seq_decompose.
        specialize (e n (s 0) 0%nat).
        simpl in e. rewrite <- plus_n_Sm in e. simpl in *.
        rewrite <- plus_n_O in e. easy. }
      rewrite H0. rewrite map_app. rewrite fold_left_Cplus_app.
      simpl. rewrite Cplus_0_l at 1. rewrite Cplus_comm.
      rewrite <- fold_left_Cplus. easy. }

  pose (plus1list := filter (fun c : C => Ceqb c C1) listD).
  pose (minus1list := filter (fun c : C => (Ceqb c (Copp C1))) listD).

  assert (plus_minus_1_in_listD : (forall x : C, In x listD -> x = C1 \/ x = (- C1)%C)).
  { intros.
    unfold listD in H0.
    rewrite in_map_iff in H0.
    do 2 destruct H0.
    rewrite <- H0.
    specialize (plus_minus_1_in_seq x0 H1).
    easy. }
    
  exists plus1list_idx, minus1list_idx, U, D.
  rewrite minus1list_idx_orth_equal.
  repeat (split; try easy).
  - apply Permutation_sym.
    apply seq_matrix_filter_orth_app_permutation.
  - rewrite <- minus1list_idx_orth_equal.
    rewrite <- ! map_length with (f := fun x:nat => D x x).
    assert (map_plus1list_idx: (map (fun x : nat => D x x) plus1list_idx) = plus1list).
    { apply map_filter_matrix_Ceqb_comm. }
    assert (map_minus1list_idx: (map (fun x : nat => D x x) minus1list_idx) = minus1list).
    { apply map_filter_matrix_Ceqb_comm. }
    rewrite map_plus1list_idx, map_minus1list_idx.
    rewrite TRD0 in trace_is_sum.
    pose (plusminus1list_sum_is_length_diff 0 listD plus_minus_1_in_listD trace_is_sum).
    rewrite Cplus_0_l in e.
    pose (INR_eq (length (filter (fun c : C => c =? C1) listD)) (length (filter (fun c : C => c =? - C1) listD))).
    inversion e.
    apply e0 in H1.
    easy.
  - intros.
    unfold plus1list_idx in H0.
    rewrite filter_In in H0.
    destruct H0.
    specialize (EigenA_in_seq x H0).
    unfold Ceqb in H1.
    destruct (Ceq_dec (D x x) C1); try discriminate.
    rewrite <- e.
    easy.
  - intros.
    rewrite <- minus1list_idx_orth_equal in H0.
    unfold minus1list_idx in H0.
    rewrite filter_In in H0.
    destruct H0.
    specialize (EigenA_in_seq x H0).
    unfold Ceqb in H1.
    destruct (Ceq_dec (D x x) (Copp C1)); try discriminate.
    rewrite <- e.
    easy.
Qed.




(** matrix_by_basis also exists **)
Lemma e_i_get_vec {n m : nat} (i : nat) (A : Matrix n m):
  WF_Matrix A -> A × e_i i = get_vec i A.
Proof. intros. unfold get_vec. unfold Mmult, e_i.
  apply functional_extensionality. intros.
  apply functional_extensionality. intros.
  bdestruct_all. 
  - assert ((fun y : nat => A x y * (if (y =? i)%nat && (y <? m) && true then C1 else 0)) =
              (fun y : nat => A x y * (if (y =? i)%nat && (y <? m) then C1 else 0))).
    { apply functional_extensionality. intros. rewrite andb_true_r. easy. }
    rewrite H2. clear H2.
    bdestruct (i <? m)%nat.
    + apply big_sum_unique.
      exists i.
      split; try easy.
      split.
      * bdestruct_all; try easy. simpl. lca.
      * intros. bdestruct_all; try easy.
        simpl. lca.
    + unfold WF_Matrix in H0.
      specialize (H0 x i).
      assert ((x >= n)%nat \/ (i >= m)%nat).
      { right. easy. }
      specialize (H0 H3).
      rewrite H0.
      assert ((fun y : nat => A x y * (if (y =? i)%nat && (y <? m) then C1 else 0)) =
                (fun y : nat => A x y * (if false then C1 else 0))).
      { apply functional_extensionality. intros. f_equal.
        bdestruct_all; easy. }
      rewrite H4.
      rewrite big_sum_0; try easy.
      intros. lca.
  - assert ((fun y : nat => A x y * (if (y =? i)%nat && (y <? m) && false then C1 else 0)) =
              (fun y : nat => A x y * (if false then C1 else 0))).
    { apply functional_extensionality. intros. f_equal.
      bdestruct_all; easy. }
    rewrite H2.
    rewrite big_sum_0; try easy.
    intros. lca.
Qed.




Import my_H.




(** ** matrix maniplulation for semantics ** **)

Definition list_vector_to_matrix {n} (l : list (Vector n)) : Matrix n (length l) := (fun r c : nat => (nth c l (@Zero n 1)) r 0%nat).
Check list_vector_to_matrix.

Lemma list_vector_to_matrix_col_wedge : forall {n} (x : Vector n) (l : list (Vector n)),
    list_vector_to_matrix (x :: l) = col_wedge (list_vector_to_matrix l) x 0.
Proof. intros n x l.
  unfold list_vector_to_matrix.
  simpl.
  unfold col_wedge. simpl.
  do 2 (apply functional_extensionality; intros).
  bdestruct_all.
  - rewrite H0.
    easy.
  - destruct x1.
    + contradiction.
    + assert (s x1 - 1 = x1)%nat.
      { lia. }
      rewrite H1.
      easy.
Qed.

Lemma WF_list_vector_to_matrix : forall {n} (l : list (Vector n)), Forall WF_Matrix l -> WF_Matrix (list_vector_to_matrix l).
Proof. intros n l H0.
  induction H0.
  - unfold WF_Matrix, list_vector_to_matrix.
    intros. simpl in *. destruct y; easy.
  - unfold WF_Matrix, list_vector_to_matrix.
    intros. simpl in *. destruct y.
    + destruct H2.
      * unfold WF_Matrix in H0.
        specialize (H0 x0 0%nat).
        assert ((x0 >= n)%nat \/ (0 >= 1)%nat).
        { left. easy. }
        specialize (H0 H3).
        easy.
      * lia.
    + destruct H2.
      * unfold list_vector_to_matrix in *.
        unfold WF_Matrix in IHForall.
        specialize (IHForall x0 y).
        assert ((x0 >= n)%nat \/ (y >= length l)%nat).
        { left. easy. }
        specialize (IHForall H3).
        easy.
      * assert (y >= length l)%nat.
        { lia. }
        rewrite nth_overflow; easy.
Qed.

Definition matrix_column_choose {n m} (indices_list : list nat) (M : Matrix n m) : Matrix n (length indices_list) := list_vector_to_matrix (map (fun i : nat => get_vec i M) indices_list).

Definition vector_row_choose {n} (indices_list : list nat) (v : Vector n) : Vector (length indices_list) := (fun r c : nat => v (nth r indices_list n) c).

Compute ((matrix_column_choose [] (I 3)) × (matrix_column_choose [] (I 3)) ⊤).
Compute ((I 0) 0%nat 0%nat).



Lemma matrix_column_choose_pop : forall {n m o} (indices_list : list nat) (M1 : Matrix m n) (M2 : Matrix n o), WF_Matrix M2 -> matrix_column_choose indices_list (M1 × M2) = M1 × (matrix_column_choose indices_list M2).
Proof. intros. unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  assert (Zero = @get_col m o (fun x1 z : nat => Σ (fun y : nat => M1 x1 y * M2 y z) n) o).
  { unfold WF_Matrix in H0.
    unfold get_vec.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all. 2: easy.
    rewrite big_sum_0. 1: easy.
    intros.
    specialize (H0 x3 o).
    assert ((x3 >= n)%nat \/ (o >= o)%nat). 1: right; lia.
    specialize (H0 H2).
    rewrite H0.
    lca. }
  rewrite H1.
  rewrite map_nth with (d := o).
  unfold get_vec.
  bdestruct_all.
  f_equal.
  apply functional_extensionality; intros.
  f_equal.
  assert (@Zero n o = (fun i0 x2 y : nat => if (y =? 0)%nat then M2 x2 i0 else 0) o).
  { do 2 (apply functional_extensionality; intros).
    bdestruct_all. 2: easy.
    unfold WF_Matrix in H0.
    specialize (H0 x2 o).
    assert ((x2 >= n)%nat \/ (o >= o)%nat). 1: right; lia.
    specialize (H0 H4).
    rewrite H0.
    easy. }
  setoid_rewrite H3.
  rewrite map_nth with (d := o).
  bdestruct_all.
  easy.
Qed.

Lemma   WF_Matrix_matrix_column_choose_indices_list_I_n: forall (n : nat) (indices_list : list nat),
    WF_Matrix (matrix_column_choose indices_list (I n)).
Proof. intros.
  unfold WF_Matrix.
  intros.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  assert (Zero = get_col (I n) n).
  { unfold get_col.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    unfold I.
    bdestruct_all; try easy. }
  rewrite H1.
  rewrite map_nth with (d := n).
  unfold get_col.
  bdestruct_all.
  destruct H0; unfold I; bdestruct_all; simpl; try easy.
  rewrite nth_overflow in H4; lia.
Qed.

Lemma WF_Matrix_matrix_column_choose_indices_list : forall {n m : nat} (indices_list : list nat) (M : Matrix n m), WF_Matrix M -> WF_Matrix (matrix_column_choose indices_list M).
Proof. intros.
  unfold WF_Matrix.
  intros.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  assert (Zero = get_col M m).
  { unfold get_col.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    unfold WF_Matrix in H0.
    assert ((x0 >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H0 x0 m H3).
    rewrite H0.
    trivial. }
  rewrite H2.
  rewrite map_nth with (d := m).
  unfold get_col.
  bdestruct_all.
  destruct H1.
  - unfold WF_Matrix in H0.
    assert ((x >= n)%nat \/ ((nth y indices_list m) >= m)%nat). { left. assumption. }
    specialize (H0 x (nth y indices_list m) H4).
    assumption.
  - rewrite nth_overflow.
    2 : lia.
    unfold WF_Matrix in H0.
    assert ((x >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H0 x m H4).
    assumption.
Qed.

Lemma  WF_Matrix_vector_row_choose_indices_list : forall {n : nat} (indices_list : list nat) (v : Vector n), WF_Matrix v -> WF_Matrix (vector_row_choose indices_list v).
Proof. intros.
  unfold WF_Matrix.
  intros.
  unfold vector_row_choose.
  destruct H1.
  - rewrite nth_overflow.
    2 : lia.
    unfold WF_Matrix in H0.
    assert ((n >= n)%nat \/ (y >= 1)%nat). { left. lia. }
    specialize (H0 n y H2).
    apply H0.
  - unfold WF_Matrix in H0.
    assert (((nth x indices_list n) >= n)%nat \/ (y >= 1)%nat). { right. assumption. }
    specialize (H0 (nth x indices_list n) y H2).
    apply H0.
Qed.

#[export] Hint Resolve WF_Matrix_matrix_column_choose_indices_list_I_n WF_Matrix_matrix_column_choose_indices_list WF_Matrix_vector_row_choose_indices_list : wf_db.

  
Lemma matrix_column_choose_inverse_r' : forall (n : nat) (indices_list : list nat),
    Permutation (List.seq 0 n) indices_list ->
    (matrix_column_choose indices_list (I n)) × (matrix_column_choose indices_list (I n)) ⊤ = I n.
Proof. intros.
  remember H0 as Perm. clear HeqPerm.
  unfold matrix_column_choose.
  unfold transpose. unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  unfold list_vector_to_matrix.

  assert (WF_Diagonal (I n)). 1: apply diag_I.
  unfold WF_Diagonal in H1. destruct H1.
  unfold WF_Matrix in H1.
  
  assert (Zero = get_vec n (I n)).
  { unfold WF_Matrix in H1.
    unfold get_col.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    rewrite H1; try easy; try lia. }
  rewrite H3.

  assert ((fun y : nat =>
     nth y (map (fun i0 : nat => get_vec i0 (I n)) indices_list) 
       (get_vec n (I n)) x 0%nat *
     nth y (map (fun i0 : nat => get_vec i0 (I n)) indices_list) 
       (get_vec n (I n)) x0 0%nat) =
            (fun y : nat =>
     get_vec (nth y indices_list n) (I n) x 0%nat *
  get_vec (nth y indices_list n) (I n) x0 0%nat)).
  { apply functional_extensionality; intros.
    rewrite map_nth with (d := n). easy. }
  rewrite H4.
  
  unfold get_vec.
  bdestruct_all.

  unfold I in H1, H2.
  unfold WF_Matrix in H0.
  unfold I.
  bdestruct_all.
  - simpl.
    rewrite H8.
    replace
      (fun y : nat =>
         (if (x0 =? nth y indices_list n)%nat && true then C1 else 0) *
           (if (x0 =? nth y indices_list n)%nat && true then C1 else 0))
      with
      (fun y : nat =>
         (if (x0 =? nth y indices_list n)%nat then C1 else 0) *
           (if (x0 =? nth y indices_list n)%nat then C1 else 0))
      by (apply functional_extensionality; intros; rewrite andb_true_r; easy).
    rewrite Permutation_nth in H0; try easy.
    destruct H0. destruct H9 as [f H9]. destruct H9. destruct H10.
    specialize (FinFun.bInjective_bSurjective H9). intros.
    rewrite H12 in H10.
    specialize (FinFun.bSurjective_bBijective H9 H10). intros.
    destruct H13 as [g H13].
    destruct H13.
    
    assert (FinFun.bInjective (length (List.seq 0 n)) g).
    { unfold FinFun.bInjective.
      intros.
      remember H14. clear Heqa.
      specialize (H14 x1 H15).
      specialize (a y H16).
      destruct H14.
      destruct a.
      apply f_equal with (f := f) in H17.
      rewrite H18, H20 in H17.
      easy. }
    specialize (FinFun.bInjective_bSurjective H13). intros.
    rewrite H16 in H15.
    
    apply big_sum_unique.

    exists (g x0). rewrite ! H0.
    remember H10 as bSurjective_f. clear HeqbSurjective_f.
    unfold FinFun.bSurjective in H10.
    specialize (seq_length n 0). intros.
    rewrite <- H17 in H6, H7.
    specialize (H10 x0 H7).
    destruct H10.
    destruct H10.
    apply f_equal with (f := g) in H18.
    remember H14. clear Heqa.
    specialize (a x1 H10).
    destruct a.
    rewrite H19 in H18.
    rewrite <- H18.
    split; try easy.
    split.
    + specialize (H11 x1 H10).
      rewrite H11.
      apply f_equal with (f := f) in H18.
      specialize (H14 x0 H7).
      destruct H14.
      rewrite H21 in H18.
      rewrite H18.
      rewrite seq_nth.
      bdestruct_all.
      lca.
      rewrite H17 in H7.
      easy.
    + intros.
      remember H14. clear Heqa.
      specialize (a x0 H7).
      destruct a.
      apply f_equal with (f := f) in H18.
      rewrite H24 in H18.
      rewrite <- H18.
      rewrite H11; try easy.
      rewrite seq_nth.
      2: { unfold FinFun.bSurjective in H15.
           specialize (H15 x' H21).
           destruct H15.
           destruct H15.
           specialize (H14 x2 H15).
           destruct H14.
           apply f_equal with (f := f) in H25.
           rewrite H26 in H25.
           rewrite <- H17.
           rewrite <- H25.
           easy. }
      bdestruct_all; try lca.
      rewrite Nat.add_0_l in H25.
      rewrite <- H12 in bSurjective_f.
      rename bSurjective_f into bInjective_f.
      unfold FinFun.bInjective in bInjective_f.
      specialize (bInjective_f x1 x' H10 H21).
      apply bInjective_f in H25.
      contradiction.
  - simpl.
    replace C0 with (big_sum (fun _ : nat => C0) (length indices_list)) at 1 by (rewrite big_sum_0; easy).
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all; simpl; lca.
  - simpl.
    replace C0 with (big_sum (fun _ : nat => C0) (length indices_list)) at 1 by (rewrite big_sum_0; easy).
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all; simpl; lca.
  - simpl.
    replace C0 with (big_sum (fun _ : nat => C0) (length indices_list)) at 1 by (rewrite big_sum_0; easy).
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all; simpl; lca.
  - simpl.
    replace C0 with (big_sum (fun _ : nat => C0) (length indices_list)) at 1 by (rewrite big_sum_0; easy).
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all; simpl; lca.
  - simpl.
    replace C0 with (big_sum (fun _ : nat => C0) (length indices_list)) at 1 by (rewrite big_sum_0; easy).
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all; simpl; lca.
Qed.

Lemma matrix_column_choose_inverse_l' : forall (n : nat) (indices_list : list nat),
    Permutation (List.seq 0 n) indices_list ->
    (matrix_column_choose indices_list (I n)) ⊤ × (matrix_column_choose indices_list (I n)) = I (length indices_list).
Proof. intros.
  remember H0 as Perm. clear HeqPerm.
  apply Permutation_length in H0.
  rewrite seq_length in H0. rewrite <- ! H0.
  apply Minv_flip.
  assert (@WF_Matrix n n (matrix_column_choose indices_list (I n)) =
            @WF_Matrix n (length indices_list) (matrix_column_choose indices_list (I n))).
  { rewrite <- H0. easy. }
  rewrite H1. apply WF_Matrix_matrix_column_choose_indices_list_I_n.
  apply WF_transpose.
  assert (@WF_Matrix n n (matrix_column_choose indices_list (I n)) =
            @WF_Matrix n (length indices_list) (matrix_column_choose indices_list (I n))).
  { rewrite <- H0. easy. }
  rewrite H1. apply WF_Matrix_matrix_column_choose_indices_list_I_n.
  assert (@eq (Matrix n n)
            (@Mmult n (@length nat indices_list) n
               (@matrix_column_choose n n indices_list (I n))
               (@transpose n (@length nat indices_list)
                  (@matrix_column_choose n n indices_list (I n)))) 
            (I n) =
            @eq (Matrix n n)
              (@Mmult n n n (@matrix_column_choose n n indices_list (I n))
                 (@transpose n n (@matrix_column_choose n n indices_list (I n)))) 
              (I n)).
  { rewrite <- H0. easy. }
  rewrite <- H1.
  apply matrix_column_choose_inverse_r'.
  easy.
Qed.

Lemma matrix_column_choose_I_n_adjoint_transpose : forall (n : nat) (indices_list : list nat),
    (matrix_column_choose indices_list (I n)) † =  (matrix_column_choose indices_list (I n)) ⊤.
Proof. intros. unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  unfold transpose, adjoint.
  do 2 (apply functional_extensionality; intros).
  assert (Zero = get_vec n (I n)).
  { unfold get_vec.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    unfold I.
    bdestruct_all; try easy. }
    rewrite H0.
  rewrite map_nth with (d := n).
  unfold get_vec.
  bdestruct_all.
  unfold I.
  bdestruct_all; simpl; lca.
Qed.

Lemma matrix_column_choose_inverse_r : forall (n : nat) (indices_list : list nat),
    Permutation (List.seq 0 n) indices_list ->
    (matrix_column_choose indices_list (I n)) × (matrix_column_choose indices_list (I n)) † = I n.
Proof. intros.
  rewrite matrix_column_choose_I_n_adjoint_transpose.
  apply matrix_column_choose_inverse_r'.
  easy.
Qed.

Lemma matrix_column_choose_inverse_l : forall (n : nat) (indices_list : list nat),
    Permutation (List.seq 0 n) indices_list ->
    (matrix_column_choose indices_list (I n)) † × (matrix_column_choose indices_list (I n)) = I (length indices_list).
Proof. intros.
  rewrite matrix_column_choose_I_n_adjoint_transpose.
  apply matrix_column_choose_inverse_l'.
  easy.
Qed.

(** 
     0    1   0       0  1  0  0
     1    0   0       1  0  0  0
     0    0   1       0  0  1  0
     0    0   0
*)


Lemma matrix_column_choose_app_smash : forall {n m} (list1 list2 : list nat) (M : Matrix n m), WF_Matrix M -> matrix_column_choose (list1 ++ list2) M = smash (matrix_column_choose list1 M) (matrix_column_choose list2 M).
Proof. intros. unfold matrix_column_choose. unfold smash.
  unfold list_vector_to_matrix.
  do 2 (apply functional_extensionality; intros).
  (*** You can get rid of this by splitting cases on x0 <? length indices_list, and using nth_indep & nth_overflow ***)
  assert (Zero = get_vec m M).
  { unfold WF_Matrix in H0.
    unfold get_vec.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all. 2: easy.
    specialize (H0 x1 m).
    assert ((x1 >= n)%nat \/ (m >= m)%nat). 1: right; lia.
    specialize (H0 H2).
    rewrite H0.
    easy. }
  rewrite ! H1.
  rewrite ! map_nth with (d := m).
  bdestruct_all.
  - f_equal. apply app_nth1; easy.
  - f_equal. apply app_nth2; easy.
Qed.




Lemma matrix_column_choose_vector_row_choose_original : forall {n m} (indices_list : list nat) (M : Matrix n m) (v : Vector m),
    WF_Matrix M ->
    Permutation (List.seq 0 m) indices_list ->
    (matrix_column_choose indices_list M)
      × (vector_row_choose indices_list v) = M × v. (** = Σ_i M_i v_i **)
Proof. intros.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  unfold vector_row_choose.
  unfold Mmult.
  do 2 (apply functional_extensionality; intros).

  remember H1 as H2. clear HeqH2.
  apply Permutation_length in H2.
  rewrite seq_length in H2.
  symmetry in H2.
  rewrite H2.
  (*** You can get rid of this by splitting cases on y <? length indices_list, and using nth_indep & nth_overflow ***)
  assert (Zero = get_vec m M).
  { unfold WF_Matrix in H0.
    unfold get_vec.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all. 2: easy.
    specialize (H0 x1 m).
    assert ((x1 >= n)%nat \/ (m >= m)%nat). 1: right; lia.
    specialize (H0 H4).
    rewrite H0.
    easy. }
  rewrite H3.

  assert ((fun y : nat =>
             nth y (map (fun i0 : nat => get_vec i0 M) indices_list) (get_vec m M) x 0%nat *
               v (nth y indices_list m) x0) =
            (fun y : nat =>
                get_vec (nth y indices_list m) M x 0%nat * v (nth y indices_list m) x0)).
  { apply functional_extensionality; intros.
    rewrite map_nth with (d := m). easy. }
  rewrite H4.
  unfold get_vec.
  bdestruct_all.

  rewrite big_sum_permutation with (A := nat) (d := m) (l1 := indices_list) (f := (fun y : nat => M x y * v y x0)) (l2 := List.seq 0 m).

  - apply big_sum_eq_bounded.
    intros.
    rewrite seq_nth; easy.
  - apply Permutation_sym in H1. easy.
  - lia.
Qed.


Lemma matrix_column_choose_pop_square : forall {n} (indices_list : list nat) (M1 M2 : Square n), WF_Matrix M2 -> matrix_column_choose indices_list (M1 × M2) = M1 × (matrix_column_choose indices_list M2).
Proof. intros. rewrite <- matrix_column_choose_pop; auto with wf_db.
Qed.

Lemma matrix_column_choose_pop_square_id : forall {n} (indices_list : list nat) (M : Square n), WF_Matrix M -> matrix_column_choose indices_list M = M × (matrix_column_choose indices_list (I n)).
Proof. intros. rewrite <- matrix_column_choose_pop; auto with wf_db.
  rewrite Mmult_1_r; auto with wf_db.
Qed.

Lemma vector_row_choose_matrix_column_choose : forall (n : nat) (v : Vector n) (indices_list : list nat),
    WF_Matrix v ->
    (vector_row_choose indices_list v) = (matrix_column_choose indices_list (I n)) ⊤ × v.
Proof. intros. unfold vector_row_choose.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  unfold transpose, Mmult.
  do 2 (apply functional_extensionality; intros).

  assert (Zero = get_vec n (I n)).
  { unfold get_vec.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all. 2: easy.
    unfold I.
    bdestruct_all; simpl; easy. }

  assert ((fun y : nat =>
     nth x (map (fun i0 : nat => get_vec i0 (I n)) indices_list) Zero y 0%nat *
     v y x0) = (fun y : nat => get_vec (nth x indices_list n) (I n) y 0%nat * v y x0)).
  { rewrite H1.
    rewrite map_nth with (d := n).
    easy. }
  rewrite H2.

  unfold get_vec.
  bdestruct_all.
  bdestruct ((nth x indices_list n) <? n).
  - rewrite big_sum_unique with (k := v (nth x indices_list n) x0); try easy.
    exists (nth x indices_list n). split; try easy.
    split.
    + unfold I. bdestruct_all. simpl. lca.
    + intros. unfold I. bdestruct_all. simpl. lca.
  - unfold WF_Matrix in H0.
    rewrite H0. 2: left; assumption.
    rewrite big_sum_0; try easy.
    intros.
    unfold I.
    bdestruct_all; simpl; lca.
Qed.


Definition selective_diagonal (n : nat) (indices_list : list nat): Square n :=
  fun x y => if (x =? y)%nat && (x <? n) && (is_in_nat_list x indices_list) then C1 else 0.

Lemma WF_selective_diagonal : forall (n : nat) (indices_list : list nat),
    WF_Matrix (selective_diagonal n indices_list).
Proof. unfold WF_Matrix. intros.
  unfold selective_diagonal.
  destruct H0.
  bdestruct_all; simpl; trivial.
  destruct ((x =? y)%nat) eqn:E; trivial.
  rewrite Nat.eqb_eq in E.
  subst.
  bdestruct_all.
  trivial.
Qed.

#[export] Hint Resolve WF_selective_diagonal : wf_db.

Lemma selective_diagonal_permutation_identity : forall (n : nat) (indices_list : list nat),
    Permutation (List.seq 0 n) indices_list ->
    I n = selective_diagonal n indices_list.
Proof. intros. unfold I. unfold selective_diagonal.
  do 2 (apply functional_extensionality; intros).
  bdestruct_all; simpl; trivial.
  assert (0 <= x < 0 + n)%nat.
  { lia. }
  rewrite <- in_seq in H3.
  apply Permutation_in with (l := (List.seq 0 n)) (l' := indices_list) in H3; trivial.
  unfold is_in_nat_list.
  assert (exists y : nat, In y indices_list /\ ((fun m : nat => (x =? m)%nat) y = true)).
  { exists x. split; bdestruct_all; trivial. }
  rewrite <- existsb_exists with (f := (fun m : nat => (x =? m)%nat)) (l := indices_list) in H4.
  rewrite H4.
  reflexivity.
Qed.

Lemma matrix_column_choose_selective_diagonal : forall (n : nat) (indices_list : list nat),
    NoDup indices_list ->
    (matrix_column_choose indices_list (I n)) × (matrix_column_choose indices_list (I n)) ⊤ = selective_diagonal n indices_list.
Proof. intros n indices_list H'.  unfold matrix_column_choose. unfold list_vector_to_matrix.
  unfold selective_diagonal.
  unfold transpose, Mmult.
  do 2 (apply functional_extensionality; intros).
  assert (Zero = get_vec n (I n)).
  { unfold get_vec, I.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; simpl; lca. }
  rewrite ! H0.
  assert ((fun y : nat =>
             nth y (map (fun i0 : nat => get_vec i0 (I n)) indices_list) 
               (get_vec n (I n)) x 0%nat *
               nth y (map (fun i0 : nat => get_vec i0 (I n)) indices_list) 
                 (get_vec n (I n)) x0 0%nat) =
            (fun y : nat =>
               get_vec (nth y indices_list n) (I n) x 0%nat *
                 get_vec (nth y indices_list n) (I n) x0 0%nat)).
  { apply functional_extensionality; intros.
    rewrite map_nth with (d := n). easy. }
  rewrite H1.
  unfold get_vec.
  bdestruct (0 =? 0)%nat.
  2: contradiction.
  unfold I.
  bdestruct_all; simpl.
  - assert ((fun y : nat =>
               (if (x =? nth y indices_list n)%nat && true then C1 else 0) *
                 (if (x0 =? nth y indices_list n)%nat && true then C1 else 0)) =
              (fun y : nat =>
                 (if (x =? nth y indices_list n)%nat then C1 else 0))).
    { rewrite H5.
      apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    unfold is_in_nat_list.
    clear - H'.
    destruct (existsb (fun m : nat => (x =? m)%nat) indices_list) eqn:E.
    + apply big_sum_unique.
      apply existsb_exists in E.
      destruct E. destruct H0.
      apply Nat.eqb_eq in H1.
      apply In_nth with (x := x0) (l := indices_list) (d := n) in H0; trivial.
      destruct H0. destruct H0.
      exists x1. split; trivial.
      split.
      * rewrite H1. bdestruct_all; easy.
      * intros.
        bdestruct_all; trivial.
        rewrite H1 in H5. symmetry in H5.
        rewrite NoDup_nth in H'.
        rewrite <- H5 in H2.
        specialize (H' x1 x' H0 H3 H2).
        contradiction.
    + assert (C0 =  Σ (fun _ : nat => 0) (length indices_list)).
      { rewrite big_sum_0; easy. }
      rewrite H0.
      apply big_sum_eq_bounded.
      intros.
      rewrite existsb_nth; trivial.
      setoid_rewrite H0 at 2.
      reflexivity.
  - assert ((fun y : nat =>
               (if (x =? nth y indices_list n)%nat && true then C1 else 0) *
                 (if (x0 =? nth y indices_list n)%nat && true then C1 else 0)) =
              (fun y : nat => 0)).
    { apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    rewrite big_sum_0; easy.
  - assert ((fun y : nat =>
               (if (x =? nth y indices_list n)%nat && true then C1 else 0) *
                 (if (x0 =? nth y indices_list n)%nat && false then C1 else 0)) =
              (fun y : nat => 0)).
    { apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    rewrite big_sum_0; easy.
  - assert ((fun y : nat =>
               (if (x =? nth y indices_list n)%nat && false then C1 else 0) *
                 (if (x0 =? nth y indices_list n)%nat && true then C1 else 0)) =
              (fun y : nat => 0)).
    { apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    rewrite big_sum_0; easy.
  - assert ((fun y : nat =>
               (if (x =? nth y indices_list n)%nat && false then C1 else 0) *
                 (if (x0 =? nth y indices_list n)%nat && false then C1 else 0)) =
              (fun y : nat => 0)).
    { apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    rewrite big_sum_0; easy.
  - assert ((fun y : nat =>
     (if (x =? nth y indices_list n)%nat && false then C1 else 0) *
     (if (x0 =? nth y indices_list n)%nat && false then C1 else 0)) =
              (fun y : nat => 0)).
    { apply functional_extensionality; intros.
      bdestruct_all; simpl; lca. }
    rewrite H6.
    rewrite big_sum_0; easy.
Qed.



Lemma selective_diagonal_app_split : forall (n : nat) (list1 list2 : list nat),
    NoDup (list1 ++ list2) ->
    selective_diagonal n (list1 ++ list2) = selective_diagonal n list1 .+ selective_diagonal n list2.
Proof. intros. unfold selective_diagonal.
  unfold Mplus.
  do 2 (apply functional_extensionality; intros).
  bdestruct_all; simpl; try lca.
  unfold is_in_nat_list.
  destruct (existsb (fun m : nat => (x =? m)%nat) (list1 ++ list2)) eqn:E.
  - rewrite existsb_app in E.
    rewrite orb_true_iff in E.
    destruct E.
    + rewrite H3.
      rewrite existsb_exists in H3.
      destruct H3. destruct H3.
      apply NoDup_app_in_neg_r with (a := x1) in H0; trivial.
      rewrite Nat.eqb_eq in H4.
      rewrite H4.
      destruct (existsb (fun m : nat => (x1 =? m)%nat) list2) eqn:E; try lca.
      rewrite existsb_exists in E.
      destruct E. destruct H5.
      rewrite Nat.eqb_eq in H6.
      rewrite H6 in H0.
      contradiction.
    + rewrite H3.
      rewrite existsb_exists in H3.
      destruct H3. destruct H3.
      apply NoDup_app_in_neg_l with (a := x1) in H0; trivial.
      rewrite Nat.eqb_eq in H4.
      rewrite H4.
      destruct (existsb (fun m : nat => (x1 =? m)%nat) list1) eqn:E; try lca.
      rewrite existsb_exists in E.
      destruct E. destruct H5.
      rewrite Nat.eqb_eq in H6.
      rewrite H6 in H0.
      contradiction.
  - rewrite existsb_app in E.
    rewrite orb_false_iff in E.
    destruct E.
    rewrite H3, H4.
    lca.
Qed.

Lemma matrix_column_choose_I_n_app_split : forall (n : nat) (list1 list2 : list nat),
    NoDup (list1 ++ list2) ->
    (matrix_column_choose (list1 ++ list2) (I n)) × (matrix_column_choose (list1 ++ list2) (I n)) ⊤ = (matrix_column_choose (list1) (I n)) × (matrix_column_choose (list1) (I n)) ⊤ .+ (matrix_column_choose (list2) (I n)) × (matrix_column_choose (list2) (I n)) ⊤.
Proof. intros.
  remember H0. clear Heqn0.
  remember H0. clear Heqn1.
  apply NoDup_app_remove_l in n0.
  apply NoDup_app_remove_r in n1.
  rewrite ! matrix_column_choose_selective_diagonal; trivial.
  rewrite selective_diagonal_app_split; trivial.
Qed.

Lemma matrix_column_choose_vector_row_choose_app_split : forall {n} (list1 list2 : list nat) (M : Square n) (v : Vector n),
    WF_Matrix M -> WF_Matrix v -> NoDup (list1 ++ list2) ->
    Permutation (list1 ++ list2) (List.seq 0 n) ->
    (matrix_column_choose (list1 ++ list2) M)
      × (vector_row_choose (list1 ++ list2) v) =
      ((matrix_column_choose list1 M)
         × (vector_row_choose list1 v)) .+
        ((matrix_column_choose list2 M)
           × (vector_row_choose list2 v)).
Proof. intros.
  rewrite matrix_column_choose_pop_square_id.
  rewrite vector_row_choose_matrix_column_choose.
  assert (M × matrix_column_choose (list1 ++ list2) (I n)
            × ((matrix_column_choose (list1 ++ list2) (I n)) ⊤ × v) =
            M × (matrix_column_choose (list1 ++ list2) (I n)
                   × (matrix_column_choose (list1 ++ list2) (I n)) ⊤) × v).
  { rewrite ! Mmult_assoc. easy. }
  rewrite H4.
  rewrite matrix_column_choose_I_n_app_split.
  rewrite Mmult_plus_distr_l.
  rewrite <- ! Mmult_assoc.
  rewrite <- ! matrix_column_choose_pop_square_id.
  rewrite Mmult_plus_distr_r.
  rewrite ! Mmult_assoc.
  rewrite <- ! vector_row_choose_matrix_column_choose.
  easy.
  all: assumption.
Qed.


Lemma matrix_column_choose_vector_row_choose_selective_diagonal :
  forall {n} (indices_list : list nat) (M : Square n) (v : Vector n),
    NoDup indices_list -> WF_Matrix M -> WF_Matrix v ->
    matrix_column_choose indices_list M × vector_row_choose indices_list v
    = M × selective_diagonal n indices_list × v.
Proof. intros.
  rewrite matrix_column_choose_pop_square_id.
  rewrite vector_row_choose_matrix_column_choose.
  replace (M × matrix_column_choose indices_list (I n)
             × ((matrix_column_choose indices_list (I n)) ⊤ × v))
    with (M × (matrix_column_choose indices_list (I n)
                 × (matrix_column_choose indices_list (I n)) ⊤) × v)
    by (rewrite <- ! Mmult_assoc; reflexivity).
  rewrite matrix_column_choose_selective_diagonal.
  all: trivial.
Qed.



Lemma selective_diagonal_idempotent : forall (n : nat) (indices_list : list nat), selective_diagonal n indices_list × selective_diagonal n indices_list = selective_diagonal n indices_list.
Proof. intros. unfold selective_diagonal. unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  bdestruct_all; simpl.
  - subst. destruct (is_in_nat_list x0 indices_list) eqn:E.
    + apply big_sum_unique.
      exists x0. repeat split; trivial.
      * bdestruct_all; simpl. rewrite E. lca.
      * intros. bdestruct_all; simpl; lca.
    + apply @big_sum_0 with (H := C_is_monoid).
      intros. bdestruct_all; simpl; lca.
  - apply @big_sum_0 with (H := C_is_monoid).
    intros. bdestruct_all; simpl; lca.
  - apply @big_sum_0 with (H := C_is_monoid).
    intros. bdestruct_all; simpl; lca.
  - apply @big_sum_0 with (H := C_is_monoid).
    intros. bdestruct_all; simpl; lca.
Qed.

Lemma selective_diagonal_orth : forall (n : nat) (list1 list2 : list nat),
    NoDup (list1 ++ list2) ->
    selective_diagonal n list1 × selective_diagonal n list2 = @Zero n n.
Proof. intros.
  unfold selective_diagonal. unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  
  replace (@Zero n n x x0) with C0 by lca.
  apply @big_sum_0_bounded with (H := C_is_monoid).
  intros.
  bdestruct_all; simpl; try lca.
  subst.
  destruct (is_in_nat_list x0 list1) eqn:E1; try lca.
  destruct (is_in_nat_list x0 list2) eqn:E2; try lca.
  unfold is_in_nat_list in *.
  rewrite existsb_exists in *.
  destruct E1, E2.
  destruct H4, H5.
  rewrite Nat.eqb_eq in *.
  subst.
  pose (NoDup_app_in_neg_l nat x1 list1 list2 H0 H5).
  contradiction.
Qed.


Lemma selective_diagonal_adjoint_transpose : forall (n : nat) (indices_list : list nat),
    (selective_diagonal n indices_list) † = (selective_diagonal n indices_list) ⊤.
Proof. intros.
  unfold adjoint, transpose.
  do 2 (apply functional_extensionality; intros).
  unfold selective_diagonal.
  bdestruct_all; simpl; try lca.
  destruct (is_in_nat_list x0 indices_list) eqn:E; lca.
Qed.
  
Lemma selective_diagonal_symmetric : forall (n : nat) (indices_list : list nat),
    (selective_diagonal n indices_list) ⊤ = selective_diagonal n indices_list.
Proof. intros.
  unfold adjoint, transpose.
  do 2 (apply functional_extensionality; intros).
  unfold selective_diagonal.
  bdestruct_all; simpl; try lca.
  subst.
  destruct (is_in_nat_list x indices_list) eqn:E; lca.
Qed.

Lemma selective_diagonal_hermitian : forall (n : nat) (indices_list : list nat),
    (selective_diagonal n indices_list) † = selective_diagonal n indices_list.
Proof. intros.
  rewrite selective_diagonal_adjoint_transpose.
  apply selective_diagonal_symmetric.
Qed.

Lemma selective_diagonal_e_i_identity : forall (n i : nat) (indices_list : list nat),
    In i indices_list -> selective_diagonal n indices_list × e_i i = e_i i.
Proof. intros.
  unfold selective_diagonal.
  unfold e_i.
  unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  assert ((fun y : nat =>
             (if (x =? y)%nat && (x =? i)%nat && (x <? n) && (x0 =? 0)%nat &&
                   is_in_nat_list x indices_list then C1 else 0))
         =
           (fun y : nat =>
              (if (x =? y)%nat && (x <? n) && is_in_nat_list x indices_list then C1 else 0) *
                (if (y =? i)%nat && (y <? n) && (x0 =? 0)%nat then C1 else 0))).
  { apply functional_extensionality; intros. 
    bdestruct_all; simpl; try lca; subst. }
  rewrite <- H1.
  bdestruct_all; simpl.
  2-8: apply @big_sum_0 with (H := C_is_monoid); intros; bdestruct_all; simpl; lca.
  subst.
  apply @big_sum_unique with (H := C_is_monoid).
  exists i.
  split; trivial.
  split; bdestruct_all.
  - simpl. destruct (is_in_nat_list i indices_list) eqn:E; try lca.
    unfold is_in_nat_list in E.
    assert (exists x : nat, In x indices_list /\ (fun m : nat => (i =? m)%nat) x = true).
    { exists i. split; trivial. rewrite Nat.eqb_eq. trivial. }
    rewrite <- existsb_exists in H4.
    rewrite H4 in E.
    discriminate.
  - intros. bdestruct_all. simpl. trivial.
Qed.

Lemma selective_diagonal_e_i_zero : forall (n i : nat) (indices_list : list nat),
    ~ In i indices_list -> selective_diagonal n indices_list × e_i i = Zero.
Proof. intros.
  unfold selective_diagonal.
  unfold e_i.
  unfold Mmult.
  do 2 (apply functional_extensionality; intros).
  assert ((fun y : nat =>
             (if (x =? y)%nat && (x =? i)%nat && (x <? n) && (x0 =? 0)%nat &&
                   is_in_nat_list x indices_list then C1 else 0))
         =
           (fun y : nat =>
              (if (x =? y)%nat && (x <? n) && is_in_nat_list x indices_list then C1 else 0) *
                (if (y =? i)%nat && (y <? n) && (x0 =? 0)%nat then C1 else 0))).
  { apply functional_extensionality; intros. 
    bdestruct_all; simpl; try lca; subst. }
  rewrite <- H1.
  bdestruct_all; simpl.
  2-8: apply @big_sum_0 with (H := C_is_monoid); intros; bdestruct_all; simpl; lca.
  subst.
  apply @big_sum_unique with (H := C_is_monoid).
  exists i.
  split; trivial.
  split; bdestruct_all.
  - simpl. destruct (is_in_nat_list i indices_list) eqn:E; try lca.
    unfold is_in_nat_list in E.
    rewrite existsb_exists in E.
    destruct E.
    destruct H4.
    rewrite Nat.eqb_eq in H5.
    subst.
    contradiction.
  - intros. bdestruct_all. simpl. trivial.
Qed.


Lemma eigenpair_to_selective_diagonal : forall {n} (indices_list : list nat) (c : C) (M1 M2 M3 : Square n),
    WF_Matrix M2 -> WF_Matrix M3 -> 
    (forall x : nat, In x indices_list -> Eigenpair M1 (M2 × M3 × e_i x, c)) ->  
    (M1 × M2 × M3 × selective_diagonal n indices_list × (M3) †
     = c .* M2 × M3 × selective_diagonal n indices_list × (M3) †).
Proof. intros. 
  unfold Eigenpair in H2. simpl in H2.
  setoid_rewrite e_i_get_vec in H2; auto with wf_db.

  do 2 (apply functional_extensionality; intros).
  unfold Matrix.scale, Mmult in *. unfold get_vec in *.
  unfold selective_diagonal in *.
  f_equal.
  apply functional_extensionality; intros.
  
  do 2 f_equal.
  apply functional_extensionality; intros.

  destruct (is_in_nat_list x2 indices_list) eqn:E.
  - unfold is_in_nat_list in E.
    rewrite existsb_exists in E.
    destruct E as [x4 [H3 H4]].
    rewrite Nat.eqb_eq in H4.
    subst.
    specialize (H2 x4 H3).
    apply f_equal_inv with (x := x) in H2.
    apply f_equal_inv with (x := 0%nat) in H2.
    simpl in H2.

    f_equal.

    assert ((fun y : nat => (c * M2 x y) * M3 y x4) = (fun y : nat => c * (M2 x y * M3 y x4))).
    { apply functional_extensionality; intros. lca. }
    rewrite H4.
    
    rewrite @big_sum_mult_l with (R := C) (H := C_is_monoid) (H0 := C_is_group) (H1 := C_is_comm_group) (H2 := C_is_ring) in H2.
    rewrite <- @big_sum_mult_l with (R := C) (H := C_is_monoid) (H0 := C_is_group) (H1 := C_is_comm_group) (H2 := C_is_ring).
    rewrite @big_sum_mult_l with (R := C) (H := C_is_monoid) (H0 := C_is_group) (H1 := C_is_comm_group) (H2 := C_is_ring).
    rewrite <- H2.
    
    pose (Mmult_assoc M1 M2 M3) as e.
    unfold Mmult in e.
    apply f_equal_inv with (x := x) in e.
    apply f_equal_inv with (x := x4) in e.
    apply e.
  - bdestruct_all; simpl; lca.
Qed.
  
  
Lemma eigenpair_to_selective_diagonal' : forall {n} (indices_list : list nat) (c : C) (M1 M2 : Square n),
    WF_Matrix M2 -> 
    ((forall i : nat, In i indices_list -> Eigenpair M1 (M2 × e_i i, c)) ->
    M1 × M2 × (selective_diagonal n indices_list) = c .* M2 × selective_diagonal n indices_list).
Proof. intros. pose (eigenpair_to_selective_diagonal indices_list c M1 M2 (I n)).
  rewrite ! Mmult_assoc in e.
  rewrite ! Mmult_1_l in e.
  rewrite ! id_adjoint_eq in e.
  rewrite ! Mmult_1_r in e.
  rewrite Mmult_assoc.
  apply e.
  all: auto with wf_db.
Qed.

Lemma eigenpair_to_selective_diagonal'' : forall {n} (indices_list : list nat) (c : C) (M1 M3 : Square n),
    WF_Matrix M3 -> 
    (forall x : nat, In x indices_list -> Eigenpair M1 (M3 × e_i x, c)) ->  
    (M1 × M3 × selective_diagonal n indices_list × (M3) †
     = c .* M3 × selective_diagonal n indices_list × (M3) †).
Proof. intros.  pose (eigenpair_to_selective_diagonal indices_list c M1 (I n) M3).
  rewrite ! Mscale_mult_dist_l in e.
  rewrite ! Mmult_1_l in e.
  rewrite ! Mmult_assoc in e.
  rewrite ! Mmult_1_l in e.
  rewrite <- ! Mmult_assoc in e.
  rewrite e.
  distribute_scale.
  all: auto with wf_db.
Qed.


(** eigenvalue is real : https://books.physics.oregonstate.edu/LinAlg/eigenhermitian.html **)
Lemma Hermitian_eigenvalue_is_real : forall {n} (M : Square n) (v : Vector n) (c : C),
    WF_Matrix M -> WF_Matrix v -> v <> Zero -> M † = M -> M × v = c .* v -> c ^* = c.
Proof. intros n M v c H0 H1 H2 H3 H4. 
  assert (v† × M × v = c .* (v† × v))
    by (rewrite Mmult_assoc, H4; distribute_scale; reflexivity).
  replace (v† × M) with (c ^* .* v†) in H5
    by (rewrite <- H3, <- Mmult_adjoint, H4; distribute_adjoint; reflexivity).
  rewrite Mscale_mult_dist_l in H5.
  destruct (Ceq_dec c C0).
  - subst; lca.
  - assert ((v) † × v <> Zero).
    { intro.
      apply f_equal_inv with (x := 0%nat) in H6.
      apply f_equal_inv with (x := 0%nat) in H6.
      replace (Zero 0%nat 0%nat) with C0 in H6 by (simpl; reflexivity).
      assert ((((v) † × v) 0%nat 0%nat) = (inner_product v v))
        by (unfold inner_product; reflexivity).
      rewrite H7 in H6.
      rewrite inner_product_zero_iff_zero in H6; auto with wf_db. }
    assert (forall a b v, (a .* v = b .* v -> (a - b) .* v = @Zero 1 1%nat)).
    { intros a b v0 H7.
      rewrite Cminus_unfold.
      rewrite Mscale_plus_distr_l.
      rewrite H7.
      rewrite <- Mscale_plus_distr_l.
      replace (b + - b) with C0 by lca.
      rewrite Mscale_0_l.
      reflexivity. }
    apply H7 in H5.
    destruct (Ceq_dec (c ^* - c) C0).
    + apply Cplus_inj_r with (c := c) in e.
      autorewrite with C_db in e.
      setoid_rewrite <- e at 2.
      lca.
    + replace (@Zero 1 1) with ((c ^* - c) .* (@Zero 1 1)) in H5 by lma'.
      apply (Mscale_cancel ((v) † × v) Zero (c ^* - c) n1) in H5.
      contradiction.
Qed.

(** eigenvalue is unimodular : https://books.physics.oregonstate.edu/LinAlg/eigenunitary.html **)
Lemma Unitary_eigenvalue_is_unimodular : forall {n} (M : Square n) (v : Vector n) (c : C),
    WF_Unitary M -> WF_Matrix v -> v <> Zero -> M × v = c .* v -> c^* * c = C1.
Proof. intros n M v c H0 H1 H2 H3.
  assert ((v) † × v <> Zero).
  { intro.
    apply f_equal_inv with (x := 0%nat) in H4.
    apply f_equal_inv with (x := 0%nat) in H4.
    replace (Zero 0%nat 0%nat) with C0 in H4 by (simpl; reflexivity).
    assert ((((v) † × v) 0%nat 0%nat) = (inner_product v v))
      by (unfold inner_product; reflexivity).
    rewrite H5 in H4.
    rewrite inner_product_zero_iff_zero in H4; auto with wf_db. }
  assert (v† × v = (c^* * c) .* (v†× v)).
  { destruct H0.
    replace (v† × v) with (v† × I n × v) at 1 by (rewrite Mmult_1_r; auto with wf_db).
    rewrite <- H5 at 1.
    replace ((v) † × ((M) † × M) × v) with (((v) † × (M) †) × (M × v))
      by (rewrite ! Mmult_assoc; reflexivity).
    rewrite <- Mmult_adjoint.
    rewrite ! H3.
    distribute_adjoint.
    distribute_scale.
    reflexivity. }
  assert (forall a v, (v = a .* v -> (a - C1) .* v = @Zero 1 1%nat)).
  { intros a v0 H6. 
    rewrite Cminus_unfold.
    rewrite Mscale_plus_distr_l.
    rewrite <- H6.
    setoid_rewrite <- Mscale_1_l at 2.
    rewrite <- Mscale_plus_distr_l.
    replace (C1 + - C1) with C0 by lca.
    rewrite Mscale_0_l.
    reflexivity. }
  apply H6 in H5.
  destruct (Ceq_dec (c ^* * c - C1) C0).
  + apply Cplus_inj_r with (c := C1) in e.
    autorewrite with C_db in e.
    setoid_rewrite <- e.
    lca.
  + replace (@Zero 1 1) with ((c ^* * c - C1) .* (@Zero 1 1)) in H5 by lma'.
    apply (Mscale_cancel ((v) † × v) Zero (c ^* * c - C1) n0) in H5.
    contradiction.
Qed.

Lemma Unitary_Hermitian_eigenvalue_plusminus1: forall {n} (M : Square n) (v : Vector n) (c : C),
    WF_Unitary M -> WF_Matrix v -> v <> Zero -> M † = M -> M × v = c .* v -> (c = C1) \/ (c = Copp C1).
Proof. intros n M v c H0 H1 H2 H3 H4.
  remember H0 as H0'. clear HeqH0'. destruct H0'.
  pose (Hermitian_eigenvalue_is_real M v c H5 H1 H2 H3 H4).
  pose (Unitary_eigenvalue_is_unimodular M v c H0 H1 H2 H4).
  destruct c.
  inversion e.
  assert (r0 = 0)%R by lra.
  subst.
  inversion e0.
  autorewrite with R_db in H9, H10.
  assert (r = 1 \/ r = - 1)%R by nra.
  autorewrite with R_db.
  destruct H7; subst.
  - left. lca.
  - right. lca.
Qed.


  

(** https://books.physics.oregonstate.edu/LinAlg/eigenhermitian.html **)
Lemma Hermitian_different_eigenvalue_orthogonal_eigenvector :
  forall {n} (v1 v2 : Vector n) (M : Square n) (c1 c2 : C),
    WF_Matrix M -> WF_Matrix v1 -> WF_Matrix v2 ->
    M † = M -> c1 <> c2 -> M × v1 = c1 .* v1 -> M × v2 = c2 .* v2 ->
    inner_product v1 v2 = 0.
Proof. intros n v1 v2 M c1 c2 H0 H1 H2 H3 H4 H5 H6. 
  assert (v1† × M × v2 = c2 .* (v1† × v2))
    by (rewrite Mmult_assoc, H6; distribute_scale; reflexivity).
  assert (v1† × M × v2 = c1^* .* (v1† × v2))
    by (rewrite <- H3, <- Mmult_adjoint, H5; distribute_adjoint; distribute_scale; reflexivity).
  destruct (Mat_eq_dec n 1%nat v1 Zero H1 (WF_Zero n 1%nat)).
  - subst.
    unfold inner_product.
    assert ((@Zero n 1%nat)† × v2 = @Zero 1%nat 1%nat)
      by (rewrite zero_adjoint_eq, Mmult_0_l; reflexivity).
    rewrite H9.
    reflexivity.
  - destruct (Mat_eq_dec n 1%nat v2 Zero H2 (WF_Zero n 1%nat)).
    + subst.
      unfold inner_product.
      assert (v1† × (@Zero n 1%nat) = @Zero 1%nat 1%nat)
        by (rewrite Mmult_0_r; reflexivity).
      rewrite H9.
      reflexivity.
    + rewrite (Hermitian_eigenvalue_is_real M v1 c1 H0 H1 n0 H3 H5) in H8.
      assert (forall (n m : nat) (c1 c2 : C) (M : Matrix n m),
                 WF_Matrix M -> c1 .* M = c2 .* M ->  (c1 - c2) .* M = Zero).
      { intros n2 m c0 c3 M0 H9 H10.
        rewrite Cminus_unfold, Mscale_plus_distr_l, H10.
        lma'. }
      assert (c1 .* ((v1) † × v2) = c2 .* ((v1) † × v2)) by (rewrite <- H7, <- H8; reflexivity).
      assert (WF_Matrix ((v1) † × v2)) by auto with wf_db.
      apply (H9 1%nat 1%nat c1 c2 ((v1) † × v2) H11) in H10.
      assert (@Zero 1%nat 1%nat = (c1 - c2) .* (@Zero 1%nat 1%nat))
        by (rewrite Mscale_0_r; reflexivity).
      rewrite H12 in H10.
      assert (c1 - c2 <> 0).
      { intro. apply Cminus_eq_0 in H13. contradiction. }
      apply Mscale_cancel with (c := c1 - c2) in H10; auto.
      unfold inner_product.
      rewrite H10.
      reflexivity.
Qed.

(** https://www.math.purdue.edu/~eremenko/dvi/spectral.pdf **)
Lemma Unitary_different_eigenvalue_orthogonal_eigenvector :
  forall {n} (v1 v2 : Vector n) (M : Square n) (c1 c2 : C),
    WF_Unitary M -> WF_Matrix v1 -> WF_Matrix v2 ->
    v1 <> Zero -> v2 <> Zero ->
    c1 <> c2 -> M × v1 = c1 .* v1 -> M × v2 = c2 .* v2 ->
    inner_product v1 v2 = 0.
Proof. intros n v1 v2 M c1 c2 H0 H1 H2 H3 H4 H5 H6 H7. 
  assert (v1† × v2 = c1^* * c2 .* (v1† × v2)).
  { unfold WF_Unitary in H0.
    destruct H0 as [WFM UM].
    setoid_rewrite <- Mmult_1_l at 4; auto.
    rewrite <- UM.
    replace ((v1) † × ((M) † × M × v2)) with ((v1† × M†) × (M × v2))
      by (rewrite ! Mmult_assoc; reflexivity).
    rewrite <- Mmult_adjoint.
    rewrite H6, H7.
    distribute_adjoint.
    distribute_scale.
    reflexivity. }
  assert (c1 <> 0).
  { destruct (Classical_Prop.classic (c1 = 0)); auto.
    rewrite H9, Mscale_0_l in H6.
    unfold WF_Unitary in H0.
    destruct H0 as [WFM UM].
    apply @Mmult_inj_l with (i := n) (m := M†) in H6.
    rewrite <- Mmult_assoc, UM, Mmult_1_l, Mmult_0_r in H6; auto. }
  assert (c2 <> 0).
  { destruct (Classical_Prop.classic (c2 = 0)); auto.
    rewrite H10, Mscale_0_l in H7.
    unfold WF_Unitary in H0.
    destruct H0 as [WFM UM].
    apply @Mmult_inj_l with (i := n) (m := M†) in H7.
    rewrite <- Mmult_assoc, UM, Mmult_1_l, Mmult_0_r in H7; auto. }
  assert (c1^* = /c1).
  { pose (Unitary_eigenvalue_is_unimodular M v1 c1 H0 H1 H3 H6).
    setoid_rewrite <- Cmult_1_l at 3.
    rewrite <- e.
    rewrite <- Cmult_assoc, Cinv_r, Cmult_1_r; auto. }
  rewrite H11 in H8.
  assert (/ c1 * c2 <> C1).
  { destruct (Classical_Prop.classic (/ c1 * c2 = C1)); auto.
    apply Cmult_l with (c := c1) in H12.
    rewrite Cmult_assoc, Cinv_r, Cmult_1_l, Cmult_1_r in H12; auto. }
  assert (forall (i j : nat) (A B : Matrix i j), WF_Matrix A -> A = B -> A .+ (- C1)%C .* B = Zero).
  { intros i0 j A B H13 H14. rewrite <- H14. lma'. }
  assert (WF_Matrix ((v1) † × v2)); auto with wf_db.
  pose (H13 1%nat 1%nat ((v1) † × v2) (/ c1 * c2 .* ((v1) † × v2)) H14 H8).
  rewrite Mscale_assoc in e.
  setoid_rewrite <- Mscale_1_l in e at 2.
  rewrite <- Mscale_plus_distr_l in e.
  replace (@Zero 1%nat 1%nat) with ((C1 + - C1 * (/ c1 * c2)) .* (@Zero 1%nat 1%nat)) in e
      by lma'.
  assert ((C1 + - C1 * (/ c1 * c2)) <> C0).
  { destruct (Classical_Prop.classic (C1 + - C1 * (/ c1 * c2) = 0)); auto.
    rewrite <- Copp_mult_distr_l, <- Cminus_unfold, Cmult_1_l in H15.
    apply Cminus_eq_0 in H15. auto. }
  apply Mscale_cancel in e; auto.
  unfold inner_product.
  rewrite e.
  reflexivity.
Qed.



(** subspace of the form { v | P v } **)
Definition subspace {n : nat} (P : Vector n -> Prop) : Prop :=
  (forall (v : Vector n), P v -> WF_Matrix v) /\
    P Zero /\
    (forall (v w : Vector n), P v -> P w -> P (v .+ w)) /\
    (forall (v : Vector n) (c : C), P v -> P (c .* v)).

Lemma WF_subspace : forall {n : nat} {P : Vector n -> Prop} {v : Vector n},
    subspace P -> P v -> WF_Matrix v.
Proof. intros n P v H0 H1. destruct H0 as [WFP [PZero [Psum Pscale]]].
  auto.
Qed.

#[export] Hint Resolve WF_subspace : wf_db.


Lemma matrix_column_choose_original : forall {n m : nat} (A : Matrix n m),
    WF_Matrix A -> matrix_column_choose (List.seq 0 m) A = A.
Proof. intros n m A H0. 
  unfold matrix_column_choose, list_vector_to_matrix.
  unfold WF_Matrix in H0.
  prep_matrix_equality.
  assert (@Zero n 1 = (get_vec m A)).
  { unfold get_vec.
    prep_matrix_equality.
    bdestruct_all; trivial.
    rewrite H0; trivial.
    lia. }
  bdestruct (x <? n)%nat.
  - bdestruct (y <? m)%nat.
    + rewrite H1.
      rewrite map_nth with (d := m).
      rewrite seq_nth; trivial.
    + rewrite nth_overflow.
      * rewrite H0; trivial.
        lia.
      * rewrite map_length.
        rewrite seq_length.
        assumption.
  - bdestruct (y <? m)%nat.
    + rewrite H1.
      rewrite map_nth with (d := m).
      rewrite seq_nth; trivial.
    + rewrite nth_overflow.
      * rewrite H0; trivial.
        lia.
      * rewrite map_length.
        rewrite seq_length.
        assumption.
Qed.

Lemma subspace_closed_under_linear_combinations : forall {n m : nat} {P : Vector n -> Prop} (M : Matrix n m) (a : Vector m), WF_Matrix a -> subspace P -> (forall (i : nat), (i < m)%nat -> P (get_vec i M)) -> P (M × a).
Proof. intros n m P M a H0 H1 H2. 
  induction m.
  - unfold Mmult. simpl.
    unfold subspace in H1.
    destruct H1 as [WFP [PZero [Psum Pscale]]].
    assumption.
  - assert (M × a = (matrix_column_choose (List.seq 0 m) M) × (vector_row_choose (List.seq 0 m) a) .+ (a m 0%nat) .* (get_vec m M)).
      { unfold Mmult.
        unfold Matrix.scale.
        unfold matrix_column_choose, list_vector_to_matrix.
        unfold vector_row_choose.
        unfold get_vec.
        unfold Mplus.
        simpl.
        do 2 (apply functional_extensionality; intros).
        unfold WF_Matrix in *.
        bdestruct (x0 <? 1)%nat.
        - bdestruct_all.
          subst.
          f_equal.
          2 : apply Cmult_comm.
          rewrite seq_length.
          apply big_sum_eq_bounded.
          intros.
          rewrite seq_nth.
          2 : assumption.
          simpl.
          f_equal.
          rewrite nth_indep with (d' := (fun i0 x1 y : nat => if (y =? 0)%nat then M x1 i0 else 0) (s m)).
          2 : rewrite map_length;
          rewrite seq_length;
          assumption.
          rewrite map_nth with (d := s m).
          bdestruct_all.
          rewrite seq_nth; trivial.
        - remember H0 as H0'. clear HeqH0'.
          remember H0 as H0''. clear HeqH0''.
          assert ((m >= s m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0 m x0 H4).
          rewrite H0. rewrite Cmult_0_r, Cplus_0_r.
          bdestruct_all.
          rewrite Cmult_0_r, Cplus_0_r.
          f_equal.
          2 : symmetry; apply seq_length.
          apply functional_extensionality; intros.
          assert ((x1 >= s m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0' x1 x0 H6).
          rewrite H0'.
          rewrite Cmult_0_r.
          assert ((nth x1 (List.seq 0 m) (s m) >= s m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0'' (nth x1 (List.seq 0 m) (s m)) x0 H7).
          rewrite H0''.
          rewrite Cmult_0_r.
          reflexivity. }
      rewrite H3.
      remember H1 as H1'.
      clear HeqH1'.
      unfold subspace in H1.
      destruct H1 as [WFP [PZero [Psum Pscale]]].
      apply Psum.
    + rewrite ! seq_length.
      apply IHm. 
      * pose (WF_Matrix_vector_row_choose_indices_list (List.seq 0 m) a).
        rewrite ! seq_length in w; auto.
      * intros i0 H1.
        assert (get_vec i0 (matrix_column_choose (List.seq 0 m) M) = get_vec i0 M).
           { unfold matrix_column_choose, list_vector_to_matrix.
             unfold get_vec.
             do 2 (apply functional_extensionality; intros).
             bdestruct_all; trivial.
             subst.
             rewrite nth_indep with (d' := (fun i1 x0 y : nat => if (y =? 0)%nat then M x0 i1 else 0) (s m)).
             2 : rewrite map_length;
             rewrite seq_length;
             assumption.
             rewrite map_nth with (d := s m).
             bdestruct_all.
             rewrite seq_nth; trivial. }
           setoid_rewrite H4.
           auto.
    + apply Pscale.
      auto.
Qed.


Definition span {n m : nat} (M : Matrix n m) (u : Vector n) : Prop := (exists (a : Vector m), WF_Matrix a /\ u = M × a).



Lemma span_is_subspace : forall (n m : nat) (M : Matrix n m),
    WF_Matrix M -> subspace (span M).
Proof. intros n m M H0. 
  repeat constructor.
  - intros v H1.
    unfold span in H1.
    destruct H1 as [a [WFa vMa]].
    rewrite vMa.
    auto with wf_db.
  - exists Zero.
    split; auto with wf_db.
    rewrite Mmult_0_r.
    reflexivity.
  - intros v w H1 H2.
    unfold span in *.
    destruct H1 as [a [WFa vMa]].
    destruct H2 as [b [WFb wMb]].
    exists (a .+ b).
    split; auto with wf_db.
    subst.
    rewrite Mmult_plus_distr_l.
    reflexivity.
  - intros v c H1. 
    unfold span in *.
    destruct H1 as [a [WFa vMa]].
    exists (c .* a).
    split; auto with wf_db.
    subst.
    distribute_scale.
    reflexivity.
Qed.


(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
Lemma equal_span_col_append : forall {n m : nat} (M : Matrix n m) (v u : Vector n),
    span M u -> span (col_append M v) u.
Proof. intros n m M v u H0.
  unfold span in *.
  destruct H0 as [a [H0 H1]].
  exists (fun (r c : nat) => if r <? m then a r c else C0).
  split.
  - unfold WF_Matrix.
    intros x y H2. 
    unfold WF_Matrix in H0.
    rewrite H0.
    bdestruct_all; reflexivity.
    lia.
  - rewrite H1.
    unfold col_append, col_wedge.
    unfold Mmult.
    prep_matrix_equality.
    simpl.
    bdestruct_all.
    rewrite Cmult_0_r, Cplus_0_r.
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all.
    reflexivity.
Qed.

(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
Lemma equal_span_col_append_inv : forall {n m : nat} (M : Matrix n m) (v : Vector n), span M v -> (forall (u : Vector n), span (col_append M v) u -> span M u).
Proof. intros n m M v H0 u H1.
  unfold span in *.
  do 2 destruct H0.
  do 2 destruct H1.
  rewrite H2 in H3.
  rewrite H3.
  unfold Mmult in H3.
  (** Σ_{i = 0}^{i = m-1} M_i x0_i + x0_m * Σ_{i = 0}^{i = m-1} M_i x_i 
           = Σ_{i = 0}^{i = m-1} M_i (x0_i + x0_m * x_i) **)
  exists (fun (r c : nat) => if (r <? m) then ((x0 r c) + (x0 m c) * (x r 0%nat)) else C0).
  split.
  - unfold WF_Matrix.
    intros x1 y H4.
    destruct H4; bdestruct_all; trivial.
    remember H1 as H1'. clear HeqH1'.
    unfold WF_Matrix in H1, H1'.
    assert ((x1 >= s m)%nat \/ (y >= 1)%nat). { right. lia. }
    specialize (H1 x1 y H6).
    rewrite H1.
    assert ((m >= s m)%nat \/ (y >= 1)%nat). { right. lia. }
    specialize (H1' m y H7).
    rewrite H1'.
    lca.
  - unfold col_append, col_wedge.
    unfold Mmult.
    do 2 (apply functional_extensionality; intros).
    simpl.
    bdestruct_all. clear H5.
    assert ( Σ (fun y : nat => M x1 y * (if y <? m then x0 y x2 + x0 m x2 * x y 0%nat else 0)) m
             =  Σ (fun y : nat => M x1 y * (x0 y x2 + x0 m x2 * x y 0%nat)) m).
    { apply big_sum_eq_bounded.
      intros x3 H5.
      bdestruct_all.
      reflexivity. }
    rewrite H5.
    replace (fun y : nat => M x1 y * (x0 y x2 + x0 m x2 * x y 0%nat))
      with (fun y : nat => M x1 y * x0 y x2 + (M x1 y * x y 0%nat)* x0 m x2)
      by (apply functional_extensionality; intros; lca).
    assert (Σ (fun y : nat => M x1 y * x0 y x2 + M x1 y * x y 0%nat * x0 m x2) m
            = Σ (fun y : nat => M x1 y * x0 y x2) m + Σ (fun y : nat => M x1 y * x y 0%nat) m  * x0 m x2).
    { setoid_rewrite big_sum_plus.
      simpl.
      f_equal.
      rewrite @big_sum_mult_r with (R := C) (H := C_is_monoid) (H0 := C_is_group) (H1 := C_is_comm_group) (H2 := C_is_ring).
      simpl.
      reflexivity. }
    rewrite H6.
    f_equal.
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all.
    reflexivity.
Qed.

(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
(*** May not be needed *)
Lemma equal_span_reduce_col_inv : forall {n m : nat} (M : Matrix n (s m)) (i : nat),
    (i < s m)%nat -> (forall (u : Vector n), span (reduce_col M i) u -> span M u).
Proof. intros n m M i H u H0.
  unfold span in *.
  destruct H0 as [a [H0 H0']].
  exists (fun r c => if (r <? i)%nat then (a r c) else if (r =? i)%nat then C0 else (a (r-1)%nat c)).
  split.
  - unfold WF_Matrix in *.
    intros.
    rewrite ! H0;
      bdestruct_all; trivial;
      lia.
  - rewrite H0'.
    unfold reduce_col.
    prep_matrix_equality.
    unfold Mmult.

    replace m with (i + (m - i))%nat at 1 by lia.
    rewrite @big_sum_sum with (H := C_is_monoid) (m := i) (n := (m - i)%nat).
    replace (s m) with (i + ((s m) - i))%nat at 1 by lia.
    rewrite @big_sum_sum with (H := C_is_monoid) (m := i) (n := ((s m) - i)%nat).
    f_equal.
    + apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      reflexivity.
    + replace ((s m) - i)%nat with (s (m - i))%nat by lia.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite Cmult_0_r, Cplus_0_l.
      apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      replace (1 + (i + x0))%nat with (i + s x0)%nat by lia.
      replace (i + s x0 - 1)%nat with (i + x0)%nat by lia.
      reflexivity.
Qed.
    
  
(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)

Lemma equal_span_reduce_col : forall {n m : nat} (M : Matrix n (s m)) (i : nat),
    (i < s m)%nat -> span (reduce_col M i) (get_vec i M) ->
    (forall (u : Vector n), span M u -> span (reduce_col M i) u).
Proof. intros n m M i H H0 u H1.
  unfold span in *.
  destruct H0 as [a [H0 H0']].
  destruct H1 as [b [H1 H1']].
  (* get_vec i M = reduce_col M i × a
     =>  M_i = (Σ_{k=0}^{k=i-1} M_k a_k) + (Σ_{k=i+1}^{k=m} M_k a_{k-1})
     
        u = M × b = Σ_{k=0}^{k=m} M_k b_k
        = (Σ_{k=0}^{k=i-1} M_k b_k) + M_i b_i + (Σ_{k=i+1}^{k=m} M_k b_k)
        = (Σ_{k=0}^{k=i-1} M_k b_k) 
        + ((Σ_{k=0}^{k=i-1} M_k a_k) + (Σ_{k=i+1}^{k=m} M_k a_{k-1})) b_i 
        + (Σ_{k=i+1}^{k=m} M_k b_k)
        = (Σ_{k=0}^{k=i-1} M_k (b_i a_k + b_k)) + (Σ_{k=i+1}^{k=m} M_k (b_i a_{k-1} + b_k))
        
        u = reduce_col M i × c = (Σ_{k=0}^{k=i-1} M_k c_k) + (Σ_{k=i+1}^{k=m} M_k c_{k-1})
        c = ((b i 0%nat) .* a) .+ (reduce_row i b) *)
  exists (((b i 0%nat) .* a) .+ (reduce_row b i)).
  split.
  - auto with wf_db.
  - rewrite H1'.
    rewrite Mmult_plus_distr_l.
    distribute_scale.
    rewrite <- H0'.
    unfold get_vec, reduce_row, reduce_col.
    unfold Mmult, Matrix.scale, Mplus.
    prep_matrix_equality.
    bdestruct_all.
    + subst.
      replace (s m) with (i + (s (m - i)))%nat by lia.
      rewrite @big_sum_sum with (H := C_is_monoid) (m := i) (n := (s (m - i))%nat).
      rewrite <- big_sum_extend_l.
      simpl.
      setoid_rewrite Cplus_comm at 1.
      rewrite <- ! Cplus_assoc.
      f_equal.
      * replace (i + 0)%nat with i by lia.
        lca.
      * rewrite Cplus_comm at 1.
        replace m with (i + (m - i))%nat at 2 by lia.
        rewrite @big_sum_sum with (H := C_is_monoid) (m := i) (n := (m - i)%nat).
        simpl.
        f_equal.
        -- apply big_sum_eq_bounded.
           intros.
           bdestruct_all.
           lca.
        -- apply big_sum_eq_bounded.
           intros.
           bdestruct_all.
           replace (i + s x0)%nat with (s (i + x0)) by lia.
           reflexivity.
    + assert ((fun y0 : nat => M x y0 * b y0 y)
              =
                (fun _ : nat => C0)).
      { apply functional_extensionality; intros.
        unfold WF_Matrix in H1.
        rewrite H1; try lca; lia. }
      rewrite H3.
      simpl.
      rewrite Cmult_0_r, Cplus_0_l, Cplus_0_r.
      apply big_sum_eq_bounded.
      intros.
      unfold WF_Matrix in H1.
      rewrite ! H1.
      bdestruct_all; lca.
      all : lia.
Qed.      


Definition col_insert_front {n m : nat} (M : Matrix n m) (v : Vector n) : Matrix n (s m) :=
  fun r c => if (c =? 0)%nat then v r 0%nat else M r (c - 1)%nat.

Lemma WF_Matrix_col_insert_front : forall {n m : nat} (M : Matrix n m) (v : Vector n),
    WF_Matrix M -> WF_Matrix v -> WF_Matrix (col_insert_front M v).
Proof. intros n m M v H0 H1.
  unfold col_insert_front.
  unfold WF_Matrix in *.
  intros.
  bdestruct_all.
  - rewrite H1; trivial.
    lia.
  - rewrite H0; trivial.
    lia.
Qed.

 #[export] Hint Resolve WF_Matrix_col_insert_front : wf_db.
 

(* # ~12 *)
    (** Theorem 24 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V , where n ≥ 2. Then {u1, u2, . . . , un} is linearly dependent if and only if at least one of u1, u2, . . . , un can be written as a linear combination of the remaining n − 1 vectors. **)

(* proves the "only if" part of theorem 24

Lemma lin_dep_gen_elem : forall {m n} (T : Matrix n (S m)),
  WF_Matrix T -> linearly_dependent T -> 
  (exists i, i < (S m) /\ 
             (exists v : Vector m, WF_Matrix v /\ 
                 @Mmult n m 1 (reduce_col T i) v = (-C1) .* (get_vec i T))). 
 *)

Lemma span_linearly_dependent_col_insert_front : forall {m n} (M : Matrix n m) (v : Vector n),
    WF_Matrix M -> span M v -> linearly_dependent (col_insert_front M v).
Proof. intros m n M v H0 H1.
  unfold linearly_dependent.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  exists (fun r c => if (r =? 0)%nat
             then if (c =? 0)%nat
                  then (- C1)%C
                  else C0
             else a (r - 1)%nat c).
  split.
  - unfold WF_Matrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_Matrix in H1.
    rewrite H1; trivial; lia.
  - split.
    + intro.
      apply f_equal_inv with (x := 0%nat) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      simpl in H3.
      inversion H3.
      lra.
    + unfold col_insert_front.
      unfold Mmult.
      prep_matrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      * subst.
        simpl.
        unfold Mmult.
        assert (@Zero n 1 x 0%nat
                = Σ (fun y : nat => M x y * a y 0%nat) m * - C1 + Σ (fun y : nat => M x y * a y 0%nat) m).
        { lca. }
        rewrite H2.
        apply Cplus_inj_l.
        apply big_sum_eq_bounded.
        intros.
        replace (x0 - 0)%nat with x0 by lia.
        reflexivity.
      * rewrite Cmult_0_r, Cplus_0_l.
        replace (@Zero n 1 x y) with C0 by lca.
        simpl.
        rewrite big_sum_0_bounded; trivial.
        intros.
        unfold WF_Matrix in H1.
        rewrite H1; try lca; lia.
Qed.

Lemma span_linearly_dependent_col_append : forall {m n} (M : Matrix n m) (v : Vector n),
    WF_Matrix M -> span M v -> linearly_dependent (col_append M v).
Proof. intros m n M v H0 H1.
  unfold linearly_dependent.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  exists (fun r c => if (r =? m)%nat
             then if (c =? 0)%nat
                  then (- C1)%C
                  else C0
             else a r c).
  split.
  - unfold WF_Matrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_Matrix in H1.
    rewrite H1; trivial; lia.
  - split.
    + intro.
      apply f_equal_inv with (x := m) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      simpl in H3.
      replace (m =? m)%nat with true in H3 by (rewrite Nat.eqb_refl; reflexivity).
      inversion H3.
      lra.
    + unfold col_append, col_wedge.
      unfold Mmult.
      prep_matrix_equality.
      rewrite <- big_sum_extend_r.
      bdestruct_all.
      * subst.
        simpl.
        unfold Mmult.
        assert (@Zero n 1 x 0%nat
                = Σ (fun y : nat => M x y * a y 0%nat) m + Σ (fun y : nat => M x y * a y 0%nat) m * - C1 ).
        { lca. }
        rewrite H2.
        apply Cplus_inj_r.
        apply big_sum_eq_bounded.
        intros.
        bdestruct_all.
        reflexivity.
      * rewrite Cmult_0_r, Cplus_0_r.
        replace (@Zero n 1 x y) with C0 by lca.
        rewrite big_sum_0_bounded; trivial.
        intros.
        bdestruct_all.
        unfold WF_Matrix in H1.
        rewrite H1; try lca; lia.
Qed.

        

Lemma linearly_dependent_linear_combination : forall {n m : nat} (M : Matrix n m), (m > 1)%nat -> WF_Matrix M -> linearly_dependent M -> (exists (i : nat) (a : Vector (m-1)), (i < m)%nat /\ WF_Matrix a /\ get_vec i M = (matrix_column_choose ((List.seq 0 i) ++ (List.seq (i+1) (m - i - 1)%nat)) M) × a).
Proof. intros n m M H0 H1 H2.
  unfold linearly_dependent in H2.
  destruct H2 as [u [H2 [H3 H4]]].
  apply nonzero_vec_nonzero_elem in H3; trivial.
  destruct H3 as [i H3].
  exists i.
  bdestruct (i <? m).
  - exists (fun r c : nat => if r <? i then (- (/ (u i 0%nat)) * (u r c))%C else (- (/ (u i 0%nat)) * (u (r+1)%nat c))%C).
    split.
    + assumption.
    + split.
      * unfold WF_Matrix in *.
        intros.
        destruct H6; bdestruct_all.
        -- assert ((x+1 >= m)%nat \/ (y >= 1)%nat). { left. lia. }
           specialize (H2 (x+1)%nat y H8).
           rewrite H2.
           lca.
        -- assert ((x >= m)%nat \/ (y >= 1)%nat). { right. lia. }
           specialize (H2 x y H8).
           rewrite H2.
           lca.
        -- assert ((x+1 >= m)%nat \/ (y >= 1)%nat). { right. lia. }
           specialize (H2 (x+1)%nat y H8).
           rewrite H2.
           lca.
      * unfold Mmult in *.
        unfold matrix_column_choose, list_vector_to_matrix.
        unfold get_vec.
        do 2 (apply functional_extensionality; intros).
        apply f_equal_inv with (x := x) in H4.
        apply f_equal_inv with (x := x0) in H4.
        replace (Zero x x0) with C0 in H4 by reflexivity.
        bdestruct_all.
        -- assert (@Zero n 1%nat = (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0) m).
           { do 2 (apply functional_extensionality; intros).
             replace (Zero x1 x2) with C0 by reflexivity.
             bdestruct_all; trivial.
             unfold WF_Matrix in H1.
             assert ((x1 >= n)%nat \/ (m >= m)%nat). { right. lia. }
             specialize (H1 x1 m H8).
             rewrite H1.
             reflexivity. }
           rewrite H7.
           assert ((fun y : nat =>
                      nth y
                        (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                           (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                        (fun x1 y0 : nat => if (y0 =? 0)%nat then M x1 m else 0) x 0%nat *
                        (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0))
                   =
                     (fun y : nat =>
                        (- / u i 0%nat)%C * ((M x (nth y (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m)) *
                                             (if y <? i then u y x0 else u (y + 1)%nat x0)))).
           { apply functional_extensionality; intros.
             rewrite map_nth with (d := m).
             bdestruct_all; lca. }
           setoid_rewrite H8.
           rewrite <- @big_sum_scale_l with (H7 := C_is_module_space).
           simpl.
           apply Cmult_cancel_l with (a := (- u i 0%nat)%C).
           ++ intro.
              rewrite Copp_opp in H9.
              replace (- C0)%C with C0%C in H9 by lca.
              contradiction.
           ++ rewrite Cmult_assoc.
              replace (- u i 0%nat * - / u i 0%nat)%C with C1.
              ** rewrite Cmult_1_l.
                 rewrite Cmult_comm.
                 rewrite <- Copp_mult_distr_r.
                 apply Cplus_inv_r with (c := (M x i * u i 0%nat)%C).
                 replace (- (M x i * u i 0%nat) + M x i * u i 0%nat)%C with C0 by lca.
                 rewrite <- H4 at 1.
                 Search big_sum.
                 
                 assert (Σ
                           (fun x1 : nat =>
                              M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m) *
                                (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                           (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) +
                           M x i * u i 0%nat
                         =
                           Σ
                             (fun x1 : nat =>
                                M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                  (if (x1 =? m-1)%nat then u i 0%nat else
                                     (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0)))
                             (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]))).
                 { rewrite app_assoc.
                   setoid_rewrite app_length at 2.
                   simpl.
                   Search ((?x + 1)%nat = Datatypes.S ?x).
                   setoid_rewrite Nat.add_1_r at 6.
                   rewrite <- @big_sum_extend_r with (H := C_is_monoid).
                   simpl.
                   assert ((length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) = (m-1)%nat).
                   { rewrite app_length.
                     rewrite ! seq_length.
                     lia. }
                   rewrite ! H9.
                   bdestruct_all.
                   rewrite <- H9 at 3.
                   rewrite nth_middle with (a := i) (l' := []).
                   f_equal.
                   apply big_sum_eq_bounded.
                   intros x1 H12.
                   bdestruct_all.
                   - setoid_rewrite app_nth1 at 2.
                     + reflexivity.
                     + rewrite app_length.
                       rewrite ! seq_length.
                       lia.
                   - setoid_rewrite app_nth1 at 2.
                     + reflexivity.
                     + rewrite app_length.
                       rewrite ! seq_length.
                       lia. }
                 rewrite H9.
                 rewrite ! app_length.
                 rewrite ! seq_length.
                 simpl.
                 replace (i + (m - i - 1 + 1))%nat with m by lia.
                 assert (Σ (fun y : nat => M x y * u y x0) m
                         =
                           Σ (fun y : nat => M x (nth y (List.seq 0 m) m) *
                                          u (nth y (List.seq 0 m) m) x0) m).
                 { apply big_sum_eq_bounded.
                   intros x1 H10. 
                   rewrite seq_nth.
                   lca.
                   assumption. }
                 rewrite H10.
                 assert ((fun x1 : nat =>
                            M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                              (if (x1 =? m - 1)%nat
                               then u i 0%nat
                               else if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                         =
                           (fun x1 : nat =>
                              M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                u (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) x0)).
                 { apply functional_extensionality; intros.
                   subst.
                   f_equal.
                   bdestruct_all.
                   - rewrite <- nth_firstn with (n := i); try lia.
                     rewrite firstn_app.
                     rewrite seq_length.
                     replace (i - i)%nat with 0%nat by lia.
                     simpl.
                     rewrite app_nil_r.
                     replace i with (length (List.seq 0 i)) at 1
                       by (rewrite seq_length; reflexivity).
                     rewrite firstn_all.
                     rewrite seq_nth; try lia.
                     lca.
                   - subst.
                     rewrite app_assoc.
                     replace (m - 1)%nat with (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                       by (rewrite app_length; rewrite ! seq_length; lia).
                     rewrite nth_middle.
                     reflexivity.
                   - bdestruct (x1 <? (m-1)%nat).
                     + rewrite <- nth_firstn with (n := (m-1)%nat); try assumption.
                       rewrite <- firstn_removelast.
                       * rewrite app_assoc.
                         rewrite removelast_last.
                         rewrite nth_firstn; try assumption.
                         rewrite app_nth2.
                         -- rewrite seq_length.
                            rewrite seq_nth; try lia.
                            replace (i + 1 + (x1 - i))%nat with (x1 + 1)%nat by lia.
                            reflexivity.
                         -- rewrite seq_length; assumption.
                       * rewrite ! app_length; rewrite ! seq_length; simpl; lia.
                     + remember H2 as H2'. clear HeqH2'.
                       unfold WF_Matrix in H2, H2'.
                       rewrite nth_overflow.
                       * assert ((x1 + 1 >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                         assert ((m >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                         specialize (H2 (x1+1)%nat 0%nat H13).
                         specialize (H2' m 0%nat H14).
                         rewrite H2, H2'.
                         reflexivity.
                       * rewrite ! app_length; rewrite ! seq_length; simpl; lia. }
                 rewrite H11.
                 apply big_sum_permutation with (f := fun z => M x z * u z x0).
                 2: rewrite seq_length; lia.
                 replace (List.seq 0 m) with (List.seq 0 i ++ List.seq i (m - i))
                   by (rewrite <- seq_app; f_equal; lia).
                 apply Permutation_app.
                 1: apply Permutation_refl.
                 replace (m - i)%nat with ((m - i - 1) + 1)%nat at 1 by lia.
                 rewrite Nat.add_1_r at 1.
                 simpl.
                 rewrite cons_conc.
                 rewrite <- Nat.add_1_r.
                 apply Permutation_app_comm.
              ** rewrite <- Copp_mult_distr_l, <- Copp_mult_distr_r.
                 rewrite Copp_involutive.
                 rewrite Cinv_r; trivial.
        -- unfold WF_Matrix in H2.
           assert ((fun y : nat =>
                      nth y
                        (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                           (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) (@Zero n 1%nat) x 0%nat *
                        (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0)) =
                     (fun _ : nat => C0)).
           { apply functional_extensionality; intros.
             assert (@Zero n 1%nat = (fun i0 x2 y0 : nat => if (y0 =? 0)%nat then M x2 i0 else 0) m).
             { do 2 (apply functional_extensionality; intros).
               replace (Zero x2 x3) with C0 by reflexivity.
               bdestruct_all; trivial.
               unfold WF_Matrix in H1.
               assert ((x2 >= n)%nat \/ (m >= m)%nat). { right. lia. }
               specialize (H1 x2 m H8).
               rewrite H1.
               reflexivity. }
             rewrite H7.
             rewrite map_nth with (d := m).
             bdestruct_all.
             - assert ((x1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H2 x1 x0 H10).
               rewrite H2.
               lca.
             - assert ((x1+1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H2 (x1+1)%nat x0 H10).
               rewrite H2.
               lca. }
           setoid_rewrite H7.
           rewrite big_sum_0; trivial. 
  - assert ((i >= m)%nat \/ (0 >= 1)%nat). { left. lia. }
    unfold WF_Matrix in H2.
    specialize (H2 i 0%nat H6).
    contradiction.
Qed.



(* # ~11 *)
(** Theorem 26 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V . Then {u1, u2, . . . , un} is linearly independent if and only if each vector in sp{u1,u2,...,un} can be written uniquely as a linear combination of u1,u2,...,un. **)

Lemma linearly_independent_iff_unique_linear_combination_of_span : forall {n m : nat} (M : Matrix n m), linearly_independent M <-> (forall v : Vector n, span M v -> (exists a : Vector m, WF_Matrix a /\ v = M × a /\ (forall b : Vector m, WF_Matrix b -> v = M × b -> b = a))).
Proof. intros n m M.
  split.
  - intros H0 v H1.
    unfold span in *.
    do 2 destruct H1.
    exists x.
    split; trivial.
    split; trivial.
    intros b H3 H4.
    apply Mscale_inj with (c := (- C1)%C) in H2.
    apply (Mplus_double_side H4) in H2.
    replace (v .+ - C1 .* v) with (@Zero n 1) in H2 by lma.
    unfold linearly_independent in *.
    symmetry in H2.
    rewrite <- Mscale_mult_dist_r in H2.
    rewrite <- Mmult_plus_distr_l in H2.
    specialize (H0 (b .+ - C1 .* x)).
    apply H0 in H2; auto with wf_db.
    apply Mplus_inj_r with (m := x) in H2.
    rewrite Mplus_assoc in H2.
    replace (- C1 .* x .+ x) with (@Zero m 1) in H2 by lma.
    rewrite Mplus_0_l, Mplus_0_r in H2.
    assumption.
  - intros.
    unfold linearly_independent.
    intros a H1 H2.
    assert (span M Zero).
    { unfold span.
      exists Zero.
      split; auto with wf_db.
      rewrite Mmult_0_r.
      reflexivity. }
    specialize (H0 Zero H3).
    do 2 destruct H0.
    destruct H4.
    symmetry in H2.
    remember H5 as H5'. clear HeqH5'.
    specialize (H5' Zero).
    assert (WF_Matrix (@Zero m 1%nat)). { auto with wf_db. }
    assert (@Zero n 1%nat = M × (@Zero m 1%nat)). { rewrite Mmult_0_r. reflexivity. }
    specialize (H5' H6 H7).
    specialize (H5 a H1 H2).
    subst.
    reflexivity.
Qed.

(** Definition 27 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V. We say that {u1,u2,...,un} is a basis for V if and only if {u1,u2,...,un} spans V and is linearly independent. **)

Definition basis {n m : nat} (P : Vector n -> Prop) (M : Matrix n m) : Prop := subspace P /\ (forall i : nat, (i < m)%nat -> P (get_vec i M)) /\ (forall v : Vector n, P v -> span M v) /\ linearly_independent M.

(** Theorem 28 Let V be a vector space over a field F, and suppose u1,u2,...,un are vectors in V. Then {u1,u2,...,un} is a basis for V if and only if each v ∈ V can be written uniquely as a linear combination of u1, u2, . . . , un. **)

Lemma basis_iff_unique_linear_combination : forall {n m : nat} (P : Vector n -> Prop) (M : Matrix n m), basis P M <-> subspace P /\ (forall i : nat, (i < m)%nat -> P (get_vec i M)) /\ (forall v : Vector n, P v -> (exists a : Vector m, WF_Matrix a /\ v = M × a /\ (forall b : Vector m, WF_Matrix b -> v = M × b -> b = a))).
Proof. intros n m P M.
  split.
  - intros H0. 
    unfold basis in H0.
    destruct H0.
    destruct H1.
    destruct H2.
    do 2 (split; trivial).
    intros v H4.
    specialize (H2 v H4).
    rewrite linearly_independent_iff_unique_linear_combination_of_span in H3.
    specialize (H3 v H2).
    assumption.
  - intros H0.
    destruct H0.
    destruct H1.
    unfold basis.
    do 2 (split; trivial).
    split.
    + intros v H3.
      unfold span.
      specialize (H2 v H3).
      destruct H2.
      exists x.
      destruct H2.
      destruct H4.
      split; trivial.
    + rewrite linearly_independent_iff_unique_linear_combination_of_span.
      intros v H3.
      unfold span in H3.
      destruct H3.
      destruct H3.
      assert (P (M × x)).
      { apply subspace_closed_under_linear_combinations; trivial. }
      rewrite <- H4 in H5.
      specialize (H2 v H5).
      assumption.
Qed.



(** another way to say the first n columns **)
Definition submatrix_column {n m} (k : nat) (M : Matrix n m) : Matrix n k :=
  (fun r c : nat => if (c <? k)%nat then M r c else C0).

Lemma subsubmatrix_column_outer : forall {n m} (i j : nat) (M : Matrix n m),
    (i >= j)%nat -> submatrix_column i (submatrix_column j M) = (submatrix_column j M).
Proof. intros.
  unfold submatrix_column.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  bdestruct_all; trivial.
Qed.

Lemma subsubmatrix_column_inner : forall {n m} (i j : nat) (M : Matrix n m),
    (i < j)%nat -> submatrix_column i (submatrix_column j M) = (submatrix_column i M).
Proof. intros.
  unfold submatrix_column.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_matrix_column_choose : forall {n m} (k : nat) (M : Matrix n m), WF_Matrix M -> submatrix_column k M = matrix_column_choose (List.seq 0 k) M.
Proof. intros.
  unfold submatrix_column.
  unfold matrix_column_choose, list_vector_to_matrix.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  (*** You can get rid of this by splitting cases on c <? k, and using nth_indep & nth_overflow ***)
  assert (Zero = (fun i0 : nat => get_vec i0 M) m).
  { unfold get_vec.
    apply functional_extensionality; intros x.
    apply functional_extensionality; intros y.
    bdestruct_all; trivial.
    unfold WF_Matrix in H0.
    assert ((x >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H0 x m H2).
    rewrite H0.
    trivial. }
  rewrite H1.
  rewrite map_nth with (d := m).
  unfold get_vec.
  bdestruct_all.
  - rewrite seq_nth; auto.
  - rewrite nth_overflow.
    + unfold WF_Matrix in H0.
      rewrite H0; auto.
    + rewrite seq_length; trivial.
Qed.

Lemma WF_Matrix_submatrix_column : forall {n m} (k : nat) (M : Matrix n m),
    WF_Matrix M -> WF_Matrix (submatrix_column k M).
Proof. intros.
  unfold WF_Matrix in *.
  unfold submatrix_column.
  intros.
  bdestruct_all; trivial.
  rewrite H0; trivial.
  destruct H1; lia.
Qed.

#[export] Hint Resolve WF_Matrix_submatrix_column : wf_db.



 (** Lemma 33 Let V be a vector space over a field F, and let v1,v2,...,vn be nonzero vectors in V . If {v1, v2, . . . , vn} is linearly dependent, then there exists an integer k, with 2 ≤ k ≤ n, such that vk is a linear combination of v1,v2,...,vk−1. **)

(* Proof Let k be the smallest positive integer such that {v1, v2, . . . , vk} is linearly dependent. By assumption k ≤ n, and k ≥ 2 because the singleton set {v1} is linearly dependent only if v1 is the zero vector, which is not the case. By Theorem 24, one of the vectors v1,v2,...,vk is a linear combination of the others. If it is vk, then the proof is complete, so suppose vt, 1 ≤ t < k, is a linear combination of v1, ..., vt−1, vt+1, ..., vk:

vt = α1 v1 + ... + αt−1 vt−1 + αt+1 vt+1 + ... + αk vk. (2.12)

We must have αk ̸= 0, since otherwise {v1, v2, . . . , vk−1} would be linearly dependent by Theorem 26, contradicting that {v1, v2, . . . , vl} is linearly inde- pendent for l < k. But, with αk ̸= 0, we can solve (2.12) for vk:

vk = −α−1α1v1−...−α−1αt−1vt−1+α−1vt−α−1αt+1vt+1−...−α−1αk−1vk−1.
Therefore vk is a linear combination of v1,v2,...,vk−1. *)


Lemma linearly_dependent_bounded_linear_combination : forall {n m : nat} (M : Matrix n m), WF_Matrix M -> (forall i : nat, (i < m)%nat -> get_vec i M <> Zero) -> linearly_dependent M -> (exists k : nat, (0 < k < m)%nat /\ (exists a : Vector k, WF_Matrix a /\ get_vec k M = (submatrix_column k M) × a)).
Proof. intros n m M H H0 H1.
  induction m.
  - exists 0%nat.
    intros.
    Search Zero.
    unfold linearly_dependent in H1.
    destruct H1 as [a [H1 [H2 H3]]].
    contradict H2.
    unfold WF_Matrix in H1.
    prep_matrix_equality.
    apply H1.
    lia.
  - remember (submatrix_column m M) as M'.
    (*** Classical Logic Used ***)
    destruct (Classical_Prop.classic (linearly_dependent M')).
    + destruct (IHm M') as [k H'].
      * subst.
        apply WF_Matrix_submatrix_column.
        assumption.
      * intros.
        rewrite HeqM'.
        intro.
        apply (H0 i).
        -- lia.
        -- unfold get_vec.
           unfold get_vec in H4.
           rewrite <- H4.
           unfold submatrix_column.
           bdestruct_all.
           reflexivity.
      * assumption.
      * exists k.
        intros.
        destruct H'.
        split; try lia.
        assert (submatrix_column k M' = submatrix_column k M).
        { rewrite HeqM'.
          rewrite subsubmatrix_column_inner; trivial.
          lia. }
        assert (get_vec k M' = get_vec k M).
        { rewrite HeqM'.
          unfold get_vec.
          unfold submatrix_column.
          bdestruct_all.
          reflexivity. }
        rewrite <- H6.
        rewrite <- H5.
        assumption.
    + assert (linearly_independent M').
      { unfold linearly_independent.
        unfold linearly_dependent in H2.
        intros.
        (*** Classical Logic Used ***)
        apply Classical_Pred_Type.not_ex_all_not with (U := Vector m) (n := a) in H2.
        apply Classical_Prop.not_and_or in H2.
        destruct H2; try contradiction.
        apply Classical_Prop.not_and_or in H2.
        destruct H2; try contradiction.
        unfold "<>" in H2.
        rewrite Decidable.not_not_iff in H2; trivial.
        unfold Decidable.decidable.
        apply (Classical_Prop.classic (a = Zero)). }
      subst.
      exists m.
      bdestruct (m =? 0)%nat.
      * subst.
        remember H1 as H1'. clear HeqH1'.
        apply lindep_implies_not_linindep in H1'.
        assert (M <> Zero).
        { intro.
          assert (0 < 1)%nat. { lia. }
          specialize (H0 0%nat H5).
          contradict H0.
          rewrite H4.
          unfold get_vec.
          prep_matrix_equality.
          bdestruct_all; trivial. }
        pose (lin_indep_vec M H H4).
        contradiction.
      * split; try lia.
        unfold linearly_dependent in H1.
        destruct H1 as [a [H5 [H6 H7]]].
        assert (a m 0%nat <> C0).
        { intro.
          assert (WF_Matrix (reduce_row a m)).
          { unfold WF_Matrix.
            unfold WF_Matrix in H5.
            intros.
            unfold reduce_row.
            bdestruct_all.
            - apply H5. right. lia.
            - apply H5. left. lia. }
          assert (reduce_row a m <> Zero).
          { unfold reduce_row.
            intro.
            destruct (nonzero_vec_nonzero_elem a H5 H6) as [x H10].
            apply f_equal_inv with (x := x) in H9.
            apply f_equal_inv with (x := 0%nat) in H9.
            replace (Zero x 0%nat) with C0 in H9 by trivial.
            bdestruct (x <? m)%nat.
            - contradiction.
            - bdestruct (x =? m)%nat.
              + subst. contradiction.
              + contradict H10.
                unfold WF_Matrix in H5.
                apply H5.
                left.
                lia. }
          assert ((submatrix_column m M) × (reduce_row a m) = Zero).
          { unfold reduce_row, submatrix_column.
            unfold Mmult.
            prep_matrix_equality.
            replace (@Zero n 1%nat x y) with C0 by trivial.
            assert ((fun y0 : nat =>
                       (if y0 <? m then M x y0 else 0) *
                         (if y0 <? m then a y0 y else a (1 + y0)%nat y))
                    =
                      (fun y0 : nat =>
                         (if y0 <? m then M x y0 * a y0 y else 0))).
            { apply functional_extensionality; intros.
              bdestruct_all; lca. }
            rewrite H10.
            assert (Σ (fun y0 : nat => if y0 <? m then M x y0 * a y0 y else 0) m
                    =
                      Σ (fun y0 : nat => M x y0 * a y0 y) m).
            { apply big_sum_eq_bounded.
              intros.
              bdestruct_all.
              reflexivity. }
            rewrite H11.
            unfold Mmult in H7.
            apply f_equal_inv with (x := x) in H7.
            apply f_equal_inv with (x := y) in H7.
            replace (@Zero n 1%nat x y) with C0 in H7 by lca.
            rewrite <- H7.
            simpl.
            bdestruct (y =? 0)%nat.
            - subst.
              rewrite H1.
              rewrite Cmult_0_r.
              rewrite Cplus_0_r.
              reflexivity.
            - unfold WF_Matrix in H5.
              rewrite H5.
              + rewrite Cmult_0_r.
                rewrite Cplus_0_r.
                reflexivity.
              + right. lia. }
          unfold linearly_independent in H3.
          specialize (H3 (reduce_row a m) H8 H10).
          contradiction. }
        exists ((- (/ (a m 0%nat)))%C .* (reduce_row a m)).
        split; auto with wf_db. 
        distribute_scale.
        apply Mscale_div with (c := (- (a m 0%nat))%C).
        -- intro.
           rewrite Copp_opp in H8.
           replace (- 0)%C with C0 in H8 by lca.
           contradiction.
        -- distribute_scale.
           replace (- a m 0%nat * - / a m 0%nat)%C with (a m 0%nat * / a m 0%nat)%C by lca.
           rewrite Cinv_r; trivial.
           rewrite Mscale_1_l.
           apply Mplus_inv_r with (m := a m 0%nat .* get_vec m M); auto with wf_db.
           replace (- a m 0%nat .* get_vec m M .+ a m 0%nat .* get_vec m M) with (@Zero n 1)
             by lma.
           rewrite <- H7.
           unfold submatrix_column, reduce_row, get_vec.
           unfold Mmult, Matrix.scale, Mplus.
           prep_matrix_equality.
           simpl.
           assert ((fun y0 : nat =>
                      (if y0 <? m then M x y0 else 0) * (if y0 <? m then a y0 y else a (s y0) y))
                   =
                     (fun y0 : nat =>
                        (if y0 <? m then M x y0 *a y0 y else C0))).
           { apply functional_extensionality; intros.
             bdestruct_all; lca. }
           rewrite H8.
           bdestruct_all.
           ++ subst.
              f_equal; try lca.
              apply big_sum_eq_bounded.
              intros.
              bdestruct_all.
              reflexivity.
           ++ unfold WF_Matrix in H5.
              rewrite H5 at 1.
              ** f_equal; try lca.
                 apply big_sum_eq_bounded.
                 intros.
                 bdestruct_all.
                 reflexivity.
              ** right. lia.
Qed.

Lemma linearly_dependent_submatrix_column : forall {n m : nat} (k : nat) (M : Matrix n m),
    (k < m)%nat -> linearly_dependent (submatrix_column k M) -> linearly_dependent M.
Proof. intros n m k M H0 H1.
  unfold submatrix_column in H1.
  unfold linearly_dependent in *.
  destruct H1 as [a [H1 [H2 H3]]].
  exists (fun r c => if (r <? k) then a r c else C0).
  split.
  - unfold WF_Matrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_Matrix in H1.
    rewrite H1; trivial.
    lia.
  - split.
    + pose (nonzero_vec_nonzero_elem a H1 H2) as H4.
      destruct H4 as [x H4].
      intro.
      apply f_equal_inv with (x := x) in H5.
      apply f_equal_inv with (x := 0%nat) in H5.
      bdestruct (x <? k)%nat.
      * contradiction.
      * unfold WF_Matrix in H1.
        rewrite H1 in H4.
        -- contradiction.
        -- lia.
    + rewrite <- H3.
      unfold Mmult.
      prep_matrix_equality.
      replace m with (k + (m - k))%nat by lia.
      rewrite @big_sum_sum with (H := C_is_monoid) (m := k) (n := (m - k)%nat).
      simpl.
      rewrite <- Cplus_0_r with (x := Σ (fun y0 : nat => (if y0 <? k then M x y0 else 0) * a y0 y) k).
      f_equal.
      * apply big_sum_eq_bounded.
        intros.
        bdestruct_all.
        reflexivity.
      * rewrite big_sum_0_bounded; trivial.
        intros.
        bdestruct_all.
        lca.
Qed.



Lemma some_zero_vector_linearly_dependent : forall {n m : nat} (M : Matrix n m),
    ~ (forall i : nat, (i < m)%nat -> get_vec i M <> Zero) -> linearly_dependent M.
Proof. intros n m M H0.
  apply Classical_Pred_Type.not_all_ex_not in H0.
  destruct H0 as [k H0 ].
  apply Classical_Prop.imply_to_and in H0.
  destruct H0.
  unfold "~", "<>" in H1.
  rewrite Decidable.not_not_iff in H1.
  2 : { unfold Decidable.decidable.
        apply (Classical_Prop.classic (get_vec k M = Zero)). }
  unfold linearly_dependent.
  exists (e_i k).
  split; auto with wf_db.
  split.
  - intro.
    unfold e_i in H2.
    apply f_equal_inv with (x := k) in H2.
    apply f_equal_inv with (x := 0%nat) in H2.
    assert ((k =? k)%nat && (k <? m) && (0 =? 0)%nat = true).
    { bdestruct_all. trivial. }
    rewrite H3 in H2.
    replace (Zero k 0%nat) with C0 in H2; trivial.
    inversion H2.
    lra.
  - rewrite <- H1.
    rewrite matrix_by_basis; trivial.
Qed.

Lemma submatrix_column_overflow : forall {n m : nat} (k : nat) (M : Matrix n m),
    WF_Matrix M -> (k >= m)%nat -> submatrix_column k M = M.
Proof. intros n m k M H0 H1.
  unfold submatrix_column.
  prep_matrix_equality.
  bdestruct_all; trivial.
  unfold WF_Matrix in H0.
  rewrite H0; trivial; lia.
Qed.

Lemma get_vec_submatrix_column : forall {n m : nat} (i k : nat) (M : Matrix n m),
    (i < k)%nat -> get_vec i (submatrix_column k M) = get_vec i M.
Proof. intros n m i0 k M H0.
  unfold submatrix_column.
  unfold get_vec.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_vec_col_insert_front_front : forall {n m : nat} (i : nat) (M : Matrix n m) (v : Vector n),
    WF_Matrix v -> (i = 0%nat) -> get_vec i (col_insert_front M v) = v.
Proof. intros n m i0 M v H0 H1.
  unfold get_vec, col_insert_front.
  prep_matrix_equality.
  bdestruct_all.
  - subst.
    reflexivity.
  - unfold WF_Matrix in H0.
    rewrite H0; trivial.
    lia.
Qed.

Lemma get_vec_col_insert_front_back : forall {n m : nat} (i : nat) (M : Matrix n m) (v : Vector n),
    (i <> 0%nat) -> get_vec i (col_insert_front M v) = get_vec (i - 1)%nat M.
Proof. intros n m i0 M v H0.
  unfold get_vec, col_insert_front.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.


Lemma get_vec_col_append_front : forall {n m : nat} (i : nat) (M : Matrix n m) (v : Vector n),
    (i < m)%nat -> get_vec i (col_append M v) = get_vec i M.
Proof. intros n m i0 M v H0.
  unfold get_vec, col_append, col_wedge.
  prep_matrix_equality.
  bdestruct_all; auto.
Qed.

Lemma get_vec_col_append_back : forall {n m : nat} (i : nat) (M : Matrix n m) (v : Vector n),
    WF_Matrix v -> (i = m) -> get_vec i (col_append M v) = v.
Proof. intros n m i0 M v H0 H1.
  unfold get_vec, col_append, col_wedge.
  prep_matrix_equality.
  bdestruct_all.
  - subst.
    reflexivity.
  - unfold WF_Matrix in H0.
    rewrite H0; trivial.
    lia.
Qed.

Lemma submatrix_column_col_append : forall {n m : nat} (k : nat) (M : Matrix n m) (v : Vector n),
    (k <= m)%nat -> submatrix_column k (col_append M v) = submatrix_column k M.
Proof. intros n m k M v H0.
  unfold submatrix_column.
  unfold col_append, col_wedge.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_1_get_vec : forall {n m : nat} (M : Matrix n m),
    submatrix_column 1%nat M = get_vec 0%nat M.
Proof. intros n m M.
  unfold submatrix_column, get_vec.
  prep_matrix_equality.
  bdestruct_all; auto.
Qed.

Lemma span_submatrix_column_span_reduce_col :
  forall {n m : nat} (k i : nat) (M : Matrix n (s m)) (v : Vector n),
    (k <= m)%nat -> (i >= k)%nat -> span (submatrix_column k M) v -> span (reduce_col M i) v.
Proof. intros n m k i0 M v H0 H1 H2.
  unfold span in *.
  destruct H2 as [a [H2 H3]].
  exists (fun r c => if (r <? k)%nat then a r c else C0).
  split.
  - unfold WF_Matrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_Matrix in H2.
    rewrite H2; trivial.
    lia.
  - rewrite H3.
    unfold submatrix_column, reduce_col.
    unfold Mmult.
    prep_matrix_equality.
    replace m with (k + (m - k))%nat by lia.
    rewrite @big_sum_sum with (H := C_is_monoid).
    rewrite <- Cplus_0_r with (x := Σ (fun y0 : nat => (if y0 <? k then M x y0 else 0) * a y0 y) k).
    simpl.
    f_equal.
    + apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      reflexivity.
    + rewrite big_sum_0_bounded; trivial.
      intros.
      bdestruct_all; lca.
Qed. 
    

Lemma span_col_insert_front :
  forall {n m : nat} (P : Vector n -> Prop) (M : Matrix n m) (v : Vector n),
    basis P M -> span M v ->
    (forall u : Vector n, span M u <-> span (col_insert_front M v) u).
Proof. intros n m P M v H0 H1 u.
  split.
  - intros H2.
    unfold span in *.
    unfold basis in *.
    destruct H0 as [H0 [H0' [H0'' H0''']]].
    destruct H1 as [a [H1 H1']].
    destruct H2 as [b [H2 H2']].
    exists (fun r c => if (r =? 0)%nat then C0 else b (r - 1)%nat c).
    split.
    + unfold WF_Matrix.
      intros x y H3.
      bdestruct_all; trivial.
      unfold WF_Matrix in H2.
      rewrite H2; trivial.
      lia.
    + rewrite H2'.
      unfold col_insert_front, Mmult.
      prep_matrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite Cmult_0_r, Cplus_0_l.
      apply big_sum_eq_bounded.
      intros x0 H4.
      bdestruct_all.
      replace (s x0 - 1)%nat with x0 by lia.
      reflexivity.
  - intros H2. 
    unfold span in *.
    unfold basis in *.
    destruct H0 as [H0 [H0' [H0'' H0''']]].
    destruct H1 as [a [H1 H1']].
    destruct H2 as [b [H2 H2']].
    exists (fun r c => (b 0%nat c) * (a r 0%nat) + (b (r + 1)%nat c)).
    split.
    + unfold WF_Matrix in *.
      intros x y H3.
      destruct H3.
      * rewrite H1; try lia.
        setoid_rewrite H2 at 2; try lia.
        lca.
      * setoid_rewrite H2; try lia.
        lca.
    + rewrite H2'.
      unfold col_insert_front, Mmult.
      prep_matrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite H1'.
      unfold Mmult.
      simpl.
      rewrite @big_sum_mult_r with (H2 := C_is_ring).
      rewrite <- @big_sum_plus with (H0 := C_is_group).
      2 : apply C_is_comm_group.
      apply big_sum_eq_bounded.
      intros x0 H4.
      simpl.
      replace (x0 - 0)%nat with x0 by lia.
      replace (x0 + 1)%nat with (s x0) by lia.
      lca.
Qed.


 Lemma span_col_append :
  forall {n m : nat} (P : Vector n -> Prop) (M : Matrix n m) (v : Vector n),
    basis P M -> span M v ->
    (forall u : Vector n, span M u <-> span (col_append M v) u).
 Proof. intros n m P M v H0 H1 u.
   split.
   - intros H2.
     unfold span in *.
     unfold basis in *.
     destruct H0 as [H0 [H0' [H0'' H0''']]].
     destruct H1 as [a [H1 H1']].
     destruct H2 as [b [H2 H2']].
     exists (fun r c => if (r <? m)%nat then b r c else C0).
     split.
     + unfold WF_Matrix.
       intros x y H3.
       bdestruct_all; trivial.
       unfold WF_Matrix in H2.
       rewrite H2; trivial.
       lia.
     + rewrite H2'.
       unfold col_append, col_wedge, Mmult.
       prep_matrix_equality.
       simpl.
       bdestruct_all.
       rewrite Cmult_0_r, Cplus_0_r.
       apply big_sum_eq_bounded.
       intros x0 H5.
       bdestruct_all.
       reflexivity.
   - intros H2.
     unfold span in *.
     unfold basis in *.
     destruct H0 as [H0 [H0' [H0'' H0''']]].
     destruct H1 as [a [H1 H1']].
     destruct H2 as [b [H2 H2']].
     exists (fun r c => if (r <? m) then (b m c) * (a r 0%nat) + (b r c) else C0).
     split.
     + unfold WF_Matrix.
       intros x y H3.
       bdestruct_all; trivial.
       unfold WF_Matrix in *.
       rewrite ! H2; try lia.
       lca.
     + rewrite H2'.
       unfold col_append, col_wedge, Mmult.
       prep_matrix_equality.
       simpl.
       bdestruct_all. clear H4.
       rewrite H1'.
       unfold Mmult.
       rewrite @big_sum_mult_r with (H2 := C_is_ring).
       rewrite <- @big_sum_plus with (H0 := C_is_group).
       2 : apply C_is_comm_group.
       apply big_sum_eq_bounded.
       intros x0 H4.
       bdestruct_all.
       lca.
 Qed.

Lemma submatrix_column_zero : forall {n m : nat} (A : Matrix n m),
    submatrix_column 0 A = @Zero n 0.
Proof. intros n m A.
  unfold submatrix_column.
  prep_matrix_equality.
  bdestruct_all.
  reflexivity.
Qed.



Lemma get_vec_matrix_column_choose : forall {n m : nat} (i d : nat) (indices_list : list nat) (A : Matrix n m),
    (i < length indices_list)%nat -> WF_Matrix A ->
    get_vec i (matrix_column_choose indices_list A) = get_vec (nth i indices_list d) A.
Proof. intros n m i0 d indices_list A H0 H1. 
  unfold get_vec, matrix_column_choose, list_vector_to_matrix.
  prep_matrix_equality.
  bdestruct_all; trivial.
  assert (@Zero n 1 = get_vec m A).
  { unfold get_vec.
    prep_matrix_equality.
    bdestruct_all; trivial.
    unfold WF_Matrix in H1.
    rewrite H1; trivial.
    lia. }
  rewrite H3.
  rewrite map_nth with (d := m).
  unfold get_vec.
  bdestruct_all.
  rewrite nth_indep with (d := d) (d' := m); trivial.
Qed.

Lemma submatrix_column_smash_left : forall {n m o : nat} (k : nat) (A : Matrix n m) (B : Matrix n o),
    (k <= m)%nat -> submatrix_column k (smash A B) = submatrix_column k A.
Proof. intros n m o k A B H0.
  unfold smash, submatrix_column.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_smash_right : forall {n m o : nat} (k : nat) (A : Matrix n m) (B : Matrix n o),
    (k > m)%nat -> submatrix_column k (smash A B) = smash A (submatrix_column (k - m) B).
Proof. intros n m o k A B H0.
  unfold smash, submatrix_column.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_original : forall {n m : nat} (k : nat) (A : Matrix n m),
    WF_Matrix A -> (k >= m)%nat -> submatrix_column k A = A.
Proof. intros n m k A H0 H1.
  unfold submatrix_column.
  prep_matrix_equality.
  bdestruct_all; trivial.
  unfold WF_Matrix in H0.
  rewrite H0; trivial; lia.
Qed.
  
Lemma get_vec_submatrix_column_linearly_dependent : forall {n m : nat} (k : nat) (a : Vector k) (A : Matrix n m),
    (k < m)%nat -> get_vec k A = (submatrix_column k A) × a -> linearly_dependent A.
Proof. intros n m k a A H0 H1.
  unfold linearly_dependent.
  exists (fun r c => if (r <? k)%nat then (if (c =? 0)%nat then a r c else C0)
             else if (r =? k)%nat then (if (c =? 0)%nat then (Copp C1) else C0)
                  else C0).
  repeat split.
  - unfold WF_Matrix.
    intros x y H2.
    bdestruct_all; trivial.
  - intro.
    apply f_equal_inv with (x := k) in H2.
    apply f_equal_inv with (x := 0%nat) in H2.
    simpl in H2.
    rewrite Nat.ltb_irrefl in H2.
    rewrite Nat.eqb_refl in H2.
    inversion H2.
    lra.
  - unfold Mmult.
    prep_matrix_equality.
    replace (@Zero n 1 x y) with C0 by easy.
    replace m with (k + (1 + (m - k - 1)))%nat by lia.
    rewrite big_sum_sum with (m := k).
    rewrite big_sum_sum with (m := 1%nat).
    simpl.
    rewrite Cplus_0_l.
    bdestruct_all.
    + assert (forall x y z : C, x + z = y -> x + (y * (Copp C1) + z) = 0).
      { intros x0 y0 z H5.
        rewrite <- H5.
        lca. }
      apply H5.
      replace (k + 0)%nat with k by lia.
      unfold get_vec in H1.
      apply f_equal_inv with (x := x) in H1.
      apply f_equal_inv with (x := 0%nat) in H1.
      simpl in H1.
      rewrite H1.
      unfold submatrix_column, Mmult.
      rewrite <- Cplus_0_r.
      f_equal.
      * apply big_sum_eq_bounded.
        intros x0 H6.
        bdestruct_all.
        subst.
        reflexivity.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H6.
        bdestruct_all.
        lca.
    + rewrite Cmult_0_r, Cplus_0_l.
      rewrite <- Cplus_0_r.
      f_equal.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H5.
        bdestruct_all.
        lca.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H5.
        bdestruct_all.
        lca.
Qed.
    


Lemma reduce_col_submatrix_column_last : forall {n m : nat} (j : nat) (A : Matrix n m),
    reduce_col (submatrix_column (s j) A) j = submatrix_column j A.
Proof. intros n m j A.
  unfold submatrix_column, reduce_col.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma reduce_col_matrix_column_choose_delete : forall {n m : nat} (k : nat) (indices_list : list nat) (A : Matrix n m),
    WF_Matrix A -> (length indices_list > k)%nat->
    reduce_col (matrix_column_choose indices_list A) k = matrix_column_choose (delete_nth indices_list k) A.
Proof. intros n m k indices_list A H0 H1. 
  unfold reduce_col, delete_nth, matrix_column_choose, list_vector_to_matrix.
  prep_matrix_equality.
  assert (@Zero n 1 = get_vec m A).
  { unfold get_vec.
    prep_matrix_equality.
    bdestruct_all; trivial.
    unfold WF_Matrix in H0.
    rewrite H0; trivial; lia. }
  bdestruct_all.
  - rewrite <- firstn_skipn with (n := k) (l := indices_list) at 1.
    rewrite ! H2.
    rewrite ! map_nth with (d := m).
    unfold get_vec.
    bdestruct_all.
    f_equal.
    rewrite ! app_nth1; trivial; rewrite firstn_length; lia.
  - rewrite H2.
    rewrite ! map_nth with (d := m).
    unfold get_vec.
    bdestruct_all.
    f_equal.
    rewrite app_nth2.
    + rewrite firstn_length.
      replace (Init.Nat.min k (length indices_list)) with k by lia.
      rewrite <- firstn_skipn with (n := (k + 1)%nat) at 1.
      rewrite app_nth2.
      * rewrite firstn_length.
        replace (Init.Nat.min (k + 1) (length indices_list)) with (k + 1)%nat by lia.
        f_equal.
        lia.
      * rewrite firstn_length.
        lia.
    + rewrite firstn_length.
      lia.
Qed.

Lemma matrix_column_choose_empty : forall {n m : nat} (A : Matrix n m),
    matrix_column_choose [] A = Zero.
Proof. intros n m A.
  unfold matrix_column_choose, list_vector_to_matrix.
  prep_matrix_equality.
  simpl.
  destruct y; auto.
Qed.



 (** separate lemma of invariant for Theorem 34 *)
Lemma invariant_span : forall {n m o : nat} (P : Vector n -> Prop) (M : Matrix n m) (A : Matrix n o),
    WF_Matrix M -> WF_Matrix A -> basis P M ->
    (forall i : nat, (i < o)%nat -> P (get_vec i A)) -> (o > m)%nat ->
    (forall i : nat, (i < m)%nat -> get_vec i M <> Zero) ->
    (forall i : nat, (i < o)%nat -> get_vec i A <> Zero) ->
    forall j , (j <= m)%nat ->
          (linearly_dependent (submatrix_column j A) \/
             (exists indices_list : list nat,
                 length indices_list = (m - j)%nat /\
                   incl indices_list (List.seq 0 m) /\
                   (forall v : Vector n,
                       span M v <->
                         (span
                            (smash
                               (submatrix_column j A)
                               (matrix_column_choose indices_list M))
                            v)))).
Proof. intros n m o P M A H0 H1 H2 H3 H4 nonzero_col_M nonzero_col_A  j H5.
  induction j.
  - right.
    exists (List.seq 0 m).
    split.
    + rewrite seq_length. lia.
    + split.
      * unfold incl.
        intros a H6.
        assumption.
      * intros v.
        -- assert (H7 : submatrix_column 0 A = @Zero n 0).
           { apply submatrix_column_zero. }
           rewrite H7.
           assert (H8 : matrix_column_choose (List.seq 0 m) M = M).
           { apply matrix_column_choose_original.
             assumption. }
           rewrite H8.
           assert (H9 : smash (@Zero n 0) M = M).
           { prep_matrix_equality.
             unfold smash.
             bdestruct_all.
             replace (y - 0)%nat with y by lia.
             reflexivity. }
           rewrite seq_length.
           rewrite H9.
           split; auto.
  - assert (H6 : (j <= m)%nat). { lia. }
    specialize (IHj H6).
    destruct IHj as [H7 | H7].
    + left.
      assert (H8 : submatrix_column j A = submatrix_column j (submatrix_column (s j) A)).
      { rewrite subsubmatrix_column_inner; auto. }
      rewrite H8 in H7.
      apply linearly_dependent_submatrix_column in H7; auto.
    + destruct H7 as [indices_list [length_indices_list [incl_indices_list eq_span]]].
      assert (H7 : WF_Matrix (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))).
      { auto with wf_db. }
      assert (H8 : forall i : nat, (i < s m)%nat ->
                       get_vec i (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) <> @Zero n (s m)).
      { intros i0 H8.
        bdestruct (i0 <? s j).
        - rewrite get_vec_smash_left; try lia.
          rewrite get_vec_submatrix_column; try lia.
          apply nonzero_col_A; lia.
        - rewrite get_vec_smash_right; try lia.
          rewrite get_vec_matrix_column_choose with (d := 0%nat); trivial; try lia.
          apply nonzero_col_M.
          assert (H10 : In (nth (i0 - s j) indices_list 0%nat) indices_list). { apply nth_In; lia. }
          apply incl_indices_list in H10.
          rewrite in_seq in H10.
          lia. }
      assert (H9 : linearly_dependent
                (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))).
      { unfold linearly_dependent.
        assert (H9 : span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_vec j A)).
        { rewrite <- eq_span.
          unfold basis in H2.
          destruct H2 as [subspaceP [MinP [MspansP lin_indep_m]]].
          apply MspansP.
          apply H3.
          lia. }
        unfold span in H9.
        destruct H9 as [a [WFa H9]].
        exists (fun r c => if (r <? j)%nat then a r c else
                     if (r =? j)%nat then
                       if (c =? 0)%nat then (Copp C1) else C0
                     else a (r - 1)%nat c).
        repeat split.
        - unfold WF_Matrix.
          intros x y H10.
          unfold WF_Matrix in WFa.
          bdestruct_all; trivial.
          + rewrite WFa; trivial; lia.
          + rewrite WFa; trivial; lia.
        - intro H10.
          apply f_equal_inv with (x := j) in H10.
          apply f_equal_inv with (x := 0%nat) in H10.
          simpl in H10.
          rewrite Nat.ltb_irrefl in H10.
          rewrite Nat.eqb_refl in H10.
          inversion H10; lra.
        - unfold smash, submatrix_column, matrix_column_choose, list_vector_to_matrix, Mmult.
          prep_matrix_equality.
          replace (@ Zero n 1 x y) with C0 by easy.
          rewrite length_indices_list.
          replace (s j + (m - j))%nat with ((j) + ((1) + (m - j)))%nat by lia.

          rewrite big_sum_sum with (m := j) (n := (1 + (m - j))%nat).
          rewrite big_sum_sum with (m := 1%nat) (n := (m - j)%nat).
          assert (H10 : forall x y z : C, x + (y + z) = (x + z) + y). { intros. lca. }
          rewrite H10.
          simpl.
          rewrite Cplus_0_l.
          bdestruct_all; trivial.
          
          + subst.
            clear H10. clear H11. clear H12.  clear H14.
            assert (H10 : forall x y z : C, x + y = z -> (x + y) + z * (Copp C1) = 0).
            { intros.
              rewrite H10.
              lca. }
            apply H10.
            replace (j + 0)%nat with j by lia.
            apply f_equal_inv with (x := x) in H9.
            apply f_equal_inv with (x := 0%nat) in H9.
            unfold get_vec in H9.
            simpl in H9.
            rewrite H9.
            unfold smash, submatrix_column, matrix_column_choose, list_vector_to_matrix, Mmult.
            rewrite length_indices_list.
            rewrite big_sum_sum with (m := j) (n := (m - j)%nat).
            simpl.
            f_equal.
            * apply big_sum_eq_bounded.
              intros x0 H11.
              bdestruct_all.
              reflexivity.
            * apply big_sum_eq_bounded.
              intros x0 H11.
              bdestruct_all.
              replace (j + s x0 - s j)%nat with x0 by lia.
              replace (j + x0 - j)%nat with x0 by lia.
              replace (j + s x0 - 1)%nat with (j + x0)%nat by lia.
              reflexivity.
          + unfold WF_Matrix in WFa.
            rewrite Cmult_0_r, Cplus_0_r.
            rewrite <- Cplus_0_r.
            f_equal.
            * rewrite big_sum_0_bounded; trivial.
              intros x0 H15.
              bdestruct_all.
              rewrite WFa; trivial.
              -- lca.
              -- lia.
            * rewrite big_sum_0_bounded; trivial.
              intros x0 H15.
              bdestruct_all.
              rewrite WFa; trivial.
              -- lca.
              -- lia. }
      
      assert (H10 : (s m = s j + length indices_list)%nat).
      { rewrite length_indices_list. rewrite <- Nat.add_1_r. lia. }
      rewrite H10 in H8.
      pose (linearly_dependent_bounded_linear_combination
              (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))
              H7 H8 H9) as H11.
      destruct H11 as [k [H11 [a [WFa H12]]]].
(* split k into two cases: 
1. when k corresponds to (submatrix_column (s j) A)
2. when k corresponds to (matrix_column_choose indices_list M)
bdestruct (k <? s j). *)
      bdestruct (k <? s j).
      * (* For case 1: k < s j *)
        (* We can get "get_vec k (submatrix_column (s j) A)
           = (submatrix_column k (submatrix_column (s j) A)) × a" *)
        rewrite get_vec_smash_left in H12; try lia.
        rewrite submatrix_column_smash_left in H12; try lia.
        (* Prove that  (submatrix_column (s j) A) is linearly_dependent by proving a separate lemma "get_vec k A = (submatrix_column k A) × a -> linearly_dependent A" then substitute A with (submatrix_column (s j) A) to get "linearly_dependent (submatrix_column (s j) A)" *)
        apply get_vec_submatrix_column_linearly_dependent with (k := k) (a := a) (A := (submatrix_column (s j) A)) in H12; auto.
      * (* For case 2: k >= s j *)
        (* We prove the assertion "span (submatrix_column k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))) (get_vec k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        assert (H14 : span (submatrix_column k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))) (get_vec k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))).
        { unfold span.
          exists a.
          auto. }
        (* Then, by using "span_submatrix_column_span_reduce_col" we prove the assertion "span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) (get_vec k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        apply span_submatrix_column_span_reduce_col with (i := k) in H14; auto.
        2: { rewrite length_indices_list.
             assert (k <= j + (m - j))%nat; trivial; lia. }
        (* Then, by using "equal_span_reduce_col" and "equal_span_reduce_col_inv" we can prove the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u" *)
        assert (H15 : forall u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u).
        { intros u.
          split.
          - intros H15.
            apply equal_span_reduce_col; trivial.
            rewrite length_indices_list.
            assert (k < s (j + (m - j)))%nat; trivial; lia.
          - intros H15.
            apply equal_span_reduce_col_inv with (i := k); trivial.
            rewrite length_indices_list.
            assert (k < s (j + (m - j)))%nat; trivial; lia. }
        (* We can directly prove the assertion "∀ u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H16 : forall u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u).
        { intros u H16.
          unfold span.
          unfold span in H16.
          rewrite length_indices_list in *.
          replace (j + (m - j))%nat with m in H16 by lia.
          replace (s j + (m - j))%nat with (s m) by lia.
          destruct H16 as [b [WFb H16]].
          exists (fun r c => if (r <? j)%nat then b r c else if (r =? j)%nat then C0 else b (r - 1)%nat c).
          split.
          - unfold WF_Matrix.
            intros x y H17.
            bdestruct_all; trivial.
            assert (y >= 1)%nat; auto; try lia.
            destruct H17; auto.
            assert (x - 1 >= m)%nat; auto; lia.
          - rewrite H16.
            unfold smash, Mmult, submatrix_column.
            prep_matrix_equality.
            replace m with (j + (m - j))%nat at 1 by lia.
            rewrite big_sum_sum with (m := j) (n := (m - j)%nat) at 1.
            replace (s m) with (j + ((s m) - j))%nat at 1 by lia.
            rewrite big_sum_sum with (m := j) (n := ((s m) - j)%nat) at 1.
            f_equal.
            + apply big_sum_eq_bounded.
              intros x0 H17.
              bdestruct_all; trivial.
            + replace (s m - j)%nat with (1 + (m - j))%nat at 1 by lia.
              rewrite big_sum_sum with (m := 1%nat) (n := (m - j)%nat) at 1.
              simpl.
              rewrite ! Cplus_0_l.
              rewrite <- Cplus_0_l at 1.
              f_equal.
              * bdestruct_all.
                lca.
              * apply big_sum_eq_bounded.
                intros x0 H17.
                bdestruct_all.
                replace (j + x0 - j)%nat with x0 by lia.
                replace (j + s x0 - s j)%nat with x0 by lia.
                replace (j + s x0 - 1)%nat with (j + x0)%nat by lia.
                reflexivity. }
        (* Using "forall i : nat, (i < o)%nat -> P (get_vec i A)" and "basis P M" and "∀ v, span M v <-> span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) v" and by proving the assertion "get_vec j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) = get_vec j A" we can prove the assertion "span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_vec j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        assert (H17 : span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_vec j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))).
        { rewrite get_vec_smash_left; try lia.
          rewrite get_vec_submatrix_column; try lia.
          rewrite <- eq_span.
          unfold basis in H2.
          destruct H2 as [subspaceP [MinP [MspansP lin_indep_M]]].
          apply MspansP.
          apply H3.
          lia. }
        (* By proving a separate general lemma "k <= size of A -> reduce_col (smash A B) k = smash (reduce_col A k) B" and by proving a separate lemma "reduce_col (submatrix_column (s j) A) j = submatrix_column j A", we can prove the assertion "smash (submatrix_column j A) (matrix_column_choose indices_list M) = reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j" *)
        assert (H18 : smash (submatrix_column j A) (matrix_column_choose indices_list M) = reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j).
        { rewrite reduce_col_smash_left, reduce_col_submatrix_column_last; trivial. }
        (* By combining the above assertions, we can get the assertion "span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j) (get_vec j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        rewrite H18 in H17.
        (* By using the lemma "equal_span_reduce_col", we can get the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u -> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j) u" *)
        assert (H19 : forall u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u -> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j) u).
        { intros u H19.
          apply equal_span_reduce_col; trivial.
          rewrite length_indices_list.
          assert (j < 1 + (j + (m - j)))%nat; trivial; lia. }
        (* By combining the above assertions, we can get the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u" *)
        rewrite <- H18 in H19.
        (* Thus, we get the assertion "∀ u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H20 : forall u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u).
        { intros u.
          split; auto. }
        (* We can now obtain the assertion "∀ u, span M u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H21 : forall u, span M u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u).
        { intros u.
          split.
          - intros H21.
            rewrite <- H20, <- eq_span; trivial.
          - intros H21.
            rewrite eq_span, H20; trivial. }
        (* By using the above assertions, we can obtain the assertion "∀ u, span M u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u" *)
        assert (H22 : forall u, span M u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u).
        { intros u.
          split.
          - intros H22.
            rewrite <- H15, <- H21; trivial.
          - intros H22.
            rewrite H21, H15; trivial. }
        (* We need to show that "reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k = smash (submatrix_column (s j) A) (reduce_col (matrix_column_choose indices_list M) (k - # around (s j)))". We can do this by proving a separate general lemma "k > size of A -> reduce_col (smash A B) k = smash A (reduce_col B (k - size of A))" *)
        assert (H23 : reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k = @smash n (s j) (m - j - 1)%nat (submatrix_column (s j) A) (reduce_col (matrix_column_choose indices_list M) (k - (s j)))).
        { rewrite ! length_indices_list.
          replace (Init.Nat.sub m j) with (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O))) by lia.
          replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
           match n0 return nat with
           | O => m0
           | Datatypes.S p => Datatypes.S (add p m0)
           end) j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O))))
            with
            (Init.Nat.add (Datatypes.S j) (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))
            by (rewrite Nat.add_succ_comm; trivial).
          rewrite reduce_col_smash_right; easy. }
        (* We show that "reduce_col (matrix_column_choose indices_list M) (k - # around (s j)) = matrix_column_choose indices_list0 M". We can do this by proving a separate general lemma "reduce_col (matrix_column_choose indices_list M) k = matrix_column_choose (delete the kth element of indices_list) M". We delete the kth element in "indices_list" to create indices_list0. Define : firstn n l ++ skipn (n + 1) l  <- ??? try to compute on a concrete sequence *)
        setoid_rewrite reduce_col_matrix_column_choose_delete with (k := (k - s j)%nat) in H23; trivial; try lia.
        (* Using the above, we obtain the assertion "∀ u, span M u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list0 M)) u" *)
        rewrite H23 in H22.
        (* Additionally, we need to show "length indices_list0 = (m - s j)%nat" and "incl indices_list0 (List.seq 0 m)". You might need to prove separate additional lemmas about lists to prove these. *)
        right.
        exists (delete_nth indices_list (k - s j)%nat).
        split.
        -- rewrite length_delete_nth, length_indices_list; lia.
        -- split.
           ++ apply incl_delete_nth; trivial.
           ++ intros v.
              split.
              ** intros H24.
                 rewrite length_delete_nth; try lia.
                 assert (H25 : (Init.Nat.add (Datatypes.S j)
                            (Init.Nat.sub (@length nat indices_list) (Datatypes.S O)))
                         =
                           ((fix add (n m : nat) {struct n} : nat :=
                               match n return nat with
                               | O => m
                               | Datatypes.S p => Datatypes.S (add p m)
                               end) j (@length nat indices_list))).
                 { rewrite length_indices_list, Nat.add_succ_comm.
                   replace (Init.Nat.add j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))) with m by lia.
                   replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
                               match n0 return nat with
                               | O => m0
                               | Datatypes.S p => Datatypes.S (add p m0)
                               end) j (Init.Nat.sub m j))
                     with
                     (Init.Nat.add j (Init.Nat.sub m j))
                     by trivial.
                   lia. }
                 rewrite H25.
                 rewrite <- H22.
                 assumption.
              ** intros H24.
                 rewrite H22.
                 rewrite length_delete_nth, length_indices_list in H24; try lia.
                 rewrite length_indices_list.
                 assert (H25 : (Init.Nat.add (Datatypes.S j)
                                  (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))
                               =
                                 ((fix add (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => m
                                     | Datatypes.S p => Datatypes.S (add p m)
                                     end) j (Init.Nat.sub m j))).
                 { rewrite Nat.add_succ_comm.
                   replace (Init.Nat.add j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))) with m by lia.
                   replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
                               match n0 return nat with
                               | O => m0
                               | Datatypes.S p => Datatypes.S (add p m0)
                               end) j (Init.Nat.sub m j))
                     with
                     (Init.Nat.add j (Init.Nat.sub m j))
                     by trivial.
                   lia. }
                 rewrite H25 in H24.
                 assumption.
Qed.

Lemma invariant_span_final_step : forall {n m o : nat} (P : Vector n -> Prop) (M : Matrix n m) (A : Matrix n o),
    WF_Matrix M -> WF_Matrix A -> basis P M ->
    (forall i : nat, (i < o)%nat -> P (get_vec i A)) -> (o > m)%nat ->
    (forall v : Vector n, span M v <-> span (submatrix_column m A) v) -> linearly_dependent A.
Proof. intros n m o P M A H0 H1 H2 H3 H4 H5.
  (** Show that the m+1 th column (get_vec m A) of A is a linear combination of (submatrix_column m A): (span (submatrix_column m A) (get_vec m A)) **)
  unfold basis in H2.
  destruct H2 as [subspaceP [MinP [MspansP lin_indep_M]]].
  specialize (H3 m H4).
  specialize (MspansP (get_vec m A) H3).
  rewrite H5 in MspansP.
  unfold span in MspansP.
  destruct MspansP as [a [WFa H6]].
  (** Use the lemma "get_vec_submatrix_column_linearly_dependent" to show (linearly_dependent A) **)
  apply (get_vec_submatrix_column_linearly_dependent m a A H4 H6).
Qed.


(** Theorem 34 Let V be a finite-dimensional vector space over a field F, and let {u1,u2,...,um} be a basis for V. If v1,v2,...,vn are any n vectors in V, with n > m, then {v1, v2, . . . , vn} is linearly dependent. **)
(*** Classical Logic used ***)
Lemma dimension_overflow : forall {n m o : nat} (P : Vector n -> Prop) (M : Matrix n m) (A : Matrix n o),
    WF_Matrix M -> WF_Matrix A ->
    basis P M -> (forall i : nat, (i < o)%nat -> P (get_vec i A)) -> (o > m)%nat -> linearly_dependent A.
Proof. intros n m o P M A WFM WFA basisM AinP overflow.
  destruct (Classical_Prop.classic (forall i : nat, (i < m)%nat -> get_vec i M <> Zero)) as [M_nonzero_cols | M_some_zero_cols].
  2 : { apply some_zero_vector_linearly_dependent in M_some_zero_cols.
        unfold basis in basisM.
        destruct basisM as [subspaceP [MinP [MspansP lin_indep_M]]].
        apply lindep_implies_not_linindep in M_some_zero_cols.
        contradiction. }  
  destruct (Classical_Prop.classic (forall i : nat, (i < o)%nat -> get_vec i A <> Zero)) as [A_nonzero_cols | A_some_zero_cols].
  2 : { apply some_zero_vector_linearly_dependent in A_some_zero_cols.
        assumption. }
  remember basisM as basisM'. clear HeqbasisM'.
  unfold basis in basisM'.
  destruct basisM' as [subspaceP [MinP [MspansP lin_indep_M]]].
  assert (m_leq_m : (m <= m)%nat); auto.
  destruct (invariant_span P M A WFM WFA basisM AinP overflow M_nonzero_cols A_nonzero_cols m m_leq_m) as [lin_dep_A_m | [indices_list [length_indices_list [incl_indices_list_seq eq_span]]]].
  - apply linearly_dependent_submatrix_column in lin_dep_A_m; assumption.
  - replace (m - m)%nat with 0%nat in length_indices_list by lia.
    rewrite length_zero_iff_nil in length_indices_list.
    rewrite length_indices_list in eq_span.
    rewrite matrix_column_choose_empty in eq_span.
    rewrite smash_zero in eq_span; auto with wf_db.
    simpl in eq_span.
    rewrite Nat.add_0_r in eq_span.
    apply (invariant_span_final_step P M A WFM WFA basisM AinP overflow eq_span).
Qed.


(* Corollary 35 Let V be a vector space over a field F, and let {u1,u2,...,un}
and {v1,v2,...,vm} be two bases for V. Then m=n.
Proof Since {u1,u2,...,un} is a basis for V and {v1,v2,...,vm} is linearly independent, Theorem 34 implies that m ≤ n. But the same reasoning implies that n ≤ m, and so m = n must hold. *)
Lemma basis_equal_number : forall {n m o : nat} (P : Vector n -> Prop) (A : Matrix n m) (B : Matrix n o),
    WF_Matrix A -> WF_Matrix B -> basis P A -> basis P B -> m = o.
Proof. intros n m o P A B WFA WFB basisA basisB.
  remember basisA as basisA'. clear HeqbasisA'.
  remember basisB as basisB'. clear HeqbasisB'.
  unfold basis in basisA', basisB'.
  destruct basisA' as [subspaceP [AinP [AspansP lin_indep_A]]].
  destruct basisB' as [subspaceP' [BinP [BspansP lin_indep_B]]].
  bdestruct (o <=? m)%nat.
  - bdestruct (m <=? o)%nat.
    + lia.
    + pose (dimension_overflow P B A WFB WFA basisB AinP H1) as lin_dep_B.
      apply lindep_implies_not_linindep in lin_dep_B.
      contradiction.
  - pose (dimension_overflow P A B WFA WFB basisA BinP H0) as lin_dep_B.
    apply lindep_implies_not_linindep in lin_dep_B.
    contradiction.
Qed.

(* Definition 36 Let V be a finite-dimensional vector space. If V is the trivial vector space, then we say that the dimension of V is zero; otherwise, the dimension of V is the number of vectors in a basis for V . *)

Definition dimension {n : nat} (P : Vector n -> Prop) (d : nat) := exists (A : Matrix n d), WF_Matrix A /\ basis P A.
Check dimension.

(* Inductive dimension {n : nat} (P : Vector n -> Prop) (d : nat) :=
| dim : forall (A : Matrix n d), basis P A -> dimension P d.

Definition dimension {n : nat} (P : Vector n -> Prop) := { d : nat & {A : Matrix n d | basis P A } }. *)

Lemma subspace_dimension : forall {n : nat} {P Q : Vector n -> Prop} {d1 d2 : nat},
    subspace P -> subspace Q -> (forall v, Q v -> P v) -> dimension Q d1  -> dimension P d2 ->
    (d1 <= d2)%nat.
Proof. intros n P Q d1 d2 H0 H1 H2 H3 H4.
  bdestruct (d1 <=? d2)%nat; auto.
  unfold dimension in *.
  destruct H3 as [A1 [WFA1 bA1]].
  destruct H4 as [A2 [WFA2 bA2]].
  unfold basis in bA1.
    destruct bA1 as [sQ [A1inQ [A1spQ indA1]]].
  assert (forall i, (i < d1)%nat -> P (get_vec i A1)).
  { intros i0 H3.
    apply H2.
    apply A1inQ; auto. }
  pose (dimension_overflow P A2 A1 WFA2 WFA1 bA2 H3 H5) as H6.
  apply lindep_implies_not_linindep in H6.
  contradiction.
Qed.

Lemma unique_dimension : forall {n d1 d2 : nat} (P : Vector n -> Prop),
    dimension P d1 -> dimension P d2 -> d1 = d2.
Proof. intros n d1 d2 P H0 H1.
  unfold dimension in *.
  destruct H0 as [A [WFA basisA]].
  destruct H1 as [B [WFB basisB]].
  apply (basis_equal_number P A B WFA WFB basisA basisB).
Qed.

Lemma list_vector_to_matrix_nil : forall n : nat, @list_vector_to_matrix n nil = Zero.
Proof. intros n.
  unfold list_vector_to_matrix.
  prep_matrix_equality.
  destruct y; auto.
Qed.


Lemma permutation_list_vector_to_matrix_times_vector : forall {n : nat} {l1 l2 : list (Vector n)},
    Permutation l1 l2 ->
    forall a : Vector (length l1), WF_Matrix a ->
            exists b : Vector (length l2), WF_Matrix b /\
                    (list_vector_to_matrix l1) × a = (list_vector_to_matrix l2) × b /\
                    Permutation (map (fun i => a i 0%nat) (List.seq 0 (length l1))) (map (fun i => b i 0%nat) (List.seq 0 (length l2))).
Proof. intros n l1 l2 H0 a H1.
  induction H0.
  - exists Zero.
    repeat (split; auto with wf_db).
  - assert (@WF_Matrix (length l) 1%nat (fun r c => a (r + 1)%nat c)).
    { unfold WF_Matrix.
      intros x0 y H2.
      apply Permutation_length in H0.
      simpl in *.
      rewrite H1; auto; destruct H2; lia. }
    destruct (IHPermutation (fun r c => a (r + 1)%nat c) H2) as [b [WFb [eqn perm]]].
    exists (fun r c => if (r =? 0)%nat then a 0%nat c else b (r - 1)%nat c).
    repeat (split; auto with wf_db).
    + unfold WF_Matrix.
      intros x0 y H3. 
      apply Permutation_length in H0.
      simpl in *.
      bdestruct_all.
      * subst.
        rewrite H1; auto; lia.
      * rewrite WFb; auto; lia.
    + unfold list_vector_to_matrix, Mmult.
      prep_matrix_equality.
      replace (length (x :: l)) with (s (length l)) by easy.
      replace (length (x :: l')) with (s (length l')) by easy.
      rewrite ! big_sum_shift.
      f_equal.
      apply Permutation_length in H0.
      rewrite H0 in *.
      unfold list_vector_to_matrix, Mmult in eqn.
      apply f_equal_inv with (x := x0) in eqn.
      apply f_equal_inv with (x := y) in eqn.

      assert ((fun x1 : nat => nth (s x1) (x :: l) Zero x0 0%nat * a (s x1) y)
              = (fun x1 : nat => nth x1 l Zero x0 0%nat * a (x1 + 1)%nat y))
        by (apply functional_extensionality; intros; rewrite Nat.add_1_r; auto).
      rewrite H3, eqn.
      apply big_sum_eq_bounded.
      intros x1 H4.
      simpl.
      replace (x1 - 0)%nat with x1 by lia.
      reflexivity.
    + simpl.
      apply Permutation_cons; auto.
      assert ((map (fun i0 : nat => a i0 0%nat) (List.seq 1 (length l)))
              = (map (fun i : nat => a (i + 1)%nat 0%nat) (List.seq 0 (length l)))).
      { apply nth_ext with (d := C0) (d' := C0).
        - rewrite ! map_length, ! seq_length; reflexivity.
        - intros n0 H3.
          rewrite nth_indep with (d' := a 0%nat 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => a i0 0%nat)) (d := 0%nat).
          rewrite nth_indep with (d' := a (0 + 1)%nat 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => a (i0 + 1)%nat 0%nat)) (d := 0%nat).
          f_equal.
          rewrite ! seq_nth.
          lia.
          all : try rewrite map_length, seq_length;
          rewrite map_length, seq_length in H3;
            auto. }
      rewrite H3.
      assert ((map
                 (fun i0 : nat => if (i0 =? 0)%nat then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat)
                 (List.seq 1 (length l')))
              = (map (fun i : nat => b i 0%nat) (List.seq 0 (length l')))).
      { apply nth_ext with (d := C0) (d' := C0).
        - rewrite ! map_length, ! seq_length; reflexivity.
        - intros n0 H4.
          rewrite map_length, seq_length in H4.
          rewrite nth_indep with (d' := (fun i0 : nat => if (i0 =? 0)%nat 
                                                   then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat) 0%nat);
            auto.
          rewrite map_nth with (f := (fun i0 : nat => if (i0 =? 0)%nat
                                                then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat)) (d := 0%nat).
          rewrite nth_indep with (d' := (fun i0 : nat => b i0 0%nat) 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => b i0 0%nat)) (d := 0%nat).
          bdestruct_all.
          + rewrite seq_nth in H5; auto; lia.
          + do 2 f_equal.
            rewrite ! seq_nth; auto; lia.
          + rewrite map_length, seq_length; easy.
          + rewrite map_length, seq_length; easy. }
      rewrite H4.
      auto.
  - exists (fun r c => if (r =? 0)%nat then a 1%nat c else
                 if (r =? 1)%nat then a 0%nat c else a r c).
    repeat (split; intros; auto).
    + unfold WF_Matrix.
      intros x0 y0 H0.
      bdestruct_all; subst; simpl in *; auto; rewrite H1; auto; lia.
    + unfold list_vector_to_matrix, Mmult.
      prep_matrix_equality.
      replace (length (y :: x :: l)) with (s (s (length l))) by easy.
      replace (length (x :: y :: l)) with (s (s (length l))) by easy.
      rewrite ! big_sum_shift.
      simpl.
      rewrite ! Cplus_assoc.
      setoid_rewrite Cplus_comm at 2.
      auto.
    + simpl.
      assert (map
                (fun i0 : nat =>
                   if (i0 =? 0)%nat
                   then a 1%nat 0%nat
                   else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat)
                (List.seq 2 (length l))
              = map (fun i0 : nat => a i0 0%nat) (List.seq 2 (length l))).
      { apply nth_ext with (d := C0) (d' := C0).
        - rewrite ! map_length; reflexivity.
        - intros n0 H0.
          rewrite ! map_length, seq_length in H0.
          rewrite nth_indep with (d' := (fun i0 : nat =>
                                                 if (i0 =? 0)%nat
                                                 then a 1%nat 0%nat
                                                 else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat) 0%nat).
          rewrite map_nth with (f := (fun i0 : nat =>
                                       if (i0 =? 0)%nat
                                       then a 1%nat 0%nat
                                       else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat)).
          rewrite nth_indep with (d' := (fun i0 : nat => a i0 0%nat) 0%nat).
          rewrite map_nth with (f := (fun i0 : nat => a i0 0%nat)).
          bdestruct_all; auto.
          + rewrite seq_nth in H2; auto; lia.
          + rewrite seq_nth in H3; auto; lia.
          + rewrite map_length, seq_length; auto.
          + rewrite map_length, seq_length; auto. }
      rewrite H0.
      apply perm_swap.
  - destruct (IHPermutation1 a H1) as [b [H2 [H3 H4]]].
    destruct (IHPermutation2 b H2) as [c [H5 [H6 H7]]].
    exists c.
    repeat (split; auto).
    + rewrite H3, H6; auto.
    + apply (perm_trans H4 H7).
Qed.

Lemma permutation_preserves_linearly_indep : forall {n : nat} {l1 l2 : list (Vector n)},
    Permutation l1 l2 -> linearly_independent (list_vector_to_matrix l1) ->
    linearly_independent (list_vector_to_matrix l2).
Proof. intros n l1 l2 H0 H1.
  unfold linearly_independent in *.
  intros a H2 H3.
  apply Permutation_sym in H0.
  destruct (permutation_list_vector_to_matrix_times_vector H0 a H2) as [b [H4 [H5 H6]]].
  rewrite H3 in H5.
  symmetry in H5.
  specialize (H1 b H4 H5).
  rewrite H1 in H6.
  unfold Zero in H6.
  rewrite map_const_repeat in H6.
  rewrite seq_length in H6.
  rewrite <- (Permutation_length H0) in H6.
  assert (forall i, nth i (map (fun i : nat => a i 0%nat) (List.seq 0 (length l2))) C0 = C0)
    by (rewrite <- permutation_repeat_nth, map_length, seq_length; auto).
  assert (forall i, (i < length l2)%nat -> a i 0%nat = C0).
  { intros i0 H8.
    assert (a (length l2) 0%nat = C0) by (rewrite H2; auto).
    setoid_rewrite <- H9 in H7 at 1.
    setoid_rewrite map_nth with (d := length l2) in H7.
    specialize (H7 i0).
    rewrite seq_nth in H7; auto. }
  rewrite zero_all_zero in H8; auto.
Qed.
    
Lemma permutation_preserves_span : forall {n : nat} {l1 l2 : list (Vector n)} {P : Vector n -> Prop},
  subspace P -> Permutation l1 l2 ->
  (forall v : Vector n, P v -> span (list_vector_to_matrix l1) v) ->
  (forall v : Vector n, P v -> span (list_vector_to_matrix l2) v).
Proof. intros n l1 l2 P H0 H1 H2 v H3.
  unfold span in *.
  specialize (H2 v H3).
  destruct H2 as [a [WFa H4]].
  destruct (permutation_list_vector_to_matrix_times_vector H1 a WFa) as [b [WFb [H5 Perm]]].
  exists b.
  split; auto.
  rewrite <- H5; apply H4.
Qed.

Lemma permutation_preserves_subspace_containment : forall {n : nat} {l1 l2 : list (Vector n)} {P : Vector n -> Prop},
        subspace P -> Permutation l1 l2 ->
        (forall i : nat, (i < (length l1))%nat -> P (get_vec i (list_vector_to_matrix l1))) ->
        (forall i : nat, (i < (length l2))%nat -> P (get_vec i (list_vector_to_matrix l2))).
Proof. intros n l1 l2 P H0 H1 H2 i0 H3.
  unfold get_vec, list_vector_to_matrix in *.
  remember H1 as H4. clear HeqH4.
  rewrite Permutation_nth in H4.
  destruct H4 as [H4 [f [H5 [H6 H7]]]].
  remember H6 as H8. clear HeqH8.
  rewrite (FinFun.bInjective_bSurjective H5) in H8.
  destruct (FinFun.bSurjective_bBijective H5 H8) as [g [H9 H10]].
  rewrite H4 in *.
  rewrite H7; auto.
Qed.

Lemma permutation_preserves_map_get_vec_matrix : forall {n m : nat} {indices_list1 indices_list2 : list nat} (M : Matrix n m),
    Permutation indices_list1 indices_list2 ->
    Permutation (map (fun i : nat => get_vec i M) indices_list1) (map (fun i : nat => get_vec i M) indices_list2).
Proof. intros n m indices_list1 indices_list2 M H0.
  remember H0 as H0'. clear HeqH0'.
  rewrite Permutation_nth in H0.
  destruct H0 as [eq_len [f [bFunf [bInjf eq_nth]]]].
  rewrite Permutation_nth.
  split; try rewrite ! map_length, eq_len; auto. 
  exists f.
  repeat split; try rewrite map_length; auto.
  intros x H0.
  setoid_rewrite map_nth with (f := (fun i0 : nat => get_vec i0 M)).
  f_equal.
  apply eq_nth; auto.
  Unshelve.
  auto.
Qed.  

Lemma permutation_preserves_basis : forall {n m : nat} {indices_list1 indices_list2 : list nat} {P : Vector n -> Prop} {M : Matrix n m},
    WF_Matrix M -> subspace P -> Permutation indices_list1 indices_list2 ->
    (basis P (matrix_column_choose indices_list1 M) <-> basis P (matrix_column_choose indices_list2 M)).
Proof. intros n m indices_list1 indices_list2 P M H0 H1 H2.
  pose (permutation_preserves_map_get_vec_matrix M H2).
  unfold basis, matrix_column_choose. 
  split; intros H3; destruct H3 as [H4 [H5 [H6 H7]]]; repeat (split; intros; auto).
  - pose (permutation_preserves_subspace_containment H4 p).
    rewrite ! map_length in p0.
    specialize (p0 H5).
    apply p0; auto.
  -  pose (permutation_preserves_span H4 p).
     rewrite ! map_length in s.
     specialize (s H6).
     apply s; auto.
  - pose (permutation_preserves_linearly_indep p).
    rewrite ! map_length in l.
    specialize (l H7); auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_subspace_containment H4 p).
    rewrite ! map_length in p0.
    specialize (p0 H5).
    apply p0; auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_span H4 p).
    rewrite ! map_length in s.
    specialize (s H6).
    apply s; auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_linearly_indep p).
    rewrite ! map_length in l.
    specialize (l H7); auto.
Qed.

(* Theorem 41 Let V be a nontrivial vector space over a field F, and suppose {u1,u2,...,um} spans V. Then a subset of {u1,u2,...,um} is a basis for V. *)
(*** Classical Logic used ***)
Lemma subset_basis : forall {n m : nat} {P : Vector n -> Prop} {M : Matrix n m},
    WF_Matrix M -> (m > 0)%nat -> subspace P -> (forall i, (i < m)%nat -> P (get_vec i M)) -> (forall v, P v -> span M v) ->
    (exists v, v <> Zero /\ P v) -> 
    (exists indices_list, incl indices_list (List.seq 0 m) /\ NoDup indices_list /\
                       basis P (matrix_column_choose indices_list M)).
Proof. intros n m P M H0 H1 H2 H3 H4 H5.
  destruct (Classical_Prop.classic (linearly_dependent M)).
  - induction m.
    + inversion H1.
    + destruct m.
      * assert (M <> Zero).
        { destruct (Classical_Prop.classic (M = Zero)).
          - destruct H5 as [v [H5 H5']].
            specialize (H4 v H5').
            unfold span in H4.
            destruct H4 as [a [H4 H4']].
            rewrite H4' in H5.
            rewrite H7 in H5.
             rewrite Mmult_0_l in H5.
             contradiction.
          - assumption. }
        pose (lin_indep_vec M H0 H7) as H8.
        apply lindep_implies_not_linindep in H6.
        contradiction.
      * destruct (lin_dep_gen_elem M H0 H6) as [i [H7 [v [H8 H9]]]].
        assert (span (reduce_col M i) (get_vec i M)).
        { unfold span.
          exists ((Copp C1) .* v).
          split; auto with wf_db.
          distribute_scale.
          rewrite H9.
          distribute_scale.
          lma'. }
        pose (equal_span_reduce_col M i H7 H10) as H11.
        assert (WF_Matrix (reduce_col M i)); auto with wf_db.
        assert (s m > 0)%nat; try lia.
        assert (forall i0 : nat, (i0 < s m)%nat -> P (get_vec i0 (reduce_col M i))).
        { intros i0 H14.
          bdestruct (i0 <? i).
          - rewrite get_col_reduce_col; auto.
          - rewrite get_vec_reduce_col_back; auto; apply H3; lia. }
        assert (forall v : Vector n, P v -> span (reduce_col M i) v).
        { intros v0 H15.
          apply H11; auto. }
        destruct (Classical_Prop.classic (linearly_dependent (reduce_col M i))).
        -- specialize (IHm (reduce_col M i) H12 H13 H14 H15 H16).
           destruct IHm as [indices_list [incl_indices_list basis_P]].
           exists (map (fun n => if (n <? i) then n else s n) indices_list).
           split.
           ++ unfold incl.
              intros a H17.
              rewrite in_map_iff in H17.
              destruct H17 as [x [H17 H18]].
              bdestruct (x <? i).
              ** simpl in H17.
                 rewrite <- H17.
                 rewrite in_seq.
                 lia.
              ** simpl in H17.
                 rewrite <- H17.
                 unfold incl in incl_indices_list.
                 specialize (incl_indices_list x H18).
                 rewrite in_seq in incl_indices_list.
                 rewrite in_seq.
                 lia.
           ++ split.
              ** apply NoDup_map_inv
                   with (f := fun n0 : nat => if (n0 <? i)%nat then n0 else (Nat.pred n0)).
                 rewrite map_map.
                 assert ((fun x : nat =>
                            if (if x <? i then x else s x) <? i
                            then if x <? i then x else s x
                            else Nat.pred (if x <? i then x else s x))
                         = (fun x : nat => x)).
                 { apply functional_extensionality.
                   intros x.
                   bdestruct_all; auto. }
                 rewrite H17.
                 rewrite map_id.
                 destruct basis_P; auto.
              ** unfold basis.
                 assert ((matrix_column_choose (map (fun n0 : nat => if n0 <? i then n0 else s n0) indices_list) M) = (matrix_column_choose indices_list (reduce_col M i))).
                 { unfold matrix_column_choose, list_vector_to_matrix.
                   prep_matrix_equality.
                   rewrite map_map.
                   unfold reduce_col.
                   assert (Zero = ((fun x0 : nat => get_vec (if x0 <? i then x0 else s x0) M) (s m))).
                   { prep_matrix_equality.
                     unfold get_vec.
                     bdestruct_all; auto.
                     rewrite H0; auto; lia. }
                   rewrite H17 at 1.
                   rewrite map_nth with (d := s m).
                   assert (Zero = (fun i0 : nat => @get_col n (s m) (fun x0 y0 : nat => if y0 <? i then M x0 y0 else M x0 (1 + y0)%nat) i0) (s m)).
                   { prep_matrix_equality.
                     unfold get_vec.
                     bdestruct_all; auto.
                     rewrite H0; auto; lia. }
                   rewrite H18.
                   rewrite map_nth with (d := s m).
                   bdestruct_all.
                   - unfold get_vec.
                     bdestruct_all.
                     reflexivity.
                   - unfold get_vec.
                     bdestruct_all.
                     reflexivity. }
                 rewrite ! H17.
                 destruct basis_P as [subspaceP [in_P [spans_P lin_ind]]].
                 rewrite ! map_length.
                 repeat (split; auto).
        -- apply not_lindep_implies_linindep in H16.
           exists (delete_nth (List.seq 0 (s (s m))) i).
           split.
           ++ unfold incl.
              intros a H17.
              unfold delete_nth in H17.
              rewrite in_app_iff in H17.
              destruct H17.
              ** apply firstn_subset in H17; auto.
              ** apply skipn_subset in H17; auto.
           ++ split.
              ** unfold delete_nth.
                 apply NoDup_remove_1 with (a := i).
                 assert (i :: skipn (i + 1) (List.seq 0 (s (s m))) = skipn i (List.seq 0 (s (s m)))).
                 { setoid_rewrite nth_helper with (x := 0%nat) at 2.
                   replace (s i) with (i + 1)%nat by lia.
                   rewrite seq_nth.
                   all : try rewrite seq_length; auto. }
                 rewrite H17.
                 rewrite firstn_skipn.
                 apply seq_NoDup.
              ** unfold basis.
                 rewrite <- ! reduce_col_matrix_column_choose_delete; auto.
                 2: rewrite seq_length; assumption.
                 rewrite ! matrix_column_choose_original; auto.
                 rewrite ! length_delete_nth.
                 2: rewrite seq_length; assumption.
                 rewrite ! seq_length.
                 replace ((s (s m)) - 1)%nat with (s m) by lia.
                 repeat (split; auto).
  - apply not_lindep_implies_linindep in H6.
    exists (List.seq 0 m).
    split.
    + apply incl_refl.
    + split.
      * apply seq_NoDup.
      * unfold basis.
        rewrite matrix_column_choose_original; auto.
        rewrite ! seq_length.
        repeat (split; try assumption).
Qed.


(* Exercise 2.5.4 Let V be a vector space over a field F and let {u1,...,uk} be a linearly independent subset of V . Prove that if v ̸∈ sp{u1, . . . , uk}, then {u1,...,uk,v} is also linearly independent. *)
Lemma extend1_lin_indep : forall {n m : nat} {P : Vector n -> Prop} {A : Matrix n m} {v : Vector n},
    subspace P -> WF_Matrix A -> WF_Matrix v -> linearly_independent A ->
    (forall i, (i < m)%nat -> P (get_vec i A)) ->
    ~ span A v -> linearly_independent (col_append A v).
Proof. intros n m P A v H0 H1 H2 H3 H4 H5.
  unfold span in H5.
  unfold linearly_independent in H3.
  unfold linearly_independent.
  intros a H6 H7.
  destruct (Classical_Prop.classic (a = Zero)); auto.
  assert (a m 0%nat <> C0).
  { intro.
    assert (col_append A v × a = A × (reduce_row a m)).
    { unfold col_append, col_wedge, reduce_row, Mmult.
      prep_matrix_equality.
      simpl.
      bdestruct_all. clear H11.
      bdestruct (y =? 0)%nat;
        [rewrite H11; rewrite H9 | rewrite H6; try lia];
        Csimpl;
        apply big_sum_eq_bounded;
        intros x0 H12;
        bdestruct_all;
        reflexivity. }
    rewrite H10 in H7.
    assert (WF_Matrix (reduce_row a m)); auto with wf_db.
    specialize (H3 (reduce_row a m) H11 H7).
    assert (a = Zero).
    { prep_matrix_equality.
      bdestruct (y =? 0)%nat.
      - subst.
        bdestruct (x <? m)%nat.
        + unfold reduce_row in H3.
          apply f_equal_inv with (x := x) in H3.
          apply f_equal_inv with (x := 0%nat) in H3.
          rewrite <- Nat.ltb_lt in H12.
          rewrite H12 in H3.
          assumption.
        + bdestruct (x =? m)%nat.
          * subst.
            assumption.
          * rewrite H6; auto; lia.
      - rewrite H6; auto; lia. }
    contradiction. }
  assert (v = A × (((- C1)%C * /(a m 0%nat)) .* (reduce_row a m))).
  { assert (col_append A v × a = A × (reduce_row a m) .+ (a m 0%nat) .* v).
    { unfold col_append, col_wedge, reduce_row, Matrix.scale, Mmult, Mplus.
      prep_matrix_equality.
      simpl.
      bdestruct_all. clear H11.
      bdestruct (y =? 0)%nat.
      - subst.
        f_equal.
        + apply big_sum_eq_bounded.
          intros x0 H11.
          bdestruct_all.
          reflexivity.
        + rewrite Cmult_comm.
          reflexivity.
      - setoid_rewrite H6 at 2; try lia.
        setoid_rewrite H2 at 3; try lia.
        Csimpl.
        apply big_sum_eq_bounded.
        intros x0 H12.
        bdestruct_all.
        reflexivity. }
    rewrite H10 in H7.
    rewrite Mplus_comm in H7.
    apply Mplus_inj_r with (m := (- C1) .* (A × reduce_row a m)) in H7.
    rewrite Mplus_assoc in H7.
    assert (forall {n m} (A : Matrix n m), WF_Matrix A -> A .+ - C1 .* A = Zero).
    { intros n0 m0 A0 H11. lma'. }
    rewrite H11 in H7; auto with wf_db.
    rewrite Mplus_0_r, Mplus_0_l in H7.
    apply Mscale_cancel with (c := a m 0%nat); auto.
    rewrite H7.
    distribute_scale.
    f_equal.
    setoid_rewrite Cmult_comm at 2.
    rewrite Cmult_assoc.
    rewrite Cinv_r; auto.
    lca. }
  assert (WF_Matrix (- C1 * / a m 0%nat .* reduce_row a m)); auto with wf_db.
  pose (Classical_Pred_Type.not_ex_all_not (Vector m) (fun a : Vector m => WF_Matrix a /\ v = A × a) H5 (- C1 * / a m 0%nat .* reduce_row a m)) as H12.
  simpl in H12.
  apply Classical_Prop.not_and_or in H12.
  destruct H12; contradiction.
Qed.


(* Theorem 43 Let V be a finite-dimensional vector space over a field F, and suppose {u1, u2, . . . , uk} ⊂ V is linearly independent. If {u1, u2, . . . , uk} does not span V , then there exist vectors uk+1 , . . . , un such that
{u1,u2,...,uk,uk+1,...,un}
is a basis for V. *)

Definition temp_before {n k : nat} (P : Vector n -> Prop) (A : Matrix n k) (m : nat) :=
  (exists (B : Matrix n (m - k)), (WF_Matrix B) /\ (forall i, (i < (m - k))%nat -> P (get_vec i B)) /\
                               (linearly_independent (smash A B)) /\
                               ~ (forall v, P v -> span (smash A B) v)).

Definition temp_middle {n k : nat} (P : Vector n -> Prop) (A : Matrix n k) (m : nat) :=
  (exists (B : Matrix n (m - k)), (WF_Matrix B) /\ (forall i, (i < (m - k))%nat -> P (get_vec i B)) /\
                               (linearly_independent (smash A B)) /\
                               (forall v, P v -> span (smash A B) v)).

Definition temp_after {n k : nat} (P : Vector n -> Prop) (A : Matrix n k) (m : nat) :=
  (forall (B : Matrix n (m - k)), (WF_Matrix B) -> (forall i, (i < (m - k))%nat -> P (get_vec i B)) ->
                             linearly_dependent (smash A B)).

Lemma temp_begin : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    ((temp_before P A (k + 1)%nat) \/ (temp_middle P A (k + 1)%nat)).
Proof. intros n k P A H0 H1 H2 H3 H4. 
  apply Classical_Pred_Type.not_all_ex_not in H4.
  destruct H4 as [v H4].
  apply Classical_Prop.imply_to_and in H4.
  destruct H4.
  assert (WF_Matrix v) by (apply (WF_subspace H1 H4); auto).
  pose (extend1_lin_indep H1 H0 H6 H3 H2 H5).
  unfold col_append in l.
  rewrite smash_append in l; auto.
  destruct (Classical_Prop.classic (forall w, P w -> span (smash A v) w)).
  - right.
    unfold temp_middle.
    exists v.
    replace (k + 1 - k)%nat with 1%nat by lia.
    replace (s k) with (k + 1)%nat by lia.
    repeat (split; auto).
    + intros i0 H8.
      replace i0 with 0%nat by lia.
      rewrite get_vec_vec; auto.
    + replace (k + 1)%nat with (s k) by lia; auto.
  - left.
    unfold temp_before.
    exists v.
    replace (k + 1 - k)%nat with 1%nat by lia.
    replace (s k) with (k + 1)%nat by lia.
    repeat (split; auto).
    + intros i0 H8.
      replace i0 with 0%nat by lia.
      rewrite get_vec_vec; auto.
    + replace (k + 1)%nat with (s k) by lia; auto.
Qed.

Lemma temp_end : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (temp_after P A (n + 1)%nat).
Proof. intros n k P A H0 H1 H2 H3.
  unfold temp_after.
  intros B H4 H5.
  apply gt_dim_lindep; auto with wf_db; lia.
Qed.

Lemma temp_before_step : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_before P A m) ->
          ((temp_before P A (s m)) \/ (temp_middle P A (s m)))). 
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_before in H5.
  destruct H5 as [B [WFB [BinP [linindAB notspanP]]]].
  apply Classical_Pred_Type.not_all_ex_not in notspanP.
  destruct notspanP as [v notspanP].
  apply Classical_Prop.imply_to_and in notspanP.
  destruct notspanP as [vinP vnotinspan].
  assert (WF_Matrix (smash A B)); auto with wf_db.
  assert (forall i : nat, (i < m)%nat -> P (get_vec i (smash A B))).
  { intros i0 H6.
    bdestruct (i0 <? k)%nat.
    - rewrite get_vec_smash_left; try apply H2; lia.
    - rewrite get_vec_smash_right; try apply BinP; lia. }
  replace m with (k + (m - k))%nat in H6 by lia.
  assert (WFv : WF_Matrix v) by (apply (WF_subspace H1 vinP); auto).
  pose (extend1_lin_indep H1 H5 WFv linindAB H6 vnotinspan).
  unfold col_append in l.
  rewrite smash_append in l; auto with wf_db.
  rewrite smash_assoc in l.
  assert (forall i : nat, (i < (m - k) + 1)%nat -> P (get_vec i (smash B v))).
  { intros i0 H7.
    bdestruct (i0 <? m - k)%nat.
    - rewrite get_vec_smash_left; try apply BinP; lia.
    - rewrite get_vec_smash_right; replace (i0 - (m - k))%nat with 0%nat by lia;
        try rewrite get_vec_vec; try apply vinP; auto with wf_db; lia. }
  destruct (Classical_Prop.classic (forall w, P w -> span (smash A (smash B v)) w)).
  - right.
    unfold temp_middle.
    exists (smash B v).
    replace (s m - k)%nat with ((m - k) + 1)%nat by lia.
    repeat (split; auto with wf_db).
    replace (k + (m - k + 1))%nat with (s (k + (m - k)))%nat by lia. 
    apply l.
  - left.
    unfold temp_before.
    exists (smash B v).
    replace (s m - k)%nat with ((m - k) + 1)%nat by lia.
    repeat (split; auto with wf_db).
    replace (k + (m - k + 1))%nat with (s (k + (m - k)))%nat by lia. 
    apply l.
Qed.

Lemma temp_middle_step : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_middle P A m) ->
          (temp_after P A (s m))).
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_middle in H5.
  destruct H5 as [B [WFB [BinP [linindAB ABspansP]]]].
  assert (basis P (smash A B)).
  repeat (split; auto).
  - intros i0 H5.
    bdestruct (i0 <? k)%nat.
    + rewrite get_vec_smash_left; try apply H2; lia.
    + rewrite get_vec_smash_right; try apply BinP; lia.
  - unfold temp_after.
    intros B0 H6 H7.
    apply (dimension_overflow P (smash A B) (smash A B0)); auto with wf_db; try lia.
    intros i0 H8.
    bdestruct (i0 <? k).
    + rewrite get_vec_smash_left; auto.
    + rewrite get_vec_smash_right; auto; apply H7; lia.
Qed.

Lemma temp_after_step : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_after P A m) ->
          (temp_after P A (s m))).
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_after.
  intros B H6 H7.
  assert ((smash A B)
          = (col_append (submatrix_column m (smash A B)) (get_vec (m - k)%nat B))).
  { prep_matrix_equality.
    assert (WF_Matrix (smash A B)); auto with wf_db.
    assert (WF_Matrix (col_append (submatrix_column m (smash A B)) (get_vec (m - k)%nat B))). unfold col_append. auto with wf_db.
    bdestruct (x <? n)%nat.
    - bdestruct (y <? s m)%nat.
      + unfold smash, submatrix_column, col_append, col_wedge, get_vec.
        bdestruct_all; auto.
      + rewrite H8; try lia.
        rewrite H9; try lia.
        reflexivity.
    - rewrite H8; try lia.
      rewrite H9; try lia.
      reflexivity. }
  rewrite H8.
  replace (k + (s m - k))%nat with (s m) by lia.
  unfold col_append.
  apply lin_dep_col_wedge. lia.
  unfold temp_after in H5.
  setoid_rewrite submatrix_column_smash_right; auto.
  assert (WF_Matrix (submatrix_column (m - k) B)); auto with wf_db.
  assert (forall i : nat, (i < m - k)%nat -> P (get_vec i (submatrix_column (m - k) B))).
  { intros i0 H10.
    rewrite get_vec_submatrix_column; auto.
    apply H7; lia. }
  replace (k + (m - k))%nat with m in H5 by lia.
  apply (H5 (submatrix_column (m - k) B) H9 H10).
Qed.

Lemma temp_no_middle_all_before : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
     (forall m, (k < m)%nat -> ~ (temp_middle P A m)) ->
    (forall m, (k < m)%nat -> (temp_before P A m)).
Proof. intros n k P A H0 H1 H2 H3 H4 H5 m H6.
  induction m.
  - inversion H6.
  - bdestruct (m =? k)%nat.
    + subst.
      replace (s k) with (k + 1)%nat in * by lia.
      assert (temp_before P A (k + 1)%nat \/ temp_middle P A (k + 1)%nat)
        by (apply temp_begin; auto).
      destruct H7; auto.
      contradict H7; auto.
    + assert (k < m)%nat by lia.
      apply IHm in H8.
      apply temp_before_step in H8; auto; try lia.
      destruct H8; auto.
      contradict H8; auto.
Qed.

Lemma temp_all_after_from_end : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (n < m)%nat -> temp_after P A m).
Proof. intros n k P A H0 H1 H2 H3 m H4.
  induction m.
  - inversion H4.
  - bdestruct (m =? n)%nat.
    + subst.
      replace (s n) with (n + 1)%nat in * by lia.
      apply temp_end; auto.
    + assert (n < m)%nat by lia.
      apply temp_after_step; auto.
      pose (linearly_independent_dimensions A H0 H3).
      lia.
Qed.

Lemma temp_trichotomy_subpart1 : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat ->
          (~ temp_after P A m <-> temp_before P A m \/ temp_middle P A m)).
Proof. intros n k P A H0 H1 H2 H3 m H4. 
  split.
  - intros H5.
    unfold temp_after in H5.
    apply Classical_Pred_Type.not_all_ex_not in H5.
    destruct H5 as [M H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5 as [WFM H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5 as [MinP linindep].
    apply not_lindep_implies_linindep in linindep.
    unfold temp_before, temp_middle.
    destruct (Classical_Prop.classic (forall v : Vector n, P v -> span (smash A M) v));
      [right | left]; exists M; auto.
  - intros H5.
    unfold temp_after.
    destruct H5 as [before | middle].
    + unfold temp_before in before.
      destruct before as [M [WFM [MinP [linindep notspanP]]]].
      intro.
      specialize (H5 M WFM MinP).
      apply lindep_implies_not_linindep in H5.
      contradiction.
    + unfold temp_middle in middle.
      destruct middle as [M [WFM [MinP [lindep spanP]]]].
      intro.
      specialize (H5 M WFM MinP).
      apply lindep_implies_not_linindep in H5.
      contradiction.
Qed.

Lemma temp_trichotomy_subpart2 : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (~ temp_before P A m \/ ~ temp_middle P A m)).
Proof. intros n k P A H0 H1 H2 H3 m H4.
  apply Classical_Prop.not_and_or.
  intro.
  destruct H5.
  apply temp_before_step in H5; auto.
  rewrite <- temp_trichotomy_subpart1 in H5; auto.
  apply temp_middle_step in H6; auto.
Qed.

Lemma temp_trichotomy : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    (forall m, (k < m)%nat ->
          (trichotomy (temp_before P A m) (temp_middle P A m) (temp_after P A m))).
Proof. intros n k P A H0 H1 H2 H3 m H4.
  assert (~ temp_after P A m <-> temp_before P A m \/ temp_middle P A m) by
    (apply temp_trichotomy_subpart1; auto; lia).
  unfold trichotomy.
  destruct (Classical_Prop.classic (temp_after P A m)).
  - do 2 right.
    assert (~ temp_before P A m /\ ~ temp_middle P A m).
    { apply Classical_Prop.not_or_and.
      intro.
      rewrite <- H5 in H7; auto. }
    destruct H7.
    repeat split; auto.
  - remember H6 as H6'. clear HeqH6'.
    rewrite H5 in H6.
    assert (~ temp_before P A m \/ ~ temp_middle P A m)
      by (apply temp_trichotomy_subpart2; auto).
    destruct H6; destruct H7; try contradiction;
      try (left; repeat split; assumption);
      try (right; left; repeat split; assumption).
Qed.

Lemma temp_exists_middle : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    (exists m, (k < m <= n)%nat /\ (temp_middle P A m)).
Proof. intros n k P A H0 H1 H2 H3 H4.
  pose (linearly_independent_dimensions A H0 H3).
  destruct (Classical_Prop.classic (forall m : nat, (k < m)%nat -> ~ temp_middle P A m)).
  - assert (temp_before P A (n + 1)%nat)
      by (apply temp_no_middle_all_before; auto; lia).
    assert (temp_after P A (n + 1)%nat)
      by (apply temp_end; auto).
    assert (k < n + 1)%nat by lia.
    destruct (temp_trichotomy H0 H1 H2 H3 (n + 1)%nat H8)
      as [[Hb [nHm nHa]] | [[nHb [Hm nHa]] | [nHb [nHm Ha]]]];
      contradiction.
  - apply Classical_Pred_Type.not_all_ex_not in H5.
    destruct H5 as [m H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5.
    apply Classical_Prop.NNPP in H6.
    bdestruct (m <=? n)%nat.
    +  exists m.
       split; auto.
    + assert (temp_after P A m) by (apply temp_all_after_from_end; auto).
      destruct (temp_trichotomy H0 H1 H2 H3 m H5)
        as [[Hb [nHm nHa]] | [[nHb [Hm nHa]] | [nHb [nHm Ha]]]];
        contradiction.
Qed.

Lemma basis_extension : forall {n k : nat} {P : Vector n -> Prop} {A : Matrix n k},
    WF_Matrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_vec i A)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    (exists d, (k < d <= n)%nat /\
            (exists (B : Matrix n (d - k)), WF_Matrix B /\
                (forall i, (i < (d - k))%nat -> P (get_vec i B)) /\ basis P (smash A B))).
Proof. intros n k P A H0 H1 H2 H3 H4.
  destruct (temp_exists_middle H0 H1 H2 H3 H4)
    as [m [mbound [B [WFB [BinP [linindepAB ABspansP]]]]]].
  exists m; repeat (split; auto);
    exists B; repeat (split; auto).
  replace (k + (m - k))%nat with m by lia.
  intros i0 H5. 
  bdestruct (i0 <? k)%nat.
  - setoid_rewrite get_vec_smash_left; auto.
  - setoid_rewrite get_vec_smash_right; auto.
    apply BinP; lia.
Qed.

Lemma exists_dimension : forall {n : nat} {P : Vector n -> Prop},
    subspace P -> (exists d, dimension P d /\ (d <= n)%nat).
Proof. intros n P H0.
  destruct (Classical_Prop.classic (forall v : Vector n, P v -> v = Zero)).
  - exists 0%nat.
    split; try lia.
    unfold dimension.
    exists Zero.
    split; auto with wf_db.
    unfold basis.
    repeat (split; auto).
    + intros i0 H2.
      inversion H2.
    + intros v H2.
      unfold span.
      specialize (H1 v H2).
      subst.
      exists Zero.
      split; auto with wf_db.
    + unfold linearly_independent.
      intros a H2 H3.
      unfold WF_Matrix in H2.
      prep_matrix_equality.
      rewrite H2; auto; lia.
  - apply Classical_Pred_Type.not_all_ex_not in H1.
    destruct H1 as [v H1].
    apply Classical_Prop.imply_to_and in H1.
    destruct H1.
    assert (WF_Matrix v).
    { unfold subspace in H0.
      destruct H0.
      apply H0; auto. }
    assert (forall i : nat, (i < 1)%nat -> P (get_vec i v)).
    { intros i0 H4.
      replace i0 with 0%nat by lia.
      setoid_rewrite get_vec_vec; auto. }
    assert (linearly_independent v)
      by (apply lin_indep_vec; auto).
    destruct (Classical_Prop.classic (forall w : Vector n, P w -> span v w)).
    + pose (linearly_independent_dimensions v H3 H5).
      exists 1%nat; split; try lia.
      unfold dimension.
      exists v; split; auto with wf_db.
      unfold basis.
      repeat (split; auto).
    + destruct (basis_extension H3 H0 H4 H5 H6)
        as [d [dbound [B [WFB [BinP basisAB]]]]].
      exists (1 + (d - 1))%nat; split; try lia.
      unfold dimension.
      exists (smash v B); split;
        auto with wf_db.
Qed.

(* Theorem 45 Let V be an n-dimensional vector space over a field F, and let u1,u2,...,un be vectors in V .
1. If {u1,u2,...,un} spans V , then {u1,u2,...,un} is linearly independent and hence is a basis for V .
2. If {u1,u2,...,un} is linearly independent, then {u1,u2,...,un} spans V and hence is a basis for V. *)
Lemma equal_dimension_span_lin_indep : forall {n d : nat} {P : Vector n -> Prop} {A : Matrix n d},
    WF_Matrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_vec i A)) ->
    (forall v, P v -> span A v) -> linearly_independent A.
Proof. intros n d P A H0 H1 H2 H3 H4.
  bdestruct (d <=? 0)%nat.
  - unfold linearly_independent.
    intros a H6 H7.
    prep_matrix_equality.
    rewrite H6; auto; try lia.
  - remember H2 as H2'. clear HeqH2'.
    unfold dimension in H2.
    destruct H2 as [B [WFB basisB]].
    unfold basis in basisB.
    destruct basisB as [subspaceP [BinP [BspansP linindepB]]].
    assert (nonzerovec : @e_i d 0%nat <> Zero).
      { intro.
        unfold e_i in H2.
        apply f_equal_inv with (x := 0%nat) in H2.
        apply f_equal_inv with (x := 0%nat) in H2.
        simpl in H2.
        rewrite andb_true_r in H2.
        assert ((0 <? d)%nat = true) by (rewrite Nat.ltb_lt; auto).
        rewrite H6 in H2.
        simpl in H2.
        inversion H2.
        lra. }
      assert (WF_Matrix (@e_i d 0%nat)) by auto with wf_db.
      assert (forall m, (@Zero m d) × (@e_i d 0%nat) = Zero) by (intros; rewrite Mmult_0_l; auto).
    assert (n <> 0%nat).
    { intro.
      subst.
      assert (B = Zero).
      { prep_matrix_equality.
        rewrite WFB; auto.
        left. lia. }
      subst.
      unfold linearly_independent in linindepB.
      contradict nonzerovec.
      apply linindepB; auto. }
    assert (~ forall i : nat, (i < d)%nat -> get_vec i B = Zero).
    { intro.
      assert (B = Zero).
      { prep_matrix_equality.
        bdestruct (x <? n)%nat; [idtac | rewrite WFB; auto].
        bdestruct (y <? d)%nat; [idtac | rewrite WFB; auto].
        assert (B x y = get_vec y B x 0%nat) by (bdestruct_all; auto).
        rewrite H11.
        rewrite H8; auto. }
      subst.
      unfold linearly_independent in linindepB.
      contradict nonzerovec.
      apply linindepB; auto. }
    assert (exists v : Vector n, v <> Zero /\ P v).
    { apply Classical_Pred_Type.not_all_ex_not in H8.
      destruct H8 as [i H8].
      apply Classical_Prop.imply_to_and in H8.
      destruct H8.
      exists (get_vec i B).
      split; auto. }
    destruct (subset_basis H0 H5 H1 H3 H4 H9)
      as [indices_list [incl_list [NoDuplist basisP]]].
    assert (length (List.seq 0 d) <= length indices_list)%nat.
    { assert (dimension P (length indices_list)).
      { unfold dimension.
        exists (matrix_column_choose indices_list A).
        split; auto with wf_db. }
      pose (unique_dimension P H10 H2').
      rewrite seq_length, e; auto. }
    pose (NoDup_Permutation_bis NoDuplist H10 incl_list) as p.
    rewrite (permutation_preserves_basis H0 subspaceP p) in basisP.
    unfold basis in basisP.
    destruct basisP as [subspaceP' [AinP [AspansP linindepA]]].
    rewrite matrix_column_choose_original in *; auto.
    rewrite ! seq_length in *; auto.
Qed.

Lemma equal_dimension_span_basis : forall {n d : nat} {P : Vector n -> Prop} {A : Matrix n d},
    WF_Matrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_vec i A)) ->
    (forall v, P v -> span A v) -> basis P A.
Proof. intros n d P A H0 H1 H2 H3 H4.
  assert (linearly_independent A)
    by (apply @equal_dimension_span_lin_indep with (P := P); auto).
  unfold basis.
  repeat (split; auto).
Qed.

Lemma equal_dimension_lin_indep_span : forall {n d : nat} {P : Vector n -> Prop} {A : Matrix n d},
    WF_Matrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_vec i A)) ->
    linearly_independent A -> (forall v, P v -> span A v).
Proof. intros n d P A H0 H1 H2 H3 H4 v H5.
  bdestruct (d <=? 0)%nat.
  - unfold span.
    exists Zero; split; auto with wf_db.
    rewrite Mmult_0_r.
    destruct H2 as [M [WFM basisM]].
    assert (d = 0)%nat by lia.
    subst.
    assert (M = Zero).
    { prep_matrix_equality.
      rewrite WFM; auto; lia. }
    subst.
    unfold basis in basisM.
    destruct basisM as [subspaceP' [ZeroinP [ZerospansP linindepZero]]].
    specialize (ZerospansP v H5).
    unfold span in ZerospansP.
    destruct ZerospansP as [a [WFa vZero]].
    rewrite Mmult_0_l in vZero.
    assumption.
  - destruct (Classical_Prop.classic (forall w, P w -> span A w)); auto.
    apply Classical_Pred_Type.not_all_ex_not in H7.
    destruct H7 as [w H7].
    apply Classical_Prop.imply_to_and in H7.
    destruct H7.
    remember H1 as H1'. clear HeqH1'.
    destruct H1' as [WFP [PZero [Psum Pscale]]].
    assert (WF_Matrix w) by (apply WFP; auto).
    pose (extend1_lin_indep H1 H0 H9 H4 H3 H8).
    destruct H2 as [B [WFB basisB]].
    assert (WF_Matrix (col_append A w)) by (unfold col_append; auto with wf_db).
    assert (forall i : nat, (i < s d)%nat -> P (get_vec i (col_append A w))).
    { intros i0 H10.
      bdestruct (i0 =? d)%nat.
      - subst.
        rewrite get_vec_col_append_back; auto.
      - rewrite get_vec_col_append_front; auto; try lia.
        apply H3; lia. }
    assert (s d > d)%nat by lia.
    pose (dimension_overflow P B (col_append A w) WFB H2 basisB H10 H11).
    apply lindep_implies_not_linindep in l0; contradiction.
Qed.

Lemma equal_dimension_lin_indep_basis : forall {n d : nat} {P : Vector n -> Prop} {A : Matrix n d},
    WF_Matrix A -> subspace P -> dimension P d ->
    WF_Matrix A -> (forall i, (i < d)%nat -> P (get_vec i A)) ->
    linearly_independent A -> basis P A.
Proof. intros n d P A H0 H1 H2 H3 H4 H5.
  assert (forall v, P v -> span A v)
    by (apply @equal_dimension_lin_indep_span with (P := P); auto).
  unfold basis.
  repeat (split; auto).
Qed.

Definition matrix_to_list_vector {n m : nat} (M : Matrix n m) :=
  map (fun i : nat => get_vec i M) (List.seq 0 m).

Lemma matrix_to_list_vector_to_matrix : forall {n m : nat} {M : Matrix n m},
    WF_Matrix M -> list_vector_to_matrix (matrix_to_list_vector M) = M.
Proof. intros n m M H0.
  unfold list_vector_to_matrix, matrix_to_list_vector.
  prep_matrix_equality.
  assert (@Zero n 1%nat = get_vec m M).
  { prep_matrix_equality.
    unfold get_vec.
    bdestruct_all; auto.
    rewrite H0; auto; lia. }
  rewrite H1.
  rewrite map_nth with (d := m).
  unfold get_vec.
  bdestruct_all.
  bdestruct (y <? m)%nat.
  - rewrite seq_nth; auto.
  - rewrite nth_overflow; try rewrite seq_length; auto.
    rewrite ! H0; auto.
Qed.

Lemma list_vector_to_matrix_to_list_vector : forall {n : nat} {list_vector : list (Vector n)},
    (Forall WF_Matrix list_vector) ->
    matrix_to_list_vector (list_vector_to_matrix list_vector) = list_vector.
Proof. intros n list_vector AllWFM.
  apply (nth_ext (matrix_to_list_vector (list_vector_to_matrix list_vector)) list_vector (@Zero n 1%nat) (@Zero n 1%nat)); unfold matrix_to_list_vector, list_vector_to_matrix;
    rewrite map_length, seq_length; auto.
  intros n0 H0.
  assert (@Zero n 1%nat = @get_col n (length list_vector) (fun r c : nat => nth c list_vector (@Zero n 1%nat) r 0%nat) (length list_vector)).
  { prep_matrix_equality.
    unfold get_vec.
    bdestruct_all; auto.
    rewrite nth_overflow; auto. }
  rewrite H1 at 1.
  rewrite map_nth with (d := length list_vector).
  unfold get_vec.
  prep_matrix_equality.
  bdestruct_all.
  - rewrite seq_nth; auto.
  - rewrite Forall_nth in AllWFM.
    specialize (AllWFM n0 (@Zero n 1%nat) H0).
    rewrite AllWFM; auto; lia.
Qed.



Lemma vector_row_choose_inverse : forall (n : nat) (indices_list : list nat) (v : Vector (length indices_list)),
    NoDup indices_list -> incl indices_list (List.seq 0%nat n) -> WF_Matrix v ->
    exists (w : Vector n), WF_Matrix w /\ v = vector_row_choose indices_list w.
Proof. intros n indices_list v H0 H1 H2. 
  exists (fun r c =>
      if (c =? 0)%nat
      then
        if (ListDec.In_dec Nat.eq_dec r indices_list)
        then v (unwrap (index indices_list r)) 0%nat
        else C0
      else C0).
  split.
  - unfold WF_Matrix.
    intros x y H3.
    bdestruct_all; auto.
    destruct (ListDec.In_dec Nat.eq_dec x indices_list) as [H5 | H5]; auto.
    apply H1 in H5.
    rewrite in_seq in H5.
    lia.
  - unfold vector_row_choose.
    prep_matrix_equality.
    bdestruct (x <? length indices_list).
    + bdestruct_all.
      2 : rewrite H2; auto; lia.
      subst.
      destruct (ListDec.In_dec Nat.eq_dec (nth x indices_list n) indices_list) as [H4 | H4].
      2 : pose (nth_In indices_list n H3); contradiction.
      rewrite (index_nth indices_list x n H0 H3).
      easy.
    + destruct (ListDec.In_dec Nat.eq_dec (nth x indices_list n) indices_list) as [H4 | H4].
      * bdestruct_all.
        -- subst. apply H1 in H4.
           rewrite in_seq, nth_overflow in H4; lia.
        -- rewrite H2; auto; lia.
      * bdestruct_all; auto.
Qed.

Lemma WF_Unitary_implies_linearly_independent : forall {n : nat} {M : Square n},
    WF_Unitary M -> linearly_independent M.
Proof. intros n M H0.
  assert (invertible M) by (apply WF_Unitary_implies_invertible; auto).
  rewrite <- lin_indep_iff_invertible in H1; auto with wf_db.
Qed.

Lemma matrix_column_choose_Zero : forall {n m : nat} {indices_list : list nat},
    matrix_column_choose indices_list (@Zero n m) = @Zero n (length indices_list).
Proof. intros n m indices_list.
  unfold matrix_column_choose, list_vector_to_matrix.
  prep_matrix_equality.
  bdestruct (y <? length indices_list).
  - rewrite nth_indep with (d' := (fun i0 : nat => get_vec i0 (@Zero n m)) 0%nat).
    + rewrite map_nth with (f := (fun i0 : nat => get_vec i0 Zero)).
      unfold get_vec.
      bdestruct_all.
      easy.
    + rewrite map_length; auto.
  - rewrite nth_overflow; auto.
    rewrite map_length; auto.
Qed.

Lemma vector_row_choose_Zero : forall {n : nat} {indices_list : list nat},
    vector_row_choose indices_list (@Zero n 1) = @Zero (length indices_list) 1.
Proof. intros n indices_list.
  unfold vector_row_choose.
  prep_matrix_equality.
  easy.
Qed.

Lemma span_get_vec : forall {n m : nat} (M : Matrix n m) (i : nat),
    WF_Matrix M -> (i < m)%nat -> span M (get_vec i M).
Proof. intros n m M i0 H0 H1.
  unfold span.
  exists (e_i i0).
  split; auto with wf_db; rewrite e_i_get_vec; auto with wf_db.
Qed.

Lemma equivalent_subspace_basis : forall {n m : nat} {P1 P2 : Vector n -> Prop} {M : Matrix n m},
    (forall v : Vector n, P1 v <-> P2 v) -> (basis P1 M <-> basis P2 M).
Proof. intros n m P1 P2 M H0.
  unfold basis; split; intros H1; destruct H1 as [H1 [H2 [H3 H4]]];
    destruct H1 as [H5 [H6 [H7 H8]]];
    repeat (split; intros; auto with wf_db).
  - apply H5; rewrite H0; easy.
  - rewrite <- H0; easy.
  - rewrite <- H0; apply H7; rewrite H0; auto.
  - rewrite <- H0; apply H8; rewrite H0; auto.
  - rewrite <- H0; apply H2; auto.
  - apply H3; rewrite H0; auto.
  - apply H5; rewrite <- H0; easy.
  - rewrite H0; easy.
  - rewrite H0; apply H7; rewrite <- H0; auto.
  - rewrite H0; apply H8; rewrite <- H0; auto.
  - rewrite H0; apply H2; auto.
  - apply H3; rewrite <- H0; auto.
Qed.
    
Lemma span_WF_Matrix : forall {n m : nat} {M : Matrix n m} {v : Vector n},
    WF_Matrix M -> span M v -> WF_Matrix v.
Proof. intros n m M v H0 H1.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  rewrite H2.
  auto with wf_db.
Qed.

Lemma span_in_subspace : forall {n m : nat} {M : Matrix n m} {P : Vector n -> Prop},
    subspace P ->
    (forall i : nat, (i < m)%nat -> P (get_vec i M)) ->
    (forall v : Vector n, span M v -> P v).
Proof. intros n m M P H0 H1 v H2.
  unfold span in H2.
  destruct H2 as [a [H2 H3]].
  rewrite H3.
  apply subspace_closed_under_linear_combinations;
    auto with wf_db.
Qed.

Lemma subspace_is_basis_span : forall {n m : nat} {P : Vector n -> Prop} {M : Matrix n m},
    basis P M -> (forall v : Vector n, P v <-> span M v).
Proof. intros n m P M H0 v.
  destruct H0 as [H0 [H1 [H2 H3]]];
    split; intros.
  - apply H2; easy.
  - apply (span_in_subspace H0 H1); easy.
Qed.

Lemma left_invertible_linearly_independent : forall {n m : nat} {M : Square n} {A : Matrix n m}, 
    WF_Matrix A -> invertible M -> (linearly_independent (M × A) <-> linearly_independent A).
Proof. intros n m M A H0 H1. 
  destruct H1 as [M0 H1].
  destruct H1 as [H1 H2].
  unfold linearly_independent.
  split; intros H3 a WFa eqn.
  - apply H3; auto.
    rewrite Mmult_assoc, eqn, Mmult_0_r; reflexivity.
  - apply H3; auto.
    apply @Mmult_inj_l with (i := n) (m := M0) in eqn.
    rewrite <- ! Mmult_assoc in eqn.
    destruct H2.
    rewrite H4, Mmult_1_l, Mmult_0_r in eqn; auto.
Qed.

Lemma get_vec_mult_matrix : forall {n m o : nat} (i : nat) (A : Matrix n m) (B : Matrix m o),
    A × get_vec i B = get_vec i (A × B).
Proof. intros n m o i0 A B.
  unfold get_vec, Mmult.
  prep_matrix_equality.
  bdestruct_all; auto.
  rewrite big_sum_0_bounded; intros; lca.
Qed.

  
Lemma det_by_get_vec_matrix : forall {n m : nat} (A B : Matrix n m),
    (forall i : nat, get_vec i A = get_vec i B) -> A = B.
Proof. intros n m A B H0.
  prep_matrix_equality.
  unfold get_vec in H0.
  specialize (H0 y).
  apply f_equal_inv with (x := x) in H0.
  apply f_equal_inv with (x := 0%nat) in H0; auto.
Qed.

Lemma unitary_columns_inner_product : forall {n : nat} (i j : nat) (U : Square n),
    WF_Unitary U -> inner_product (get_vec i U) (get_vec j U) = I n i j.
Proof. intros n i0 j U H0.
  rewrite inner_product_is_mult.
  destruct H0 as [WFU unitary_U].
  rewrite unitary_U.
  easy.
Qed.



Lemma unitary_adjoint_on_column_vector : forall {n : nat} (i : nat) (U : Square n),
    WF_Unitary U -> (get_vec i U)† × U = (e_i i)†.
Proof. intros n i0 U H0.
  apply det_by_get_vec_matrix.
  intros i1. 
  rewrite <- get_vec_mult_matrix.
  rewrite single_element_matrix_equality; auto with wf_db.
  replace ((adjoint (get_vec i0 U) × get_vec i1 U) 0%nat 0%nat)
    with (inner_product (get_vec i0 U) (get_vec i1 U))
    by auto.
  rewrite unitary_columns_inner_product; auto.
  unfold I, e_i, adjoint, get_vec, Cconj; simpl.
  bdestruct_all; simpl; lca.
Qed.

Lemma inner_product_vector_with_standard_basis : forall {n : nat} (i : nat) (v : Vector n),
    (i < n)%nat -> inner_product (e_i i) v = v i 0%nat.
Proof. intros n i0 v H0.
  unfold e_i, inner_product, adjoint, Mmult, Cconj.
  simpl.
  apply big_sum_unique.
  exists i0.
  repeat (split; intros; simpl; auto; bdestruct_all; simpl; auto; try lca).
Qed.


Lemma inner_product_vector_with_standard_basis' : forall {n : nat} (i : nat) (v : Vector n),
    WF_Matrix v -> inner_product (e_i i) v = v i 0%nat.
Proof. intros n i0 v H0.
  bdestruct (i0 <? n)%nat.
  - apply (inner_product_vector_with_standard_basis i0 v H1).
  - setoid_rewrite H0 at 1; try lia.
    rewrite e_i_overflow; auto.
    unfold inner_product.
    rewrite zero_adjoint_eq, Mmult_0_l; auto.
Qed.

