Require Import QuantumLib.Eigenvectors.
Require Export QuantumLib.Permutations.
Require Import QuantumLib.VectorStates.
Require Import HeisenbergFoundations.F2Math.
Require Export HeisenbergFoundations.Normalization.


Local Open Scope F2_scope.


(* Check Matrix *)


(** *** Check Matrix *** **)
Definition toCheckMatrixF2ElementLeftX (a : Pauli) : F2 :=
  match a with
  | gI => zero
  | gX => one
  | gY => one
  | gZ => zero
  end.

Definition toCheckMatrixF2ElementRightZ (a : Pauli) : F2 :=
  match a with
  | gI => zero
  | gX => zero
  | gY => one
  | gZ => one
  end.

Definition toCheckMatrixF2Left (row col : nat) (LLp : list (list Pauli)) : MatrixF2 row col := 
  (fun r c : nat => toCheckMatrixF2ElementLeftX (nth c (nth r LLp (repeat gI col)) gI)).
Definition toCheckMatrixF2Right (row col : nat) (LLp : list (list Pauli)) : MatrixF2 row col := 
  (fun r c : nat => toCheckMatrixF2ElementRightZ (nth c (nth r LLp (repeat gI col)) gI)).

Lemma WF_toCheckMatrixF2Left : forall (row col : nat) (LLp : list (list Pauli)),
    (length LLp <= row)%nat -> Forall (fun Lp : list Pauli => (length Lp <= col)%nat) LLp -> 
    WF_MatrixF2 (toCheckMatrixF2Left row col LLp).
Proof. intros row col LLp H H0. 
  unfold WF_MatrixF2, toCheckMatrixF2Left, toCheckMatrixF2ElementLeftX. 
  intros x y H1.
  destruct H1.
  - rewrite nth_overflow with (d := (repeat gI col)); try lia.
    rewrite nth_repeat. auto.
  - bdestruct (x <? length LLp)%nat.
    + rewrite nth_overflow with (d := gI); auto.
      rewrite Forall_nth in H0.
      specialize (H0 x (repeat gI col) H2). lia.
    + rewrite nth_overflow with (d := (repeat gI col)); try lia.
      rewrite nth_repeat. auto.
Qed.

Lemma toCheckMatrixF2Left_nil : forall (r c : nat), 
    toCheckMatrixF2Left r c [] = ZeroF2.
Proof. intros r c.
  unfold toCheckMatrixF2Left, ZeroF2.
  prep_matrix_equality.
  unfold toCheckMatrixF2ElementLeftX.
  simpl; destruct x; rewrite nth_repeat; auto.
Qed.

Lemma WF_toCheckMatrixF2Right : forall (row col : nat) (LLp : list (list Pauli)),
    (length LLp <= row)%nat -> Forall (fun Lp : list Pauli => (length Lp <= col)%nat) LLp -> 
    WF_MatrixF2 (toCheckMatrixF2Right row col LLp).
Proof. intros row col LLp H H0. 
  unfold WF_MatrixF2, toCheckMatrixF2Right, toCheckMatrixF2ElementRightZ. 
  intros x y H1.
  destruct H1.
  - rewrite nth_overflow with (d := (repeat gI col)); try lia.
    rewrite nth_repeat. auto.
  - bdestruct (x <? length LLp)%nat.
    + rewrite nth_overflow with (d := gI); auto.
      rewrite Forall_nth in H0.
      specialize (H0 x (repeat gI col) H2). lia.
    + rewrite nth_overflow with (d := (repeat gI col)); try lia.
      rewrite nth_repeat. auto.
Qed.

Lemma toCheckMatrixF2Right_nil : forall (r c : nat), 
    toCheckMatrixF2Right r c [] = ZeroF2.
Proof. intros r c.
  unfold toCheckMatrixF2Right, ZeroF2.
  prep_matrix_equality.
  unfold toCheckMatrixF2ElementRightZ.
  simpl; destruct x; rewrite nth_repeat; auto.
Qed.

Definition fromLLpToCheckMatrixF2 (row col : nat) (LLp : list (list Pauli)) : MatrixF2 row (col + col)%nat := 
  F2Module.smash (toCheckMatrixF2Left row col LLp) (toCheckMatrixF2Right row col LLp).

Lemma WF_fromLLpToCheckMatrixF2 : forall (row col : nat) (LLp : list (list Pauli)),
    (length LLp <= row)%nat -> Forall (fun Lp : list Pauli => (length Lp <= col)%nat) LLp -> 
    WF_MatrixF2 (fromLLpToCheckMatrixF2 row col LLp).
Proof. intros row col LLp H H0.
  apply F2Module.WF_smash.
  apply WF_toCheckMatrixF2Left; auto.
  apply WF_toCheckMatrixF2Right; auto.
Qed.

Lemma fromLLpToCheckMatrixF2_nil : forall (r c : nat), 
    fromLLpToCheckMatrixF2 r c [] = ZeroF2.
Proof. intros r c.
  unfold fromLLpToCheckMatrixF2.
  rewrite toCheckMatrixF2Left_nil, toCheckMatrixF2Right_nil.
  unfold F2Module.smash, ZeroF2.
  prep_matrix_equality.
  bdestruct_all; auto.
Qed.
  

Definition elemToVecF2 (z : F2) : VectorF2 1%nat :=
  (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then z else zero).

Lemma elemToVecF2_zero : elemToVecF2 0 = ZeroF2.
Proof. unfold elemToVecF2, ZeroF2. prep_matrix_equality. bdestruct_all; auto. Qed.

Lemma elemToVecF2_one00 : elemToVecF2 1%F2 0%nat 0%nat = 1.
Proof. unfold elemToVecF2, ZeroF2. bdestruct_all; auto. Qed.

Lemma elemToVec_innerproduct : forall (z1 z2 : F2),
    elemToVecF2 z1 × transposeF2 (elemToVecF2 z2) = elemToVecF2 (z1 · z2).
Proof. intros z1 z2.
  unfold elemToVecF2, transposeF2, MmultF2.
  prep_matrix_equality.
  bdestruct_all; simpl; auto.
  - destruct (z1 · z2); auto.
  - destruct z1; auto.
  - destruct z2; auto.
Qed.

Lemma toCheckMatrixF2Left_cons : forall (Lp : list Pauli) (p : Pauli),
    toCheckMatrixF2Left 1%nat (S (length Lp)) [p :: Lp] =
      F2Module.smash (elemToVecF2 (toCheckMatrixF2ElementLeftX p)) (toCheckMatrixF2Left 1%nat (length Lp) [Lp]).
Proof. intros Lp p.
  unfold toCheckMatrixF2Left, F2Module.smash, elemToVecF2.
  prep_matrix_equality.
  bdestruct_all; subst; simpl; auto.
  - destruct x; simpl; try lia.
    destruct x; simpl; auto.
  - destruct x; subst; simpl.
    + destruct y; subst; simpl; try lia.
      repeat f_equal; try lia.
    + destruct x; subst; simpl.
      * destruct y; subst; simpl; try lia.
        repeat f_equal; try lia.
      * destruct y; subst; simpl; try lia.
        repeat f_equal; try lia.
Qed.

Lemma toCheckMatrixF2Right_cons : forall (Lp : list Pauli) (p : Pauli),
    toCheckMatrixF2Right 1%nat (S (length Lp)) [p :: Lp] =
      F2Module.smash (elemToVecF2 (toCheckMatrixF2ElementRightZ p)) (toCheckMatrixF2Right 1%nat (length Lp) [Lp]).
Proof. intros Lp p.
  unfold toCheckMatrixF2Right, F2Module.smash, elemToVecF2.
  prep_matrix_equality.
  bdestruct_all; subst; simpl; auto.
  - destruct x; simpl; try lia.
    destruct x; simpl; auto.
  - destruct x; subst; simpl.
    + destruct y; subst; simpl; try lia.
      repeat f_equal; try lia.
    + destruct x; subst; simpl.
      * destruct y; subst; simpl; try lia.
        repeat f_equal; try lia.
      * destruct y; subst; simpl; try lia.
        repeat f_equal; try lia.
Qed.

(** Λ **)
Definition checkLambdaF2 (n : nat) : MatrixF2 (n + n)%nat (n + n)%nat :=
  (fun r c : nat =>
     if (r <? (n + n))%nat && (c <? (n + n))%nat && ((c =? r + n)%nat || (r =? c + n)%nat) 
     then 1 else 0).

Lemma WF_checkLambdaF2 : forall {n : nat},
    WF_MatrixF2 (checkLambdaF2 n).
Proof. intros n.
  unfold WF_MatrixF2.
  intros x y H.
  destruct H; unfold checkLambdaF2; bdestruct_all; simpl; auto.
Qed.

Lemma checkLambdaF2_inv : forall (n : nat),
    (checkLambdaF2 n) × (checkLambdaF2 n) = IF2 (n + n)%nat.
Proof. intros n. 
  unfold checkLambdaF2, IF2, MmultF2.
  prep_matrix_equality.
  bdestruct_all; subst; simpl.
  - bdestruct (y <? n).
    + apply big_sum_unique.
      exists (y + n)%nat. split; try lia. split.
      * bdestruct_all. auto.
      * intros x' H2 H3. bdestruct_all. auto.
    + apply big_sum_unique.
      exists (y - n)%nat. split; try lia. split.
      * bdestruct_all. auto.
      * intros x' H2 H3. bdestruct_all. auto.
  - rewrite big_sum_0_bounded; auto.
    intros x0 H2. bdestruct_all; auto.
  - rewrite big_sum_0_bounded; auto.
    intros x0 H2. bdestruct_all; auto.
  - rewrite big_sum_0_bounded; auto.
    intros x0 H2. bdestruct_all; auto.
  - rewrite big_sum_0_bounded; auto.
    intros x0 H2. bdestruct_all; auto.
  - rewrite big_sum_0_bounded; auto.
    intros x0 H2. bdestruct_all; auto.
Qed.

Lemma checkLambdaF2_switch_right : forall (n : nat) (a b : MatrixF2 1%nat n),
    WF_MatrixF2 a ->
    (checkLambdaF2 n) × (F2Module.smash a b)⊤ = (F2Module.smash b a)⊤.
Proof. intros n a b H.
  unfold checkLambdaF2, F2Module.smash, transposeF2, MmultF2.
  prep_matrix_equality.
  bdestruct_all; subst; simpl.
  - apply big_sum_unique.
    exists (x + n)%nat. split; try lia. split.
    + bdestruct_all. F2simpl. f_equal. lia.
    + intros x' H2 H3. bdestruct_all; rewrite F2mult_0_l; simpl; auto.
  - apply big_sum_unique.
    exists (x - n)%nat. split; try lia. split.
    + bdestruct_all. rewrite F2mult_1_l. auto.
    + intros x' H2 H3. bdestruct_all; rewrite F2mult_0_l; auto.
  - rewrite H; auto; try lia.
    rewrite big_sum_0_bounded; auto.
    intros x0 H2. destruct (if x0 <? n then a y x0 else b y (x0 - n)%nat); auto.
Qed.

Lemma smash_innerproduct : forall (n m : nat) (a a' : MatrixF2 1%nat n) (b b' : MatrixF2 1%nat m),
    F2Module.smash a b × (F2Module.smash a' b')⊤ = a × a'⊤ .+ b × b'⊤.
Proof. intros n m a a' b b'.
  unfold F2Module.smash, transposeF2, MmultF2, MplusF2.
  prep_matrix_equality.
  rewrite big_sum_sum.
  simpl.
  f_equal.
  - apply big_sum_eq_bounded.
    intros x0 H.
    bdestruct_all.
    auto.
  - apply big_sum_eq_bounded.
    intros x0 H.
    bdestruct_all.
    replace (n + x0 - n)%nat with x0 by lia.
    auto.
Qed.

(* Exercise 10.33: Show that g and g′ commute if and only if r(g)Λr(g′)T = 0. (In the check matrix representation, arithmetic is done modulo two.) *)
Lemma fromLLpToCheckMatrixF2_checkLambdaF2_comm_anticomm : forall (Lp1 Lp2 : list Pauli),
    length Lp1 = length Lp2 -> (length Lp1 > 0)%nat ->
    (((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp1]) × (checkLambdaF2 (length Lp1)) × ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp2]) ⊤)) 0%nat 0%nat = 0 -> commute_listP Lp1 Lp2) /\
      (((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp1]) × (checkLambdaF2 (length Lp1)) × ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp2]) ⊤)) 0%nat 0%nat = 1 -> anticommute_listP Lp1 Lp2).
Proof. intros Lp1 Lp2 H H0. gen Lp2. induction Lp1; intros. simpl in *; try lia.
  destruct Lp2 as [| b Lp2]. inversion H.
  simpl in H. apply Nat.succ_inj in H. clear H0.
  unfold fromLLpToCheckMatrixF2.
  rewrite ! F2Module.GMmult_assoc.
  rewrite ! checkLambdaF2_switch_right.
  2:{ apply WF_toCheckMatrixF2Left; auto. constructor. simpl; lia. constructor. }
  rewrite ! smash_innerproduct.
  replace (length (a :: Lp1)) with (S (length Lp1)) by auto.
  rewrite ! toCheckMatrixF2Left_cons, ! toCheckMatrixF2Right_cons.
  rewrite ! H.
  rewrite ! toCheckMatrixF2Left_cons, ! toCheckMatrixF2Right_cons.
  replace (S (length Lp2)) with (1 + (length Lp2))%nat by lia.
  rewrite ! smash_innerproduct.
  rewrite ! elemToVec_innerproduct.
  rewrite <- ! H.
  destruct Lp1.
  clear IHLp1. simpl in *. symmetry in H. rewrite length_zero_iff_nil in H. subst.
  unfold toCheckMatrixF2Left, toCheckMatrixF2Right,
    toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ,
    transposeF2, MmultF2, MplusF2; 
    destruct a, b; simpl; split; intros H'; constructor; try constructor; auto;
    repeat match goal with
    | Hyp: 0 = 1 |- _ => symmetry in Hyp
    | Hyp: 1 = 0 |- _ => contradict Hyp; apply F2_1_neq_0
    end;
    match goal with
    | Hyp: _ |- _ <> _ => intro H''; try discriminate
    end.
  destruct Lp2 as [| q Lp2]. inversion H.
  assert (length (p :: Lp1) > 0)%nat by (simpl; lia).
  specialize (IHLp1 H0 (q :: Lp2) H). clear H0.
  unfold fromLLpToCheckMatrixF2 in IHLp1.
  rewrite ! F2Module.GMmult_assoc in IHLp1.
  rewrite ! checkLambdaF2_switch_right in IHLp1.
  2:{ apply WF_toCheckMatrixF2Left; auto. constructor. simpl in *; try lia. constructor. }
  rewrite ! smash_innerproduct in IHLp1.
  destruct IHLp1.
  split; intro H2.
  destruct a, b;
    try match goal with
      | Hyp : _ |- commute_listP (gI :: _) (_) => 
          apply commuting_listP_commP_commL; [constructor; auto | apply H0];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- commute_listP (_) (gI :: _) => 
          apply commuting_listP_commP_commL; [constructor; auto | apply H0];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- commute_listP (gX :: _) (gX :: _) => 
          apply commuting_listP_commP_commL; [constructor; auto | apply H0];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- commute_listP (gY :: _) (gY :: _) => 
          apply commuting_listP_commP_commL; [constructor; auto | apply H0];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- commute_listP (gZ :: _) (gZ :: _) => 
          apply commuting_listP_commP_commL; [constructor; auto | apply H0];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      end.

  4: { try rewrite ! F2mult_1_l in H2; try rewrite ! F2mult_1_r in H2.
       unfold MplusF2 in H2.
       rewrite ! elemToVecF2_one00 in H2.
       rewrite <- H2.
       unfold MplusF2. rewrite ! F2plus_assoc.
       setoid_rewrite F2plus_comm at 5. rewrite ! F2plus_assoc.
       F2simpl. auto. }  

  1-6: apply commuting_listP_anticommP_anticommL; 
  [constructor; intro H''; discriminate | apply H1];
  unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
  try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2;
  try rewrite ! F2mult_1_l in H2; try rewrite ! F2mult_1_r in H2;
  try rewrite ! elemToVecF2_zero in H2;
  try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2;
  unfold MplusF2 in H2; unfold MplusF2;
  rewrite ! elemToVecF2_one00 in H2;
  try rewrite <- ! F2plus_assoc in H2;
  try apply F2plus_flip_l_0 in H2;
  try rewrite <- H2; auto.
 
  1-3: try rewrite F2plus_comm in H2 at 1;
  try rewrite <- ! F2plus_assoc in H2;
  try apply F2plus_flip_l_0 in H2;
  try rewrite <- H2; auto; try rewrite F2plus_comm at 1; auto.

  destruct a, b;
    try match goal with
      | Hyp : _ |- anticommute_listP (gI :: _) (_) => 
          apply anticommuting_listP_commP_anticommL; [constructor; auto | apply H1];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- anticommute_listP (_) (gI :: _) => 
          apply anticommuting_listP_commP_anticommL; [constructor; auto | apply H1];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- anticommute_listP (gX :: _) (gX :: _) => 
          apply anticommuting_listP_commP_anticommL; [constructor; auto | apply H1];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- anticommute_listP (gY :: _) (gY :: _) => 
          apply anticommuting_listP_commP_anticommL; [constructor; auto | apply H1];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      | Hyp : _ |- anticommute_listP (gZ :: _) (gZ :: _) => 
          apply anticommuting_listP_commP_anticommL; [constructor; auto | apply H1];
          unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
          try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2; 
          try rewrite ! elemToVecF2_zero in H2;
          try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2; 
          auto
      end.
 
  4: { try rewrite ! F2mult_1_l in H2; try rewrite ! F2mult_1_r in H2.
       unfold MplusF2 in H2.
       rewrite ! elemToVecF2_one00 in H2.
       rewrite <- H2.
       unfold MplusF2. rewrite ! F2plus_assoc.
       setoid_rewrite F2plus_comm at 5. rewrite ! F2plus_assoc.
       F2simpl. auto. }  
  
  1-6: apply anticommuting_listP_anticommP_commL; 
  [constructor; intro H''; discriminate | apply H0];
  unfold toCheckMatrixF2ElementLeftX, toCheckMatrixF2ElementRightZ in H2;
  try rewrite ! F2mult_0_l in H2; try rewrite ! F2mult_0_r in H2;
  try rewrite ! F2mult_1_l in H2; try rewrite ! F2mult_1_r in H2;
  try rewrite ! elemToVecF2_zero in H2;
  try rewrite ! F2Module.GMplus_0_l in H2; try rewrite ! F2Module.GMplus_0_r in H2;
  unfold MplusF2 in H2; unfold MplusF2;
  rewrite ! elemToVecF2_one00 in H2;
  try rewrite <- ! F2plus_assoc in H2;
  try apply F2plus_flip_l_1 in H2;
  try rewrite <- H2; auto.
  
  1-3: try rewrite F2plus_comm in H2 at 1;
  try rewrite <- ! F2plus_assoc in H2;
  try apply F2plus_flip_l_1 in H2;
  try rewrite <- H2; auto; try rewrite F2plus_comm at 1; auto.
Qed.

Lemma fromLLpToCheckMatrixF2_checkLambdaF2_comm_iff : forall (Lp1 Lp2 : list Pauli),
    length Lp1 = length Lp2 -> (length Lp1 > 0)%nat ->
    ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp1]) × (checkLambdaF2 (length Lp1)) × ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp2]) ⊤)) 0%nat 0%nat = 0 <-> commute_listP Lp1 Lp2.
Proof. intros Lp1 Lp2 H H0.
  destruct (fromLLpToCheckMatrixF2_checkLambdaF2_comm_anticomm Lp1 Lp2 H H0).
  split; auto.
  intros H3.
  rewrite <- F2_neq1_iff_eq0.
  intro H4.
  destruct (anticommute_commute_listP_no_middle Lp1 Lp2); try contradiction.
  contradict H5.
  apply H2; auto.
Qed.

Lemma fromLLpToCheckMatrixF2_checkLambdaF2_anticomm_iff : forall (Lp1 Lp2 : list Pauli),
    length Lp1 = length Lp2 -> (length Lp1 > 0)%nat ->
    ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp1]) × (checkLambdaF2 (length Lp1)) × ((fromLLpToCheckMatrixF2 1%nat (length Lp1) [Lp2]) ⊤)) 0%nat 0%nat = 1 <-> anticommute_listP Lp1 Lp2.
Proof. intros Lp1 Lp2 H H0.
  destruct (fromLLpToCheckMatrixF2_checkLambdaF2_comm_anticomm Lp1 Lp2 H H0).
  split; auto.
  intros H3.
  rewrite <- F2_neq0_iff_eq1.
  intro H4.
  destruct (anticommute_commute_listP_no_middle Lp1 Lp2); try contradiction.
  contradict H5.
  apply H1; auto.
Qed.

Lemma rowF2_fromLLpToCheckMatrixF2 : forall {n i : nat} {LLp : list (list Pauli)},
  Forall (fun Lp : list Pauli => length Lp = n) LLp -> LLp <> [] -> (n > 0)%nat ->
  get_rowF2 (fromLLpToCheckMatrixF2 (length LLp) n LLp) i = 
    fromLLpToCheckMatrixF2 1 n [nth i LLp (repeat gI n)].
Proof. intros n i LLp H H0 H1.
  unfold get_rowF2, fromLLpToCheckMatrixF2.
  unfold F2Module.smash.
  prep_matrix_equality.
  bdestruct_all; subst;
    unfold toCheckMatrixF2Left, toCheckMatrixF2ElementLeftX,
    toCheckMatrixF2Right, toCheckMatrixF2ElementRightZ; auto;
    rewrite nth_overflow with (n := x); try rewrite nth_repeat;
    simpl; try lia; auto.
Qed.

Lemma get_rowF2_e_iF2_hit : forall {i m : nat},
    (i < m)%nat -> (get_rowF2 (@e_iF2 m i) i) 0%nat 0%nat = 1%F2.
Proof. intros i m H.
  unfold get_rowF2, e_iF2; bdestruct_all; simpl; auto.
Qed.

Lemma get_rowF2_e_iF2_miss : forall {i j m : nat},
    (i < m)%nat -> (j < m)%nat -> (i <> j)%nat -> (get_rowF2 (@e_iF2 m i) j) 0%nat 0%nat = 0%F2.
Proof. intros i j m H H0 H1. 
  unfold get_rowF2, e_iF2; bdestruct_all; simpl; auto.
Qed.

Lemma existsCheckMatrixF2Vector : forall (n : nat) (LLp : list (list Pauli)),
    Forall (fun Lp : list Pauli => length Lp = n) LLp -> LLp <> [] -> (n > 0)%nat ->
    linearly_independentF2 ((fromLLpToCheckMatrixF2 (length LLp) n LLp) ⊤) ->
    (forall i : nat, (i < length LLp)%nat -> (exists v : VectorF2 (n + n), WF_MatrixF2 v /\ 
        (fromLLpToCheckMatrixF2 (length LLp) n LLp) × checkLambdaF2 n × v = e_iF2 i /\
             (fromLLpToCheckMatrixF2 1%nat n [nth i LLp (repeat gI n)] × checkLambdaF2 n × v) 0%nat 0%nat = 1%F2 /\
        (forall j : nat, (j < length LLp)%nat -> j <> i -> 
             (fromLLpToCheckMatrixF2 1%nat n [nth j LLp (repeat gI n)] × checkLambdaF2 n × v) 0%nat 0%nat = 0%F2))). 
Proof. intros n LLp H H0 H1 H2 i H3.
  assert (WF_MatrixF2 (fromLLpToCheckMatrixF2 (length LLp) n LLp)).
  { apply WF_fromLLpToCheckMatrixF2; auto.
    apply Forall_impl with (P := (fun Lp : list Pauli => length Lp = n)); intros; auto; lia. }
  assert (WF_MatrixF2 (@e_iF2 (length LLp) i)).
  { apply F2Module.WF_e_i. }
  destruct (F2Module.lin_indep_rows_implies_exists_sol
          (fromLLpToCheckMatrixF2 (length LLp) n LLp) (e_iF2 i) H4 H5 H2)
    as [v [WFv Avb]].
  assert ((IF2 (n + n)%nat) × v = v).
  { rewrite F2Module.GMmult_1_l; auto. }
  rewrite <- checkLambdaF2_inv in H6.
  rewrite F2Module.GMmult_assoc in H6.
  exists (checkLambdaF2 n × v).
  repeat split.
  - apply F2Module.WF_mult; auto. apply WF_checkLambdaF2.
  - rewrite F2Module.GMmult_assoc.
    rewrite H6. auto.
  - rewrite ! F2Module.GMmult_assoc. rewrite H6.
    assert (F2Module.get_row (fromLLpToCheckMatrixF2 (length LLp) n LLp × v) i =
              F2Module.get_row (@e_iF2 (length LLp) i) i).
    { rewrite Avb. auto. }
    rewrite F2Module.matrix_by_basis_transpose in H7; try lia.
    rewrite <- F2Module.GMmult_assoc in H7.
    rewrite <- F2Module.matrix_by_basis_transpose in H7; try lia.
    rewrite rowF2_fromLLpToCheckMatrixF2 in H7; auto.
    rewrite H7. rewrite get_rowF2_e_iF2_hit ; auto.
  - intros j H7 H8. 
    rewrite ! F2Module.GMmult_assoc. rewrite H6.
    assert (F2Module.get_row (fromLLpToCheckMatrixF2 (length LLp) n LLp × v) j =
              F2Module.get_row (@e_iF2 (length LLp) i) j).
    { rewrite Avb. auto. }
    rewrite F2Module.matrix_by_basis_transpose in H9; try lia.
    rewrite <- F2Module.GMmult_assoc in H9.
    rewrite <- F2Module.matrix_by_basis_transpose in H9; try lia.
    rewrite rowF2_fromLLpToCheckMatrixF2 in H9; auto.
    rewrite H9. rewrite get_rowF2_e_iF2_miss; auto.
Qed.

Definition fromF2PairToPauli (x z : F2) : Pauli :=
  match x, z with
  | 0, 0 => gI
  | 1, 0 => gX
  | 0, 1 => gZ
  | 1, 1 => gY
  end.

Fixpoint fromCheckMatrixF2RowToLp_rec 
  {m n : nat} (M : MatrixF2 m (n + n)) (row col_count : nat) (acc : list Pauli) : list Pauli :=
  match col_count with
  | 0%nat => acc
  | S col_count' => fromCheckMatrixF2RowToLp_rec M row col_count'
                     ((fromF2PairToPauli (M row col_count') (M row (n + col_count')%nat)) :: acc)
  end.

Definition fromCheckMatrixF2RowToLp {m n : nat} (M : MatrixF2 m (n + n)) (row : nat) : list Pauli :=
  fromCheckMatrixF2RowToLp_rec M row n [].

Fixpoint fromCheckMatrixF2ToLLp_rec 
  {m n : nat} (M : MatrixF2 m (n + n)) (row_count : nat) (acc : list (list Pauli)) : list (list Pauli) :=
  match row_count with
  | 0%nat => acc
  | S row_count' => fromCheckMatrixF2ToLLp_rec M row_count'
                     ((fromCheckMatrixF2RowToLp M row_count') :: acc)
  end.

Definition fromCheckMatrixF2ToLLp {m n : nat} (M : MatrixF2 m (n + n)) : list (list Pauli) :=
  fromCheckMatrixF2ToLLp_rec M m [].


Lemma fromCheckMatrixF2RowToLp_rec_acc_app : 
  forall {m n : nat} (M : MatrixF2 m (n + n)) (row col_count : nat) (acc : list Pauli),
    fromCheckMatrixF2RowToLp_rec M row col_count acc =
      (fromCheckMatrixF2RowToLp_rec M row col_count []) ++ acc.
Proof. intros m n M row col_count acc.
  gen acc. induction col_count; intros; auto.
  simpl. setoid_rewrite IHcol_count. 
  rewrite <- app_assoc. auto.
Qed.

Lemma fromCheckMatrixF2ToLLp_rec_acc_app : 
  forall {m n : nat} (M : MatrixF2 m (n + n)) (row_count : nat) (acc : list (list Pauli)),
    fromCheckMatrixF2ToLLp_rec M row_count acc =
      (fromCheckMatrixF2ToLLp_rec M row_count []) ++ acc.
Proof. intros m n M row_count acc.
  gen acc. induction row_count; intros; auto.
  simpl. setoid_rewrite IHrow_count.
  rewrite <- app_assoc. auto.
Qed.

Lemma fromCheckMatrixF2RowToLp_rec_reduce_row : 
  forall {m n : nat} (M : MatrixF2 (S m) (n + n)) (row row' col_count : nat) (acc : list Pauli),
    (row' < row)%nat ->
    fromCheckMatrixF2RowToLp_rec M row' col_count acc =
      fromCheckMatrixF2RowToLp_rec (reduce_rowF2 M row) row' col_count acc.
Proof. intros m n M row row' col_count acc H. 
  gen acc. induction col_count; intros; auto.
  simpl. setoid_rewrite IHcol_count; auto. f_equal.
  unfold reduce_rowF2. bdestruct_all; auto.
Qed.

Lemma fromCheckMatrixF2ToLLp_rec_reduce_row : 
  forall {m n : nat} (M : MatrixF2 (S m) (n + n)) (row row_count : nat) (acc : list (list Pauli)),
    (row_count <= row)%nat ->
    fromCheckMatrixF2ToLLp_rec M row_count acc =
      fromCheckMatrixF2ToLLp_rec (reduce_rowF2 M row) row_count acc.
Proof. intros m n M row row_count acc H.
  gen n m M row acc. induction row_count; intros; auto.
  simpl. rewrite IHrow_count with (row := row); try lia.
  do 2 f_equal. unfold fromCheckMatrixF2RowToLp.
  rewrite fromCheckMatrixF2RowToLp_rec_reduce_row with (row := row); auto; try lia.
Qed.

Lemma fromCheckMatrixF2ToLLp_rec_length_row :
  forall {m n : nat} (M : MatrixF2 m (n + n)) (row_count : nat) (acc : list (list Pauli)),
    length (fromCheckMatrixF2ToLLp_rec M row_count acc) = (row_count + length acc)%nat.
Proof. intros m n M row_count acc.
  gen acc. induction row_count; intros; auto.
  simpl. rewrite IHrow_count. auto.
Qed.

Lemma fromCheckMatrixF2RowToLp_rec_length :
  forall {m n : nat} (M : MatrixF2 m (n + n)) (row col_count : nat) (acc : list Pauli),
    length (fromCheckMatrixF2RowToLp_rec M row col_count acc) =
      (col_count + length acc)%nat.
Proof. intros m n M row col_count acc. 
  gen acc. induction col_count; intros; auto.
  simpl. rewrite IHcol_count. auto.
Qed.

Lemma fromCheckMatrixF2ToLLp_rec_length_col :
  forall {m n : nat} (M : MatrixF2 m (n + n)) (row_count : nat) (acc : list (list Pauli)),
    Forall (fun Lp : list Pauli => length Lp = n) acc ->
    Forall (fun Lp : list Pauli => length Lp = n) (fromCheckMatrixF2ToLLp_rec M row_count acc).
Proof. intros m n M row_count acc H.
  gen acc. induction row_count; intros; auto.
  simpl. apply IHrow_count; auto.
  rewrite Forall_forall. intros x H0.
  destruct H0.
  - subst. unfold fromCheckMatrixF2RowToLp.
    rewrite fromCheckMatrixF2RowToLp_rec_length. auto.
  - rewrite Forall_forall in H.
    apply H; auto.
Qed.

Lemma toCheckMatrixF2ElementLeftX_nth_fromCheckMatrixF2RowToLp_rec :
  forall {m n : nat} (M : MatrixF2 m (n + n)) (r y col_count : nat), 
    WF_MatrixF2 M -> (y < col_count)%nat ->
    toCheckMatrixF2ElementLeftX (nth y (fromCheckMatrixF2RowToLp_rec M r col_count []) gI) = M r y.
Proof. intros m n M r y col_count H H0.
  gen m n M r y. 
  induction col_count; intros; try lia. simpl. 
  rewrite fromCheckMatrixF2RowToLp_rec_acc_app.
  bdestruct (y =? col_count)%nat.
  - subst. 
    assert (length (fromCheckMatrixF2RowToLp_rec M r col_count []) = col_count).
    { rewrite fromCheckMatrixF2RowToLp_rec_length. simpl. auto. }
    rewrite <- H1 at 1.
    rewrite nth_middle.
    unfold toCheckMatrixF2ElementLeftX, fromF2PairToPauli.
    destruct (M r col_count); destruct (M r (n + col_count)%nat); auto.
  - rewrite <- nth_firstn with (i := y) (n := col_count); try lia.
    rewrite firstn_app.
    rewrite fromCheckMatrixF2RowToLp_rec_length.
    simpl. replace (col_count - (col_count + 0))%nat with 0%nat by lia. simpl.
    rewrite app_nil_r.
    rewrite firstn_all2 at 1.
    + apply IHcol_count; auto; lia.
    + rewrite fromCheckMatrixF2RowToLp_rec_length; simpl; lia.
Qed.

Lemma toCheckMatrixF2ElementRightZ_nth_fromCheckMatrixF2RowToLp_rec :
  forall {m n : nat} (M : MatrixF2 m (n + n)) (r y col_count : nat), 
    WF_MatrixF2 M -> (y < col_count)%nat ->
    toCheckMatrixF2ElementRightZ (nth y (fromCheckMatrixF2RowToLp_rec M r col_count []) gI) = M r (n + y)%nat.
Proof. intros m n M r y col_count H H0.
  gen m n M r y. 
  induction col_count; intros; try lia. simpl. 
  rewrite fromCheckMatrixF2RowToLp_rec_acc_app.
  bdestruct (y =? col_count)%nat.
  - subst. 
    assert (length (fromCheckMatrixF2RowToLp_rec M r col_count []) = col_count).
    { rewrite fromCheckMatrixF2RowToLp_rec_length. simpl. auto. }
    rewrite <- H1 at 1.
    rewrite nth_middle.
    unfold toCheckMatrixF2ElementRightZ, fromF2PairToPauli.
    destruct (M r col_count); destruct (M r (n + col_count)%nat); auto.
  - rewrite <- nth_firstn with (i := y) (n := col_count); try lia.
    rewrite firstn_app.
    rewrite fromCheckMatrixF2RowToLp_rec_length.
    simpl. replace (col_count - (col_count + 0))%nat with 0%nat by lia. simpl.
    rewrite app_nil_r.
    rewrite firstn_all2 at 1.
    + apply IHcol_count; auto; lia.
    + rewrite fromCheckMatrixF2RowToLp_rec_length; simpl; lia.
Qed.

Lemma fromCheckMatrixF2ToLLpToCheckMatrixF2 : 
  forall {m n : nat} (M : MatrixF2 m (n + n)),
    WF_MatrixF2 M -> 
    fromLLpToCheckMatrixF2 m n (fromCheckMatrixF2ToLLp M) = M.
Proof. intros m n M H.
  unfold fromLLpToCheckMatrixF2.
  unfold F2Module.smash, toCheckMatrixF2Left, toCheckMatrixF2Right.
  prep_matrix_equality.
  bdestruct_all.
  - unfold fromCheckMatrixF2ToLLp. 
    gen n M x y. induction m; intros.
    + simpl. destruct x; rewrite nth_repeat; rewrite H; auto; try lia.
    + simpl. rewrite fromCheckMatrixF2ToLLp_rec_acc_app.
      bdestruct (x <? m)%nat.
      * rewrite fromCheckMatrixF2ToLLp_rec_reduce_row with (row := m); auto.
        rewrite <- nth_firstn with (i := x) (n := m); auto.
        rewrite firstn_app.
        rewrite fromCheckMatrixF2ToLLp_rec_length_row.
        rewrite firstn_all2 at 1.
        -- simpl. replace (m - (m + 0))%nat with 0%nat by lia. simpl.
           rewrite app_nil_r.
           assert (M x y = (reduce_rowF2 M m) x y).
           { unfold reduce_rowF2. bdestruct_all. auto. }
           rewrite H2.
           apply IHm; auto.
           apply F2Module.WF_reduce_row; auto.
        -- rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. lia.
      * bdestruct (x =? m)%nat.
        -- subst. 
           assert (length (fromCheckMatrixF2ToLLp_rec M m []) = m).
           { rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. auto. }
           rewrite <- H2 at 1.
           rewrite nth_middle.
           clear IHm H1 H2.
           unfold fromCheckMatrixF2RowToLp.
           rewrite toCheckMatrixF2ElementLeftX_nth_fromCheckMatrixF2RowToLp_rec;
             auto.
        -- rewrite nth_overflow with (n := x).
           ++ rewrite nth_repeat. unfold toCheckMatrixF2ElementLeftX. rewrite H; auto; lia.
           ++ rewrite app_length. rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. lia.
  - unfold fromCheckMatrixF2ToLLp. 
    gen n M x y. induction m; intros.
    + simpl. destruct x; rewrite nth_repeat; rewrite H; auto; try lia.
    + simpl. rewrite fromCheckMatrixF2ToLLp_rec_acc_app.
      bdestruct (x <? m)%nat.
      * rewrite fromCheckMatrixF2ToLLp_rec_reduce_row with (row := m); auto.
        rewrite <- nth_firstn with (i := x) (n := m); auto.
        rewrite firstn_app.
        rewrite fromCheckMatrixF2ToLLp_rec_length_row.
        rewrite firstn_all2 at 1.
        -- simpl. replace (m - (m + 0))%nat with 0%nat by lia. simpl.
           rewrite app_nil_r.
           assert (M x y = (reduce_rowF2 M m) x y).
           { unfold reduce_rowF2. bdestruct_all. auto. }
           rewrite H2.
           apply IHm; auto.
           apply F2Module.WF_reduce_row; auto.
        -- rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. lia.
      * bdestruct (x =? m)%nat.
        -- subst. 
           assert (length (fromCheckMatrixF2ToLLp_rec M m []) = m).
           { rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. auto. }
           rewrite <- H2 at 1.
           rewrite nth_middle.
           clear IHm H1 H2.
           unfold fromCheckMatrixF2RowToLp.
           bdestruct (y <? n + n)%nat.
           ++ rewrite toCheckMatrixF2ElementRightZ_nth_fromCheckMatrixF2RowToLp_rec;
                auto; f_equal; lia.
           ++ rewrite nth_overflow with (n := (y - n)%nat).
              ** unfold toCheckMatrixF2ElementRightZ.
                 rewrite H; auto; lia.
              ** rewrite fromCheckMatrixF2RowToLp_rec_length. simpl. lia.
        -- rewrite nth_overflow with (n := x).
           ++ rewrite nth_repeat. unfold toCheckMatrixF2ElementLeftX. rewrite H; auto; lia.
           ++ rewrite app_length. rewrite fromCheckMatrixF2ToLLp_rec_length_row. simpl. lia.
Qed.

Lemma exists_commute_anticommute_Lp : forall (n : nat) (LLp : list (list Pauli)),
    Forall (fun Lp : list Pauli => length Lp = n) LLp -> LLp <> [] -> (n > 0)%nat ->
    linearly_independentF2 ((fromLLpToCheckMatrixF2 (length LLp) n LLp) ⊤) ->
    (forall i : nat, (i < length LLp)%nat -> (exists Lp : list Pauli, length Lp = n /\ 
       anticommute_listP (nth i LLp (repeat gI n)) Lp /\
       (forall j : nat, (j < length LLp)%nat -> j <> i -> commute_listP (nth j LLp (repeat gI n)) Lp))).
Proof. intros n LLp H H0 H1 H2 i H3.
  destruct (existsCheckMatrixF2Vector n LLp H H0 H1 H2 i H3)
    as [v [WFv [v_to_e_i [to_one to_zero]]]].
  assert (WFvt: WF_MatrixF2 v ⊤). { apply F2Module.WF_transpose. auto. }
  pose (fromCheckMatrixF2ToLLpToCheckMatrixF2 (v⊤) WFvt) as e.
  assert ((fromLLpToCheckMatrixF2 1 n (fromCheckMatrixF2ToLLp (v) ⊤)) ⊤ = ((v) ⊤) ⊤).
  { rewrite e. auto. }
  rewrite F2Module.transpose_involutive in H4.
  rewrite <- H4 in to_one, to_zero.
  exists (nth 0%nat (fromCheckMatrixF2ToLLp (v) ⊤) (repeat gI n)).
  repeat split.
  - simpl. unfold fromCheckMatrixF2RowToLp. 
    rewrite fromCheckMatrixF2RowToLp_rec_length.
    simpl. auto.
  - rewrite <- fromLLpToCheckMatrixF2_checkLambdaF2_anticomm_iff. 
    + assert (length (nth i LLp (repeat gI n)) = n).
      { bdestruct (i <? length LLp).
        - rewrite Forall_nth in H. apply H; auto.
        - rewrite nth_overflow; auto; rewrite repeat_length; auto. }
      rewrite ! H5. apply to_one.
    + simpl. unfold fromCheckMatrixF2RowToLp.
      rewrite  fromCheckMatrixF2RowToLp_rec_length. simpl.
      bdestruct (i <? length LLp).
      * rewrite Forall_nth in H. rewrite H; auto.
      * rewrite nth_overflow; auto; rewrite repeat_length; auto.
    + rewrite Forall_nth in H. rewrite H; auto.
  - intros j H5 H6.
    rewrite <- fromLLpToCheckMatrixF2_checkLambdaF2_comm_iff. 
    + assert (length (nth j LLp (repeat gI n)) = n).
      { bdestruct (j <? length LLp).
        - rewrite Forall_nth in H. apply H; auto.
        - rewrite nth_overflow; auto; rewrite repeat_length; auto. }
      rewrite ! H7. apply to_zero; auto.
    + simpl. unfold fromCheckMatrixF2RowToLp.
      rewrite  fromCheckMatrixF2RowToLp_rec_length. simpl.
      bdestruct (j <? length LLp).
      * rewrite Forall_nth in H. rewrite H; auto.
      * rewrite nth_overflow; auto; rewrite repeat_length; auto.
    + rewrite Forall_nth in H. rewrite H; auto.
Qed.



(* Separability Semantics *)
Close Scope F2_scope.
Local Open Scope genmatrix_scope.
Local Open Scope matrix_scope.

Declare Module CField : FieldModule
  with Definition F := C
  with Definition R0 := C_is_monoid
  with Definition R1 := C_is_group
  with Definition R2 := C_is_comm_group
  with Definition R3 := C_is_ring
  with Definition R4 := C_is_comm_ring
  with Definition R5 := C_is_field.

Module CM := SubspacesOverField CField.



Definition stabilizeByListT
  {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt : list (TType n)) (v : Vector (2 ^ n)%nat) := 
  P v /\ (forall t : TType n, In t Lt -> (@Mmult (2 ^ n)%nat (2 ^ n)%nat 1%nat (translate t) v = v)).

Lemma stabilizeByListT_is_subspace : 
  forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt : list (TType n)),
    @CM.subspace (2 ^ n)%nat P ->
    @CM.subspace (2 ^ n)%nat (stabilizeByListT P Lt).
Proof. intros n P Lt H. 
  unfold stabilizeByListT in *.
  unfold CM.subspace in *.
 split; [idtac | split; [idtac | split]]; intros.
 - destruct H0.
   destruct H as [H2 [H3 [H4 H5]]].
   apply H2; auto.
 - destruct H as [H0 [H1 [H2 H3]]].
   split; auto. intros t H.
   rewrite Mmult_0_r. lma'.
 - destruct H as [H [H2 [H3 H4]]].
   destruct H0, H1.
   split.
   + apply H3; auto.
   + intros t H7.
     rewrite Mmult_plus_distr_l.
     f_equal.
     * intros. rewrite <- H10 at 2. rewrite <- H11 at 2.
       lma.
     * apply H5; auto.
     * apply H6; auto.
 - destruct H as [H [H2 [H3 H4]]].
   destruct H0.
   split; auto.
   intros t H5.
   rewrite Mscale_mult_dist_r.
   f_equal. intros. rewrite H9. auto.
   apply H1; auto.
Qed.

Lemma stabilizeByListT_app : 
  forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt1 Lt2 : list (TType n)),
    (forall v : Vector (2 ^ n)%nat, stabilizeByListT P (Lt1 ++ Lt2) v <->
                               stabilizeByListT P Lt1 v /\ stabilizeByListT P Lt2 v).
Proof. intros n P Lt1 Lt2 v. 
  unfold stabilizeByListT in *. 
  split; intros.
  - destruct H.
    repeat (split; auto); intros.
    + apply H0.
      rewrite in_app_iff.
      left. auto.
    + apply H0.
      rewrite in_app_iff.
      right. auto.
  - destruct H as [[H H0] [H1 H2]].
    split; auto; intros.
    rewrite in_app_iff in H3.
    destruct H3.
    + apply H0; auto.
    + apply H2; auto.
Qed.

Lemma stabilizeByListT_app_comm : 
  forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt1 Lt2 : list (TType n)),
    (forall v : Vector (2 ^ n)%nat, stabilizeByListT P (Lt1 ++ Lt2) v <->
                               stabilizeByListT P (Lt2 ++ Lt1) v).
Proof. intros n P Lt1 Lt2 v.
  split; intros;
  rewrite stabilizeByListT_app; 
    rewrite and_comm; 
    rewrite <- stabilizeByListT_app;
    auto.
Qed.

Lemma stabilizeByListT_cons : 
  forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt : list (TType n)) (t : TType n),
    (forall v : Vector (2 ^ n)%nat, stabilizeByListT P (t :: Lt) v <->
                               stabilizeByListT P [t] v /\ stabilizeByListT P Lt v).
Proof. intros n P Lt t v.
  replace (t :: Lt) with ([t] ++ Lt) by (simpl; auto).
  rewrite stabilizeByListT_app; split; auto.
Qed.

Lemma stabilizeByListT_Permutation : 
  forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop) (Lt1 Lt2 : list (TType n)),
    Permutation Lt1 Lt2 ->
    (forall v : Vector (2^n)%nat, stabilizeByListT P Lt1 v -> stabilizeByListT P Lt2 v).
Proof. intros n P Lt1 Lt2 H v H0.
  induction H; auto.
  - rewrite stabilizeByListT_cons.
    assert ((stabilizeByListT P [x] v /\ stabilizeByListT P l v) ->
            (stabilizeByListT P [x] v /\ stabilizeByListT P l' v)).
    { intros H1. destruct H1. split; auto. }
    apply H1.
    rewrite <- stabilizeByListT_cons; auto.
  - rewrite stabilizeByListT_cons in H0.
    destruct H0.
    rewrite stabilizeByListT_cons in H0.
    destruct H0. 
    rewrite stabilizeByListT_cons. split; auto.
    rewrite stabilizeByListT_cons. split; auto.
Qed.

Lemma stabilizeByListT_nil : forall {n : nat} (P : Vector (2 ^ n)%nat -> Prop),
    (forall v : Vector (2^n)%nat, stabilizeByListT P [] v <-> P v).
Proof. intros n P v.
  unfold stabilizeByListT.
  split; intros.
  - destruct H; auto.
  - split; auto. intros. inversion H0.
Qed.


Lemma translate_defaultT_I_comm : forall {n : nat} (t : TType n),
    proper_length_TType t ->
    (translate (defaultT_I n) × translate t = translate t × translate (defaultT_I n))%M.
Proof. intros n t H.
  rewrite ! translate_defaultT_I.
  rewrite Mmult_1_l, Mmult_1_r; auto.
  all : apply WF_translate; auto.
Qed.


Lemma anticommute_commute_T_translate : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    (anticommute_T t1 t2 -> translate(t1) × translate(t2) = -C1 .* (translate(t2) × translate(t1))) /\
    (commute_T t1 t2 -> translate(t1) × translate(t2) = translate(t2) × translate(t1)).
Proof. intros n t1 t2 H H0. 
  destruct t1, t2, H, H0; unfold translate; simpl in *.
  split; intros.
  - inversion H3; clear H3; simpl in *.
    gen n.
    apply anticommute_listP_ind' with 
      (P0 := fun l l0 : list Pauli => forall n : nat, n <> 0%nat -> length l = n -> n <> 0%nat -> length l0 = n -> @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c .* (⨂ map translate_P l)) (c0 .* (⨂ map translate_P l0)) = - C1 .* (@Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c0 .* (⨂ map translate_P l0)) (c .* (⨂ map translate_P l))))
      (P := fun l l0 : list Pauli => forall n : nat, n <> 0%nat -> length l = n -> n <> 0%nat -> length l0 = n -> @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c .* (⨂ map translate_P l)) (c0 .* (⨂ map translate_P l0)) = @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c0 .* (⨂ map translate_P l0)) (c .* (⨂ map translate_P l))) in H4; intros.
    + apply H4; auto.
    + inversion H.
      destruct H5 as [H5 | [H5 | H5]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *. 
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct H3 as [H3 | [H3 | H3]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
      * destruct l1, l2; inversion H0; subst; simpl in *.
        -- rewrite ! Matrix.kron_1_r in *.
           apply (H1 1%nat); lia.
        -- apply (H1 (S (length l1))); lia.
        -- apply (H1 (S (length l1))); lia.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *. 
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      assert (translate_P P2 × translate_P P1 = -C1 .* (translate_P P1 × translate_P P2)).
      { inversion H. destruct P1, P2; try contradiction; simpl; lma'. }
      rewrite H3.
      setoid_rewrite Mscale_kron_dist_l.
      setoid_rewrite <- Mscale_kron_dist_r.
      f_equal.
      apply anticommute_listP_nonempty_equal_len in H0.
      destruct H0. destruct H7.
      apply H1; auto;
        intro H'; rewrite length_zero_iff_nil in H'; contradiction.
    + simpl in *.
      inversion H.
      rewrite ! Matrix.kron_1_r in *.
      subst. rewrite ! Mscale_mult_dist_l, ! Mscale_mult_dist_r.
      rewrite ! Mscale_assoc.
      replace (- C1 * c0 * c) with (c * c0 * - C1) by lca.
      rewrite <- ! Mscale_assoc.
      do 2 f_equal.
      destruct P1, P2; try contradiction; simpl; lma'.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite <- Mscale_mult_dist_l.
      setoid_rewrite <- Mscale_kron_dist_l.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct P1, P2; try contradiction; simpl; lma'. 
      * destruct l1, l2; inversion H0; subst; simpl in *.
        -- rewrite ! Matrix.kron_1_r in *.
           apply (H1 1%nat); lia.
        -- apply (H1 (S (length l1))); lia.
        -- apply (H1 (S (length l1))); lia.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite <- Mscale_mult_dist_l.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct H3 as [H3 | [H3 | H3]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
      * apply anticommute_listP_nonempty_equal_len in H0.
        destruct H0. destruct H3.
        setoid_rewrite Mscale_mult_dist_l with (x := (- C1)%C).
        apply H1; auto;
          intro H'; rewrite length_zero_iff_nil in H'; contradiction.
  - inversion H3; clear H3; simpl in *.
    gen n.
    apply commute_listP_ind' with 
      (P0 := fun l l0 : list Pauli => forall n : nat, n <> 0%nat -> length l = n -> n <> 0%nat -> length l0 = n -> @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c .* (⨂ map translate_P l)) (c0 .* (⨂ map translate_P l0)) = - C1 .* (@Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c0 .* (⨂ map translate_P l0)) (c .* (⨂ map translate_P l))))
      (P := fun l l0 : list Pauli => forall n : nat, n <> 0%nat -> length l = n -> n <> 0%nat -> length l0 = n -> @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c .* (⨂ map translate_P l)) (c0 .* (⨂ map translate_P l0)) = @Mmult (2 ^ n)%nat (2 ^ n)%nat (2 ^ n)%nat (c0 .* (⨂ map translate_P l0)) (c .* (⨂ map translate_P l))) in H4; intros.
    + apply H4; auto.
    + inversion H.
      destruct H5 as [H5 | [H5 | H5]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *. 
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct H3 as [H3 | [H3 | H3]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
      * destruct l1, l2; inversion H0; subst; simpl in *.
        -- rewrite ! Matrix.kron_1_r in *.
           apply (H1 1%nat); lia.
        -- apply (H1 (S (length l1))); lia.
        -- apply (H1 (S (length l1))); lia.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *. 
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      assert (translate_P P2 × translate_P P1 = -C1 .* (translate_P P1 × translate_P P2)).
      { inversion H. destruct P1, P2; try contradiction; simpl; lma'. }
      rewrite H3.
      setoid_rewrite Mscale_kron_dist_l.
      setoid_rewrite <- Mscale_kron_dist_r.
      f_equal.
      apply anticommute_listP_nonempty_equal_len in H0.
      destruct H0. destruct H7.
      apply H1; auto;
        intro H'; rewrite length_zero_iff_nil in H'; contradiction.
    + simpl in *.
      inversion H.
      rewrite ! Matrix.kron_1_r in *.
      subst. rewrite ! Mscale_mult_dist_l, ! Mscale_mult_dist_r.
      rewrite ! Mscale_assoc.
      replace (- C1 * c0 * c) with (c * c0 * - C1) by lca.
      rewrite <- ! Mscale_assoc.
      do 2 f_equal.
      destruct P1, P2; try contradiction; simpl; lma'.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite <- Mscale_mult_dist_l.
      setoid_rewrite <- Mscale_kron_dist_l.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct P1, P2; try contradiction; simpl; lma'. 
      * destruct l1, l2; inversion H0; subst; simpl in *.
        -- rewrite ! Matrix.kron_1_r in *.
           apply (H1 1%nat); lia.
        -- apply (H1 (S (length l1))); lia.
        -- apply (H1 (S (length l1))); lia.
    + simpl in *. destruct n; try contradiction.
      apply Nat.succ_inj in H3, H6.
      rewrite ! map_length in *. subst. rewrite ! H6 in *.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite <- Mscale_mult_dist_l.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite kron_mixed_product'; auto.
      f_equal.
      * inversion H.
        destruct H3 as [H3 | [H3 | H3]]; subst;
        try destruct P1; try destruct P2; simpl in *; lma'.
      * apply anticommute_listP_nonempty_equal_len in H0.
        destruct H0. destruct H3.
        setoid_rewrite Mscale_mult_dist_l with (x := (- C1)%C).
        apply H1; auto;
          intro H'; rewrite length_zero_iff_nil in H'; contradiction.
Qed.

Lemma anticommute_T_translate_anticomm : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    anticommute_T t1 t2 -> translate(t1) × translate(t2) = -C1 .* (translate(t2) × translate(t1)).
Proof. intros n t1 t2 H H0 H1.
  destruct (anticommute_commute_T_translate t1 t2 H H0); auto.
Qed.

Lemma commute_T_translate_comm : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    commute_T t1 t2 -> translate(t1) × translate(t2) = translate(t2) × translate(t1).
Proof. intros n t1 t2 H H0 H1.
  destruct (anticommute_commute_T_translate t1 t2 H H0); auto.
Qed.


Definition commutingListT {n : nat} (Lt : list (TType n)) :=
  forall t1 t2 : TType n, In t1 Lt -> In t2 Lt -> commute_T t1 t2.

Definition Lt_to_LLp {n : nat} (Lt : list (TType n)) : list (list Pauli) := map snd Lt.

Definition fromLtToCheckMatrixF2 {n : nat} (Lt : list (TType n)) := 
  fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt).

Lemma WF_fromLtToCheckMatrixF2 : forall {n : nat} (Lt : list (TType n)),
  Forall proper_length_TType Lt ->
  WF_MatrixF2 (fromLtToCheckMatrixF2 Lt).
Proof. intros n Lt H.
  unfold fromLtToCheckMatrixF2.
  apply WF_fromLLpToCheckMatrixF2.
  unfold Lt_to_LLp. rewrite map_length. auto.
  unfold Lt_to_LLp.
  rewrite Forall_forall in *.
  intros x H0.
  rewrite in_map_iff in H0.
  destruct H0 as [[c lp] [H0 H1]].
  simpl in *; subst.
  specialize (H (c, x) H1).
  destruct H. simpl in H0.
  lia.
Qed.

Lemma exists_commute_anticommute_T : forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Lt <> [] -> n <> 0%nat ->
    linearly_independentF2 ((fromLtToCheckMatrixF2 Lt) ⊤)%F2 ->
    (forall i : nat, (i < length Lt)%nat -> (exists t : TType n, proper_length_TType t /\
       coef_plus_minus_1 t /\ anticommute_T (nth i Lt (defaultT_I n)) t /\
       (forall j : nat, (j < length Lt)%nat -> j <> i -> commute_T (nth j Lt (defaultT_I n)) t))).
Proof. intros n Lt H H0 H1 H2 i H3.
  pose exists_commute_anticommute_Lp as E.
  assert (Forall (fun Lp : list Pauli => length Lp = n) (Lt_to_LLp Lt)).
  { unfold Lt_to_LLp. rewrite Forall_map.
    apply Forall_impl with (P := proper_length_TType); auto.
    intros a H4. destruct H4; auto. }
  assert (Lt_to_LLp Lt <> []).
  { unfold Lt_to_LLp. intro. destruct Lt; try contradiction.
    destruct t. simpl in *. discriminate. }
  assert (n > 0)%nat by lia.
  assert (linearly_independentF2 (transposeF2
           (fromLLpToCheckMatrixF2 (length (Lt_to_LLp Lt)) n (Lt_to_LLp Lt)))).
  { unfold fromLtToCheckMatrixF2 in H2. unfold Lt_to_LLp in *.
    rewrite map_length. auto. }
  assert (i < length (Lt_to_LLp Lt))%nat.
  { unfold Lt_to_LLp. rewrite map_length. auto. }
  specialize (E n (Lt_to_LLp Lt) H4 H5 H6 H7 i H8).
  destruct E as [Lp [lenLp [anticomm_i comm_j]]].
  exists (C1, Lp).
  repeat split; auto; try lia.
  - unfold coef_plus_minus_1. left. auto.
  - simpl. unfold Lt_to_LLp in anticomm_i.
    assert (snd (defaultT_I n) = repeat gI n).
    { unfold defaultT_I. auto. }
    rewrite <- H9 in anticomm_i.
    rewrite map_nth in anticomm_i. auto.
  - simpl. unfold Lt_to_LLp in comm_j.
    assert (snd (defaultT_I n) = repeat gI n).
    { unfold defaultT_I. auto. }
    rewrite map_length in comm_j.
    specialize (comm_j j H9 H10).
    rewrite <- H11 in comm_j.
    rewrite map_nth in comm_j. auto.
Qed.

Lemma commutingListT_iff_checkLambdaF2_is_Zero : forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt ->
    (commutingListT Lt <-> 
       ((fromLtToCheckMatrixF2 Lt) ×
         (checkLambdaF2 n) ×
         ((fromLtToCheckMatrixF2 Lt) ⊤) = ZeroF2)%F2).
Proof. intros n Lt H. 
  unfold fromLtToCheckMatrixF2.
  split; intros.
  - unfold commutingListT in H0.
    assert (WF_MatrixF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt) × checkLambdaF2 n × transposeF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt)))%F2).
    { apply F2Module.WF_mult. apply F2Module.WF_mult.
      apply WF_fromLLpToCheckMatrixF2.
      unfold Lt_to_LLp. inversion H; auto. simpl. rewrite map_length. auto.
      unfold Lt_to_LLp. clear H0. induction H; auto. simpl. constructor; auto.
      inversion H. lia.
      apply WF_checkLambdaF2.
      apply F2Module.WF_transpose.
      apply WF_fromLLpToCheckMatrixF2.
      unfold Lt_to_LLp. inversion H; auto. simpl. rewrite map_length. auto.
      unfold Lt_to_LLp. clear H0. induction H; auto. simpl. constructor; auto.
      inversion H. lia. }
    prep_matrix_equality.
    bdestruct (x <? (length Lt)).
    + bdestruct (y <? (length Lt)).
      * unfold ZeroF2.
        inversion H.
        -- subst; clear H; simpl in *; lia.
        -- rewrite H6. 
           assert ((fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt) × checkLambdaF2 n
   × transposeF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt)))%F2 x y =
                  (get_colF2 (get_rowF2 ((fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt) × checkLambdaF2 n
   × transposeF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt)))%F2) x) y) 0%nat 0%nat).
        { unfold get_rowF2, get_colF2. bdestruct_all. auto. }
        rewrite H7.
        rewrite F2Module.GMmult_assoc.
        rewrite <- F2Module.get_row_mult.
        rewrite <- F2Module.GMmult_assoc.
        rewrite <- F2Module.get_col_mult.
        rewrite <- F2Module.get_row_transpose.
        setoid_rewrite rowF2_fromLLpToCheckMatrixF2.
        pose fromLLpToCheckMatrixF2_checkLambdaF2_comm_iff as e.
        specialize (e (nth x (Lt_to_LLp Lt) (repeat gI n)) (nth y (Lt_to_LLp Lt) (repeat gI n))).        
        assert (length (nth x (Lt_to_LLp Lt) (repeat gI n)) = n).
        { unfold Lt_to_LLp.
          assert (snd (defaultT_I n) = repeat gI n).
          { unfold defaultT_I. auto. }
          rewrite <- H8.
          rewrite map_nth.
          assert (In (nth x Lt (defaultT_I n)) Lt) by (apply nth_In; auto).
          rewrite Forall_forall in H.
          specialize (H (nth x Lt (defaultT_I n)) H9).
          inversion H. auto. }
        assert (length (nth y (Lt_to_LLp Lt) (repeat gI n)) = n).
        { unfold Lt_to_LLp.
          assert (snd (defaultT_I n) = repeat gI n).
          { unfold defaultT_I. auto. }
          rewrite <- H9.
          rewrite map_nth.
          assert (In (nth y Lt (defaultT_I n)) Lt) by (apply nth_In; auto).
          rewrite Forall_forall in H.
          specialize (H (nth y Lt (defaultT_I n)) H10).
          inversion H. auto. }
        rewrite H8, H9 in e.
        rewrite e; auto.
        specialize (H0 (nth x Lt (defaultT_I n)) (nth y Lt (defaultT_I n))).
        assert (In (nth x Lt (defaultT_I n)) Lt).
        { apply nth_In; auto. }
        assert (In (nth y Lt (defaultT_I n)) Lt).
        { apply nth_In; auto. }
        specialize (H0 H10 H11).
        inversion H0.
        unfold Lt_to_LLp.
        setoid_rewrite <- map_nth in H12.
        assert (snd (defaultT_I n) = repeat gI n).
        { unfold defaultT_I. auto. }
        rewrite ! H13 in H12. auto.
        inversion H4; lia.
        unfold Lt_to_LLp.
        rewrite Forall_map.
        apply Forall_impl with (P := proper_length_TType); auto.
        intros a H8.
        inversion H8; auto.
        rewrite <- H6. unfold Lt_to_LLp. simpl. intro H8. inversion H8.
        inversion H4; lia.
        unfold Lt_to_LLp.
        rewrite Forall_map.
        apply Forall_impl with (P := proper_length_TType); auto.
        intros a H8.
        inversion H8; auto.
        rewrite <- H6. unfold Lt_to_LLp. simpl. intro H8. inversion H8.
        inversion H4; lia.
      * rewrite H1; auto.
    + rewrite H1; auto.
  - unfold commutingListT. 
    intros t1 t2 H1 H2.
    inversion H. subst. inversion H1.
    constructor.
    destruct t1, t2; simpl.
    rewrite <- fromLLpToCheckMatrixF2_checkLambdaF2_comm_iff.
    apply In_nth with (d := defaultT_I n) in H1, H2.
    destruct H1 as [a [H1 H6]].
    destruct H2 as [b [H2 H7]].
    unfold ZeroF2 in *.
    apply f_equal_inv with (x := a) in H0.
    apply f_equal_inv with (x := b) in H0.
    assert ((fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt) × checkLambdaF2 n
   × transposeF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt)))%F2 a b =
                  (get_colF2 (get_rowF2 ((fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt) × checkLambdaF2 n
   × transposeF2 (fromLLpToCheckMatrixF2 (length Lt) n (Lt_to_LLp Lt)))%F2) a) b) 0%nat 0%nat).
        { unfold get_rowF2, get_colF2. bdestruct_all. auto. }
        rewrite H8 in H0.
        rewrite F2Module.GMmult_assoc in H0.
        rewrite <- F2Module.get_row_mult in H0.
        rewrite <- F2Module.GMmult_assoc in H0.
        rewrite <- F2Module.get_col_mult in H0.
        rewrite <- F2Module.get_row_transpose in H0.
        setoid_rewrite rowF2_fromLLpToCheckMatrixF2 in H0.
        unfold Lt_to_LLp in H0.
        assert (snd (defaultT_I n) = repeat gI n).
        { unfold defaultT_I. auto. }
        rewrite <- ! H9 in H0.
        rewrite ! map_nth in H0.
        setoid_rewrite H6 in H0.
        setoid_rewrite H7 in H0.
        simpl in *.
        assert (length l0 = n).
        { assert (In (nth a Lt (defaultT_I n)) Lt) by (apply nth_In; auto).
          rewrite Forall_forall in H.
          specialize (H (nth a Lt (defaultT_I n)) H10).
          inversion H.
          rewrite H6 in H12.
          simpl in H12. auto. }
        rewrite ! H10.
        auto.
        unfold Lt_to_LLp. rewrite Forall_map. 
        apply Forall_impl with (P := proper_length_TType); auto. intros a0 H9.
        inversion H9. auto.
        unfold Lt_to_LLp. rewrite <- H5. simpl. intro H9. inversion H9.
        inversion H3. lia.
        unfold Lt_to_LLp. rewrite Forall_map. 
        apply Forall_impl with (P := proper_length_TType); auto. intros a0 H9.
        inversion H9. auto.
        unfold Lt_to_LLp. rewrite <- H5. simpl. intro H9. inversion H9.
        inversion H3. lia.
        rewrite Forall_forall in H.
        remember H as H'. clear HeqH'.
        specialize (H (c, l0) H1).
        destruct H. simpl in H6.
        specialize (H' (c0, l1) H2).
        destruct H'. simpl in H8.
        subst; lia.
        rewrite Forall_forall in H.
        remember H as H'. clear HeqH'.
        specialize (H (c, l0) H1).
        destruct H. simpl in H6.
        lia.
Qed.


Lemma commutingListT_cons : forall {n : nat} (Lt : list (TType n)) (t : TType n),
    commutingListT (t :: Lt) -> ((forall t' : TType n, In t' Lt -> commute_T t t') /\ commutingListT Lt).
Proof. intros n Lt t. unfold commutingListT. split; intros; apply H; simpl; auto. Qed.

Lemma commutingListT_cons_iff : forall {n : nat} (Lt : list (TType n)) (t : TType n),
    proper_length_TType t ->
    (commutingListT (t :: Lt) <-> ((forall t' : TType n, In t' Lt -> commute_T t t') /\ commutingListT Lt)).
Proof. intros n Lt t H. split. apply commutingListT_cons.
  intros H0. destruct H0.
  unfold commutingListT in *. intros t1 t2 H2 H3. 
  destruct H2, H3; subst; auto.
  - apply self_commute_T; auto.
  - apply commute_T_swap. auto.
Qed.

Lemma commutingListT_Permutation : forall {n : nat} (Lt1 Lt2 : list (TType n)),
    commutingListT Lt1 -> Permutation Lt1 Lt2 -> commutingListT Lt2.
Proof. intros n Lt1 Lt2 H H0.
  unfold commutingListT in *.
  intros t1 t2 H1 H2.
  apply Permutation_sym in H0.
  apply (Permutation_in t1 H0) in H1.
  apply (Permutation_in t2 H0) in H2.
  auto.
Qed.

Lemma fold_right_Mmult_map_translate_Permutation :
  forall {n : nat} (Lt1 Lt2 : list (TType n)),
    commutingListT Lt1 -> Forall proper_length_TType Lt1 -> Permutation Lt1 Lt2 -> 
    fold_right Mmult (I (2 ^ n)%nat) (map translate Lt1) = 
      fold_right Mmult (I (2 ^ n)%nat) (map translate Lt2).
Proof. intros n Lt1 Lt2 H H0 H1.
  induction H1; auto.
  - simpl. f_equal.
    apply commutingListT_cons in H. destruct H.
    rewrite Forall_cons_iff in H0. destruct H0.
    apply IHPermutation; auto.
  - simpl. rewrite <- ! Mmult_assoc.
    apply commutingListT_cons in H. destruct H.
    apply commutingListT_cons in H1. destruct H1.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H3. destruct H3.
    rewrite commute_T_translate_comm; auto.
    apply H; simpl; auto.
  - rewrite IHPermutation1; auto.
    pose (commutingListT_Permutation l l' H H1_) as H'.
    rewrite IHPermutation2; auto.
    rewrite Forall_forall.
    intros x H1.
    clear H'.
    apply Permutation_sym in H1_.
    apply (Permutation_in x H1_) in H1.
    gen x. rewrite <- Forall_forall. auto.
Qed.


(* (-1)^z *)
Definition neg_powF2 (z : F2) : C :=
  match z with
  | zero => C1
  | one => (- C1)%C
  end.

Lemma neg_powF2_idempotent : forall (z : F2),
    (neg_powF2 z) * (neg_powF2 z) = C1.
Proof. intros z. destruct z; lca. Qed.


Definition projectorT {n : nat} (z : F2) (t : TType n) : Square (2 ^ n) :=
  Matrix.scale (1 / C2) (Matrix.Mplus (translate (defaultT_I n)) (neg_powF2 z .* (translate t))).

Lemma WF_projectorT : forall {n : nat} (z : F2) (t : TType n),
    proper_length_TType t -> WF_Matrix (projectorT z t).
Proof. intros n z t H.
  unfold projectorT.
  apply WF_scale.
  apply WF_plus.
  apply WF_translate.
  unfold proper_length_TType, defaultT_I in *.
  simpl in *. destruct H. split; auto. apply repeat_length.
  apply WF_scale.
  apply WF_translate; auto.
Qed.

Lemma projectorT_comm : forall {n : nat} (z1 z2 : F2) (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    commute_T t1 t2 -> 
    (projectorT z1 t1) × (projectorT z2 t2) = (projectorT z2 t2) × (projectorT z1 t1).
Proof. intros n z1 z2 t1 t2 H H0 H1.
  unfold projectorT. 
  distribute_scale. f_equal.
  distribute_plus. 
  rewrite <- ! Mplus_assoc. f_equal. 
  rewrite ! Mplus_assoc. f_equal.
  rewrite Mplus_comm. f_equal.
  rewrite ! translate_defaultT_I; rewrite ! Mmult_1_l, ! Mmult_1_r; auto with wf_db.
  rewrite ! translate_defaultT_I; rewrite ! Mmult_1_l, ! Mmult_1_r; auto with wf_db.
  distribute_scale.
  rewrite commute_T_translate_comm; auto. f_equal. lca.
Qed.

Lemma projectorT_idempotent : forall {n : nat} (z : F2) (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t ->
    (projectorT z t) × (projectorT z t) = (projectorT z t).
Proof. intros n z t H H0.
  unfold projectorT.
  distribute_scale. rewrite <- Mscale_assoc.
  f_equal. distribute_plus. distribute_scale.
  rewrite neg_powF2_idempotent. rewrite ! translate_mult_inv; auto.
  rewrite Mscale_1_l. rewrite translate_defaultT_I.
  rewrite Mmult_1_l, Mmult_1_r. lma'.
  apply WF_scale. apply WF_plus.
  apply WF_plus; auto with wf_db.
  apply WF_plus; auto with wf_db.
  auto with wf_db. auto with wf_db.
  apply proper_length_TType_defaultT_I. destruct H; auto.
  apply coef_plus_minus_1_defaultT_I.
Qed.


Definition projectorListT {n : nat} (Lz : list F2) (Lt : list (TType n)) : Square (2 ^ n) :=
  fold_right Mmult (I (2 ^ n)%nat) (zipWith projectorT Lz Lt).

Lemma projectorListT_commutingListT_Permutation :
  forall {n : nat} (Lz1 Lz2 : list F2) (Lt1 Lt2 : list (TType n)),
    commutingListT Lt1 -> Forall proper_length_TType Lt1 -> 
    length Lz1 = length Lt1 -> length Lz2 = length Lt2 -> 
    Permutation (combine Lz1 Lt1) (combine Lz2 Lt2) -> 
    projectorListT Lz1 Lt1 = projectorListT Lz2 Lt2.
Proof. intros n Lz1 Lz2 Lt1 Lt2 H H0 H1 H2 H3.
  unfold projectorListT.
  dependent induction H3.
  - destruct Lz1, Lt1; destruct Lz2, Lt2; simpl in *;
      try reflexivity; try discriminate.
  - unfold zipWith.
    destruct Lz1, Lt1; destruct Lz2, Lt2; simpl in *;
      try discriminate.
    f_equal.
    inversion x1. inversion x. subst. inversion H7; subst. auto.
    apply IHPermutation; auto.
    apply commutingListT_cons in H; destruct H; auto.
    rewrite Forall_cons_iff in H0; destruct H0; auto.
    inversion x1. auto.
    inversion x. auto.
  - destruct Lz1, Lt1; destruct Lz2, Lt2; simpl in *;
      try discriminate.
    destruct Lz1, Lt1; destruct Lz2, Lt2; simpl in *;
      try discriminate.
    unfold uncurry; simpl. rewrite <- ! Mmult_assoc.
    rewrite (projectorT_comm f f1 t t1).
    inversion x1. inversion x. subst. 
    inversion H7. inversion H8. subst. rewrite H9. auto.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H3. destruct H3. auto.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H3. destruct H3. auto.
    apply commutingListT_cons in H. destruct H. apply H; simpl; auto.
  - destruct (split l') eqn:E.
    rewrite <- (split_combine l' E) in *; auto.
    rewrite IHPermutation1 with (Lz2 := l) (Lt2 := l0); auto.
    rewrite IHPermutation2 with (Lz2 := Lz2) (Lt2 := Lt2); auto.
    remember H3_ as H3_'. clear HeqH3_'. 
    apply Permutation_map with (f := snd) in H3_'.
    rewrite ! map_snd_combine in H3_'; auto. apply Permutation_sym in H3_'.
    unfold commutingListT in *. intros t1 t2 H3 H4. apply H.
    apply Permutation_in with (l := l0); auto.
    apply Permutation_in with (l := l0); auto.
    pose (split_length_l l') as e1. rewrite E in e1. simpl in e1.
    pose (split_length_r l') as e2. rewrite E in e2. simpl in e2. rewrite e1, e2; auto.
    remember H3_ as H3_'. clear HeqH3_'. 
    apply Permutation_map with (f := snd) in H3_'.
    rewrite ! map_snd_combine in H3_'; auto. apply Permutation_sym in H3_'.
    rewrite Forall_forall in *. intros x H3. apply H0. apply Permutation_in with (l := l0); auto.
    pose (split_length_l l') as e1. rewrite E in e1. simpl in e1.
    pose (split_length_r l') as e2. rewrite E in e2. simpl in e2. rewrite e1, e2; auto.
    pose (split_length_l l') as e1. rewrite E in e1. simpl in e1.
    pose (split_length_r l') as e2. rewrite E in e2. simpl in e2. rewrite e1, e2; auto.
    pose (split_length_l l') as e1. rewrite E in e1. simpl in e1.
    pose (split_length_r l') as e2. rewrite E in e2. simpl in e2. rewrite e1, e2; auto.
Qed.

Lemma WF_projectorListT : forall {n : nat} (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> Forall proper_length_TType Lt ->
    WF_Matrix (projectorListT Lz Lt).
Proof. intros n Lz Lt H H0.
  unfold projectorListT.
  unfold zipWith, uncurry.
  gen Lz. induction Lt as [| t Lt]; intros.
  - simpl in *. rewrite length_zero_iff_nil in H. subst. simpl. auto with wf_db.
  - destruct Lz as [| z Lz]. inversion H.
    simpl in *.
    rewrite Forall_cons_iff in H0. destruct H0.
    apply Nat.succ_inj in H.
    specialize (IHLt H1 Lz H).
    apply WF_mult; auto.
    apply WF_projectorT; auto.
Qed.

Lemma projectorListT_cons : forall {n : nat} (Lz : list F2) (Lt : list (TType n)) (z : F2) (t : TType n),
    (projectorListT (z :: Lz) (t :: Lt)) = (projectorT z t) × (projectorListT Lz Lt).
Proof. intros n Lz Lt z t.
  unfold projectorListT. auto.
Qed.

Lemma projectorListT_singleton : forall {n : nat} (z : F2) (t : TType n),
    proper_length_TType t -> projectorListT [z] [t] = projectorT z t.
Proof. intros n z t H.
  unfold projectorListT.
  unfold zipWith, uncurry. simpl.
  rewrite Mmult_1_r; auto.
  apply WF_projectorT; auto.
Qed.

Lemma projectorListT_app : forall {n : nat} (Lz1 Lz2 : list F2) (Lt1 Lt2 : list (TType n)),
    length Lz1 = length Lt1 -> length Lz2 = length Lt2 ->
    Forall proper_length_TType Lt2 ->
    (projectorListT (Lz1 ++ Lz2) (Lt1 ++ Lt2)) = 
      (projectorListT Lz1 Lt1) × (projectorListT Lz2 Lt2).
Proof. intros n Lz1 Lz2 Lt1 Lt2 H H0 H1.
  unfold projectorListT.
  unfold zipWith. rewrite combine_app; auto.
  rewrite map_app.
  rewrite fold_right_Mmult_I_app; auto.
  clear H Lz1 Lt1.
  gen Lz2. induction Lt2; intros.
  - rewrite combine_nil. simpl. constructor.
  - destruct Lz2; try discriminate.
    rewrite Forall_cons_iff in H1. destruct H1.
    simpl. constructor.
    + unfold uncurry. simpl. 
      apply WF_projectorT. auto.
    + apply IHLt2; auto.
Qed.

Lemma projector_span_stabilized_space : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t -> n <> 0%nat ->
    (forall v : Vector (2 ^ n)%nat, 
        @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorT zero t) v <-> 
          stabilizeByListT (fun v => WF_Matrix v) [t] v).
Proof. intros n t H H0 H1 v. 
  unfold CM.span, stabilizeByListT.
  unfold projectorT.
  unfold neg_powF2; simpl.
  rewrite Mscale_1_l.
  split; intros.
  - destruct H2 as [a [WFa H2]].
    split; auto; intros.
    + assert (CM.WF_GenMatrix a = @WF_Matrix (2 ^ n)%nat 1%nat a) by auto.
      assert (CM.GMmult (C1 / C2 .* (translate (defaultT_I n) .+ translate t)) a =
                Mmult (C1 / C2 .* (translate (defaultT_I n) .+ translate t)) a) by auto.
      rewrite H2, H4. rewrite H3 in WFa.
      apply WF_mult; auto. apply WF_scale; auto. apply WF_plus; auto.
      all: apply WF_translate; auto. unfold defaultT_I. 
      split; simpl; auto. rewrite repeat_length; auto.
    + destruct H3; subst; try contradiction.
    rewrite translate_defaultT_I.
    assert (@CM.GMmult (2 ^ n) (2 ^ n) 1%nat (C1 / C2 .* (I (2 ^ n) .+ translate t0)) a = 
              @Mmult (2 ^ n) (2 ^ n) 1%nat (C1 / C2 .* (I (2 ^ n) .+ translate t0)) a)
      by auto.
    rewrite H2.
    rewrite <- Mmult_assoc. f_equal.
    distribute_scale. f_equal.
    rewrite Mmult_plus_distr_l.
    rewrite translate_mult_inv; auto.
    rewrite Mmult_1_r. apply Mplus_comm.
    apply WF_translate; auto.
  - destruct H2 as [WFv H2].
    assert (H' : t = t \/ False) by auto.
    specialize (H2 t H'). clear H'.
    unfold proper_length_TType, coef_plus_minus_1 in *.
    destruct H.
    exists v. split.
    assert (CM.WF_GenMatrix v = WF_Matrix v) by auto.
    rewrite H4; auto.
    assert (CM.GMmult (C1 / C2 .* (translate (defaultT_I n) .+ translate t)) v =
              Mmult (C1 / C2 .* (translate (defaultT_I n) .+ translate t)) v) by auto.
    rewrite H4.
    distribute_scale.
    distribute_plus.
    rewrite H2.
    rewrite translate_defaultT_I.
    rewrite Mmult_1_l; auto.
    lma'.
Qed.
  
Lemma projectorListT_span_stabilized_space : forall {n : nat} (Lt : list (TType n)),
    commutingListT Lt ->
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt -> n <> 0%nat ->
    (forall v : Vector (2 ^ n)%nat, 
        @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT (repeat zero (length Lt)) Lt) v <-> 
          stabilizeByListT (fun v => WF_Matrix v) Lt v).
Proof. intros n Lt commutingListTLt H H0 H1 v. 
  split; intros.
  - gen v. induction Lt as [| t Lt]; intros.
    + unfold stabilizeByListT, projectorListT in *. simpl in *.
      unfold CM.span in H2.
      destruct H2 as [a [WFa va]].
      assert (CM.WF_GenMatrix a = WF_Matrix a) by auto.
      assert (CM.GMmult (I (2 ^ n)) a = Mmult (I (2 ^ n)) a) by auto.
      rewrite H3 in va. rewrite H2 in WFa.
      rewrite Mmult_1_l in va; auto. subst.
      split; auto. intros t H4. contradiction. 
    + simpl in *. unfold CM.span in H2.
      destruct H2 as [a [WFa va]].
      assert (CM.WF_GenMatrix a = WF_Matrix a) by auto.
      assert (CM.GMmult (projectorListT (0%F2 :: repeat 0%F2 (length Lt)) (t :: Lt)) a =
                Mmult (projectorListT (0%F2 :: repeat 0%F2 (length Lt)) (t :: Lt)) a) by auto.
      rewrite H2 in WFa. rewrite H3 in va. clear H2 H3.
      remember H as proper_length_TType_Lt'. clear Heqproper_length_TType_Lt'.
      rewrite Forall_cons_iff in H. destruct H.
      remember H0 as coef_plus_minus_1_Lt'. clear Heqcoef_plus_minus_1_Lt'.
      rewrite Forall_cons_iff in H0. destruct H0.
      remember commutingListTLt as commutingListTLt'. clear HeqcommutingListTLt'.
      apply commutingListT_cons in commutingListTLt. 
      destruct commutingListTLt as [commute_t commutingListTLt].
      specialize (IHLt commutingListTLt H2 H3).
      unfold CM.span in IHLt.
      split.
      * rewrite projectorListT_cons in va.
        rewrite va. apply WF_mult; auto.
        apply WF_mult.
        apply WF_projectorT; auto.
        apply WF_projectorListT; auto.
        rewrite repeat_length; auto.
      * intros t0 H4. destruct H4; subst.
        -- rewrite projectorListT_cons.
           pose (projector_span_stabilized_space t0 H H0 H1) as e.
           unfold CM.span in e.
           specialize (e (projectorT 0%F2 t0 × projectorListT (repeat 0%F2 (length Lt)) Lt × a)).
           assert (exists a0 : CM.GenMatrix (2 ^ n) 1,
                      CM.WF_GenMatrix a0 /\
                        @Mmult (2 ^ n) (2 ^ n) 1 (@Mmult (2 ^ n) (2 ^ n) 1 (projectorT 0%F2 t0) (projectorListT (repeat 0%F2 (length Lt)) Lt)) a =
         @CM.GMmult (2 ^ n) (2 ^ n) 1 (projectorT 0%F2 t0) a0).
           { exists (@Mmult (2 ^ n) (2 ^ n) 1 (projectorListT (repeat 0%F2 (length Lt)) Lt) a).
             split.
             - assert (CM.WF_GenMatrix (@Mmult (2 ^ n) (2 ^ n) 1 (projectorListT (repeat 0%F2 (length Lt)) Lt) a) = 
                         WF_Matrix (projectorListT (repeat 0%F2 (length Lt)) Lt × a)) by auto.
               rewrite H4. apply WF_mult; auto.
               apply WF_projectorListT; auto. rewrite repeat_length; auto.
             - assert (CM.GMmult (projectorT 0%F2 t0) (@Mmult (2 ^ n) (2 ^ n) 1 (projectorListT (repeat 0%F2 (length Lt)) Lt) a) = Mmult (projectorT 0%F2 t0) (projectorListT (repeat 0%F2 (length Lt)) Lt × a)) by auto.
               rewrite H4. rewrite <- Mmult_assoc. auto. }
           rewrite e in H4.
           unfold stabilizeByListT in H4.
           destruct H4. specialize (H5 t0). apply H5; simpl; auto.
        -- remember H4 as t0_in_Lt. clear Heqt0_in_Lt.
          apply In_nth with (d := defaultT_I n) in H4.
           destruct H4 as [k [k_bounded nth_k_Lt]].
           rewrite (nth_inc k Lt (defaultT_I n)) at 2; auto.
           rewrite (nth_inc k Lt (defaultT_I n)) at 6; auto.
           rewrite nth_k_Lt.
           assert (Permutation (combine (0%F2 :: repeat 0%F2 (length Lt))
                                        (t :: firstn k Lt ++ [t0] ++ skipn (S k) Lt))
                     (combine (0%F2 :: repeat 0%F2 (length Lt))
                              (t0 :: firstn k Lt ++ [t] ++ skipn (S k) Lt))).
           { replace (length Lt) with (k + (1%nat + ((length Lt) - (S k))))%nat by lia.
             rewrite ! repeat_app. rewrite ! combine_cons. rewrite ! combine_app.
             setoid_rewrite cons_conc at 1. setoid_rewrite cons_conc at 7.
             rewrite ! app_assoc. apply Permutation_app_tail.
             rewrite <- ! app_assoc. apply Permutation_app_middle.
             apply Permutation_app_comm.
             auto. rewrite repeat_length. rewrite firstn_length_le; try lia.
             rewrite repeat_length. auto.
             rewrite repeat_length. rewrite firstn_length_le; try lia. }
           rewrite projectorListT_commutingListT_Permutation
             with (Lz2 := (0%F2 :: repeat 0%F2 (length Lt)))
                  (Lt2 := (t0 :: firstn k Lt ++ [t] ++ skipn (S k) Lt)); auto.
           rewrite projectorListT_cons.
           pose (projector_span_stabilized_space t0) as E.
           assert (proper_length_TType t0).
           { rewrite Forall_forall in H2. apply H2; auto. }
           assert (coef_plus_minus_1 t0).
           { rewrite Forall_forall in H3. apply H3; auto. }
           specialize (E H5 H6 H1 
                         (projectorT 0%F2 t0 × projectorListT (repeat 0%F2 (length Lt))
                            (firstn k Lt ++ [t] ++ skipn (S k) Lt) × a)).
           assert (@CM.span (2 ^ n) (2 ^ n) (projectorT 0%F2 t0)
                     (@Mmult (2 ^ n) (2 ^ n) 1%nat 
                        (@Mmult (2 ^ n) (2 ^ n) (2 ^ n) (projectorT 0%F2 t0)
                        (projectorListT (repeat 0%F2 (length Lt))
                        (firstn k Lt ++ [t] ++ skipn (S k) Lt))) a)).
           { unfold CM.span. 
             exists (@Mmult (2 ^ n) (2 ^ n) 1%nat (projectorListT (repeat 0%F2 (length Lt))
                  (firstn k Lt ++ [t] ++ skipn (S k) Lt)) a).
             split.
             assert ((@CM.WF_GenMatrix (2 ^ n) 1%nat
                       (@Mmult (2 ^ n) (2 ^ n) 1%nat (projectorListT (repeat 0%F2 (length Lt))
                          (firstn k Lt ++ [t] ++ skipn (S k) Lt)) a)) = 
                      @WF_Matrix (2 ^ n) 1%nat
                        (@Mmult (2 ^ n) (2 ^ n) 1%nat (projectorListT (repeat 0%F2 (length Lt))
                           (firstn k Lt ++ [t] ++ skipn (S k) Lt)) a)) by auto.
             rewrite H7. apply WF_mult; auto.
             apply WF_projectorListT.
             rewrite repeat_length. rewrite ! app_length.
             rewrite firstn_length_le; try lia. rewrite skipn_length. simpl. lia.
             rewrite ! Forall_app.
             rewrite (nth_inc k Lt (defaultT_I n)) in H2; auto.
             rewrite ! Forall_app in H2.
             destruct H2 as [H2 [H2' H2'']]. auto.
             assert (@CM.GMmult (2 ^ n) (2 ^ n) 1%nat (projectorT 0%F2 t0)
                       (@Mmult (2 ^ n) (2 ^ n) 1%nat (projectorListT (repeat 0%F2 (length Lt))
                          (firstn k Lt ++ [t] ++ skipn (S k) Lt)) a) =
                       Mmult (projectorT 0%F2 t0)
                       (projectorListT (repeat 0%F2 (length Lt))
                          (firstn k Lt ++ [t] ++ skipn (S k) Lt) × a)) by auto.
             rewrite H7. rewrite <- Mmult_assoc. auto. }
           rewrite E in H7.
           unfold stabilizeByListT in H7.
           destruct H7.
           assert (In t0 [t0]) by (simpl; auto).
           specialize (H8 t0 H9). auto.
           rewrite <- nth_k_Lt. rewrite <- nth_inc; auto.
           rewrite <- nth_k_Lt. rewrite <- nth_inc; auto.
           rewrite <- nth_k_Lt. rewrite <- nth_inc; auto.
           simpl. rewrite repeat_length; lia.
           simpl. f_equal.  rewrite app_length. simpl. 
           rewrite firstn_length_le; try lia.
           replace (match Lt with
             | [] => []
             | _ :: l => skipn k l
             end) with (skipn (S k) Lt) by auto.
           rewrite skipn_length. rewrite repeat_length. lia.
  - unfold stabilizeByListT in *.
    destruct H2.
    unfold CM.span.
    gen v. induction Lt; intros.
    + unfold projectorListT.
      simpl. exists v. split.
      assert (CM.WF_GenMatrix v = WF_Matrix v) by auto.
      rewrite H4; auto.
      assert (CM.GMmult (I (2 ^ n)) v = Mmult (I (2 ^ n)) v) by auto.
      rewrite H4. rewrite Mmult_1_l; auto.
    + remember H3 as H3'. clear HeqH3'.
      assert (In a (a :: Lt)) by (simpl; auto).
      specialize (H3' a H4).
      pose (projector_span_stabilized_space a) as E.
      remember commutingListTLt as commutingListTLt'. clear HeqcommutingListTLt'.
      apply commutingListT_cons in commutingListTLt'. destruct commutingListTLt'.
      remember H as H'. clear HeqH'.
      rewrite Forall_cons_iff in H'. destruct H'.
      remember H0 as H0'. clear HeqH0'.
      rewrite Forall_cons_iff in H0'. destruct H0'.
      specialize (E H7 H9 H1 v).
      assert (stabilizeByListT (fun v : Vector (2 ^ n) => WF_Matrix v) [a] v).
      { unfold stabilizeByListT. split; auto. intros t H11.
        apply H3. simpl in *. destruct H11; try contradiction. auto. }
      rewrite <- E in H11.
      unfold CM.span in H11.
      destruct H11 as [b [WFb vb]].
      assert (CM.WF_GenMatrix b = WF_Matrix b) by auto.
      rewrite H11 in WFb.
      assert (CM.GMmult (projectorT 0%F2 a) b =
                Mmult (projectorT 0%F2 a) b) by auto.
      remember vb as vb'. clear Heqvb'.
      rewrite H12 in vb, vb'.
      rewrite <- projectorT_idempotent in vb; auto.
      rewrite Mmult_assoc in vb.
      rewrite <- vb' in vb.
      assert (forall t : TType n, In t Lt -> translate t × v = v).
      { intros t H13. apply H3; simpl; auto. }
      specialize (IHLt H6 H8 H10 v H2 H13).
      destruct IHLt as [u [WFu vu]].
      exists u. split; auto.
      assert (CM.GMmult (projectorListT (repeat 0%F2 (length (a :: Lt))) (a :: Lt)) u = 
                Mmult (projectorListT (repeat 0%F2 (length (a :: Lt))) (a :: Lt)) u) by auto.
      rewrite H14.
      simpl. rewrite projectorListT_cons. 
      assert (CM.GMmult (projectorListT (repeat 0%F2 (length Lt)) Lt) u =
                Mmult (projectorListT (repeat 0%F2 (length Lt)) Lt) u) by auto.
      rewrite H15 in vu.
      rewrite Mmult_assoc.
      rewrite <- vu; auto.
Qed.

Lemma anticommute_T_flipF2_projectorT : forall {n : nat} (z : F2) (t t' : TType n),
    proper_length_TType t -> proper_length_TType t' ->
    coef_plus_minus_1 t -> anticommute_T t t' ->
    (translate t) × (projectorT z t') × (translate t)† = projectorT (z+1)%F2 t'.
Proof. intros n z t t' H H0 H1 H2.
  unfold projectorT.
  rewrite translate_adjoint_eq; auto.
  apply anticommute_T_translate_anticomm in H2; auto.
  distribute_scale. f_equal.
  distribute_plus. distribute_scale. rewrite H2. distribute_scale.
  rewrite <- translate_defaultT_I_comm; auto.
  rewrite ! Mmult_assoc. rewrite ! translate_mult_inv; auto.
  rewrite ! Mmult_1_r. f_equal. f_equal.
  unfold neg_powF2. destruct z; simpl; lca.
  apply WF_translate; auto.
  apply WF_translate. apply proper_length_TType_defaultT_I.
  destruct H; auto.
Qed.

Lemma commute_T_projectorT_commute : forall {n : nat} (z : F2) (t t' : TType n),
    proper_length_TType t -> proper_length_TType t' -> commute_T t t' ->
    (translate t) × (projectorT z t') = (projectorT z t') × (translate t).
Proof. intros n z t t' H H0 H1.
  unfold projectorT.
  apply commute_T_translate_comm in H1; auto.
  distribute_scale. f_equal.
  distribute_plus. distribute_scale. rewrite H1.
  rewrite <- translate_defaultT_I_comm; auto.
Qed.

Lemma commute_T_commute_projectorListT : 
  forall {n : nat} (t : TType n) (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> (forall t' : TType n, In t' Lt -> commute_T t t') ->
    Forall proper_length_TType Lt ->
    proper_length_TType t -> coef_plus_minus_1 t ->
    (forall j : nat, (j < length Lt)%nat -> commute_T (nth j Lt (defaultT_I n)) t) ->
    (translate t) × (projectorListT Lz Lt) = (projectorListT Lz Lt) × (translate t).
Proof. intros n t Lz Lt H H0 H1 H2 H3.
  gen Lz. induction Lt; intros.
  - destruct Lz; try discriminate. unfold projectorListT, projectorT. simpl.
    rewrite Mmult_1_l, Mmult_1_r; auto.
    all : apply WF_translate; auto.
  - destruct Lz; try discriminate. simpl in H.
    apply Nat.succ_inj in H.
    rewrite projectorListT_cons.
    remember H0 as H0'. clear HeqH0'.
    assert (In a (a :: Lt)) by (simpl; auto).
    specialize (H0' a H5).
    remember H1 as H1'. clear HeqH1'.
    rewrite Forall_cons_iff in H1'. destruct H1'.
    apply commute_T_translate_comm in H0'; auto.
    rewrite <- Mmult_assoc.
    rewrite commute_T_projectorT_commute; auto.
    rewrite ! Mmult_assoc. f_equal.
    apply IHLt; auto.
    + intros t' H8. apply H0. simpl; auto.
    + intros j H8. assert (S j < length (a :: Lt))%nat by (simpl; lia).
      specialize (H4 (S j) H9). simpl in H4. auto.
Qed.

Lemma exists_commute_anticommute_T_flip_nthF2_projectorListT : 
  forall {n : nat} (k : nat) (Lz : list F2) (Lt : list (TType n)),
    (k < length Lt)%nat -> length Lz = length Lt -> Forall proper_length_TType Lt ->
(forall i : nat, (i < length Lt)%nat -> (exists t : TType n, proper_length_TType t /\
       coef_plus_minus_1 t /\ anticommute_T (nth i Lt (defaultT_I n)) t /\
       (forall j : nat, (j < length Lt)%nat -> j <> i -> commute_T (nth j Lt (defaultT_I n)) t))) ->
(exists t : TType n,
    proper_length_TType t /\
      coef_plus_minus_1 t /\ anticommute_T (nth k Lt (defaultT_I n)) t /\
      (forall j : nat, (j < length Lt)%nat -> j <> k -> commute_T (nth j Lt (defaultT_I n)) t) /\
    projectorListT (firstn k Lz) (firstn k Lt)
    × (projectorT (nth k Lz 0 + 1)%F2 (nth k Lt (defaultT_I n))
       × projectorListT (skipn (S k) Lz) (skipn (S k) Lt)) =
    translate t
    × (projectorListT (firstn k Lz) (firstn k Lt)
       × (projectorT (nth k Lz 0%F2) (nth k Lt (defaultT_I n))
          × projectorListT (skipn (S k) Lz) (skipn (S k) Lt))) × 
    (translate t)†).
Proof. intros n k Lz Lt H H0 H1 H2. 
  destruct  (H2 k H) as [t [pltT [coefT [anticommT commT]]]].
  exists t. rewrite translate_adjoint_eq; auto.
  repeat (split; auto).
  rewrite ! Mmult_assoc.
  rewrite <- commute_T_commute_projectorListT; auto.
  rewrite <- ! Mmult_assoc.
  rewrite commute_T_commute_projectorListT; auto.
  assert (projectorListT (firstn k Lz) (firstn k Lt) × translate t
  × projectorT (nth k Lz 0%F2) (nth k Lt (defaultT_I n)) × 
  translate t × projectorListT (skipn (S k) Lz) (skipn (S k) Lt) = 
            projectorListT (firstn k Lz) (firstn k Lt) × (translate t
              × projectorT (nth k Lz 0%F2) (nth k Lt (defaultT_I n)) × 
              translate t) × projectorListT (skipn (S k) Lz) (skipn (S k) Lt)).
  { rewrite ! Mmult_assoc. auto. }
  rewrite H3.
  rewrite <- translate_adjoint_eq at 2; auto.
  rewrite anticommute_T_flipF2_projectorT; auto.
  - apply Forall_nth; auto.
  - apply anticommute_T_swap. auto.
  - rewrite ! firstn_length_le; auto; lia.
  - intros t' H3.  apply In_nth with (d := defaultT_I n) in H3.
    destruct H3 as [j [jbound nthj]].
    rewrite <- nthj.
    rewrite firstn_length in jbound. rewrite nth_firstn; try lia.
    apply commute_T_swap. apply commT; lia.
  - rewrite <- (firstn_skipn k Lt) in H1.
    rewrite Forall_app in H1. destruct H1. auto.
  - intros j H3. rewrite firstn_length in H3.
    rewrite nth_firstn with (d := defaultT_I n); try lia.
    apply commT; try lia.
  - rewrite ! skipn_length. rewrite H0. auto.
  - intros t' H3. apply In_nth with (d := defaultT_I n) in H3.
    destruct H3 as [j [jbound nthj]].
    rewrite nth_skipn in nthj. rewrite <- nthj.
    apply commute_T_swap. 
    rewrite skipn_length in jbound. apply commT; lia.
  - rewrite <- (firstn_skipn (S k) Lt) in H1.
    rewrite Forall_app in H1. destruct H1. auto.
  - intros j H3. rewrite ! skipn_length in H3. 
    rewrite nth_skipn. apply commT; lia.
Qed.

Lemma flip_nthF2_projectorListT : forall {n : nat} (Lz : list F2) (Lt : list (TType n)) (k : nat),
  linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat -> Lt <> [] ->
  length Lz = length Lt -> Forall proper_length_TType Lt -> (k < length Lt)%nat -> 
  exists t : TType n, 
    proper_length_TType t /\
      coef_plus_minus_1 t /\ anticommute_T (nth k Lt (defaultT_I n)) t /\
      (forall j : nat, (j < length Lt)%nat -> j <> k -> commute_T (nth j Lt (defaultT_I n)) t) /\
    projectorListT (firstn k Lz ++ [((nth k Lz zero) + 1)%F2] ++ skipn (S k) Lz) Lt = 
      (translate t) × (projectorListT Lz Lt) × (translate t)†.
Proof. intros n Lz Lt k H H0 H1 H2 H3 H4. 
  setoid_rewrite (nth_inc k Lt (defaultT_I n)) at 4.
  setoid_rewrite (nth_inc k Lt (defaultT_I n)) at 7.
  setoid_rewrite (nth_inc k Lz zero) at 4.
  rewrite ! projectorListT_app.
  rewrite ! projectorListT_singleton.
  apply exists_commute_anticommute_T_flip_nthF2_projectorListT; auto.
  - apply exists_commute_anticommute_T; auto.
  - apply Forall_nth; auto.
  - apply Forall_nth; auto.
  - auto.
  - rewrite ! skipn_length. rewrite H2. auto.
  - rewrite <- (firstn_skipn (S k) Lt) in H3.
    rewrite Forall_app in H3. destruct H3. auto.
  - rewrite ! firstn_length. rewrite H2. auto.
  - rewrite ! app_length, ! skipn_length, H2. auto.
  - rewrite Forall_app. split.
    + constructor. rewrite Forall_nth in H3. apply H3; auto. constructor.
    + rewrite <- (firstn_skipn (S k) Lt) in H3.
      rewrite Forall_app in H3. destruct H3. auto.
  - auto.
  - rewrite ! skipn_length. rewrite H2. auto.
  - rewrite <- (firstn_skipn (S k) Lt) in H3.
    rewrite Forall_app in H3. destruct H3. auto.
  - rewrite ! firstn_length. rewrite H2. auto.
  - rewrite ! app_length, ! skipn_length, H2. auto.
  - rewrite Forall_app. split.
    + constructor. rewrite Forall_nth in H3. apply H3; auto. constructor.
    + rewrite <- (firstn_skipn (S k) Lt) in H3.
      rewrite Forall_app in H3. destruct H3. auto.
  - rewrite H2. auto.
  - auto.
  - auto.
Qed.

Lemma set_nthF2_projectorListT : forall {n : nat} (Lz : list F2) (Lt : list (TType n)) (k : nat) (z : F2),
  linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat -> Lt <> [] ->
  length Lz = length Lt -> Forall proper_length_TType Lt -> (k < length Lt)%nat -> 
  exists t : TType n, 
    proper_length_TType t /\
      coef_plus_minus_1 t /\ 
      (forall j : nat, (j < length Lt)%nat -> j <> k -> commute_T (nth j Lt (defaultT_I n)) t) /\
    projectorListT (firstn k Lz ++ [z] ++ skipn (S k) Lz) Lt = 
      (translate t) × (projectorListT Lz Lt) × (translate t)†.
Proof. intros n Lz Lt k z H H0 H1 H2 H3 H4.
  destruct (F2eq_dec z (nth k Lz zero)) as [e | e].
  - rewrite e. rewrite <- nth_inc. exists (defaultT_I n).
    split; [idtac | split; [idtac | split]].
    + apply proper_length_TType_defaultT_I; auto.
    + apply coef_plus_minus_1_defaultT_I.
    + intros j H5 H6. apply commute_T_defaultT_I.
      apply Forall_nth; auto.
    + rewrite translate_defaultT_I.
      rewrite id_adjoint_eq.
      rewrite Mmult_1_l, Mmult_1_r; auto.
      all: apply WF_projectorListT; auto.
    + rewrite H2. auto.
  - assert (z = (nth k Lz 0) + 1)%F2.
    { destruct z, (nth k Lz 0%F2); auto; contradiction. }
    rewrite H5.
    destruct (flip_nthF2_projectorListT Lz Lt k H H0 H1 H2 H3 H4)
      as [t [H6 [H7 [H8 [H9 H10]]]]].
    exists t. auto.
Qed.

Lemma set_listF2_projectorListT_firstn : forall {n : nat} (Lz : list F2) (Lt : list (TType n)) (k : nat),
  linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat -> Lt <> [] ->
  length Lz = length Lt -> Forall proper_length_TType Lt -> 
  exists t : TType n, proper_length_TType t /\ coef_size_1 t /\
    (projectorListT ((firstn k Lz) ++ (repeat zero ((length Lt) - k)%nat)) Lt) = 
      (translate t) × (projectorListT (repeat zero (length Lt)) Lt) × (translate t)†.
Proof. intros n Lz Lt k H H0 H1 H2 H3. 
  induction k.
  - simpl. rewrite Nat.sub_0_r.
    exists (defaultT_I n). 
    rewrite translate_defaultT_I.
    rewrite id_adjoint_eq.
    rewrite Mmult_1_l, Mmult_1_r; auto.
    all: try apply WF_projectorListT; try rewrite repeat_length; auto.
    split; auto. apply proper_length_TType_defaultT_I; auto.
    split; auto. apply coef_size_1_defaultT_I.
  - destruct IHk as [t [proper_len_t [coef_size_1_t H4]]].
    bdestruct (k <? length Lt).
    + assert (length (firstn k Lz ++ repeat 0%F2 (length Lt - k)) = length Lt).
      { rewrite app_length, firstn_length, repeat_length, H2. minmax_breakdown. lia. }
      destruct (set_nthF2_projectorListT (firstn k Lz ++ repeat 0%F2 (length Lt - k)) Lt k (nth k Lz zero) H H0 H1 H6 H3 H5)
        as [t0 [H7 [H8 [H9 H10]]]].
      assert (firstn k (firstn k Lz ++ repeat 0%F2 (length Lt - k)) ++
           [nth k Lz 0%F2] ++
           skipn (S k) (firstn k Lz ++ repeat 0%F2 (length Lt - k)) = 
                firstn (S k) Lz ++ repeat 0%F2 (length Lt - (S k))).
      { rewrite firstn_app. rewrite skipn_app. rewrite skipn_firstn_comm.
        rewrite firstn_length. minmax_breakdown.
        replace (k - k)%nat with 0%nat by lia.
        replace (k - S k)%nat with 0%nat by lia. 
        replace (S k - k)%nat with 1%nat by lia. 
        replace (length Lt - k)%nat with (1%nat + (length Lt - S k))%nat by lia.
        simpl. rewrite app_nil_r. rewrite cons_conc. rewrite app_assoc. f_equal.
        rewrite firstn_firstn. minmax_breakdown.
        replace (match Lz with
                 | [] => []
                 | a :: l => a :: firstn k l
                 end) with (firstn (S k) Lz) by (simpl; auto).
        apply firstn_last_nth_app; lia. }
      rewrite H11 in H10.
      exists (gMulT t0 t).
      rewrite ! translate_gMulT_mult; auto.
      rewrite Mmult_adjoint.
      assert (translate t0 × translate t × projectorListT (repeat 0%F2 (length Lt)) Lt
                × (adjoint (translate t) × adjoint (translate t0)) = 
                translate t0 × (translate t × projectorListT (repeat 0%F2 (length Lt)) Lt
                  × adjoint (translate t)) × adjoint (translate t0)).
      { rewrite ! Mmult_assoc. auto. }
      rewrite H12.
      rewrite <- H4. rewrite <- H10.
      split; auto. apply proper_length_TType_gMulT; auto.
      split; auto. apply coef_size_1_gMultT_preserve; auto.
      apply coef_plus_minus_1_implies_coef_size_1; auto.
    + exists t. rewrite ! firstn_all2; try lia. rewrite <- H4. 
      rewrite firstn_all2; try lia.
      replace (length Lt - S k)%nat with 0%nat by lia.
      replace (length Lt - k)%nat with 0%nat by lia.
      split; auto.
Qed.

Lemma set_listF2_projectorListT : forall {n : nat} (Lz : list F2) (Lt : list (TType n)),
  linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat -> Lt <> [] ->
  length Lz = length Lt -> Forall proper_length_TType Lt -> 
  exists t : TType n, proper_length_TType t /\ coef_size_1 t /\
    (projectorListT Lz Lt) = 
      (translate t) × (projectorListT (repeat zero (length Lt)) Lt) × (translate t)†.
Proof. intros n Lz Lt H H0 H1 H2 H3.
  destruct (set_listF2_projectorListT_firstn Lz Lt (length Lz) H H0 H1 H2 H3)
    as [t [proper_len_t H4]].
  rewrite firstn_all in H4. rewrite H2 in H4.
  replace (length Lt - length Lt)%nat with 0%nat in H4 by lia. simpl in H4.
  rewrite app_nil_r in H4.
  exists t. split; auto.
Qed.

Lemma projectorListT_equal_rank : forall {n : nat} (d : nat) (Lz : list F2) (Lt : list (TType n)),
  linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat -> Lt <> [] ->
  length Lz = length Lt -> Forall proper_length_TType Lt -> 
    @CM.rank (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz Lt) d <->
      @CM.rank (2 ^ n)%nat (2 ^ n)%nat (projectorListT (repeat zero (length Lt)) Lt) d.
Proof. intros. unfold CM.rank. split; intros.
  - constructor.
    inversion H4; clear H4.
    destruct (set_listF2_projectorListT Lz Lt H H0 H1 H2 H3)
      as [t [proper_len_t [coef_size_1_t H4]]].
    rewrite H4 in H5.
    rewrite @CM.swap_equivalent_subspace_in_dimension
      with (P2 := @CM.span (2 ^ n)%nat (2 ^ n)%nat 
                   (translate t × projectorListT (repeat 0%F2 (length Lt)) Lt)) in H5; auto.
    2: { intros v. symmetry. apply CM.invertible_right_mult_span_preserve.
         apply WF_adjoint. apply WF_translate; auto. 
         apply translate_adjoint_invertible; auto. }
    rewrite <- CM.invertible_left_mult_dim_preserve in H5; auto.
    apply WF_translate; auto.
    apply WF_projectorListT; auto. rewrite repeat_length; auto.
    apply translate_invertible; auto.
  - constructor.
    inversion H4; clear H4.
    destruct (set_listF2_projectorListT Lz Lt H H0 H1 H2 H3)
      as [t [proper_len_t [coef_size_1_t H4]]].
    rewrite H4.
    rewrite @CM.swap_equivalent_subspace_in_dimension
      with (P2 := @CM.span (2 ^ n)%nat (2 ^ n)%nat 
                   (translate t × projectorListT (repeat 0%F2 (length Lt)) Lt)); auto.
    2: { intros v. symmetry. apply CM.invertible_right_mult_span_preserve.
         apply WF_adjoint. apply WF_translate; auto. 
         apply translate_adjoint_invertible; auto. }
    rewrite <- CM.invertible_left_mult_dim_preserve; auto.
    apply WF_translate; auto.
    apply WF_projectorListT; auto. rewrite repeat_length; auto.
    apply translate_invertible; auto.
Qed.

(** orthogonal subspaces **)
Inductive orthogonal_subspaces {n : nat} (P1 P2 : Vector n -> Prop) :=
| OrthSubspace : @CM.subspace n P1 -> @CM.subspace n P2 ->
                 (forall u v : Vector n, P1 u -> P2 v -> ((u †) × v) 0%nat 0%nat = C0) ->
                 orthogonal_subspaces P1 P2.

Lemma orthogonal_subspaces_sym : forall {n : nat} (P1 P2 : Vector n -> Prop),
    orthogonal_subspaces P1 P2 -> orthogonal_subspaces P2 P1.
Proof. intros n P1 P2 H.
  inversion H. constructor; auto.
  intros u v H3 H4.
  specialize (H2 v u H4 H3).
  unfold Mmult, adjoint in *.
  assert ((Σ (fun y : nat => (v y 0%nat) ^* * u y 0%nat) n)^* = C0).
  { rewrite H2. lca. }
  rewrite big_sum_func_distr in H5. 
  2: intros; lca.
  rewrite <- H5.
  apply big_sum_eq_bounded.
  intros x H6. lca.
Qed.

Lemma differentF2_projectorT_orth : forall {n : nat} (z1 z2 : F2) (t : TType n),
    z1 <> z2 -> coef_plus_minus_1 t -> proper_length_TType t ->
    adjoint (projectorT z1 t) × (projectorT z2 t) = Zero.
Proof. intros n z1 z2 t H H0 H1.
  unfold projectorT.
  distribute_adjoint.
  distribute_scale.
  distribute_plus.
  rewrite ! translate_defaultT_I.
  rewrite id_adjoint_eq.
  rewrite ! Mmult_1_l, ! Mmult_1_r.
  distribute_scale.
  rewrite translate_adjoint_mult_inv.
  assert ((neg_powF2 z1) ^* * neg_powF2 z2 = (- C1)%C).
  { destruct z1, z2; try contradiction; unfold neg_powF2; simpl; lca. }
  rewrite H2.
  assert ((neg_powF2 z1) ^* = - (neg_powF2 z2))%C.
  { destruct z1, z2; try contradiction; unfold neg_powF2; simpl; lca. }
  rewrite H3. 
  assert ((I (2 ^ n) .+ - neg_powF2 z2 .* adjoint (translate t)
      .+ (neg_powF2 z2 .* translate t .+ - C1 .* I (2 ^ n))) = Zero).
  { rewrite translate_adjoint_eq; auto. lma'. }
  rewrite H4. lma'.
  all: auto with wf_db.
  apply coef_plus_minus_1_implies_coef_size_1; auto.
Qed.

Lemma differentF2_projectorListT_orth : 
  forall {n : nat} (k : nat) (Lz1 Lz2 : list F2) (Lt  : list (TType n)),
    Forall coef_plus_minus_1 Lt -> Forall proper_length_TType Lt ->
    commutingListT Lt ->
    (k < length Lz1)%nat -> length Lz1 = length Lt -> length Lz2 = length Lt ->
    nth k Lz1 0%F2 <> nth k Lz2 0%F2 ->
    (adjoint (projectorListT Lz1 Lt) × projectorListT Lz2 Lt) = Zero.
Proof. intros. 
  rewrite (nth_inc k Lz1 zero); try lia.
  rewrite (nth_inc k Lz2 zero); try lia.
  rewrite (nth_inc k Lt (defaultT_I n)); try lia.
  rewrite projectorListT_commutingListT_Permutation 
    with (Lz1 := (firstn k Lz1 ++ [nth k Lz1 0%F2] ++ skipn (S k) Lz1))
         (Lt1 := (firstn k Lt ++ [nth k Lt (defaultT_I n)] ++ skipn (S k) Lt))
         (Lz2 := ([nth k Lz1 0%F2] ++ firstn k Lz1 ++ skipn (S k) Lz1))
         (Lt2 := ([nth k Lt (defaultT_I n)] ++ firstn k Lt ++ skipn (S k) Lt)); auto.
   rewrite projectorListT_commutingListT_Permutation 
    with (Lz1 := (firstn k Lz2 ++ [nth k Lz2 0%F2] ++ skipn (S k) Lz2))
         (Lt1 := (firstn k Lt ++ [nth k Lt (defaultT_I n)] ++ skipn (S k) Lt))
         (Lz2 := ([nth k Lz2 0%F2] ++ firstn k Lz2 ++ skipn (S k) Lz2))
         (Lt2 := ([nth k Lt (defaultT_I n)] ++ firstn k Lt ++ skipn (S k) Lt)); auto.
  rewrite ! projectorListT_app; try lia.
  rewrite ! projectorListT_singleton.
  distribute_adjoint.
  rewrite ! Mmult_assoc.
  assert (H' : adjoint (projectorListT (skipn (S k) Lz1) (skipn (S k) Lt))
  × (adjoint (projectorListT (firstn k Lz1) (firstn k Lt))
     × (adjoint (projectorT (nth k Lz1 0%F2) (nth k Lt (defaultT_I n)))
        × (projectorT (nth k Lz2 0%F2) (nth k Lt (defaultT_I n))
           × (projectorListT (firstn k Lz2) (firstn k Lt)
              × projectorListT (skipn (S k) Lz2) (skipn (S k) Lt))))) =
            adjoint (projectorListT (skipn (S k) Lz1) (skipn (S k) Lt))
              × (adjoint (projectorListT (firstn k Lz1) (firstn k Lt))
                   × ((adjoint (projectorT (nth k Lz1 0%F2) (nth k Lt (defaultT_I n))))
                        × (projectorT (nth k Lz2 0%F2) (nth k Lt (defaultT_I n))))
                             × (projectorListT (firstn k Lz2) (firstn k Lt)
                                  × projectorListT (skipn (S k) Lz2) (skipn (S k) Lt)))).
  { rewrite ! Mmult_assoc. auto. }
  rewrite H'.
  rewrite differentF2_projectorT_orth.
  rewrite ! Mmult_0_r, ! Mmult_0_l, ! Mmult_0_r; auto.
  all: auto.
  all: try (rewrite <- ! nth_inc; auto; lia).
  all: try rewrite ! firstn_length; try lia.
  all: try rewrite ! skipn_length; try lia.
  all: try (apply Forall_nth; auto; lia).
  all: try (try rewrite ! Forall_app; rewrite (nth_inc k Lt (defaultT_I n)) in H0; try lia;
            rewrite ! Forall_app in H0; destruct H0 as [H0 [H0' H0'']]; easy).
  all: try (rewrite ! app_length; rewrite ! firstn_length; rewrite ! skipn_length; simpl; lia).
  all: rewrite ! combine_app, ! app_assoc;
    try apply Permutation_app_tail;
    try apply Permutation_app_comm;
    simpl; try rewrite ! firstn_length; lia.
Qed. 

Lemma orthogonal_projectorListT : forall {n : nat} (Lz1 Lz2 : list F2) (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt ->
    commutingListT Lt ->
    length Lz1 = length Lt -> length Lz2 = length Lt -> Lz1 <> Lz2 ->
    @orthogonal_subspaces (2 ^ n)%nat
      (@CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz1 Lt)) 
      (@CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz2 Lt)).
Proof. intros n Lz1 Lz2 Lt H H0 H1 H2 H3 H4. 
  constructor; try apply CM.span_is_subspace;
    try apply WF_projectorListT; auto.
  intros u v H5 H6. unfold CM.span in H5, H6.
  destruct H5 as [a [WFa H5]].
  destruct H6 as [b [WFb H6]].
  assert (length Lz1 = length Lz2) by lia.
  pose (nth_ext Lz1 Lz2 zero zero H7) as e.
  rewrite <- Decidable.contrapositive in e; auto.
  2: unfold Decidable.decidable;
  destruct (list_eq_dec F2eq_dec Lz1 Lz2); auto.
  specialize (e H4).
  apply Classical_Pred_Type.not_all_ex_not in e.
  destruct e as [k e].
  apply Classical_Prop.imply_to_and in e.
  destruct e.
  assert (CM.WF_GenMatrix a = WF_Matrix a) by auto.
  rewrite H10 in WFa.
  assert (CM.WF_GenMatrix b = WF_Matrix b) by auto.
  rewrite H11 in WFb.
  assert (CM.GMmult (projectorListT Lz1 Lt) a = Mmult (projectorListT Lz1 Lt) a) by auto.
  rewrite H12 in H5.
  assert (CM.GMmult (projectorListT Lz2 Lt) b = Mmult (projectorListT Lz2 Lt) b) by auto.
  rewrite H13 in H6.
  rewrite H5, H6.
  rewrite Mmult_adjoint.
  rewrite ! Mmult_assoc.
  assert ((@Mmult 1%nat (2 ^ n) 1%nat (adjoint a) (@Mmult (2 ^ n) (2 ^ n) 1%nat (adjoint (projectorListT Lz1 Lt)) (@Mmult (2 ^ n) (2 ^ n) 1%nat (projectorListT Lz2 Lt) b))) = 
            (a) † × ((adjoint (projectorListT Lz1 Lt)) × (projectorListT Lz2 Lt)) × b).
  { rewrite ! Mmult_assoc. auto. }
  rewrite H14.
  rewrite differentF2_projectorListT_orth with (k := k); auto.
  rewrite Mmult_0_r, Mmult_0_l. auto.
Qed.


(* orthogonal subspaces implies internal direct sum *)
Lemma orthogonal_subspaces_implies_no_subspace_overlap : 
  forall {n : nat} (P1 P2 : Vector n -> Prop),
    orthogonal_subspaces P1 P2 -> @CM.no_subspace_overlap n P1 P2.
Proof. intros n P1 P2 H.
  inversion H.
  unfold CM.no_subspace_overlap.
  intros v H3 H4.
  specialize (H2 v v H3 H4).
  prep_matrix_equality.
  unfold CM.Zero.
  pose (CM.WF_subspace H0 H3) as H5.
  assert (CM.WF_GenMatrix v = WF_Matrix v) by auto.
  rewrite H6 in H5.
  bdestruct (x <? n).
  - bdestruct (y =? 0)%nat.
    subst.
    + setoid_rewrite inner_product_zero_iff_zero in H2; auto.
      rewrite H2; auto.
    + rewrite H5; auto; lia.
  - rewrite H5; auto; lia.
  Qed.


Definition multi_orthogonal_subspaces {n : nat} (Ps : list (Vector n -> Prop)) :=
  (forall i j : nat, (i < length Ps)%nat -> (j < length Ps)%nat -> i <> j ->
              orthogonal_subspaces
                (nth i Ps (fun v : Vector n => v = Zero)) 
                (nth j Ps (fun v : Vector n => v = Zero))).

Lemma multi_orthogonal_subspaces_cons :
  forall {n : nat} (P : Vector n -> Prop) (Ps : list (Vector n -> Prop)),
    multi_orthogonal_subspaces (P :: Ps) <->
      (forall i : nat, (i < length Ps)%nat -> 
                orthogonal_subspaces P (nth i Ps (fun v : Vector n => v = Zero))) /\
        multi_orthogonal_subspaces Ps.
Proof. intros n P Ps.
  unfold multi_orthogonal_subspaces in *.
  split; intros.
  - split; intros. 
    + specialize (H 0%nat (S i)).
      simpl in H. apply H; simpl; lia.
    + specialize (H (S i) (S j)).
      simpl in H. apply H; simpl; lia.
  - destruct H.
    bdestruct (i =? 0)%nat; subst.
    + replace (nth 0 (P :: Ps) (fun v : Vector n => v = Zero)) with P by auto.
      destruct j; simpl in *; try contradiction. apply H; lia.
    + bdestruct (j =? 0)%nat; subst.
      * replace (nth 0 (P :: Ps) (fun v : Vector n => v = Zero)) with P by auto.
        apply orthogonal_subspaces_sym.
        destruct i; simpl in *; try contradiction. apply H; lia.
      * destruct i, j; simpl in *; try contradiction. apply H3; lia.
Qed.

Lemma multi_orthogonal_subspaces_cons_orthogonal_subspaces_multi_subspace_sum : 
  forall {n : nat} (P : Vector n -> Prop) (Ps : list (Vector n -> Prop)),
    @CM.subspace n P -> Forall (@CM.subspace n) Ps ->
    multi_orthogonal_subspaces (P :: Ps) ->
    orthogonal_subspaces P (@CM.multi_subspace_sum n Ps).
Proof. intros n P Ps H H0 H1.
  rewrite multi_orthogonal_subspaces_cons in H1. destruct H1.
  constructor; auto.
  apply CM.multi_subspace_sum_is_subspace; auto.
  gen P. induction Ps; intros.
  - simpl in *. rewrite H4. rewrite Mmult_0_r. unfold Zero. auto.
  - rewrite Forall_cons_iff in H0. destruct H0.
    rewrite multi_orthogonal_subspaces_cons in H2. destruct H2. 
    assert (forall i : nat, (i < length Ps)%nat ->
          orthogonal_subspaces P (nth i Ps (fun v : Vector n => v = Zero))).
    { intros i H7. specialize (H1 (S i)). apply H1; simpl; lia. }
    simpl in H4.
    destruct H4 as [vh [vt [avh [Psvt vvhvt]]]].
    replace (CM.GMplus vh vt) with (@Mplus n 1 vh vt) in vvhvt by auto.
    specialize (IHPs H5 H6 P H H7 u vt H3 Psvt).
    assert (orthogonal_subspaces P a).
    { specialize (H1 0%nat). simpl in H1. apply H1; lia. }
    inversion H4.
    specialize (H10 u vh H3 avh).
    rewrite vvhvt.
    distribute_plus.
    unfold Mplus.
    rewrite H10, IHPs.
    lca.
Qed.

Lemma multi_orthogonal_subspaces_implies_multi_no_subspace_overlap :
  forall {n : nat} (Ps : list (Vector n -> Prop)),
    Forall (@CM.subspace n) Ps ->
    multi_orthogonal_subspaces Ps -> @CM.multi_no_subspace_overlap n Ps.
Proof. intros n Ps H H0. 
  induction Ps; simpl; auto.
  rewrite multi_orthogonal_subspaces_cons in H0. destruct H0.
  rewrite Forall_cons_iff in H. destruct H.
  split; auto.
  specialize (IHPs H2 H1).
  induction Ps.
  - simpl. unfold CM.no_subspace_overlap. intros; auto.
  - rewrite Forall_cons_iff in H2. destruct H2.
    rewrite multi_orthogonal_subspaces_cons in H1. destruct H1.
    simpl in IHPs. destruct IHPs.
    assert (forall i : nat, (i < length Ps)%nat ->
           orthogonal_subspaces a (nth i Ps (fun v : Vector n => v = Zero))).
    { intros i H7. specialize (H0 (S i)). apply H0; simpl; lia. }
    specialize (IHPs0 H3 H7 H4 H6).
    apply orthogonal_subspaces_implies_no_subspace_overlap.
    apply multi_orthogonal_subspaces_cons_orthogonal_subspaces_multi_subspace_sum; auto.
    rewrite ! multi_orthogonal_subspaces_cons; split; auto.
Qed.

Lemma multi_orthogonal_subspaces_projectorListT :
  forall {n : nat} (LzList : list (list F2)) (Lt : list (TType n)),
    NoDup LzList -> Forall proper_length_TType Lt -> 
    Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    Forall (fun Lz => length Lz = length Lt) LzList ->
    @multi_orthogonal_subspaces (2 ^ n)%nat
      (map (fun Lz => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz Lt)) LzList).
Proof. intros n LzList Lt H H0 H1 H2 H3.
  induction LzList; simpl; auto.
  - unfold multi_orthogonal_subspaces. intros i j H4 H5 H6. simpl in *. lia.
  - rewrite NoDup_cons_iff in H. destruct H.
    rewrite Forall_cons_iff in H3. destruct H3.
    specialize (IHLzList H4 H5).
    rewrite multi_orthogonal_subspaces_cons.
    split; intros; auto.
    rewrite nth_indep 
      with (d' := @CM.span (2^n) (2^n)  (projectorListT (repeat zero (length Lt)) Lt)); auto.
    rewrite map_nth with (d := (repeat zero (length Lt))).
    rewrite map_length in H6.
    apply orthogonal_projectorListT; auto.
    + rewrite Forall_nth in H5. apply H5. auto.
    + intro. subst. contradict H. apply nth_In. auto.
Qed.

(* https://math.stackexchange.com/questions/1227031/do-commuting-matrices-share-the-same-eigenvectors *)
Lemma nonzero_invariant_subspace_exists_eigenvector :
  forall {n : nat} (M : Square n) (P : Vector n -> Prop) (d : nat),
    WF_Matrix M ->
    @CM.subspace n P -> @CM.dimension n P d -> d <> 0%nat ->
    (forall v : Vector n, P v -> P (M × v)) ->
    exists (c : C) (v : Vector n), WF_Matrix v /\ v <> Zero /\ M × v = c .* v /\ P v.
Proof. intros n M P d H H0 H1 H2 H3.
  unfold CM.dimension in H1.
  destruct H1 as [B [WFB basisB]].
  pose (CM.subspace_is_basis_span basisB) as H1.
  assert (forall i, (i < d)%nat -> CM.span B (@CM.get_col n d (@Mmult n n d M B) i)).
  { intros i H4. 
    rewrite matrix_by_basis; auto.
    rewrite <- H1.
    rewrite Mmult_assoc.
    apply H3.
    rewrite H1.
    unfold CM.span.
    exists (@e_i d i).
    split; auto with wf_db.
    apply WF_e_i. }
  assert (@CM.WF_GenMatrix n d (@Mmult n n d M B)).
  { apply WF_mult; auto. }
  destruct (CM.collect_columns_in_span H5 WFB H4) as [A [WFA MBBA]].
  replace (CM.GMmult B A) with (@Mmult n d d B A) in MBBA by auto.
  replace (CM.WF_GenMatrix A) with (@WF_Matrix d d A) in WFA by auto.
  destruct d; try contradiction.
  destruct (exists_eigenvector d A WFA) as [c [v [WFv [v_nonzero cv_eigenpair]]]].
  exists c. exists (B × v). repeat split; auto with wf_db.
  - intro. contradict v_nonzero.
    unfold CM.basis in basisB. destruct basisB as [H' [H'' [H''' H'''']]].
    unfold CM.linearly_independent in H''''.
    apply H''''; auto with wf_db.
  - rewrite <- Mmult_assoc, MBBA, Mmult_assoc, cv_eigenpair.
    distribute_scale. auto.
  - rewrite H1.
    unfold CM.span.
    exists v. split; auto with wf_db.
Qed.

(* https://math.stackexchange.com/questions/2025842/common-eigenvectors-of-commuting-operators *)
Lemma Hermitian_commutative_exists_common_eigenvector : 
  forall {n : nat} (A B : Square (S n)),
    WF_Matrix A -> WF_Matrix B ->
    A = A † -> B = B † -> A × B = B × A -> 
    exists (c1 c2 : C) (v : Vector (S n)), WF_Matrix v /\ v <> Zero /\ A × v = c1 .* v /\ B × v = c2 .* v.
Proof. intros n A B H H0 H1 H2 H3.
  destruct (exists_eigenvector n A H) as [c [v [WFv [v_nonzero cv_eigenpair]]]].
  assert (@CM.subspace (S n) (fun v : Vector (S n) => WF_Matrix v /\ A × v = c .* v)).
  { unfold CM.subspace. repeat split; intros.
    - destruct H4; auto.
    - rewrite Mmult_0_r. rewrite Mscale_0_r. auto.
    - destruct H4, H5. auto with wf_db.
    - replace (CM.GMplus v0 w) with (@Mplus (S n) 1 v0 w) by auto.
      distribute_plus. destruct H4, H5.
      rewrite H6, H7. rewrite Mscale_plus_distr_r. auto.
    - destruct H4. auto with wf_db.
    - replace (CM.scale c0 v0) with (@Matrix.scale (S n) 1 c0 v0) by auto.
      destruct H4. distribute_scale. rewrite H5. lma'. }
  destruct (CM.exists_dimension H4) as [d [dimd dbound]].
  destruct d.
  - unfold CM.dimension in dimd.
    destruct dimd as [M [WFM basisM]].
    assert (M = @Zero (S n) 0).
    { prep_matrix_equality. rewrite WFM; auto; lia. }
    pose (CM.subspace_is_basis_span basisM) as H6.
    assert (CM.span M v).
    { rewrite <- H6. split; auto. }
    rewrite H5 in H7.
    unfold CM.span in H7.
    destruct H7 as [a [WFa vZero]].
    rewrite Mmult_0_l in vZero.
    contradiction.
  - assert (forall v : Vector n, (fun v : Vector (S n) => WF_Matrix v /\ A × v = c .* v) v -> 
                            (fun v : Vector (S n) => WF_Matrix v /\ A × v = c .* v) (B × v)).
    { intros v0 H5. destruct H5. split; auto with wf_db.
      rewrite <- Mmult_assoc, H3, Mmult_assoc, H6.
      distribute_scale. auto. }
    assert (S d <> 0%nat) by lia.
    destruct (nonzero_invariant_subspace_exists_eigenvector
                B (fun v : Vector (S n) => WF_Matrix v /\ A × v = c .* v) (S d)
                H0 H4 dimd H6 H5) as [c' [v' [WFv' [v'_nonzero [eigenpair in_subspace]]]]].
    destruct in_subspace.
    exists c. exists c'. exists v'. repeat split; auto.
Qed.

Lemma projectorT_Hermitian : forall {n : nat} (z : F2) (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t ->
    adjoint (projectorT z t) = projectorT z t.
Proof. intros n z t H H0.
  unfold projectorT.
  distribute_adjoint.
  rewrite ! Mscale_plus_distr_r. 
  rewrite ! translate_defaultT_I.
  rewrite id_adjoint_eq.
  assert ((C1 / C2) ^* = (C1 / C2)) by lca.
  rewrite ! H1. do 2 f_equal.
  assert ((neg_powF2 z) ^* = (neg_powF2 z)).
  { destruct z; unfold neg_powF2; simpl; lca. }
  rewrite ! H2. f_equal.
  apply translate_Hermitian; auto.
Qed.

Lemma projectorT_projectorListT_comm : 
  forall {n : nat} (z : F2) (t : TType n) (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> Forall proper_length_TType Lt -> proper_length_TType t ->
    Forall coef_plus_minus_1 Lt -> coef_plus_minus_1 t -> commutingListT (t :: Lt) ->
    projectorT z t × projectorListT Lz Lt = projectorListT Lz Lt × projectorT z t.
Proof. intros n z t Lz Lt H H0 H1 H2 H3 H4.
  gen Lz. induction Lt; intros.
  - destruct Lz; try discriminate.
    unfold projectorListT. simpl. 
    rewrite Mmult_1_l, Mmult_1_r; auto; apply WF_projectorT; auto.
  - destruct Lz; try discriminate.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H2. destruct H2.
    apply commutingListT_cons in H4. destruct H4.
    apply commutingListT_cons in H7. destruct H7.
    assert (forall t' : TType n, In t' Lt -> commute_T t t').
    { intros t' H9. apply H4. simpl. auto. } 
    assert (commutingListT (t :: Lt)).
    { rewrite commutingListT_cons_iff; auto. }
    inversion H.
    specialize (IHLt H5 H6 H10 Lz H12).
    rewrite projectorListT_cons.
    rewrite Mmult_assoc.
    rewrite <- IHLt.
    rewrite <- ! Mmult_assoc.
    f_equal. apply projectorT_comm; auto.
    apply H4. simpl. auto.
Qed.

Lemma projectorListT_Hermitian : forall {n : nat} (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> Forall proper_length_TType Lt -> 
    Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    adjoint (projectorListT Lz Lt) = projectorListT Lz Lt.
Proof. intros n Lz Lt H H0 H1 H2.
  gen Lz. induction Lt; intros.
  - destruct Lz; try discriminate.
    unfold projectorListT. simpl.
    rewrite id_adjoint_eq. auto.
  - destruct Lz; try discriminate.
    rewrite projectorListT_cons.
    distribute_adjoint.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H1. destruct H1.
    remember H2 as H2'. clear HeqH2'.
    apply commutingListT_cons in H2. destruct H2.
    rewrite projectorT_Hermitian; auto.
    rewrite projectorT_projectorListT_comm; auto.
    f_equal.
    apply IHLt; auto.
Qed.

Lemma adjoint_projectorListT_projectorListT : forall {n : nat} (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> Forall proper_length_TType Lt -> 
    Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    (adjoint (projectorListT Lz Lt) × projectorListT Lz Lt) = projectorListT Lz Lt.
Proof. intros n Lz Lt H H0 H1 H2.
  gen Lz. induction Lt; intros.
  - simpl in *. apply length_zero_iff_nil in H. subst.
    unfold projectorListT. simpl. rewrite id_adjoint_eq. rewrite Mmult_1_r; auto; apply WF_I.
  - destruct Lz; try discriminate.
    rewrite projectorListT_cons.
    distribute_adjoint.
    rewrite ! Mmult_assoc.
    assert (adjoint (projectorListT Lz Lt) × (adjoint (projectorT f a) 
                        × (projectorT f a × projectorListT Lz Lt)) =
           adjoint (projectorListT Lz Lt) × (adjoint (projectorT f a) 
                        × (projectorT f a)) × projectorListT Lz Lt)
             by (rewrite ! Mmult_assoc; auto).
    rewrite H3.
    rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H1. destruct H1.
    remember H2 as H2'. clear HeqH2'.
    apply commutingListT_cons in H2. destruct H2.
    inversion H.
    rewrite projectorT_Hermitian; auto.
    rewrite projectorT_idempotent; auto.
    rewrite Mmult_assoc.
    rewrite ! projectorT_projectorListT_comm; auto.
    rewrite <- Mmult_assoc.
    f_equal.
    apply IHLt; auto.
Qed.

Lemma projectorListT_idempotent : forall {n : nat} (Lz : list F2) (Lt : list (TType n)),
    length Lz = length Lt -> Forall proper_length_TType Lt -> 
    Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    projectorListT Lz Lt × projectorListT Lz Lt = projectorListT Lz Lt.
Proof. intros n Lz Lt H H0 H1 H2.
  rewrite <- projectorListT_Hermitian at 1; auto.
  apply adjoint_projectorListT_projectorListT; auto.
Qed.


Lemma multi_no_subspace_overlap_projectorListT :
  forall {n : nat} (LzList : list (list F2)) (Lt : list (TType n)),
    NoDup LzList -> Forall proper_length_TType Lt -> 
    Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    Forall (fun Lz => length Lz = length Lt) LzList ->
    @CM.multi_no_subspace_overlap (2 ^ n)%nat
      (map (fun Lz => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz Lt)) LzList).
Proof. intros n LzList Lt H H0 H1 H2 H3.
  apply multi_orthogonal_subspaces_implies_multi_no_subspace_overlap.
  - rewrite Forall_forall. intros x H4.
    apply In_nth 
      with (d := @CM.span (2^n) (2^n) (projectorListT (repeat zero (length Lt)) Lt)) in H4.
    destruct H4 as [k [kbound kth]]. subst. rewrite map_nth with (d := repeat zero (length Lt)).
    apply CM.span_is_subspace.
    apply WF_projectorListT; auto.
    rewrite Forall_nth in H3. apply H3. rewrite map_length in kbound. auto.
  - apply multi_orthogonal_subspaces_projectorListT; auto.
Qed.


Lemma projectorT_F2_sum : forall {n : nat} (t : TType n),
    proper_length_TType t ->
    projectorT 0%F2 t .+ projectorT 1%F2 t = I (2 ^ n)%nat.
Proof. intros n t H.
  unfold projectorT.
  unfold neg_powF2.
  rewrite ! translate_defaultT_I.
  lma'. 
  apply WF_plus; apply WF_scale; 
    apply WF_plus; auto with wf_db.
Qed.

Lemma projectorListT_split_F2 : forall {n : nat} (t : TType n) (Lz : list F2) (Lt : list (TType n)),
  proper_length_TType t -> length Lz = length Lt -> Forall proper_length_TType Lt ->
  projectorListT Lz Lt = 
    projectorListT (0%F2 :: Lz) (t :: Lt) .+ projectorListT (1%F2 :: Lz) (t :: Lt).
Proof. intros n t Lz Lt H H0 H1.
  rewrite ! projectorListT_cons.
  assert (projectorT 0%F2 t × projectorListT Lz Lt
            .+ projectorT 1%F2 t × projectorListT Lz Lt = 
            (projectorT 0%F2 t .+ projectorT 1%F2 t  ) × projectorListT Lz Lt).
  { distribute_plus. auto. }
  rewrite H2.
  rewrite projectorT_F2_sum; auto.
  rewrite Mmult_1_l; auto.
  apply WF_projectorListT; auto.
Qed.

Fixpoint F2ListList (n : nat) : list (list F2) :=
  match n with
  | 0%nat => [[]]
  | S n' => (map (cons 0%F2) (F2ListList n')) ++ (map (cons 1%F2) (F2ListList n'))
  end.

Lemma F2ListList_length : forall (n : nat),
    length (F2ListList n) = (2 ^ n)%nat.
Proof. intros n.
  induction n; auto.
  simpl. rewrite app_length, ! map_length, IHn; lia.
Qed.

Lemma Forall_length_F2ListList : forall (n : nat),
    Forall (fun Lz : list F2 => length Lz = n) (F2ListList n).
Proof. intros n.
  induction n; simpl.
  - constructor; auto.
  - rewrite Forall_app. rewrite ! Forall_forall. split.
    + intros Lz H.
      rewrite in_map_iff in H.
      destruct H as [Lz' [eqLz In_x]].
      subst. simpl.
      apply In_nth with (d := repeat zero n) in In_x.
      destruct In_x as [k [kbound kth]].
      rewrite <- kth.
      f_equal.
      rewrite Forall_nth in IHn.
      apply IHn. auto.
    + intros Lz H.
      rewrite in_map_iff in H.
      destruct H as [Lz' [eqLz In_x]].
      subst. simpl.
      apply In_nth with (d := repeat zero n) in In_x.
      destruct In_x as [k [kbound kth]].
      rewrite <- kth.
      f_equal.
      rewrite Forall_nth in IHn.
      apply IHn. auto.
Qed.

Lemma NoDup_F2ListList : forall (n : nat), NoDup (F2ListList n).
Proof. intros n.
  induction n.
  - simpl. constructor; auto. constructor.
  - simpl. rewrite NoDup_nth with (d := zero :: (repeat zero (2 ^ n)%nat)).
    intros i j H H0 H1.
    rewrite app_length in H, H0.
    rewrite ! map_length in H, H0.
    rewrite ! F2ListList_length in H, H0.
    bdestruct (i <? 2 ^ n)%nat; bdestruct (j <? 2 ^ n)%nat.
    + rewrite app_nth1 in H1 at 1. rewrite app_nth1 in H1 at 1.
      rewrite ! map_nth in H1.
      inversion H1.
      rewrite NoDup_nth in IHn.
      Unshelve.
      4: apply (repeat zero (2 ^ n)%nat).
      apply IHn; auto.
      all: try rewrite ! map_length;
        try rewrite ! F2ListList_length; 
        lia.
    + rewrite app_nth1 in H1 at 1. rewrite app_nth2 in H1 at 1.
      rewrite (nth_indep (map (cons 1%F2) (F2ListList n)) 
                 (0%F2 :: repeat 0%F2 (2 ^ n))
                 (1%F2 :: repeat 1%F2 (2 ^ n))) in H1.
      rewrite ! map_nth in H1.
      inversion H1.
      all:  try rewrite ! map_length;
        try rewrite ! F2ListList_length; 
        lia.
    + rewrite app_nth2 in H1 at 1. rewrite app_nth1 in H1 at 1.
      rewrite (nth_indep (map (cons 1%F2) (F2ListList n)) 
                 (0%F2 :: repeat 0%F2 (2 ^ n))
                 (1%F2 :: repeat 1%F2 (2 ^ n))) in H1.
      rewrite ! map_nth in H1.
      inversion H1.
      all:  try rewrite ! map_length;
        try rewrite ! F2ListList_length; 
        lia.
    + rewrite app_nth2 in H1 at 1. rewrite app_nth2 in H1 at 1.
      rewrite ! (nth_indep (map (cons 1%F2) (F2ListList n)) 
                 (0%F2 :: repeat 0%F2 (2 ^ n))
                 (1%F2 :: repeat 1%F2 (2 ^ n))) in H1.
      rewrite ! map_nth in H1.
      inversion H1.
      rewrite NoDup_nth in IHn.
      Unshelve.
      6: apply (repeat one (2 ^ n)%nat).
      assert (i - 2 ^ n  = j - 2 ^ n)%nat.
      apply IHn; auto.
      all: try rewrite ! map_length in *;
        try rewrite ! F2ListList_length in *; 
        try lia; auto.
Qed.


Lemma fold_right_Mplus_map_projectorListT_F2ListList :
  forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt ->
    fold_right Mplus Zero (map (fun Lz : list F2 => projectorListT Lz Lt) (F2ListList (length Lt))) 
    = I (2 ^ n)%nat.
Proof. intros n Lt H.
  induction Lt as [ | t Lt]; simpl.
  - unfold projectorListT. simpl. rewrite Mplus_0_r. auto.
  - rewrite ! map_app, ! map_map.
    rewrite Forall_cons_iff in H. destruct H.
    rewrite fold_right_Mplus_Zero_app.
    assert ((fun x : list F2 => projectorListT (0%F2 :: x) (t :: Lt)) =
              (fun x : list F2 => projectorT 0%F2 t × projectorListT x Lt)).
    { apply functional_extensionality. intros. apply projectorListT_cons. }
    rewrite H1.
    assert ((fun x : list F2 => projectorListT (1%F2 :: x) (t :: Lt)) =
              (fun x : list F2 => projectorT 1%F2 t × projectorListT x Lt)).
    { apply functional_extensionality. intros. apply projectorListT_cons. }
    rewrite H2.
    assert ((map (fun x : list F2 => projectorT 0%F2 t × projectorListT x Lt)
       (F2ListList (length Lt))) = 
             (map (fun x => projectorT 0%F2 t × x ) 
                (map (fun x : list F2 => projectorListT x Lt) (F2ListList (length Lt))))).
    { rewrite map_map. auto. }
    rewrite H3.
    assert ((map (fun x : list F2 => projectorT 1%F2 t × projectorListT x Lt)
       (F2ListList (length Lt))) = 
             (map (fun x => projectorT 1%F2 t × x ) 
                (map (fun x : list F2 => projectorListT x Lt) (F2ListList (length Lt))))).
    { rewrite map_map. auto. }
    rewrite H4.
    rewrite ! fold_right_Mplus_Zero_map_Mmult_distr.
    rewrite <- Mmult_plus_distr_r.
    rewrite projectorT_F2_sum; auto.
    rewrite IHLt; auto.
    rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma orthogonal_projectorListT_multi_subspace_sum_cons :
  forall {n : nat} (Lz : list F2) (LzList : list (list F2)) (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    length Lz = length Lt -> Forall (fun Lz : list F2 => length Lz = length Lt) LzList ->
    ~ In Lz LzList -> 
    @multi_orthogonal_subspaces (2 ^ n)%nat
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) LzList) ->
    @multi_orthogonal_subspaces (2 ^ n)%nat
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (Lz :: LzList)).
Proof. intros n Lz LzList Lt H H0 H1 H2 H3 H4 H5. 
  simpl. rewrite multi_orthogonal_subspaces_cons.
  split; intros; auto.
  rewrite nth_indep with (d := (fun v : Vector (2 ^ n) => v = Zero))
                         (d' := (fun Lz' : list F2 => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt))
                                 (repeat zero (length Lt))); auto.
  rewrite map_nth with (d := (repeat zero (length Lt))).
  apply orthogonal_projectorListT; auto.
  - rewrite Forall_nth in H3. apply H3. rewrite map_length in H6. auto.
  - intro. subst. contradict H4. apply nth_In. rewrite map_length in H6. auto.
Qed.

Lemma multi_no_subspace_overlap_projectorListT_cons :
  forall {n : nat} (Lz : list F2) (LzList : list (list F2)) (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    length Lz = length Lt -> Forall (fun Lz : list F2 => length Lz = length Lt) LzList ->
    ~ In Lz LzList -> 
    @multi_orthogonal_subspaces (2 ^ n)%nat
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) LzList) ->
    CM.multi_no_subspace_overlap 
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (Lz :: LzList)).
Proof. intros n Lz LzList Lt H H0 H1 H2 H3 H4 H5. 
  apply multi_orthogonal_subspaces_implies_multi_no_subspace_overlap.
  - simpl. rewrite Forall_cons_iff. split.
    + apply CM.span_is_subspace. apply WF_projectorListT; auto.
    + rewrite Forall_forall. intros x H6.
      apply In_nth with (d := @CM.span (2 ^ n) (2 ^ n) (projectorListT (repeat zero (length Lt)) Lt)) in H6. 
      destruct H6 as [k [kbound kth]]. subst.
      rewrite map_nth with (d := repeat zero (length Lt)).
      apply CM.span_is_subspace. apply WF_projectorListT; auto.
      rewrite Forall_nth in H3. apply H3. rewrite map_length in kbound. auto.
  - apply orthogonal_projectorListT_multi_subspace_sum_cons; auto.
Qed.

Lemma multi_orthogonal_subspaces_projectorListT_F2ListList : forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    @multi_orthogonal_subspaces (2 ^ n)%nat
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))).
Proof. intros n Lt H H0 H1.
  apply multi_orthogonal_subspaces_projectorListT; auto.
  apply NoDup_F2ListList.
  apply Forall_length_F2ListList.
Qed.

Lemma multi_no_subspace_overlap_projectorListT_F2ListList : forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt -> commutingListT Lt ->
    CM.multi_no_subspace_overlap 
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))).
Proof. intros n Lt H H0 H1.
  apply multi_orthogonal_subspaces_implies_multi_no_subspace_overlap.
  - rewrite Forall_forall. intros x H2.
    apply In_nth with (d := @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT (repeat zero (length Lt)) Lt))in H2.
    destruct H2 as [k [kbound kth]]. subst.
    rewrite map_nth with (d := (repeat zero (length Lt))).
    apply CM.span_is_subspace.
    apply WF_projectorListT; auto. 
    pose (Forall_length_F2ListList (length Lt)) as H2.
    rewrite Forall_nth in H2.
    apply H2. rewrite map_length in kbound. auto.
  - apply multi_orthogonal_subspaces_projectorListT_F2ListList; auto.
Qed.


Lemma multi_subspace_sum_projectorListT_F2ListList_total_space_necessary : 
  forall {n : nat} (Lt : list (TType n)) (v : Vector (2 ^ n)%nat),
    Forall proper_length_TType Lt -> WF_Matrix v -> 
    CM.multi_subspace_sum
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))) v.
Proof. intros n Lt v H H0. 
  gen v. induction Lt as [ | t Lt]; intros.
  - simpl. unfold projectorListT. simpl. exists v. exists (@Zero (2 ^ n) 1). repeat split; auto. 
    + unfold CM.span. exists v.  split; auto. rewrite Mmult_1_l; auto.
    + rewrite Mplus_0_r. auto.
  - simpl. rewrite map_app, ! map_map.
    rewrite CM.multi_subspace_sum_app.
    unfold CM.subspace_sum.
    assert ((fun x : list F2 => @CM.span (2^n) (2^n) (projectorListT (0%F2 :: x) (t :: Lt))) =
              (fun x : list F2 => @CM.span (2^n) (2^n) (projectorT 0%F2 t × projectorListT x Lt))).
    { apply functional_extensionality. intros. rewrite projectorListT_cons. auto. }
    rewrite H1.
    assert ((fun x : list F2 => @CM.span (2^n) (2^n) (projectorListT (1%F2 :: x) (t :: Lt))) =
              (fun x : list F2 => @CM.span (2^n) (2^n) (projectorT 1%F2 t × projectorListT x Lt))).
    { apply functional_extensionality. intros. rewrite projectorListT_cons. auto. }
    rewrite H2.
    rewrite Forall_cons_iff in H. destruct H.
    specialize (IHLt H3 v H0).
    exists (projectorT 0%F2 t × v). exists (projectorT 1%F2 t × v).
    clear H1 H2.
    repeat split.
    + assert ((map (fun x : list F2 => @CM.span (2^n) (2^n) (projectorT 0%F2 t × projectorListT x Lt))
       (F2ListList (length Lt))) = 
                (map (fun m : Square (2^n) => @CM.span (2^n) (2^n) (projectorT 0%F2 t × m)) (map (fun x : list F2 =>  projectorListT x Lt)
       (F2ListList (length Lt))))).
      { rewrite map_map. auto. }
      rewrite H1.
      apply CM.multi_subspace_sum_span_left_Mmult.
      rewrite map_map. auto.
    + assert ((map (fun x : list F2 => @CM.span (2^n) (2^n) (projectorT 1%F2 t × projectorListT x Lt))
       (F2ListList (length Lt))) = 
                (map (fun m : Square (2^n) => @CM.span (2^n) (2^n) (projectorT 1%F2 t × m)) (map (fun x : list F2 =>  projectorListT x Lt)
       (F2ListList (length Lt))))).
      { rewrite map_map. auto. }
      rewrite H1.
      apply CM.multi_subspace_sum_span_left_Mmult.
      rewrite map_map. auto.
    + replace (CM.GMplus (projectorT 0%F2 t × v) (projectorT 1%F2 t × v))
        with (Mplus (projectorT 0%F2 t × v) (projectorT 1%F2 t × v)) by auto.
      rewrite <- Mmult_plus_distr_r.
      rewrite projectorT_F2_sum; auto. rewrite Mmult_1_l; auto.
Qed.

Lemma multi_subspace_sum_projectorListT_F2ListList_total_space_sufficient : 
  forall {n : nat} (Lt : list (TType n)) (v : Vector (2 ^ n)%nat),
    Forall proper_length_TType Lt ->
    CM.multi_subspace_sum
      (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))) v -> WF_Matrix v.
Proof. intros n Lt v H H0.
  pose @CM.multi_subspace_sum_is_subspace as E.
  specialize (E (2^n)%nat (map (fun Lz' : list F2 => @CM.span (2^n) (2^n) (projectorListT Lz' Lt)) (F2ListList (length Lt)))).
  assert (Forall CM.subspace (map (fun Lz' : list F2 => @CM.span (2^n) (2^n) (projectorListT Lz' Lt)) (F2ListList (length Lt)))).
  { rewrite Forall_forall. intros x H1.
    apply In_nth with (d := @CM.span (2^n) (2^n) (projectorListT (repeat zero (length Lt)) Lt)) in H1.
    destruct H1 as [k [kbound kth]]. subst.
    rewrite map_nth with (d := (repeat zero (length Lt))).
    apply CM.span_is_subspace.
    apply WF_projectorListT; auto. rewrite Forall_nth in H.
    pose (Forall_length_F2ListList (length Lt)) as E'.
    rewrite Forall_nth in E'. apply E'. rewrite map_length in kbound. auto. }
  specialize (E H1).
  apply (CM.WF_subspace E H0).
Qed.

Lemma multi_subspace_sum_projectorListT_F2ListList_total_space_iff :
  forall {n : nat} (Lt : list (TType n)),
    Forall proper_length_TType Lt ->
    (forall v : Vector (2 ^ n)%nat,
        CM.multi_subspace_sum
          (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))) v <-> WF_Matrix v).
Proof. intros n Lt H v. split; intros.
  - apply (multi_subspace_sum_projectorListT_F2ListList_total_space_sufficient Lt v); auto.
  - apply (multi_subspace_sum_projectorListT_F2ListList_total_space_necessary Lt v); auto.
Qed.

Lemma dimension_multi_subspace_sum_span_projectorListT_F2ListList_fold_right_plus_repeat :
  forall {n : nat} (d : nat) (Lt : list (TType n)),
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat ->
    Lt <> [] -> Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt ->
    commutingListT Lt ->
    @CM.rank (2 ^ n)%nat (2 ^ n)%nat (projectorListT (repeat zero (length Lt)) Lt) d ->
    CM.dimension (CM.multi_subspace_sum (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt)))) (fold_right plus 0%nat (repeat d (2 ^ (length Lt))%nat)).
Proof. intros n d Lt H H0 H1 H2 H3 H4 H5. 
  apply CM.multi_subspace_sum_dimension.
  - rewrite map_length, F2ListList_length, repeat_length. auto.
  - rewrite Forall_forall. intros x H6. 
    apply In_nth with (d := (@CM.span (2^n)%nat (2^n)%nat (projectorListT (repeat zero (length Lt)) Lt), d)) in H6.
    destruct H6 as [k [kbound kth]]. subst.
    rewrite ! combine_nth.
    2: rewrite map_length, F2ListList_length, repeat_length; auto.
    simpl. rewrite map_nth with (d := (repeat 0%F2 (length Lt))).
    rewrite nth_repeat.
    rewrite <- (projectorListT_equal_rank d (nth k (F2ListList (length Lt)) (repeat 0%F2 (length Lt))) Lt) in H5; auto.
    2: { pose (Forall_length_F2ListList (length Lt)) as E.
        rewrite Forall_nth in E. apply E. 
        rewrite combine_length in kbound.
        rewrite map_length, F2ListList_length, repeat_length in kbound. 
        minmax_breakdown_context. 
        rewrite F2ListList_length. auto. }
    inversion H5. auto.
  - apply multi_no_subspace_overlap_projectorListT_F2ListList; auto.
Qed.

(* Main Theorem *)
Lemma dimension_stabilizeByListT :
  forall {n : nat} (d : nat) (Lt : list (TType n)),
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt)) -> n <> 0%nat ->
    Lt <> [] -> Forall proper_length_TType Lt -> Forall coef_plus_minus_1 Lt ->
    commutingListT Lt -> (length Lt <= n)%nat ->
    @CM.dimension (2^n)%nat (stabilizeByListT (fun v => WF_Matrix v) Lt) d ->
    d = (2 ^ (n - (length Lt)))%nat.
Proof. intros n d Lt H H0 H1 H2 H3 H4 H5 H6. 
  assert ((2^n)%nat = (d * (2 ^ (length Lt)))%nat).
  { apply @CM.unique_dimension with (P := (CM.multi_subspace_sum (map (fun Lz' => @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT Lz' Lt)) (F2ListList (length Lt))))).
    - rewrite @CM.swap_equivalent_subspace_in_dimension with (P2 := (fun v : Vector (2^n)%nat => WF_Matrix v)).
      apply CM.dimension_totalspace.
      intros v. apply multi_subspace_sum_projectorListT_F2ListList_total_space_iff; auto.
    - assert ((fold_right plus 0%nat (repeat d (2 ^ (length Lt))%nat)) = (d * 2 ^ length Lt)%nat).
      { clear - Lt. induction Lt.
        - simpl. lia.
        - simpl. rewrite <- repeat_combine, fold_right_add_0_app.
          rewrite Nat.add_0_r. rewrite ! IHLt. lia. }
      rewrite <- H7.
      apply dimension_multi_subspace_sum_span_projectorListT_F2ListList_fold_right_plus_repeat; auto.
      rewrite <- @CM.swap_equivalent_subspace_in_dimension with (P1 := @CM.span (2 ^ n)%nat (2 ^ n)%nat (projectorListT (repeat zero (length Lt)) Lt)) in H6.
      2: intros; apply projectorListT_span_stabilized_space; auto.
      constructor. auto. }
  rewrite Nat.pow_sub_r; auto. rewrite H7. rewrite Nat.div_mul; auto.
  apply Nat.pow_nonzero. lia.
Qed.



(* CheckMatrix related *)

Definition smash_rowF2 {m1 m2 n : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n) : MatrixF2 (m1 + m2) n :=
  fun i j : nat => if (i <? m1)%nat then M1 i j else M2 (i - m1)%nat j.

Lemma WF_smash_rowF2 : forall {m1 m2 n : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n),
    WF_MatrixF2 M1 -> WF_MatrixF2 M2 -> WF_MatrixF2 (smash_rowF2 M1 M2).
Proof. intros m1 m2 n M1 M2 H H0.
  unfold smash_rowF2, WF_MatrixF2.
  intros x y H1.
  destruct H1.
  - bdestruct_all; rewrite H0; auto; lia.
  - bdestruct_all; try rewrite H; try rewrite H0; auto; lia.
Qed.

Lemma smashF2_transposeF2_smash_rowF2 : forall {m1 m2 n : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n),
    transposeF2 (smash_rowF2 M1 M2) =
      smashF2 (transposeF2 M1) (transposeF2 M2).
Proof. intros m1 m2 n M1 M2.
  unfold transposeF2, smashF2, smash_rowF2.
  prep_matrix_equality. auto.
Qed.

Lemma smash_rowF2_transposeF2_smashF2 : forall {m n1 n2 : nat} (M1 : MatrixF2 m n1) (M2 : MatrixF2 m n2),
    transposeF2 (smashF2 M1 M2) =
      smash_rowF2 (transposeF2 M1) (transposeF2 M2).
Proof. intros m1 m2 n M1 M2.
  unfold transposeF2, smashF2, smash_rowF2.
  prep_matrix_equality. auto.
Qed.

Lemma smashF2_smash_rowF2_comm : forall {m1 m2 n1 n2} (UL : MatrixF2 m1 n1) (UR : MatrixF2 m1 n2) (DL : MatrixF2 m2 n1) (DR : MatrixF2 m2 n2),
    smashF2 (smash_rowF2 UL DL) (smash_rowF2 UR DR) = 
      smash_rowF2 (smashF2 UL UR) (smashF2 DL DR).
Proof. intros m1 m2 n1 n2 UL UR DL DR.
  unfold smashF2, smash_rowF2.
  prep_matrix_equality.
  bdestruct_all; auto.
Qed.

Lemma toCheckMatrixF2Left_split_smash_rowF2 : forall {n : nat} {LLp1 LLp2 : list (list Pauli)},
    (toCheckMatrixF2Left (length (LLp1 ++ LLp2)) n (LLp1 ++ LLp2)) =
      smash_rowF2 (toCheckMatrixF2Left (length LLp1) n LLp1)
                  (toCheckMatrixF2Left (length LLp2) n LLp2).
Proof. intros n LLp1 LLp2.
  unfold smash_rowF2, toCheckMatrixF2Left.
  prep_matrix_equality.
  bdestruct_all.
  - rewrite app_nth1; auto.
  - rewrite app_nth2; auto.
Qed.

Lemma toCheckMatrixF2Right_split_smash_rowF2 : forall {n : nat} {LLp1 LLp2 : list (list Pauli)},
    (toCheckMatrixF2Right (length (LLp1 ++ LLp2)) n (LLp1 ++ LLp2)) =
      smash_rowF2 (toCheckMatrixF2Right (length LLp1) n LLp1)
                  (toCheckMatrixF2Right (length LLp2) n LLp2).
Proof. intros n LLp1 LLp2.
  unfold smash_rowF2, toCheckMatrixF2Right.
  prep_matrix_equality.
  bdestruct_all.
  - rewrite app_nth1; auto.
  - rewrite app_nth2; auto.
Qed.

Lemma linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_app_split :
  forall {n : nat} (Lt1 Lt2 : list (TType n)),
    Forall proper_length_TType Lt1 -> Forall proper_length_TType Lt2 -> 
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 (Lt1 ++ Lt2))) ->
    linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt1)) /\
      linearly_independentF2 (transposeF2 (fromLtToCheckMatrixF2 Lt2)).
Proof. intros n Lt1 Lt2 properLt1 properLt2 H. split. 
  - unfold fromLtToCheckMatrixF2 in *.
    unfold fromLLpToCheckMatrixF2 in *.
    unfold Lt_to_LLp in *.
    rewrite ! map_app in H.
    assert (length (Lt1 ++ Lt2) = length (map snd Lt1 ++ map snd Lt2)).
    { rewrite ! app_length, ! map_length; auto. }
    rewrite ! H0 in H.
    rewrite toCheckMatrixF2Left_split_smash_rowF2 in H.
    rewrite toCheckMatrixF2Right_split_smash_rowF2 in H.
    setoid_rewrite smashF2_smash_rowF2_comm in H.
    setoid_rewrite smashF2_transposeF2_smash_rowF2 in H.
    rewrite ! app_length, ! map_length in *.
    apply @F2Module.lin_indep_smash_left with (A2 := (transposeF2
              (smashF2 (toCheckMatrixF2Left (length Lt2) n (map snd Lt2))
                 (toCheckMatrixF2Right (length Lt2) n (map snd Lt2)))))
                                              (n2 := (length Lt2)). auto.
  - unfold fromLtToCheckMatrixF2 in *.
    unfold fromLLpToCheckMatrixF2 in *.
    unfold Lt_to_LLp in *.
    rewrite ! map_app in H.
    assert (length (Lt1 ++ Lt2) = length (map snd Lt1 ++ map snd Lt2)).
    { rewrite ! app_length, ! map_length; auto. }
    rewrite ! H0 in H.
    rewrite toCheckMatrixF2Left_split_smash_rowF2 in H.
    rewrite toCheckMatrixF2Right_split_smash_rowF2 in H.
    setoid_rewrite smashF2_smash_rowF2_comm in H.
    setoid_rewrite smashF2_transposeF2_smash_rowF2 in H.
    rewrite ! app_length, ! map_length in *.
    apply @F2Module.lin_indep_smash_right with (A1 := (transposeF2
              (smashF2 (toCheckMatrixF2Left (length Lt1) n (map snd Lt1))
                 (toCheckMatrixF2Right (length Lt1) n (map snd Lt1)))))
                                              (n1 := (length Lt1)); auto.
    + apply F2Module.WF_transpose. apply F2Module.WF_smash.
      * apply WF_toCheckMatrixF2Left. 
        -- rewrite map_length; auto.
        -- rewrite Forall_forall in *. intros x H1.
           rewrite in_map_iff in H1.
           destruct H1 as [t [sndt int]].
           specialize (properLt1 t int).
           destruct properLt1.
           rewrite sndt in H2.
           lia.
      * apply WF_toCheckMatrixF2Right. 
        -- rewrite map_length; auto.
        -- rewrite Forall_forall in *. intros x H1.
           rewrite in_map_iff in H1.
           destruct H1 as [t [sndt int]].
           specialize (properLt1 t int).
           destruct properLt1.
           rewrite sndt in H2.
           lia.
    + apply F2Module.WF_transpose. apply F2Module.WF_smash.
      * apply WF_toCheckMatrixF2Left. 
        -- rewrite map_length; auto.
        -- rewrite Forall_forall in *. intros x H1.
           rewrite in_map_iff in H1.
           destruct H1 as [t [sndt int]].
           specialize (properLt2 t int).
           destruct properLt2.
           rewrite sndt in H2.
           lia.
      * apply WF_toCheckMatrixF2Right. 
        -- rewrite map_length; auto.
        -- rewrite Forall_forall in *. intros x H1.
           rewrite in_map_iff in H1.
           destruct H1 as [t [sndt int]].
           specialize (properLt2 t int).
           destruct properLt2.
           rewrite sndt in H2.
           lia.
Qed.


Lemma toCheckMatrixF2Left_ExtendQubitsToRight_smashF2_ZeroF2 :
  forall (row col m : nat) (LLp : list (list Pauli)),
    length LLp = row -> Forall (fun Lp => length Lp = col) LLp ->
    toCheckMatrixF2Left row (col + m) (map (fun Lp => Lp ++ (repeat gI m)) LLp) =
      smashF2 (toCheckMatrixF2Left row col LLp) (@ZeroF2 row m).
Proof. intros row col m LLp lenLLP lenLp.
  prep_matrix_equality.
  assert (WF_Ext : WF_MatrixF2 (toCheckMatrixF2Left row (col + m)
    (map (fun Lp : list Pauli => Lp ++ repeat gI m) LLp))).
  { apply WF_toCheckMatrixF2Left.
    - rewrite map_length; lia.
    - rewrite Forall_forall in *. intros x0 H.
      rewrite in_map_iff in H. destruct H as [x1 [x1app inx1]].
      specialize (lenLp x1 inx1).
      rewrite <- x1app.
      rewrite app_length, repeat_length.
      lia. }
  assert (WF_sm : WF_MatrixF2 (smashF2 (toCheckMatrixF2Left row col LLp) (@ZeroF2 row m))).
  { apply WF_smashF2. 2: apply F2Module.WF_Zero.
    apply WF_toCheckMatrixF2Left; try lia.
    rewrite Forall_forall in *.
    intros x0 H.
    rewrite lenLp; auto. }
  bdestruct (x <? row)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  bdestruct (y <? col + m)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  unfold toCheckMatrixF2Left, smashF2.
  bdestruct_all.
  - f_equal.
    assert ((repeat gI col) ++ (repeat gI m) = repeat gI (col + m)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth1; auto.
    rewrite Forall_forall in lenLp.
    assert (In (nth x LLp (repeat gI col)) LLp).
    { apply nth_In; lia. }
    rewrite lenLp; auto.
  - assert ((repeat gI col) ++ (repeat gI m) = repeat gI (col + m)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    assert (length (nth x LLp (repeat gI col)) = col).
    { rewrite Forall_forall in *.
      assert (In (nth x LLp (repeat gI col)) LLp).
      { apply nth_In; lia. }
      rewrite lenLp; auto. }
    rewrite app_nth2; try lia.
    rewrite nth_repeat.
    simpl. unfold ZeroF2. auto.
Qed.

Lemma toCheckMatrixF2Right_ExtendQubitsToRight_smashF2_ZeroF2 :
  forall (row col m : nat) (LLp : list (list Pauli)),
    length LLp = row -> Forall (fun Lp => length Lp = col) LLp ->
    toCheckMatrixF2Right row (col + m) (map (fun Lp => Lp ++ (repeat gI m)) LLp) =
      smashF2 (toCheckMatrixF2Right row col LLp) (@ZeroF2 row m).
Proof. intros row col m LLp lenLLP lenLp.
  prep_matrix_equality.
  assert (WF_Ext : WF_MatrixF2 (toCheckMatrixF2Right row (col + m)
    (map (fun Lp : list Pauli => Lp ++ repeat gI m) LLp))).
  { apply WF_toCheckMatrixF2Right.
    - rewrite map_length; lia.
    - rewrite Forall_forall in *. intros x0 H.
      rewrite in_map_iff in H. destruct H as [x1 [x1app inx1]].
      specialize (lenLp x1 inx1).
      rewrite <- x1app.
      rewrite app_length, repeat_length.
      lia. }
  assert (WF_sm : WF_MatrixF2 (smashF2 (toCheckMatrixF2Right row col LLp) (@ZeroF2 row m))).
  { apply WF_smashF2. 2: apply F2Module.WF_Zero.
    apply WF_toCheckMatrixF2Right; try lia.
    rewrite Forall_forall in *.
    intros x0 H.
    rewrite lenLp; auto. }
  bdestruct (x <? row)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  bdestruct (y <? col + m)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  unfold toCheckMatrixF2Right, smashF2.
  bdestruct_all.
  - f_equal.
    assert ((repeat gI col) ++ (repeat gI m) = repeat gI (col + m)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth1; auto.
    rewrite Forall_forall in lenLp.
    assert (In (nth x LLp (repeat gI col)) LLp).
    { apply nth_In; lia. }
    rewrite lenLp; auto.
  - assert ((repeat gI col) ++ (repeat gI m) = repeat gI (col + m)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    assert (length (nth x LLp (repeat gI col)) = col).
    { rewrite Forall_forall in *.
      assert (In (nth x LLp (repeat gI col)) LLp).
      { apply nth_In; lia. }
      rewrite lenLp; auto. }
    rewrite app_nth2; try lia.
    rewrite nth_repeat.
    simpl. unfold ZeroF2. auto.
Qed.

Lemma fromLtToCheckMatrixF2_ExtendQubitsToRight_smashF2 :
  forall {n m : nat} (Lt1 : list (TType n)),
       Forall proper_length_TType Lt1 ->
  (fromLtToCheckMatrixF2
     (map (uncurry gTensorT)
        (combine Lt1 (repeat (defaultT_I m) (length Lt1))))) =

smashF2 (smashF2 (toCheckMatrixF2Left (length Lt1) n (Lt_to_LLp Lt1)) (@ZeroF2 (length Lt1) m))
(smashF2 (toCheckMatrixF2Right (length Lt1) n (Lt_to_LLp Lt1)) (@ZeroF2 (length Lt1) m)).
Proof. intros n m Lt1 H.
  unfold fromLtToCheckMatrixF2.
  unfold fromLLpToCheckMatrixF2.
  unfold Lt_to_LLp.
  rewrite ! map_map.
  assert ((map (fun x : TType n * TType m => snd (uncurry gTensorT x))
          (combine Lt1 (repeat (defaultT_I m) (length Lt1)))) =
            (map (fun x : list Pauli => x ++ (repeat gI m)) (map snd Lt1))).
  { apply nth_ext with (d := snd (uncurry gTensorT (defaultT_I n, defaultT_I m))) (d' := (repeat gI n) ++ (repeat gI m)).
     - rewrite ! map_length, combine_length, repeat_length. minmax_breakdown. auto.
     - intros n0 H0.
       rewrite map_nth with (d := (defaultT_I n, defaultT_I m)).
       rewrite map_nth with (d := repeat gI n).
       unfold gTensorT, uncurry. 
       rewrite combine_nth.
       simpl. 
       2: rewrite repeat_length; auto.
       destruct (nth n0 Lt1 (defaultT_I n)) eqn:E1.
       destruct (nth n0 (repeat (defaultT_I m) (length Lt1)) (defaultT_I m)) eqn:E2.
       simpl. 
       rewrite nth_repeat in E2.
       unfold defaultT_I in E2.
       inversion E2.
       f_equal.
       assert (l = snd (nth n0 Lt1 (defaultT_I n))).
       { rewrite E1. auto. }
       rewrite H1.
       assert (snd (defaultT_I n) = repeat gI n).
       { unfold defaultT_I. auto. }
       rewrite <- H4.
       rewrite map_nth. auto. }
  rewrite H0.
  assert ((length
          (map (uncurry gTensorT)
             (combine Lt1 (repeat (defaultT_I m) (length Lt1))))) =
            length Lt1).
  { rewrite map_length, combine_length, repeat_length. minmax_breakdown. auto. }
  rewrite H1.
  rewrite (toCheckMatrixF2Left_ExtendQubitsToRight_smashF2_ZeroF2
             (length Lt1) n m (map snd Lt1)).
  rewrite (toCheckMatrixF2Right_ExtendQubitsToRight_smashF2_ZeroF2
             (length Lt1) n m (map snd Lt1)).
  auto.
  all : try rewrite map_length; auto.
  rewrite Forall_forall in *.
  intros x H2.
  rewrite in_map_iff in H2.
  destruct H2 as [x0 [sndx0 inx0]].
  specialize (H x0 inx0).
  destruct H.
  rewrite sndx0 in H2.
  auto.
  rewrite Forall_forall in *.
  intros x H2.
  rewrite in_map_iff in H2.
  destruct H2 as [x0 [sndx0 inx0]].
  specialize (H x0 inx0).
  destruct H.
  rewrite sndx0 in H2.
  auto.
Qed.

Lemma toCheckMatrixF2Left_ExtendQubitsToLeft_smashF2_ZeroF2 :
  forall (row col n : nat) (LLp : list (list Pauli)),
    length LLp = row -> Forall (fun Lp => length Lp = col) LLp ->
    toCheckMatrixF2Left row (n + col) (map (fun Lp => (repeat gI n) ++ Lp) LLp) =
      smashF2 (@ZeroF2 row n) (toCheckMatrixF2Left row col LLp).
Proof. intros row col n LLp lenLLP lenLp.
  prep_matrix_equality.
  assert (WF_Ext : WF_MatrixF2 (toCheckMatrixF2Left row (n + col)
    (map (fun Lp : list Pauli => repeat gI n ++ Lp) LLp))).
  { apply WF_toCheckMatrixF2Left.
    - rewrite map_length; lia.
    - rewrite Forall_forall in *. intros x0 H.
      rewrite in_map_iff in H. destruct H as [x1 [x1app inx1]].
      specialize (lenLp x1 inx1).
      rewrite <- x1app.
      rewrite app_length, repeat_length.
      lia. }
  assert (WF_sm : WF_MatrixF2 (smashF2 (@ZeroF2 row n) (toCheckMatrixF2Left row col LLp))).
  { apply WF_smashF2. apply F2Module.WF_Zero.
    apply WF_toCheckMatrixF2Left; try lia.
    rewrite Forall_forall in *.
    intros x0 H.
    rewrite lenLp; auto. }
  bdestruct (x <? row)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  bdestruct (y <? n + col)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  unfold toCheckMatrixF2Left, smashF2, ZeroF2.
  bdestruct_all.
  - assert ((repeat gI n) ++ (repeat gI col) = repeat gI (n + col)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth1; auto.
    rewrite nth_repeat.
    simpl. auto.
    rewrite repeat_length; auto.
  - assert ((repeat gI n) ++ (repeat gI col) = repeat gI (n + col)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth2; try lia.
    all: rewrite repeat_length; auto.
Qed.

Lemma toCheckMatrixF2Right_ExtendQubitsToLeft_smashF2_ZeroF2 :
  forall (row col n : nat) (LLp : list (list Pauli)),
    length LLp = row -> Forall (fun Lp => length Lp = col) LLp ->
    toCheckMatrixF2Right row (n + col) (map (fun Lp => (repeat gI n) ++ Lp) LLp) =
      smashF2 (@ZeroF2 row n) (toCheckMatrixF2Right row col LLp).
Proof. intros row col n LLp lenLLP lenLp.
  prep_matrix_equality.
  assert (WF_Ext : WF_MatrixF2 (toCheckMatrixF2Right row (n + col)
    (map (fun Lp : list Pauli => repeat gI n ++ Lp) LLp))).
  { apply WF_toCheckMatrixF2Right.
    - rewrite map_length; lia.
    - rewrite Forall_forall in *. intros x0 H.
      rewrite in_map_iff in H. destruct H as [x1 [x1app inx1]].
      specialize (lenLp x1 inx1).
      rewrite <- x1app.
      rewrite app_length, repeat_length.
      lia. }
  assert (WF_sm : WF_MatrixF2 (smashF2 (@ZeroF2 row n) (toCheckMatrixF2Right row col LLp))).
  { apply WF_smashF2. apply F2Module.WF_Zero.
    apply WF_toCheckMatrixF2Right; try lia.
    rewrite Forall_forall in *.
    intros x0 H.
    rewrite lenLp; auto. }
  bdestruct (x <? row)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  bdestruct (y <? n + col)%nat.
  2: rewrite WF_Ext, WF_sm; auto; lia.
  unfold toCheckMatrixF2Right, smashF2, ZeroF2.
  bdestruct_all.
  - assert ((repeat gI n) ++ (repeat gI col) = repeat gI (n + col)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth1; auto.
    rewrite nth_repeat.
    simpl. auto.
    rewrite repeat_length; auto.
  - assert ((repeat gI n) ++ (repeat gI col) = repeat gI (n + col)).
    { rewrite repeat_app; auto. }
    rewrite <- H2.
    rewrite map_nth with (d := repeat gI col).
    rewrite app_nth2; try lia.
    all: rewrite repeat_length; auto.
Qed.

Lemma fromLtToCheckMatrixF2_ExtendQubitsToLeft_smashF2 :
  forall {n m : nat} (Lt2 : list (TType m)),
       Forall proper_length_TType Lt2 ->
  (fromLtToCheckMatrixF2
     (map (uncurry gTensorT)
        (combine (repeat (defaultT_I n) (length Lt2)) Lt2))) =

smashF2 (smashF2 (@ZeroF2 (length Lt2) n) (toCheckMatrixF2Left (length Lt2) m (Lt_to_LLp Lt2)))
(smashF2 (@ZeroF2 (length Lt2) n) (toCheckMatrixF2Right (length Lt2) m (Lt_to_LLp Lt2))).
Proof. intros n m Lt2 H. 
  unfold fromLtToCheckMatrixF2.
  unfold fromLLpToCheckMatrixF2.
  unfold Lt_to_LLp.
  rewrite ! map_map.
  assert ((map (fun x : TType n * TType m => snd (uncurry gTensorT x))
          (combine (repeat (defaultT_I n) (length Lt2)) Lt2)) =
            (map (fun x : list Pauli => (repeat gI n) ++ x) (map snd Lt2))).
  { apply nth_ext with (d := snd (uncurry gTensorT (defaultT_I n, defaultT_I m))) (d' := (repeat gI n) ++ (repeat gI m)).
     - rewrite ! map_length, combine_length, repeat_length. minmax_breakdown. auto.
     - intros n0 H0.
       rewrite map_nth with (d := (defaultT_I n, defaultT_I m)).
       rewrite map_nth with (d := repeat gI m).
       unfold gTensorT, uncurry. 
       rewrite combine_nth.
       simpl. 
       2: rewrite repeat_length; auto.
       destruct (nth n0 Lt2 (defaultT_I m)) eqn:E1.
       destruct (nth n0 (repeat (defaultT_I n) (length Lt2)) (defaultT_I n)) eqn:E2.
       simpl. 
       rewrite nth_repeat in E2.
       unfold defaultT_I in E2.
       inversion E2.
       f_equal.
       assert (l = snd (nth n0 Lt2 (defaultT_I m))).
       { rewrite E1. auto. }
       rewrite H1.
       assert (snd (defaultT_I m) = repeat gI m).
       { unfold defaultT_I. auto. }
       rewrite <- H4.
       rewrite map_nth. auto. }
  rewrite H0.
  assert ((length
          (map (uncurry gTensorT)
             (combine (repeat (defaultT_I n) (length Lt2)) Lt2))) =
            length Lt2).
  { rewrite map_length, combine_length, repeat_length. minmax_breakdown. auto. }
  rewrite H1.
  rewrite (toCheckMatrixF2Left_ExtendQubitsToLeft_smashF2_ZeroF2
             (length Lt2) m n (map snd Lt2)).
  rewrite (toCheckMatrixF2Right_ExtendQubitsToLeft_smashF2_ZeroF2
             (length Lt2) m n (map snd Lt2)).
  auto.
  all : try rewrite map_length; auto.
  rewrite Forall_forall in *.
  intros x H2.
  rewrite in_map_iff in H2.
  destruct H2 as [x0 [sndx0 inx0]].
  specialize (H x0 inx0).
  destruct H.
  rewrite sndx0 in H2.
  auto.
  rewrite Forall_forall in *.
  intros x H2.
  rewrite in_map_iff in H2.
  destruct H2 as [x0 [sndx0 inx0]].
  specialize (H x0 inx0).
  destruct H.
  rewrite sndx0 in H2.
  auto.
Qed.

Lemma smash_rowF2_assoc : forall {n m1 m2 m3 : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n) (M3 : MatrixF2 m3 n),
    smash_rowF2 (smash_rowF2 M1 M2) M3 = smash_rowF2 M1 (smash_rowF2 M2 M3).
Proof. intros n m1 m2 m3 M1 M2 M3.
  unfold smash_rowF2.
  prep_matrix_equality.
  bdestruct_all; auto.
  replace (x - (m1 + m2))%nat with (x - m1 - m2)%nat by lia.
  auto.
Qed.

Lemma linearly_independentF2_smash_rowF2_swap : 
  forall {n m1 m2 : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n),
    WF_MatrixF2 M1 -> WF_MatrixF2 M2 ->
    linearly_independentF2 (smash_rowF2 M1 M2) ->
    linearly_independentF2 (smash_rowF2 M2 M1).
Proof. intros n m1 m2 M1 M2 WFM1 WFM2 H.
  unfold linearly_independentF2 in *.
  intros a H0 H1.
  apply H; auto.
  unfold smash_rowF2, MmultF2, ZeroF2.
  unfold smash_rowF2, MmultF2, ZeroF2 in H1.
  prep_matrix_equality.
  bdestruct (x <? m1 + m2)%nat.
  2: { apply big_sum_0_bounded.
       intros x0 H3. bdestruct_all.
       rewrite WFM2; auto; try lia. F2simpl. auto. }
  bdestruct (x <? m1)%nat.
  - apply f_equal_inv with (x := (x + m2)%nat) in H1.
    apply f_equal_inv with (x := y) in H1.
    rewrite <- H1.
    apply big_sum_eq_bounded.
    intros x0 H4.
    bdestruct_all.
    replace (x + m2 - m2)%nat with x by lia.
    auto.
  - apply f_equal_inv with (x := (x - m1)%nat) in H1.
    apply f_equal_inv with (x := y) in H1.
    rewrite <- H1.
    apply big_sum_eq_bounded.
    intros x0 H4.
    bdestruct_all.
    auto.
Qed.

Lemma linearly_independentF2_smash_rowF2_swap_iff : 
  forall {n m1 m2 : nat} (M1 : MatrixF2 m1 n) (M2 : MatrixF2 m2 n),
    WF_MatrixF2 M1 -> WF_MatrixF2 M2 ->
    (linearly_independentF2 (smash_rowF2 M1 M2) <->
    linearly_independentF2 (smash_rowF2 M2 M1)).
Proof. intros n m1 m2 M1 M2 H H0. split; intros;
  apply linearly_independentF2_smash_rowF2_swap; auto.
Qed.
    
Lemma smash_rowF2_ZeroF2_right_preserves_linearly_independentF2 :
  forall {n m1 m2 : nat} (M : MatrixF2 m1 n),
    WF_MatrixF2 M ->
    (linearly_independentF2 (smash_rowF2 M (@ZeroF2 m2 n)) <-> 
      linearly_independentF2 M).
Proof. intros n m1 m2 M WFM.
  split; intros.
  - unfold linearly_independentF2 in *.
    intros a H0 H1.
    apply H; auto.
    unfold ZeroF2, MmultF2 in H1.
    unfold smash_rowF2, ZeroF2, MmultF2.
    prep_matrix_equality.
    apply f_equal_inv with (x := x) in H1.
    apply f_equal_inv with (x := y) in H1.
    setoid_rewrite <- H1 at 2.
    apply big_sum_eq_bounded.
    intros x0 H2. simpl.
    bdestruct_all; auto.
    rewrite WFM; auto; lia.
  - unfold linearly_independentF2 in *.
    intros a H0 H1.
    specialize (H a H0).
    apply H.
    unfold ZeroF2, MmultF2.
    unfold smash_rowF2, ZeroF2, MmultF2 in H1.
    prep_matrix_equality.
    apply f_equal_inv with (x := x) in H1.
    apply f_equal_inv with (x := y) in H1.
    setoid_rewrite <- H1 at 1.
    apply big_sum_eq_bounded.
    intros x0 H2. simpl.
    bdestruct_all; auto.
    rewrite WFM; auto; lia.
Qed.


Lemma linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_ExtendQubitsToRight : 
  forall {n m : nat} (Lt1 : list (TType n)),
    (n <> 0)%nat -> Lt1 <> [] -> length Lt1 = n -> Forall proper_length_TType Lt1 ->
    linearly_independentF2
         (transposeF2
            (fromLtToCheckMatrixF2
               (map (uncurry gTensorT)
                  (combine Lt1 (repeat (defaultT_I m) (length Lt1)))))) ->
     linearly_independentF2
         (transposeF2
            (fromLtToCheckMatrixF2 Lt1)).
Proof. intros n m Lt1 H H0 H1 H2 H3.
  rewrite fromLtToCheckMatrixF2_ExtendQubitsToRight_smashF2 in H3; auto.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M1 := (smashF2 (toCheckMatrixF2Left (length Lt1) n (Lt_to_LLp Lt1)) ZeroF2))
         (M2 := (smashF2 (toCheckMatrixF2Right (length Lt1) n (Lt_to_LLp Lt1)) ZeroF2))
    in H3.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M1 := (toCheckMatrixF2Left (length Lt1) n (Lt_to_LLp Lt1)))
    in H3.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M1 := (toCheckMatrixF2Right (length Lt1) n (Lt_to_LLp Lt1)))
    in H3.
  setoid_rewrite F2Module.zero_transpose_eq in H3.
  setoid_rewrite <- smash_rowF2_assoc in H3.
  rewrite ! map_length, ! combine_length, ! repeat_length in H3.
  minmax_breakdown_context.
  rewrite smash_rowF2_ZeroF2_right_preserves_linearly_independentF2
    with (M := (@smash_rowF2 (Init.Nat.add n m) n (@length (TType n) Lt1)
               (@smash_rowF2 n m (@length (TType n) Lt1)
                  (@F2Module.transpose (@length (TType n) Lt1) n
                     (toCheckMatrixF2Left (@length (TType n) Lt1) n
                        (@Lt_to_LLp n Lt1)))
                  (@F2Module.Zero m (@length (TType n) Lt1)))
               (@F2Module.transpose (@length (TType n) Lt1) n
                  (toCheckMatrixF2Right (@length (TType n) Lt1) n
                     (@Lt_to_LLp n Lt1)))))
    in H3.
  apply linearly_independentF2_smash_rowF2_swap in H3.
  rewrite <- smash_rowF2_assoc in H3.
  rewrite smash_rowF2_ZeroF2_right_preserves_linearly_independentF2
    with (M := (@smash_rowF2 n n (@length (TType n) Lt1)
               (@F2Module.transpose (@length (TType n) Lt1) n
                  (toCheckMatrixF2Right (@length (TType n) Lt1) n
                     (@Lt_to_LLp n Lt1)))
               (@F2Module.transpose (@length (TType n) Lt1) n
                  (toCheckMatrixF2Left (@length (TType n) Lt1) n (@Lt_to_LLp n Lt1)))))
    in H3.
  apply linearly_independentF2_smash_rowF2_swap in H3.
  unfold fromLtToCheckMatrixF2, fromLLpToCheckMatrixF2.
  rewrite smash_rowF2_transposeF2_smashF2. auto.
  - apply F2Module.WF_transpose.
    apply WF_toCheckMatrixF2Right.
    unfold Lt_to_LLp.
    rewrite map_length; auto.
    rewrite Forall_forall in *.
    intros x H4. unfold Lt_to_LLp in H4.
    rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
    destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply F2Module.WF_transpose.
    apply WF_toCheckMatrixF2Left.
    unfold Lt_to_LLp.
    rewrite map_length; auto.
    rewrite Forall_forall in *.
    intros x H4. unfold Lt_to_LLp in H4.
    rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
    destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Right.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Left.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Left.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply F2Module.WF_Zero.
  - apply F2Module.WF_transpose.
    apply WF_toCheckMatrixF2Right.
    unfold Lt_to_LLp.
    rewrite map_length; auto.
    rewrite Forall_forall in *.
    intros x H4. unfold Lt_to_LLp in H4.
    rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
    destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply WF_smash_rowF2.
      * apply F2Module.WF_transpose.
        apply WF_toCheckMatrixF2Left.
        unfold Lt_to_LLp.
        rewrite map_length; auto.
        rewrite Forall_forall in *.
        intros x H4. unfold Lt_to_LLp in H4.
        rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
        destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
      * apply F2Module.WF_Zero.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Right.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
Qed.

Lemma linearly_independentF2_transposeF2_fromLtToCheckMatrixF2_ExtendQubitsToLeft : 
  forall {n m : nat} (Lt2 : list (TType m)),
    (m <> 0)%nat -> Lt2 <> [] -> length Lt2 = m -> Forall proper_length_TType Lt2 ->
    linearly_independentF2
         (transposeF2
            (fromLtToCheckMatrixF2
               (map (uncurry gTensorT)
                  (combine (repeat (defaultT_I n) (length Lt2)) Lt2)))) ->
     linearly_independentF2
         (transposeF2
            (fromLtToCheckMatrixF2 Lt2)).
Proof. intros n m Lt2 H H0 H1 H2 H3. 
  rewrite fromLtToCheckMatrixF2_ExtendQubitsToLeft_smashF2 in H3; auto.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M1 := (smashF2 ZeroF2 (toCheckMatrixF2Left (length Lt2) m (Lt_to_LLp Lt2))))
         (M2 := (smashF2 ZeroF2 (toCheckMatrixF2Right (length Lt2) m (Lt_to_LLp Lt2))))
    in H3.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M2 := (toCheckMatrixF2Left (length Lt2) m (Lt_to_LLp Lt2)))
    in H3.
  setoid_rewrite smash_rowF2_transposeF2_smashF2
    with (M2 := (toCheckMatrixF2Right (length Lt2) m (Lt_to_LLp Lt2)))
    in H3.
  setoid_rewrite F2Module.zero_transpose_eq in H3.
  setoid_rewrite <- smash_rowF2_assoc in H3.
  rewrite ! map_length, ! combine_length, ! repeat_length in H3.
  minmax_breakdown_context.
  rewrite linearly_independentF2_smash_rowF2_swap_iff 
          with (M1 := (@smash_rowF2 (Init.Nat.add n m) n (@length (TType m) Lt2)
               (@smash_rowF2 n m (@length (TType m) Lt2)
                  (@F2Module.Zero n (@length (TType m) Lt2))
                  (@F2Module.transpose (@length (TType m) Lt2) m
                     (toCheckMatrixF2Left (@length (TType m) Lt2) m
                        (@Lt_to_LLp m Lt2))))
               (@F2Module.Zero n (@length (TType m) Lt2))))
          (M2 := (@F2Module.transpose (@length (TType m) Lt2) m
               (toCheckMatrixF2Right (@length (TType m) Lt2) m (@Lt_to_LLp m Lt2))))
    in H3.
  setoid_rewrite <- smash_rowF2_assoc in H3.
  rewrite smash_rowF2_ZeroF2_right_preserves_linearly_independentF2
    with (M := (@smash_rowF2 m (Init.Nat.add n m) (@length (TType m) Lt2)
               (@F2Module.transpose (@length (TType m) Lt2) m
                  (toCheckMatrixF2Right (@length (TType m) Lt2) m
                     (@Lt_to_LLp m Lt2)))
               (@smash_rowF2 n m (@length (TType m) Lt2)
                  (@F2Module.Zero n (@length (TType m) Lt2))
                  (@F2Module.transpose (@length (TType m) Lt2) m
                     (toCheckMatrixF2Left (@length (TType m) Lt2) m
                        (@Lt_to_LLp m Lt2))))))
    in H3.
  setoid_rewrite <- smash_rowF2_assoc in H3.
  rewrite linearly_independentF2_smash_rowF2_swap_iff 
    with (M1 := (@smash_rowF2 m n (@length (TType m) Lt2)
               (@F2Module.transpose (@length (TType m) Lt2) m
                  (toCheckMatrixF2Right (@length (TType m) Lt2) m
                     (@Lt_to_LLp m Lt2)))
               (@F2Module.Zero n (@length (TType m) Lt2))))
         (M2 := (@F2Module.transpose (@length (TType m) Lt2) m
               (toCheckMatrixF2Left (@length (TType m) Lt2) m (@Lt_to_LLp m Lt2))))
    in H3.
  rewrite <- smash_rowF2_assoc in H3.
  rewrite smash_rowF2_ZeroF2_right_preserves_linearly_independentF2
    with (M := (@smash_rowF2 m m (@length (TType m) Lt2)
               (@F2Module.transpose (@length (TType m) Lt2) m
                  (toCheckMatrixF2Left (@length (TType m) Lt2) m (@Lt_to_LLp m Lt2)))
               (@F2Module.transpose (@length (TType m) Lt2) m
                  (toCheckMatrixF2Right (@length (TType m) Lt2) m
                     (@Lt_to_LLp m Lt2)))))
    in H3.
  unfold fromLtToCheckMatrixF2, fromLLpToCheckMatrixF2.
  rewrite smash_rowF2_transposeF2_smashF2. auto.
  - apply WF_smash_rowF2.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Left.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Right.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Right.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply F2Module.WF_Zero.
  - apply F2Module.WF_transpose.
    apply WF_toCheckMatrixF2Left.
    unfold Lt_to_LLp.
    rewrite map_length; auto.
    rewrite Forall_forall in *.
    intros x H4. unfold Lt_to_LLp in H4.
    rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
    destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply F2Module.WF_transpose.
      apply WF_toCheckMatrixF2Right.
      unfold Lt_to_LLp.
      rewrite map_length; auto.
      rewrite Forall_forall in *.
      intros x H4. unfold Lt_to_LLp in H4.
      rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
      destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply WF_smash_rowF2.
      * apply F2Module.WF_Zero.
      * apply F2Module.WF_transpose.
        apply WF_toCheckMatrixF2Left.
        unfold Lt_to_LLp.
        rewrite map_length; auto.
        rewrite Forall_forall in *.
        intros x H4. unfold Lt_to_LLp in H4.
        rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
        destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
  - apply WF_smash_rowF2.
    + apply WF_smash_rowF2.
      * apply F2Module.WF_Zero.
      * apply F2Module.WF_transpose.
        apply WF_toCheckMatrixF2Left.
        unfold Lt_to_LLp.
        rewrite map_length; auto.
        rewrite Forall_forall in *.
        intros x H4. unfold Lt_to_LLp in H4.
        rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
        destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
    + apply F2Module.WF_Zero.
  - apply F2Module.WF_transpose.
    apply WF_toCheckMatrixF2Right.
    unfold Lt_to_LLp.
    rewrite map_length; auto.
    rewrite Forall_forall in *.
    intros x H4. unfold Lt_to_LLp in H4.
    rewrite in_map_iff in H4. destruct H4 as [x0 [sndx0 inx0]].
    destruct (H2 x0 inx0). rewrite sndx0 in H5. lia.
Qed.




Import my_H.





(**************************************)
(** ** Semantical Definitions ** **)
(**************************************)

(** order is from left to right **)
Definition collect_fun {A : Type} (len : nat) (f : nat -> A) := map f (List.seq 0%nat len).
Definition to_fun {A : Type} (d : A) (ls : list A) := (fun n : nat => nth n ls d).

Lemma collect_fun_length : forall {A : Type} (len : nat) (f : nat -> A),
    length (collect_fun len f) = len.
Proof. intros A len f.
  unfold collect_fun.
  rewrite map_length, seq_length; auto.
Qed.

Lemma collect_fun_to_fun : forall {A : Type} (d : A) (ls : list A),
    collect_fun (length ls) (to_fun d ls) = ls.
Proof. intros A d ls. 
  unfold collect_fun, to_fun.
  apply nth_ext with (d := nth (length ls) ls d) (d' := d).
  - rewrite map_length, seq_length. auto.
  - intros n H0.
    rewrite map_nth with (d := length ls).
    rewrite map_length, seq_length in H0.
    rewrite seq_nth; auto.
Qed.

Lemma WF_collect_fun_perm_to_fun : forall {n m : nat} (d : Matrix n m) (ls : list (Matrix n m)) (p : nat -> nat),
    permutation (length ls) p -> Forall WF_Matrix ls -> WF_Matrix d ->
    Forall WF_Matrix (collect_fun (length ls) ((to_fun d ls) ∘ p)%prg).
Proof. intros n m d ls p H0 H1 H2. 
  unfold collect_fun, to_fun, compose.
  rewrite Forall_forall. intros x H3.
  rewrite in_map_iff in H3.
  destruct H3 as [y [H3 H4]].
  rewrite <- H3.
  rewrite in_seq in H4.
  assert (y < length ls)%nat by lia.
  apply Forall_nth; auto.
  unfold permutation in H0.
  destruct H0 as [g H0].
  destruct (H0 y H5) as [H6 [H7 [H8 H9]]].
 auto.
Qed.

Lemma to_fun_collect_fun : forall {A : Type} (d : A) (len : nat) (f : nat -> A),
    forall i : nat, (i < len)%nat -> to_fun d (collect_fun len f) i = f i.
Proof. intros A d len f i H0. 
  unfold collect_fun, to_fun.
  rewrite nth_indep with (d' := f 0%nat).
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth; auto.
  rewrite map_length, seq_length; auto.
Qed.

Lemma to_fun_seq : forall (d len : nat),
    forall i : nat, (i < len)%nat -> to_fun d (List.seq 0%nat len) i = i.
Proof. intros. unfold to_fun. rewrite seq_nth; auto. Qed.

Lemma to_fun_seq_permutation : forall (d len : nat),
    permutation len (to_fun d (List.seq 0%nat len)).
Proof. intros d len.
  unfold permutation. exists idn.
  intros x H0. rewrite to_fun_seq; auto.
Qed.

Lemma collect_fun_idn_seq : forall (len : nat),
    collect_fun len idn = List.seq 0%nat len.
Proof. intros. unfold collect_fun. rewrite map_id. auto. Qed.

Lemma collect_fun_to_fun_map : 
  forall {A B : Type} (f : A -> B) (n : nat) (a : A) (l : list A) (p : nat -> nat),
    map f (collect_fun n (to_fun a l ∘ p)%prg) = 
       collect_fun n (to_fun (f a) (map f l) ∘ p)%prg.
Proof. intros A B f n a l p.
  unfold collect_fun, to_fun, compose.
  rewrite map_map. f_equal.
  apply functional_extensionality; intros.
  rewrite map_nth. auto.
Qed.

Lemma Permutation_permutation_nth : forall {A : Type} (l l' : list A) (d : A),
  Permutation l l' <->
    length l' = length l /\ 
      (exists f : nat -> nat, permutation (length l) f /\ 
                      (forall x : nat, (x < length l)%nat -> nth x l' d = nth (f x) l d)).
Proof. intros A l l' d.
  split; intros.
  - rewrite Permutation_nth in H0.
    destruct H0 as [H [f [H0 [H1 H2]]]].
    split; auto. exists f. split; auto.
    + unfold permutation.
      remember H1 as H1'. clear HeqH1'.
     rewrite FinFun.bInjective_bSurjective in H1'; auto.
     destruct (FinFun.bSurjective_bBijective H0 H1') as [g [H3 H4]].
     exists g. intros. repeat split.
      * unfold FinFun.bFun in H0; auto.
      * unfold FinFun.bFun in H3; auto.
      * destruct (H4 x H5); auto.
      * destruct (H4 x H5); auto.
  - rewrite Permutation_nth.
    destruct H0 as [H [f [H0 H1]]].
    split; auto. exists f. repeat split; auto.
    + unfold FinFun.bFun. intros.
      unfold permutation in H0.
      destruct H0 as [g H0].
      destruct (H0 x H2) as [H3 [H4 [H5 H6]]]. auto.
    + unfold FinFun.bInjective. intros.
      unfold permutation in H0.
      destruct H0 as [g H0].
      destruct (H0 x H2) as [H5 [H6 [H7 H8]]].  rewrite <- H7. 
      destruct (H0 y H3) as [H9 [H10 [H11 H12]]].  rewrite <- H11. 
      rewrite H4; auto.
Qed.  

Lemma Permutation_permutation_to_fun : forall {A : Type} (d : A) (l l' : list A),
    Permutation l l' <-> length l' = length l /\ 
                         (exists f : nat -> nat, permutation (length l) f /\ 
                                         (forall x : nat, (x < length l)%nat -> to_fun d l' x = (to_fun d l ∘ f)%prg x)).
Proof. intros A d l l'.
  rewrite Permutation_permutation_nth.
  split; intros; destruct H0 as [H0 [f [H1 H2]]]; split; auto; exists f ; split; auto.
  - intros. unfold to_fun, compose. apply H2; auto.
  - intros. unfold to_fun, compose in H2. apply H2; auto.
Qed.

Lemma Permutation_permutation_collect_fun : forall {A : Type} (d : A) (l l' : list A),
    Permutation l l' <-> length l' = length l /\ 
                         (exists f : nat -> nat, permutation (length l) f /\ 
                                         l' = collect_fun (length l) (to_fun d l ∘ f)%prg).
Proof. intros A d l l'.
  rewrite Permutation_permutation_to_fun.
  split; intros H0; destruct H0 as [H0 [f [H1 H2]]]; split; auto; exists f ; split; auto.
  - unfold collect_fun.
    apply nth_ext with (d := d) (d' := d).
    rewrite map_length, seq_length; auto.
    intros n H3. rewrite H0 in H3.
    setoid_rewrite nth_indep with (d' := (to_fun d l ∘ f)%prg 0%nat) at 2.
    rewrite map_nth. rewrite seq_nth; auto; simpl.
    unfold to_fun, compose. apply H2; auto.
    rewrite map_length, seq_length; auto.
  - intros. rewrite H2. rewrite to_fun_collect_fun; auto.
Qed.

Lemma perm_eq_permutation_swap : forall (n : nat) (f g : nat -> nat),
    perm_eq n f g -> (permutation n f <-> permutation n g).
Proof. intros n f g H0; split; intros H1.
  - unfold permutation in *.
    destruct H1 as [h H1].
    exists h. intros x H2.
    specialize (H1 x H2).
    destruct H1 as [H1 [H3 [H4 H5]]].
    repeat split; try rewrite <- H0; auto.
  - unfold permutation in *.
    destruct H1 as [h H1].
    exists h. intros x H2.
    specialize (H1 x H2).
    destruct H1 as [H1 [H3 [H4 H5]]].
    repeat split; try rewrite H0; auto.
Qed.

Lemma Permutation_permutation_seq : forall (n : nat) (orderlist : list nat),
    Permutation orderlist (List.seq 0%nat n) ->
    permutation n (to_fun 0%nat orderlist).
Proof. intros n orderlist H0.
  apply Permutation_sym in H0.
  rewrite Permutation_permutation_to_fun in H0.
  rewrite ! seq_length in H0.
  destruct H0 as [len [f [permf permeq]]].
  rewrite (perm_eq_permutation_swap n (to_fun 0%nat orderlist) (to_fun 0%nat (List.seq 0 n) ∘ f)%prg permeq).
  apply permutation_compose; auto.
  apply to_fun_seq_permutation.
Qed.

Module Import NatSort := Sort NatOrder.

Lemma sort_seq_Permutation : forall (l : list nat),
  sort l = (List.seq 0%nat (length l)) -> Permutation l (List.seq 0%nat (length l)).
Proof. intros l H0.
  rewrite <- H0.
  apply Permuted_sort.
Qed.

Lemma perm_inv_involutive : forall (n : nat) (p : nat -> nat),
    permutation n p ->
    perm_eq n p (perm_inv n (perm_inv n p)).
Proof. intros n p H0.
  apply permutation_inverse_injective with (f := perm_inv n p).
  apply perm_inv_permutation; auto.
  split. pose (perm_inv_is_linv_of_permutation n p H0); auto.
  pose (perm_inv_is_rinv_of_permutation n p H0); auto.
  pose (perm_inv_permutation n p H0) as H1.
  split. pose (perm_inv_is_rinv_of_permutation n (perm_inv n p) H1); auto.
  pose (perm_inv_is_linv_of_permutation n (perm_inv n p) H1); auto.
Qed.

Lemma collect_fun_perm_to_fun_involutive : forall {A : Type} (ls : list A) (d : A) (p : nat -> nat),
    permutation (length ls) p ->
    (collect_fun (length ls) (to_fun d ls ∘ p)%prg) = 
      (collect_fun (length ls) (to_fun d ls ∘ (perm_inv (length ls) (perm_inv (length ls) p)))%prg).
Proof. intros A ls d p H0.
  unfold collect_fun, to_fun, compose.
  pose (perm_inv_involutive (length ls) p H0) as H1.
  apply nth_ext with (d := (fun x : nat => nth (p x) ls d) 0%nat) (d' := (fun x : nat => nth (perm_inv (length ls) (perm_inv (length ls) p) x) ls d) 0%nat);
    rewrite ! map_length, ! seq_length; auto.
  intros. rewrite ! map_nth with (d := 0%nat).
  rewrite ! seq_nth; auto. simpl.
  rewrite H1; auto.
Qed.

Lemma perm_mat_inv : forall (n : nat) (p : nat -> nat),
  permutation n p ->
  perm_mat n (perm_inv n p) = (perm_mat n p)†.
Proof. intros n p H0.
  assert (I n × perm_mat n (perm_inv n p) = perm_mat n (perm_inv n p)).
  { rewrite Mmult_1_l; auto with wf_db. }
  rewrite <- H1.
  assert (I n × adjoint (perm_mat n p) = adjoint (perm_mat n p)).
  { rewrite Mmult_1_l; auto with wf_db. }
  rewrite <- H2.
  destruct (perm_mat_unitary n p H0).
  rewrite <- ! H4. rewrite ! Mmult_assoc.
  apply Mmult_inj_l.
  rewrite perm_mat_Mmult; try apply perm_inv_permutation;
    try apply perm_inv_bounded; auto.
  apply Minv_flip in H4; auto with wf_db.
  rewrite H4.
  assert (perm_eq n (p ∘ perm_inv n p)%prg idn).
  { unfold compose. pose (perm_inv_is_rinv_of_permutation n p H0); auto. }
  unfold perm_mat, I. prep_matrix_equality. bdestruct_all; simpl; auto. 
  all : rewrite H5 in H8; auto; try contradiction.
Qed.

Lemma perm_to_matrix_inv : forall (n : nat) (p : nat -> nat),
  permutation n p ->
  perm_to_matrix n (perm_inv n p) = (perm_to_matrix n p)†.
Proof. intros n p H0.
  assert (I (2 ^ n) × perm_to_matrix n (perm_inv n p) = perm_to_matrix n (perm_inv n p)).
  { rewrite Mmult_1_l; auto with wf_db. }
  rewrite <- H1.
  assert (I (2 ^ n) × adjoint (perm_to_matrix n p) = adjoint (perm_to_matrix n p)).
  { rewrite Mmult_1_l; auto with wf_db. }
  rewrite <- H2.
  destruct (perm_to_matrix_unitary n p H0).
  rewrite <- ! H4. rewrite ! Mmult_assoc.
  apply Mmult_inj_l.
  rewrite perm_to_matrix_Mmult; try apply perm_inv_permutation;  auto.
  apply Minv_flip in H4; auto with wf_db.
  rewrite H4.
  unfold perm_to_matrix.
  unfold perm_mat, I. prep_matrix_equality.
  bdestruct_all; simpl; auto.
  assert (qubit_perm_to_nat_perm n (perm_inv n p ∘ p)%prg y = y).
  { unfold qubit_perm_to_nat_perm, compose. 
    erewrite funbool_to_nat_eq.
    2: { intros x0 H9. rewrite perm_inv_is_linv_of_permutation; auto. }
    setoid_rewrite nat_to_funbool_inverse; auto. bdestruct_all; auto. }
  rewrite H9 in H7; contradiction.
  assert (qubit_perm_to_nat_perm n (perm_inv n p ∘ p)%prg y = y).
  { unfold qubit_perm_to_nat_perm, compose. 
    erewrite funbool_to_nat_eq.
    2: { intros x0 H9. rewrite perm_inv_is_linv_of_permutation; auto. }
    setoid_rewrite nat_to_funbool_inverse; auto. bdestruct_all; auto. }
  rewrite H9 in H7; contradiction.
Qed.

Local Coercion Nat.b2n : bool >-> nat.

Fixpoint ls_by_f_to_vec (n : nat) (ls : list (Square 2)) (f g : nat -> bool) : Vector 1 :=
  match n with 
  | 0%nat => I 1
  | Datatypes.S n' => 
      (ls_by_f_to_vec n' ls f g) ⊗ ( bra (f n') × (nth n' ls (I 2)) × (ket ( g n')))
  end.

Fixpoint ls_by_f_to_vec_list' (n : nat) (ls : list (Square 2)) (f g : nat -> bool) : list (Vector 1) :=
  match n with 
  | 0%nat => []
  | Datatypes.S n' => 
      ( bra (f n') × (nth n' ls (I 2)) × (ket ( g n'))) :: (ls_by_f_to_vec_list' n' ls f g)
  end.

Lemma WF_ls_by_f_to_vec_list' : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    Forall WF_Matrix ls -> Forall WF_Matrix (ls_by_f_to_vec_list' n ls f g).
Proof. intros n ls f g H0.
  induction n; auto. simpl.
  apply Forall_cons; auto.
  apply WF_mult; auto with wf_db.
  apply WF_mult; auto with wf_db.
  bdestruct (n <? length ls).
  - apply Forall_nth; auto.
  - rewrite nth_overflow; auto with wf_db.
Qed.

Definition ls_by_f_to_vec_list (n : nat) (ls : list (Square 2)) (f g : nat -> bool) := rev (ls_by_f_to_vec_list' n ls f g).

Lemma WF_ls_by_f_to_vec_list : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    Forall WF_Matrix ls -> Forall WF_Matrix (ls_by_f_to_vec_list n ls f g).
Proof. intros n ls f g H0.
  unfold ls_by_f_to_vec_list. apply Forall_rev. apply WF_ls_by_f_to_vec_list'; auto.
Qed.

Lemma ls_by_f_to_vec_list'_length : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    length (ls_by_f_to_vec_list' n ls f g) = n.
Proof. intros n ls f g.
  induction n; auto. simpl. auto.
Qed.

Lemma ls_by_f_to_vec_list_length : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    length (ls_by_f_to_vec_list n ls f g) = n.
Proof. intros n ls f g. unfold ls_by_f_to_vec_list. rewrite rev_length. rewrite ls_by_f_to_vec_list'_length. auto.
Qed.

Lemma ls_by_f_to_vec_list'_firstn : forall (n m : nat) (ls : list (Square 2)) (f g : nat -> bool),
    (n <= length ls)%nat -> (n <= m)%nat ->
    ls_by_f_to_vec_list' n ls f g = ls_by_f_to_vec_list' n (firstn m ls) f g.
Proof. intros n m ls f g H0 H1. 
  gen m f g ls. induction n; intros; auto.
  simpl. f_equal. f_equal. f_equal. rewrite nth_firstn; try lia. auto.
  rewrite IHn with (m := m); try lia. auto.
Qed.

Lemma ls_by_f_to_vec_list'_perm_eq : forall (n : nat) (ls : list (Square 2)) (f f' g g' : nat -> bool),
    perm_eq n f f' -> perm_eq n g g' ->
    ls_by_f_to_vec_list' n ls f g = ls_by_f_to_vec_list' n ls f' g'.
Proof. intros n ls f f' g g' H0 H1.
  induction n; auto.
  simpl. f_equal.
  rewrite H0, H1; try lia; auto.
  apply IHn; unfold perm_eq; intros.
  rewrite H0; auto; lia.
  rewrite H1; auto; lia.
Qed.

Lemma nth_ls_by_f_to_vec_list' : forall (k n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    (k < n)%nat ->
    nth k (ls_by_f_to_vec_list' n ls f g) (I 1) = ( bra (f (n - S k)%nat) × (nth (n - S k)%nat ls (I 2)) × (ket ( g (n - S k)%nat))).
Proof. intros k n ls f g H0. gen k. induction n; intros. simpl. inversion H0.
  induction k. simpl. replace (n - 0)%nat with n by lia. auto.
  assert (k < n)%nat by lia. clear H0.
  replace (S n - S k)%nat with (n - k)%nat in * by lia.
  replace (S n - S (S k))%nat with (n - S k)%nat in * by lia.
  simpl. auto.
Qed.

Lemma nth_ls_by_f_to_vec_list : forall (k n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    (k < n)%nat ->
    nth k (ls_by_f_to_vec_list n ls f g) (I 1) = ( bra (f k) × (nth k ls (I 2)) × (ket ( g k))).
Proof. intros k n ls f g H0. unfold  ls_by_f_to_vec_list. rewrite rev_nth. 2: rewrite ls_by_f_to_vec_list'_length; auto.
  rewrite ls_by_f_to_vec_list'_length. rewrite nth_ls_by_f_to_vec_list'.
  2: lia. replace (n - S (n - S k))%nat with (k) by lia. auto.
Qed.


Lemma ls_by_f_to_vec_list_iff : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    Forall WF_Matrix ls ->
    big_kron (ls_by_f_to_vec_list n ls f g) = ls_by_f_to_vec n ls f g.
Proof. intros n ls f g H.
  induction n; auto. unfold ls_by_f_to_vec_list in *. simpl. rewrite big_kron_app. 
  2: { intros. bdestruct (i <? n)%nat.
       - rewrite rev_nth. 
           all: rewrite ls_by_f_to_vec_list'_length; auto.
           pose (WF_ls_by_f_to_vec_list' n ls f g H) as E.
           apply Forall_nth; auto; rewrite ls_by_f_to_vec_list'_length; lia.
       - rewrite nth_overflow; auto with wf_db.
         rewrite rev_length, ls_by_f_to_vec_list'_length; lia. }
  2: { intros. bdestruct (i =? 0)%nat; subst.
       - simpl. apply WF_mult; auto with wf_db.
         apply WF_mult; auto with wf_db.
         bdestruct (n <? length ls)%nat.
         + apply Forall_nth; auto.
         + rewrite nth_overflow; auto with wf_db.
       - rewrite nth_overflow; auto with wf_db; simpl; lia. }
  rewrite IHn. f_equal. 
  1-2: rewrite Nat.pow_1_l; auto.
  simpl. rewrite kron_1_r. auto.
Qed.

Lemma ls_by_f_to_vec_S : forall (n : nat) (ls : list (Square 2)) (f g : nat -> bool),
    (n >= length ls)%nat ->
    ls_by_f_to_vec (Datatypes.S n) ls f g = ls_by_f_to_vec n ls f g ⊗ (bra (f n) × ket (g n)).
Proof. intros n ls f g H0.
  simpl. rewrite nth_overflow; auto. rewrite Mmult_1_r; auto with wf_db.
Qed.

Lemma big_kron_Permutation : forall (ls ls' : list (Vector 1)),
    Forall WF_Matrix ls ->
    Permutation ls ls' -> big_kron ls = big_kron ls'.
Proof. intros ls ls' H0 H1.  induction H1; auto; simpl. 
  - rewrite IHPermutation. f_equal. 
    1-2: rewrite ! Nat.pow_1_l; auto.
    rewrite Forall_cons_iff in H0; destruct H0; auto.
  - rewrite Forall_cons_iff in H0; destruct H0.
    rewrite Forall_cons_iff in H1; destruct H1.
    unfold kron. prep_matrix_equality. rewrite ! Nat.pow_1_l. rewrite ! Nat.add_0_r. simpl. 
    rewrite ! divmod_0. rewrite ! Cmult_assoc. f_equal. 
    bdestruct (x0 =? 0)%nat; subst.
    + bdestruct (y0 =? 0)%nat; subst; try lca.
      rewrite H0; try lia. rewrite Cmult_0_l. rewrite H1; try lia. lca.
    + rewrite H0; try lia. rewrite Cmult_0_l. rewrite H1; try lia. lca.
  - rewrite IHPermutation1; auto. apply IHPermutation2.
    rewrite Forall_forall. intros.
    apply Permutation_sym in H1_.
    apply (Permutation_in x H1_) in H1.
    rewrite Forall_forall in H0. apply H0; auto.
Qed.

Lemma ls_by_f_to_vec_permutation : forall (ls : list (Square 2)) (f g : nat -> bool) (p : nat -> nat),
    Forall WF_Matrix ls ->
    permutation (length ls) p -> 
    ls_by_f_to_vec (length ls) ls (f ∘ p)%prg (g ∘ p)%prg = 
      ls_by_f_to_vec (length ls) (collect_fun (length ls) ((to_fun (I 2) ls) ∘ (perm_inv (length ls) p))%prg) f g.
Proof. intros ls f g p H H0.
  unfold collect_fun, to_fun, compose.
  rewrite <- ! ls_by_f_to_vec_list_iff; auto.
  apply big_kron_Permutation. 
  apply WF_ls_by_f_to_vec_list; auto.
  rewrite Permutation_permutation_nth. split. 
  rewrite ! ls_by_f_to_vec_list_length; auto.
  exists (perm_inv (length ls) p). split. 
  rewrite ls_by_f_to_vec_list_length; apply perm_inv_permutation; auto.
  intros. 
  rewrite ! ls_by_f_to_vec_list_length in *.
  rewrite ! nth_ls_by_f_to_vec_list; auto. 
  2: { pose (perm_inv_permutation (length ls) p H0) as E.
       unfold permutation in E.
       destruct E as [pinv H2].
       destruct (H2 x H1) as [H3 [H4 [H5 H6]]].
       auto. }
  2: { rewrite Forall_forall. intros.
       rewrite in_map_iff in H1.
       destruct H1 as [y [H1 H2]].
       rewrite <- H1.
       apply Forall_nth; auto.
       rewrite in_seq in H2.
       pose (perm_inv_permutation (length ls) p H0) as E.
       unfold permutation in E.
       destruct E as [pinv H3]. assert (y < length ls)%nat by lia.
       destruct (H3 y H4) as [H5 [H6 [H7 H8]]].
       auto. }
  assert ((p (perm_inv (length ls) p x)) = x). 
  { rewrite perm_inv_is_rinv_of_permutation; auto. }
  rewrite ! H2. f_equal. f_equal.
  rewrite nth_indep with (d' := (fun x0 : nat => nth (perm_inv (length ls) p x0) ls (I 2)) 0%nat).
  2: rewrite map_length, seq_length; auto.
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth; auto.
Qed.

Lemma ls_by_f_to_vec_by_f_to_vec_rev : forall (ls : list (Square 2)) (f g : nat -> bool),
    Forall WF_Matrix ls ->
 (ls_by_f_to_vec (length ls) (rev ls) f g) = (f_to_vec (length ls) f) † × (big_kron (rev ls)) × (f_to_vec (length ls) g).
Proof. intros ls f g H.
  induction ls. simpl. lma'.
  rewrite <- ! ls_by_f_to_vec_list_iff in *. unfold ls_by_f_to_vec_list in *.
  simpl. rewrite big_kron_app. 
  5: apply Forall_rev; auto.
  4: apply Forall_rev; rewrite Forall_cons_iff in H; destruct H; auto.
  2: { rewrite ls_by_f_to_vec_list'_firstn with (m := length ls); auto.
       2: rewrite app_length; simpl; rewrite rev_length; lia.
       intros. rewrite firstn_app. rewrite rev_length.
       replace (length ls - length ls)%nat with 0%nat by lia. simpl. 
       rewrite app_nil_r. rewrite firstn_all2; try rewrite rev_length; try lia.
       bdestruct (i <? length ls).
       - rewrite rev_nth. all: rewrite ls_by_f_to_vec_list'_length; auto.
         rewrite Forall_cons_iff in H; destruct H.
         assert (Forall WF_Matrix (rev ls)). { apply Forall_rev; auto. }
         pose (WF_ls_by_f_to_vec_list' (length ls) (rev ls) f g H3) as E.
         apply Forall_nth; try rewrite ls_by_f_to_vec_list'_length; auto; lia.
       - rewrite nth_overflow; auto with wf_db.
         rewrite rev_length, ls_by_f_to_vec_list'_length; lia. }
  2: { intros. bdestruct (i =? 0)%nat; subst.
       - simpl. apply WF_mult; auto with wf_db.
         apply WF_mult; auto with wf_db. 
         rewrite app_nth2; rewrite rev_length; try lia.
         replace (length ls - length ls)%nat with 0%nat by lia. simpl.
         rewrite Forall_cons_iff in H; destruct H; auto.
       - rewrite nth_overflow; auto with wf_db. simpl. lia. }
  simpl. rewrite big_kron_app. 
  2: { intros. bdestruct (i <? length ls).
       - rewrite rev_nth; auto.
         rewrite Forall_cons_iff in H; destruct H.
         apply Forall_nth; auto; lia.
       - rewrite nth_overflow; auto with wf_db.
         rewrite rev_length; lia. }
  2: { intros. bdestruct (i =? 0)%nat; subst.
       - simpl. rewrite Forall_cons_iff in H; destruct H; auto.
       - rewrite nth_overflow; auto with wf_db. simpl. lia. }
  simpl. rewrite ! kron_1_r.
  setoid_rewrite kron_adjoint. 
  setoid_rewrite Mmult_assoc.
  setoid_rewrite kron_mixed_product'; try rewrite rev_length; simpl; auto; try lia.
  setoid_rewrite kron_mixed_product'; try rewrite rev_length; simpl; auto; try lia.
  assert ((ls_by_f_to_vec_list' (length ls) (rev ls ++ [a]) f g) =
            (ls_by_f_to_vec_list' (length ls) (rev ls) f g)).
  { rewrite ls_by_f_to_vec_list'_firstn with (m := length ls) at 1. 
    rewrite firstn_app, ! rev_length.
    replace (length ls - length ls)%nat with 0%nat by lia. simpl. rewrite app_nil_r.
    rewrite firstn_all2; try rewrite rev_length; try lia; auto.
    rewrite app_length, rev_length; simpl. all: lia. }
  rewrite H0. rewrite Forall_cons_iff in H; destruct H. rewrite IHls; auto. f_equal.
  1-2: rewrite Nat.pow_1_l; auto.
  rewrite Mmult_assoc; auto.
  rewrite app_nth2; try rewrite rev_length; try lia.
  replace (length ls - length ls)%nat with 0%nat by lia. simpl. f_equal.
  destruct (f (length ls)); lma'.
Qed.

Lemma ls_by_f_to_vec_by_f_to_vec : forall (ls : list (Square 2)) (f g : nat -> bool),
    Forall WF_Matrix ls ->
    (ls_by_f_to_vec (length ls) ls f g) = (f_to_vec (length ls) f) † × (big_kron ls) × (f_to_vec (length ls) g).
Proof. intros ls f g H0. 
  rewrite <- (rev_involutive ls).
  rewrite rev_length.
  rewrite ls_by_f_to_vec_by_f_to_vec_rev; auto.
  apply Forall_rev; auto.
Qed.


Lemma permute_kron_rev : forall (ls : list (Square 2)) (p : nat -> nat),
    Forall WF_Matrix (rev ls) ->
    permutation (length (rev ls)) p -> 
    (big_kron (rev ls)) =
      (perm_to_matrix (length (rev ls)) p)† × big_kron (collect_fun (length (rev ls)) ((to_fun (I 2) (rev ls)) ∘ p)%prg) × (perm_to_matrix (length (rev ls)) p).
Proof. intros ls p H0 H1.
  apply equal_by_basis_states_implies_equal.
  apply WF_big_kron'; rewrite <- Forall_forall; auto.
  apply WF_mult; auto with wf_db. apply WF_mult; auto with wf_db.
  pose (WF_big_kron' 2 2 (collect_fun (length (rev ls)) (to_fun (I 2) (rev ls) ∘ p)%prg)) as E. 
  rewrite ! collect_fun_length in E. apply E. rewrite <- Forall_forall.
  apply WF_collect_fun_perm_to_fun; auto with wf_db.
  intros f g.
  rewrite ! Mmult_assoc. rewrite perm_to_matrix_permutes_qubits; auto.
  rewrite <- ! Mmult_assoc. rewrite <- Mmult_adjoint.
  rewrite perm_to_matrix_permutes_qubits; auto.
  rewrite <- ls_by_f_to_vec_by_f_to_vec; auto.
  assert ((collect_fun (length (rev ls)) (to_fun (I 2) (rev ls) ∘ p)%prg) = 
            (collect_fun (length (rev ls)) (to_fun (I 2) (rev ls) ∘ (perm_inv (length (rev ls)) (perm_inv (length (rev ls)) p)))%prg)).
  { rewrite collect_fun_perm_to_fun_involutive; auto. }
  rewrite H2.
  assert (adjoint (f_to_vec (length (rev ls)) (fun x : nat => f (p x))) = adjoint (f_to_vec (length (collect_fun (length (rev ls))
         (to_fun (I 2) (rev ls) ∘ perm_inv (length (rev ls)) (perm_inv (length (rev ls)) p))%prg)) (f ∘ p)%prg)).
  { rewrite collect_fun_length. unfold compose. auto. }
  rewrite H3.
  assert (f_to_vec (length (rev ls)) (fun x : nat => g (p x)) = f_to_vec (length (collect_fun (length (rev ls))
         (to_fun (I 2) (rev ls) ∘ perm_inv (length (rev ls)) (perm_inv (length (rev ls)) p))%prg)) (g ∘ p)%prg).
  { rewrite collect_fun_length. unfold compose. auto. }
  rewrite H4.
  pose (ls_by_f_to_vec_by_f_to_vec (collect_fun (length (rev ls))
             (to_fun (I 2) (rev ls) ∘ perm_inv (length (rev ls)) (perm_inv (length (rev ls)) p))%prg) (f ∘ p)%prg (g ∘ p)%prg) as E.
  rewrite collect_fun_length in *.
  rewrite <- E. rewrite <- ls_by_f_to_vec_permutation; auto.
  rewrite <- ! ls_by_f_to_vec_list_iff; auto.
  unfold ls_by_f_to_vec_list. do 2 f_equal.
  apply ls_by_f_to_vec_list'_perm_eq.
  - intros. unfold compose. 
    pose (perm_inv_is_rinv_of_permutation (length (rev ls)) p H1) as H5.
    unfold perm_eq; intros. rewrite H5; lia.
  - intros. unfold compose. 
    pose (perm_inv_is_rinv_of_permutation (length (rev ls)) p H1) as H5.
    unfold perm_eq; intros. rewrite H5; lia.
  - apply perm_inv_permutation; auto.
  - apply WF_collect_fun_perm_to_fun; auto with wf_db.
    do 2 apply perm_inv_permutation; auto.
  - apply permutation_is_bounded; auto.
  - apply permutation_is_bounded; auto.
Qed.

Lemma permute_kron : forall (ls : list (Square 2)) (p : nat -> nat),
    Forall WF_Matrix ls ->
    permutation (length ls) p -> 
    (big_kron ls) =
      (perm_to_matrix (length ls) p)† × big_kron (collect_fun (length ls) ((to_fun (I 2) ls) ∘ p)%prg) × (perm_to_matrix (length ls) p).
Proof. intros ls p H0 H1.
  assert (rev (rev ls) = ls). { rewrite rev_involutive; auto. }
  rewrite <- H2 in *.
  apply permute_kron_rev; rewrite rev_involutive in *; auto.
Qed.

Lemma permute_kron_inv : forall (ls : list (Square 2)) (p : nat -> nat),
    Forall WF_Matrix ls ->
    permutation (length ls) p -> 
    (perm_to_matrix (length ls) p) × (big_kron ls) × (perm_to_matrix (length ls) p) † =
      big_kron (collect_fun (length ls) ((to_fun (I 2) ls) ∘ p)%prg).
Proof. intros ls p H0 H1.
  rewrite permute_kron with (p := p); auto.
  destruct (perm_to_matrix_unitary (length ls) p H1).
  apply Minv_flip in H3; auto with wf_db.
  rewrite ! Mmult_assoc, H3, Mmult_1_r.
  rewrite <- ! Mmult_assoc, H3, Mmult_1_l. auto.
  - pose (WF_big_kron' 2 2 (collect_fun (length ls) (to_fun (I 2) ls ∘ p)%prg)) as E.
    rewrite ! collect_fun_length in E. apply E.
    rewrite <- Forall_forall. apply WF_collect_fun_perm_to_fun; auto with wf_db.
  - pose (WF_big_kron' 2 2 (collect_fun (length ls) (to_fun (I 2) ls ∘ p)%prg)) as E.
    rewrite ! collect_fun_length in E. apply E.
    rewrite <- Forall_forall. apply WF_collect_fun_perm_to_fun; auto with wf_db.
Qed.




Definition ExtendQubitsToRight {n : nat} (Lt1 : list (TType n)) (m : nat) :=
  (map (uncurry gTensorT) (combine Lt1 (repeat (defaultT_I m) (length Lt1)))).

Lemma ExtendQubitsToRight_length : forall {n : nat} (Lt1 : list (TType n)) (m : nat),
    length (ExtendQubitsToRight Lt1 m) = length Lt1.
Proof. intros n Lt1 m.
  unfold ExtendQubitsToRight.
  rewrite map_length, combine_length, repeat_length.
  minmax_breakdown. auto.
Qed.

Lemma ExtendQubitsToRight_nil : forall {n m : nat},
    @ExtendQubitsToRight n [] m = [].
Proof. intros. unfold ExtendQubitsToRight. auto. Qed.

Lemma ExtendQubitsToRight_zero : forall {n : nat} (Lt1 : list (TType n)),
    ExtendQubitsToRight Lt1 0%nat = Lt1.
Proof. intros n Lt1.
  unfold ExtendQubitsToRight.
  unfold defaultT_I. simpl.
  apply nth_ext with (d := (uncurry gTensorT) (defaultT_I n, (C1, []))) (d' := defaultT_I n).
  rewrite map_length, combine_length, repeat_length. minmax_breakdown. auto.
  intros n0 H0.
  rewrite ! map_nth. rewrite combine_nth. rewrite nth_repeat.
  unfold uncurry. simpl. unfold gTensorT. 
  replace (n+0)%nat with n by lia.
  destruct (nth n0 Lt1 (defaultT_I n)) eqn:E.
  rewrite Cmult_1_r, app_nil_r; auto.
  rewrite repeat_length; auto.
Qed.

Definition ExtendQubitsToLeft {m : nat} (Lt2 : list (TType m)) (n : nat) :=
  (map (uncurry gTensorT) (combine (repeat (defaultT_I n) (length Lt2)) Lt2)).

Lemma ExtendQubitsToLeft_length : forall {m : nat} (Lt2 : list (TType m)) (n : nat),
    length (ExtendQubitsToLeft Lt2 n) = length Lt2.
Proof. intros m Lt2 n.
  unfold ExtendQubitsToLeft.
  rewrite map_length, combine_length, repeat_length.
  minmax_breakdown. auto.
Qed.

Lemma ExtendQubitsToLeft_nil : forall {m n : nat},
    @ExtendQubitsToLeft m [] n = [].
Proof. intros. unfold ExtendQubitsToLeft. auto. Qed.

Lemma ExtendQubitsToLeft_zero : forall {m : nat} (Lt2 : list (TType m)),
    ExtendQubitsToLeft Lt2 0%nat = Lt2.
Proof. intros m Lt2.
  unfold ExtendQubitsToLeft.
  unfold defaultT_I. simpl.
  apply nth_ext with (d := (uncurry gTensorT) ((C1, []) : TType 0%nat, defaultT_I m)) (d' := defaultT_I m).
  rewrite map_length, combine_length, repeat_length. minmax_breakdown. auto.
  intros n0 H0.
  rewrite ! map_nth. rewrite combine_nth. rewrite nth_repeat.
  unfold uncurry. simpl. unfold gTensorT. 
  replace (0+m)%nat with m by lia.
  destruct (nth n0 Lt2 (defaultT_I m)) eqn:E.
  rewrite Cmult_1_l; auto.
  rewrite repeat_length; auto.
Qed.

Definition DiagonalTwice {n m : nat} (Lt1 : list (TType n)) (Lt2 : list (TType m)) :=
  (ExtendQubitsToRight Lt1 m) ++ (ExtendQubitsToLeft Lt2 n).

Lemma DiagonalTwice_length : forall {n m : nat} (Lt1 : list (TType n)) (Lt2 : list (TType m)),
    length Lt1 = n -> length Lt2 = m ->
    length (DiagonalTwice Lt1 Lt2) = (n + m)%nat.
Proof. intros n m Lt1 Lt2 H0 H1. 
  unfold DiagonalTwice.
  rewrite app_length.
  rewrite ExtendQubitsToRight_length, ExtendQubitsToLeft_length.
  lia.
Qed.

Fixpoint DiagonalQubits (Ln : list nat) (LLT : list (list TTypes)) : list (TType (fold_right Nat.add 0%nat Ln)) :=
  match Ln, LLT with
  | [], _ => ([] : list (TType 0%nat))
  | _, [] => ([] : list (TType 0%nat))
  | (n :: Ln'), (LT :: LLT') => DiagonalTwice (map (AssignT n) LT) (DiagonalQubits Ln' LLT')
  end.

Lemma DiagonalQubits_length : forall (Ln : list nat) (LLT : list (list TTypes)),
    length Ln = length LLT -> Forall2 (fun n LT => length LT = n) Ln LLT ->
    length (DiagonalQubits Ln LLT) = (fold_right Nat.add 0%nat Ln).
Proof. intros Ln LLT H0 H1. 
  gen Ln. induction LLT; intros.
  - destruct Ln; try discriminate. simpl. auto.
  - destruct Ln; try discriminate. simpl in *.
    apply Nat.succ_inj in H0.
    inversion H1; subst. clear H1.
    rewrite DiagonalTwice_length; auto.
    rewrite map_length; auto.
Qed.                                    



Lemma commutingListT_app : forall {n : nat} (Lt1 Lt2 : list (TType n)),
    commutingListT (Lt1 ++ Lt2) -> commutingListT Lt1 /\ commutingListT Lt2.
Proof. intros n Lt1 Lt2 H0. split.
  - unfold commutingListT in *.
    intros t1 t2 H1 H2.
    assert (In t1 (Lt1 ++ Lt2)).
    { rewrite in_app_iff. left; auto. }
    assert (In t2 (Lt1 ++ Lt2)).
    { rewrite in_app_iff. left; auto. }
    apply H0; auto.
  - unfold commutingListT in *.
    intros t1 t2 H1 H2.
    assert (In t1 (Lt1 ++ Lt2)).
    { rewrite in_app_iff. right; auto. }
    assert (In t2 (Lt1 ++ Lt2)).
    { rewrite in_app_iff. right; auto. }
    apply H0; auto.
Qed.




(*** Functions for Separability Computation ***)
(** ith qubit has pivot **)
Definition has_pivot (n i : nat) (LLp : list (list Pauli)) : bool :=
  negb (forallb (fun p => POrd.eqb p gI) (map (fun Lp => nth i Lp gI) LLp)).

(** i := n = # of qubits
    m := length LLp = # of terms **)
Fixpoint get_pivots_loop (n m i : nat) (LLp : list (list Pauli)) (term_qubit : list (nat * nat)) {struct i} : list (nat * nat) :=
  match i with
  | 0%nat => rev term_qubit
  | Datatypes.S i' => if has_pivot n (n - i) LLp
                     then match LLp with
                          | [] => rev term_qubit
                          | _ :: L => get_pivots_loop n m i' L (((m - (length LLp)), (n - i))%nat :: term_qubit)
                          end
                     else get_pivots_loop n m i' LLp term_qubit
  end.

Definition get_pivots (n : nat) (LLp : list (list Pauli)) := 
  get_pivots_loop n (length LLp) n LLp [].

Definition all_pivots (K : list nat) (term_qubit : list (nat * nat)) :=
  forallb (fun k => (existsb (fun pivot => Nat.eqb pivot k) (map snd term_qubit))) K.

Definition commute (Lp1 Lp2 : list Pauli) :=
  Nat.even (length (filter (fun p =>
                              (andb
                                 (negb (orb
                                          (POrd.eqb (fst p) gI)
                                          (POrd.eqb (snd p) gI)))
                                 (negb (POrd.eqb (fst p) (snd p))))) 
                      (combine Lp1 Lp2))).

Definition commutativity_condition (n : nat) (LLp : list (list Pauli)) (K : list nat) :=
  forallb (fun p => commute 
                   (nth (hd 0%nat K) LLp (repeat gI n))
                   (nth p LLp (repeat gI n)))
    (tl K).

Definition check_complement (n : nat) (LLp : list (list Pauli)) (K : list nat) (term_qubit : list (nat * nat)) := 
  forallb (fun p =>
             forallb (fun i =>
                        POrd.eqb (nth i (nth (fst p) LLp (repeat gI n)) gI) gI
               ) (filter (fun a => negb (existsb (fun k => Nat.eqb k a) K)) (List.seq 0 n))
    ) (filter (fun p => existsb (fun k => Nat.eqb k (snd p)) K) term_qubit).

Definition separable {n : nat} (L : list (TType n)) (K : list nat) :=
  let LLp := map snd L in
  let term_qubit := get_pivots n LLp in
  all_pivots K term_qubit && 
    commutativity_condition n LLp K &&
    check_complement n LLp K term_qubit.

Definition separable_all {n : nat} (L : list (TType n)) (LK : list (list nat)) :=
  forallb (separable L) LK.


Fixpoint get_pivot_loop {n : nat} (L : list (TType n)) (k : nat) (term_qubit : list (nat * nat)) : nat :=
  match term_qubit with
  | [] => 0%nat
  | (term, qubit) :: t => if Nat.eqb k qubit then term else get_pivot_loop L k t
  end. 

Definition get_pivot {n : nat} (L : list (TType n)) (k : nat) : nat :=
  let LLp := map snd L in
  let term_qubit := get_pivots n LLp in
  get_pivot_loop L k term_qubit.


Fixpoint separate_loop {n : nat} (lt : list (TType n)) (input : list (list nat)) (acc : (list nat) * (list (list TTypes)) * (list nat)) : (list nat) * (list (list TTypes)) * (list nat) :=
  match input with
  | h :: t => separate_loop lt t 
         ((length h) :: (fst (fst acc)), 
           (map (fun k => ForgetT (unpad_Sep_TType (nth (get_pivot lt k) lt (defaultT_I n)) h)) h) :: (snd (fst acc)), 
           snd acc)
  | [] => (rev (fst (fst acc)), rev (snd (fst acc)), snd acc)
  end.

Definition separate {n : nat} (lt : list (TType n)) (input : list (list nat)) :=
  separate_loop lt input ([], [], fold_right (@app nat) [] input).
