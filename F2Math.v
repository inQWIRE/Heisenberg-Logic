Require Export QuantumLib.GenSubspaces.


(** ** mathematics for semantical proof of separability ** **)

Declare Scope F2_scope.
Delimit Scope F2_scope with F2.
Local Open Scope F2_scope.

Inductive F2 : Type := zero | one.
Notation "0" := zero : F2_scope.
Notation "1" := one : F2_scope.

Definition F2plus (z1 z2 : F2) : F2 := 
  match z1, z2 with
  | zero, zero => zero
  | zero, one => one
  | one, zero => one
  | one, one => zero
  end.
Infix "+" := F2plus (at level 50, left associativity) : F2_scope.

Lemma F2plus_0_l : forall z : F2, 0 + z = z. Proof. intros; destruct z; auto. Qed.
Lemma F2plus_0_r : forall z : F2, z + 0 = z. Proof. intros; destruct z; auto. Qed.
Lemma F2plus_assoc : forall z1 z2 z3 : F2, 
    z1 + (z2 + z3) = (z1 + z2) + z3.
Proof. intros; destruct z1, z2, z3; auto. Qed.
Lemma F2plus_flip_l_0 : forall z : F2, 1 + z = 0 -> z = 1. Proof. intros; destruct z; auto. Qed.
Lemma F2plus_flip_l_1 : forall z : F2, 1 + z = 1 -> z = 0. Proof. intros; destruct z; auto. Qed.
Lemma F2plus_flip_r_0 : forall z : F2, z + 1 = 0 -> z = 1. Proof. intros; destruct z; auto. Qed.
Lemma F2plus_flip_r_1 : forall z : F2, z + 1 = 1 -> z = 0. Proof. intros; destruct z; auto. Qed.

#[global] Instance F2_is_monoid : Monoid F2 := 
  { Gzero := zero;
    Gplus := F2plus;
    Gplus_0_l := F2plus_0_l;
    Gplus_0_r := F2plus_0_r;
    Gplus_assoc := F2plus_assoc }.

(* Definition F2_is_monoid : Monoid F2 := 
  Build_Monoid F2 zero F2plus F2plus_0_l F2plus_0_r F2plus_assoc. *)

Existing Instance F2_is_monoid.

Definition F2opp (z : F2) : F2 := z.
Notation "- z" := (F2opp z) : F2_scope.

Definition F2minus (z1 z2 : F2) : F2 := z1 + (- z2).
Infix "-" := F2minus (at level 50, left associativity) : F2_scope.

Lemma F2opp_l : forall z : F2, - z + z = 0. Proof. intros; destruct z; auto. Qed.
Lemma F2opp_r : forall z : F2, z + (- z) = 0. Proof. intros; destruct z; auto. Qed.
Definition F2_is_group : Group F2 := 
  Build_Group F2 F2_is_monoid F2opp F2opp_l F2opp_r.

Existing Instance F2_is_group.

Lemma F2plus_comm : forall z1 z2 : F2, z1 + z2 = z2 + z1. 
Proof. intros; destruct z1, z2; auto. Qed.
Definition F2_is_comm_group : Comm_Group F2 := 
  Build_Comm_Group F2 F2_is_monoid F2_is_group F2plus_comm.

Existing Instance F2_is_comm_group.

Definition F2mult (z1 z2 : F2) : F2 := 
  match z1, z2 with
  | zero, zero => zero
  | zero, one => zero
  | one, zero => zero
  | one, one => one
  end.
Infix "·" := F2mult (at level 40, left associativity) : F2_scope.
Lemma F2mult_1_l : forall z : F2, 1 · z = z. Proof. intros; destruct z; auto. Qed.
Lemma F2mult_1_r : forall z : F2, z · 1 = z. Proof. intros; destruct z; auto. Qed.
Lemma F2mult_assoc : forall z1 z2 z3, z1 · (z2 · z3) = (z1 · z2) · z3.
Proof. intros; destruct z1, z2, z3; auto. Qed.
Lemma F2mult_plus_distr_l : forall z1 z2 z3, z3 · (z1 + z2) = (z3 · z1) + (z3 · z2).
Proof. intros; destruct z1, z2, z3; auto. Qed.
Lemma F2mult_plus_distr_r : forall z1 z2 z3, (z1 + z2) · z3 = (z1 · z3) + (z2 · z3).
Proof. intros; destruct z1, z2, z3; auto. Qed.
Lemma F2eq_dec : forall z1 z2 : F2, { z1 = z2 } + { z1 <> z2 }.
Proof. intros; destruct z1, z2; auto; try (left; easy); try (right; easy). Qed.    
Definition F2_is_ring : Ring F2 :=
  Build_Ring F2 F2_is_monoid F2_is_group F2_is_comm_group one F2mult
             F2mult_1_l F2mult_1_r F2mult_assoc F2mult_plus_distr_l F2mult_plus_distr_r
             F2eq_dec.

Existing Instance F2_is_ring.

Lemma F2mult_comm : forall z1 z2 : F2, F2mult z1 z2 = F2mult z2 z1.
Proof. intros; destruct z1, z2; auto. Qed.
Definition F2_is_comm_ring : Comm_Ring F2 :=
  Build_Comm_Ring F2 F2_is_monoid F2_is_group F2_is_comm_group F2_is_ring
                  F2mult_comm.

Existing Instance F2_is_comm_ring.

Lemma F2_ring_theory : ring_theory 0%F2 1%F2 F2plus F2mult F2minus F2opp eq.
Proof. apply (@G_ring_theory F2 F2_is_monoid F2_is_group F2_is_comm_group F2_is_ring F2_is_comm_ring). Qed.

Add Ring F_ring_ring : F2_ring_theory.

Definition F2inv (z : F2) : F2 := z.
Notation "/ z" := (F2inv z) : F2_scope.

Definition F2div (z1 z2 : F2) : F2 := z1 · (/ z2).
Lemma F2_1_neq_0 : 1 <> 0. Proof. intro. discriminate. Qed.
Lemma F2inv_r : forall z : F2, z <> 0 -> z · (/ z) = 1. Proof. intros; destruct z; auto; contradiction. Qed.
Definition F2_is_field : Field F2 := 
  Build_Field F2 F2_is_monoid F2_is_group F2_is_comm_group F2_is_ring
              F2_is_comm_ring F2inv F2_1_neq_0 F2inv_r.

Existing Instance F2_is_field.

Lemma F2_field_theory : field_theory 0%F2 1%F2 F2plus F2mult F2minus F2opp F2div F2inv eq.
Proof. apply (@G_field_theory F2 F2_is_monoid F2_is_group F2_is_comm_group F2_is_ring F2_is_comm_ring F2_is_field). Qed.

Add Field F_field : F2_field_theory.

Lemma F2mult_0_l : forall z : F2, 0 · z = 0. Proof. intros; destruct z; auto. Qed.
Lemma F2mult_0_r : forall z : F2, z · 0 = 0. Proof. intros; destruct z; auto. Qed.
Definition F2_beq (z1 z2 : F2) : bool :=
  match z1, z2 with
  | zero, zero => true
  | zero, one => false
  | one, zero => false
  | one, one => true
  end.
Infix "=?" := F2_beq : F2_scope.
Lemma F2_beq_true_iff : forall z1 z2 : F2, (z1 =? z2)%F2 = true <-> z1 = z2.
Proof. intros z1 z2. split; intros;  destruct z1, z2; simpl in *; auto; discriminate. Qed.
Lemma F2_beq_false_iff : forall z1 z2 : F2, (z1 =? z2)%F2 = false <-> z1 <> z2.
Proof. intros z1 z2. split; intros;  destruct z1, z2; simpl in *; auto; try discriminate; contradiction. Qed.
Lemma F2_neq0_iff_eq1 : forall z : F2, z <> 0 <-> z = 1.
Proof. intros z. split; intros H; destruct z; try contradiction; try discriminate; auto. Qed.
Lemma F2_neq1_iff_eq0 : forall z : F2, z <> 1 <-> z = 0.
Proof. intros z. split; intros H; destruct z; try contradiction; try discriminate; auto. Qed.

Ltac F2simpl :=
repeat
  match goal with
  | _ => rewrite F2mult_0_l
  | _ => rewrite F2mult_0_r
  | _ => rewrite F2plus_0_l
  | _ => rewrite F2plus_0_r
  | _ => rewrite F2mult_1_l
  | _ => rewrite F2mult_1_r
  end.

Declare Module F2Field : FieldModule
  with Definition F := F2
  with Definition R0 := F2_is_monoid
  with Definition R1 := F2_is_group
  with Definition R2 := F2_is_comm_group
  with Definition R3 := F2_is_ring
  with Definition R4 := F2_is_comm_ring
  with Definition R5 := F2_is_field.

Module F2Module := SubspacesOverField F2Field.


Notation MatrixF2 := (F2Module.GenMatrix).
Notation VectorF2 n := (F2Module.GenMatrix n%nat 1%nat).
Notation SquareF2 n := (F2Module.GenMatrix n%nat n%nat).
Notation WF_MatrixF2 := (F2Module.WF_GenMatrix).
Notation ZeroF2 := (F2Module.Zero).
Notation IF2 := (F2Module.I).
Notation traceF2 := (F2Module.trace).
Notation scaleF2 := (F2Module.scale).
Notation MplusF2 := (F2Module.GMplus).
Notation MoppF2 := (F2Module.GMopp).
Notation MminusF2 := (F2Module.GMminus).
Notation MmultF2 := (F2Module.GMmult).
Notation kronF2 := (F2Module.Gkron).
Notation transposeF2 := (F2Module.transpose).
Notation Mmult_nF2 := (F2Module.GMmult_n).
Notation genmat_equivF2 := (F2Module.genmat_equiv).
Notation get_colF2 := (F2Module.get_col).
Notation get_col_convF2 := (F2Module.get_col_conv).
Notation get_rowF2 := (F2Module.get_row).
Notation reduce_rowF2 := (F2Module.reduce_row).
Notation reduce_colF2 := (F2Module.reduce_col).
Notation col_swapF2 := (F2Module.col_swap).
Notation row_swapF2 := (F2Module.row_swap).
Notation col_addF2 := (F2Module.col_add).
Notation row_addF2 := (F2Module.row_add).
Notation col_swap_invF2 := (F2Module.col_swap_inv).
Notation row_swap_invF2 := (F2Module.row_swap_inv).
Notation col_add_invF2 := (F2Module.col_add_inv).
Notation row_add_invF2 := (F2Module.row_add_inv).
Notation swap_preserves_mul_ltF2 := (F2Module.swap_preserves_mul_lt).
Notation swap_preserves_mulF2 := (F2Module.swap_preserves_mul).
Notation add_preserves_mul_ltF2 := (F2Module.add_preserves_mul_lt).
Notation add_preserves_mulF2 := (F2Module.add_preserves_mul).
Notation WF_col_swapF2 := (F2Module.WF_col_swap).
Notation WF_row_swapF2 := (F2Module.WF_row_swap).
Notation WF_col_addF2 := (F2Module.WF_col_add).
Notation WF_row_addF2 := (F2Module.WF_row_add).
Notation col_swap_mult_rF2 := (F2Module.col_swap_mult_r).
Notation col_add_mult_rF2 := (F2Module.col_add_mult_r).
Notation col_row_swap_invr_IF2 := (F2Module.col_row_swap_invr_I).
Notation col_row_add_invr_IF2 := (F2Module.col_row_add_invr_I).
Notation e_iF2 := (F2Module.e_i).
Notation WF_e_iF2 := (F2Module.WF_e_i).
Notation matrix_by_basisF2 := (F2Module.matrix_by_basis).
Notation linearly_independentF2 := (F2Module.linearly_independent).
Notation linearly_dependentF2 := (F2Module.linearly_dependent).
Notation lindep_implies_not_linindepF2 := (F2Module.lindep_implies_not_linindep).
Notation not_lindep_implies_linindepF2 := (F2Module.not_lindep_implies_linindep).
Notation invr_col_swapF2 := (F2Module.invr_col_swap).
Notation invr_col_addF2 := (F2Module.invr_col_add).
Notation prop_zero_trueF2 := (F2Module.prop_zero_true).
Notation prop_zero_falseF2 := (F2Module.prop_zero_false).
Notation mat_prop_col_swap_convF2 := (F2Module.mat_prop_col_swap_conv).
Notation mat_prop_col_add_convF2 := (F2Module.mat_prop_col_add_conv).
Notation lin_indep_swap_invrF2 := (F2Module.lin_indep_swap_invr).
Notation lin_dep_swap_invrF2 := (F2Module.lin_dep_swap_invr).
Notation lin_indep_add_invrF2 := (F2Module.lin_indep_add_invr).
Notation lin_dep_add_invrF2 := (F2Module.lin_dep_add_invr).
Notation lin_indep_pzfF2 := (F2Module.lin_indep_pzf).
Notation lin_dep_pztF2 := (F2Module.lin_dep_pzt).
Notation smashF2 := (F2Module.smash).
Notation WF_smashF2 := (F2Module.WF_smash).

Infix ".+" := MplusF2 (at level 50, left associativity) : F2_scope.
Infix ".*" := scaleF2 (at level 40, left associativity) : F2_scope.
Infix "×" := MmultF2 (at level 40, left associativity) : F2_scope.
Infix "⊗" := kronF2 (at level 40, left associativity) : F2_scope.
Infix "≡" := genmat_equivF2 (at level 70) : F2_scope.
Notation "A ⊤" := (transposeF2 A) (at level 0) : F2_scope. 
Notation Σ2 := (@big_sum F2Field.F F2Field.R0).  (* we intoduce Σ2 notation here *)
Notation "p ⨉ A" := (Mmult_nF2 A p) (at level 30, no associativity) : F2_scope.

Check eq_refl : F2Field.F = F2.
Check eq_refl : F2Field.R0 = F2_is_monoid.


(** ** Defining a transposed Gaussian elimination. ** **)
Definition col_search_ones_right {m n : nat} (M : MatrixF2 m n) (r c : nat) :=
  filter (fun i : nat => (M r i =? one)%F2) (List.seq c (n - c)).

Fixpoint col_add_rec {m n : nat} (M : MatrixF2 m n) (c : nat) (cols : list nat) : MatrixF2 m n :=
  match cols with
  | [] => M
  | col :: t => col_add_rec (col_addF2 M col c 1%F2) c t
  end.

Definition col_add_right_ones {m n : nat} (M : MatrixF2 m n) (r c : nat): MatrixF2 m n :=
  col_add_rec M c (col_search_ones_right M r (Datatypes.S c)).

Fixpoint gaussian_elimination_transposed_rec {m n : nat} (M : MatrixF2 m n) (row_count col : nat) {struct row_count} : MatrixF2 m n :=
match row_count with
| 0%nat => M
| Datatypes.S row_count' => 
  match hd_error (col_search_ones_right M (m - row_count) col) with
  | None => gaussian_elimination_transposed_rec M row_count' col 
  | Some c => 
      if (col <? c)
      then gaussian_elimination_transposed_rec 
             (col_add_right_ones (col_swapF2 M col c) (m - row_count) col)
             row_count' (Datatypes.S col)
      else gaussian_elimination_transposed_rec 
             (col_add_right_ones M (m - row_count) col)
             row_count' (Datatypes.S col)
  end
end.

Definition gaussian_elimination_transposed {m n : nat} (M : MatrixF2 m n) :=
  gaussian_elimination_transposed_rec M m 0%nat.


(** ** Elementary column operations for matrices over F2 ** **)
Inductive elem_col_ops_chainF2 {m n : nat} : MatrixF2 m n -> MatrixF2 m n -> Prop :=
| idColOpsChain : forall (M : MatrixF2 m n), elem_col_ops_chainF2 M M
| swapColOpsChain : forall (M : MatrixF2 m n) (x y : nat), (x < n)%nat -> (y < n)%nat -> 
                                 elem_col_ops_chainF2 M (col_swapF2 M x y)
| addColOpsChain : forall (M : MatrixF2 m n) (x y : nat) (z : F2), x <> y -> (x < n)%nat -> (y < n)%nat -> 
                                         elem_col_ops_chainF2 M (col_addF2 M x y z)
| concatColOpsChain : forall (M M' M'' : MatrixF2 m n),
    elem_col_ops_chainF2 M M' -> elem_col_ops_chainF2 M' M'' ->
    elem_col_ops_chainF2 M M''.

Lemma elem_col_ops_chainF2_preserves_lin_indep : forall {m n : nat} (M M' : MatrixF2 m n), 
    elem_col_ops_chainF2 M M' -> (linearly_independentF2 M <-> linearly_independentF2 M').
Proof. intros m n M M' H.
  induction H; split; intros; auto.
  - pose lin_indep_swap_invrF2 as H'; inversion H'; subst; clear H'.
    apply H2; auto.
  - pose lin_indep_swap_invrF2 as H'.
    apply mat_prop_col_swap_convF2 in H1; auto.
  - pose lin_indep_add_invrF2 as H'; inversion H'; subst; clear H'.
    apply H3; auto.
  - pose lin_indep_add_invrF2 as H'.
    apply mat_prop_col_add_convF2 in H2; auto.
  - rewrite <- IHelem_col_ops_chainF2_2, <- IHelem_col_ops_chainF2_1; auto.
  - rewrite IHelem_col_ops_chainF2_1, IHelem_col_ops_chainF2_2; auto.
Qed.

Lemma elem_col_ops_chainF2_preserves_lin_dep : forall {m n : nat} (M M' : MatrixF2 m n), 
    elem_col_ops_chainF2 M M' -> (linearly_dependentF2 M <-> linearly_dependentF2 M').
Proof. intros m n M M' H.
  induction H; split; intros; auto.
  - pose lin_dep_swap_invrF2 as H'; inversion H'; subst; clear H'.
    apply H2; auto.
  - pose lin_dep_swap_invrF2 as H'.
    apply mat_prop_col_swap_convF2 in H1; auto.
  - pose lin_dep_add_invrF2 as H'; inversion H'; subst; clear H'.
    apply H3; auto.
  - pose lin_dep_add_invrF2 as H'.
    apply mat_prop_col_add_convF2 in H2; auto.
  - rewrite <- IHelem_col_ops_chainF2_2, <- IHelem_col_ops_chainF2_1; auto.
  - rewrite IHelem_col_ops_chainF2_1, IHelem_col_ops_chainF2_2; auto.
Qed.

Lemma elem_col_ops_chainF2_col_add_rec : 
  forall {m n : nat} (M : MatrixF2 m n) (c : nat) (cols : list nat),
    ~ In c cols -> (c < n)%nat -> incl cols (List.seq 0%nat n) ->
    elem_col_ops_chainF2 M (col_add_rec M c cols).
Proof. intros m n M c cols H H0 H1. 
  gen M c. induction cols; intros; try constructor; simpl.
  apply concatColOpsChain with (M' := (col_addF2 M a c 1)); auto.
  - constructor; auto.
    + rewrite not_in_cons in H; destruct H; auto.
    + assert (In a (a :: cols)) by (simpl; auto).
      apply H1 in H2. rewrite in_seq in H2. lia.
  - apply IHcols; auto.
    + apply incl_cons_inv in H1; destruct H1; auto.
    + rewrite not_in_cons in H; destruct H; auto.
Qed.

Lemma not_in_col_search_ones_right : forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
    ~ In c (col_search_ones_right M r (S c)).
Proof. intros m n M r c.
  unfold col_search_ones_right.
  intro H.
  rewrite filter_In in H.
  destruct H.
  rewrite in_seq in H.
  lia.
Qed.

Lemma incl_col_search_ones_right_seq : forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
    incl (col_search_ones_right M r (S c)) (List.seq 0%nat n).
Proof. intros m n M r c.
  unfold col_search_ones_right.
  unfold incl; intros.
  rewrite filter_In in H.
  destruct H.
  rewrite in_seq in H.
  rewrite in_seq.
  lia.
Qed.

Lemma elem_col_ops_chainF2_col_add_right_ones : 
  forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
    (c < n)%nat -> elem_col_ops_chainF2 M (col_add_right_ones M r c).
Proof. intros m n M r c H.
  unfold col_add_right_ones.
  apply elem_col_ops_chainF2_col_add_rec; auto.
  apply not_in_col_search_ones_right.
  apply incl_col_search_ones_right_seq.
Qed.

Lemma elem_col_ops_chainF2_gaussian_elimination_transposed_rec : 
  forall {m n : nat} (M : MatrixF2 m n) (row_count col : nat),
    elem_col_ops_chainF2 M (gaussian_elimination_transposed_rec M row_count col).
Proof. intros m n M row_count col.
  gen M col. induction row_count; intros;
    unfold gaussian_elimination_transposed_rec;
    try constructor.
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; auto.
  bdestruct_all.
  - fold (@gaussian_elimination_transposed_rec m n).
    apply concatColOpsChain with (M' := (col_add_right_ones (col_swapF2 M col n0) (m - S row_count) col)); auto.
    unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    apply concatColOpsChain with (M' := (col_swapF2 M col n0)).
    constructor; lia.
    apply elem_col_ops_chainF2_col_add_right_ones; lia.
  - fold (@gaussian_elimination_transposed_rec m n).
    apply concatColOpsChain with (M' := (col_add_right_ones M (m - S row_count) col)); auto.
    unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    apply elem_col_ops_chainF2_col_add_right_ones; lia.
Qed.

Lemma gaussian_elimination_transposed_rec_preserves_lin_indep : 
  forall {m n : nat} (M : MatrixF2 m n) (row_count col : nat), 
    linearly_independentF2 M <-> linearly_independentF2 (gaussian_elimination_transposed_rec M row_count col).
Proof. intros m n M row_count col.
  apply elem_col_ops_chainF2_preserves_lin_indep.
  apply elem_col_ops_chainF2_gaussian_elimination_transposed_rec.
Qed.

Lemma gaussian_elimination_transposed_rec_preserves_lin_dep : 
  forall {m n : nat} (M : MatrixF2 m n) (row_count col : nat), 
    linearly_dependentF2 M <-> linearly_dependentF2 (gaussian_elimination_transposed_rec M row_count col).
Proof. intros m n M row_count col.
  apply elem_col_ops_chainF2_preserves_lin_dep.
  apply elem_col_ops_chainF2_gaussian_elimination_transposed_rec.
Qed.

Lemma elem_col_ops_chainF2_gaussian_elimination_transposed : 
  forall {m n : nat} (M : MatrixF2 m n),
    elem_col_ops_chainF2 M (gaussian_elimination_transposed M).
Proof. intros; apply elem_col_ops_chainF2_gaussian_elimination_transposed_rec. Qed.

Lemma gaussian_elimination_transposed_preserves_lin_indep : 
  forall {m n : nat} (M : MatrixF2 m n), 
    linearly_independentF2 M <-> linearly_independentF2 (gaussian_elimination_transposed M).
Proof. intros m n M.
  apply elem_col_ops_chainF2_preserves_lin_indep.
  apply elem_col_ops_chainF2_gaussian_elimination_transposed.
Qed.

Lemma gaussian_elimination_transposed_preserves_lin_dep : 
  forall {m n : nat} (M : MatrixF2 m n), 
    linearly_dependentF2 M <-> linearly_dependentF2 (gaussian_elimination_transposed M).
Proof. intros m n M.
  apply elem_col_ops_chainF2_preserves_lin_dep.
  apply elem_col_ops_chainF2_gaussian_elimination_transposed.
Qed.


Fixpoint gaussian_elimination_transposed_rec_get_pivot_row {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat) {struct row_count} : (MatrixF2 m n) * option nat :=
  match row_count with
  | 0%nat => (M, None)
  | Datatypes.S row_count' => 
      match hd_error (col_search_ones_right M (m - row_count) col) with
      | None => gaussian_elimination_transposed_rec_get_pivot_row M row_count' col pivot_col
      | Some c => if (col <? pivot_col)
                 then
                   if (col <? c)
                   then gaussian_elimination_transposed_rec_get_pivot_row
                          (col_add_right_ones (col_swapF2 M col c) (m - row_count) col)
                          row_count' (Datatypes.S col) pivot_col
                   else gaussian_elimination_transposed_rec_get_pivot_row
                          (col_add_right_ones M (m - row_count) col)
                          row_count' (Datatypes.S col) pivot_col
                 else
                   if (col <? c)
                   then ((col_add_right_ones (col_swapF2 M col c) (m - row_count) col), Some (m - row_count)%nat)
                   else ((col_add_right_ones M (m - row_count) col), Some (m - row_count)%nat)
      end
  end. 

Lemma WF_col_add_rec : forall {m n : nat} (M : MatrixF2 m n) (c : nat) (cols : list nat),
     incl cols (seq 0 n) -> WF_MatrixF2 M -> WF_MatrixF2 (col_add_rec M c cols).
Proof. intros m n M c cols H H0.
  gen M c. induction cols; intros; simpl; auto.
  apply IHcols.
  - unfold incl. intros a0 H1.
    assert (In a0 (a :: cols)) by (simpl; auto).
    apply H in H2. auto.
  - apply F2Module.WF_col_add; auto.
    assert (In a (seq 0 n)).
    { assert (In a (a :: cols)) by (simpl; auto). 
      apply H in H1. auto. }
    rewrite in_seq in H1; lia.
Qed.

Lemma WF_col_add_right_ones : forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
   (c < n)%nat -> WF_MatrixF2 M -> WF_MatrixF2 (col_add_right_ones M r c).
  intros m n M r c H H0.
  unfold col_add_right_ones.
  apply WF_col_add_rec; auto.
  unfold incl. intros a H1.
  unfold col_search_ones_right in H1.
  apply filter_In in H1. destruct H1.
  rewrite in_seq in H1.
  rewrite in_seq. lia.
Qed.

Lemma WF_fst_gaussian_elimination_transposed_rec_get_pivot_row : 
  forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat),
    WF_MatrixF2 M -> WF_MatrixF2 (fst (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col)).
Proof. intros m n M row_count col pivot_col H.
  unfold WF_MatrixF2.
  intros x y H0.
  gen M col pivot_col x y. induction row_count; intros; auto.
  simpl.
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E.
  - unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    bdestruct_all.
    + apply IHrow_count; try lia; auto.
      apply WF_col_add_right_ones; try lia; auto.
      apply F2Module.WF_col_swap; try lia; auto.
    + apply IHrow_count; try lia; auto.
      apply WF_col_add_right_ones; try lia; auto.
    + simpl.
      assert (WF_MatrixF2 (col_add_right_ones (col_swapF2 M col n0) (m - S row_count) col)).
      { apply WF_col_add_right_ones; try lia; auto.
        apply F2Module.WF_col_swap; try lia; auto. }
      rewrite H3; auto.
    + simpl. 
      assert (WF_MatrixF2 (col_add_right_ones M (m - S row_count) col)).
      { apply WF_col_add_right_ones; try lia; auto. }
      rewrite H3; auto.
  - apply IHrow_count; try lia; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_col_overflow : 
  forall {m n : nat} (M : MatrixF2 m n) (row_count col : nat),
    (col >= n)%nat ->
  gaussian_elimination_transposed_rec M row_count col = M.
Proof. intros m n M row_count col H.
  gen M col. induction row_count; intros; auto. simpl.
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E.
  unfold col_search_ones_right in E.
  destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
  apply hd_error_some_nil in E; contradiction.
  simpl in E. inversion E; subst; clear E.
  assert (H' : In n0 (n0 :: l)) by (simpl; auto).
  rewrite <- E' in H'.
  rewrite filter_In in H'; destruct H' as [H' H''].
  rewrite in_seq in H'.
  bdestruct_all; try lia.
  apply IHrow_count; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_get_pivot_row_saturated :
  forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat),
    (pivot_col >= n - 1)%nat ->
    gaussian_elimination_transposed_rec M row_count col =
      fst (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col).
Proof. intros m n M row_count col pivot_col H.
  gen M pivot_col col. induction row_count; intros; auto; simpl. 
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E.
  - unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    bdestruct_all; try apply IHrow_count with (pivot_col := n); auto; simpl; try lia. 
    bdestruct (pivot_col =? col)%nat; try lia. subst.
    bdestruct (col =? n-1)%nat; try lia. subst. simpl.
    rewrite gaussian_elimination_transposed_rec_col_overflow; auto; lia.
  - apply IHrow_count; auto.
Qed.

Lemma WF_gaussian_elimination_transposed : forall {m n : nat} (M : MatrixF2 m n),
    WF_MatrixF2 M -> WF_MatrixF2 (gaussian_elimination_transposed M).
Proof. intros m n M H.
  unfold gaussian_elimination_transposed.
  rewrite gaussian_elimination_transposed_rec_get_pivot_row_saturated with (pivot_col := (n - 1)%nat); try lia; auto.
  apply WF_fst_gaussian_elimination_transposed_rec_get_pivot_row; auto.
Qed.

Definition col_slice_one_hd_error {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat) :=
  let GM := gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col in
  hd_error (filter (fun r : nat => ((fst GM) r pivot_col =? one)%F2) (List.seq (m - row_count) row_count)).

Lemma col_add_rec_one_bool_true : 
  forall {m n : nat} (M : MatrixF2 m n) (c c' r' : nat) (cols : list nat),
    (c' < c)%nat -> (c < n)%nat -> (M r' c' =? 1) = true ->
    ~ In c cols -> NoDup cols -> incl cols (seq c (n - c)) ->
    (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    (col_add_rec M c cols r' c' =? 1) = true.
Proof. intros m n M c c' r' cols H H0 H1 H2 H3 H4 H5.
  gen M c c' r'. induction cols; intros; auto.
  simpl. apply IHcols; try lia; auto.
  - rewrite NoDup_cons_iff in H3. destruct H3. auto.
  - rewrite not_in_cons in H2. destruct H2. auto.
  - unfold incl. intros a0 H6.
    assert (H' : In a0 (a :: cols)) by (simpl; auto).
    apply H4 in H'. auto.
  - unfold col_addF2.
    bdestruct_all; auto.
    rewrite F2_beq_true_iff in H1.
    rewrite ! H1.
    assert ((M r' c =? 1) = false).
    { apply H5; lia. }
    rewrite F2_beq_false_iff in H7.
    destruct (M r' c) eqn:E; try contradiction.
    F2simpl. auto.
  - intros i H6.
    unfold col_addF2.
    bdestruct_all; subst; auto.
    assert ((M r' c =? 1) = false).
    { apply H5; lia. }
    assert ((M r' a =? 1) = false).
    { apply H5; lia. }
    rewrite F2_beq_false_iff in H7, H8.
    destruct (M r' c) eqn:E; try contradiction.
    destruct (M r' a) eqn:E'; try contradiction.
    F2simpl. auto.
Qed.

Lemma col_add_right_ones_one_bool_true :
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c'  : nat),
    (c' < c)%nat -> (c < n)%nat -> (M r' c' =? 1) = true ->
    (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    (col_add_right_ones M r c r' c' =? 1) = true.
Proof. intros m n M r r' c c' H H0 H1 H2. 
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_one_bool_true; try lia; auto.
  - intro H3. rewrite filter_In in H3. destruct H3.
    rewrite in_seq in H3. lia.
  - apply NoDup_filter. apply seq_NoDup.
  - unfold incl. intros a H3. rewrite filter_In in H3. destruct H3.
    rewrite in_seq in H3. rewrite in_seq. lia.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_true :
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c' k  : nat),
    (c' < c)%nat -> (c < k)%nat -> (k < n)%nat -> (M r' c' =? 1) = true ->
    (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    (col_add_right_ones (col_swapF2 M c k) r c r' c' =? 1) = true.
Proof. intros m n M r r' c c' k H H0 H1 H2 H3.
  apply col_add_right_ones_one_bool_true; try lia; auto.
  unfold col_swapF2. bdestruct_all; subst; auto.
  intros i H4. unfold col_swapF2. bdestruct_all; auto; apply H3; try lia.
Qed.

Lemma col_add_rec_one_bool_false : 
  forall {m n : nat} (M : MatrixF2 m n) (c c' r' i : nat) (cols : list nat),
    (c' < c)%nat -> (c < n)%nat -> (c' < i < n)%nat -> (M r' i =? 1) = false ->
    (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    ~ In c cols -> NoDup cols -> incl cols (seq c (n - c)) ->
    (col_add_rec M c cols r' i =? 1) = false.
Proof. intros m n M c c' r' i cols H H0 H1 H2 H3 H4 H5 H6. 
  gen M c c' r' i. induction cols; intros; auto.
 apply IHcols with (c' := c'); try lia; auto.
  - rewrite NoDup_cons_iff in H5. destruct H5. auto.
  - rewrite not_in_cons in H4. destruct H4. auto.
  - unfold incl. intros a0 H7.
    assert (H' : In a0 (a :: cols)) by (simpl; auto).
    apply H6 in H'. auto.
  - intros i0 H7.
    unfold col_addF2.
    bdestruct_all; subst; auto.
    assert ((M r' c =? 1) = false).
    { apply H3; lia. }
    assert ((M r' a =? 1) = false).
    { apply H3; lia. }
    rewrite F2_beq_false_iff in H8, H9.
    destruct (M r' c) eqn:E; try contradiction.
    destruct (M r' a) eqn:E'; try contradiction.
    F2simpl. auto.
  - unfold col_addF2.
    bdestruct_all; subst; auto.
    rewrite F2_beq_false_iff in H2.
    destruct (M r' a) eqn:E; try contradiction.
    assert ((M r' c =? 1) = false).
    { apply H3; lia. }
    rewrite F2_beq_false_iff in H7.
    destruct (M r' c) eqn:E'; try contradiction.
    F2simpl. auto.
Qed.

Lemma col_add_right_ones_one_bool_false : 
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c'  : nat),
    (c' < c)%nat -> (c < n)%nat -> (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    (forall i : nat, (c' < i < n)%nat -> (col_add_right_ones M r c r' i =? 1) = false).
Proof. intros m n M r r' c c' H H0 H1 i H2.
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_one_bool_false with (c' := c'); try lia; auto.
  - intro H3. rewrite filter_In in H3. destruct H3.
    rewrite in_seq in H3. lia.
  - apply NoDup_filter. apply seq_NoDup.
  - unfold incl. intros a H3. rewrite filter_In in H3. destruct H3.
    rewrite in_seq in H3. rewrite in_seq. lia.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_false :
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c' k  : nat),
    (c' < c)%nat -> (c < k)%nat -> (k < n)%nat -> (forall i : nat, (c' < i < n)%nat -> (M r' i =? 1) = false) ->
    (forall i : nat, (c' < i < n)%nat -> (col_add_right_ones (col_swapF2 M c k) r c r' i =? 1) = false).
Proof. intros m n M r r' c c' k H H0 H1 H2 i H3.
  apply col_add_right_ones_one_bool_false with (c' := c'); try lia; auto.
  intros i0 H4. unfold col_swapF2. bdestruct_all; auto; apply H2; try lia.
Qed.

Lemma fst_gaussian_elimination_transposed_rec_get_pivot_row_above_one_false :
  forall {m n : nat} (M : MatrixF2 m n) (r c pc r' c' : nat),
    (r < r' <= m)%nat -> (c' < c)%nat -> (c <= pc < n)%nat -> (M (m - r')%nat c' =? 1) = true -> 
    (forall i : nat, (c' < i < n)%nat -> (M (m - r')%nat i =? 1) = false) ->
    (fst (gaussian_elimination_transposed_rec_get_pivot_row M r c pc) (m - r')%nat pc =? 1) = false. 
Proof. intros m n M r c pc r' c' H H0 H1 H2 H3. 
  gen M c pc r' c'. induction r; intros; simpl.
  - apply H3; lia.
  - destruct (hd_error (col_search_ones_right M (m - S r) c)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S r)%nat i =? 1) (seq c (n - c))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite IHr with (c' := c'); auto; try lia.
        -- apply col_add_right_ones_col_swapF2_one_bool_true; try lia; auto.
        -- apply col_add_right_ones_col_swapF2_one_bool_false; try lia; auto.
      * rewrite IHr with (c' := c'); auto; try lia.
        -- apply col_add_right_ones_one_bool_true; try lia; auto.
        -- apply col_add_right_ones_one_bool_false; try lia; auto.
      * apply col_add_right_ones_col_swapF2_one_bool_false with (c' := c'); try lia; auto.
      * apply col_add_right_ones_one_bool_false with (c' := c'); try lia; auto.
    + bdestruct_all; try lia; simpl.
      rewrite IHr with (c' := c'); auto; try lia.
Qed.

Lemma col_addF2_one_bool_true_true : forall {m n : nat} (M : MatrixF2 m n) (r c a : nat),
    c <> a -> (M r c =? 1) = true -> (M r a =? 1) = true -> ((col_addF2 M a c 1) r c =? 1) = true.
Proof. intros m n M r c a H H0 H1.
  rewrite F2_beq_true_iff in H0, H1.
  rewrite F2_beq_true_iff.
  unfold col_addF2.
  bdestruct_all; auto.
Qed.

Lemma col_add_rec_one_bool_preserve : forall {m n : nat} (M : MatrixF2 m n) (r c : nat) (cols : list nat),
    NoDup cols -> (forall a : nat, In a cols -> (M r a =? 1) = true) ->
    ~ In c cols -> (M r c =? 1) = true -> ((col_add_rec M c cols) r c =? 1) = true.
Proof. intros m n M r c cols H H0 H1 H2.
  rewrite F2_beq_true_iff in H2.
  rewrite F2_beq_true_iff.
  gen M r c. induction cols; intros; auto.
  simpl. 
  rewrite not_in_cons in H1.
  destruct H1.
  rewrite NoDup_cons_iff in H.
  destruct H.
  apply IHcols; auto.
  - intros a0 H5. 
    assert (In a0 (a :: cols)) by (simpl; auto).
    apply H0 in H6.
    rewrite F2_beq_true_iff in H6.
    rewrite F2_beq_true_iff.
    unfold col_addF2.
    bdestruct_all; auto.
    subst. contradiction.
  - rewrite <- F2_beq_true_iff.
    apply col_addF2_one_bool_true_true; auto.
    rewrite F2_beq_true_iff; auto.
    apply H0; simpl; auto.
Qed.

Lemma col_add_right_ones_one_bool_preserve : forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
    (M r c =? 1) = true -> ((col_add_right_ones M r c) r c =? 1) = true.
Proof. intros m n M r c H.
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  simpl.
  apply col_add_rec_one_bool_preserve; auto.
  - apply NoDup_filter.
    apply seq_NoDup.
  - intros a H0.
    rewrite filter_In in H0.
    destruct H0; auto.
  - intro.
    rewrite filter_In in H0.
    destruct H0.
    rewrite in_seq in H0.
    lia.
Qed.

Lemma col_swapF2_one_bool_preserve : forall {m n : nat} (M : MatrixF2 m n) (r c i : nat),
    (M r i =? 1) = true -> ((col_swapF2 M c i) r c =? 1) = true.
Proof. intros m n M r c i H.
  rewrite F2_beq_true_iff in H.
  rewrite F2_beq_true_iff.
  unfold col_swapF2.
  bdestruct_all; auto.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_preserve : 
  forall {m n : nat} (M : MatrixF2 m n) (r c i : nat),
    (M r i =? 1) = true -> ((col_add_right_ones (col_swapF2 M c i) r c) r c =? 1) = true.
Proof. intros m n M r c i H.
  apply col_add_right_ones_one_bool_preserve.
  apply col_swapF2_one_bool_preserve; auto.
Qed.


Lemma col_add_rec_zero_bool_preserve :
  forall {m n : nat} (M : MatrixF2 m n) (r c : nat) (cols : list nat),
    (c < n)%nat -> NoDup cols -> ~ In c cols -> incl cols (seq c (n - c)) ->
    (forall i : nat, (c < i < n)%nat -> ((M r i =? 1) = true <-> In i cols)) -> (M r c =? 1) = true ->
    (forall i : nat, (c < i < n)%nat -> (col_add_rec M c cols r i =? 1) = false).
Proof. intros m n M r c cols H H0 H1 H2 H3 H4 i H5. 
  gen M r c. induction cols; intros; simpl.
  - rewrite F2_beq_false_iff. intro H6. rewrite <- F2_beq_true_iff in H6.
    rewrite H3 in H6; auto.
  - apply IHcols; auto.
    + rewrite NoDup_cons_iff in H0.
      destruct H0. auto.
    + rewrite not_in_cons in H1.
      destruct H1. auto.
    + unfold incl. intros a0 H6.
      assert (In a0 (a :: cols)) by (simpl; auto).
      apply H2 in H7. auto.
    + intros i0 H6. split; intros H7.
      * assert ((M r i0 =? 1) = true).
        { rewrite F2_beq_true_iff. 
          destruct (M r i0) eqn:E; auto.
          rewrite F2_beq_true_iff in H7. 
          destruct (col_addF2 M a c 1 r i0) eqn:E'; auto.
          contradict E'. unfold col_addF2.
          bdestruct_all; subst.
          - assert (In a (a :: cols)) by (simpl; auto).
            rewrite <- H3 in H8; auto.
            rewrite F2_beq_true_iff in H8.
            rewrite E in H8.
            discriminate.
          - rewrite E. intro. discriminate. }
        remember H8 as H'. clear HeqH'.
        rewrite H3 in H8; auto.
        destruct H8; auto.
        subst.
        rewrite F2_beq_true_iff in H7.
        contradict H7.
        unfold col_addF2.
        bdestruct_all; subst; auto.
        rewrite F2_beq_true_iff in H4, H'.
        rewrite H4, H'.
        F2simpl. simpl. intro. discriminate.
      * unfold col_addF2.
        bdestruct_all; subst; auto.
        -- rewrite NoDup_cons_iff in H0. destruct H0. auto.
        -- rewrite H3; simpl; auto.
    + unfold col_addF2.
      bdestruct_all; subst; auto.
      assert (In a (a :: cols)) by (simpl; auto).
      contradiction.
Qed.

Lemma col_add_right_ones_zero_bool_preserve : 
  forall {m n : nat} (M : MatrixF2 m n) (r c : nat),
    (c < n)%nat -> (M r c =? 1) = true ->
    (forall i : nat, (c < i < n)%nat -> ((col_add_right_ones M r c) r i =? 1) = false).
Proof. intros m n M r c H H0 i H1. 
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_zero_bool_preserve; auto.
  - apply NoDup_filter. apply seq_NoDup.
  - intro H2. rewrite filter_In in H2. destruct H2. 
    rewrite in_seq in H2. lia. 
  - unfold incl. intros a H2. 
    rewrite filter_In in H2. destruct H2.
    rewrite in_seq in H2. rewrite in_seq. lia.
  - intros i0 H2. split; intros H3.
    + rewrite filter_In. split; auto.
      rewrite in_seq; lia.
    + rewrite filter_In in H3. destruct H3. auto.
Qed.

Lemma col_add_right_ones_col_swapF2_zero_bool_preserve : 
  forall {m n : nat} (M : MatrixF2 m n) (r c k : nat),
    (M r k =? 1) = true -> (c < n)%nat -> (c < k < n)%nat ->
    (forall i : nat, (c < i < n)%nat -> (col_add_right_ones (col_swapF2 M c k) r c r i =? 1) = false).
Proof. intros m n M r c k H H0 H1 i H2.
  apply col_add_right_ones_zero_bool_preserve; auto.
  unfold col_swapF2.
  bdestruct_all; subst; auto.
Qed. 


Lemma col_add_rec_one_bool_false_inclusive_domain : 
  forall {m n : nat} (M : MatrixF2 m n) (r c i : nat) (cols : list nat),
    (c < i < n)%nat -> (forall i : nat, (c <= i < n)%nat -> (M r i =? 1) = false) ->
    NoDup cols -> ~ In c cols -> incl cols (seq c (n - c)) ->
    (col_add_rec M c cols r i =? 1) = false.
Proof. intros m n M r c i cols H H0 H1 H2 H3.
  gen M r c i. induction cols; intros; simpl.
  - apply H0; lia.
  - apply IHcols; try lia; auto.
    + rewrite NoDup_cons_iff in H1.
      destruct H1. auto.
    + intros i0 H4.
      unfold col_addF2.
      bdestruct_all; subst; auto.
      assert (M r a = zero).
      { destruct (M r a) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      assert (M r c = zero).
      { destruct (M r c) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      rewrite H5, H6.
      F2simpl. auto.
    + rewrite not_in_cons in H2.
      destruct H2. auto.
    + unfold incl. intros a0 H4.
      assert (In a0 (a :: cols)) by (simpl; auto).
      apply H3 in H5. auto.
Qed.

Lemma col_add_right_ones_one_bool_false_inclusive_domain : 
  forall {m n : nat} (M : MatrixF2 m n) (r r' c i : nat),
    (forall i : nat, (c <= i < n)%nat -> (M r' i =? 1) = false) -> (c < i < n)%nat ->
    (col_add_right_ones M r c r' i =? 1) = false.
Proof. intros m n M r r' c i H H0. 
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_one_bool_false_inclusive_domain; try lia; auto.
  - apply NoDup_filter. apply seq_NoDup.
  - intro H1. rewrite filter_In in H1. destruct H1. 
    rewrite in_seq in H1. lia. 
  - unfold incl. intros a H1. 
    rewrite filter_In in H1. destruct H1.
    rewrite in_seq in H1. rewrite in_seq. lia.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_false_inclusive_domain : 
  forall {m n : nat} (M : MatrixF2 m n) (r r' c k i : nat),
    (forall i : nat, (c <= i < n)%nat -> (M r' i =? 1) = false) ->
    (c < k < n)%nat -> (c < i < n)%nat ->
    (col_add_right_ones (col_swapF2 M c k) r c r' i =? 1) = false.
Proof. intros m n M r r' c k i H H0 H1. 
   apply col_add_right_ones_one_bool_false_inclusive_domain; try lia; auto.
   - intros i0 H2. unfold col_swapF2.
     bdestruct_all; subst; apply H; try lia.
Qed.

Lemma col_add_rec_one_bool_false_pivot_col_is_col_inclusive_domain : 
  forall {m n : nat} (M : MatrixF2 m n) (r c : nat) (cols : list nat),
    (c < n)%nat -> (forall i : nat, (c <= i < n)%nat -> (M r i =? 1) = false) ->
    NoDup cols -> ~ In c cols -> incl cols (seq c (n - c)) ->
    (col_add_rec M c cols r c =? 1) = false.
Proof. intros m n M r c cols H H0 H1 H2 H3.
  gen M r c. induction cols; intros; simpl.
  - apply H0; lia.
  - apply IHcols; try lia; auto.
    + rewrite NoDup_cons_iff in H1.
      destruct H1. auto.
    + intros i0 H4.
      unfold col_addF2.
      bdestruct_all; subst; auto.
      assert (M r a = zero).
      { destruct (M r a) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      assert (M r c = zero).
      { destruct (M r c) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      rewrite H5, H6.
      F2simpl. auto.
    + rewrite not_in_cons in H2.
      destruct H2. auto.
    + unfold incl. intros a0 H4.
      assert (In a0 (a :: cols)) by (simpl; auto).
      apply H3 in H5. auto.
Qed.

Lemma col_add_right_ones_one_bool_false_pivot_col_is_col_inclusive_domain : forall {m n : nat} (M : MatrixF2 m n) (r r' c : nat),
    (forall i : nat, (c <= i < n)%nat -> (M r' i =? 1) = false) -> (c < n)%nat ->
    (col_add_right_ones M r c r' c =? 1) = false.
Proof. intros m n M r r' c H H0. 
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_one_bool_false_pivot_col_is_col_inclusive_domain; try lia; auto.
  - apply NoDup_filter. apply seq_NoDup.
  - intro H1. rewrite filter_In in H1. destruct H1. 
    rewrite in_seq in H1. lia. 
  - unfold incl. intros a H1. 
    rewrite filter_In in H1. destruct H1.
    rewrite in_seq in H1. rewrite in_seq. lia.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_false_pivot_col_is_col_inclusive_domain : forall {m n : nat} (M : MatrixF2 m n) (r r' c k : nat),
    (r <= m)%nat -> (r' < r)%nat -> (forall i : nat, (c <= i < n)%nat -> (M r' i =? 1) = false) -> (c < k < n)%nat ->
    (M r k =? 1) = true -> (col_add_right_ones (col_swapF2 M c k) r c r' c =? 1) = false.
Proof. intros m n M r r' c k H H0 H1 H2 H3.
  apply col_add_right_ones_one_bool_false_pivot_col_is_col_inclusive_domain; try lia; auto.
  - intros i H4. unfold col_swapF2.
     bdestruct_all; subst; apply H1; try lia.
Qed.

Lemma fst_gaussian_elimination_transposed_rec_get_pivot_row_one_bool_empty_false :
  forall {m n : nat} (M : MatrixF2 m n) (r r' c pc : nat),
    (r' <= m)%nat -> (c <= pc < n)%nat -> (r < r')%nat -> 
    (forall i : nat, (c <= i < n)%nat -> (M (m - r')%nat i =? 1) = false) ->
    (fst (gaussian_elimination_transposed_rec_get_pivot_row M r c pc)
       (m - r')%nat pc =? 1) = false.
Proof. intros m n M r r' c pc H H0 H1 H2.
  gen M r' c pc. induction r; intros; auto; simpl.
  - destruct (hd_error (col_search_ones_right M (m - S r) c)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S r)%nat i =? 1) (seq c (n - c))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite IHr; auto; try lia. intros i H5. 
        apply col_add_right_ones_col_swapF2_one_bool_false_inclusive_domain; try lia; auto.
      * rewrite IHr; auto; try lia. intros i H5. 
        assert (n0 = c) by lia; subst.
        apply col_add_right_ones_one_bool_false_inclusive_domain; try lia; auto.
      * assert (pc = c) by lia; subst.
        apply col_add_right_ones_col_swapF2_one_bool_false_pivot_col_is_col_inclusive_domain; try lia; auto.
      * assert (n0 = c) by lia; subst.
        assert (pc = c) by lia; subst.
        apply col_add_right_ones_one_bool_false_pivot_col_is_col_inclusive_domain; try lia; auto.
    + rewrite IHr; auto; try lia.
Qed.

Lemma col_slice_one_hd_error_is_gaussian_elimination_transposed_rec_get_pivot_row :
  forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat),
    (row_count <= m)%nat -> (col <= pivot_col < n)%nat ->
    col_slice_one_hd_error M row_count col pivot_col = snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col).
Proof. intros m n M row_count col pivot_col H H0.
  gen M col pivot_col. induction row_count; intros; auto.
  unfold col_slice_one_hd_error.
  simpl.
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
  - unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    bdestruct_all; try lia; simpl.
    + rewrite <- IHrow_count; try lia.
      unfold col_slice_one_hd_error.
      rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_above_one_false with (c' := col); try lia; auto.
      * replace (S (m - S row_count))%nat with (m - row_count)%nat by lia; auto.
      * apply col_add_right_ones_col_swapF2_one_bool_preserve; try lia; auto.
      * intros i H3. apply col_add_right_ones_col_swapF2_zero_bool_preserve; try lia; auto.
    + assert (n0 = col) by lia; subst.
      rewrite <- IHrow_count; try lia.
      unfold col_slice_one_hd_error.
      rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_above_one_false with (c' := col); try lia; auto.
      * replace (S (m - S row_count))%nat with (m - row_count)%nat by lia; auto.
      * apply col_add_right_ones_one_bool_preserve; try lia; auto.
      * intros i H3. apply col_add_right_ones_zero_bool_preserve; try lia; auto.
    + assert (pivot_col = col) by lia; subst.
      rewrite col_add_right_ones_col_swapF2_one_bool_preserve; auto.
    + assert (n0 = col) by lia; subst.
      assert (pivot_col = col) by lia; subst.
      rewrite col_add_right_ones_one_bool_preserve; auto.
  - rewrite <- IHrow_count; try lia.
    unfold col_slice_one_hd_error.
    unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E';
      simpl in E; try discriminate. clear E.
    assert (forall i : nat, (col <= i < n)%nat -> (M (m - S row_count)%nat i =? 1) = false).
    { intros i H1.
      assert (~ In i (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col)))).
      { intros H2. rewrite E' in H2. inversion H2. }
      rewrite filter_In in H2.
      rewrite in_seq in H2.
      destruct (M (m - S row_count)%nat i =? 1) eqn:E''; auto.
      assert ((col <= i < col + (n - col))%nat /\ true = true).
      { split; auto; try lia. }
      apply H2 in H3. contradiction. }
    rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_one_bool_empty_false; try lia; auto.
    replace (S (m - S row_count))%nat with (m - row_count)%nat by lia; auto.
Qed.


Definition col_slice_one_hd_error_original {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat) :=
  let GM := gaussian_elimination_transposed_rec M row_count col in
  hd_error (filter (fun r : nat => (GM r pivot_col =? one)%F2) (List.seq (m - row_count) row_count)).

Lemma gaussian_elimination_transposed_rec_above_one_false :
  forall {m n : nat} (M : MatrixF2 m n) (r c pc r' c' : nat),
    (r < r' <= m)%nat -> (c' < c)%nat -> (c' < pc < n)%nat -> (M (m - r')%nat c' =? 1) = true -> 
    (forall i : nat, (c' < i < n)%nat -> (M (m - r')%nat i =? 1) = false) ->
    ((gaussian_elimination_transposed_rec M r c) (m - r')%nat pc =? 1) = false. 
Proof. intros m n M r c pc r' c' H H0 H1 H2 H3. 
  gen M c pc r' c'. induction r; intros; simpl.
  - apply H3; try lia.
  - destruct (hd_error (col_search_ones_right M (m - S r) c)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S r)%nat i =? 1) (seq c (n - c))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite IHr with (c' := c'); auto; try lia.
        -- apply col_add_right_ones_col_swapF2_one_bool_true; try lia; auto.
        -- apply col_add_right_ones_col_swapF2_one_bool_false; try lia; auto.
      * rewrite IHr with (c' := c'); auto; try lia.
        -- apply col_add_right_ones_one_bool_true; try lia; auto.
        -- apply col_add_right_ones_one_bool_false; try lia; auto.
    + bdestruct_all; try lia; simpl.
      rewrite IHr with (c' := c'); auto; try lia.
Qed.

Lemma col_add_rec_one_bool_false_inclusive_domain_previous : 
  forall {m n : nat} (M : MatrixF2 m n) (r c c' i : nat) (cols : list nat),
    (c' <= i < n)%nat -> (forall i : nat, (c' <= i < n)%nat -> (M r i =? 1) = false) -> (c' <= c < n)%nat ->
    NoDup cols -> ~ In c cols -> incl cols (seq c (n - c)) ->
    (col_add_rec M c cols r i =? 1) = false.
Proof. intros m n M r c c' i cols H H0 H1 H2 H3 H4.
  gen M r c i. induction cols; intros; simpl.
  - apply H0; lia.
  - apply IHcols; try lia; auto.
    + rewrite NoDup_cons_iff in H2.
      destruct H2. auto.
    + intros i0 H5.
      unfold col_addF2.
      bdestruct_all; subst; auto.
      assert (M r a = zero).
      { destruct (M r a) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      assert (M r c = zero).
      { destruct (M r c) eqn:E; auto.
        contradict E.
        rewrite <- F2_beq_false_iff.
        apply H0. lia. }
      rewrite H6, H7.
      F2simpl. auto.
    + rewrite not_in_cons in H3.
      destruct H3. auto.
    + unfold incl. intros a0 H5.
      assert (In a0 (a :: cols)) by (simpl; auto).
      apply H4 in H6. auto.
Qed.

Lemma col_add_right_ones_one_bool_false_inclusive_domain_previous : 
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c' i : nat),
    (forall i : nat, (c' <= i < n)%nat -> (M r' i =? 1) = false) -> (c' <= c < n)%nat -> (c' <= i < n)%nat ->
    (col_add_right_ones M r c r' i =? 1) = false.
Proof. intros m n M r r' c c' i H H0 H1. 
  unfold col_add_right_ones.
  unfold col_search_ones_right.
  apply col_add_rec_one_bool_false_inclusive_domain_previous with (c' := c'); try lia; auto. 
  - apply NoDup_filter. apply seq_NoDup.
  - intro H2. rewrite filter_In in H2. destruct H2. 
    rewrite in_seq in H2. lia. 
  - unfold incl. intros a H2. 
    rewrite filter_In in H2. destruct H2.
    rewrite in_seq in H2. rewrite in_seq. lia.
Qed.

Lemma col_add_right_ones_col_swapF2_one_bool_false_inclusive_domain_previous : 
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c' k i : nat),
    (forall i : nat, (c' <= i < n)%nat -> (M r' i =? 1) = false) -> (c' <= c < n)%nat ->
    (c < k < n)%nat -> (c' <= i < n)%nat ->
    (col_add_right_ones (col_swapF2 M c k) r c r' i =? 1) = false.
Proof. intros m n M r r' c c' k i H H0 H1 H2. 
   apply col_add_right_ones_one_bool_false_inclusive_domain_previous with (c' := c'); try lia; auto.
   - intros i0 H3. unfold col_swapF2.
     bdestruct_all; subst; apply H; try lia.
Qed.

Lemma gaussian_elimination_transposed_rec_one_bool_empty_false :
  forall {m n : nat} (M : MatrixF2 m n) (r r' c c' pc : nat),
    (r < r' <= m)%nat -> (c' <= pc < n)%nat -> (c' <= c)%nat -> 
    (forall i : nat, (c' <= i < n)%nat -> (M (m - r')%nat i =? 1) = false) ->
    ((gaussian_elimination_transposed_rec M r c)
       (m - r')%nat pc =? 1) = false.
Proof. intros m n M r r' c c' pc H H0 H1 H2.
  gen M r' c c' pc. induction r; intros; auto; simpl.
  - destruct (hd_error (col_search_ones_right M (m - S r) c)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S r)%nat i =? 1) (seq c (n - c))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite IHr with (c' := c'); auto; try lia. intros i H5. 
        apply col_add_right_ones_col_swapF2_one_bool_false_inclusive_domain_previous with (c' := c'); try lia; auto.
      * rewrite IHr with (c' := c'); auto; try lia. intros i H5. 
        assert (n0 = c) by lia; subst.
        apply col_add_right_ones_one_bool_false_inclusive_domain_previous with (c' := c'); try lia; auto.
    + rewrite IHr with (c' := c'); auto; try lia.
Qed.

Lemma gaussian_elimination_transposed_rec_one_bool_true : forall {m n : nat} (M : MatrixF2 m n) (r r' c c' : nat),
    (r < r' <= m)%nat -> (c' < c)%nat -> (M (m - r')%nat c' =? 1) = true ->
    (forall i : nat, (c' < i < n)%nat -> (M (m - r')%nat i =? 1) = false) ->
    (gaussian_elimination_transposed_rec M r c (m - r')%nat c' =? 1) = true.
Proof. intros m n M r r' c c' H H0 H1 H2.
  gen M r' c c'. induction r; intros; auto; simpl.
  destruct (hd_error (col_search_ones_right M (m - S r) c)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S r)%nat i =? 1) (seq c (n - c))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * apply IHr; try lia; auto.
        apply col_add_right_ones_col_swapF2_one_bool_true; try lia; auto.
        intros i H4. apply col_add_right_ones_col_swapF2_one_bool_false with (c' := c'); try lia; auto.
      * apply IHr; try lia; auto.
        apply col_add_right_ones_one_bool_true; try lia; auto.
        intros i H4. apply col_add_right_ones_one_bool_false with (c' := c'); try lia; auto.
    + apply IHr; try lia; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_col_add_right_ones_one_bool_true : forall {m n : nat} (M : MatrixF2 m n) (r r' c c' : nat),
(r < r' <= m)%nat -> (c' < c)%nat -> (M (m - r')%nat c' =? 1) = true -> 
(gaussian_elimination_transposed_rec
        (col_add_right_ones M (m - r') c') r c (m - r')%nat c' =? 1) = true.
Proof. intros m n M r r' c c' H H0 H1.
  apply gaussian_elimination_transposed_rec_one_bool_true; try lia; auto.
  - apply col_add_right_ones_one_bool_preserve; try lia; auto.
  - intros i H2. apply col_add_right_ones_zero_bool_preserve; try lia; auto. 
Qed.

Lemma gaussian_elimination_transposed_rec_col_add_right_ones_col_swapF2_one_bool_true : forall {m n : nat} (M : MatrixF2 m n) (r r' c c' k : nat),
(r < r' <= m)%nat -> (c' < c < n)%nat -> (M (m - r')%nat k =? 1) = true -> (c' < k < n)%nat ->
(gaussian_elimination_transposed_rec
        (col_add_right_ones (col_swapF2 M c' k) (m - r') c') r c (m - r')%nat c' =? 1) = true.
Proof. intros m n M r r' c c' k H H0 H1 H2.
  apply gaussian_elimination_transposed_rec_col_add_right_ones_one_bool_true; try lia; auto.
  apply col_swapF2_one_bool_preserve; try lia; auto.
Qed.

Lemma col_slice_one_hd_error_original_eq :
  forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col : nat),
    (row_count <= m)%nat -> (col <= pivot_col < n)%nat ->
    col_slice_one_hd_error M row_count col pivot_col = col_slice_one_hd_error_original M row_count col pivot_col.
Proof. intros m n M row_count col pivot_col H H0.
  gen M col pivot_col. induction row_count; intros; auto.
  unfold col_slice_one_hd_error, col_slice_one_hd_error_original in *.
  simpl. bdestruct_all. 
  - destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_above_one_false with (c' := col); try lia; auto.
        rewrite gaussian_elimination_transposed_rec_above_one_false with (c' := col); try lia; auto.
        replace (S (m - S row_count))%nat with (m - row_count)%nat by lia.
        apply IHrow_count; try lia; auto.
        apply col_add_right_ones_col_swapF2_one_bool_preserve; try lia; auto.
        intros i H3. apply col_add_right_ones_col_swapF2_zero_bool_preserve; try lia; auto. 
        apply col_add_right_ones_col_swapF2_one_bool_preserve; try lia; auto.
        intros i H3. apply col_add_right_ones_col_swapF2_zero_bool_preserve; try lia; auto.
      * assert (n0 = col) by lia; subst.
        rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_above_one_false with (c' := col); try lia; auto.
        rewrite gaussian_elimination_transposed_rec_above_one_false with (c' := col); try lia; auto.
        replace (S (m - S row_count))%nat with (m - row_count)%nat by lia.
        apply IHrow_count; try lia; auto.
        apply col_add_right_ones_one_bool_preserve; try lia; auto.
        intros i H3. apply col_add_right_ones_zero_bool_preserve; try lia; auto. 
        apply col_add_right_ones_one_bool_preserve; try lia; auto.
        intros i H3. apply col_add_right_ones_zero_bool_preserve; try lia; auto.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E';
        simpl in E; try discriminate. clear E.
      assert (forall i : nat, (col <= i < n)%nat -> (M (m - S row_count)%nat i =? 1) = false).
      { intros i H2.
        assert (~ In i (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col)))).
        { intros H3. rewrite E' in H3. inversion H3. }
        rewrite filter_In in H3.
        rewrite in_seq in H3.
        destruct (M (m - S row_count)%nat i =? 1) eqn:E''; auto.
        assert ((col <= i < col + (n - col))%nat /\ true = true).
        { split; auto; try lia. }
        apply H3 in H4. contradiction. }
      rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_one_bool_empty_false; try lia; auto.
      rewrite gaussian_elimination_transposed_rec_one_bool_empty_false with (c' := col); try lia; auto.
      replace (S (m - S row_count))%nat with (m - row_count)%nat by lia; auto.
      apply IHrow_count; try lia; auto.
  - assert (pivot_col = col) by lia; subst.
    destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * rewrite col_add_right_ones_col_swapF2_one_bool_preserve; try lia; auto.
        rewrite gaussian_elimination_transposed_rec_col_add_right_ones_col_swapF2_one_bool_true; try lia; auto.
      * assert (n0 = col) by lia; subst.
        rewrite col_add_right_ones_one_bool_preserve; try lia; auto.
        rewrite gaussian_elimination_transposed_rec_col_add_right_ones_one_bool_true; try lia; auto.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E';
        simpl in E; try discriminate. clear E.
      assert (forall i : nat, (col <= i < n)%nat -> (M (m - S row_count)%nat i =? 1) = false).
      { intros i H2.
        assert (~ In i (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col)))).
        { intros H3. rewrite E' in H3. inversion H3. }
        rewrite filter_In in H3.
        rewrite in_seq in H3.
        destruct (M (m - S row_count)%nat i =? 1) eqn:E''; auto.
        assert ((col <= i < col + (n - col))%nat /\ true = true).
        { split; auto; try lia. }
        apply H3 in H4. contradiction. }
      rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_one_bool_empty_false; try lia; auto.
      rewrite gaussian_elimination_transposed_rec_one_bool_empty_false with (c' := col); try lia; auto.
      replace (S (m - S row_count))%nat with (m - row_count)%nat by lia; auto.
      apply IHrow_count; try lia; auto.
Qed.

(* if pivot_col1 < pivot_col2 /\ pivot_row(pivot_col1) = None
then pivot_row(pivot_col2) = None *)
Lemma gaussian_elimination_transposed_rec_get_pivot_row_preserves_pivot_ordering_None : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col1 pivot_col2 : nat),
    (pivot_col1 < pivot_col2)%nat -> 
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col1) = None) ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2) = None).
Proof. intros m n M row_count col pivot_col1 pivot_col2 H H0 (*H1 H2*). 
  gen M col pivot_col1 pivot_col2. induction row_count; intros; auto.
  simpl in *. bdestruct_all.
  - destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * apply IHrow_count with (pivot_col1 := pivot_col1); try lia; auto.
        bdestruct (col <? pivot_col1)%nat; subst; auto.
        simpl in H0. inversion H0.
      * apply IHrow_count with (pivot_col1 := pivot_col1); try lia; auto.
        bdestruct (col <? pivot_col1)%nat; subst; auto.
        simpl in H0. inversion H0.
    + apply IHrow_count with (pivot_col1 := pivot_col1); try lia; auto.
  - destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl;
        bdestruct (col <? pivot_col1)%nat; subst; try lia; auto.
    + apply IHrow_count with (pivot_col1 := pivot_col1); try lia; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_get_pivot_row_greater_than : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col k : nat),
snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col) = Some k -> (row_count < m)%nat -> (m - S row_count < k)%nat.
Proof. intros m n M row_count col pivot_col k H H0.
  gen M col pivot_col k. induction row_count; intros; auto.
  - simpl in *. discriminate.
  - simpl in *.
    destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct (col <? pivot_col)%nat; try lia.
      * bdestruct (col <? n0)%nat; try lia.
        -- apply IHrow_count in H; try lia.
        -- apply IHrow_count in H; try lia.
      * bdestruct (col <? n0)%nat; simpl in *; try lia.
        -- inversion H; try lia.
        -- inversion H; try lia.
    + apply IHrow_count in H; try lia.
Qed.

Lemma gaussian_elimination_transposed_rec_get_pivot_row_preserves_pivot_ordering_Some : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col1 pivot_col2 k1 k2 : nat),
    (col <= pivot_col1 < pivot_col2)%nat -> (row_count <= m)%nat ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2) = Some k2) ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col1) = Some k1) -> (k1< k2)%nat.
Proof. intros m n M row_count col pivot_col1 pivot_col2 k1 k2 H H0 H1 H2.
  gen col pivot_col1 pivot_col2 k1 k2. gen M. induction row_count; intros; auto.
  - simpl in *. discriminate.
  - simpl in *. 
    destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct (col <? pivot_col1)%nat.
      * bdestruct (col <? pivot_col2)%nat; try lia.
        bdestruct (col <? n0)%nat; try lia.
        -- apply IHrow_count with (M := (col_add_right_ones (col_swapF2 M col n0) (m - S row_count) col)) (col := S col) (pivot_col1 := pivot_col1) (pivot_col2 := pivot_col2); try lia; auto.
        -- apply IHrow_count with (M := (col_add_right_ones M (m - S row_count) col)) (col := S col) (pivot_col1 := pivot_col1) (pivot_col2 := pivot_col2); try lia; auto.
      * bdestruct (col <? pivot_col2)%nat; try lia.
        -- bdestruct (col <? n0)%nat; try lia.
           ++ simpl in *.
              apply gaussian_elimination_transposed_rec_get_pivot_row_greater_than in H1; try lia; auto.
              inversion H2; auto.
           ++ simpl in *.
              apply gaussian_elimination_transposed_rec_get_pivot_row_greater_than in H1; try lia; auto.
              inversion H2; auto.
    + apply IHrow_count with (M := M) (col := col) (pivot_col1 := pivot_col1) (pivot_col2 := pivot_col2); try lia; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_ordering_Some : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col1 pivot_col2 k2 : nat),
    (col <= pivot_col1 < pivot_col2)%nat -> (row_count <= m)%nat ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2) = Some k2) ->
    (exists k1 : nat, (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col1) = Some k1) /\ (k1< k2)%nat).
Proof. intros m n M row_count col pivot_col1 pivot_col2 k2 H H0 H1. 
  destruct (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col1)) eqn:E. 
  2:{apply gaussian_elimination_transposed_rec_get_pivot_row_preserves_pivot_ordering_None with (pivot_col2 := pivot_col2) in E; auto. rewrite E in H1. discriminate. lia. }
  exists n0. split; auto.
  apply @gaussian_elimination_transposed_rec_get_pivot_row_preserves_pivot_ordering_Some with (m := m) (n := n) (M := M) (row_count := row_count) (col := col) (pivot_col1 := pivot_col1) (pivot_col2 := pivot_col2) (k1 := n0) (k2 := k2); try lia; auto.
Qed.

(* if pivot_col1 < pivot_col2
then either 
pivot_row(pivot_col2) = None
or
pivot_row(pivot_col1) < pivot_row(pivot_col2) *)
Lemma gaussian_elimination_transposed_rec_get_pivot_row_None_or_preserves_pivot_ordering  : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col1 pivot_col2 : nat),
    (col <= pivot_col1 < pivot_col2)%nat -> (row_count <= m)%nat ->
    ((snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2) = None) \/
       (exists k1 k2 : nat, ((snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col1)) = Some k1) /\ 
          ((snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2)) = Some k2) /\
          (k1 < k2)%nat)).
Proof. intros m n M row_count col pivot_col1 pivot_col2  H H0.
  destruct (snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col2)) eqn:E.
  - right. apply gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_ordering_Some with (pivot_col1 := pivot_col1) in E; try lia; auto.
   destruct E. destruct H1.
   eexists. eexists. split. apply H1. split; auto.
  - left; auto.
Qed.

Lemma fst_gaussian_elimination_transposed_rec_get_pivot_row_M_vector :
  forall {m : nat} (M : VectorF2 m) (row_count : nat),
    fst (gaussian_elimination_transposed_rec_get_pivot_row M row_count 0%nat 0%nat) = M.
Proof. intros m M row_count.
  gen m M. induction row_count; intros; auto; simpl. 
  destruct (hd_error (col_search_ones_right M (m - S row_count) 0%nat)) eqn:E; simpl.
  + unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq 0%nat (1 - 0)%nat)) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n (n :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    assert (n = 0%nat) by lia; subst.
    bdestruct_all. simpl.
    unfold col_add_right_ones.
    unfold col_search_ones_right.
    simpl. auto.
  + apply IHrow_count.
Qed.

Lemma snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_pivot_col_one : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col k : nat),
    (col <= pivot_col < n)%nat -> (row_count <= m)%nat ->
    snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col) =
      Some k ->
    (gaussian_elimination_transposed_rec M row_count col) k pivot_col = one.
Proof. intros m n M row_count col pivot_col k H H0 H1.
  gen M col pivot_col k. induction row_count; intros.
  - simpl in *; try discriminate.
  - simpl in *.
    destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
    + unfold col_search_ones_right in E.
      destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In n0 (n0 :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      bdestruct_all; try lia; simpl.
      * bdestruct (col <? pivot_col)%nat.
        -- try apply IHrow_count; try lia; auto.
        -- assert (pivot_col = col)%nat by lia; subst.
           simpl in *.
           inversion H1; subst.
           rewrite <- F2_beq_true_iff.
           apply gaussian_elimination_transposed_rec_col_add_right_ones_col_swapF2_one_bool_true; try lia; auto.
      * assert (n0 = col) by lia; subst.
        bdestruct (col <? pivot_col)%nat.
        -- try apply IHrow_count; try lia; auto.
        -- assert (pivot_col = col)%nat by lia; subst.
           simpl in *.
           inversion H1; subst.
           rewrite <- F2_beq_true_iff.
           apply gaussian_elimination_transposed_rec_col_add_right_ones_one_bool_true; try lia; auto.
    + apply IHrow_count; try lia; auto.
Qed.

Lemma snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_right_zero : forall {m n : nat} (M : MatrixF2 m n) (row_count col pivot_col k y : nat),
    (col <= pivot_col < n)%nat -> (row_count <= m)%nat ->
    snd (gaussian_elimination_transposed_rec_get_pivot_row M row_count col pivot_col) =
      Some k ->
    (pivot_col < y < n)%nat ->
    (gaussian_elimination_transposed_rec M row_count col) k y = zero.
Proof. intros m n M row_count col pivot_col k y H H0.
  gen M col pivot_col k y. induction row_count; intros; simpl in *; try discriminate.
  destruct (hd_error (col_search_ones_right M (m - S row_count) col)) eqn:E; simpl.
  - unfold col_search_ones_right in E.
    destruct (filter (fun i : nat => M (m - S row_count)%nat i =? 1) (seq col (n - col))) eqn:E'.
    apply hd_error_some_nil in E; contradiction.
    simpl in E. inversion E; subst; clear E.
    assert (H' : In n0 (n0 :: l)) by (simpl; auto).
    rewrite <- E' in H'.
    rewrite filter_In in H'; destruct H' as [H' H''].
    rewrite in_seq in H'.
    bdestruct_all; try lia; simpl.
    * bdestruct (col <? pivot_col)%nat.
      -- apply IHrow_count with (pivot_col := pivot_col); try lia; auto.
      -- assert (pivot_col = col)%nat by lia; subst.
         simpl in *.
         inversion H1; subst.
         rewrite <- F2_neq1_iff_eq0.
         rewrite <- F2_beq_false_iff.
         apply gaussian_elimination_transposed_rec_above_one_false with (c' := col); try lia; auto.
         ++ apply col_add_right_ones_col_swapF2_one_bool_preserve; try lia; auto.
         ++ intros i H5. apply col_add_right_ones_col_swapF2_zero_bool_preserve; try lia; auto.
    * assert (n0 = col) by lia; subst.
      bdestruct (col <? pivot_col)%nat.
      -- apply IHrow_count with (pivot_col := pivot_col); try lia; auto.
      -- assert (pivot_col = col)%nat by lia; subst.
         simpl in *.
         inversion H1; subst.
         rewrite <- F2_neq1_iff_eq0.
         rewrite <- F2_beq_false_iff.
         apply gaussian_elimination_transposed_rec_above_one_false with (c' := col); try lia; auto.
         ++ apply col_add_right_ones_one_bool_preserve; try lia; auto.
         ++ intros i H5. apply col_add_right_ones_zero_bool_preserve; try lia; auto.
  - apply IHrow_count with (pivot_col := pivot_col); try lia; auto.
Qed.

(** i in declaration, i < n in precondition **)
Lemma gaussian_elimination_transposed_rec_get_pivot_row_lin_indep_zero_coef : forall {m n : nat} (M : MatrixF2 m n) (a : VectorF2 n) (k i j : nat),
    (0 < n)%nat -> WF_MatrixF2 M -> WF_MatrixF2 a ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M m 0%nat (n - 1)%nat) = Some k) -> 
    ((fst (gaussian_elimination_transposed_rec_get_pivot_row M m 0%nat (n - 1)%nat)) × a) = ZeroF2 -> (i <= j < n)%nat -> (a i 0%nat = zero).
Proof. intros m n M a k i j H H0 H1 H2 H3 H4. 
  gen M a k i. induction j; intros; simpl; auto.
  - assert (i = 0)%nat by lia; subst.
    bdestruct (n =? 1)%nat; subst; simpl in *.
    + rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_M_vector in H3.
      rewrite <- col_slice_one_hd_error_is_gaussian_elimination_transposed_rec_get_pivot_row in H2; try lia.
      unfold col_slice_one_hd_error in H2.
      rewrite fst_gaussian_elimination_transposed_rec_get_pivot_row_M_vector in H2.
      replace (m - m)%nat with 0%nat in H2 by lia.
      destruct (hd_error (filter (fun r : nat => M r 0%nat =? 1) (seq 0 m))) eqn:E; simpl;
        try discriminate.
      inversion H2; subst.
      destruct (filter (fun r : nat => M r 0%nat =? 1) (seq 0 m)) eqn:E'.
      apply hd_error_some_nil in E; contradiction.
      simpl in E. inversion E; subst; clear E.
      assert (H' : In k (k :: l)) by (simpl; auto).
      rewrite <- E' in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      unfold MmultF2 in H3.
      apply f_equal_inv with (x := k) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      simpl in H3.
      rewrite F2_beq_true_iff in H''.
      rewrite H'' in H3.
      rewrite F2mult_1_l in H3.
      destruct (a 0%nat 0%nat) eqn:E''; try discriminate; auto.
    + destruct (gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_ordering_Some M m 0%nat 0%nat (n - 1)%nat k) as [k' [H6 H7]]; try lia; auto.
      remember H6 as H6'; clear HeqH6'.
      rewrite <- col_slice_one_hd_error_is_gaussian_elimination_transposed_rec_get_pivot_row in H6; try lia.
      rewrite col_slice_one_hd_error_original_eq in H6; try lia.
      unfold col_slice_one_hd_error_original in H6.
      rewrite gaussian_elimination_transposed_rec_get_pivot_row_saturated with (pivot_col := (n - 1)%nat) in H6; try lia.
      replace (m - m)%nat with 0%nat in H6 by lia.
      destruct (filter
                  (fun r : nat =>
                     fst (gaussian_elimination_transposed_rec_get_pivot_row M m 0 (n - 1)%nat) r
                       0%nat =? 1) (seq 0 m)) eqn:E; try discriminate.
      simpl in *. inversion H6; subst.
      assert (H' : In k' (k' :: l)) by (simpl; auto).
      rewrite <- E in H'.
      rewrite filter_In in H'; destruct H' as [H' H''].
      rewrite in_seq in H'.
      rewrite F2_beq_true_iff in H''.
      unfold MmultF2 in H3.
      apply f_equal_inv with (x := k') in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      simpl in H3.
      rewrite <- gaussian_elimination_transposed_rec_get_pivot_row_saturated in *; try lia.
      destruct n.
      * simpl in *. rewrite H2 in H6'. inversion H6'; subst. lia.
      * rewrite <- big_sum_extend_l in H3.
        rewrite H'' in H3.
        rewrite F2mult_1_l in H3.
        simpl in H3.
        assert (Σ2 (fun x : nat => 
                      gaussian_elimination_transposed_rec M m 0 k' (S x) · a (S x) 0%nat) n = 0).
        { rewrite big_sum_0_bounded; auto. intros x H8.
          rewrite snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_right_zero with (pivot_col := 0%nat); try lia; auto.
          rewrite F2mult_0_l. auto. }
        unfold big_sum in *.
        rewrite H8 in H3.
        rewrite F2plus_0_r in H3.
        auto.
  - bdestruct (i =? S j)%nat; subst.
    assert (n > 1)%nat by lia.
    + bdestruct (n =? S (S j))%nat; subst.
      * simpl in *.
        remember H3 as H3'; clear HeqH3'.
        unfold MmultF2 in H3.
        apply f_equal_inv with (x := k) in H3.
        apply f_equal_inv with (x := 0%nat) in H3.
        rewrite <- big_sum_extend_r in H3.
        rewrite <- gaussian_elimination_transposed_rec_get_pivot_row_saturated in *; try lia.
        rewrite snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_pivot_col_one in H3; try lia; auto.
        rewrite F2mult_1_l in H3.
        assert ((Σ2 (fun y : nat => ((gaussian_elimination_transposed_rec M m 0 k y) · (a y 0%nat))%F2) (S j)) = 0).
        { rewrite big_sum_0_bounded; auto. intros x H6.
          rewrite IHj with (M := M) (k := k); try lia; auto.
          simpl. rewrite F2mult_0_r. auto.
          rewrite <- gaussian_elimination_transposed_rec_get_pivot_row_saturated in *; try lia.
          auto. }
        simpl in H3, H6.
        rewrite H6 in H3.
        rewrite F2plus_0_l in H3.
        auto.
      * destruct (gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_ordering_Some M m 0%nat (S j) (n - 1)%nat k) as [k' [H7 H8]]; try lia; auto. 
        rewrite <- gaussian_elimination_transposed_rec_get_pivot_row_saturated in *; try lia.
        remember H3 as H3'; clear HeqH3'.
        unfold MmultF2 in H3.
        apply f_equal_inv with (x := k') in H3.
        apply f_equal_inv with (x := 0%nat) in H3.
        replace n with (S (S j) + (n - S (S j)))%nat in H3 by lia.
        rewrite big_sum_sum in H3.
        rewrite <- big_sum_extend_r in H3.
        assert (Σ2 (fun y : nat => gaussian_elimination_transposed_rec M m 0 k' y · a y 0%nat) 
                  (S j) = 0)%F2.
        { rewrite big_sum_0_bounded; auto. intros x H9.
          rewrite IHj with (M := M) (k := k); try lia; auto.
          rewrite F2mult_0_r. auto.
          rewrite <- gaussian_elimination_transposed_rec_get_pivot_row_saturated in *; try lia.
          auto. }
        assert (Σ2 (fun x : nat => gaussian_elimination_transposed_rec M m 0 k' (S (S j) + x)%nat ·
                                a (S (S j) + x)%nat 0%nat) (n - S (S j)) = 0)%F2.
        { rewrite big_sum_0_bounded; auto. intros x H10.
          rewrite snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_right_zero with (pivot_col := S j); try lia; auto.
          rewrite F2mult_0_l. auto. }
        simpl in *.
        replace (S (S (j + (n - S (S j)))))%nat with n in H3 by lia.
        rewrite H10, H9 in H3.
        rewrite F2plus_0_l, F2plus_0_r in H3.
        rewrite snd_gaussian_elimination_transposed_rec_get_pivot_row_exists_pivot_implies_pivot_col_one in H3; try lia; auto.
        rewrite F2mult_1_l in H3. 
        auto.
    + apply IHj with (M := M) (k := k); try lia; auto.
Qed.

Lemma gaussian_elimination_transposed_rec_get_pivot_row_lin_indep : forall {m n : nat} (M : MatrixF2 m n) (a : VectorF2 n) (k : nat),
    (0 < n)%nat -> WF_MatrixF2 M ->
    (snd (gaussian_elimination_transposed_rec_get_pivot_row M m 0%nat (n - 1)%nat) = Some k) -> 
    linearly_independentF2 (fst (gaussian_elimination_transposed_rec_get_pivot_row M m 0%nat (n - 1)%nat)).
Proof. intros m n M a k H H0 H1.
  unfold linearly_independentF2.
  intros a0 H2 H3.
  F2Module.prep_genmatrix_equality. simpl.
  bdestruct (y =? 0)%nat; subst.
  - bdestruct (x <? n)%nat.
    + rewrite @gaussian_elimination_transposed_rec_get_pivot_row_lin_indep_zero_coef with (m := m) (n := n) (M := M) (k := k) (j := x); try lia; auto.
    + rewrite H2; try lia; auto. 
  - rewrite H2; try lia; auto.
Qed.

Lemma last_col_zero_lin_dep : forall {m n : nat} (M : MatrixF2 m n),
    WF_MatrixF2 M -> (n > 0)%nat ->
    hd_error (filter (fun r : nat => M r (n - 1)%nat =? 1) (seq 0%nat m)) = None ->
    linearly_dependentF2 M.
Proof. intros m n M H H0 H1.
  unfold linearly_dependentF2.
  assert (forall i : nat, In i (seq 0 m) -> M i (n - 1)%nat = zero).
  { intros i H2.
    destruct (filter (fun r : nat => M r (n - 1)%nat =? 1) (seq 0 m)) eqn:E; 
      simpl in H1; try discriminate.
    rewrite <- F2_neq1_iff_eq0.
    intro H3.
    assert (In i []).
    { rewrite <- E.
     rewrite filter_In.
     split; auto.
     rewrite F2_beq_true_iff.
     auto. }
    inversion H4. }
  exists (fun r c : nat => if (r =? n-1)%nat && (c =? 0)%nat then 1 else 0).
  split.
  - unfold WF_MatrixF2.
    intros x y H3.
    bdestruct_all; simpl; auto.
  - split.
    + intro H3.
      apply f_equal_inv with (x := (n - 1)%nat) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      rewrite ! Nat.eqb_refl in H3.
      simpl in H3.
      discriminate.
    + unfold MmultF2.
      F2Module.prep_genmatrix_equality.
      simpl.
      rewrite big_sum_0_bounded; auto.
      intros x0 H3.
      bdestruct_all; simpl;
        try rewrite F2mult_0_r; auto.
      subst.
      bdestruct (x <? m)%nat.
      rewrite H2; try rewrite in_seq; try lia; rewrite F2mult_0_l; auto. 
      rewrite H; try lia; auto.
Qed.

Definition last_col_pivot_row_hd_error_gaussian_elimination_transposed {m n : nat} (M : MatrixF2 m n) : option nat :=
  let GM := gaussian_elimination_transposed M in
  hd_error (filter (fun r : nat => GM r (n - 1)%nat =? 1) (seq 0%nat m)).

Lemma last_col_pivot_row_hd_error_gaussian_elimination_transposed_None_lin_dep :
  forall {m n : nat} (M : MatrixF2 m n),
    WF_MatrixF2 M -> (n > 0)%nat ->
    last_col_pivot_row_hd_error_gaussian_elimination_transposed M = None ->
    linearly_dependentF2 M.
Proof. intros m n M H H0 H1.
  unfold last_col_pivot_row_hd_error_gaussian_elimination_transposed in H1.
  rewrite gaussian_elimination_transposed_preserves_lin_dep.
  apply last_col_zero_lin_dep; auto.
  apply WF_gaussian_elimination_transposed; auto.
Qed.

Lemma last_col_pivot_row_hd_error_gaussian_elimination_transposed_Some_lin_indep :
  forall {m n : nat} (M : MatrixF2 m n) (k : nat),
    WF_MatrixF2 M -> (n > 0)%nat ->
    last_col_pivot_row_hd_error_gaussian_elimination_transposed M = Some k ->
    linearly_independentF2 M.
Proof. intros m n M k H H0 H1.
  unfold last_col_pivot_row_hd_error_gaussian_elimination_transposed in H1.
  rewrite gaussian_elimination_transposed_preserves_lin_indep.
  unfold gaussian_elimination_transposed in *.
  rewrite gaussian_elimination_transposed_rec_get_pivot_row_saturated with (pivot_col := (n - 1)%nat); try lia; auto.
  apply gaussian_elimination_transposed_rec_get_pivot_row_lin_indep with (k := k); try lia; auto.
  rewrite <- col_slice_one_hd_error_is_gaussian_elimination_transposed_rec_get_pivot_row; try lia; auto.
  rewrite col_slice_one_hd_error_original_eq; try lia; auto.
  unfold col_slice_one_hd_error_original.
  replace (m - m)%nat with 0%nat by lia. auto.
Qed.

Lemma no_col_WF_MatrixF2_lin_indep : forall {m : nat} (M : MatrixF2 m 0%nat),
    WF_MatrixF2 M -> linearly_independentF2 M.
Proof. intros m M H.
  unfold linearly_independentF2.
  intros a H0 H1.
  F2Module.prep_genmatrix_equality.
  rewrite H0; try lia; auto.
Qed.

Definition linearly_independentF2_bool {m n : nat} (M : MatrixF2 m n) : bool :=
  if (n =? 0)%nat then true else
    match last_col_pivot_row_hd_error_gaussian_elimination_transposed M with
    | None => false
    | Some k => true
    end.

Lemma linearly_independentF2_bool_true_iff_lin_indepF2 : forall {m n : nat} (M : MatrixF2 m n),
    WF_MatrixF2 M ->
    ((linearly_independentF2_bool M) = true <-> linearly_independentF2 M).
Proof. intros m n M H. split; intros H0.
  - bdestruct (n =? 0)%nat; subst.
    + apply no_col_WF_MatrixF2_lin_indep; auto.
    + unfold linearly_independentF2_bool in H0.
      remember H1 as H1'; clear HeqH1'.
      rewrite <- Nat.eqb_neq in H1.
      rewrite H1 in H0; simpl in H0.
      destruct (last_col_pivot_row_hd_error_gaussian_elimination_transposed M) eqn:E;
        try discriminate.
      apply last_col_pivot_row_hd_error_gaussian_elimination_transposed_Some_lin_indep with (k := n0); try lia; auto.
  - destruct (linearly_independentF2_bool M) eqn:E; auto.
    contradict H0.
    apply lindep_implies_not_linindepF2.
    unfold linearly_independentF2_bool in E.
    bdestruct (n =? 0)%nat; try discriminate.
    destruct (last_col_pivot_row_hd_error_gaussian_elimination_transposed M) eqn:E';
      try discriminate.
    apply last_col_pivot_row_hd_error_gaussian_elimination_transposed_None_lin_dep;
      try lia; auto.
Qed.


(** ** Example calculation of Gaussian elimination ** **)

Definition set_F2matrix (m n : nat) (LLz : list (list F2)) : MatrixF2 m n := 
  (fun r c : nat => nth c (nth r LLz (repeat zero n)) zero).

(** col_count := n, acc := [] **)
Fixpoint print_F2matrix_row_rec {m n : nat} (M : MatrixF2 m n) (row col : nat) (acc : list F2) {struct col} : list F2 :=
  match col with
  | 0%nat => acc
  | S col' => print_F2matrix_row_rec M row col' ((M row col') :: acc)
  end.

Definition print_F2matrix_row {m n : nat} (M : MatrixF2 m n) (row : nat) :=
  print_F2matrix_row_rec M row n [].
  
(** row_count := m, acc := [] **)
Fixpoint print_F2matrix_rec {m n : nat} (M : MatrixF2 m n) (row : nat) (acc : list (list F2)) {struct row} : list (list F2) :=
  match row with
  | 0%nat => acc
  | S row' => print_F2matrix_rec M row' ((print_F2matrix_row M row') :: acc)
  end.

Definition print_F2matrix {m n : nat} (M : MatrixF2 m n) :=
  print_F2matrix_rec M m [].

(* 
Compute print_F2matrix (gaussian_elimination_transposed
(set_F2matrix 3%nat 4%nat 
[[1; 0; 1; 1];
 [1; 1; 1; 0];
 [1; 1; 1; 0]]
)). 
*)
(** 
[[1; 0; 0; 0];
 [1; 1; 0; 0];
 [1; 1; 0; 0]]
**)



