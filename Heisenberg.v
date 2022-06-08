Require Import Psatz.  
Require Import String. 
Require Import Program.
Require Import List.

 
Require Export QuantumLib.Complex.
Require Export QuantumLib.Matrix.
Require Export QuantumLib.Quantum.
Require Export QuantumLib.Eigenvectors.
Require Export QuantumLib.Pad.


(* Some helpers *)

Declare Scope heisenberg_scope.
Delimit Scope heisenberg_scope with H.
Open Scope heisenberg_scope.


(* some helpers *)

Lemma in_simplify : forall {X} (x x1 : X),
  In x1 [x] -> x1 = x.
Proof. intros. simpl in H.
       destruct H. easy. easy.  
Qed.


(*********************************************************)
(* Defining our set of gates and proving some properties *)
(*********************************************************)



(* it will be cool to have Quaternions as an example of a finite, non comm group of size 8 *) 
Inductive Quaternion :=
| p_1
| n_1
| p_i
| n_i
| p_j
| n_j
| p_k
| n_k.

Definition quatNeg (q : Quaternion) : Quaternion :=
  match q with
  | p_1 => n_1
  | n_1 => p_1
  | p_i => n_i
  | n_i => p_i
  | p_j => n_j 
  | n_j => p_j
  | p_k => n_k
  | n_k => p_k
  end.

Definition quatInv (q : Quaternion) : Quaternion :=
  match q with
  | p_1 => p_1
  | n_1 => n_1
  | p_i => n_i
  | n_i => p_i
  | p_j => n_j 
  | n_j => p_j
  | p_k => n_k
  | n_k => p_k
  end.

Lemma quatNeg_inv : forall (q : Quaternion), quatNeg (quatNeg q) = q.
Proof. destruct q; easy.
Qed.

Lemma quatInv_inv : forall (q : Quaternion), quatInv (quatInv q) = q.
Proof. destruct q; easy.
Qed.


(* could split this up into multiple functions like in Types.v, but would overcomplicate *)
Definition quatMul (q1 q2 : Quaternion) : Quaternion :=
  match (q1, q2) with
  | (p_1, _) => q2
  | (_, p_1) => q1
  | (n_1, _) => quatNeg q2
  | (_, n_1) => quatNeg q1
  | (p_i, p_i) => n_1
  | (p_i, n_i) => p_1
  | (p_i, p_j) => p_k
  | (p_i, n_j) => n_k
  | (p_i, p_k) => n_j
  | (p_i, n_k) => p_j
  | (n_i, p_i) => p_1
  | (n_i, n_i) => n_1
  | (n_i, p_j) => n_k
  | (n_i, n_j) => p_k
  | (n_i, p_k) => p_j
  | (n_i, n_k) => n_j
  | (p_j, p_i) => n_k
  | (p_j, n_i) => p_k
  | (p_j, p_j) => n_1
  | (p_j, n_j) => p_1
  | (p_j, p_k) => p_i
  | (p_j, n_k) => n_i
  | (n_j, p_i) => p_k
  | (n_j, n_i) => n_k
  | (n_j, p_j) => p_1
  | (n_j, n_j) => n_1
  | (n_j, p_k) => n_i
  | (n_j, n_k) => p_i
  | (p_k, p_i) => p_j
  | (p_k, n_i) => n_j
  | (p_k, p_j) => n_i
  | (p_k, n_j) => p_i
  | (p_k, p_k) => n_1
  | (p_k, n_k) => p_1
  | (n_k, p_i) => n_j
  | (n_k, n_i) => p_j
  | (n_k, p_j) => p_i
  | (n_k, n_j) => n_i
  | (n_k, p_k) => p_1
  | (n_k, n_k) => n_1
  end.

Fixpoint quatBigMul (qs : list Quaternion) : Quaternion := 
  match qs with
  | nil => p_1 
  | q :: qs' => quatMul q (quatBigMul qs')
  end. 


 
Infix "*q" := quatMul (at level 40, left associativity) : heisenberg_scope. 


Lemma quatMul_comm : forall (q1 q2 : Quaternion), 
    q1 *q q2 = q2 *q q1 \/ q1 *q q2 = quatNeg (q2 *q q1).
Proof. intros. 
       destruct q1;
       destruct q2;
       try (left; easy); try (right; easy).  
Qed.

Lemma quatMul_assoc : forall (q1 q2 q3 : Quaternion), (q1 *q q2) *q q3 = q1 *q (q2 *q q3).
Proof. intros. 
       destruct q1;
       destruct q2;
       destruct q3;
       easy. 
Qed.

Lemma quatInv_l : forall (q : Quaternion), (quatInv q) *q q = p_1.
Proof. intros; destruct q; easy. Qed.

Lemma quatInv_r : forall (q : Quaternion), q *q (quatInv q) = p_1.
Proof. intros; destruct q; easy. Qed.

Lemma quatBigMul_app : forall (l1 l2 : list Quaternion),
  (quatBigMul l1) *q (quatBigMul l2) = quatBigMul (l1 ++ l2).
Proof. induction l1 as [| h]; try easy.
       intros. simpl. 
       rewrite quatMul_assoc, IHl1; easy.
Qed.



Definition translate_quat (q : Quaternion) : Square 2 :=
  match q with
  | p_1 => (I 2)
  | p_i => σx
  | p_j => σy
  | p_k => σz
  | n_1 => -1 .* (I 2)
  | n_i => -1 .* σx
  | n_j => -1 .* σy
  | n_k => -1 .* σz
  end. 






(* a is valid if it is a Ci multiple of a Pauli gate *)
Inductive valid_base_gate : Square 2 -> Prop :=
| GI : valid_base_gate (I 2)
| GX : valid_base_gate σx
| GY : valid_base_gate σy
| GZ : valid_base_gate σz
| Si : forall (a : Square 2), valid_base_gate a -> valid_base_gate (Ci .* a).


Lemma WF_valid_base_gate : forall (a : Square 2),
  valid_base_gate a -> WF_Matrix a.
Proof. intros. 
       induction H; auto with wf_db.
Qed.

#[export] Hint Resolve WF_valid_base_gate : wf_db. 

Lemma valid_base_gate_unitary : forall (a : Square 2),
  valid_base_gate a -> WF_Unitary a.
Proof. intros. 
       induction H; auto with unit_db.
       apply scale_unitary; auto; lca.
Qed.

#[export] Hint Resolve valid_base_gate_unitary : unit_db. 

Lemma valid_base_gate_det_1 : forall (a : Square 2), 
  valid_base_gate a -> (Determinant a = C1 \/ Determinant a = -C1).
Proof. intros. 
       induction H.
       5 : rewrite <- (Mmult_1_l _ _ a), <- Mscale_mult_dist_l; auto with wf_db;
           rewrite <- Determinant_multiplicative;
           destruct IHvalid_base_gate; rewrite H0; try (right; lca); left; lca.
       all : simpl; try (left; lca); try (right; lca).
Qed.

Lemma valid_base_gate_mult : forall (a b : Square 2),
  valid_base_gate a -> valid_base_gate b ->
  valid_base_gate (a × b).
Proof. intros. 
       induction H.
       rewrite Mmult_1_l; try apply WF_valid_base_gate; easy.
       all : induction H0.
       all : try rewrite XtimesXid; try rewrite YtimesYid; try rewrite ZtimesZid; try apply GI.
       all : try rewrite Mmult_1_r; auto with wf_db; try apply GX; try apply GY; try apply GZ.
       replace (σx × σy) with (Ci .* σz) by lma'; apply Si; apply GZ.
       replace (σx × σz) with (Ci .* (Ci .* (Ci .* σy))) by lma'; repeat apply Si; apply GY.
       distribute_scale; apply Si; easy. 
       replace (σy × σx) with (Ci .* (Ci .* (Ci .* σz))) by lma'; repeat apply Si; apply GZ.
       replace (σy × σz) with (Ci .* σx) by lma'; apply Si; apply GX.
       distribute_scale; apply Si; easy. 
       replace (σz × σx) with (Ci .* σy) by lma'; apply Si; apply GY.
       replace (σz × σy) with (Ci .* (Ci .* (Ci .* σx))) by lma'; repeat apply Si; apply GX.
       distribute_scale; apply Si; easy. 
       apply Si; rewrite <- (Mmult_1_r _ _ a); auto with wf_db.  
       all : try (distribute_scale; apply Si; easy). 
       rewrite Mscale_mult_dist_l; apply Si; easy.
Qed.


(**************************)
(* Defining Vector typing *)
(**************************)


Definition vec_is_plus1_eig {n} (v : Vector n) (a : Square n) :=
  WF_Matrix v /\ a × v = v.

Notation "v :' a" := (vec_is_plus1_eig v a) (at level 62) : heisenberg_scope. 



Ltac solveType := intros; split; auto with wf_db; try lma'; try solve_matrix.


Lemma all_hastype_I : forall (v : Vector 2), WF_Matrix v -> v :' (I 2).
Proof. solveType. Qed.
  
Lemma X_plus1_eig : ∣+⟩ :' σx. Proof. solveType. Qed.
Lemma Y_plus1_eig : ∣R⟩ :' σy. Proof. solveType. Qed.
Lemma Z_plus1_eig : ∣0⟩ :' σz. Proof. solveType. Qed.

Lemma B_hastype_XX : ∣Φ+⟩ :' σx ⊗ σx. Proof. solveType. Qed.


#[export] Hint Resolve all_hastype_I X_plus1_eig Y_plus1_eig Z_plus1_eig B_hastype_XX : eig_db.

(* proving that some statements are not true *)
Lemma not_X_plus1_eig_Yp : ~ (∣R⟩ :' σx). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       do 2 apply (f_equal_inv O) in H0.
       replace ((σx × ∣R⟩) 0%nat 0%nat) with (Ci / (√ 2)) in H0 by lca. 
       replace (∣R⟩ 0%nat 0%nat) with (1 / (√ 2)) in H0 by lca. 
       apply (Cmult_simplify _ _ (√ 2) (√ 2)) in H0; auto.
       unfold Cdiv in H0. 
       do 2 rewrite <- Cmult_assoc in H0.
       rewrite Cinv_l in H0.
       do 2 rewrite Cmult_1_r in H0.
       apply (f_equal snd) in H0; simpl in H0.
       apply c_proj_eq; easy.
       apply Csqrt2_neq_0.
Qed.

Lemma not_X_plus1_eig_Zp : ~ (∣0⟩ :' σx). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       do 2 apply (f_equal_inv O) in H0.
       replace ((σx × ∣0⟩) 0%nat 0%nat) with C0 in H0 by lca. 
       replace (∣0⟩ 0%nat 0%nat) with C1 in H0 by lca. 
       easy. 
Qed.
   
Lemma not_Y_plus1_eig_Xp : ~ (∣+⟩ :' σy). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       apply (f_equal_inv 1%nat) in H0.
       apply (f_equal_inv O) in H0.
       replace ((σy × ∣+⟩) 1%nat 0%nat) with (Ci / (√ 2)) in H0 by lca. 
       replace (∣+⟩ 1%nat 0%nat) with (1 / (√ 2)) in H0 by lca. 
       apply (Cmult_simplify _ _ (√ 2) (√ 2)) in H0; auto.
       unfold Cdiv in H0. 
       do 2 rewrite <- Cmult_assoc in H0.
       rewrite Cinv_l in H0.
       do 2 rewrite Cmult_1_r in H0.
       apply (f_equal snd) in H0; simpl in H0.
       apply c_proj_eq; easy.
       apply Csqrt2_neq_0.
Qed.

Lemma not_Y_plus1_eig_Zp : ~ (∣0⟩ :' σy). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       do 2 apply (f_equal_inv O) in H0.
       replace ((σy × ∣0⟩) 0%nat 0%nat) with C0 in H0 by lca. 
       replace (∣0⟩ 0%nat 0%nat) with C1 in H0 by lca. 
       easy. 
Qed.


Lemma not_Z_plus1_eig_Xp : ~ (∣+⟩ :' σz). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       apply (f_equal_inv 1%nat) in H0.
       apply (f_equal_inv O) in H0.
       replace ((σz × ∣+⟩) 1%nat 0%nat) with (-C1 / (√ 2)) in H0 by lca. 
       replace (∣+⟩ 1%nat 0%nat) with (C1 / (√ 2)) in H0 by lca. 
       apply (Cmult_simplify _ _ (√ 2) (√ 2)) in H0; auto.
       unfold Cdiv in H0. 
       do 2 rewrite <- Cmult_assoc in H0.
       rewrite Cinv_l in H0.
       do 2 rewrite Cmult_1_r in H0.
       apply (Cplus_simplify _ _ C1 C1) in H0; auto.
       replace (- C1 + C1) with C0 in H0 by lca.
       replace (C1 + C1) with C2 in H0 by lca.
       apply (f_equal fst) in H0; simpl in H0.
       assert (H' : 2%R <> 0). lra.
       rewrite H0 in H'; easy.
       apply Csqrt2_neq_0.
Qed.

Lemma not_Z_plus1_eig_Yp : ~ (∣R⟩ :' σz). 
Proof. unfold not; intros. 
       apply C1_neq_C0. 
       destruct H.
       apply (f_equal_inv 1%nat) in H0.
       apply (f_equal_inv O) in H0.
       replace ((σz × ∣R⟩) 1%nat 0%nat) with (-Ci / (√ 2)) in H0 by lca. 
       replace (∣R⟩ 1%nat 0%nat) with (Ci / (√ 2)) in H0 by lca. 
       apply (Cmult_simplify _ _ (√ 2) (√ 2)) in H0; auto.
       unfold Cdiv in H0. 
       do 2 rewrite <- Cmult_assoc in H0.
       rewrite Cinv_l in H0.
       do 2 rewrite Cmult_1_r in H0.
       apply (Cplus_simplify _ _ Ci Ci) in H0; auto.
       replace (- Ci + Ci) with C0 in H0 by lca.
       replace (Ci + Ci) with (0,2) in H0 by lca.
       apply (f_equal snd) in H0; simpl in H0.
       assert (H' : 2%R <> 0). lra.
       rewrite H0 in H'; easy.
       apply Csqrt2_neq_0.
Qed.
 


(* not actually true... 
Lemma valid_base_gate_has_plus1_eig : forall (a : Square 2),
  valid_base_gate a -> exists v, v :' a.
Proof. intros.
       induction H. 
       - exists ∣0⟩; apply all_hastype_I; auto with wf_db.
       - exists ∣+⟩; auto with eig_db.
       - exists ∣R⟩; auto with eig_db.
       - exists ∣0⟩; auto with eig_db.
       - destruct IHvalid_base_gate as [v H0].
         exists (Ci .* v).
         destruct H0; split; auto with wf_db.
         distribute_scale.



Lemma eq_plus1_eig_eq : forall (a b : Square 2),
  valid_base_gate a -> valid_base_gate b ->
  (forall v, v :' a <-> v :' b) <-> a = b.
Proof. intros; split; intros.
       induction H.
       - induction H0; try easy.
         + apply except.
           apply not_X_plus1_eig_Yp.
           apply H1.
           apply all_hastype_I; auto with wf_db. 
         + apply except.
           apply not_Y_plus1_eig_Xp.
           apply H1.
           apply all_hastype_I; auto with wf_db. 
         + apply except.
           apply not_Z_plus1_eig_Xp.
           apply H1.
           apply all_hastype_I; auto with wf_db. 
         + 

*)





(**************************************************************)
(* Defining pairHasType, which is a helper function for later *)
(**************************************************************)
 
Definition pairHasType {n : nat} (p : Vector n * C) (U : Square n) : Prop := 
  WF_Matrix (fst p) /\ Eigenpair U p.




(***************************)
(* Writing actual programs *)
(***************************)

Notation gateType n := (Square n * Square n)%type.


(* Eigenvector semantics def *)
Definition progHasType_E {n : nat} (prog : Square n) (T : gateType n) : Prop :=
  forall v c, pairHasType (v, c) (fst T) -> pairHasType (prog × v, c) (snd T). 


(* Heisenberg semantics def *)
Definition progHasType_H {n} (prog : Square n) (T : gateType n) : Prop :=
  prog × (fst T) = (snd T) × prog.


Lemma Hsem_implies_Esem : forall {n} (prog : Square n) (T : gateType n),
  WF_Unitary prog -> 
  progHasType_H prog T -> progHasType_E prog T.
Proof. intros. 
       unfold progHasType_E, progHasType_H, pairHasType in *. 
       intros; destruct T as [A B]; simpl in *.
       destruct H; destruct H1.
       split; auto with wf_db.
       unfold Eigenpair in *; simpl in *.
       rewrite <- Mmult_assoc, <- H0, Mmult_assoc, H3.
       distribute_scale; reflexivity.
Qed.


Lemma Esem_implies_Hsem : forall {n} (prog : Square n) (T : gateType n),
  WF_Unitary prog -> WF_Unitary (fst T) -> WF_Unitary (snd T) ->
  progHasType_E prog T -> progHasType_H prog T.
Proof. intros.
       unfold progHasType_E, progHasType_H, pairHasType in *. 
       intros; destruct T as [A B]; simpl in *.
       assert (H': eq_eigs A (prog† × B × prog)). 
       { intros p H3 H4. 
         destruct p; simpl in *.
         apply eig_unit_conv; try easy.  
         apply H2; easy. }
       apply eq_eigs_implies_eq_unit in H'; auto with U_db.
       2 : repeat apply Mmult_unitary; auto with U_db; apply transpose_unitary; auto.
       rewrite H'.
       do 2 (rewrite <- Mmult_assoc).
       destruct H as [Hwf Hu].
       apply Minv_flip in Hu; auto with wf_db. 
       rewrite Hu, Mmult_1_l; auto.
       destruct H1; easy. 
Qed. 



(* takes two vecTypes and makes gateType *)
Definition formGateType {n} (A B : Square n) : gateType n := (A, B).

Definition gateApp {n : nat} (U A : Square n) : Square n :=
  U × A × U†.

(* NOTE!! We use the second def, formGateType', here since it works better with singletons *)
Notation "U ::' F" := (progHasType_E U F) (at level 61) : heisenberg_scope.
Infix "→" := formGateType (at level 60, no associativity).
Notation "U [ A ]" := (gateApp U A) (at level 0) : heisenberg_scope. 


Lemma type_is_app : forall (n: nat) (U A B : Square n),
  WF_Unitary U -> WF_Unitary A -> WF_Unitary B ->
  (U ::' A → B  <-> U [ A ] = B).
Proof. intros n U A B [Huwf Hu] [Hawf Ha] [Hbwf Hb]. split.
       - intros. 
         apply Esem_implies_Hsem in H; simpl; auto; try (split; easy).
         unfold gateApp, progHasType_H in *; simpl in H.
         rewrite H.
         apply Minv_flip in Hu; try easy.
         rewrite Mmult_assoc, Hu, Mmult_1_r; auto.
         apply transpose_unitary; split; auto.
       - intros. 
         apply Hsem_implies_Esem; simpl; auto; try (split; easy).
         unfold gateApp, progHasType_H in *; simpl.
         rewrite <- H.
         repeat rewrite Mmult_assoc.
         rewrite Hu, Mmult_1_r; easy.
Qed.


(* Gate definitions *)

Definition H' := hadamard.
Definition S' := Sgate.
Definition T' := Tgate.
Definition CNOT :=  cnot.


Definition seq {n : nat} (U1 U2 : Square n) := U2 × U1. 

Infix ";" := seq (at level 52, right associativity).


(* lemmas about seq*)
Lemma app_comp : forall (n : nat) (U1 U2 A B C : Square n),
  U1[A] = B -> U2[B] = C -> (U2×U1) [A] = C.
Proof. unfold gateApp. intros n U1 U2 A B C H1 H2. rewrite <- H2. rewrite <- H1.
       rewrite Mmult_adjoint. do 3 rewrite <- Mmult_assoc. reflexivity. 
Qed.

Lemma SeqTypes : forall {n} (g1 g2 : Square n) (A B C : Square n),
    g1 ::' A → B ->
    g2 ::' B → C ->
    g1 ; g2 ::' A → C.
Proof. intros n g1 g2 A B C. 
       simpl. intros.
       unfold progHasType_E in *; intros; simpl in *. 
       apply H in H1.
       apply H0 in H1.
       unfold seq. 
       rewrite (Mmult_assoc g2 g1 v).
       easy. 
Qed.
       

Lemma seq_assoc : forall {n} (p1 p2 p3 : Square n) (T : gateType n),
    p1 ; (p2 ; p3) ::' T <-> (p1 ; p2) ; p3 ::' T.
Proof. intros n p1 p2 p3 A. unfold seq. split.
       - rewrite Mmult_assoc. easy.
       - rewrite Mmult_assoc. easy.
Qed.





Lemma Types_I : forall {n} (p : Square n), WF_Unitary p -> p ::' (I n) → (I n).
Proof. intros.
       apply Hsem_implies_Esem; auto.
       unfold progHasType_H; simpl. 
       destruct H.
       rewrite Mmult_1_l, Mmult_1_r; easy. 
Qed.
 

(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI1 : forall (p : Square 2), WF_Unitary p -> p ::' (I 2) → (I 2).
Proof. apply Types_I. Qed.


Lemma TypesI2 : forall (p : Square 4), WF_Unitary p -> p ::' (I 2) ⊗ (I 2) → (I 2) ⊗ (I 2).
Proof. intros p H.
       assert (H0 : I 2 ⊗ I 2 = I 4).
       { simpl. rewrite id_kron. easy. }
       rewrite H0.
       apply Types_I; auto.
Qed.


Lemma TypesIn : forall (n : nat) (p : Square (2^n)), WF_Unitary p -> p ::' n ⨂ (I 2) → n ⨂ (I 2).
Proof. intros n p H. 
       rewrite kron_n_I.
       apply Types_I; auto.
Qed.


Hint Resolve TypesI1 TypesI2 TypesIn : base_types_db.


(* Formal statements of all the transformations listed in figure 1 of Gottesman*)



(*********************)
(** Structural rules *)
(*********************)







Lemma arrow_sub : forall {n} (g : Square n) (A A' B B' : Square n),
  (forall l, pairHasType l A' -> pairHasType l A) ->
  (forall r, pairHasType r B -> pairHasType r B') ->
  g ::' A → B ->
  g ::' A' → B'.
Proof. intros. simpl in *.
       unfold progHasType_E in *; simpl in *.
       intros.
       apply H0.
       apply H1.
       apply H.
       apply H2.
Qed.


Hint Resolve arrow_sub : subtype_db.



(***************)
(* Arrow rules *)
(***************)



Lemma arrow_mul : forall {n} (p : Square n) (A A' B B' : Square n),
    WF_Unitary p ->
    WF_Unitary A -> WF_Unitary A' ->
    WF_Unitary B -> WF_Unitary B' ->
    p ::' A → A' ->
    p ::' B → B' ->
    p ::' A × B → A' × B'.
Proof. intros.
       apply Hsem_implies_Esem; auto.
       apply Esem_implies_Hsem in H4; apply Esem_implies_Hsem in H5; simpl in *; auto.
       unfold progHasType_H in *; simpl in *.
       rewrite <- Mmult_assoc, H4, Mmult_assoc, H5, <- Mmult_assoc. 
       easy.
Qed.


(*
Lemma arrow_scale : forall {n} (p : Square n) (A A' : vecType n) (c : C),
    c <> C0 -> p ::' A → A' -> p ::' c · A → c · A'.
Proof. intros n p A A' c H0 [H _]. 
       apply kill_true.
       unfold singGateType' in *.
       intros v x H1. simpl in *.
       intros A0 H2.
       unfold pairHasType in *.
       apply in_scale in H2.
       destruct H2 as [a' [H2 H2']].
       assert (H' : Eigenpair a' (p × v, x / c)). 
       { apply H. intros A1 H3. 
         apply (eigen_scale_div _ _ _ c).
         apply H0.
         assert (H' : c * (x / c) = x). 
         { C_field_simplify. reflexivity. apply H0. }
         rewrite H'. apply H1.
         apply in_scale_rev. apply H3.
         apply H2. }
       rewrite H2'.
       assert (H'' : x = (x / c) * c). 
       { C_field_simplify. reflexivity. apply H0. }
       rewrite H''.
       apply eigen_scale.
       apply H'.
Qed.           


Lemma arrow_i : forall {n} (p : Square n) (A A' : vecType n),
    p ::' A → A' ->
    p ::' i A → i A'.
Proof. unfold i. intros. 
       apply arrow_scale. 
       apply C0_snd_neq. simpl. easy. 
       apply H.
Qed.

Lemma arrow_neg : forall {n} (p : Square n) (A A' : vecType n),
    p ::' A → A' ->
    p ::' -A → -A'.
Proof. unfold neg. intros.
       apply arrow_scale.
       rewrite <- Cexp_PI.
       apply Cexp_nonzero.
       apply H.
Qed.



Lemma eq_arrow_r : forall {n} (g : Square n) (A B B' : vecType n),
    g ::' A → B ->
    B = B' ->
    g ::' A → B'.
Proof. intros; subst; easy. Qed.
*)


(*****************************)
(** Typing Rules for Tensors *)
(*****************************)

Local Open Scope nat_scope.


Definition vecTypeT (len : nat) := (list (Square 2)).

Definition vecTypeT' := (list (Square 2)).


Definition X' : vecTypeT 1 := [σx].
Definition Z' : vecTypeT 1 := [σz].
Definition I' : vecTypeT 1 := [I 2].


Definition tensorT {n m} (A : vecTypeT n) (B : vecTypeT m) : vecTypeT (n + m) := A ++ B.

Fixpoint mulT' (A B : vecTypeT') : vecTypeT' :=
  match A with
  | [] => B
  | (a :: As) => 
    match B with 
    | [] => A
    | (b :: Bs) => (a × b :: mulT' As Bs)
    end
  end.


Definition mulT {n : nat} (A B : vecTypeT n) : vecTypeT n := mulT' A B.


Definition scaleT (c : C) {n : nat} (A : vecTypeT n) : vecTypeT n :=
  match A with
  | [] => []
  | (h :: t) => (c .* h :: t)
  end.



Definition formGateTypeT {n : nat} (A B : vecTypeT n) : gateType n := (⨂ A) → (⨂ B).


Infix "'⊗'" := tensorT (at level 51, right associativity) : heisenberg_scope. 
Notation "A →' B" := (formGateTypeT A B) (at level 60, no associativity) : heisenberg_scope.


Definition WF_vtt {len : nat} (vt : vecTypeT len) := length vt = len.


(* very similar to def's in pad.v but its a lot nicer to have the out of bounds case be the
   identity instead of the zero matrix *)
Definition prog_smpl_app (prg_len : nat) (bit : nat) (U : Square 2) : Square (2^prg_len) :=
  match bit <? prg_len with
  | true => pad_u prg_len bit U
  | false => I (2^prg_len)
  end.

                          
Definition prog_ctrl_app (prg_len ctrl targ : nat) (U : Square 2) : Square (2^prg_len) :=
  match ((ctrl <? prg_len) && (targ <? prg_len) && (negb (ctrl =? targ))) with  
  | true => pad_ctrl prg_len ctrl targ U
  | false => I (2^prg_len)
  end.
                      



Lemma unit_prog_smpl_app : forall (prg_len : nat) (U : Square 2) (bit : nat),
  WF_Unitary U -> WF_Unitary (prog_smpl_app prg_len bit U). 
Proof. intros.  
       unfold prog_smpl_app.
       bdestruct (bit <? prg_len); auto with unit_db.
       apply pad_u_unitary; easy.
Qed.

Lemma unit_prog_ctrl_app : forall (prg_len : nat) (U : Square 2) (ctrl targ : nat),
  WF_Unitary U -> WF_Unitary (prog_ctrl_app prg_len ctrl targ U). 
Proof. intros.
       unfold prog_ctrl_app.
       bdestruct_all; simpl; auto with unit_db.
       apply pad_ctrl_unitary; easy.
Qed.


(*

Lemma big_tensor_simpl : forall {n m} (A : vecTypeT n) (B : vecTypeT m) (a : vecType 2),
  (forall a, In a A -> uni_vecType a) -> (forall b, In b B -> uni_vecType b) 
  -> uni_vecType a ->
  ⨂' (A ++ [a] ++ B) = (⨂' A) ⊗' a ⊗' (⨂' B).
Proof. induction A as [| h].
       - intros.
         apply univ_tensor_list in H0.
         rewrite big_tensor_1_l; auto with univ_db.
       - intros. simpl.  
         rewrite cons_conc. 
         rewrite IHA; auto with univ_db.
         assert (H': forall (n : nat), 2^n + (2^n + 0) = 2 * 2^n). { nia. }
         repeat (rewrite H'). 
         rewrite <- tensor_assoc; auto with univ_db.
         rewrite length_change.
         reflexivity.
         apply H; left; auto. 
         apply univ_tensor_list; auto.
         all : intros; try (apply H; right; easy). 
         apply univ_tensor_list in H0.
         auto with univ_db.
Qed.



Lemma nth_tensor_inc : forall (n len : nat) (A : vecTypeT len),
  (forall a, In a A -> uni_vecType a) -> 
  n < len -> WF_vtt A -> ⨂' A = (⨂' (firstn n A)) ⊗' (nth n A I') ⊗' (⨂' (skipn (S n) A)).
Proof. intros. 
       rewrite <- (@big_tensor_simpl n (len - n) (firstn n A) (skipn (S n) A) (nth n A I')).
       rewrite <- nth_inc.
       reflexivity. 
       rewrite H1.
       assumption. 
       all : intros; apply H.
       - rewrite <- (firstn_skipn n).
         apply in_or_app.
         auto. 
       - rewrite <- (firstn_skipn (S n)).
         apply in_or_app.
         auto. 
       - apply nth_In.
         rewrite H1; auto.
Qed.


Lemma switch_tensor_inc : forall (n len : nat) (A : vecTypeT len) (x : vecType 2),
  (forall a, In a A -> uni_vecType a) -> uni_vecType x ->
  n < len -> WF_vtt A -> ⨂' (switch A x n) = (⨂' (firstn n A)) ⊗' x ⊗' (⨂' (skipn (S n) A)).
Proof. intros. 
       rewrite <- (@big_tensor_simpl n (len - n) (firstn n A) (skipn (S n) A) x); auto.
       rewrite <- switch_inc.
       reflexivity. 
       rewrite H2.
       assumption. 
       all : intros; apply H.
       - rewrite <- (firstn_skipn n).
         apply in_or_app.
         auto. 
       - rewrite <- (firstn_skipn (S n)).
         apply in_or_app.
         auto. 
Qed.


Lemma sgt'_reduce_smpl : forall {n m : nat} (u : Square 2) (a b : vecType 2) 
                                (A : vecType n) (B : vecType m),
  Singleton A -> Singleton B -> Singleton a -> Singleton b ->
  WF_Unitary u -> uni_vecType a -> uni_vecType b ->
  uni_vecType A -> uni_vecType B ->
  singGateType' u (a, b) -> 
  singGateType' ((I n) ⊗ u ⊗ (I m)) (A ⊗' a ⊗' B, A ⊗' b ⊗' B).  
Proof. intros n m u a b A B HSA HSB HSa HSb Huu Hua Hub HuA HuB Hsgt.
       apply singleton_simplify in HSA;
       destruct HSA as [A' HSA];
       apply singleton_simplify in HSB;
       destruct HSB as [B' HSB];
       apply singleton_simplify in HSa;
       destruct HSa as [a' HSa];
       apply singleton_simplify in HSb;
       destruct HSb as [b' HSb];       
       rewrite HSA, HSB, HSa, HSb in *.    
       apply sgt_implies_sgt'; try easy. 
       apply sgt'_implies_sgt in Hsgt; try easy.
       unfold singGateType in *.
       intros.
       simpl in *;
       destruct H as [H | F];
       destruct H0 as [H0 | F0]; try easy.
       rewrite <- H, <- H0.
       rewrite kron_assoc. 
       assert (H' : m + (m + 0) = 2 * m). { nia. }
       assert (H'' : (n * 2) * m = n * (2 * m)). { nia. } 
       repeat (rewrite H'). repeat (rewrite H'').
       do 4 (rewrite kron_mixed_product).  
       repeat rewrite Mmult_1_l, Mmult_1_r.
       rewrite (Hsgt a' b'); 
       try easy; 
       try (left; easy).
       all : auto with wf_db; 
         try (apply HuB; left; auto); try (apply HuA; left; auto).
       apply Huu.
Qed.


Lemma tensor_smpl : forall (prg_len bit : nat) (g : Square 2) 
                           (A : vecTypeT prg_len) (a : vecType 2),
    (forall a : vecType 2, In a A -> uni_vecType a) ->
    Singleton (⨂' A) -> Singleton a ->
    WF_Unitary g -> uni_vecType (nth bit A I') -> uni_vecType a ->
    bit < prg_len -> WF_vtt A -> 
    g ::' ((nth bit A I') → a) ->
    (prog_smpl_app prg_len g bit) ::'  A →' (switch A a bit).
Proof. intros prg_len bit g A a Huvt SA Sa Hug Hunb Hua Hbpl Hwf H. 
       simpl. 
       rewrite (nth_tensor_inc bit prg_len A); try easy.
       rewrite (switch_tensor_inc bit prg_len A a); try easy. 
       unfold prog_smpl_app.
       apply kill_true.
       repeat (rewrite firstn_length_le).
       repeat (rewrite skipn_length').
       repeat (rewrite switch_len).
       unfold WF_vtt in Hwf. 
       rewrite Hwf in *.
       repeat (rewrite (easy_pow3 prg_len bit)); try easy.  
       bdestruct (bit <? prg_len); try lia. 
       apply sgt'_reduce_smpl; try easy.
       apply (S_tensor_subset _ A _). 
       apply SA. apply firstn_subset.
       apply (S_tensor_subset _ A _). 
       apply SA. apply skipn_subset.
       apply (S_big_tensor_conv _ A _).
       apply SA. apply nth_In.
       rewrite Hwf; assumption.
       destruct H as [H _].  
       - assert (H' : forall a : vecType 2, In a (firstn bit A) -> uni_vecType a).
         { intros; apply Huvt.
           rewrite <- (firstn_skipn bit).
           apply in_or_app; auto. }
         apply univ_tensor_list in H'.
         rewrite firstn_length_le in H'.
         auto. rewrite Hwf; nia. 
       - assert (H' : forall a : vecType 2, In a (skipn (S bit) A) -> uni_vecType a).
         { intros; apply Huvt.
           rewrite <- (firstn_skipn (S bit)).
           apply in_or_app; auto. }
         apply univ_tensor_list in H'.
         rewrite skipn_length, Hwf in H'.
         replace ((prg_len - bit) - 1) with (prg_len - (S bit)) by lia.
         auto.  
       - apply H.
       - rewrite Hwf; lia. 
Qed.

           

Lemma CX_is_CNOT : (∣0⟩⟨0∣ ⊗ (I 2) .+ ∣1⟩⟨1∣ ⊗ σx) = cnot. 
Proof. lma'. 
Qed.

Lemma CX_is_NOTC : ((Matrix.I 2) ⊗ ∣0⟩⟨0∣ .+ σx ⊗ ∣1⟩⟨1∣) = notc. 
Proof. lma'. 
Qed.


Definition CZ := (∣0⟩⟨0∣ ⊗ (I 2) .+ ∣1⟩⟨1∣ ⊗ σz).


Lemma WF_CZ : WF_Matrix CZ. 
Proof. unfold CZ. 
       auto with wf_db.
Qed.

Hint Resolve WF_CZ : wf_db.

Lemma unit_CZ : WF_Unitary CZ. 
Proof. split; auto with wf_db. 
       lma'. Qed.


Hint Resolve unit_CZ : unit_db.
                


Lemma adj_ctrlX_is_cnot : forall (prg_len ctrl : nat),
  1 + ctrl < prg_len ->
  prog_ctrl_app prg_len σx ctrl (1 + ctrl) = 
  I (2^ctrl) ⊗ cnot ⊗ I (2^(prg_len - ctrl - 2)).
Proof. intros; unfold prog_ctrl_app.
       bdestruct_all. 
       replace (1 + ctrl - ctrl) with 1 by lia. 
       simpl. 
       assert (H' : (∣0⟩⟨0∣ ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ I 1 ⊗ σx) = cnot).
       { lma'. }
       assert (H'' : forall (n m : nat) (a b : Square n) (c d : Square m), 
                  a = b -> c = d -> a ⊗ c = b ⊗ d).
       { intros. rewrite H4, H5; easy. }
       replace (prg_len - ctrl - 2) with (prg_len - S ctrl - 1) by lia.
       apply H''; try easy.
       apply H''; try easy.
Qed.


Lemma adj_ctrlX_is_notc : forall (prg_len targ : nat),
  1 + targ < prg_len ->
  prog_ctrl_app prg_len σx (1 + targ) targ = 
  I (2^targ) ⊗ notc ⊗ I (2^(prg_len - targ - 2)).
Proof. intros; unfold prog_ctrl_app.
       bdestruct_all. 
       replace (1 + targ - targ) with 1 by lia. 
       simpl. 
       assert (H' : (I 2 ⊗ ∣0⟩⟨0∣ .+ σx ⊗ I 1 ⊗ ∣1⟩⟨1∣) = notc).
       { lma'. }
       assert (H'' : forall (n m : nat) (a b : Square n) (c d : Square m), 
                  a = b -> c = d -> a ⊗ c = b ⊗ d).
       { intros. rewrite H4, H5; easy. }
       replace (prg_len - targ - 2) with (prg_len - S targ - 1) by lia.
       apply H''; try easy.
       apply H''; try easy.
Qed.


Lemma adj_ctrlX_is_cnot1 : prog_ctrl_app 2 σx 0 1 = cnot.
Proof. rewrite adj_ctrlX_is_cnot; try lia. 
       rewrite Nat.sub_0_r, Nat.sub_diag, Nat.pow_0_r.
       rewrite kron_1_l, kron_1_r; auto with wf_db.
Qed.


Lemma adj_ctrlX_is_notc1 : prog_ctrl_app 2 σx 1 0 = notc.
Proof. rewrite adj_ctrlX_is_notc; try lia. 
       rewrite Nat.sub_0_r, Nat.sub_diag, Nat.pow_0_r.
       rewrite kron_1_l, kron_1_r; auto with wf_db.
Qed.



(* switched order of 2 by 2 kron products. *) 
(* Useful for showing that effect of cnot on a ⊗ b *) 
Definition switch_kron_order (A : Square 4) : Square 4 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => A 0 0
  | (0, 1) => A 0 2
  | (0, 2) => A 0 1
  | (0, 3) => A 0 3
  | (1, 0) => A 2 0
  | (1, 1) => A 2 2
  | (1, 2) => A 2 1
  | (1, 3) => A 2 3
  | (2, 0) => A 1 0
  | (2, 1) => A 1 2
  | (2, 2) => A 1 1
  | (2, 3) => A 1 3
  | (3, 0) => A 3 0
  | (3, 1) => A 3 2
  | (3, 2) => A 3 1
  | (3, 3) => A 3 3
  | _ => C0
  end.

Lemma WF_sko : forall A, WF_Matrix (switch_kron_order A).
Proof. unfold WF_Matrix; intros. 
       destruct H.
       - do 4 (destruct x; try lia); easy.   
       - do 4 (destruct y; try lia). 
         do 4 (destruct x; try easy).
Qed.

Hint Resolve WF_sko : wf_db.

Lemma sko_twice_id : forall (A : Square 4), 
    WF_Matrix A -> switch_kron_order (switch_kron_order A) = A.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order. 
       do 4 (destruct i0; 
             try (do 4 (destruct j; try lca); lia)).
       lia.
Qed.


Lemma Mmult_sko : forall (A B : Square 4), switch_kron_order (A × B) = 
                                      switch_kron_order A × switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mmult. 
       do 4 (destruct i0; 
             try (do 4 (destruct j; try lca); lia)).
Qed.


Lemma Mplus_sko : forall (A B : Square 4), switch_kron_order (A .+ B) = 
                                      switch_kron_order A .+ switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mplus. 
       do 4 (destruct i0; 
             try (do 4 (destruct j; try lca); lia)).
Qed.

Lemma kron_sko_verify : forall (a b : Square 2),
  WF_Matrix a -> WF_Matrix b ->
  switch_kron_order (a ⊗ b) = b ⊗ a.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, kron.
       do 4 (destruct i0; 
             try (do 4 (destruct j; try lca); lia)).
       lia. 
Qed.

Lemma notc_sko_cnot : switch_kron_order cnot = notc.
Proof. rewrite <- CX_is_NOTC, <- CX_is_CNOT.
       rewrite Mplus_sko, kron_sko_verify, kron_sko_verify; auto with wf_db.
Qed.

Lemma cnot_sko_notc : switch_kron_order notc = cnot.
Proof. rewrite <- CX_is_NOTC, <- CX_is_CNOT.
       rewrite Mplus_sko, kron_sko_verify, kron_sko_verify; auto with wf_db.
Qed.


Lemma notc_conv : forall (a a' b b' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  notc × (a ⊗ b) = (a' ⊗ b') × notc ->
  cnot × (b ⊗ a) = (b' ⊗ a') × cnot.
Proof. intros. 
       assert (H4: forall a a', a = a' -> switch_kron_order a = switch_kron_order a').
       { intros. rewrite H4; easy. }
       apply H4 in H3.
       do 2 rewrite Mmult_sko, kron_sko_verify in H3; auto.
       rewrite cnot_sko_notc in H3; easy. 
Qed.

Lemma cnot_conv : forall (a a' b b' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  cnot × (a ⊗ b) = (a' ⊗ b') × cnot ->
  notc × (b ⊗ a) = (b' ⊗ a') × notc.
Proof. intros. 
       assert (H4: forall a a', a = a' -> switch_kron_order a = switch_kron_order a').
       { intros. rewrite H4; easy. }
       apply H4 in H3.
       do 2 rewrite Mmult_sko, kron_sko_verify in H3; auto.
       rewrite notc_sko_cnot in H3; easy. 
Qed.


Lemma kron_breakdown1 : forall (a a' b b' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  a ⊗ b = a' ⊗ b' -> 
  (forall i j k l : nat, ((a i j) * (b k l) = (a' i j) * (b' k l))%C).
Proof. intros a a' b b' H H0 H1 H2 H3 i j k l.  
       bdestruct (i <? 2); bdestruct (j <? 2); bdestruct (k <? 2); bdestruct (l <? 2);
         try (rewrite H, H0; try (left; easy); try (right; easy); lca);
         try (rewrite H1, H2; try (left; easy); try (right; easy); lca).
       assert (H' : (a ⊗ b) (k + i*2) (l + j*2) = (a' ⊗ b') (k + i*2) (l + j*2)).
       rewrite H3; easy. 
       unfold kron in H'. 
       do 2 rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
Qed.


Lemma kron_breakdown2 : forall (a a' b b' c c' d d' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  WF_Matrix c -> WF_Matrix c' -> WF_Matrix d -> WF_Matrix d' ->
  a ⊗ b .+ c ⊗ d = a' ⊗ b' .+ c' ⊗ d' -> 
  (forall i j k l : nat, ((a i j) * (b k l) + (c i j) * (d k l) = 
                          (a' i j) * (b' k l) + (c' i j) * (d' k l))%C).
Proof. intros a a' b b' c c' d d' H H0 H1 H2 H3 H4 H5 H6 H7 i j k l.  
       bdestruct (i <? 2); bdestruct (j <? 2); bdestruct (k <? 2); bdestruct (l <? 2);
         try (rewrite H, H0, H3, H4; try (left; easy); try (right; easy); lca);
         try (rewrite H1, H2, H5, H6; try (left; easy); try (right; easy); lca).
       assert (H' : (a ⊗ b .+ c ⊗ d) (k + i*2) (l + j*2) = 
                    (a' ⊗ b' .+ c' ⊗ d') (k + i*2) (l + j*2)).
       rewrite H7; easy. 
       unfold kron, Mplus in H'. 
       do 2 rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
Qed.


Lemma kron_rearrange1 : forall {n} (a a' b b' : Square 2) (C C' : Square n),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  WF_Matrix C ->
  a ⊗ b = a' ⊗ b' -> C = C' ->
  a ⊗ C ⊗ b = a' ⊗ C' ⊗ b'.
Proof. intros; subst.
       prep_matrix_equality. 
       unfold kron.
       rewrite Cmult_comm, Cmult_assoc. 
       rewrite (Cmult_comm _ (b' _ _)), Cmult_assoc. 
       apply Cmult_simplify; try easy. 
       rewrite Cmult_comm, (Cmult_comm (b' _ _)).
       apply kron_breakdown1; auto. 
Qed.




Lemma kron_rearrange2 : forall {n} (a a' b b' c c' d d' : Square 2) (C : Square n),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' -> 
  WF_Matrix c -> WF_Matrix c' -> WF_Matrix d -> WF_Matrix d' ->
  WF_Matrix C -> 
  a ⊗ b .+ c ⊗ d = a' ⊗ b' .+ c' ⊗ d' ->
  a ⊗ C ⊗ b .+ c ⊗ C ⊗ d = a' ⊗ C ⊗ b' .+ c' ⊗ C ⊗ d'.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv, kron, Mplus; intros i j H9 H10. 
       rewrite Cmult_comm, (Cmult_comm _ (d _ _)), 
               (Cmult_comm _ (b' _ _)), (Cmult_comm _ (d' _ _)). 
       do 4 rewrite Cmult_assoc.
       do 2 rewrite <- Cmult_plus_distr_r.
       apply Cmult_simplify; try easy.
       rewrite (Cmult_comm (b _ _)), (Cmult_comm (b' _ _)), 
               (Cmult_comm (d _ _)), (Cmult_comm (d' _ _)).
       apply kron_breakdown2; easy.
Qed.
       
Lemma cnot_conv_inc : forall {n} (a a' b b' : Square 2) (C C' : Square (2^n)),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  WF_Matrix C -> 
  cnot × (a ⊗ b) = (a' ⊗ b') × cnot -> C = C' ->
  @Mmult (2 * 2^n * 2) (2 * 2^n * 2) (2 * 2^n * 2) 
         (∣0⟩⟨0∣ ⊗ Matrix.I (2 * 2 ^ n) .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ n) ⊗ σx) (a ⊗ C ⊗ b) =
  (a' ⊗ C' ⊗ b') × (∣0⟩⟨0∣ ⊗ Matrix.I (2 * 2 ^ n) .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ n) ⊗ σx).
Proof. intros; subst.
       do 2 replace (2 * (2 * 2^n)) with (2 * 2^n * 2) by lia.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
       replace (2 * 2 ^ n) with (2 ^ n * 2) by lia. 
       rewrite <- id_kron.
       rewrite <- kron_assoc; auto with wf_db.
       repeat rewrite kron_mixed_product.
       replace (2 ^ n * 2) with (2 * 2 ^ n) by lia. 
       repeat rewrite kron_mixed_product.
       rewrite Mmult_1_l, Mmult_1_r; auto.
       assert (H' : cnot = ∣0⟩⟨0∣ ⊗ Matrix.I 2 .+ ∣1⟩⟨1∣ ⊗ σx).
       { lma'. }
       rewrite H' in H4.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l in H4.
       repeat rewrite kron_mixed_product in H4.
       apply kron_rearrange2; auto with wf_db.
Qed.



Ltac solve_gate_type :=
  repeat match goal with
         | |- singGateType' ?U ?g /\ _ => split
         | |- ?g <> [] => easy
         | |- singGateType' ?U ?g => apply sgt_implies_sgt' 
         | |- singGateType ?U ?g => simpl; apply singleton_simplify2; lma'
         | |- _ => try easy
         end.


Lemma HTypes : H' ::' (Z' → X') ∩ (X' → Z').
Proof. simpl. unfold Z', X', prog_smpl_app. 
       solve_gate_type. 
Qed.
       
Lemma HTypes' : H' ::' (Z'' →' X'') ∩ (X'' →' Z'').
Proof. simpl.
       repeat (rewrite kron_1_r).  
       solve_gate_type. 
Qed.


Lemma STypes : (prog_smpl_app 1 S' 0) ::' (X' → Y') ∩ (Z' → Z').
Proof. simpl. unfold Z', X', prog_smpl_app. 
       solve_gate_type. 
       Admitted.

Lemma CNOTTypes : (prog_ctrl_app 2 σx 0 1) ::' (X' ⊗' I' → X' ⊗' X') ∩ (I' ⊗' X' → I' ⊗' X') ∩
                          (Z' ⊗' I' → Z' ⊗' I') ∩ (I' ⊗' Z' → Z' ⊗' Z').
Proof. rewrite adj_ctrlX_is_cnot1.
       simpl. unfold X', I', Z'. 
       solve_gate_type.
Qed.
      

Lemma CNOTTypes' : cnot ::' (X' ⊗' I' → X' ⊗' X') ∩ (I' ⊗' X' → I' ⊗' X') ∩
                          (Z' ⊗' I' → Z' ⊗' I') ∩ (I' ⊗' Z' → Z' ⊗' Z').
Proof. simpl. unfold X', I', Z'. 
       solve_gate_type.
Qed.

Lemma CZTypes' : CZ ::' (X' ⊗' I' → X' ⊗' Z') ∩ (I' ⊗' X' → Z' ⊗' X') ∩
                          (Z' ⊗' I' → Z' ⊗' I') ∩ (I' ⊗' Z' → I' ⊗' Z').
Proof. simpl. unfold X', I', Z'. 
       solve_gate_type.
Qed.



(* T only takes Z → Z *)
Lemma TTypes : T' ::' (Z' → Z').
Proof. simpl. unfold T', Z'. 
       solve_gate_type. 
Qed.

Hint Resolve HTypes HTypes' STypes TTypes CNOTTypes CNOTTypes' CZTypes' : base_types_db.
Hint Resolve cap_elim_l_gate cap_elim_r_gate : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.


Definition appH (len bit : nat) := prog_smpl_app len H' bit.
Definition appCNOT (len ctrl targ : nat) := prog_ctrl_app len σx ctrl targ.
Definition appCZ (len ctrl targ : nat) := appH len targ ; appCNOT len ctrl targ ; appH len targ.
 

Definition bell00 : Square 16 := (prog_smpl_app 4 H' 2); (prog_ctrl_app 4 σx 2 3).

Definition encode : Square 16 := (prog_ctrl_app 4 σz 0 2); (prog_ctrl_app 4 σx 1 2).

Definition decode : Square 16 := (prog_ctrl_app 4 σx 2 3); (prog_smpl_app 4 H' 2).

Definition superdense := bell00 ; encode; decode.

*)
