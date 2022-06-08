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



    
(**************************)
(* Defining Vector typing *)
(**************************)


Definition vec_is_plus1_eig {n} (v : Vector n) (a : Square n) :=
  WF_Matrix v /\ a × v = v.

Notation "v :' a" := (vec_is_plus1_eig v a) (at level 62) : heisenberg_scope. 



Ltac solveType := intros; split; simpl; auto with wf_db; try lma'; try solve_matrix.


Lemma all_hastype_I : forall (v : Vector 2), WF_Matrix v -> v :' (translate_quat p_1).
Proof. solveType. Qed.
  
Lemma pX_plus1_eig : ∣+⟩ :' (translate_quat p_i). Proof. solveType. Qed.
Lemma pY_plus1_eig : ∣R⟩ :' (translate_quat p_j). Proof. solveType. Qed.
Lemma pZ_plus1_eig : ∣0⟩ :' (translate_quat p_k). Proof. solveType. Qed.
Lemma nX_plus1_eig : ∣-⟩ :' (translate_quat n_i). Proof. solveType. Qed.
Lemma nY_plus1_eig : ∣L⟩ :' (translate_quat n_j). Proof. solveType. Qed.
Lemma nZ_plus1_eig : ∣1⟩ :' (translate_quat n_k). Proof. solveType. Qed.
                        
Lemma B_hastype_XX : ∣Φ+⟩ :' σx ⊗ σx. Proof. solveType. Qed.


#[export] Hint Resolve all_hastype_I pX_plus1_eig pY_plus1_eig pZ_plus1_eig nX_plus1_eig nY_plus1_eig nZ_plus1_eig B_hastype_XX : eig_db.

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
 


(**************************************************************)
(* Defining pairHasType, which is a helper function for later *)
(**************************************************************)


(* this is the only def in this file that Types.v uses *)                                 
Definition pairHasType {n : nat} (p : Vector n * C) (U : Square n) : Prop := 
  WF_Matrix (fst p) /\ Eigenpair U p.




Lemma vType_mult : forall {n} (v : Vector n) (A B : Square n), 
  v :' A -> 
  v :' B -> 
  v :' (A × B).     
Proof. intros.  
       destruct H; destruct H0; split; auto.
       rewrite Mmult_assoc, H2; easy.
Qed.



Lemma vType_scale : forall {n} (v : Vector n) (A : Square n) (c λ : C),
  c <> C0 -> WF_Matrix A ->
  (pairHasType (v, c * λ) A <-> pairHasType (v, λ) (/c .* A)).  
Proof. intros. 
       unfold pairHasType.
       split; intros [H1 H2]; split; simpl in *; auto.
       all : unfold Eigenpair in *; simpl in *.
       rewrite Mscale_mult_dist_l, H2, Mscale_assoc, Cmult_assoc, Cinv_l; try easy; lma'.
       rewrite <- Mscale_assoc, <- H2; distribute_scale; rewrite Cinv_r; try easy; lma'.  
Qed.



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
*)

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

