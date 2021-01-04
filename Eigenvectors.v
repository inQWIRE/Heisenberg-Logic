Require Import List.
Require Export Complex.
Require Export Matrix.
Require Export Quantum.



(* Some preliminary lemmas/additions to tactics that could be moved to other files *)


Local Open Scope nat_scope.

Fixpoint first_n (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => n :: first_n n'
  end.

Lemma first_n_contains : forall (n i : nat),
  i <= n <-> In i (first_n n).
Proof. split.
       - induction n as [| n'].
         * intros. bdestruct (i =? 0). 
           + rewrite H0. simpl. left. easy.
           + apply le_n_0_eq in H. rewrite H in H0. easy.
         * intros. simpl. bdestruct (i =? S n').
           + left. rewrite H0. easy. 
           + right. apply IHn'. 
             apply le_lt_eq_dec in H. destruct H.
             ** apply Nat.lt_succ_r. apply l.
             ** rewrite e in H0. easy.
       - induction n as [| n'].
         * intros [H | F]. 
           + rewrite H. easy.
           + simpl in F. easy.
         * intros. simpl in H. destruct H.
           + rewrite H. easy.
           + apply IHn' in H. 
             apply le_n_S in H. apply le_Sn_le.
             apply H.
Qed.


Lemma norm_real : forall {n} (v : Vector n), snd ((v† × v) 0 0) = 0%R. 
Proof. intros. unfold Mmult, adjoint.
       rewrite Csum_snd_0. easy.
       intros. rewrite Cmult_comm.
       rewrite Cmult_conj_real.
       reflexivity.
Qed.


Lemma sqrt_1_unique : forall x, √ x = 1%R -> x = 1%R.
Proof. intros. assert (H' := H). unfold sqrt in H. destruct (Rcase_abs x).
       - assert (H0: 1%R <> 0%R). { apply R1_neq_R0. }
         rewrite H in H0. easy.
       - rewrite <- (sqrt_def x). rewrite H'. lra. 
         apply Rge_le. easy.
Qed.


Definition Phase : Matrix 2 2 := phase_shift (PI / 2).

Definition Phase' : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Ci
          | _, _ => C0
          end.

Definition Tgate :=  phase_shift (PI / 4).


Lemma WF_Phase : WF_Matrix Phase. Proof. show_wf. Qed.
Lemma WF_Phase' : WF_Matrix Phase'. Proof. show_wf. Qed.
Lemma WF_Tgate: WF_Matrix Tgate. Proof. show_wf. Qed.
Lemma WF_notc : WF_Matrix notc. Proof. show_wf. Qed.

Lemma WF_ket : forall (x : nat), WF_Matrix ∣x⟩.
Proof. intros x. unfold ket. destruct (x =? 0). show_wf. show_wf. 
Qed. 

Lemma WF_bra : forall (x : nat), WF_Matrix (bra x).
Proof. intros x. unfold bra. destruct (x =? 0). show_wf. show_wf. 
Qed. 


Hint Resolve WF_Phase WF_Phase' WF_Tgate WF_notc WF_ket WF_bra : wf_db.

(* ran into problems with hadamard. Can probably make this more general. *)
Ltac Hhelper :=
   unfold Mmult;
   unfold Csum;
   unfold I;
   simpl;
   C_field_simplify;
   try lca;
   C_field.


Lemma PEqP' : Phase = Phase'.
Proof. lma'. autorewrite with Cexp_db. reflexivity.
Qed.


(* these allow us to bypass WF requirements in every definition, which get annoying *)
(* we could also just make an axiom saying that all Squares are WF... *)
Axiom Mmult_1_r': forall {n m} (A : Matrix n m),
  A × I n = A.

Axiom Mmult_1_l': forall {n m} (A : Matrix n m),
  I n × A = A.



Lemma inverse_is_valid : forall {n} (X X' : Square n) (u v : Vector n),
  X × X' = I n -> X × u = v -> X' × v = u.
Proof. intros. 
       rewrite <- H0.
       rewrite <- Mmult_assoc.
       apply Minv_flip in H.
       rewrite H.
       rewrite Mmult_1_l'.
       reflexivity.
Qed.



(*************************)
(* Defining determinants *)
(*************************)


Definition reduce {n} (A : Square (1 + n)) (row col : nat) : Square n :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).



Lemma leq_helper : forall (x r n : nat),
  r <= n -> x >= n -> x <? r = false.
Proof. intros. assert (H': r <= x).
       { apply (le_trans r n x). 
         apply H. apply H0. }
       apply Nat.le_ngt in H'. 
       bdestruct (x <? r). easy.
       easy.
Qed.

Lemma WF_reduce : forall {n} (A : Square (1 + n)) (row col : nat),
  WF_Matrix A -> row <= n -> col <= n -> WF_Matrix (reduce A row col).
Proof. unfold WF_Matrix. intros.
       unfold reduce. destruct H2 as [H2 | H2].
       - rewrite (leq_helper x row n). 
         assert (Hx : 1 + x >= 1 + n). 
         { apply Nat.succ_le_mono in H2. 
           apply H2. }
         bdestruct (y <? col). 
         * apply H. left. apply Hx.
         * apply H. left. apply Hx.
         * apply H0.
         * apply H2.
       - rewrite (leq_helper y col n). 
         assert (Hy : 1 + y >= 1 + n). 
         { apply Nat.succ_le_mono in H2. 
           apply H2. }
         bdestruct (x <? row). 
         * apply H. right. apply Hy.
         * apply H. right. apply Hy.
         * apply H1.
         * apply H2.
Qed.
         

(*
Fixpoint Determinant {n : nat} (A : Square n) : C :=
  match n with 
  | 0 => C1
  | S 0 => A 0 0
  | S n' => (Csum (fun i => Cmult (A 0 i) (@Determinant (n - 1) (reduce A 0 i))) n)
  end.
*)


(************************************************************************)
(* Defining a set of vectors, linear independence, other prelims etc... *)
(************************************************************************)

(* a set of m vectors of dimension n *)
Definition VecSet n m := (Matrix n m).

Definition zero_vec (n : nat) : Vector n := @Zero n 1.

Definition vecs_to_vecSet {n} (vs : list (Vector n)) : VecSet n (length vs) := 
  fun x y => (nth y vs (zero_vec n)) x 0%nat.

Definition get_vec {n m} (i : nat) (S : VecSet n m) : Vector n :=
  fun x y => (if (y =? 0) then S x i else C0).   


Lemma get_vec_convsersion : forall {n m} (x y : nat) (S : VecSet n m),
  (get_vec y S) x 0 = S x y.
Proof. intros. unfold get_vec.
       easy.
Qed.


Definition linearly_independent {n m} (S : VecSet n m) : Prop :=
  forall (a : Vector n), @Mmult n m 1 S a = Zero -> a = Zero.


Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then C1 else C0). 

Lemma I_is_eis : forall {n} (i : nat),
  get_vec i (I n) = e_i i. 
Proof. intros. unfold get_vec, e_i.
       prep_matrix_equality. 
       bdestruct (x =? i).
       - bdestruct (y =? 0).
         rewrite H. unfold I. simpl. 
         assert (H1 : (i =? i) && (i <? n) = (i <? n) && true).
         { bdestruct (i =? i). apply andb_comm. easy. }
         rewrite H1. reflexivity.
         simpl; rewrite andb_false_r; reflexivity.
       - simpl. destruct (y =? 0). unfold I.
         bdestruct (x =? i). easy.
         reflexivity. reflexivity.
Qed.

Lemma invertible_implies_linind : forall {n} (X : Square n),
  (exists X', X × X' = I n) -> linearly_independent X.
Proof. intros. destruct H.
       unfold linearly_independent. intros.
       apply Minv_flip in H. 
       rewrite <- (Mmult_1_l' a); 
       rewrite <- H.
       rewrite Mmult_assoc, H0.
       rewrite Mmult_0_r.
       reflexivity.
Qed.


Lemma matrix_by_basis : forall {n} (X : Square n),
  WF_Matrix X ->  
  (forall i : nat, get_vec i X = X × e_i i).
Proof. intros. unfold get_vec, e_i, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0). 
       - bdestruct (i <? n).
         + rewrite (Csum_unique (X x i) _ n). 
           reflexivity. 
           exists i. split.
           apply H1. split. 
           apply Nat.ltb_lt in H1. rewrite H1. 
           bdestruct (i =? i). simpl.
           rewrite Cmult_1_r. reflexivity.
           easy.
           intros.
           bdestruct (x' =? i).
           rewrite H3 in H2; easy.
           simpl.
           rewrite Cmult_0_r. reflexivity.
         + rewrite Csum_0.
           unfold WF_Matrix in H; rewrite H.
           reflexivity. right. apply H1. 
           intros. bdestruct (x0 =? i).
           rewrite H2. bdestruct (i <? n).
           nia. simpl. rewrite Cmult_0_r.
           reflexivity.
           simpl. rewrite Cmult_0_r.
           reflexivity.
       - rewrite Csum_0. reflexivity.
         intros. rewrite andb_false_r. 
         rewrite Cmult_0_r. reflexivity.
Qed.         


Definition orthogonal {n m} (S : VecSet n m) : Prop := 
  forall i j, i <> j -> inner_product (get_vec i S) (get_vec j S) = C0.


Definition orthonormal {n m} (S : VecSet n m) : Prop :=
  orthogonal S /\ (forall (i : nat), i < n -> norm (get_vec i S) = 1%R).


Lemma inner_product_is_mult : forall {n} (i j : nat) (S : Square n),
  inner_product (get_vec i S) (get_vec j S) = ((S†) × S) i j.
Proof. intros. unfold inner_product, get_vec, Mmult, adjoint.
       apply Csum_eq.
       apply functional_extensionality; intros. simpl.
       reflexivity.
Qed.


(************************************************)
(* Lemmas relating to forming orthonormal bases *)
(************************************************)

Fixpoint nonzero_entry_imp {n} (v : Vector n) (i : nat) : nat :=
  match (v i 0) <> C0 with
  | True => i
  end.


Definition form_basis {n} (v : Vector n) : VecSet n n :=
  fun x y => if (y =? 0) 
             then (v x 0)
             else if (y <? nonzero_entry_imp v 0)
                  then (@e_i n (y - 1)) x 0
                  else (@e_i n y) x 0.

Lemma form_basis_ver : forall {n} (v : Vector n),
  v <> Zero -> linearly_independent (form_basis v).
Proof. Admitted.

Definition gram_schmidt {n} (S : VecSet n n) : VecSet n n := S.

Definition v_to_onb {n} (v : Vector n) : VecSet n n := gram_schmidt (form_basis v).

Lemma WF_onb : forall {n} (v : Vector n),
  WF_Matrix v -> @WF_Matrix n n (v_to_onb v).
Proof. Admitted.


Lemma gram_schmidt_ver : forall {n} (v : Vector n),
  v <> Zero -> get_vec 0 (v_to_onb v) = normalize v /\ orthonormal (v_to_onb v).
Proof. Admitted. 

(********************************************************************)
(* Defining unitary matrices and proving some basic lemmas/examples *)
(********************************************************************)


Definition unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 



Lemma X_unitary : unitary σx. Proof. lma'. Qed.
Lemma Y_unitary : unitary σy. Proof. lma'. Qed.
Lemma Z_unitary : unitary σz. Proof. lma'. Qed.
Lemma P_unitary : unitary Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma cnot_unitary : unitary cnot. Proof. lma'. Qed.
Lemma notc_unitary : unitary notc. Proof. lma'. Qed.

Lemma H_unitary : unitary hadamard.
Proof. assert (H : hadamard † = hadamard). { lma'. }
       unfold unitary; rewrite H.
       lma'; Hhelper.
Qed.

Lemma unit_I : forall (n : nat), unitary (I n).
Proof. intros. unfold unitary. rewrite Mmult_1_l'.
       apply id_adjoint_eq. 
Qed.

Lemma unit_mult : forall {n} (A B : Square n),
  unitary A -> unitary B -> unitary (A × B).
Proof. intros. unfold unitary in *.
       rewrite Mmult_adjoint.
       rewrite Mmult_assoc.
       rewrite <- (Mmult_assoc B _ _).
       rewrite H0. rewrite Mmult_1_l'.
       rewrite H. reflexivity.
Qed.


Lemma unit_adjoint : forall {n} (A : Square n),
  unitary A -> unitary (A†).
Proof. intros.
       unfold unitary in *.
       rewrite adjoint_involutive.
       apply Minv_flip.
       assumption.
Qed.


Lemma unit_is_orthonormal : forall {n} (U : Square n),
  WF_Matrix U -> (unitary U <-> orthonormal U).
Proof. intros n U H0'. split. 
       - split.
         * unfold orthogonal. intros.
           rewrite inner_product_is_mult.
           unfold unitary in H. apply Minv_flip in H.
           rewrite H. 
           unfold I. bdestruct (i =? j).
           + rewrite H1 in H0. easy.
           + reflexivity.
         * intros. unfold norm.
           assert (H1 : ((get_vec i U) † × get_vec i U) 0%nat 0%nat = 
                        inner_product (get_vec i U) (get_vec i U)).
           { unfold inner_product. reflexivity. }
           rewrite H1. rewrite inner_product_is_mult.
           unfold unitary in H. apply Minv_flip in H.
           rewrite H. unfold I.
           apply Nat.ltb_lt in H0. rewrite H0.
           assert (H' : i =? i = true). { apply Nat.eqb_eq. easy. }
           rewrite H'. simpl. apply sqrt_1. 
       - intros [H1 H2]. unfold unitary.
         apply Minv_flip.
         prep_matrix_equality.
         rewrite <- inner_product_is_mult.
         unfold orthogonal in H1. unfold I.
         bdestruct (x =? y).
         * bdestruct (x <? n).
           + simpl. apply H2 in H0.
             unfold norm in H0; unfold inner_product.
             apply sqrt_1_unique in H0.
             unfold RtoC.
             apply c_proj_eq.
             rewrite <- H, H0. easy.
             rewrite H.
             rewrite norm_real. easy.
           + unfold get_vec, inner_product, Mmult.
             simpl. apply Csum_0.
             unfold adjoint. intros.
             unfold WF_Matrix in H0'.
             rewrite H0'. simpl.
             rewrite Cconj_0.
             rewrite Cmult_0_l.
             reflexivity. right. apply H0.
         * simpl. rewrite H1.
           reflexivity. apply H.
Qed.


Lemma onb_unit : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> @unitary n (v_to_onb v).
Proof. intros.
       apply unit_is_orthonormal.
       apply WF_onb. apply H.
       apply gram_schmidt_ver in H0.
       easy.
Qed.          


(***********************************************************************************)
(* We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition diagonal {n : nat} (A : Square n) : Prop := 
  forall i j, i <> j -> A i j = C0.


Lemma diag_Zero : forall n : nat, diagonal (@Zero n n).
Proof. intros n. unfold diagonal. reflexivity. Qed.

Lemma diag_I : forall n : nat, diagonal (I n). 
Proof. 
  unfold diagonal, I; intros.
  bdestruct (i =? j). 
  - easy. 
  - easy.
Qed.

Lemma diag_I1 : diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonal A -> diagonal (r .* A).
Proof.
  unfold diagonal, scale.
  intros n r A H i j H0. 
  apply H in H0. 
  rewrite H0.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A .+ B).
Proof.
  unfold diagonal, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0. 
  rewrite Cplus_0_l.
  reflexivity.
  apply H1. apply H1. 
Qed.

Lemma diag_mult : forall {n : nat} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A × B).
Proof.
  unfold diagonal, Mmult.
  intros n A B H H0 i j D.
  apply Csum_0.
  intros x.
  bdestruct (x =? i).
  + rewrite <- H1 in D. 
    rewrite H0, Cmult_0_r.
    reflexivity.
    apply D.
  + rewrite H, Cmult_0_l.    
    reflexivity. auto.
Qed.

(* short lemma to prove diag_kron *)
Lemma div_mod_eq : forall (a b m : nat),
  m <> 0 -> (a / m = b / m) -> (a mod m = b mod m) -> a = b.
Proof. intros a b m H0 Hdiv Hmod.
       rewrite (Nat.mod_eq a m), (Nat.mod_eq b m) in Hmod.
       rewrite Hdiv in Hmod.
       assert (H : m * (b / m) + (a - m * (b / m)) = m * (b / m) + (b - m * (b / m))).
       { rewrite Hmod. reflexivity. }
       rewrite <- (le_plus_minus  (m * (b / m)) a) in H.
       rewrite <- (le_plus_minus  (m * (b / m)) b) in H.
       apply H.
       apply Nat.mul_div_le; apply H0.
       rewrite <- Hdiv; apply Nat.mul_div_le; apply H0.
       apply H0. apply H0.
Qed.


Lemma diag_kron : forall {m n : nat} (A : Square n) (B : Square m), 
                  m <> 0 -> 
                  diagonal A -> diagonal B -> @diagonal (m * n) (A ⊗ B).
Proof.
  unfold diagonal, kron.
  intros m n A B No H H0 i j H1.
  bdestruct (i / m =? j / m).
  - bdestruct (i mod m =? j mod m).
    + apply (div_mod_eq i j m) in No.
      rewrite No in H1. easy.
      apply H2. apply H3.
    + rewrite H0. rewrite Cmult_0_r. reflexivity.
      apply H3.
  - rewrite H. rewrite Cmult_0_l. reflexivity.
    apply H2.
Qed.


Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     diagonal A -> diagonal A⊤. 
Proof. unfold diagonal, transpose. intros n A H i j H0. 
       apply H. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      diagonal A -> diagonal A†. 
Proof. unfold diagonal, adjoint, Cconj. intros n A H i j H0.
       rewrite H. lca. auto.
Qed.


Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   m <> 0 -> diagonal A ->  diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply (@diag_kron m (m^n) _ A). 
    apply H. apply IHn. apply H0.
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        n <> 0 -> (forall A, In A l -> diagonal A) ->
                         diagonal (⨂ l). 
Proof.                         
  intros n l nNeq0 H.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply Nat.pow_nonzero; apply nNeq0.
    apply H. simpl. auto. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 


Lemma diag_Mmult_n : forall n {m} (A : Square m),
   diagonal A -> diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(* defining what it means to be diagonalizable *)
Definition diagonalizable {n : nat} (A : Square n) : Prop :=
  exists (X X' B: Square n), 
    diagonal B /\ X × X' = I n /\ B = X × A × X'.

Lemma diag_imps_diagble : forall {n} (A : Square n),
  diagonal A -> diagonalizable A.
Proof. intros. unfold diagonalizable.
       exists (I n), (I n), A. 
       split.
       apply H.  
       do 2 (rewrite Mmult_1_l'). 
       rewrite Mmult_1_r'.
       auto.
Qed.


Lemma diagble_Zero : forall n : nat, diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.


Lemma diagble_I : forall n : nat, diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : diagonal (I 1). Proof. apply diag_I. Qed.
  


Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonalizable A -> diagonalizable (r .* A).
Proof.
  unfold diagonalizable.
  intros. do 3 (destruct H).
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. split.
  apply H2.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H3.
  reflexivity. 
Qed.




(**************************************************)
(* Defining eignestates to be used in type system *)
(**************************************************)


Definition Eigenpair {n : nat} (U : Square n) (p : Vector n * C) : Prop :=
  U × (fst p) = (snd p) .* (fst p).

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   Eigenpair (I n) (v, C1).
Proof. intros n v. unfold Eigenpair. 
       simpl. rewrite Mmult_1_l'. lma. 
Qed.


Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> diagonal U -> Eigenpair U (e_i i, U i i).
Proof. unfold diagonal, Eigenpair, e_i. intros.
       unfold Mmult, scale.
       prep_matrix_equality.
       eapply Csum_unique. exists i. 
       split. apply H.
       split.
       - simpl. bdestruct (x =? i).
         * rewrite H1. bdestruct (i =? i). 
           reflexivity. easy. 
         * simpl.  
           rewrite H0.
           rewrite Cmult_0_l, Cmult_0_r. 
           reflexivity. apply H1.
       - intros. simpl. bdestruct (x' =? i).
         * rewrite H2 in H1. easy.
         * simpl. rewrite Cmult_0_r.
           reflexivity.
Qed.


Lemma eigen_scale : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  Eigenpair A (v, c1) -> Eigenpair (c2 .* A) (v, Cmult c1 c2).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite Mscale_mult_dist_l.
       rewrite H.
       rewrite Mscale_assoc.
       rewrite Cmult_comm.
       reflexivity.
Qed.


Lemma eigen_scale_div : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  c2 <> C0 -> Eigenpair (c2 .* A) (v, Cmult c2 c1) -> Eigenpair A (v, c1).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite <- Mscale_assoc in H0.
       rewrite Mscale_mult_dist_l in H0.
       apply Mscale_div in H0;
       assumption.
Qed.



Lemma lin_ind_has_eigen : forall {n} (X : Square n),
  (exists X', X × X' = I n) -> exists p, Eigenpair X p /\ fst p <> Zero /\ WF_Matrix (fst p).
Proof. Admitted. 



Lemma ind_step1 : forall {n} (A : Square (n + 1)),
  WF_Matrix A -> unitary A -> 
  exists X, unitary X /\
  (forall x, x <> 0 -> (X†×A×X) x 0 = C0).
Proof. intros. 
       assert (H' : exists p, Eigenpair A p /\ fst p <> Zero /\ WF_Matrix (fst p)).  
       { apply lin_ind_has_eigen. exists A†. apply H0. }
       destruct H'; destruct H1 as [H1 H2]; destruct H2 as [H2 H3]; destruct x.
       simpl in *.
       exists (v_to_onb m). split. 
       - apply onb_unit. 
         apply H3. apply H2.
       - intros x H4. 
         rewrite <- (get_vec_convsersion x 0 _).
         rewrite matrix_by_basis.
         rewrite Mmult_assoc.
         rewrite <- matrix_by_basis.
         assert (H' : get_vec 0 (v_to_onb m) = normalize m /\ orthonormal (v_to_onb m)).
         { apply gram_schmidt_ver. apply H2. }
         destruct H' as [H5 H6].
         rewrite H5.
         unfold normalize.
         rewrite Mmult_assoc.
         rewrite Mscale_mult_dist_r. 
         unfold Eigenpair in H1; simpl in H1.
         rewrite H1. rewrite Mscale_assoc.
         rewrite Cmult_comm.
         rewrite <- Mscale_assoc.
         rewrite Mscale_mult_dist_r. 
         assert (H' : (v_to_onb m) † × (/ norm m .* m) = @e_i (n+1) 0).
         { apply (inverse_is_valid (v_to_onb m) _ (e_i 0) _). 
           apply unit_is_orthonormal in H6; 
           unfold unitary in H6. apply H6.
           apply WF_onb. apply H3.
           rewrite <- matrix_by_basis.
           rewrite H5. reflexivity. 
           apply WF_onb. apply H3. }
         rewrite H'.
         unfold scale, e_i.
         bdestruct (x =? 0).
         + rewrite H7 in H4. easy.
         + simpl. rewrite Cmult_0_r.
           reflexivity.
         + apply WF_onb. apply H3.
         + apply WF_mult. apply WF_mult.
           apply WF_adjoint. apply WF_onb. apply H3.
           apply H. apply WF_onb. apply H3.
Qed.           


       
Lemma ind_step2 : forall {n} (A : Square (n + 1)),
  WF_Matrix A -> unitary A -> 
  exists X, unitary X /\ @unitary n (reduce (X†×A×X) 0 0) /\ 
  (forall x y, (x = 0 \/ y = 0) /\ x <> y -> (X†×A×X) x y = C0).
Admitted. 


(* Now, we build up the main important theorem *)
Theorem unit_implies_diagble : forall {n} (A : Square n),
  WF_Matrix A -> unitary A -> diagonalizable A.
Proof. induction n as [| n']. 
       - intros. assert (H' : A = Zero).
         { unfold Zero; unfold WF_Matrix in H.
           prep_matrix_equality.
           rewrite H. easy.
           left. apply le_0_n. } 
         rewrite H'. 
         apply diagble_Zero.
       - intros. unfold unitary in H0.
         assert (H' : exists p, Eigenpair A p /\ fst p <> Zero).  
Admitted. 






(* we want to prove *)

Theorem eigs_def_unit : forall (n : nat) (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> 
  (forall v, Eigenpair U1 v <-> Eigenpair U2 v) ->
  exists c, c .* U1 = U2.
Proof. intros. Admitted.


Local Close Scope nat_scope.

(*******************************)
(* Some actual examples/lemmas *)
(*******************************)



Definition qubitP : Vector 2 := / (√ 2) .* (∣0⟩ .+ ∣1⟩).
Definition qubitM : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-1) .* ∣1⟩)).
Definition EPRpair : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ ∣1,1⟩).

Lemma EPRpair_creation : cnot × (hadamard ⊗ I 2) × ∣0,0⟩ = EPRpair.
Proof. unfold EPRpair. lma'.
Qed.

                                                                 
Notation "∣+⟩" := qubitP.
Notation "∣-⟩" := qubitM.
Notation "∣Φ+⟩" := EPRpair.

Lemma WF_qubitP : WF_Matrix ∣+⟩. Proof. show_wf. Qed.
Lemma WF_qubitM : WF_Matrix ∣-⟩. Proof. show_wf. Qed.
Lemma WF_EPRpair : WF_Matrix ∣Φ+⟩. Proof. unfold EPRpair. auto with wf_db.  Qed.

Hint Resolve WF_qubitP WF_qubitM WF_EPRpair : wf_db. 

Lemma EigenXp : Eigenpair σx (∣+⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenXm : Eigenpair σx (∣-⟩, -C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenZ0 : Eigenpair σz (∣0⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenZ1 : Eigenpair σz (∣1⟩, -C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenXXB : Eigenpair (σx ⊗ σx) (∣Φ+⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.


Hint Resolve EigenXp EigenXm EigenZ0 EigenZ1 EigenXXB all_v_eigen_I : eig_db.


(***********************************************************)
(* Important lemmas about eigenvectors of unitary matrices *)
(***********************************************************)

Fixpoint list_eq {X : Type} (l1 l2 : list X) : Prop :=
  match l1 with
  | [] => l2 = []
  | h1 :: l1' => 
      match l2 with
      | [] => False
      | h2 :: l2' => h1 = h2 /\ list_eq l1' l2'
      end
  end.

Lemma list_eq_same : forall {X} (ls : list X),
  list_eq ls ls. 
Proof. induction ls as [| h].
       * easy.
       * easy.
Qed.

Lemma list_eq_implies_eq : forall {X} (l1 l2 : list X),
  list_eq l1 l2 -> l1 = l2.
Proof. induction l1 as [| h1].
       - easy.
       - intros. destruct l2 as [| h2].
         * easy.
         * simpl in H; destruct H as [H1 H2].
           apply IHl1 in H2. 
           rewrite H1, H2; reflexivity.
Qed.

Lemma list_eq_is_eq : forall {X} (l1 l2 : list X),
  l1 = l2 <-> list_eq l1 l2.  
Proof. intros. split. 
       - intros H; rewrite H; apply list_eq_same.
       - apply list_eq_implies_eq.
Qed.


Definition det2 (U : Square 2) : C := 
  ((U 0%nat 0%nat) * (U 1%nat 1%nat)) - 
  ((U 0%nat 1%nat) * (U 1%nat 0%nat)).

(* must figure out a good way to do this... *) 
Definition sqrtC (c : C) : C :=
  sqrt (fst c).


Definition quad_solver (a b c : C) : list C :=
  [(-b + sqrtC (b^2 - 4%C * a * c)) / (2*a) ; 
   (-b - sqrtC (b^2 - 4%C * a * c)) / (2*a)].


Definition get_eig_vals (U : Square 2) : list C :=
  quad_solver 1 (- (U 0%nat 0%nat + U 1%nat 1%nat)) (det2 U).

Lemma helper : sqrtC 4 = 2.
Proof. unfold sqrtC. simpl. apply c_proj_eq. simpl. 
       assert (H : 2%R ^2 = 4%R). { simpl. lca. } 
       unfold RtoC in H. apply sqrt_lem_1. lra. lra. lra. easy. 
Qed.

Lemma evs_σx : get_eig_vals σx = [C1 ; - C1].
Proof. unfold get_eig_vals. 
       unfold det2. 
       unfold quad_solver.
       apply list_eq_is_eq.
       simpl. Csimpl. 
       assert (H: (- 0 * - 0 - 4 * (0 - 1)) = 4).
       { lca. }
       rewrite H; rewrite helper. 
       split.
       - lca. 
       - split. lca. easy. 
Qed.


Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall p, Eigenpair U1 p -> Eigenpair U2 p. 


(* this is the main lemma we will need to assume *)
Lemma eq_eigs_implies_eq : forall {n} (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> eq_eigs U1 U2 -> U1 = U2.
Proof. Admitted.


Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> (U1 = U2 <-> eq_eigs U1 U2).
Proof. intros. split.
       - intros H'; rewrite H'; easy.
       - apply eq_eigs_implies_eq.
         apply H. apply H0.
Qed.


