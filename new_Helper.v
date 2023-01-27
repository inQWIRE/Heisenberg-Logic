Require Import Psatz.  
Require Import String. 
Require Import Program.
Require Import List.

 
Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.


Local Open Scope nat_scope.

(* Some helpers *)


(* this is trivial but helps shorten proofs and Ltacs *)

(* Heisenberg.v line 18 *)
Lemma kill_true : forall P : Prop,
  P /\ True <-> P.
Proof. split. intros [H _]. easy.
       intros. split. easy. easy.
Qed.

(* Heisenberg.v line 24 *)
Lemma kill_false : forall P : Prop,
  P \/ False <-> P.
Proof. split. intros [H| ].  easy. easy.
       intros. left. easy.
Qed.

(* Heisenberg.v line 30 *)
Lemma in_simplify : forall {X} (x x1 : X),
  In x1 [x] -> x1 = x.
Proof. intros. simpl in H.
       destruct H. easy. easy.  
Qed.

(* Heisenberg.v line 537 *)
Lemma cons_conc : forall (X : Type) (x : X) (ls : list X),
    x :: ls = [x] ++ ls.
Proof. reflexivity. Qed.


(* Heisenberg.v line 1588 *)
Ltac pauli_matrix_computation :=
  repeat
    (try apply mat_equiv_eq;
     match goal with
     | |- WF_Unitary ?A => unfold WF_Unitary
    | |- WF_Matrix ?A /\ _ => split
    | |- WF_Matrix ?A => auto 10 with wf_db;
                                        try (unfold WF_Matrix;
                                        (let x := fresh "x" in
                                         let y := fresh "y" in
                                         let H := fresh "H" in
                                         intros x y [H| H];
                                         apply le_plus_minus in H;
                                         rewrite H; compute; destruct_m_eq))
    | |- (?A ≡ ?B)%M => by_cell
    | |- _ => autounfold with U_db;
                  simpl;
                  autorewrite with Cexp_db C_db;
                  try (eapply c_proj_eq);
                  simpl;
                  repeat (autorewrite with R_db; field_simplify_eq; simpl);
                  try easy
    end).


(* defining program application *)
(* Heisenberg.v line 2355 *)
Definition prog_simpl_app (prg_len : nat) (U : Square 2) (bit : nat) : Square (2^prg_len) :=
  match bit <? prg_len with
  | true => I (2^bit) ⊗ U ⊗ I (2^(prg_len - bit - 1))
  | false => I (2^prg_len)
  end.


(* Heisenberg.v line 2363 *)
Lemma unit_prog_simpl_app : forall (prg_len : nat) (U : Square 2) (bit : nat),
  WF_Unitary U -> WF_Unitary (prog_simpl_app prg_len U bit). 
Proof. intros.  
       unfold prog_simpl_app.
       destruct (bit <? prg_len) eqn:E; auto with unit_db.
       rewrite (easy_pow3 _ bit); try (apply Nat.ltb_lt; easy).
       auto with unit_db.
Qed.


(* Heisenberg.v line 2374 *)
Definition prog_ctrl_app (prg_len : nat) (U : Square 2) (ctrl targ : nat) : Square (2^prg_len) :=
  match ((ctrl <? prg_len) && (targ <? prg_len) && (negb (ctrl =? targ))) with
  | false => I (2^prg_len)
  | true =>
    match (ctrl <? targ) with
    | true => I (2^ctrl) ⊗
               (∣0⟩⟨0∣ ⊗ I (2^(targ - ctrl)) .+ 
                ∣1⟩⟨1∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ U) ⊗ I (2^(prg_len - targ - 1))
    | false => I (2^targ) ⊗
               (I (2^(ctrl - targ)) ⊗ ∣0⟩⟨0∣ .+ 
                U ⊗ I (2^(ctrl - targ - 1)) ⊗ ∣1⟩⟨1∣) ⊗ I (2^(prg_len - ctrl - 1))
    end
  end.

(* Heisenberg.v line 2390 *)
Lemma unit_proj : forall (n : nat) (U : Square 2),
  n <> 0%nat -> WF_Unitary U -> WF_Unitary (∣0⟩⟨0∣ ⊗ I (2^n) .+ ∣1⟩⟨1∣ ⊗ I (2^(n - 1)) ⊗ U).
Proof. intros.
       destruct H0 as [Huwf H0].
       split; auto with wf_db.
       rewrite Mplus_adjoint.
       rewrite kron_adjoint.
       assert (H1 : ∣0⟩⟨0∣  † = ∣0⟩⟨0∣). 
       { lma'. }
       assert (H1' : ∣1⟩⟨1∣  † = ∣1⟩⟨1∣). 
       { lma'. }
       rewrite H1.
       rewrite id_adjoint_eq.
       assert (H' : (n - 0)%nat = n). { nia. }
       assert (H2 : (2 * 2^(n - 1) = 2^n)%nat).
       { rewrite (easy_pow3 n 0%nat); try nia.
         rewrite H'. simpl. nia. }
       assert (H2' : (2^(n - 1)*2 = 2^n)%nat). { rewrite mult_comm. apply H2. }
       assert (H3 : ( ∣1⟩⟨1∣ ⊗ I (2 ^ (n - 1)) ⊗ U ) † = ∣1⟩⟨1∣ ⊗ I (2 ^ (n - 1)) ⊗ U † ).
       { rewrite H2.
         rewrite kron_adjoint.
         rewrite <- H2.
         rewrite kron_adjoint.
         rewrite id_adjoint_eq.
         rewrite H1'.
         reflexivity. }       
       rewrite easy_pow6; try easy. 
       rewrite H3. 
       rewrite Mmult_plus_distr_l.
       do 2 (rewrite Mmult_plus_distr_r). 
       rewrite kron_mixed_product.      
       rewrite <- easy_pow6; try easy.
       do 2 (rewrite kron_mixed_product).       
       assert (H4 : ∣0⟩⟨0∣ × ∣0⟩⟨0∣ = ∣0⟩⟨0∣). { lma'. }
       rewrite H4. rewrite Mmult_1_l; try auto with wf_db.
       assert (H4' : ∣1⟩⟨1∣ × ∣1⟩⟨1∣ = ∣1⟩⟨1∣). { lma'. }
       rewrite H4'. rewrite Mmult_1_l; try auto with wf_db.
       rewrite kron_assoc; auto with wf_db. 
       rewrite H2'.
       rewrite kron_mixed_product; auto with wf_db.
       rewrite kron_assoc; auto with wf_db. 
       rewrite H2'. rewrite kron_mixed_product; auto with wf_db.
       assert (H5 : ∣1⟩⟨1∣ × ∣0⟩⟨0∣ = Zero). { lma'. }
       assert (H5' : ∣0⟩⟨0∣ × ∣1⟩⟨1∣ = Zero). { lma'. }
       rewrite H5, H5', kron_0_l, kron_0_l, H0, Mplus_0_r, Mplus_0_l.  
       rewrite kron_assoc, id_kron; auto with wf_db.
       replace ((2^ (n - 1) * 2)%nat) with ((2^n)%nat) by lia. 
       rewrite <- kron_plus_distr_r.
       assert (H6 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2). { lma'. }
       rewrite H6.
       rewrite id_kron.
       reflexivity.
Qed.

(* Heisenberg.v line 2445 *)
Lemma unit_proj2 : forall (n : nat) (U : Square 2),
  n <> 0%nat -> WF_Unitary U -> 
  WF_Unitary (I (2 ^ n) ⊗ ∣0⟩⟨0∣ .+ U ⊗ I (2 ^ (n - 1)) ⊗ ∣1⟩⟨1∣).
Proof. intros. 
       destruct H0 as [Huwf H0]. 
       split; auto with wf_db.
       rewrite Mplus_adjoint.
       rewrite kron_adjoint.
       assert (H1 : ∣0⟩⟨0∣  † = ∣0⟩⟨0∣). 
       { lma'. }
       assert (H1' : ∣1⟩⟨1∣  † = ∣1⟩⟨1∣). 
       { lma'. }
       rewrite H1.
       rewrite id_adjoint_eq.
       assert (H' : (n - 0)%nat = n). { nia. }
       assert (H2 : (2 * 2^(n - 1) = 2^n)%nat).
       { rewrite (easy_pow3 n 0); try nia.
         rewrite H'. simpl. nia. }
       assert (H2' : (2^(n - 1)*2 = 2^n)%nat). { rewrite mult_comm. apply H2. }
       assert (H3 :  (U ⊗ I (2 ^ (n - 1)) ⊗ ∣1⟩⟨1∣) † = U † ⊗ I (2 ^ (n - 1)) ⊗ ∣1⟩⟨1∣).
       { rewrite H2.
         rewrite kron_adjoint.
         rewrite <- H2.
         rewrite kron_adjoint.
         rewrite id_adjoint_eq.
         rewrite H1'.
         reflexivity. }
       rewrite easy_pow6'; try easy. 
       rewrite H3. 
       rewrite Mmult_plus_distr_l.
       do 2 (rewrite Mmult_plus_distr_r). 
       rewrite kron_mixed_product.      
       rewrite <- easy_pow6'; try easy. 
       do 2 (rewrite kron_mixed_product).       
       assert (H4 : ∣0⟩⟨0∣ × ∣0⟩⟨0∣ = ∣0⟩⟨0∣). { lma'. }
       rewrite H4. rewrite Mmult_1_l; try auto with wf_db.
       assert (H4' : ∣1⟩⟨1∣ × ∣1⟩⟨1∣ = ∣1⟩⟨1∣). { lma'. }
       rewrite H4'. rewrite Mmult_1_l; try auto with wf_db.
       rewrite (kron_mixed_product' (2*2^(n-1)) (2*2^(n-1)) _ _ 2 2 _ _ 
                                    (2^n*2) (2^n*2) (2^n*2) _ _ _ _); try easy;
                                    try (rewrite H2; easy).
       rewrite (kron_mixed_product' (2^n) (2^n) (2*2^(n-1)) (2*2^(n-1)) 2 2 _ _ 
                                    (2^n*2) (2^n*2) (2^n*2) _ _ _ _); try easy;
                                    try (rewrite H2; easy).
       assert (H5 : ∣1⟩⟨1∣ × ∣0⟩⟨0∣ = Zero). { lma'. }
       assert (H5' : ∣0⟩⟨0∣ × ∣1⟩⟨1∣ = Zero). { lma'. }
       rewrite H5, H5'.
       do 2 (rewrite kron_0_r). 
       rewrite H0.
       rewrite id_kron.
       rewrite H2.
       rewrite Mplus_0_l.
       rewrite Mplus_0_r.
       rewrite <- kron_plus_distr_l.
       assert (H6 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2). { lma'. }
       rewrite H6.
       rewrite id_kron.
       reflexivity.
Qed.


(* Heisenberg.v line 2506 *)
Lemma unit_prog_ctrl_app : forall (prg_len : nat) (U : Square 2) (ctrl targ : nat),
  WF_Unitary U -> WF_Unitary (prog_ctrl_app prg_len U ctrl targ). 
Proof. intros.
       unfold prog_ctrl_app.
       bdestruct (ctrl =? targ).
       - rewrite andb_false_r.
         auto with unit_db.
       - bdestruct (ctrl <? prg_len);
         bdestruct (targ <? prg_len);
         simpl; try lia; auto with unit_db.
         bdestruct (ctrl <? targ).
         + rewrite (easy_pow5 ctrl targ _); try easy.
           apply kron_unitary.
           apply kron_unitary; auto with unit_db.
           apply unit_proj; try easy.
           intro.  
           nia. 
           auto with unit_db. 
         + rewrite (easy_pow5' targ ctrl _); try easy.
           apply kron_unitary.
           apply kron_unitary; auto with unit_db.
           auto with unit_db.
           apply unit_proj2; try easy. 
           intro. lia.
           auto with unit_db.
           lia. 
Qed.



(* Heisenberg.v line 2888 *)
Lemma kron_breakdown1 : forall (a a' b b' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  a ⊗ b = a' ⊗ b' -> 
  (forall i j k l : nat, ((a i j) * (b k l) = (a' i j) * (b' k l))%C).
Proof. intros a a' b b' H H0 H1 H2 H3 i j k l.  
       bdestruct (i <? 2); bdestruct (j <? 2); bdestruct (k <? 2); bdestruct (l <? 2);
         try (rewrite H, H0; try (left; easy); try (right; easy); lca);
         try (rewrite H1, H2; try (left; easy); try (right; easy); lca).
       assert (H' : ((a ⊗ b) (k + i*2) (l + j*2) = (a' ⊗ b') (k + i*2) (l + j*2))%nat).
       rewrite H3; easy. 
       unfold kron in H'. 
       do 2 rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
Qed.

(* Heisenberg.v line 2903 *)
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
       assert (H' : ((a ⊗ b .+ c ⊗ d) (k + i*2) (l + j*2) = 
                    (a' ⊗ b' .+ c' ⊗ d') (k + i*2) (l + j*2))%nat).
       rewrite H7; easy. 
       unfold kron, Mplus in H'. 
       do 2 rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
Qed.

(* Heisenberg.v line 2921 *)
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



(* Heisenberg.v line 2939 *)
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

(* Heisenberg.v line 2958 *)
Lemma cnot_conv_inc : forall {n} (a a' b b' : Square 2) (C C' : Square (2^n)),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
  WF_Matrix C -> 
  cnot × (a ⊗ b) = (a' ⊗ b') × cnot -> C = C' ->
  @Mmult (2 * 2^n * 2) (2 * 2^n * 2) (2 * 2^n * 2) 
         (∣0⟩⟨0∣ ⊗ Matrix.I (2 * 2 ^ n) .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ n) ⊗ σx) (a ⊗ C ⊗ b) =
  (a' ⊗ C' ⊗ b') × (∣0⟩⟨0∣ ⊗ Matrix.I (2 * 2 ^ n) .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ n) ⊗ σx).
Proof. intros; subst.
       do 2 replace (2 * (2 * 2^n))%nat with (2 * 2^n * 2)%nat by lia.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
       replace (2 * 2 ^ n)%nat with (2 ^ n * 2)%nat by lia. 
       rewrite <- id_kron.
       rewrite <- kron_assoc; auto with wf_db.
       repeat rewrite kron_mixed_product.
       replace (2 ^ n * 2)%nat with (2 * 2 ^ n)%nat by lia. 
       repeat rewrite kron_mixed_product.
       rewrite Mmult_1_l, Mmult_1_r; auto.
       assert (H' : cnot = ∣0⟩⟨0∣ ⊗ Matrix.I 2 .+ ∣1⟩⟨1∣ ⊗ σx).
       { lma'. }
       rewrite H' in H4.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l in H4.
       repeat rewrite kron_mixed_product in H4.
       apply kron_rearrange2; auto with wf_db.
Qed.

(* Heisenberg.v line 2983 *)
Lemma notc_conv_inc : forall {n} (a a' b b' : Square 2) (C C' : Square (2^n)),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->  WF_Matrix C -> 
  notc × (a ⊗ b) = (a' ⊗ b') × notc -> C = C' ->
  @Mmult (2 * 2^n * 2) (2 * 2^n * 2) (2 * 2^n * 2) 
         ( Matrix.I (2 * 2 ^ n)  ⊗  ∣0⟩⟨0∣ .+ σx  ⊗ Matrix.I (2 ^ n) ⊗ ∣1⟩⟨1∣) (a ⊗ C ⊗ b) =
  (a' ⊗ C' ⊗ b') × (Matrix.I (2 * 2 ^ n) ⊗  ∣0⟩⟨0∣  .+ σx ⊗ Matrix.I (2 ^ n) ⊗ ∣1⟩⟨1∣).
Proof. intros; subst.
       do 2 replace (2 * (2 * 2^n))%nat with (2 * 2^n * 2)%nat by lia.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
       rewrite <- id_kron.
       repeat rewrite kron_mixed_product.
       Msimpl.
       assert (H' : notc = Matrix.I 2  ⊗  ∣0⟩⟨0∣ .+ σx ⊗  ∣1⟩⟨1∣).
       { lma'. }
       rewrite H' in H4.
       rewrite Mmult_plus_distr_r, Mmult_plus_distr_l in H4.
       repeat rewrite kron_mixed_product in H4.
       apply kron_rearrange2; auto with wf_db.
       rewrite Mmult_1_l, Mmult_1_r in H4; try auto.
Qed.


(* Heisenberg.v line 2692 *)
Lemma CX_is_CNOT : (∣0⟩⟨0∣ ⊗ (I 2) .+ ∣1⟩⟨1∣ ⊗ σx) = cnot. 
Proof. lma'. 
Qed.

(* Heisenberg.v line 2696 *)
Lemma CX_is_NOTC : ((Matrix.I 2) ⊗ ∣0⟩⟨0∣ .+ σx ⊗ ∣1⟩⟨1∣) = notc. 
Proof. lma'. 
Qed.

(* Heisenberg.v line 2701 *)
Definition CZ := (∣0⟩⟨0∣ ⊗ (I 2) .+ ∣1⟩⟨1∣ ⊗ σz).

(* Heisenberg.v line 2704 *)
Lemma WF_CZ : WF_Matrix CZ. 
Proof. unfold CZ. 
       auto with wf_db.
Qed.

(* Heisenberg.v line 2709 *)
Hint Resolve WF_CZ : wf_db.

(* Heisenberg.v line 2711 *)
Lemma unit_CZ : WF_Unitary CZ. 
Proof. split; auto with wf_db. 
       lma'. Qed.

(* Heisenberg.v line 2716 *)
Hint Resolve unit_CZ : unit_db.
                

(* Heisenberg.v line 2720 *)
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

(* Heisenberg.v line 2739 *)
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

(* Heisenberg.v line 2758 *)
Lemma adj_ctrlX_is_cnot1 : prog_ctrl_app 2 σx 0 1 = cnot.
Proof. rewrite adj_ctrlX_is_cnot; try lia. 
       rewrite Nat.sub_0_r, Nat.sub_diag, Nat.pow_0_r.
       rewrite kron_1_l, kron_1_r; auto with wf_db.
Qed.

(* Heisenberg.v line 2765 *)
Lemma adj_ctrlX_is_notc1 : prog_ctrl_app 2 σx 1 0 = notc.
Proof. rewrite adj_ctrlX_is_notc; try lia. 
       rewrite Nat.sub_0_r, Nat.sub_diag, Nat.pow_0_r.
       rewrite kron_1_l, kron_1_r; auto with wf_db.
Qed.



(* switched order of 2 by 2 kron products. *) 
(* Useful for showing that effect of cnot on a ⊗ b *)
(* Heisenberg.v line 2775 *)
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

(* Heisenberg.v line 2797 *)
Lemma WF_sko : forall A, WF_Matrix (switch_kron_order A).
Proof. unfold WF_Matrix; intros. 
       destruct H.
       - do 4 (destruct x; try lia); easy.   
       - do 4 (destruct y; try lia). 
         do 4 (destruct x; try easy).
Qed.

(* Heisenberg.v line 2805 *)
Hint Resolve WF_sko : wf_db.

(* Heisenberg.v line 2807 *)
Lemma sko_twice_id : forall (A : Square 4), 
    WF_Matrix A -> switch_kron_order (switch_kron_order A) = A.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order. 
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
       lia.
Qed.

(* Heisenberg.v line 2819 *)
Lemma Mmult_sko : forall (A B : Square 4), switch_kron_order (A × B) = 
                                      switch_kron_order A × switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mmult. 
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
Qed.

(* Heisenberg.v line 2830 *)
Lemma Mplus_sko : forall (A B : Square 4), switch_kron_order (A .+ B) = 
                                      switch_kron_order A .+ switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mplus. 
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
Qed.

(* Heisenberg.v line 2840 *)
Lemma kron_sko_verify : forall (a b : Square 2),
  WF_Matrix a -> WF_Matrix b ->
  switch_kron_order (a ⊗ b) = b ⊗ a.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, kron.
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
       lia. 
Qed.

(* Heisenberg.v line 2852 *)
Lemma notc_sko_cnot : switch_kron_order cnot = notc.
Proof. rewrite <- CX_is_NOTC, <- CX_is_CNOT.
       rewrite Mplus_sko, kron_sko_verify, kron_sko_verify; auto with wf_db.
Qed.

(* Heisenberg.v line 2857 *)
Lemma cnot_sko_notc : switch_kron_order notc = cnot.
Proof. rewrite <- CX_is_NOTC, <- CX_is_CNOT.
       rewrite Mplus_sko, kron_sko_verify, kron_sko_verify; auto with wf_db.
Qed.

(* Heisenberg.v line 2863 *)
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

(* Heisenberg.v line 2875 *)
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

(* Types.v line 123 *)
Lemma fold_left_Cmult : forall (c : C) (l : list C),
        fold_left Cmult l (C1 * c)%C = (c * (fold_left Cmult l C1))%C.
Proof. intros c l. generalize dependent c.
  induction l.
  - simpl. intros c.  lca.
  - simpl. intros c. rewrite <- Cmult_assoc. rewrite (Cmult_comm c a).
    rewrite 2 IHl.
    rewrite Cmult_assoc.
    rewrite (Cmult_comm a c). reflexivity.
Qed.

(* Types.v line 846 *)
Lemma n_plus_m_zero_n_zero : forall (n m : nat), (n + m = 0 -> n = 0)%nat.
  intros n m H. induction m.
  - rewrite Nat.add_0_r in H. assumption.
  - rewrite Nat.add_comm in H. simpl in H. discriminate.
Qed.

(* Types.v line 947 *)
Lemma fold_left_Mplus : forall {n} (a b : Square n) (A : list (Square n)),  
    fold_left Mplus (A) (b .+ a)%M =  (fold_left Mplus A (b) .+  a)%M.
Proof. intros n a b A.  generalize dependent a. simpl. induction A.
  - simpl. reflexivity.
  - simpl. intros a0. rewrite (Mplus_assoc _ _ b a0 a).
    rewrite (Mplus_comm _ _ a0 a).  rewrite IHA. symmetry. rewrite IHA.
    rewrite <- (Mplus_assoc _ _ _ a a0). reflexivity.
Qed.


(* Types.v line 1206 *)
Lemma C_inj_l : forall (c x y : C), x = y -> (c * x = c * y)%C.
Proof. intros. rewrite H. easy. Qed.

(* Types.v line 1209 *)
Lemma C_inv_l : forall (c x y : C), c <> C0 -> (c * x = c * y)%C -> x = y.
Proof. intros. apply C_inj_l with (c:=/c) in H0. rewrite ! Cmult_assoc in H0.
  rewrite Cinv_l in H0; try assumption. rewrite ! Cmult_1_l in H0; assumption.
Qed.

(* Types.v line 1213 *)
Lemma C_inj_r : forall (c x y : C), x = y -> (x * c = y * c)%C.
Proof. intros. rewrite H. easy. Qed.

(* Types.v line 1216 *)
Lemma C_inv_r : forall (c x y : C), c <> C0 -> (x * c = y * c)%C -> x = y.
Proof. intros. apply C_inj_r with (c:=/c) in H0. rewrite <- ! Cmult_assoc in H0.
  rewrite Cinv_r in H0; try assumption. rewrite ! Cmult_1_r in H0; assumption.
Qed.

(* Types.v line 1247 *)
Lemma Mmult_eq_l : forall {m n o : nat} (A A' : Matrix m n) (B : Matrix n o), A = A' -> A × B = A' × B.
Proof. intros. rewrite H. easy. Qed.

(* Types.v line 1250 *)
Lemma Mmult_eq_r : forall {m n o : nat} (A : Matrix m n) (B B' : Matrix n o), B = B' -> A × B = A × B'.
Proof. intros. rewrite H. easy. Qed.

(* Types.v line 1253 *)
Lemma Mscale_inj : forall {m n} (A B : Matrix m n) (c : C), A = B -> (c .* A = c .* B)%M.
Proof. intros m n A B c H. rewrite H. easy. Qed. 

(* Types.v line 1256 *)
Lemma Mscale_inv : forall {m n} (A B : Matrix m n) (c : C), c <> C0 -> (c .* A = c .* B)%M ->  A = B.
Proof. intros m n A B c H H0. apply Mscale_inj with (c:= /c) in H0.
  rewrite ! Mscale_assoc in H0. rewrite Cinv_l in H0; try easy.
  rewrite ! Mscale_1_l in H0. easy.
Qed.

(* Types.v line 1262 *)
Lemma kron_2_l' : forall {n} ,
      Matrix.I 2 ⊗ Matrix.I (2 ^ n + (2 ^ n + 0)) =
        Matrix.I (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + 0)).
Proof. intros n.
        replace (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + 0))%nat with (2 ^ (S (S n)))%nat.
        2:{ simpl; easy. }
        replace (2 ^ n + (2 ^ n + 0))%nat with (2 ^ (S n))%nat.
        2:{ simpl; easy. }
        rewrite <- ! kron_n_I. rewrite <- kron_n_assoc; auto with wf_db.
Qed.

Lemma kron_2_l : forall {n},
    Matrix.I 2 ⊗ Matrix.I (2 ^ n) = Matrix.I (2 ^ (S n)).
Proof.
  intros n.
  rewrite <- ! kron_n_I. rewrite <- kron_n_assoc; auto with wf_db.
Qed.
    

(* Types.v line 1273 *)
Lemma big_kron_adj : forall {n} (l : list (Square n)), (⨂ l)† = (⨂ (map adjoint l)).
Proof. intros n l. induction l; simpl. lma'. rewrite kron_adjoint. rewrite IHl. rewrite ! map_length. reflexivity. Qed.

(* Types.v line 1289 *)
Lemma unitary_hermitian_anticommute_hermitian : forall {n} (A B : Square n), WF_Unitary A -> WF_Unitary B -> A † = A -> B † = B -> (A × B = -C1 .* (B × A))%M -> (((C1/√2) .* (A .+ B)) † = ((C1/√2) .* (A .+ B)))%M.
Proof. intros n A B UA UB HA HB AC. 
    rewrite Mscale_adj.
    replace ((C1 / √ 2) ^* )%C with (C1 / √ 2)%C by lca.
    rewrite Mplus_adjoint.
    rewrite HA, HB.
    reflexivity.
Qed.

(* Types.v line 1299 *)
Lemma unitary_hermitian_anticommute_unitary : forall {n} (A B : Square n), WF_Unitary A -> WF_Unitary B -> A † = A -> B † = B -> (A × B = - C1 .* (B × A))%M -> WF_Unitary ((C1/√2) .* (A .+ B))%M.
Proof. intros n A B UA UB HA HB AC.
    inversion UA. inversion UB.
    constructor; auto with wf_db.
    rewrite Mscale_adj.
    replace ((C1 / √ 2) ^* )%C with (C1 / √ 2)%C by lca.
    rewrite Mplus_adjoint.
    rewrite HA, HB.
    rewrite Mscale_mult_dist_l, Mscale_mult_dist_r.
    rewrite Mscale_assoc.
    replace (C1 / √ 2 * (C1 / √ 2))%C with (C1/C2)%C by C_field.
    rewrite Mmult_plus_distr_l.
    rewrite ! Mmult_plus_distr_r.
    rewrite Mplus_assoc.
    replace (B × A .+ (A × B .+ B × B))%M with ((B × A .+ A × B) .+ B × B)%M by lma'.
    rewrite AC.
    replace (B × A .+ -C1 .* (B × A))%M with (@Zero n n) by lma'.
    rewrite Mplus_0_l.
    rewrite <- HA at 1.
    rewrite <- HB at 1.
    rewrite H0, H2.
    lma'.
Qed.

(* Types.v line 1689 *)
Lemma fold_left_Mplus_app_Zero : forall {n : nat} (A B : list (Square n)),
    fold_left Mplus (A++B) Zero%M = ((fold_left Mplus A Zero) .+ (fold_left Mplus B Zero))%M.
Proof. intros n A B. induction A.
  - simpl. rewrite Mplus_0_l. reflexivity.
  - simpl. rewrite 2 fold_left_Mplus. rewrite IHA.
    symmetry. do 2 (rewrite Mplus_assoc; rewrite Mplus_comm).
    assert (fold_left Mplus B Zero .+ fold_left Mplus A Zero = fold_left Mplus A Zero .+ fold_left Mplus B Zero)%M. { rewrite Mplus_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.

(* Types.v line 1699 *)
Lemma Zero_kron : forall {m n o p} (a : Matrix m n) (b : Matrix (m * o) (n * p)),
    ((@Zero (m * o) (n * p)) .+ b = a ⊗ (@Zero o p) .+ b)%M.
Proof. intros m n o p a b. lma. Qed. 

(* Types.v line 1918 *)
Lemma ite_conv : forall {X : Type} (x1 x2 : X), (if true && true then x1 else x2) = x1.
Proof. easy. Qed.

(* TODO : remove since in Matrix.v => could not find in Matrix.v *)
(* Types.v line 3882 *)
Lemma kron_simplify : forall (n m o p : nat) (a b : Matrix n m) (c d : Matrix o p), 
    a = b -> c = d -> a ⊗ c = b ⊗ d.
Proof. intros n m o p a b c d H H0.
       rewrite H, H0.
       easy.
Qed.

(* Types.v line 4387 *)
(** B invertible -> 
     A * B = C * B -> A = C ***)

(* Types.v line 4389 *)
Lemma Minvert_r {n : nat} (A B C : Square n) :
  WF_Matrix A -> WF_Matrix C ->
  invertible B -> A × B = C × B ->  A = C.
Proof. intros WFA WFC H H0.
       destruct H as [B' H']. inversion H'.
       assert ( A × B × B' = C × B × B' ).
       { rewrite H0. easy. }
       rewrite ! Mmult_assoc in H2.
       rewrite ! H in H2.
       rewrite ! Mmult_1_r in H2; assumption.
Qed.

(* Types.v line 4401 *)
(** B invertible -> A * B = B -> A = Id ***) (* results from the above *)

(* Types.v line 4404 *)
(** unitary -> invertible ***) (* obvious *)

(* Types.v line 4407 *)
Lemma Mmult_r {n : nat} (A B C : Square n) :
  WF_Matrix A -> WF_Matrix C ->
  WF_Matrix B -> A = C -> A × B = C × B.
Proof. intros H H0 H1 H2. rewrite H2. reflexivity. Qed. 

(* Types.v line 4413 *)
Lemma Cmult_r (a b c : C) : a = b -> (a * c = b * c)%C.
Proof. intros H. rewrite H. easy. Qed.

(* Types.v line 4416 *)
Lemma Cmult_l (a b c : C) : a = b -> (c * a = c * b)%C.
Proof. intros H. rewrite H. easy. Qed.


(* Types.v line 4412 *)
(** ** A ⊗ B = C ⊗ D -> A = c1 * C & B = c2 * D & c1*c2 = 1 ** **)
(** Proof :
  Let A, C have the same w × x dimensions and B, D have the same y × z dimensions.
  Let A, B, C, D be nonzero matrices.
  
  Then there exists some nonzero elements a_{i,j}, b_{k,l} in A, B respectively.
  Consider the (y(i-1)+k, w(j-1)+l) th element in A ⊗ B which is a nonzero element 
               a_{i,j} * b_{k,l}.
  Now consider the (y(i-1)+k, w(j-1)+l) th element in C ⊗ D = A ⊗ B which must be a 
               nonzero element c_{i,j} * d_{k,l} = a_{i,j} * b_{k,l}.           --------------------------- (1)
  Both c_{i,j} and d_{k,l} are nonzero.

  From A ⊗ B = C ⊗ D, we have a_{p,q} * b_{r,s} = c_{p,q} * d_{r,s}   
               for any 1 <= p <= w, 1 <= q <= x, 1 <= r <= y, and 1 <= s <= z.    ---------------- (2)

  Consider the matrix A * b_{k,l} and C * d_{k,l}. 
  For an arbitrary p, q, since the (p,q) th element of both matrices are 
               a_{p,q} * b_{k,l} and c_{p,q} * d_{k,l} respectively, 
               by (2), we have A * b_{k,l} = C * d_{k,l}.               -------------------------------------- (3)

  Now consider the matrix a_{i,j} * B and c_{i,j} * D. 
  For an arbitrary p, q, since the (p,q) th element of both matrices are 
               a_{i,j} * b_{p,q} and c_{i,j} * d_{p,q} respectively, 
               by (2), we have a_{i,j} * B = c_{i,j} * D.                  -------------------------------------- (4)

   From (1), let β = d_{k,l} / b_{k,l} = a_{i,j} / c_{i,j}.

   Then from (3), A = C * d_{k.l} / b_{k,l} = C * β,
   and from (4), B = D * c_{i,j} / a_{i,j} = D * (1/β).
QED.
 **)

(* Types.v line 4453 *)
Lemma tensor_nonzero_exists {n m o p : nat} (A D : Matrix n m) (B E : Matrix o p) (* c1 c2 : C *) :
  WF_Matrix A -> WF_Matrix B -> WF_Matrix D -> WF_Matrix E ->
  A ⊗ B <> Zero ->
  A ⊗ B = D ⊗ E -> exists c1 c2, A = (c1 .* D)%M /\ B = (c2 .* E)%M /\ (c1 * c2)%C = C1.
Proof.
  intros WFA WFB WFD WFE H G. 
  Search (?f = ?g -> ?f _ = ?g _).
  Search Coq.Logic.ClassicalFacts.excluded_middle.
  assert (A0 : A <> Zero).
  { intro H0. rewrite H0 in H. rewrite kron_0_l in H. contradiction. }
  assert (A1 :  ~ A == Zero ).
  { intro H0. apply mat_equiv_eq in H0. contradiction. assumption. auto with wf_db. }
  assert (A2 : exists i j, i < n /\ j < m /\ A i j <> C0).
  { unfold mat_equiv in A1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in A1.
    destruct A1 as [i A1].
    apply Classical_Pred_Type.not_all_ex_not in A1.
    destruct A1 as [j A1].
    exists i, j.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in A1.
    destruct A1 as [A1 A2].
    split. assumption.
    apply Classical_Prop.imply_to_and in A2.
    destruct A2 as [A2 A3].
    split. assumption.
    assumption. }
  assert (B0 : B <> Zero).
  { intro H0. rewrite H0 in H. rewrite kron_0_r in H. contradiction. }
  assert (B1 : ~ B == Zero ).
  { intro H0. apply mat_equiv_eq in H0. contradiction. assumption. auto with wf_db. }
  assert (B2 : exists i j, i < o /\ j < p /\ B i j <> C0).
  { unfold mat_equiv in B1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in B1.
    destruct B1 as [k B1].
    apply Classical_Pred_Type.not_all_ex_not in B1.
    destruct B1 as [l B1].
    exists k, l.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in B1.
    destruct B1 as [B1 B2].
    split. assumption.
    apply Classical_Prop.imply_to_and in B2.
    destruct B2 as [B2 B3].
    split. assumption.
    assumption. }

  destruct A2 as [i [j [A2 [A3 A4]]]].
  destruct B2 as [k [l [B2 [B3 B4]]]].

  remember G as G0. clear HeqG0.
  
  unfold kron in G0.
  apply f_equal_inv with (x := o * i + k) in G0.
  apply f_equal_inv with (x := p * j + l) in G0.
  assert (R1: (o * i + k) / o = i). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R2: (p * j + l) / p = j). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }
  assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }


  rewrite R1, R2, R3, R4 in G0.

  assert (H0 : (A i j * B k l)%C <> C0). { apply Cmult_neq_0; assumption. }

  assert (H1 : (D i j * E k l)%C <> C0). { rewrite G0 in H0. assumption. }
  assert (H2 : A i j <> C0). { intro H2. rewrite H2 in H0. rewrite Cmult_0_l in H0. contradiction. }
  assert (H3 : B k l <> C0). { intro H3. rewrite H3 in H0. rewrite Cmult_0_r in H0. contradiction. }
  assert (H4 : D i j <> C0). { intro H4. rewrite H4 in H1. rewrite Cmult_0_l in H1. contradiction. }
  assert (H5 : E k l <> C0). {intro H5. rewrite H5 in H1. rewrite Cmult_0_r in H1. contradiction. }

  assert (G1 : forall w x y z : nat, w < n -> x < m -> y < o -> z < p -> (A w x * B y z = D w x * E y z)%C). { intros w x y z G1 G2 G3 G4. remember G as G5. clear HeqG5. unfold kron in G5.
  apply f_equal_inv with (x := o * w + y) in G5. apply f_equal_inv with (x := p * x + z) in G5.
  assert (R1': (o * w + y) / o = w). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R2': (p * x + z) / p = x). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R3': (o * w + y) mod o = y). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }
  assert (R4': (p * x + z) mod p = z). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }
  
  rewrite R1', R2', R3', R4' in G5. assumption. }

  eexists. eexists.
  split. 
  - prep_matrix_equality.
    remember G1 as G2. clear HeqG2.
  
    specialize (G2 x y k l ).
    bdestruct (x <? n).
    + bdestruct (y <? m).
      * unfold ".*"%M.
        specialize (G2 H6 H7 B2 B3). 
        assert ( A x y = ((E k l) / (B k l)) * D x y )%C.
        { apply Cmult_r with (c := /(B k l)) in G2.
          assert ((B k l * / B k l)%C = C1).
          { apply Cinv_r. assumption. }
          rewrite <- Cmult_assoc in G2.
          rewrite H8 in G2.
          rewrite Cmult_1_r in G2.
          rewrite <- Cmult_assoc in G2.
          rewrite Cmult_comm in G2.
          assumption. }
        instantiate (1 := (E k l / B k l)%C).
        assumption.
      * unfold ".*"%M.
        unfold WF_Matrix in WFA. 
        unfold WF_Matrix in WFD.
        assert (x >= n \/ y >= m). { right. assumption. }
        specialize (WFA x y H8).
        specialize (WFD x y H8).
        rewrite WFA, WFD.
        lca.
    + unfold ".*"%M.
        unfold WF_Matrix in WFA. 
        unfold WF_Matrix in WFD.
        assert (x >= n \/ y >= m). { left. assumption. }
        specialize (WFA x y H7).
        specialize (WFD x y H7).
        rewrite WFA, WFD.
        lca. 
  - split. 
    + prep_matrix_equality.
    remember G1 as G2. clear HeqG2.
  
    specialize (G2 i j x y ).
    bdestruct (x <? o).
    * bdestruct (y <? p).
      -- unfold ".*"%M.
        specialize (G2 A2 A3 H6 H7). 
        assert ( B x y = ((D i j) / (A i j)) * E x y )%C.
        setoid_rewrite Cmult_comm in G2.
        { apply Cmult_r with (c := /(A i j)) in G2.
          assert ((A i j * / A i j)%C = C1).
          { apply Cinv_r. assumption. }
          rewrite <- Cmult_assoc in G2.
          rewrite H8 in G2.
          rewrite Cmult_1_r in G2.
          rewrite <- Cmult_assoc in G2.
          rewrite Cmult_comm in G2.
          assumption. }
        instantiate (1 := (D i j / A i j)%C).
        assumption.
      -- unfold ".*"%M.
         unfold WF_Matrix in WFB. 
        unfold WF_Matrix in WFE.
        assert (x >= o \/ y >= p). { right. assumption. }
        specialize (WFB x y H8).
        specialize (WFE x y H8).
        rewrite WFB, WFE.
        lca.
    * unfold ".*"%M.
         unfold WF_Matrix in WFB. 
        unfold WF_Matrix in WFE.
        assert (x >= o \/ y >= p). { left. assumption. }
        specialize (WFB x y H7).
        specialize (WFE x y H7).
        rewrite WFB, WFE.
        lca.
    + setoid_rewrite Cmult_assoc.
      apply Cmult_r with (c := /(A i j * B k l)%C) in G0.
      rewrite Cinv_r in G0.
      symmetry in G0.
      rewrite Cinv_mult_distr in G0.
      rewrite Cmult_assoc in G0.
      unfold Cdiv.
      rewrite <- ! Cmult_assoc.
      assert (/ B k l * (D i j * / A i j) = D i j * (/ A i j * / B k l))%C.
      {rewrite Cmult_comm.
       rewrite <- Cmult_assoc.
       reflexivity. }
      rewrite H6.
      rewrite ! Cmult_assoc.
      assert (E k l * D i j = D i j * E k l)%C.
      { rewrite Cmult_comm.
        reflexivity. }
      rewrite H7.
      assumption.
      assumption.
      assumption.
      assumption.
Qed.


(* Types.v line 4641 *)
Lemma Mat_eq_dec : forall m n (A B : Matrix m n),
    WF_Matrix A ->
    WF_Matrix B ->
    {A = B} + {A <> B}.
Proof.
  intros.
  destruct (mat_equiv_dec A B).
  - left.
    apply mat_equiv_eq; easy.
  - right.
    intros F.
    rewrite F in n0.
    apply n0.
    apply mat_equiv_refl. 
Qed.


(* Types.v line 4658 *)
Lemma tensor_swap {n m o p : nat} (A D : Matrix n m) (B E : Matrix o p) :
  WF_Matrix A -> WF_Matrix B -> WF_Matrix D -> WF_Matrix E ->
  A ⊗ B = D ⊗ E -> B ⊗ A = E ⊗ D.
Proof. intros.
       assert ({A ⊗ B = Zero} + {A ⊗ B <> Zero}). { apply Mat_eq_dec; auto with wf_db. }
       destruct H4.
       - assert (A = Zero \/ B = Zero).
         {
    (*** classical logic used.
         is this ok? ***)
           apply Classical_Prop.NNPP.
           intro.
           apply Classical_Prop.not_or_and in H4.
           destruct H4.
           assert (A1 : ~ A == Zero ).
           { intro. apply mat_equiv_eq in H6. contradiction. assumption. auto with wf_db. }
           assert (B1 : ~ B == Zero ).
           { intro. apply mat_equiv_eq in H6. contradiction. assumption. auto with wf_db. }
           
           assert (A2 : exists i j, i < n /\ j < m /\ A i j <> C0).
             { unfold mat_equiv in A1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in A1.
    destruct A1 as [i A1].
    apply Classical_Pred_Type.not_all_ex_not in A1.
    destruct A1 as [j A1].
    exists i, j.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in A1.
    destruct A1 as [A1 A2].
    split. assumption.
    apply Classical_Prop.imply_to_and in A2.
    destruct A2 as [A2 A3].
    split. assumption.
    assumption. }


  assert (B2 : exists i j, i < o /\ j < p /\ B i j <> C0).
  { unfold mat_equiv in B1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in B1.
    destruct B1 as [k B1].
    apply Classical_Pred_Type.not_all_ex_not in B1.
    destruct B1 as [l B1].
    exists k, l.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in B1.
    destruct B1 as [B1 B2].
    split. assumption.
    apply Classical_Prop.imply_to_and in B2.
    destruct B2 as [B2 B3].
    split. assumption.
    assumption. }

  destruct A2 as [i [j [A2 [A3 A4]]]].
  destruct B2 as [k [l [B2 [B3 B4]]]].
  
  Print f_equal_inv.
  unfold kron in H3.
  apply f_equal_inv with (x := o*i+k) in H3.
  apply f_equal_inv with (x := p*j+l) in H3.

    assert (R1: (o * i + k) / o = i). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R2: (p * j + l) / p = j). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }
    assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }

    rewrite R1, R2, R3, R4 in H3.

    assert ((A i j * B k l)%C <> C0).
    { intro.
      assert (A i j = C0).
      { Search "Cmult". apply Cmult_r with (c := /B k l) in H6.
        rewrite Cmult_0_l in H6.
        rewrite <- Cmult_assoc in H6.
        rewrite Cinv_r in H6.
        rewrite Cmult_1_r in H6.
        assumption. assumption. }
      contradiction. }

    unfold kron in e.
  apply f_equal_inv with (x := o*i+k) in e.
  apply f_equal_inv with (x := p*j+l) in e.
  rewrite R1, R2, R3, R4 in e.
  unfold Zero in e.
  contradiction. }

                assert (D = Zero \/ E = Zero).
         {
    (*** classical logic used.
         is this ok? ***)
           apply Classical_Prop.NNPP.
           intro.
           apply Classical_Prop.not_or_and in H5.
           destruct H5.
           assert (D1 : ~ D == Zero ).
           { intro. apply mat_equiv_eq in H7. contradiction. assumption. auto with wf_db. }
           assert (E1 : ~ E == Zero ).
           { intro. apply mat_equiv_eq in H7. contradiction. assumption. auto with wf_db. }
           
           assert (D2 : exists i j, i < n /\ j < m /\ D i j <> C0).
             { unfold mat_equiv in D1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in D1.
    destruct D1 as [i D1].
    apply Classical_Pred_Type.not_all_ex_not in D1.
    destruct D1 as [j D1].
    exists i, j.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in D1.
    destruct D1 as [D1 D2].
    split. assumption.
    apply Classical_Prop.imply_to_and in D2.
    destruct D2 as [D2 D3].
    split. assumption.
    assumption. }


  assert (E2 : exists i j, i < o /\ j < p /\ E i j <> C0).
  { unfold mat_equiv in E1. Print Logic. Search (~ forall x, _ ).
    (*** classical logic used.
         is this ok? ***)
    apply Classical_Pred_Type.not_all_ex_not in E1.
    destruct E1 as [k E1].
    apply Classical_Pred_Type.not_all_ex_not in E1.
    destruct E1 as [l E1].
    exists k, l.
    Search (~ (?P -> ?Q) -> (?P /\ ~ ?Q)).
    apply Classical_Prop.imply_to_and in E1.
    destruct E1 as [E1 E2].
    split. assumption.
    apply Classical_Prop.imply_to_and in E2.
    destruct E2 as [E2 E3].
    split. assumption.
    assumption. }

  destruct D2 as [i [j [D2 [D3 D4]]]].
  destruct E2 as [k [l [E2 [E3 E4]]]].
  
  Print f_equal_inv.
  unfold kron in H3.
  apply f_equal_inv with (x := o*i+k) in H3.
  apply f_equal_inv with (x := p*j+l) in H3.

    assert (R1: (o * i + k) / o = i). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R2: (p * j + l) / p = j). { rewrite Nat.mul_comm. rewrite Nat.div_add_l. rewrite Nat.div_small. rewrite Nat.add_0_r. reflexivity. assumption. lia. }
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }
    assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.mod_add. rewrite Nat.mod_small. reflexivity. assumption. lia. }

    rewrite R1, R2, R3, R4 in H3.

    assert ((D i j * E k l)%C <> C0).
    { intro.
      assert (D i j = C0).
      { Search "Cmult". apply Cmult_r with (c := /E k l) in H7.
        rewrite Cmult_0_l in H7.
        rewrite <- Cmult_assoc in H7.
        rewrite Cinv_r in H7.
        rewrite Cmult_1_r in H7.
        assumption. assumption. }
      contradiction. }

    unfold kron in e.
  apply f_equal_inv with (x := o*i+k) in e.
  apply f_equal_inv with (x := p*j+l) in e.
  rewrite R1, R2, R3, R4 in e.
  unfold Zero in e.
  rewrite H3 in e.
  contradiction. }

         destruct H4.
         + destruct H5.
           * rewrite H4.
             rewrite H5.
             rewrite kron_0_r.
             rewrite kron_0_r.
             reflexivity.
           * rewrite H4.
             rewrite H5.
             rewrite kron_0_r.
             rewrite kron_0_l.
             reflexivity.
         + destruct H5.
           * rewrite H4.
             rewrite H5.
             rewrite kron_0_r.
             rewrite kron_0_l.
             reflexivity.
           * rewrite H4.
             rewrite H5.
             rewrite kron_0_l.
             rewrite kron_0_l.
             reflexivity.
       - apply tensor_nonzero_exists in H3; auto.
       do 2 destruct H3.
       destruct H3 as [E1 [E2 E3]].
       rewrite E1, E2.
       distribute_scale.
       rewrite Cmult_comm.
       rewrite E3.
       rewrite Mscale_1_l.
       reflexivity.
Qed.

(* Types.v line 5169 *)
Lemma pow_inv : forall (a b c : nat), b = c -> a^b = a^c.
Proof. intros a b c H. rewrite H. easy. Qed.

(* Types.v line 5392 *)
Lemma kron_unitary3 : forall {m n o} (A : Matrix m m) (B : Matrix n n) (C : Matrix o o),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary C -> WF_Unitary (A ⊗ B ⊗ C).
Proof.
  intros m n o A B C [WFA UA] [WFB UB] [WFC UC].
  unfold WF_Unitary in *.
  split.
  auto with wf_db.
  rewrite kron_adjoint.
  rewrite kron_mixed_product.
  rewrite UC.
  rewrite kron_adjoint.
  rewrite kron_mixed_product.
  rewrite UA, UB.
  rewrite ! id_kron. 
  easy.
Qed.

(* Types.v line 5408 *)
Lemma kron_unitary3' : forall {m n o} (A : Matrix m m) (B : Matrix n n) (C : Matrix o o),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary C ->  (A ⊗ B ⊗ C) † × (A ⊗ B ⊗ C) =
  Matrix.I (m * n * o) .
Proof.
  intros m n o A B C WFUA WFUB WFUC.
  apply (kron_unitary3 _ _ _ WFUA WFUB WFUC).
Qed.

(* Types.v line 5417 *)
Lemma cnot_unitary' : forall (n : nat),
    0 < n ->
    WF_Unitary(∣0⟩⟨0∣ ⊗ Matrix.I (2 ^ (n))
                     .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ (n - 1)) ⊗ σx)%M.
Proof. intros n H.
       apply unit_proj; auto with unit_db. lia.
Qed.

(* Types.v line 5425 *)
Lemma notc_unitary' : forall (n : nat),
    0 < n ->
    WF_Unitary
    (Matrix.I (2 ^ n) ⊗ ∣0⟩⟨0∣
                              .+ σx ⊗ Matrix.I (2 ^ (n - 1)) ⊗ ∣1⟩⟨1∣)%M.
Proof. intros n H.
       apply unit_proj2; auto with unit_db. lia.
Qed.

(* Types.v line 5522 *)
Lemma matrix_equality_implies_element_equality :
  forall {m n} (A B : Matrix m n) (o p : nat),
    A = B -> A o p = B o p.
Proof. intros m n A B o p H. rewrite H. easy. Qed. 

(* Types.v line 5546 *)
Ltac mydo1 tac A B x y H :=
  match x with
  | O => idtac
  | S ?n => (tac A B n y H) ; (mydo1 tac A B n y H)
  end.

(* Types.v line 5551 *)
Ltac mydo2 tac A B x y H :=
  match y with
  | O => idtac
  | S ?n => (mydo1 tac A B x n H) ; (mydo2 tac A B x n H)
  end.

(* Types.v line 5556 *)
Ltac specialize_destruct_matrix_equality A B m n H :=
  let ceq := fresh "ceq" in
  specialize (matrix_equality_implies_element_equality A B m n H) as ceq;
  inversion ceq.

(* Types.v line 5560 *)
Ltac extract_linear_system H :=
  match type of H with
  | ?A = ?B =>
      match type of A with
      | Matrix ?m ?n => mydo2 specialize_destruct_matrix_equality A B m n H;
                        autorewrite with R_db in *;
                        subst
      end
  end.

(* Types.v line 5569 *)
Ltac extract_linear_systems :=
  repeat match goal with
    | [H : ?A = ?B |- _] =>
        match type of A with
        | Matrix ?m ?n => extract_linear_system H; clear H
        end
    end.

(* Types.v line 5576 *)
Ltac contradict_matrix_equality H :=
  repeat match goal with
  | [NZ: ?c <> C0 |- _] => apply C0_imp in NZ
  end;
  try (exfalso;
       extract_linear_system H;
       lra).

(* Types.v line 5583 *)
Ltac contradict_matrix_equalities :=
  repeat match goal with
  | [NZ: ?c <> C0 |- _] => apply C0_imp in NZ
  end;
  try (exfalso;
       extract_linear_systems;
       lra).


(* Types.v line 5612 *)
Lemma norm_is_one_implies_nonzero : forall (c : C),
    (c * c ^* )%C = C1 -> c <> C0.
Proof. intros c H.
       destruct c.
       inversion H.
       rewrite H2.
       intros H0.
       inversion H0.
       rewrite H4, H5 in H1.
       contradict H1.
       lra.
Qed.






