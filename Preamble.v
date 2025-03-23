Require Export Permutation.
Require Export QuantumLib.Quantum.
Require Import QuantumLib.VectorStates.

(* Some helpers *)

Local Open Scope nat_scope.

Lemma kron_assoc' : forall {m n p q r s mp nq pr qs : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  mp = m * p -> nq = n * q -> pr = p * r -> qs = q * s ->
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  (@kron mp nq r s (@kron m n p q A B) C) = (@kron m n pr qs A (@kron p q r s B C)).                                
Proof. intros. subst. apply kron_assoc; auto. Qed.  


Lemma easy_sub3 : forall (n k : nat), n <> 0 -> n + k - 0 - 1 = n - 0 - 1 + k. 
Proof. intros. 
       destruct n as [| n].
       - easy.
       - simpl. lia. 
Qed.

Lemma easy_sub6 : forall (a c b : nat), 
  b < c -> a < b -> c = (a + S (b - a) + (c - b - 1)).
Proof. intros. lia. Qed.


Lemma easy_pow : forall (a n m : nat), a^(n + m) = a^n * a^m.
Proof. intros. induction n as [| n'].
       - simpl. nia.
       - simpl. rewrite IHn'. nia.
Qed.
Lemma easy_pow2 : forall (a p : nat), p <> 0 -> a^p = a * a ^ (p - 0 - 1). 
Proof. intros. destruct p as [| p']. easy. simpl. 
       rewrite Nat.sub_0_r.  easy.
Qed.
Lemma easy_pow3 : forall (n m : nat), m < n -> 2^n = (2^m) * 2 * 2^(n - m - 1).
Proof. intros. 
       assert (H' : 2^m * 2 = 2^(m + 1)). 
       { rewrite easy_pow. reflexivity. } 
       rewrite H'. 
       rewrite <- easy_pow.
       assert (H'' : m < n -> m + 1 + (n - m - 1) = n).
       { nia. }
       rewrite H''. 
       reflexivity.
       assumption. 
Qed.
Lemma easy_pow4 : forall (n : nat), (0 >= 2^n) -> False. 
Proof. intros. induction n as [| n'].
       - simpl in *. nia.
       - simpl in *. 
         assert (H' : forall (a : nat), a + 0 = a). { nia. }
         rewrite H' in H.
         assert (H'' : forall (a : nat), a + a >= a). { nia. }
         apply IHn'.
         nia. 
Qed.
Lemma easy_pow5 : forall (a b c : nat), 
  b < c -> a < b ->
  2^c = (2^a * (2^(b - a) + (2^(b - a) + 0))) * 2^(c - b - 1).
Proof. intros.
       assert (H' : forall n, 2^n + (2^n + 0) = 2^(S n)).
       { reflexivity. } 
       rewrite H'.
       do 2 (rewrite <- easy_pow).  
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow5' : forall (a b c : nat), 
  b < c ->  a < b ->
  2^c = (2^a * (2^(b - a) * 2)) * 2^(c - b - 1).
Proof. intros.
       assert (H' : 2 ^ (b - a) * 2 = 2 ^ (b - a) * 2^1).
       { reflexivity. } 
       rewrite H'.
       do 3 (rewrite <- easy_pow).
       assert (H'' : b - a + 1 = S (b - a)). { nia. }
       rewrite H''.
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow6 : forall (n : nat), n <> 0 -> 2*2^n = (2*2^(n-1))*2. 
Proof. destruct n.
       - easy.
       - intros. 
         simpl.  
         replace (n - 0) with n by lia. 
         nia. 
Qed.

Lemma easy_pow6' : forall (n : nat), n <> 0 -> (2^n)*2 = (2*2^(n-1))*2. 
Proof. intros. rewrite Nat.mul_comm.
       apply easy_pow6; easy.
Qed.



(*************************)
(* Some basic list stuff *)
(*************************)


Definition zipWith {X Y Z: Type} (f : X -> Y -> Z) (As : list X) (Bs : list Y) : list Z :=
  map (uncurry f) (combine As Bs).


Lemma zipWith_len_pres : forall {X Y Z : Type} (f : X -> Y -> Z) (n : nat) 
                                (As : list X) (Bs : list Y),
  length As = n -> length Bs = n -> length (zipWith f As Bs) = n.
Proof. intros. 
       unfold zipWith.
       rewrite map_length.
       rewrite combine_length.
       rewrite H, H0; lia.
Qed.


Lemma zipWith_app_product : forall {X Y Z: Type} (f : X -> Y -> Z) (n : nat) 
                               (l0s l2s : list X) (l1s l3s : list Y),
  length l0s = n -> length l1s = n -> 
  (zipWith f l0s l1s) ++ (zipWith f l2s l3s) = zipWith f (l0s ++ l2s) (l1s ++ l3s).
Proof. induction n as [| n'].
       - intros. destruct l0s; destruct l1s; easy. 
       - intros. destruct l0s; destruct l1s; try easy.
         unfold zipWith in *.
         simpl in *. 
         rewrite <- IHn'; try nia. 
         reflexivity. 
Qed.


Lemma zipWith_cons : forall {X Y Z : Type} (f : X -> Y -> Z) (a : X) (b : Y) (A : list X) (B : list Y),
  zipWith f (a :: A) (b :: B) = (f a b) :: (zipWith f A B).
Proof. intros. 
       unfold zipWith. simpl. 
       unfold uncurry. 
       simpl. easy. 
Qed.


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
           + apply Nat.le_0_r in H. rewrite H in H0. easy.
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
             apply le_n_S in H. apply Nat.lt_le_incl.
             apply H.
Qed.


(* defining switch and many lemmas having to do with switch and nth *)

Fixpoint switch {X : Type} (ls : list X) (x : X) (n : nat) :=
  match ls with
  | [] => []
  | (h :: ls') =>
    match n with
    | 0 => x :: ls'
    | S n' => h :: (switch ls' x n')
    end
  end.

Lemma switch_len : forall {X : Type} (n : nat) (ls : list X) (x : X),
    length (switch ls x n) = length ls. 
Proof. induction n as [| n'].
       - destruct ls. easy. easy.
       - intros. destruct ls. 
         easy. simpl. 
         rewrite IHn'. 
         reflexivity. 
Qed.


Lemma switch_map : forall {X Y : Type} (n : nat) (ls : list X) (x : X) (f : X -> Y),
    map f (switch ls x n) = switch (map f ls) (f x) n.
Proof. induction n as [| n'].
       - intros. destruct ls; easy.
       - intros. destruct ls. easy.
         simpl. rewrite IHn'. easy.
Qed.
         
Lemma switch_switch_diff : forall {X : Type} (n m : nat) (ls : list X) (a b : X), 
  n <> m ->
  switch (switch ls a n) b m = switch (switch ls b m) a n.
Proof. induction n as [| n'].
       - intros. 
         destruct m; destruct ls; easy. 
       - intros. 
         destruct m; try (destruct ls; easy). 
         destruct ls; try easy. 
         simpl. 
         rewrite IHn'; try easy.
         bdestruct (n' =? m); lia. 
Qed.

Lemma switch_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> switch ls x 0 = x :: (skipn 1 ls).
Proof. intros. 
       destruct ls. 
       easy. 
       reflexivity. 
Qed.



Lemma nth_switch_hit : forall {X : Type} (n : nat) (ls : list X) (x def : X),
    n < length ls ->
    nth n (switch ls x n) def = x.
Proof. induction n as [| n'].
       - destruct ls; easy.
       - intros. 
         destruct ls; try easy.
         apply IHn'. 
         simpl in H.
         nia. 
Qed.



Lemma nth_switch_miss : forall {X : Type} (sn n : nat) (ls : list X) (x def : X),
    n <> sn ->
    nth n (switch ls x sn) def = nth n ls def.
Proof. induction sn as [| sn'].
       - destruct ls.
         easy.
         destruct n; easy.
       - intros. 
         destruct n.
         + destruct ls; easy.
         + assert (H' : n <> sn'). { nia. }
           destruct ls.                                   
           easy. simpl.  
           apply IHsn'.
           apply H'.
Qed.


Lemma switch_inc_helper : forall {X : Type} (n : nat) (l1 l2 : list X) (x : X),
    length l1 = n -> 
    switch (l1 ++ l2) x n = l1 ++ switch l2 x 0.
Proof. induction n as [| n'].
       - destruct l1. 
         reflexivity. 
         easy.
       - intros. destruct l1.  
         easy. 
         simpl. 
         rewrite <- IHn'.
         reflexivity. 
         simpl in H. 
         injection H. 
         easy. 
Qed.


Lemma switch_inc_helper2 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ switch (skipn n ls) x 0.
Proof. intros. 
       assert (H' : switch ls x n = switch (firstn n ls ++ skipn n ls) x n).
       { rewrite (firstn_skipn n ls). reflexivity. }
       rewrite H'.
       rewrite switch_inc_helper.
       reflexivity. 
       rewrite firstn_length_le.
       reflexivity. 
       nia.  
Qed.



Lemma skipn_nil_length : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls = [] -> length ls <= n. 
Proof. intros. 
       rewrite <- (firstn_skipn n ls).
       rewrite H. 
       rewrite app_nil_r.
       apply firstn_le_length.
Qed.


Lemma skipskip : forall {X : Type} (ls : list X) (n : nat),
    skipn (S n) ls = skipn 1 (skipn n ls).
Proof. induction ls as [| h].
       - destruct n. easy. easy. 
       - destruct n. easy.  
         assert (H : skipn (S n) (h :: ls) = skipn n ls). 
         { reflexivity. } 
         rewrite H.
         rewrite <- IHls. 
         reflexivity. 
Qed.


Lemma switch_inc_helper3 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch (skipn n ls) x 0 = [x] ++ (skipn (S n) ls).
Proof. intros. destruct (skipn n ls) as [| h] eqn:E.
       - apply skipn_nil_length in E. nia. 
       - assert (H' : skipn (S n) ls = l).
         { rewrite skipskip. 
           rewrite E.
           reflexivity. }
         rewrite H'.
         reflexivity.
Qed.


Lemma switch_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ [x] ++ (skipn (S n) ls). 
Proof. intros. 
       rewrite switch_inc_helper2.
       rewrite switch_inc_helper3.
       reflexivity. 
       apply H. apply H.
Qed.


Lemma nth_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> ls = (nth 0 ls x) :: (skipn 1 ls).
Proof. intros.
       destruct ls.
       easy. 
       reflexivity. 
Qed.


Lemma nth_helper : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> skipn n ls = [nth n ls x] ++ skipn (S n) ls.
Proof. induction n as [| n']. 
       - destruct ls. easy. easy. 
       - intros. destruct ls. 
         assert (H' : forall (n : nat), S n < 0 -> False). { nia. }
         apply H' in H. easy.
         rewrite skipn_cons.
         assert (H'' : nth (S n') (x0 :: ls) x = nth n' ls x). { easy. }
         rewrite H''.
         rewrite (IHn' ls x). 
         easy. 
         simpl in H. 
         assert (H''' : forall (n m : nat), S m < S n -> m < n). { nia. } 
         apply H''' in H.
         easy.
Qed.
         


Lemma nth_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> ls = (firstn n ls) ++ [nth n ls x] ++ (skipn (S n) ls). 
Proof. intros.
       rewrite <- nth_helper.  
       rewrite (firstn_skipn n ls).
       reflexivity. easy. 
Qed.








Lemma length_change : forall {X : Type} (A B : list X) (x : X),
  2 ^ (length (A ++ [x] ++ B)) = (2 ^ (length A)) * (2 * (2 ^ (length B))).
Proof. intros. 
       do 2 (rewrite app_length).
       simpl. 
       rewrite easy_pow.
       reflexivity. 
Qed.




(* a similar lemma to the one defined by Coq, but better for our purposes *)
Lemma skipn_length' : forall {X : Type} (n : nat) (ls : list X),
    length (skipn (S n) ls) = length ls - n - 1.
Proof. intros. 
       rewrite skipn_length.
       nia. 
Qed.


Lemma firstn_subset : forall {X : Type} (n : nat) (ls : list X),
    firstn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         destruct H as [H | H].
         left; easy. 
         right; apply IHn'; apply H.
Qed.

Lemma skipn_subset : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         right; apply IHn'; apply H.
Qed.


(* this is trivial but helps shorten proofs and Ltacs *)

Lemma kill_true : forall P : Prop,
  P /\ True <-> P.
Proof. split. intros [H _]. easy.
       intros. split. easy. easy.
Qed.

Lemma kill_false : forall P : Prop,
  P \/ False <-> P.
Proof. split. intros [H| ].  easy. easy.
       intros. left. easy.
Qed.

Lemma in_simplify : forall {X} (x x1 : X),
  In x1 [x] -> x1 = x.
Proof. intros. simpl in H.
       destruct H. easy. easy.  
Qed.

Lemma cons_conc : forall (X : Type) (x : X) (ls : list X),
    x :: ls = [x] ++ ls.
Proof. reflexivity. Qed.




Ltac matrix_compute :=
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
                                         apply Nat.sub_add in H;
                                         rewrite Nat.add_comm in H;
                                         rewrite <- H; compute; destruct_m_eq))
    | |- (?A ≡ ?B)%M => by_cell
    | |- _ => autounfold with U_db;
                  simpl;
                  autorewrite with Cexp_db C_db;
                  try (eapply c_proj_eq);
                  simpl;
                  repeat (autorewrite with R_db; field_simplify_eq; simpl);
                  try easy
    end).


Lemma WF_Unitary_implies_WF_Matrix : forall {n} (U : Square n),
    WF_Unitary U -> WF_Matrix U.
Proof. intros. unfold WF_Unitary in H. destruct H. assumption. Qed.

#[export] Hint Resolve WF_Unitary_implies_WF_Matrix : wf_db unit_db.


(* defining program application *)
Definition prog_simpl_app (prg_len : nat) (U : Square 2) (bit : nat) : Square (2^prg_len) :=
  match bit <? prg_len with
  | true => I (2^bit) ⊗ U ⊗ I (2^(prg_len - bit - 1))
  | false => I (2^prg_len)
  end.


Lemma unit_prog_simpl_app : forall (prg_len : nat) (U : Square 2) (bit : nat),
  WF_Unitary U -> WF_Unitary (prog_simpl_app prg_len U bit). 
Proof. intros.  
       unfold prog_simpl_app.
       destruct (bit <? prg_len) eqn:E; auto with unit_db.
       rewrite (easy_pow3 _ bit); try (apply Nat.ltb_lt; easy).
       auto with unit_db.
Qed.

#[export] Hint Resolve unit_prog_simpl_app : unit_db.

Lemma WF_Matrix_prog_simpl_app : forall (prg_len : nat) (U : Square 2) (bit : nat),
  WF_Matrix U -> WF_Matrix (prog_simpl_app prg_len U bit).
Proof. intros.
  unfold prog_simpl_app.
  bdestruct_all; auto with wf_db.
Qed.

#[export] Hint Resolve WF_Matrix_prog_simpl_app : wf_db.


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
       assert (H2' : (2^(n - 1)*2 = 2^n)%nat). { rewrite Nat.mul_comm. apply H2. }
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
       assert (H2' : (2^(n - 1)*2 = 2^n)%nat). { rewrite Nat.mul_comm. apply H2. }
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

#[export] Hint Resolve unit_prog_ctrl_app : unit_db.

Lemma WF_Matrix_prog_ctrl_app : forall (prg_len : nat) (U : Square 2) (ctrl targ : nat),
  WF_Matrix U -> WF_Matrix (prog_ctrl_app prg_len U ctrl targ). 
Proof. intros.
  unfold prog_ctrl_app.
  bdestruct_all; simpl; auto with wf_db;
    apply WF_kron;
    try (replace (2 ^ (targ - ctrl) + (2 ^ (targ - ctrl) + 0))
        with (2 ^ (1 + (targ - ctrl)))
        by (rewrite Nat.pow_add_r; simpl; auto);
         rewrite <- ! Nat.pow_add_r; f_equal; lia);
    auto with wf_db.
Qed.

#[export] Hint Resolve WF_Matrix_prog_ctrl_app : wf_db.


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
       do 2 rewrite Nat.div_add, Nat.Div0.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
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
       assert (H' : ((a ⊗ b .+ c ⊗ d) (k + i*2) (l + j*2) = 
                    (a' ⊗ b' .+ c' ⊗ d') (k + i*2) (l + j*2))%nat).
       rewrite H7; easy. 
       unfold kron, Mplus in H'. 
       do 2 rewrite Nat.div_add, Nat.Div0.mod_add, Nat.div_small, Nat.mod_small in H'; auto.
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


#[export] Hint Resolve WF_CZ : wf_db.


Lemma unit_CZ : WF_Unitary CZ. 
Proof. split; auto with wf_db. 
       lma'. Qed.


#[export] Hint Resolve unit_CZ : unit_db.
                

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


#[export] Hint Resolve WF_sko : wf_db.


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


Lemma Mmult_sko : forall (A B : Square 4), switch_kron_order (A × B) = 
                                      switch_kron_order A × switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mmult. 
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
Qed.


Lemma Mplus_sko : forall (A B : Square 4), switch_kron_order (A .+ B) = 
                                      switch_kron_order A .+ switch_kron_order B.
Proof. intros.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv. intros. 
       unfold switch_kron_order, Mplus. 
       do 4 (destruct i; 
             try (do 4 (destruct j; try lca); lia)).
Qed.


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


Lemma n_plus_m_zero_n_zero : forall (n m : nat), (n + m = 0 -> n = 0)%nat.
  intros n m H. induction m.
  - rewrite Nat.add_0_r in H. assumption.
  - rewrite Nat.add_comm in H. simpl in H. discriminate.
Qed.


Lemma fold_left_Mplus : forall {n m} (a b : Matrix n m) (A : list (Matrix n m)),  
    fold_left Mplus (A) (b .+ a)%M =  (fold_left Mplus A (b) .+  a)%M.
Proof. intros n m a b A.  generalize dependent a. simpl. induction A.
  - simpl. reflexivity.
  - simpl. intros a0. rewrite (Mplus_assoc _ _ b a0 a).
    rewrite (Mplus_comm _ _ a0 a).  rewrite IHA. symmetry. rewrite IHA.
    rewrite <- (Mplus_assoc _ _ _ a a0). reflexivity.
Qed.


Lemma C_inj_l : forall (c x y : C), x = y -> (c * x = c * y)%C.
Proof. intros. rewrite H. easy. Qed.


Lemma C_inv_l : forall (c x y : C), c <> C0 -> (c * x = c * y)%C -> x = y.
Proof. intros. apply C_inj_l with (c:=/c) in H0. rewrite ! Cmult_assoc in H0.
  rewrite Cinv_l in H0; try assumption. rewrite ! Cmult_1_l in H0; assumption.
Qed.


Lemma C_inj_r : forall (c x y : C), x = y -> (x * c = y * c)%C.
Proof. intros. rewrite H. easy. Qed.


Lemma C_inv_r : forall (c x y : C), c <> C0 -> (x * c = y * c)%C -> x = y.
Proof. intros. apply C_inj_r with (c:=/c) in H0. rewrite <- ! Cmult_assoc in H0.
  rewrite Cinv_r in H0; try assumption. rewrite ! Cmult_1_r in H0; assumption.
Qed.


Lemma Mmult_eq_l : forall {m n o : nat} (A A' : Matrix m n) (B : Matrix n o), A = A' -> A × B = A' × B.
Proof. intros. rewrite H. easy. Qed.


Lemma Mmult_eq_r : forall {m n o : nat} (A : Matrix m n) (B B' : Matrix n o), B = B' -> A × B = A × B'.
Proof. intros. rewrite H. easy. Qed.


Lemma Mscale_inj : forall {m n} (A B : Matrix m n) (c : C), A = B -> (c .* A = c .* B)%M.
Proof. intros m n A B c H. rewrite H. easy. Qed. 


Lemma Mscale_cancel : forall {m n} (A B : Matrix m n) (c : C), c <> C0 -> (c .* A = c .* B)%M ->  A = B.
Proof. intros m n A B c H H0. apply Mscale_inj with (c:= /c) in H0.
  rewrite ! Mscale_assoc in H0. rewrite Cinv_l in H0; try easy.
  rewrite ! Mscale_1_l in H0. easy.
Qed.


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
    


Lemma big_kron_adj : forall {n} (l : list (Square n)), (⨂ l)† = (⨂ (map adjoint l)).
Proof. intros n l. induction l; simpl. lma'. rewrite kron_adjoint. rewrite IHl. rewrite ! map_length. reflexivity. Qed.


Lemma unitary_hermitian_anticommute_hermitian : forall {n} (A B : Square n), WF_Unitary A -> WF_Unitary B -> A † = A -> B † = B -> (A × B = -C1 .* (B × A))%M -> (((C1/√2) .* (A .+ B)) † = ((C1/√2) .* (A .+ B)))%M.
Proof. intros n A B UA UB HA HB AC. 
    rewrite Mscale_adj.
    replace ((C1 / √ 2) ^* )%C with (C1 / √ 2)%C by lca.
    rewrite Mplus_adjoint.
    rewrite HA, HB.
    reflexivity.
Qed.


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


Lemma fold_left_Mplus_app_Zero : forall {n m : nat} (A B : list (Matrix n m)),
    fold_left Mplus (A++B) Zero%M = ((fold_left Mplus A Zero) .+ (fold_left Mplus B Zero))%M.
Proof. intros n m A B. induction A.
  - simpl. rewrite Mplus_0_l. reflexivity.
  - simpl. rewrite 2 fold_left_Mplus. rewrite IHA.
    symmetry. do 2 (rewrite Mplus_assoc; rewrite Mplus_comm).
    assert (fold_left Mplus B Zero .+ fold_left Mplus A Zero = fold_left Mplus A Zero .+ fold_left Mplus B Zero)%M. { rewrite Mplus_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.


Lemma Zero_kron : forall {m n o p} (a : Matrix m n) (b : Matrix (m * o) (n * p)),
    ((@Zero (m * o) (n * p)) .+ b = a ⊗ (@Zero o p) .+ b)%M.
Proof. intros m n o p a b. lma. Qed. 


Lemma ite_conv : forall {X : Type} (x1 x2 : X), (if true && true then x1 else x2) = x1.
Proof. easy. Qed.


Lemma kron_simplify : forall (n m o p : nat) (a b : Matrix n m) (c d : Matrix o p), 
    a = b -> c = d -> a ⊗ c = b ⊗ d.
Proof. intros n m o p a b c d H H0.
       rewrite H, H0.
       easy.
Qed.


(** B invertible -> 
     A * B = C * B -> A = C ***)
Lemma Minvert_r {n : nat} (A B C : Square n) :
  WF_Matrix A -> WF_Matrix C ->
  invertible B -> A × B = C × B ->  A = C.
Proof. intros WFA WFC H H0.
       destruct H as [B' [WFB' invB']]. inversion invB'.
       assert ( A × B × B' = C × B × B' ).
       { rewrite H0. easy. }
       rewrite ! Mmult_assoc in H2.
       rewrite ! H in H2.
       rewrite ! Mmult_1_r in H2; assumption.
Qed.

(** B invertible -> A * B = B -> A = Id ***) (* results from the above *)

(** unitary -> invertible ***) (* obvious *)

Lemma Mmult_r {n : nat} (A B C : Square n) :
  WF_Matrix A -> WF_Matrix C ->
  WF_Matrix B -> A = C -> A × B = C × B.
Proof. intros H H0 H1 H2. rewrite H2. reflexivity. Qed. 

Lemma Cmult_r (a b c : C) : a = b -> (a * c = b * c)%C.
Proof. intros H. rewrite H. easy. Qed.

Lemma Cmult_l (a b c : C) : a = b -> (c * a = c * b)%C.
Proof. intros H. rewrite H. easy. Qed.


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
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }
  assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }


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
  assert (R3': (o * w + y) mod o = y). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }
  assert (R4': (p * x + z) mod p = z). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }
  
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
      all: assumption.
Qed.


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


Lemma tensor_swap {n m o p : nat} (A D : Matrix n m) (B E : Matrix o p) :
  WF_Matrix A -> WF_Matrix B -> WF_Matrix D -> WF_Matrix E ->
  A ⊗ B = D ⊗ E -> B ⊗ A = E ⊗ D.
Proof. intros.
       assert ({A ⊗ B = Zero} + {A ⊗ B <> Zero}). { apply Mat_eq_dec; auto with wf_db. }
       destruct H4.
       - assert (A = Zero \/ B = Zero).
         {
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
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }
    assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }

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
  assert (R3: (o * i + k) mod o = k). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }
    assert (R4: (p * j + l) mod p = l). { rewrite Nat.add_comm. rewrite Nat.mul_comm. rewrite Nat.Div0.mod_add. rewrite Nat.mod_small. reflexivity. assumption. }

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

Lemma pow_inv : forall (a b c : nat), b = c -> a^b = a^c.
Proof. intros a b c H. rewrite H. easy. Qed.

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

Lemma kron_unitary3' : forall {m n o} (A : Matrix m m) (B : Matrix n n) (C : Matrix o o),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary C ->  (A ⊗ B ⊗ C) † × (A ⊗ B ⊗ C) =
  Matrix.I (m * n * o) .
Proof.
  intros m n o A B C WFUA WFUB WFUC.
  apply (kron_unitary3 _ _ _ WFUA WFUB WFUC).
Qed.

Lemma cnot_unitary' : forall (n : nat),
    0 < n ->
    WF_Unitary(∣0⟩⟨0∣ ⊗ Matrix.I (2 ^ (n))
                     .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ (n - 1)) ⊗ σx)%M.
Proof. intros n H.
       apply unit_proj; auto with unit_db. lia.
Qed.

Lemma notc_unitary' : forall (n : nat),
    0 < n ->
    WF_Unitary
    (Matrix.I (2 ^ n) ⊗ ∣0⟩⟨0∣
                              .+ σx ⊗ Matrix.I (2 ^ (n - 1)) ⊗ ∣1⟩⟨1∣)%M.
Proof. intros n H.
       apply unit_proj2; auto with unit_db. lia.
Qed.

Lemma matrix_equality_implies_element_equality :
  forall {m n} {A B : Matrix m n} (o p : nat),
    A = B -> A o p = B o p.
Proof. intros m n A B o p H. rewrite H. easy. Qed. 

Ltac mydo1 tac x y H :=
  match x with
  | O => idtac
  | S ?n => (tac n y H) ; (mydo1 tac n y H)
  end.

Ltac mydo2 tac x y H :=
  match y with
  | O => idtac
  | S ?n => (mydo1 tac x n H) ; (mydo2 tac x n H)
  end.

Ltac specialize_destruct_matrix_equality m n H :=
  let ceq := fresh "ceq" in
  specialize (matrix_equality_implies_element_equality m n H) as ceq;
  inversion ceq.

Ltac extract_linear_system H :=
  match type of H with
  | ?A = ?B =>
      match type of A with
      | Matrix ?m ?n => mydo2 specialize_destruct_matrix_equality m n H;
                        autorewrite with R_db in *;
                        subst
      end
  end.

Ltac extract_linear_systems :=
  repeat match goal with
    | [H : ?A = ?B |- _] =>
        match type of A with
        | Matrix ?m ?n => extract_linear_system H; clear H
        end
    end.

Ltac contradict_matrix_equality H :=
  repeat match goal with
  | [NZ: ?c <> C0 |- _] => apply C0_imp in NZ
  end;
  try (exfalso;
       extract_linear_system H;
       lra).

Ltac contradict_matrix_equalities :=
  repeat match goal with
  | [NZ: ?c <> C0 |- _] => apply C0_imp in NZ
  end;
  try (exfalso;
       extract_linear_systems;
       lra).


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




(************************)
(* Misc Helper Lemmas *)
(************************)

Local Open Scope C_scope.


Lemma Ropp_R0 : (- R0)%R = R0. Proof. lra. Qed.

Lemma Ropp_mult_twice : (-R1 * -R1)%R = R1. Proof. lra. Qed.

Ltac Rsimpl :=
repeat
  match goal with
  | _ => rewrite Rmult_0_l
  | _ => rewrite Rmult_0_r
  | _ => rewrite Rplus_0_l
  | _ => rewrite Rplus_0_r
  | _ => rewrite Rmult_1_l
  | _ => rewrite Rmult_1_r
  | _ => rewrite Ropp_0
  | _ => rewrite Ropp_involutive
  | _ => rewrite Ropp_R0
  | _ => rewrite Ropp_mult_twice
  | _ => rewrite Ropp_mult_distr_l
  | _ => rewrite Ropp_mult_distr_r
  end.

Ltac Rsimpl_context H :=
repeat
  match goal with
  | _ => rewrite Rmult_0_l in H
  | _ => rewrite Rmult_0_r in H
  | _ => rewrite Rplus_0_l in H
  | _ => rewrite Rplus_0_r in H
  | _ => rewrite Rmult_1_l in H
  | _ => rewrite Rmult_1_r in H
  | _ => rewrite Ropp_0 in H
  | _ => rewrite Ropp_involutive in H
  | _ => rewrite Ropp_R0 in H
  | _ => rewrite Ropp_mult_twice in H
  | _ => rewrite Ropp_mult_distr_l in H
  | _ => rewrite Ropp_mult_distr_r in H
  end.

Ltac Csimpl_context H :=
  repeat
   match goal with
   | _ => rewrite Cmult_0_l in H
   | _ => rewrite Cmult_0_r in H
   | _ => rewrite Cplus_0_l in H
   | _ => rewrite Cplus_0_r in H
   | _ => rewrite Cmult_1_l in H
   | _ => rewrite Cmult_1_r in H
   | _ => rewrite Cconj_R in H
   end.

Lemma fold_right_app_nil_app : forall {A : Type} (l1 l2 : list (list A)),
    fold_right (@app A) [] (l1 ++ l2) = 
      (fold_right (@app A) [] l1) ++ (fold_right (@app A) [] l2).
Proof. intros A l1 l2.
  induction l1; auto.
  simpl. rewrite <- app_assoc. 
  f_equal. auto.
Qed.

Lemma fold_right_app_nil_map : forall {A B : Type} (l : list (list A)) (f : A -> B),
    fold_right (app (A:=B)) [] (map (map f) l) = map f (fold_right (app (A:=A)) [] l).
Proof. intros A B l f.
  induction l; auto; simpl.
  rewrite map_app. f_equal. auto.
Qed.

Lemma WF_Matrix_fold_right_Mmult_I : forall {n : nat} (LM : list (Square n)),
    Forall WF_Matrix LM ->
    WF_Matrix (fold_right Mmult (I n) LM).
Proof. intros n LM H.
  induction LM; simpl.
  - auto with wf_db.
  - rewrite Forall_cons_iff in H. destruct H. 
    apply WF_mult; auto.
Qed.

Lemma fold_right_Mmult_I_app : forall {n : nat} {LM1 LM2 : list (Square n)},
    Forall WF_Matrix LM2 ->
    fold_right Mmult (I n) (LM1 ++ LM2) = 
      fold_right Mmult (I n) LM1 × fold_right Mmult (I n) LM2.
Proof. intros n LM1 LM2 H.
  induction LM1.
  - simpl. rewrite Mmult_1_l; auto.
    apply WF_Matrix_fold_right_Mmult_I; auto.
  - simpl. rewrite Mmult_assoc. f_equal. auto.
Qed.

Lemma fold_right_add_0_app : forall {Ln1 Ln2 : list nat},
fold_right Init.Nat.add 0%nat (Ln1 ++ Ln2) =
  (fold_right Init.Nat.add 0%nat Ln1 + fold_right Init.Nat.add 0%nat Ln2)%nat.
Proof. intros Ln1 Ln2.
  induction Ln1; auto.
  simpl. rewrite <- Nat.add_assoc. f_equal. auto.
Qed.


Lemma fold_right_Mplus_Zero_app : forall {m n : nat} (Lm1 Lm2 : list (Matrix m n)),
    fold_right Mplus Zero (Lm1 ++ Lm2) = 
      (fold_right Mplus Zero Lm1) .+ (fold_right Mplus Zero Lm2).
Proof. intros m n Lm1 Lm2.
  induction Lm1; simpl.
  - rewrite Mplus_0_l. auto.
  - rewrite Mplus_assoc. f_equal. auto.
Qed.

Lemma fold_right_Mplus_Zero_map_Mmult_distr : 
  forall {m n o : nat} (M : Matrix m n) (Lm : list (Matrix n o)),
  fold_right Mplus Zero (map (fun m => M × m) Lm) = M × fold_right Mplus Zero Lm.
Proof. intros m n o M Lm.
  induction Lm; simpl.
  - rewrite Mmult_0_r. auto.
  - distribute_plus. f_equal. auto.
Qed.

Lemma firstn_last_nth_app : forall {A : Type} (k : nat) (d : A) (ls : list A),
    (k < length ls)%nat ->
    firstn k ls ++ [nth k ls d] = firstn (S k) ls.
Proof. intros A k d ls H.
  gen k. induction ls; intros. simpl in *. lia.
  simpl in *. destruct k. simpl. auto.
  simpl. f_equal. apply IHls. lia.
Qed. 

Lemma map_fst_combine : forall {A B : Type} (La : list A) (Lb : list B),
   length La = length Lb -> map fst (combine La Lb) = La.
Proof. intros A B La Lb H.
  gen Lb. induction La; intros; auto.
  destruct Lb; try discriminate.
  simpl in *. apply Nat.succ_inj in H.
  f_equal. apply IHLa; auto.
Qed.
  
Lemma map_snd_combine : forall {A B : Type} (La : list A) (Lb : list B),
   length La = length Lb -> map snd (combine La Lb) = Lb.
Proof. intros A B La Lb H.
  gen La. induction Lb; intros. 
  - rewrite combine_nil; auto.
  - destruct La; try discriminate.
    simpl in *. apply Nat.succ_inj in H.
    f_equal. apply IHLb; auto.
Qed.

Lemma combine_app : forall {A B : Type} (La1 La2 : list A) (Lb1 Lb2 : list B),
    length La1 = length Lb1 ->
    combine (La1 ++ La2) (Lb1 ++ Lb2) = (combine La1 Lb1) ++ (combine La2 Lb2).
Proof. intros A B La1 La2 Lb1 Lb2 H.
  gen La2 Lb1 Lb2. induction La1; intros.
  - destruct Lb1; try discriminate. auto.
  - destruct Lb1; try discriminate. simpl in *.
    apply Nat.succ_inj in H.
    f_equal. apply IHLa1; auto.
Qed.

Lemma combine_cons : forall {A B : Type} (La : list A) (Lb : list B) (a : A) (b : B),
    combine (a :: La) (b :: Lb) = (a, b) :: (combine La Lb).
Proof. intros A B La Lb a b. auto. Qed.

Lemma combine_map_list_app (X Y Z: Type) (f : X -> Y) (g : X -> Z) (l1 l2 : list X) :
  (combine
     (map (fun x => f x) (l1 ++ l2))
     (map (fun x => g x) (l1 ++ l2))) =
    (combine
     (map (fun x => f x) (l1))
     (map (fun x => g x) (l1))) ++
      (combine
         (map (fun x => f x) (l2))
         (map (fun x => g x) (l2))).
Proof. intros. induction l1; try easy.
  simpl. rewrite IHl1. easy.
Qed.

Lemma switch_switch_overshadow : forall {X : Type} (n : nat) (ls : list X) (a b : X),
    switch (switch ls a n) b n = switch ls b n.
Proof. intros X n ls a b.
  gen ls a b.
  induction n; intros; destruct ls; auto.
  simpl. f_equal. auto.
Qed.

Lemma list_coord_map_destruct : forall {A B : Type} (l1 l2 : list (A * B)),
    map fst l1 = map fst l2 -> map snd l1 = map snd l2 -> l1 = l2.
Proof. intros A B l1 l2 H H0.
  rewrite <- map_id.
  rewrite <- map_id at 1.
  assert ((fun x : A * B => x) = (fun x : A * B => (fst x, snd x))).
  { apply functional_extensionality. intros x. destruct x. auto. }
  rewrite ! H1.
  clear H1.
  gen l2.
  induction l1; intros.
  - simpl in *. symmetry in H, H0.
    apply map_eq_nil in H, H0.
    subst. auto.
  - destruct l2 as [ | b l2].
    + simpl in *.
      inversion H.
    + simpl in *.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      specialize (IHl1 l2 H3 H4).
      rewrite IHl1. auto.
Qed.

Lemma nonzero_mat_nonzero_elem : forall {n m : nat} (M : Matrix n m),
    WF_Matrix M -> (M <> Zero <-> (exists i j, (i < n)%nat /\ (j < m)%nat /\ M i j <> C0)).
Proof. intros n m M H.
  split; intros.
  - destruct (Classical_Prop.classic (exists i j : nat, (i < n)%nat /\ (j < m)%nat /\ M i j <> C0)); auto. 
    contradict H0.
    prep_matrix_equality.
    apply Classical_Pred_Type.not_ex_all_not with (n := x) in H1.
    apply Classical_Pred_Type.not_ex_all_not with (n := y) in H1.
    apply Classical_Prop.not_and_or in H1.
    destruct H1.
    + assert ((x >= n)%nat \/ (y >= m)%nat) by lia.
      apply H in H1.
      assumption.
    + apply Classical_Prop.not_and_or in H0.
      destruct H0.
      * assert ((x >= n)%nat \/ (y >= m)%nat) by lia.
        apply H in H1.
        assumption.
      * apply Classical_Prop.NNPP in H0.
        assumption.
  - destruct H0 as [i [j [H0 [H1 H2]]]].
    bdestruct (i <? n); bdestruct (j <? m); 
      try (assert (H' : (i >= n)%nat \/ (j >= m)%nat) by lia;
           apply H in H'; contradiction).
    intro.
    rewrite H5 in H2.
    contradiction.
Qed.

Lemma kron_breakdown3 : forall (a a' b b' c c' : Square 2),
  WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' -> WF_Matrix c -> WF_Matrix c' ->
  a ⊗ b ⊗ c = a' ⊗ b' ⊗ c' -> 
  (forall i j k l m n : nat, ((a i j) * (b k l) * (c m n) = (a' i j) * (b' k l) * (c' m n))%C).
Proof. intros a a' b b' c c' H H0 H1 H2 H3 H4 H5 i j k l m n. 
  bdestruct (i <? 2); bdestruct (j <? 2); 
    bdestruct (k <? 2); bdestruct (l <? 2);
    bdestruct (m <? 2); bdestruct (n <? 2);
    try (rewrite H, H0; try (left; easy); try (right; easy); lca);
    try (rewrite H1, H2; try (left; easy); try (right; easy); lca);
    try (rewrite H3, H4; try (left; easy); try (right; easy); lca).
  assert (H' : ((a ⊗ b ⊗ c) (m + (k + i*2)*2) (n + (l + j*2)*2) = (a' ⊗ b' ⊗ c') (m + (k + i*2)*2) (n + (l + j*2)*2))%nat).
  rewrite H5; easy. 
  unfold kron in H'. 
  assert (H_0 : ((m + (k + i * 2) * 2) / 2 = m / 2 + (k + i * 2))%nat) by (rewrite Nat.div_add; auto).
  assert (H_1 : ((n + (l + j * 2) * 2) / 2 = n / 2 + (l + j * 2))%nat) by (rewrite Nat.div_add; auto).
  rewrite ! Nat.Div0.mod_add, ! H_0, ! H_1 in H'.
  assert (H_2 : ((m / 2 + (k + i * 2)) = ((m / 2 + k) + i * 2))%nat) by lia.
  assert (H_3 : ((n / 2 + (l + j * 2)) = ((n / 2 + l) + j * 2))%nat) by lia.
  rewrite ! H_2, ! H_3 in H'. 
  rewrite ! Nat.div_add, ! Nat.Div0.mod_add in H'; auto.
  rewrite ! Nat.div_small in H'; try rewrite ! Nat.div_small; try lia.
  rewrite ! Nat.mod_small in H'; auto.
Qed.

Lemma kron_rearrange3 : forall (a a' b b' C C' : Square 2),
    WF_Matrix a -> WF_Matrix a' -> WF_Matrix b -> WF_Matrix b' ->
    WF_Matrix C -> C <> Zero ->
    a ⊗ C ⊗ b = a' ⊗ C' ⊗ b' -> C = C' ->
    a ⊗ b = a' ⊗ b'.
Proof. intros; subst.
  prep_matrix_equality. 
  rewrite (nonzero_mat_nonzero_elem C' H3) in H4.
  destruct H4 as [i [j [H6 [H7 H4]]]].
  unfold kron.
  apply Cmult_cancel_r with (a := C' i j); auto.
  setoid_rewrite <- Cmult_assoc.
  setoid_rewrite Cmult_comm at 2.
  setoid_rewrite Cmult_comm at 4.
  setoid_rewrite Cmult_assoc.
  apply kron_breakdown3; auto.
Qed.

Lemma eq_implies_JMeq : forall (A : Type) (x y : A), 
    x = y -> JMeq x y.
Proof. intros A x y H. rewrite H. reflexivity. Qed.

Lemma eq_eq_dep : forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
  x = y -> EqdepFacts.eq_dep U P p x p y.
Proof. intros. apply JMeq_eq_dep; auto. 
  apply eq_implies_JMeq; auto. 
Qed.

Lemma filter_orth_app_permutation : forall A l f,
    Permutation l ((filter f l) ++ (filter (fun (x : A) => negb (f x)) l)).
Proof. intros. gen l.
  induction l; try easy.
  simpl. destruct (f a); simpl.
  - constructor. easy.
  - assert (Permutation ((a :: filter (fun x : A => negb (f x)) l) ++ filter f l) (filter f l ++ a :: filter (fun x : A => negb (f x)) l)).
    { apply Permutation_app_comm. }
    apply perm_trans with (l' := ((a :: filter (fun x : A => ¬ f x) l) ++ filter f l)); try easy.
    simpl. constructor.
    assert (Permutation (filter f l ++ filter (fun x : A => ¬ f x) l) (filter (fun x : A => ¬ f x) l ++ filter f l)). 
    { apply perm_trans with (l' := (filter f l ++ filter (fun x : A => ¬ f x) l)); try easy.
      apply Permutation_app_comm. }
    apply perm_trans with (l' := (filter f l ++ filter (fun x : A => ¬ f x) l)); easy.
Qed.

Lemma filter_orth_length : forall A l f, (length l = length (filter f l) + length (filter (fun (x : A) => negb (f x)) l))%nat.
Proof. intros.
  assert (Permutation l ((filter f l) ++ (filter (fun (x : A) => negb (f x)) l))).
  { apply (filter_orth_app_permutation A l f). }
  apply Permutation_length in H.
  rewrite app_length in H.
  easy.
Qed.

Lemma get_vec_vec : forall {n} (v : Vector n),
  WF_Matrix v -> get_vec 0 v = v.
Proof. intros. 
       unfold get_vec.
       prep_matrix_equality. 
       bdestruct (y =? 0). 
       - rewrite H0; easy.
       - unfold WF_Matrix in H.  
         rewrite H; try easy.
         right. 
         bdestruct (y <? 1); try lia.          
Qed.

Lemma Cmult_neg1_mult : ((-C1 * -C1)%C = C1). Proof. lca. Qed.
 
Lemma Copp_opp : forall (a b : C), -a = b <-> a = -b. Proof. split; intros; [rewrite <- H | rewrite H]; lca. Qed. 

Lemma Cplus_opp_r : forall c : C, c + - c = C0. Proof. intros; lca. Qed.

Lemma Cplus_inj_r : forall (c : C) {c1 c2 : C},
    c1 = c2 -> c1 + c = c2 + c.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Cplus_inj_l : forall (c : C) {c1 c2 : C},
    c1 = c2 -> c + c1 = c + c2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Cplus_inv_r : forall (c c1 c2 : C),
    c1 + c = c2 + c -> c1 = c2.
Proof. intros. apply Cplus_inj_r with (c:=-c) in H.
  rewrite <- ! Cplus_assoc in H.
  rewrite ! Cplus_opp_r in H.
  rewrite ! Cplus_0_r in H.
  assumption.
Qed.

Lemma Cplus_inv_l : forall (c c1 c2 : C),
    c + c1= c + c2 -> c1 = c2.
Proof. intros. apply Cplus_inj_l with (c:=-c) in H.
  rewrite ! Cplus_assoc in H.
  rewrite ! Cplus_opp_l in H.
  rewrite ! Cplus_0_l in H.
  assumption.
Qed.

Lemma Cplus_zero_iff_equals_minus : forall (c1 c2 : C),
    c1 + c2 = C0 <-> c1 = -c2.
Proof. split.
  - intro. apply Cplus_inj_r with (c := -c2) in H.
    rewrite <- ! Cplus_assoc in H.
    rewrite Cplus_opp_r in H.
    rewrite Cplus_0_l, Cplus_0_r in H.
    assumption.
  - intro. rewrite H. rewrite Cplus_opp_l. reflexivity.
Qed.

Lemma adjoint_inj : forall {j k : nat} (A B : Matrix j k),
    A = B -> A † = B †.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mmult_inj_l : forall {i j k : nat} (m : Matrix i j) {m1 m2 : Matrix j k},
    m1 = m2 -> m × m1 = m × m2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mmult_inj_r : forall {i j k : nat} (m : Matrix j k) {m1 m2 : Matrix i j},
    m1 = m2 -> m1 × m = m2 × m.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma WF_Unitary_implies_invertible : forall {n : nat} (M : Square n),
    WF_Unitary M -> invertible M.
Proof. intros. unfold WF_Unitary in H. destruct H. unfold invertible.
  exists M †. unfold Minv. split; auto with wf_db. 
  split; auto; rewrite Minv_flip; auto with wf_db. 
Qed.

#[export] Hint Resolve WF_Unitary_implies_invertible : unit_db.

Lemma Mmult_inj_square_inv_l : forall {n m : nat} (M : Square n) (M1 M2 : Matrix n m),
    invertible M -> WF_Matrix M1 -> WF_Matrix M2 -> M × M1 = M × M2 -> M1 = M2.
Proof. intros. unfold invertible in H. destruct H as [M' [H3 [H4 H5]]].
  apply @Mmult_inj_l with (i := n) (m := M') in H2.
  rewrite <- ! Mmult_assoc in H2.
  rewrite ! H5 in H2.
  rewrite ! Mmult_1_l in H2.
  all : trivial.
Qed.

Lemma Mmult_inj_square_inv_r : forall {n m} (M : Square n) (M1 M2 : Matrix m n),
    invertible M -> WF_Matrix M1 -> WF_Matrix M2 -> M1 × M = M2 × M -> M1 = M2.
Proof. intros. unfold invertible in H. destruct H as [M' [H3 [H4 H5]]].
  apply @Mmult_inj_r with (k := n) (m := M') in H2.
  rewrite ! Mmult_assoc in H2.
  rewrite ! H4 in H2.
  rewrite ! Mmult_1_r in H2.
  all : trivial.
Qed.

Lemma Mmult_double_side : forall {i j k : nat} {m1 m1' : Matrix i j} {m2 m2' : Matrix j k} ,
    m1 = m1' -> m2 = m2' -> m1 × m2 = m1' × m2'.
Proof. intros. rewrite H, H0. reflexivity. Qed.

Lemma Mplus_inj_l : forall {j k : nat} (m m1 m2 : Matrix j k),
    m1 = m2 -> m .+ m1 = m .+ m2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mplus_inj_r : forall {j k : nat} (m m1 m2 : Matrix j k),
    m1 = m2 -> m1 .+ m = m2 .+ m.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mplus_double_side : forall {j k : nat} {m1 m1' m2 m2' : Matrix j k} ,
    m1 = m1' -> m2 = m2' -> m1 .+ m2 = m1' .+ m2'.
Proof. intros. rewrite H, H0. reflexivity. Qed.

Lemma Mplus_opp_r : forall {j k : nat} (m : Matrix j k),
    WF_Matrix m -> m .+ - C1 .* m = Zero.
Proof. intros. lma'. Qed.

Lemma Mplus_opp_l : forall {j k : nat} (m : Matrix j k),
    WF_Matrix m -> - C1 .* m .+ m = Zero.
Proof. intros. lma'. Qed.

Lemma Mplus_inv_r : forall {j k : nat} (m m1 m2 : Matrix j k),
    WF_Matrix m -> m1 .+ m = m2 .+ m -> m1 = m2.
Proof. intros. apply Mplus_inj_r with (m := -C1.*m) in H0.
  rewrite ! Mplus_assoc in H0.
  rewrite ! Mplus_opp_r in H0; auto.
  rewrite ! Mplus_0_r in H0.
  assumption.
Qed. 

Lemma Mplus_inv_l : forall {j k : nat} (m m1 m2 : Matrix j k),
    WF_Matrix m -> m .+ m1 = m .+ m2 -> m1 = m2.
Proof. intros. apply Mplus_inj_l with (m := -C1.*m) in H0.
  rewrite <- ! Mplus_assoc in H0.
  rewrite ! Mplus_opp_l in H0; auto.
  rewrite ! Mplus_0_l in H0.
  assumption.
Qed. 

Lemma Mplus_zero_iff_equals_minus : forall {j k : nat} (m1 m2 : Matrix j k),
    WF_Matrix m2 -> (m1 .+ m2 = Zero <-> m1 = -C1 .* m2).
Proof. intros. split.
  - intro. apply Mplus_inj_r with (m := -C1 .* m2) in H0.
    rewrite Mplus_assoc in H0.
    rewrite Mplus_opp_r in H0; auto.
    rewrite Mplus_0_l, Mplus_0_r in H0.
    assumption.
  - intro. rewrite H0. lma'.
Qed.


Lemma trace_kron_dist : forall n m (A : Square n) (B : Square m),
    m <> 0%nat -> trace (A ⊗ B) = ((trace A) * (trace B))%G.
Proof.
  intros.
  unfold trace, kron.
  rewrite big_sum_product; auto.
Qed.


Lemma In_list_WF_Matrix_implies_WF_big_kron : forall {m n} (A : list (Matrix m n)),
    (forall a, In a A -> WF_Matrix a) -> WF_Matrix (⨂ A).
Proof. intros. induction A.
  - auto with wf_db.
  - simpl.
    apply WF_kron; auto.
    specialize (H a). assert (In a (a :: A)). { simpl. left. reflexivity. }
    apply H in H0. assumption.
    apply IHA. intros.
    specialize (H a0). assert (In a0 (a :: A)). {simpl. right. assumption. }
    apply H in H1. assumption.
Qed.

Lemma big_kron_split : forall {m n} (A B : list (Matrix m n)),
    (forall a, In a A -> WF_Matrix a) -> (forall b, In b B -> WF_Matrix b) -> 
    (⨂ (A ++ B)) = (⨂ A) ⊗ (⨂ B).
Proof. intros. induction A.
  - simpl. rewrite kron_1_l. easy.
    induction B.
    + simpl. auto with wf_db.
    + simpl. apply WF_kron; try easy.
      specialize (H0 a). assert (In a (a :: B)). { simpl. left. reflexivity. }
      apply H0 in H1. assumption.
      apply IHB. intros.
      specialize (H0 b). assert (In b (a :: B)). { simpl. right. assumption. }
      apply H0 in H2. assumption.
  - simpl. rewrite IHA. rewrite kron_assoc.
    rewrite ! app_length.
    assert ((Init.Nat.mul (Nat.pow m (@length (Matrix m n) A))
               (Nat.pow m (@length (Matrix m n) B))) =
              (Nat.pow m (Init.Nat.add (@length (Matrix m n) A) (@length (Matrix m n) B)))).
    { rewrite Nat.pow_add_r. reflexivity. }
    assert ((Init.Nat.mul (Nat.pow n (@length (Matrix m n) A))
               (Nat.pow n (@length (Matrix m n) B))) =
              (Nat.pow n (Init.Nat.add (@length (Matrix m n) A) (@length (Matrix m n) B)))).
    { rewrite Nat.pow_add_r. reflexivity. }
    rewrite ! H1, ! H2.
    reflexivity.
    specialize (H a). assert (In a (a :: A)). { simpl. left. reflexivity. }
    apply H in H1. assumption.
    assert  (forall a, In a A -> WF_Matrix a).
    { intros. specialize (H a0). assert (In a0 (a :: A)).
      { simpl. right. assumption. }
      apply H in H2. assumption. }
    apply In_list_WF_Matrix_implies_WF_big_kron in H1.
    assumption.
    apply In_list_WF_Matrix_implies_WF_big_kron in H0.
    assumption.
    intros. specialize (H a0). assert (In a0 (a :: A)).
    { simpl. right. assumption. }
    apply H in H2. assumption.
Qed.

Lemma linearly_independent_dimensions : forall {n m : nat} (A : Matrix n m),
    WF_Matrix A -> linearly_independent A -> (m <= n)%nat.
Proof. intros n m A H H0. 
  bdestruct (n <? m)%nat; auto.
  contradict H0.
  apply lindep_implies_not_linindep.
  apply gt_dim_lindep; auto.
Qed.

Lemma seq_inc : forall (a k : nat),
    (0 <= a < k)%nat -> seq 0 k = seq 0 a ++ [a] ++ seq (S a) (k - (S a)).
Proof. intros a k H.
  replace [a] with (seq a 1) by auto.
  rewrite app_assoc.
  rewrite <- seq_app.
  replace (a + 1)%nat with (S a) by lia.
  rewrite <- seq_app.
  replace (S a + (k - S a))%nat with k by lia.
  auto.
Qed.

Fixpoint removeKfromList (K ls : list nat) : list nat :=
  match K with
  | [] => ls
  | h :: t => removeKfromList t (remove Nat.eq_dec h ls)
  end.

Ltac minmax_breakdown :=
  repeat match goal with
    | |- context [Nat.min ?n ?m] =>
        try replace (Nat.min n m) with n by lia;
        try replace (Nat.min n m) with m by lia
    | |- context [Nat.max ?n ?m] =>
        try replace (Nat.max n m) with n by lia;
        try replace (Nat.max n m) with m by lia
    end.

Ltac minmax_breakdown_context :=
  repeat match goal with
    | [H : context [Nat.min ?n ?m] |- _] =>
        try replace (Nat.min n m) with n in H by lia;
        try replace (Nat.min n m) with m in H by lia
    | [H : context [Nat.max ?n ?m] |- _] =>
        try replace (Nat.max n m) with n in H by lia;
        try replace (Nat.max n m) with m in H by lia
    end.



Module my_H.
  Definition H := I.
End my_H.

Import my_H.

(* denote successor as s instead of S since it overlaps with the S gate *)
Local Notation s := Datatypes.S.




Definition Ceqb (c1 c2 : C) : bool :=
  if Ceq_dec c1 c2 then true else false.

Example test : Ceqb C1 C1 = true.
Proof. unfold Ceqb. destruct (Ceq_dec C1 C1).
  easy. contradiction.
Qed.

Lemma Ceqb_eq : forall c1 c2, c1 = c2 <-> Ceqb c1 c2 = true.
Proof. intros.
  unfold Ceqb.
  destruct (Ceq_dec c1 c2); auto with *.
Qed.

Infix "=?" := Ceqb.

Lemma fold_left_Cplus : forall (c : C) (l : list C),
    fold_left Cplus l (C0 + c) = c + (fold_left Cplus l C0).
Proof. intros c l. gen c.
  induction l.
  - intros. simpl. lca.
  - intros. simpl.
    rewrite <- Cplus_assoc.
    rewrite ! IHl.
    rewrite Cplus_assoc.
    easy.
Qed.

Lemma fold_left_Cplus_app : forall (l1 l2 : list C),
    fold_left Cplus (l1 ++ l2) C0 = (fold_left Cplus l1 C0) + (fold_left Cplus l2 C0).
Proof. intros. induction l1.
  - simpl. rewrite Cplus_0_l. easy.
  - simpl. rewrite ! fold_left_Cplus.
    rewrite IHl1. rewrite Cplus_assoc.
    easy.
Qed.

Lemma list_seq_decompose : forall (n1 n2 m : nat),
    List.seq m (n1 + n2)%nat = List.seq m n1 ++ List.seq (n1 + m) n2.
Proof. intros. gen m n2. induction n1; try easy.
  intros. simpl. f_equal. rewrite IHn1. rewrite <- plus_n_Sm. easy.
Qed.

Lemma seq_matrix_filter_orth_app_permutation : forall n a (A : Square n),
    Permutation (List.seq 0 n)
      ((filter (fun x : nat => A x x =? a) (List.seq 0 n)) ++
         (filter (fun x : nat => negb (A x x =? a)) (List.seq 0 n))).
Proof. intros. apply filter_orth_app_permutation. Qed.

Lemma Clist_disjoint2_is_orth : forall l a b,
  (forall c : C, In c l -> (c=a \/ c=b)) -> (a <> b) ->
  (filter (fun x:C => Ceqb x b) l = filter (fun x:C => (negb (Ceqb x a))) l).
Proof. intros.
  induction l; try easy.
  assert (forall c : C, In c l -> c = a \/ c = b).
  { intros.
    assert (In c (a0 :: l)).
    { simpl. right. easy. }
    specialize (H0 c H3).
    easy. }
  specialize (IHl H2).
  assert (In a0 (a0 :: l)).
  { simpl. left. easy. }
  specialize (H0 a0 H3).
  simpl.
  destruct H0; rewrite H0.
  - unfold Ceqb.
    destruct (Ceq_dec a b);
      destruct (Ceq_dec a a);
      try contradiction.
    simpl. easy.
  - unfold Ceqb.
    destruct (Ceq_dec b b);
      destruct (Ceq_dec b a);
      try contradiction.
    symmetry in e0.
    contradiction.
    simpl.
    f_equal.
    easy.
Qed.

Lemma filter_Cdisjoint2_length : forall (a b : C) (l : list C),
    (forall c : C, In c l -> (c=a \/ c=b)) -> (a <> b) ->
    (length l = length (filter (fun x:C => Ceqb x a) l) + length (filter (fun x:C => Ceqb x b) l))%nat.
Proof. intros.
  rewrite (Clist_disjoint2_is_orth l a b); try easy.
  apply filter_orth_length.
Qed.

Lemma seq_matrix_filter_disjoint2_is_orth : forall n a b (A: Square n),
  (forall x:nat, In x (List.seq 0 n) -> (A x x = a \/ A x x = b)) -> (a <> b) ->
  (filter (fun x:nat => Ceqb (A x x) b) (List.seq 0 n) = filter (fun x:nat => (negb (Ceqb (A x x) a))) (List.seq 0 n)).
Proof. intros.
  apply filter_ext_in.
  intros.
  specialize (H0 a0 H2).
  destruct H0.
  - unfold Ceqb.
    rewrite H0.
    destruct (Ceq_dec a b);
      destruct (Ceq_dec a a);
      try contradiction.
    easy.
  - unfold Ceqb.
    rewrite H0.
    destruct (Ceq_dec b b);
      destruct (Ceq_dec b a);
      try contradiction.
    symmetry in e0.
    contradiction.
    easy.
Qed.

Lemma map_filter_Ceqb_comm : forall n a (f : nat -> C),
    (map f (filter (fun x : nat => f x =? a) (List.seq 0 n))) =
      (filter (fun c : C => c =? a) (map f (List.seq 0 n))).
Proof. induction n; intros; try easy.
  rewrite seq_S.
  simpl. rewrite filter_app, ! map_app, filter_app.
  simpl. 
  f_equal.
  - apply IHn.
  - unfold Ceqb.
    destruct (Ceq_dec (f n) a); easy.
Qed.

Lemma map_filter_matrix_Ceqb_comm : forall n a (A : Square n),
  (map (fun x : nat => A x x) (filter (fun x : nat => A x x =? a) (List.seq 0 n))) =
    (filter (fun c : C => c =? a) (map (fun x : nat => A x x) (List.seq 0 n))).
Proof. intros. apply map_filter_Ceqb_comm. Qed.


Lemma plusminus1list_sum_is_length_diff : forall n l,
    (forall x, In x l -> x = C1 \/ x = Copp C1) -> fold_left Cplus l C0 = n ->
    RtoC (INR (length (filter (fun c : C => Ceqb c C1) l))) = n + RtoC (INR (length (filter (fun c : C => Ceqb c (Copp C1)) l))).
Proof. intros. gen n. induction l.
  - intros. simpl in *. rewrite <- H1. lca.
  - intros.
    assert (forall x : C, In x l -> x = C1 \/ x = (- C1)%C).
    { intros.
      assert (In x (a :: l)).
      { simpl. right. easy. }
      specialize (H0 x H3).
      easy. }
    specialize (IHl H2).
    assert (In a (a :: l)).
    { simpl. left. easy. }
    specialize (H0 a H3).
    destruct H0; rewrite H0 in *.
    + rewrite cons_conc in H1.
      rewrite fold_left_Cplus_app in H1.
      simpl in H1. rewrite Cplus_0_l in H1.
      simpl. unfold Ceqb.
      destruct (Ceq_dec C1 C1);
        destruct (Ceq_dec C1 (Copp C1));
        try easy.
      * inversion e0. lra.
      * assert ((length (C1 :: filter (fun c : C => if Ceq_dec c C1 then true else false) l)) =
                  s (length (filter (fun c : C => if Ceq_dec c C1 then true else false) l))).
        { simpl. easy. }
        rewrite H4.
        rewrite S_INR.
        apply Cplus_inj_l with (c := Copp C1) in H1.
        rewrite Cplus_assoc in H1.
        rewrite Cplus_opp_l in H1.
        rewrite Cplus_0_l in H1.
        specialize (IHl ((Copp C1) + n) H1).
        unfold Ceqb in IHl.
        assert (RtoC (INR (length (filter (fun c : C => if Ceq_dec c C1 then true else false) l)) + 1)%R = C1 + RtoC (INR (length (filter (fun c : C => if Ceq_dec c C1 then true else false) l)))).
        { lca. }
        rewrite H5.
        rewrite IHl.
        rewrite ! Cplus_assoc.
        rewrite Cplus_opp_r.
        rewrite Cplus_0_l.
        easy.
    + rewrite cons_conc in H1.
      rewrite fold_left_Cplus_app in H1.
      simpl in H1. rewrite Cplus_0_l in H1.
      simpl. unfold Ceqb.
      destruct (Ceq_dec (Copp C1) C1);
        destruct (Ceq_dec (Copp C1) (Copp C1));
        try easy.
      * inversion e. lra.
      * assert ((length ((Copp C1) :: filter (fun c : C => if Ceq_dec c (Copp C1) then true else false) l)) = s (length (filter (fun c : C => if Ceq_dec c (- C1) then true else false) l))).
        { simpl. easy. }
        rewrite H4.
        rewrite S_INR.
        apply Cplus_inj_l with (c := C1) in H1.
        rewrite Cplus_assoc in H1.
        rewrite Cplus_opp_r in H1.
        rewrite Cplus_0_l in H1.
        specialize (IHl (C1 + n) H1).
        unfold Ceqb in IHl.
        assert (RtoC (INR (length (filter (fun c : C => if Ceq_dec c (- C1) then true else false) l)) + 1)%R = C1 + RtoC (INR (length (filter (fun c : C => if Ceq_dec c (- C1) then true else false) l)))).
        { lca. }
        rewrite H5.
        rewrite IHl.
        rewrite ! Cplus_assoc.
        setoid_rewrite Cplus_comm at 2.
        easy.
Qed.


Lemma big_sum_permutation : forall (A : Type) (m : nat) (d : A) (l1 l2 : list A) (f : A -> C),
    Permutation l1 l2 -> (m >= length l1)%nat ->
    Σ (fun y : nat => f (nth y l1 d)) m = Σ (fun y : nat => f (nth y l2 d)) m.
Proof. intros.
  gen m.
  induction H0.
  - simpl. easy.
  - intros. simpl in *.
    destruct m; try easy.
    rewrite <- ! big_sum_extend_l.
    rewrite IHPermutation.
    easy. lia.
  - intros. 
    destruct m; try easy.
    destruct m.
    simpl in *.
    lia.
    rewrite <- ! big_sum_extend_l.
    simpl.
    lca.
  - intros.
    rewrite IHPermutation1; try easy.
    rewrite IHPermutation2; try easy.
    apply Permutation_length in H0_.
    rewrite H0_ in H1.
    easy.
Qed.  

Definition is_in_nat_list (n : nat) (listN : list nat) : bool :=
  existsb (fun m : nat => Nat.eqb n m) listN.



Lemma NoDup_app_comm : forall (A : Type) (list1 list2 : list A),
    NoDup (list1 ++ list2) -> NoDup (list2 ++ list1).
Proof. intros. apply NoDup_incl_NoDup with (l := list1 ++ list2) (l' := list2 ++ list1); trivial.
  - rewrite ! app_length. lia.
  - apply incl_app.
    + apply incl_appr.
      apply incl_refl.
    + apply incl_appl.
      apply incl_refl.
Qed.

Lemma NoDup_app_in_neg_r : forall (A : Type) (a : A) (list1 list2 : list A),
    NoDup (list1 ++ list2) -> In a list1 -> ~ In a list2.
Proof. intros.
  gen a list1. induction list2.
  - intros. intro. inversion H2.
  - intros.
    apply NoDup_remove in H0.
    intro.
    simpl in *.
    destruct H0.
    destruct H2.
    + rewrite <- H2 in H1.
      assert (In a (list1 ++ list2)).
      { rewrite in_app_iff. left. easy. }
      apply H3 in H4.
      contradiction.
    + contradict H2.
      apply IHlist2 with (list1 := list1); trivial.
Qed.

Lemma NoDup_app_in_neg_l : forall (A : Type) (a : A) (list1 list2 : list A),
    NoDup (list1 ++ list2) -> In a list2 -> ~ In a list1.
Proof. intros. apply NoDup_app_comm in H0.
  apply NoDup_app_in_neg_r with (list1 := list2); trivial.
Qed.

Lemma Permutation_incl : forall (A : Type) (l l' : list A), Permutation l l' -> incl l l'.
Proof. intros. unfold incl. intros. apply Permutation_in with (l := l); trivial. Qed.


Lemma last_in_list : forall {A : Type} (d : A) (l : list A),
    l <> [] -> In (last l d) l.
Proof. intros A d l H0.
  apply app_removelast_last with (d := d) in H0.
  rewrite <- nth_middle with (a := (last l d)) (d := d) (l := removelast l) (l' := []).
  rewrite <- H0.
  apply nth_In.
  rewrite H0.
  rewrite removelast_last.
  rewrite app_length.
  simpl.
  lia.
Qed.



 Lemma get_vec_reduce_col_back : forall {n m : nat} (i col : nat) (A : Matrix n (s m)),
     (i >= col)%nat -> get_vec i (reduce_col A col) = get_vec (1 + i)%nat A.
 Proof. intros n m i0 col A H0.
   unfold get_vec, reduce_col.
   prep_matrix_equality.
   bdestruct_all; reflexivity.
 Qed.

 Lemma get_vec_overflow : forall {n m : nat} (k : nat) (A : Matrix n m),
    (k >= m)%nat -> WF_Matrix A -> get_vec k A = Zero.
Proof. intros n m k A H0 H1.
  prep_matrix_equality.
  unfold get_vec.
  bdestruct_all; trivial.
  unfold WF_Matrix in H1.
  rewrite H1; trivial; lia.
Qed.


Lemma get_vec_smash_left : forall {n m o : nat} (i : nat) (A : Matrix n m) (B : Matrix n o),
    (i < m)%nat -> get_vec i (smash A B) = get_vec i A.
Proof. intros n m o i0 A B H0.
  unfold smash, get_vec.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_vec_smash_right : forall {n m o : nat} (i : nat) (A : Matrix n m) (B : Matrix n o),
    (i >= m)%nat -> get_vec i (smash A B) = get_vec (i - m) B.
Proof. intros n m o i0 A B H0.
  unfold smash, get_vec.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.


Lemma reduce_col_smash_left : forall {n m o : nat} (k : nat) (A : Matrix n (s m)) (B : Matrix n o),
    (k <= m)%nat -> reduce_col (smash A B) k = smash (reduce_col A k) B.
Proof. intros n m o k A B H0.
  unfold smash, reduce_col.
  prep_matrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma reduce_col_smash_right : forall {n m o : nat} (k : nat) (A : Matrix n m) (B : Matrix n (s o)),
    (k >= m)%nat -> reduce_col (smash A B) k = smash A (reduce_col B (k - m)).
Proof. intros n m o k A B H0.
  unfold smash, reduce_col.
  prep_matrix_equality.
  bdestruct_all; trivial.
  replace (1 + (y - m))%nat with (1 + y - m)%nat by lia.
  reflexivity.
Qed.

Definition delete_nth {A : Type} (l : list A) (n : nat) := firstn n l ++ skipn (n + 1) l.


Lemma length_delete_nth : forall {A : Type} (l : list A) (k : nat),
    (k < length l)%nat -> length (delete_nth l k) = ((length l) - 1)%nat.
Proof. intros A l k H0. 
  unfold delete_nth.
  rewrite app_length.
  rewrite firstn_length.
  rewrite skipn_length.
  lia.
Qed.

Lemma incl_firstn_next : forall {A : Type} (l : list A) (k : nat),
    incl (firstn k l) (firstn (s k) l).
Proof. unfold incl.
  intros A l k a H0.
  gen l.
  induction k.
  - intros.
    simpl in H0.
    contradiction.
  - intros.
    destruct l.
    + inversion H0.
    + simpl in H0.
      destruct H0.
      * simpl.
        auto.
      * right.
        auto.
Qed.

Lemma incl_skipn_previous : forall {A : Type} (l : list A) (k : nat),
    incl (skipn (s k) l) (skipn k l).
Proof. unfold incl.
  intros A l k a H0.
    gen l.
  induction k.
  - intros.
    simpl.
    destruct l.
    + inversion H0.
    + simpl in H0.
      simpl.
      auto.
  - intros. 
    destruct l.
    + inversion H0.
    + simpl.
      apply IHk.
      simpl in H0.
      apply H0.
Qed.

Lemma incl_delete_nth_original : forall {A : Type} (l : list A) (k : nat),
    incl (delete_nth l k) l.
Proof. intros A l k.
  unfold incl, delete_nth.
  intros a H0.
  rewrite in_app_iff in H0.
  destruct H0.
  - induction l.
    + rewrite firstn_nil in H0.
      assumption.
    + destruct k.
      * simpl in *.
        contradiction.
      * rewrite firstn_cons in H0.
        simpl in H0.
        simpl.
        destruct H0.
        -- left; assumption.
        -- right.
           apply IHl.
           apply incl_firstn_next; trivial.
  - induction k.
    + replace l with (skipn 0%nat l) by easy.
      apply incl_skipn_previous.
      assumption.
    + apply IHk.
      apply incl_skipn_previous.
      assumption.
Qed.

Lemma incl_delete_nth : forall {A : Type} (l l' : list A) (k : nat),
    incl l l' -> incl (delete_nth l k) l'.
Proof. intros A l l' k H0.
  apply (incl_tran (incl_delete_nth_original l k)) in H0.
  assumption.
Qed.

Lemma map_const_repeat : forall {A B : Type} {a : A} {l : list B},
    map (fun x => a) l = repeat a (length l).
Proof. intros A B a l.
  induction l; auto.
  simpl. rewrite IHl.
  reflexivity.
Qed.

Lemma zero_all_zero : forall {n : nat} {a : Vector n},
    WF_Matrix a -> ((forall i, (i < n)%nat -> a i 0%nat = C0) <-> a = Zero).
Proof. intros n a H0.
  split; intros.
  - prep_matrix_equality.
    bdestruct (y <? 1)%nat.
    + replace y with 0%nat by lia.
      bdestruct (x <? n)%nat.
      * rewrite H1; auto.
      * rewrite H0; auto; lia.
    + rewrite H0; auto; lia.
  - rewrite H1; auto.
Qed.

Lemma repeat_nth : forall {A : Type} {a : A} {l : list A},
    l = repeat a (length l) <-> (forall i, nth i l a = a).
Proof. intros A a l.
  split; intros.
  - rewrite H0, nth_repeat; reflexivity.
  - apply nth_ext with (d := a) (d' := a).
    + rewrite repeat_length; auto.
    + intros n H1.
      rewrite H0.
      rewrite nth_repeat.
      reflexivity.
Qed.

Lemma permutation_repeat_nth : forall {A : Type} {a : A} {l : list A},
    Permutation l (repeat a (length l)) <-> (forall i, nth i l a = a).
Proof. intros A a l.
  split; intros.
  - rewrite Permutation_nth in H0.
    destruct H0 as [H0 [f [H1 [H2 H3]]]].
    remember H2 as H4. clear HeqH4.
    rewrite FinFun.bInjective_bSurjective in H4; auto.
    destruct (FinFun.bSurjective_bBijective H1 H4) as [g [H5 H6]].
    bdestruct (i <? length l)%nat.
    + destruct (H6 i H7) as [H8 H9].
      unfold FinFun.bFun in H5.
      specialize (H5 i H7).
      specialize (H3 (g i) H5).
      rewrite H9 in H3.
      rewrite <- H3.
      rewrite nth_repeat.
      reflexivity.
    + rewrite nth_overflow; auto; lia.
  - rewrite <- repeat_nth in H0.
    rewrite <- H0.
    apply Permutation_refl.
Qed.

Definition trichotomy (A B C : Prop) := (A /\ ~ B /\ ~ C) \/ (~ A /\ B /\ ~ C) \/ (~ A /\ ~ B /\ C).



Fixpoint index_rec (i : nat) (list0 : list nat) (n : nat) {struct list0} : option nat :=
  match list0 with
  | nil => None
  | h :: t => if (n =? h)%nat then Some i else index_rec (s i) t n
  end.
Definition index := index_rec 0%nat.

Lemma index_rec_nil : forall i n : nat, index_rec i nil n = None.
Proof. intros; unfold index; easy. Qed.
Lemma index_nil : forall n : nat, index nil n = None.
Proof. apply index_rec_nil. Qed.

Definition add_Some (i : nat) (x : option nat) : option nat :=
  match x with
  | None => None
  | Some n => Some (n + i)%nat
  end.
Definition add_one := add_Some 1%nat.

Lemma add_one_Some : forall (i : nat), add_one (Some i) = Some (s i).
Proof. unfold add_one; simpl; setoid_rewrite Nat.add_1_r; auto. Qed.

Lemma add_Some_add_Some : forall (i j : nat) (x : option nat),
    add_Some i (add_Some j x) = add_Some (j + i) x.
Proof. intros i0 j x.
  induction x; auto; simpl; rewrite Nat.add_assoc; easy.
Qed.

Lemma index_rec_nat : forall (i : nat) (list0 : list nat) (n : nat),
    index_rec i list0 n = add_Some i (index list0 n).
Proof. intros i0 list0 n. unfold index.
  gen i0.
  induction list0.
  - intros; rewrite index_rec_nil, index_nil; easy.
  - intros; simpl; bdestruct_all; auto.
    setoid_rewrite IHlist0.
    rewrite add_Some_add_Some.
    f_equal; lia.
Qed.

Lemma index_rec_one : forall (list0 : list nat) (n : nat),
    index_rec 1%nat list0 n = add_one (index list0 n).
Proof. intros list0 n. apply index_rec_nat. Qed. 

Definition unwrap (x : option nat) : nat :=
  match x with
  | None => 0%nat
  | Some n => n
  end.
  
Lemma index_cons : forall (x : nat) (list0 : list nat) (n : nat),
    index (x :: list0) n = if (n =? x)%nat then Some 0%nat else add_one (index list0 n).
Proof. intros x list0 n.
  unfold index.
  bdestruct_all; subst; simpl; bdestruct_all; auto.
  apply index_rec_one.
Qed.

Lemma index_bound : forall (list0 : list nat) (n : nat),
    list0 <> [] -> (unwrap (index list0 n) < length list0)%nat.
Proof. intros list0 n H0.
  destruct (index list0 n) eqn:E.
  - simpl.
    gen n0.
    induction list0; intros n0 E.
    + rewrite index_nil in E.
      inversion E.
    + rewrite index_cons in E.
      bdestruct (n =? a)%nat.
      * inversion E.
        simpl. lia.
      * destruct (list_eq_dec Nat.eq_dec list0 nil) as [E' | E'].
        -- subst.
           rewrite index_nil in E.
           inversion E.
        -- specialize (IHlist0 E' ).
           destruct (index list0 n) eqn:E0.
           ++ simpl in *.
              inversion E.
              subst.
              specialize (IHlist0 n1 eq_refl).
              lia.
           ++ inversion E.
  - simpl. rewrite <- length_zero_iff_nil in H0. lia.
Qed.

Lemma In_index_Some : forall (list0 : list nat) (n : nat), In n list0 <-> (exists i, index list0 n = Some i).
Proof. intros list0 n.
  split; intros H0.
  - apply In_nth with (d := 0%nat) in H0.
    destruct H0 as [i [H0 H1]].
    gen i.
    induction list0; simpl in *.
    + intros; lia.
    + intros i0 H0 H1.
      rewrite index_cons.
      bdestruct_all.
      * exists 0%nat. easy.
      * destruct i0; try lia.
        assert (i0 < length list0)%nat by lia.
        destruct (IHlist0 i0 H3 H1) as [j H4].
        exists (s j).
        rewrite H4.
        rewrite add_one_Some.
        reflexivity.
  - destruct H0 as [i H0].
    unfold index in H0.
    gen i.
    induction list0.
    + intros; simpl in *; inversion H0.
    + intros; rewrite index_cons in H0.
      bdestruct (n =? a)%nat.
      * subst. apply in_eq.
      * destruct (index list0 n) eqn:E.
        -- simpl in H0.
           inversion H0.
           subst.
           specialize (IHlist0 n0 E).
           apply in_cons; auto.
        -- inversion H0.
Qed.

Lemma nth_index : forall (list0 : list nat) (n d : nat),
    In n list0 -> nth (unwrap (index list0 n)) list0 d = n.
Proof. intros list0 n d H0.
  (* remember H0 as H0'. clear HeqH0'. *)
  rewrite In_index_Some in H0.
  destruct H0 as [i H0].
  rewrite H0 in *.
  simpl.
  gen i.
  induction list0; intros.
  - rewrite index_nil in H0. inversion H0.
  - rewrite index_cons in H0.
    bdestruct (n =? a)%nat.
    + subst.
      inversion H0.
      subst.
      easy.
    + destruct (index list0 n) eqn:E.
      * simpl in H0.
        inversion H0.
        subst.
        rewrite Nat.add_1_r in *.
        simpl.
        apply IHlist0; easy.
      * simpl in H0. inversion H0.
Qed.

Lemma index_nth : forall (list0 : list nat) (i d : nat), NoDup list0 -> (i < length list0)%nat ->
                                                index list0 (nth i list0 d) = Some i.
Proof. intros list0 i d H0 H1.
  pose (nth_In list0 d H1) as H2.
  rewrite In_index_Some in H2.
  destruct H2 as [j H2].
  rewrite H2.
  rewrite NoDup_nth in H0.
 assert (length list0 <> 0%nat).
 { intro. rewrite length_zero_iff_nil in H3. subst. simpl in *. inversion H1. }
 rewrite length_zero_iff_nil in H3.
 pose (index_bound list0 (nth i list0 d) H3) as H4.
 rewrite H2 in H4.
 simpl in H4.
 specialize (H0 i j H1 H4).
 assert (nth (unwrap (index list0 (nth i list0 d))) list0 d = nth j list0 d) by (rewrite H2; auto).
 assert (In (nth i list0 d) list0) by (apply nth_In; lia).
 rewrite (nth_index list0 (nth i list0 d) d H6) in H5.
 specialize (H0 H5).
 rewrite H0 in *.
 reflexivity.
Qed.

Lemma single_element_matrix_equality : forall (A B : Matrix 1%nat 1%nat),
    WF_Matrix A -> WF_Matrix B -> (A = B <-> A 0%nat 0%nat = B 0%nat 0%nat).
Proof. intros A B H0 H1.
  split; intros.
  - rewrite H2; auto.
  - prep_matrix_equality.
    bdestruct (x <? 1%nat).
    + replace x with 0%nat by lia.
      bdestruct (y <? 1%nat).
      * replace y with 0%nat by lia; auto.
      * rewrite H0, H1; auto; lia.
    + rewrite H0, H1; auto; lia.
Qed.

Lemma e_i_overflow : forall (n i : nat), (i >= n)%nat -> @e_i n i = @Zero n 1%nat.
Proof. intros n i0 H0.
  unfold e_i.
  prep_matrix_equality.
  bdestruct_all; auto.
Qed.


Lemma basis_vector_e_i : forall len n,
    (n < len)%nat ->
  basis_vector len n = @e_i len n.
Proof. intros len n H. prep_matrix_equality.
  unfold basis_vector, e_i. 
  bdestruct_all; simpl; try lca.
Qed.



Lemma equal_by_basis_vectors_implies_equal : forall m n (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall j k, (j < m)%nat -> (k < n)%nat -> (basis_vector m j) † × A × (basis_vector n k) =
                  (basis_vector m j) † × B × (basis_vector n k)) ->
  A = B.
Proof. intros m n A B H0 H1 H2.
  assert (forall j k : nat,
       (j < m)%nat ->
       (k < n)%nat ->
       adjoint (@e_i m j) × A × @e_i n k =
       adjoint (@e_i m j) × B × @e_i n k).
  { intros j k H3 H4. rewrite <- ! basis_vector_e_i; auto. }
  prep_matrix_equality.
  bdestruct (x <? m)%nat. 
  - bdestruct (y <? n)%nat. 
    + setoid_rewrite get_entry_with_e_i; auto.
      rewrite H3; auto.
    + rewrite H0, H1; try lia; auto.
  - rewrite H0, H1; try lia; auto.
Qed.

Lemma equal_by_basis_states_implies_equal : forall n (A B : Square (2 ^ n)),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall f g, (f_to_vec n f) † × A × (f_to_vec n g) =
                  (f_to_vec n f) † × B × (f_to_vec n g)) ->
  A = B.
Proof. intros n A B H0 H1 H2.
  apply equal_by_basis_vectors_implies_equal; auto.
  intros j k H3 H4.
  rewrite ! basis_f_to_vec_alt; auto.
Qed.


Lemma e_i_kron : forall (n m i j : nat),
    (i < n)%nat -> (j < m)%nat -> @e_i n i ⊗ @e_i m j = @e_i (n*m) (m*i+j).
Proof. intros.
  unfold e_i, kron.
  prep_matrix_equality.
  bdestruct_all; simpl in *; auto; try lca. 
  all: try rewrite divmod_0 in *; try contradiction.
  all: try (rewrite <- H5, <- H7 in H9; rewrite <- Nat.div_mod_eq in H9; contradiction).
  all: try (contradict H7; symmetry; apply Nat.mod_unique with (q := i); easy).
  all: try (contradict H5; symmetry; apply Nat.div_unique with (r := j); easy).
  nia.
Qed.

Lemma e_i_kron_inv : forall (n m k : nat),
    m <> 0%nat -> (k < n*m)%nat -> @e_i (n*m) k = @e_i n (k/m)%nat ⊗ @e_i m (k mod m)%nat.
Proof. intros n m k H H0.
  rewrite (Nat.div_mod_eq k m) at 1. rewrite <- e_i_kron; auto.
  apply Nat.Div0.div_lt_upper_bound. lia.
  apply Nat.mod_upper_bound. auto.
Qed.
 
Lemma fold_right_Mplus_Zero_Mscale_distr : 
  forall {m n : nat} (c : C) (Lm : list (Matrix m n)),
    fold_right Mplus Zero (map (fun M => c .* M) Lm) =
      c .* fold_right Mplus Zero (map (fun M => M) Lm).
Proof. intros m n c Lm.
  induction Lm.
  simpl. lma'.
  simpl. rewrite Mscale_plus_distr_r. f_equal. auto.
Qed.



Definition vector_slice {n : nat} (v : Vector n) (k : nat) : Vector n :=
  (fun r c => if (r <? k)%nat then v r c else C0).

Lemma vector_slice_all : forall {n : nat} (v : Vector n) (k : nat),
    WF_Matrix v -> (k >= n)%nat -> vector_slice v k = v.
Proof. intros n v k H H0. 
  unfold vector_slice. 
  prep_matrix_equality. 
  bdestruct_all; auto.
  rewrite H; auto; lia.
Qed.

Lemma vector_slice_none : forall {n : nat} (v : Vector n),
    vector_slice v 0%nat = Zero.
Proof. intros n v.
  unfold vector_slice, Zero.
  prep_matrix_equality.
  bdestruct_all. auto.
Qed.

Lemma vector_slice_step : forall {n : nat} (v : Vector n) (k : nat),
  WF_Matrix v -> vector_slice v k .+ (v k 0%nat) .* (e_i k) = vector_slice v (Datatypes.S k).
Proof. intros n v k H0.
  unfold vector_slice, Matrix.scale, e_i, Mplus.
  prep_matrix_equality.
  bdestruct_all; simpl; subst; auto; try lca; try setoid_rewrite H0 at 2; auto; try lia; try lca.
Qed.

Lemma vector_slice_as_e_i_sum : forall {n : nat} (v : Vector n) (k : nat),
    WF_Matrix v -> (k <= n)%nat ->
    vector_slice v k = fold_right Mplus Zero (map (fun i => (v i 0%nat) .* e_i i) (List.seq 0 k)).
Proof. intros n v k H H0.
  induction k.
  - simpl. apply vector_slice_none.
  - rewrite seq_S. simpl. rewrite map_app. rewrite fold_right_Mplus_Zero_app.
    rewrite <- IHk; try lia. simpl. rewrite <- vector_slice_step; auto. f_equal. lma'.
Qed.

Lemma vector_as_e_i_sum : forall {n : nat} (v : Vector n),
    WF_Matrix v -> 
    v = fold_right Mplus Zero (map (fun i => (v i 0%nat) .* e_i i) (List.seq 0 n)).
Proof. intros n v H0.
  rewrite <- vector_slice_as_e_i_sum; auto.
  rewrite vector_slice_all; auto.
Qed.

Lemma WF_vector_slice : forall {n : nat} (v : Vector n) (k : nat),
    WF_Matrix v -> WF_Matrix (vector_slice v k).
Proof. intros n v k H0.
  unfold WF_Matrix. intros x y H1.
  unfold vector_slice. bdestruct_all; auto.
Qed.

Lemma WF_e_i_sum : 
  forall {n : nat} (v : Vector n) (k : nat),
  WF_Matrix v -> (k <= n)%nat ->
  @WF_Matrix n 1%nat (fold_right Mplus Zero (map (fun i => (v i 0%nat) .* e_i i) (List.seq 0 k))).
Proof. intros n v k H0 H1.
  rewrite <- vector_slice_as_e_i_sum; auto.
  apply WF_vector_slice; auto.
Qed.

Lemma matrix_times_vector_slice_as_get_col_sum : forall {m n : nat} (M : Matrix m n) (v : Vector n) (k : nat),
WF_Matrix v -> (k <= n)%nat ->
M × (vector_slice v k) = fold_right Mplus Zero (map (fun i => ((v i 0%nat) .* get_col M i)) (List.seq 0 k)).
Proof. intros m n M v k H0 H1.
  induction k. rewrite vector_slice_none. rewrite Mmult_0_r. auto.
  rewrite <- vector_slice_step; auto.
  rewrite seq_S. simpl. rewrite map_app.
  rewrite fold_right_Mplus_Zero_app. simpl. 
  rewrite Mmult_plus_distr_l.
  rewrite IHk; try lia. f_equal.
  distribute_scale. rewrite Mplus_0_r.
  f_equal. rewrite matrix_by_basis; auto; lia.
Qed.

Lemma matrix_span_as_get_col_sum : forall {m n : nat} (M : Matrix m n) (v : Vector n),
    WF_Matrix v -> 
    M × v = fold_right Mplus Zero (map (fun i => ((v i 0%nat) .* get_col M i)) (List.seq 0 n)).
Proof. intros m n M v H0.
  rewrite (vector_as_e_i_sum v) at 1; auto.
  rewrite <- matrix_times_vector_slice_as_get_col_sum; auto.
  rewrite vector_slice_as_e_i_sum; auto.
Qed.

Lemma fold_right_Mplus_Zero_double_swap : forall {m n : nat} (F : nat -> nat -> Matrix m n) (l1 l2 : list nat),
  fold_right Mplus Zero (map (fun i : nat => fold_right Mplus Zero (map (fun j : nat => F i j) l2)) l1) =
    fold_right Mplus Zero (map (fun j : nat => fold_right Mplus Zero (map (fun i : nat => F i j) l1)) l2).
Proof. intros m n F0 l1 l2.
  gen l1. induction l2; intros.
  - simpl. induction l1; auto. simpl. rewrite Mplus_0_l. auto.
  - simpl. rewrite <- IHl2.
    gen l2. induction l1; intros. simpl. lma'.
    simpl. rewrite ! Mplus_assoc. f_equal.
    rewrite IHl1; auto.
    rewrite <- ! Mplus_assoc. setoid_rewrite Mplus_comm at 2.
    rewrite ! Mplus_assoc. f_equal. 
Qed.

Lemma fold_right_Mplus_Zero_collect_scalar : 
  forall {m n : nat} (M : Matrix m n) (c_i : nat -> C) (l : list nat),
  fold_right Mplus Zero (map (fun i : nat => (c_i i) .* M) l) = 
    (fold_right Cplus C0 (map (fun i : nat => c_i i) l)) .* M.
Proof. intros m n M c_i l.
  induction l. 
  - simpl. rewrite Mscale_0_l. auto. 
  - simpl. rewrite Mscale_plus_distr_l. f_equal. auto.
Qed.

Lemma fold_right_Mplus_Zero_big_sum : forall {m n : nat} (M_i : nat -> (Matrix m n)) (k : nat),
    fold_right Mplus Zero (map (fun i : nat => M_i i) (List.seq 0 k)) =
      big_sum (fun i : nat => M_i i) k.
Proof. intros m n M_i k.
  induction k; auto.
  rewrite seq_S. simpl. rewrite map_app, fold_right_Mplus_Zero_app. 
  simpl. rewrite Mplus_0_r. 
  replace (Mplus (big_sum (fun i : nat => M_i i) k) (M_i k)) with
            (Mplus (big_sum (fun i : nat => M_i i) k) (M_i k)) by auto.
  f_equal. auto.
Qed.
  

Lemma fold_right_Cplus_C0_big_sum : forall (C_i : nat -> C) (k : nat),
  fold_right Cplus C0 (map (fun i : nat => C_i i) (List.seq 0 k)) =
    big_sum (fun i : nat => C_i i) k.
Proof. intros C_i k.
  induction k; auto.
  rewrite seq_S. simpl. rewrite map_app. 
  rewrite <- fold_symmetric. simpl. rewrite fold_left_Cplus_app. simpl.
  rewrite Cplus_0_l. f_equal. rewrite fold_symmetric. auto.
  all : try apply Cplus_assoc; intros; lca.
Qed.

Lemma fold_right_Mplus_Zero_scaled_vector_sum :
  forall {n : nat} (c_i : nat -> C) (v_i : nat -> Vector n) (k : nat),
    Forall (fun i : nat => WF_Matrix (v_i i)) (List.seq 0 k) ->
    fold_right Mplus Zero (map  (fun i : nat => c_i i .* v_i i) (List.seq 0%nat k)) =
      @Mmult n k 1%nat (fun r c : nat => v_i c r 0%nat) (fun r c : nat => if (c =? 0)%nat then c_i r else C0).
Proof. intros n c_i v_i k H.
  induction k. 
  - simpl. unfold Mmult. simpl. lma'.
  - rewrite seq_S. rewrite Nat.add_0_l, map_app, fold_right_Mplus_Zero_app. simpl.
    rewrite Mplus_0_r. rewrite IHk.
    unfold Mmult, Mplus, Matrix.scale. prep_matrix_equality. simpl. bdestruct_all; subst. 
    f_equal. lca.
    rewrite Forall_forall in H. setoid_rewrite in_seq in H. rewrite H; try lia.
    rewrite ! Cmult_0_r, ! Cplus_0_r. auto.
    rewrite seq_S, Nat.add_0_l, Forall_app in H. destruct H. auto.
Qed.
    
Lemma delete_right_kron_from_vector : forall {n j k : nat} (A_i B_i : nat -> Vector n),
    j <> 0%nat -> (k <= j)%nat ->
    Forall (fun i : nat => WF_Matrix (A_i i)) (List.seq 0 k) ->
    Forall (fun i : nat => WF_Matrix (B_i i)) (List.seq 0 k) ->
(@eq (Vector (n * j))
(fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum (Vector (n * j)) (M_is_monoid (n * j) 1%nat)
            (fun y0 : nat =>
             A_i y0 ⊗ @e_i j y0) (k) x 0%nat
         else C0)
  (fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum  (Vector (n * j)) (M_is_monoid (n * j) 1%nat)
            (fun y0 : nat =>
             B_i y0 ⊗ @e_i j y0) (k) x 0%nat
         else C0))
->
(forall i, (0 <= i < k)%nat -> A_i i = B_i i).
Proof. intros n j k A_i B_i H0 H1 H2 H3 H4 i H5. 
  induction k.
  - intros. lia.
  - intros. 
    prep_matrix_equality. remember H4 as H4'. clear HeqH4'.
    apply f_equal_inv with (x := (x * j + k)%nat) in H4.
    apply f_equal_inv with (x := y) in H4.
    bdestruct (y =? 0)%nat; subst.
    + rewrite ! Msum_Csum in H4.
      unfold kron in H4. simpl in H4.
      rewrite seq_S in H2, H3. rewrite Nat.add_0_l in H2, H3.
      rewrite Forall_app in H2, H3. destruct H2, H3.
      inversion H6; subst; clear H6. clear H11.
      inversion H7; subst; clear H7. clear H11.
      bdestruct (i =? k)%nat; subst.
      * clear IHk. 
        rewrite ! Nat.div_add_l in H4; auto.
        rewrite ! Nat.div_small in H4; try lia.
        rewrite ! Nat.add_0_r in H4.
        rewrite ! (Nat.add_comm (x * j) k) in H4.
        rewrite ! Nat.Div0.mod_add in H4.
        rewrite ! Nat.mod_small in H4; try lia.
        assert (Σ (fun x0 : nat => A_i x0 x 0%nat * @e_i j x0 k 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H6 in H4. rewrite Cplus_0_l in H4. clear H6.
        assert (Σ (fun x0 : nat => B_i x0 x 0%nat * @e_i j x0 k 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H6 in H4. rewrite Cplus_0_l in H4. clear H6.
        unfold e_i in H4. simpl in H4. 
        bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia. 
        simpl in H4. rewrite ! Cmult_1_r in H4. auto.
      * rewrite ! Nat.div_add_l in H4; auto.
        rewrite ! Nat.div_small in H4; try lia.
        rewrite ! Nat.add_0_r in H4.
        rewrite ! (Nat.add_comm (x * j) k) in H4.
        rewrite ! Nat.Div0.mod_add in H4.
        rewrite ! Nat.mod_small in H4; try lia.
        assert (Σ (fun x0 : nat => A_i x0 x 0%nat * @e_i j x0 k 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H7 in H4. rewrite Cplus_0_l in H4. clear H7.
        assert (Σ (fun x0 : nat => B_i x0 x 0%nat * @e_i j x0 k 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H7 in H4. rewrite Cplus_0_l in H4. clear H7.
        unfold e_i in H4. simpl in H4. 
        bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia. 
        simpl in H4. rewrite ! Cmult_1_r in H4.

        assert (k <= j)%nat by lia.
        specialize (IHk H11 H2 H3).
        assert ((fun x y : nat =>
         if (y =? 0)%nat
         then @big_sum  (Vector (n * j)) (M_is_monoid (n * j) 1%nat) (fun y0 : nat => A_i y0 ⊗ @e_i j y0) k x 0%nat
         else C0) =
        (fun x y : nat =>
         if (y =? 0)%nat
         then @big_sum  (Vector (n * j)) (M_is_monoid (n * j) 1%nat) (fun y0 : nat => B_i y0 ⊗ @e_i j y0) k x 0%nat
         else C0)).
        { prep_matrix_equality. bdestruct_all; subst; auto.
          assert (forall x : nat, @big_sum (Vector (n*j)%nat) (M_is_monoid (n*j)%nat 1%nat) (fun y0 : nat => A_i y0 ⊗ @e_i j y0) (s k) x 0%nat =
                             @big_sum (Vector (n*j)%nat) (M_is_monoid (n*j)%nat 1%nat) (fun y0 : nat => B_i y0 ⊗ @e_i j y0) (s k) x 0%nat).
          { intros x1. apply f_equal_inv with (x := x1) in H4'.
            apply f_equal_inv with (x := 0%nat) in H4'. simpl in *. auto. }
          
          simpl in H12. unfold Mplus in H12. 
          setoid_rewrite Msum_Csum in H12.
          unfold kron in H12. simpl in H12.
          setoid_rewrite Msum_Csum. unfold kron. simpl.
          
          assert ((A_i k ⊗ @e_i j k) x0 0%nat = (B_i k ⊗ @e_i j k) x0 0%nat).
          { unfold kron. simpl. unfold e_i. bdestruct_all; simpl; try lca. rewrite ! Cmult_1_r.
            specialize (H12 x0). rewrite ! H14 in H12.
            assert (Σ (fun x : nat => A_i x (x0 / j)%nat 0%nat * @e_i j x k 0%nat) k = C0).
            { rewrite big_sum_0_bounded; auto; intros.
              unfold e_i. bdestruct_all; simpl; try lca. }
            rewrite H16 in H12. rewrite Cplus_0_l in H12.
            assert (Σ (fun x : nat => B_i x (x0 / j)%nat 0%nat * @e_i j x k 0%nat) k = C0).
            { rewrite big_sum_0_bounded; auto; intros.
              unfold e_i. bdestruct_all; simpl; try lca. }
            rewrite H17 in H12. rewrite Cplus_0_l in H12.
            unfold e_i in H12. bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia.
            simpl in H12. rewrite ! Cmult_1_r in H12. auto. }
          specialize (H12 x0).
          unfold kron in H13. simpl in H13. rewrite H13 in H12.
          apply Cplus_inv_r in H12. auto. }
        assert (0 <= i < k)%nat by lia.
        specialize (IHk H12 H13).
        rewrite IHk. auto.
    + rewrite Forall_forall in H2, H3.
      rewrite H2; auto; try rewrite in_seq; try lia.
      rewrite H3; auto; try rewrite in_seq; try lia.
Qed.

Lemma delete_left_kron_from_vector : forall {m j k : nat} (A_i B_i : nat -> Vector m),
    m <> 0%nat -> (k <= j)%nat ->
    Forall (fun i : nat => WF_Matrix (A_i i)) (List.seq 0 k) ->
    Forall (fun i : nat => WF_Matrix (B_i i)) (List.seq 0 k) ->
(@eq (Vector (j * m)%nat)
(fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat)
            (fun x0 : nat =>
            @e_i j x0 ⊗ A_i x0) (k) x 0%nat
         else C0)
(fun x y : nat =>
         if (y =? 0)%nat
         then
          @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat)
            (fun x0 : nat =>
            @e_i j x0 ⊗ B_i x0) (k) x 0%nat
         else C0))
->
(forall i, (0 <= i < k)%nat -> A_i i = B_i i).
Proof. intros m j k A_i B_i H0 H1 H2 H3 H4 i H5. 
  induction k.
  - intros. lia.
  - intros. 
    prep_matrix_equality. 
    bdestruct (x <? m)%nat.
    2: { rewrite Forall_nth in H2, H3.
         assert (WF_Matrix (A_i i)).
         { specialize (H2 i).
           setoid_rewrite seq_nth in H2; try lia.
           setoid_rewrite seq_length in H2.
           apply H2; auto; lia. }
         assert (WF_Matrix (B_i i)).
         { specialize (H3 i).
           setoid_rewrite seq_nth in H3; try lia.
           setoid_rewrite seq_length in H3.
           apply H3; auto; lia. }
         rewrite H7, H8; auto; lia. }
    remember H4 as H4'. clear HeqH4'.
    apply f_equal_inv with (x := (k * m + x)%nat) in H4.
    apply f_equal_inv with (x := y) in H4.
    bdestruct (y =? 0)%nat; subst.
    + rewrite ! Msum_Csum in H4.
      unfold kron in H4. simpl in H4.
      rewrite seq_S in H2, H3. rewrite Nat.add_0_l in H2, H3.
      rewrite Forall_app in H2, H3. destruct H2, H3.
      inversion H7; subst; clear H7. clear H12.
      inversion H8; subst; clear H8. clear H12.
      bdestruct (i =? k)%nat; subst.
      * clear IHk. 
        rewrite ! Nat.div_add_l in H4; auto.
        rewrite ! Nat.div_small in H4; try lia.
        rewrite ! Nat.add_0_r in H4.
        rewrite ! (Nat.add_comm (k * m) x) in H4.
        rewrite ! Nat.Div0.mod_add in H4.
        rewrite ! Nat.mod_small in H4; try lia.
        assert (Σ (fun x0 : nat => @e_i j x0 k 0%nat * A_i x0 x 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H7 in H4. rewrite Cplus_0_l in H4. clear H7.
        assert (Σ (fun x0 : nat => @e_i j x0 k 0%nat * B_i x0 x 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H7 in H4. rewrite Cplus_0_l in H4. clear H7.
        unfold e_i in H4. simpl in H4. 
        bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia. 
        simpl in H4. rewrite ! Cmult_1_l in H4. auto.
      * rewrite ! Nat.div_add_l in H4; auto.
        rewrite ! Nat.div_small in H4; try lia.
        rewrite ! Nat.add_0_r in H4.
        rewrite ! (Nat.add_comm (k * m) x) in H4.
        rewrite ! Nat.Div0.mod_add in H4.
        rewrite ! Nat.mod_small in H4; try lia.
        assert (Σ (fun x0 : nat => @e_i j x0 k 0%nat * A_i x0 x 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H8 in H4. rewrite Cplus_0_l in H4. clear H8.
        assert (Σ (fun x0 : nat => @e_i j x0 k 0%nat * B_i x0 x 0%nat) k = C0).
        { rewrite big_sum_0_bounded; auto; intros.
          unfold e_i. bdestruct_all; simpl; auto; lca. }
        rewrite H8 in H4. rewrite Cplus_0_l in H4. clear H8.
        unfold e_i in H4. simpl in H4. 
        bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia. 
        simpl in H4. rewrite ! Cmult_1_l in H4.

        assert (k <= j)%nat by lia.
        specialize (IHk H12 H2 H3). 
        assert ((fun x y : nat =>
         if (y =? 0)%nat
         then @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat) (fun x0 : nat => e_i x0 ⊗ A_i x0) k x 0%nat
         else C0) =
        (fun x y : nat =>
         if (y =? 0)%nat
         then @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat) (fun x0 : nat => e_i x0 ⊗ B_i x0) k x 0%nat
         else C0)). 
        { prep_matrix_equality. bdestruct_all; subst; auto.
          assert (forall x : nat, @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat) (fun x0 : nat => e_i x0 ⊗ A_i x0) (s k) x 0%nat =
                             @big_sum (Vector (j * m)%nat) (M_is_monoid (j * m)%nat 1%nat) (fun x0 : nat => e_i x0 ⊗ B_i x0) (s k) x 0%nat).
          { intros x1. apply f_equal_inv with (x := x1) in H4'.
            apply f_equal_inv with (x := 0%nat) in H4'. simpl in *. auto. }
          
          simpl in H13. unfold Mplus in H13. 
          setoid_rewrite Msum_Csum in H13.
          unfold kron in H13. simpl in H13.
          setoid_rewrite Msum_Csum. unfold kron. simpl.
          
          assert ((@e_i j k ⊗ A_i k) x0 0%nat = (@e_i j k ⊗ B_i k) x0 0%nat).
          { unfold kron. simpl. unfold e_i. bdestruct_all; simpl; try lca. rewrite ! Cmult_1_l.
            specialize (H13 x0). rewrite ! H15 in H13.
            assert (Σ (fun x : nat => @e_i j x k 0%nat * A_i x (x0 mod m) 0%nat) k = C0).
            { rewrite big_sum_0_bounded; auto; intros.
              unfold e_i. bdestruct_all; simpl; try lca. }
            rewrite H17 in H13. rewrite Cplus_0_l in H13.
            assert (Σ (fun x : nat => @e_i j x k 0%nat * B_i x (x0 mod m) 0%nat) k = C0).
            { rewrite big_sum_0_bounded; auto; intros.
              unfold e_i. bdestruct_all; simpl; try lca. }
            rewrite H18 in H13. rewrite Cplus_0_l in H13.
            unfold e_i in H13. bdestruct (k =? k)%nat; bdestruct (k <? j)%nat; try lia.
            simpl in H13. rewrite ! Cmult_1_l in H13. auto. }
          specialize (H13 x0).
          unfold kron in H14. simpl in H14. rewrite H14 in H13.
          apply Cplus_inv_r in H13. auto. }
        assert (0 <= i < k)%nat by lia.
        specialize (IHk H13 H14).
        rewrite IHk. auto.
    + rewrite Forall_forall in H2, H3.
      rewrite H2; auto; try rewrite in_seq; try lia.
      rewrite H3; auto; try rewrite in_seq; try lia.
Qed.


Definition submatrix_row {n m : nat} (M : Matrix n m) (k : nat) : Matrix k m :=
  (fun r c : nat => if (r <? k)%nat then M r c else C0).

Lemma WF_submatrix_row : forall {n m : nat} (M : Matrix n m) (k : nat),
    WF_Matrix M -> (k < n)%nat -> WF_Matrix (submatrix_row M k).
Proof. intros n m M k H0 H1. 
  unfold submatrix_row.
  unfold WF_Matrix. intros x y H2.
  bdestruct_all; auto. destruct H2; try lia.
  rewrite H0; auto; lia.
Qed.

Lemma submatrix_row_mult_distr : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o) (k : nat),
    submatrix_row (A × B) k = (submatrix_row A k) × B.
Proof. intros m n o A B k.
  unfold submatrix_row, Mmult.
  prep_matrix_equality.
  bdestruct_all; auto.
  rewrite big_sum_0_bounded; auto; intros; lca.
Qed.

Lemma collect_kron1 : forall {m n : nat} (v : Vector n) (u : Matrix 1%nat m) (M : Vector (n*m)%nat),
    WF_Matrix v -> WF_Matrix u -> WF_Matrix M ->
    v × u = ((fun r c : nat => if (r <? n)%nat && (c <? m) then M (m * r + c)%nat 0%nat else C0) : Matrix n m) -> M = v ⊗ u⊤.
Proof. intros m n v u M H0 H1 H2 H3.
  bdestruct (m =? 0)%nat; subst.
  - assert (M = Zero).
    { prep_matrix_equality. rewrite H2; auto; lia. }
    assert (u = Zero).
    { prep_matrix_equality. rewrite H1; auto; lia. }
    subst. rewrite kron_0_r. auto.
  - unfold transpose.
    unfold Mmult in H3. simpl in H3.
    unfold kron. prep_matrix_equality.
    bdestruct (y =? 0)%nat; subst; simpl.
    + apply f_equal_inv with (x := (x/m)%nat) in H3.
      apply f_equal_inv with (x := (x mod m)%nat) in H3.
      rewrite Cplus_0_l in H3.
      rewrite H3. bdestruct_all; simpl.
      * rewrite <- Nat.div_mod_eq. auto.
      * pose (Nat.mod_bound_pos x m) as E.
        assert (0 <= x)%nat by lia.
        assert (0 < m)%nat by lia.
        specialize (E H7 H8). lia.
      * bdestruct (x <? m*n)%nat.
        -- apply Nat.Div0.div_lt_upper_bound in H7. lia.
        -- rewrite H2; auto; lia.
      * pose (Nat.mod_bound_pos x m) as E.
        assert (0 <= x)%nat by lia.
        assert (0 < m)%nat by lia.
        specialize (E H7 H8). lia.
    + rewrite divmod_0. rewrite H2, H0; try lia; lca.
Qed.

Lemma collect_kron2 : forall {m n : nat} (v : Vector m) (u : Matrix 1%nat n) (M : Vector (n*m)%nat),
    WF_Matrix v -> WF_Matrix u -> WF_Matrix M ->
    v × u = ((fun r c : nat => if (r <? m)%nat && (c <? n) then M (m * c + r)%nat 0%nat else C0) : Matrix n m) -> M = u⊤ ⊗ v.
Proof. intros m n v u M H0 H1 H2 H3. 
  bdestruct (m =? 0)%nat; subst.
  - assert (M = Zero).
    { prep_matrix_equality. rewrite H2; auto; lia. }
    assert (v = Zero).
    { prep_matrix_equality. rewrite H0; auto; lia. }
    subst. rewrite kron_0_r. auto.
  - unfold transpose.
    unfold Mmult in H3. simpl in H3.
    unfold kron. prep_matrix_equality.
    bdestruct (y =? 0)%nat; subst; simpl. 
    + apply f_equal_inv with (x := (x mod m)%nat) in H3.
      apply f_equal_inv with (x := (x/m)%nat) in H3.
      rewrite Cplus_0_l in H3. rewrite Cmult_comm in H3.
      rewrite H3. bdestruct_all; simpl.
      * rewrite <- Nat.div_mod_eq. auto.
      * bdestruct (x <? m*n)%nat.
        -- apply Nat.Div0.div_lt_upper_bound in H7. lia.
        -- rewrite H2; auto; lia.
      * pose (Nat.mod_bound_pos x m) as E.
        assert (0 <= x)%nat by lia.
        assert (0 < m)%nat by lia.
        specialize (E H7 H8). lia. 
      * pose (Nat.mod_bound_pos x m) as E.
        assert (0 <= x)%nat by lia.
        assert (0 < m)%nat by lia.
        specialize (E H7 H8). lia.
    + rewrite divmod_0. rewrite H1, H2; try lia; lca.
Qed.


Fixpoint big_kron_sigT_Vector (Lnw : list {n : nat & Vector (2 ^ n)}) : Vector (2 ^ (fold_right Nat.add 0%nat (map (@projT1 nat (fun n : nat => Vector (2 ^ n))) Lnw))) :=
  match Lnw with
  | [] => I 1
  | nw :: Lnw' => @kron (2^(projT1 nw))%nat 1%nat (2 ^ (fold_right Nat.add 0%nat (map (@projT1 nat (fun n : nat => Vector (2 ^ n))) Lnw')))%nat 1%nat (projT2 nw) (big_kron_sigT_Vector Lnw')
  end.

Lemma WF_big_kron_sigT_Vector : forall (Lnw : list {n : nat & Vector (2 ^ n)}),
  Forall (fun nw : {n : nat & Vector (2 ^ n)} => WF_Matrix (projT2 nw)) Lnw ->
  WF_Matrix (big_kron_sigT_Vector Lnw).
Proof. intros Lnw H0.
  induction Lnw; simpl; auto with wf_db.
  rewrite Forall_cons_iff in H0. destruct H0.
  apply WF_kron; auto.
  rewrite Nat.pow_add_r; auto.
Qed.
#[export] Hint Resolve WF_big_kron_sigT_Vector : wf_db.


Lemma fold_right_add_nonzero : forall (Ln : list nat),
    Forall (fun n : nat => n <> 0%nat) Ln -> Ln <> [] ->
    fold_right Nat.add 0%nat Ln <> 0%nat.
Proof. intros Ln H0 H1.
  induction Ln; try contradiction. clear H1.
  destruct (list_eq_dec Nat.eq_dec Ln []) as [H1 | H1]; subst.
  - inversion H0; subst. simpl. lia.
  - rewrite Forall_cons_iff in H0. destruct H0. simpl.
    specialize (IHLn H2 H1). lia.
Qed.



Lemma split_Forall2 : 
  forall {A B : Type} {R : A -> B -> Prop} {a : A} {la : list A} {b : B} {lb : list B},
    R a b -> Forall2 R la lb ->
    Forall2 R (a :: la) (b :: lb).
Proof. intros. constructor; auto. Qed. 


Lemma firstn1_singleton : forall {A : Type} (d : A) (l : list A),
    l <> [] -> firstn 1 l = [hd d l].
Proof. intros A d l H0.
  destruct l; try contradiction; auto.
Qed.

Lemma hd_skipn_nth : forall {A : Type} (d : A) (l : list A) (m : nat),
    hd d (skipn m l) = nth m l d.
Proof. intros A d l m.
  gen m.
  induction l; intros m;  destruct m; simpl; auto.
Qed.
