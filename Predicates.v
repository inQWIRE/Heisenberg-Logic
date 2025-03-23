Require Export HeisenbergFoundations.Preamble.

Declare Scope Predicate_scope.
Delimit Scope Predicate_scope with P.
Local Open Scope Predicate_scope.



(************************)
(* Defining coeficients *)
(************************)


Definition Coef := C.

Definition cBigMul (cs : list Coef) : Coef :=
  fold_left Cmult cs C1.

Lemma cBigMul_app : forall (l1 l2 : list Coef),
  (cBigMul l1) * (cBigMul l2) = cBigMul (l1 ++ l2).
Proof. induction l1 as [| h]; try easy.
  intros. simpl.
  - unfold cBigMul. simpl. lca.
  - intros l2. simpl. unfold cBigMul. simpl.
    rewrite 2 fold_left_Cmult. rewrite <- Cmult_assoc.
    unfold cBigMul in IHl1.
    rewrite  IHl1; easy.
Qed.


(**********************)
(* Defining the types *)
(**********************)

(* this is the lowest level, only Pauli gates are defined *)
Inductive Pauli :=
| gI
| gX
| gY
| gZ.

Definition beq_Pauli (a b : Pauli) : bool :=
  match a, b with
  | gI, gI => true
  | gZ, gI => false
  | gY, gI => false
  | gX, gI => false
  | gI, gZ => false
  | gZ, gZ => true
  | gY, gZ => false
  | gX, gZ => false
  | gI, gY => false
  | gZ, gY => false
  | gY, gY => true
  | gX, gY => false
  | gI, gX => false
  | gZ, gX => false
  | gY, gX => false
  | gX, gX => true
  end.

Lemma eqdec_Pauli (a b : Pauli) : { a = b } + { a <> b }.
Proof. destruct a, b.
  all : try (left; reflexivity); try (right; intro; discriminate).
Qed.


Definition not_gI (g : Pauli) : Prop := g = gX \/ g = gY \/ g = gZ.

Lemma not_gI_equiv : forall (g : Pauli), not_gI g <-> g <> gI.
Proof. intros g.
  unfold not_gI.
  split; intros.
  - intro; subst.
    repeat (destruct H; try discriminate).
  - destruct g; try contradiction.
    + left; reflexivity.
    + right; left; reflexivity.
    + right; right; reflexivity.
Qed. 

Definition translate_P (g : Pauli) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gY => σy
  | gZ => σz
  end.

Lemma list_Pauli_Hermitian : forall (l : list Pauli),  (⨂ map translate_P l) † = ⨂ map translate_P l.
Proof. intros l. induction l.
  - simpl. lma'.
  - simpl. setoid_rewrite kron_adjoint. rewrite IHl.
    destruct a; simpl.
    + replace  (Matrix.I 2) †  with  (Matrix.I 2) by lma'. reflexivity.
    + replace (σx) † with  (σx) by lma'. reflexivity.
    + replace (σy) † with  (σy) by lma'. reflexivity.
    + replace (σz) † with  (σz) by lma'. reflexivity.
Qed.
 
Lemma WF_Matrix_Pauli : forall (g : Pauli), WF_Matrix (translate_P g).
Proof. intros. 
  destruct g; simpl; auto with wf_db.
Qed.

Lemma In_list_WF_Matrix_Pauli : forall (A : list Pauli),
  forall a : Square 2, In a (map translate_P A) -> WF_Matrix a.
Proof. induction A; intros.
  - simpl in H. exfalso. assumption.
  - simpl in H. destruct H.
    + rewrite <- H. apply WF_Matrix_Pauli.
    + apply IHA. assumption.
Qed.

Lemma WF_Matrix_nth_Pauli : forall (l : list Pauli),
  forall i : nat, WF_Matrix (nth i (map translate_P l) Zero).
Proof. intros. destruct (nth_in_or_default i (map translate_P l) Zero).
  - apply In_list_WF_Matrix_Pauli with (A := l). assumption.
  - rewrite e. auto with wf_db.
Qed.

Lemma WF_Unitary_Pauli : forall (g : Pauli), WF_Unitary (translate_P g).
Proof. intros.
       destruct g; simpl; auto with unit_db.
Qed.

Lemma WF_Matrix_Big_Pauli : forall (l : list Pauli), WF_Matrix (⨂ map translate_P l).
Proof. intros.
  induction l; simpl; auto with wf_db.
  apply Matrix.WF_kron; try lia; try apply IHl.
  apply WF_Matrix_Pauli.
Qed.

#[export] Hint Resolve WF_Matrix_Pauli WF_Matrix_Big_Pauli : wf_db.
#[export] Hint Resolve WF_Unitary_Pauli : unit_db.




(* Here we define a gMul to give Coef followed by a gMul to give the actual type *)
(* this allows for an easy zip in gMulT *)

Definition gMul_Coef (g1 g2 : Pauli) : Coef :=
  match g1, g2 with
  | gI, _ => C1
  | _, gI => C1
  | gX, gX => C1
  | gY, gY => C1
  | gZ, gZ => C1
  | gX, gY => Ci
  | gY, gX => (- Ci)%C
  | gX, gZ => (-Ci)%C
  | gZ, gX => Ci
  | gY, gZ => Ci
  | gZ, gY => (-Ci)%C
  end.



Definition gMul_base (g1 g2 : Pauli) : Pauli :=
  match g1, g2 with
  | gI, _ => g2
  | _, gI => g1
  | gX, gX => gI
  | gY, gY => gI
  | gZ, gZ => gI
  | gX, gY => gZ
  | gY, gX => gZ
  | gX, gZ => gY
  | gZ, gX => gY
  | gY, gZ => gX
  | gZ, gY => gX
  end.


(* Scaling, and tensoring done at this level *)
Definition TType (len : nat) := (Coef * (list Pauli))%type.

Definition TTypes := (Coef * (list Pauli))%type.

Definition ForgetT {len : nat} (t : TType len) := (t : TTypes).
Definition AssignT (len : nat) (t : TTypes) := (t : TType len).

Lemma AssignTForgetT : forall (len : nat) (t : TType len),
    AssignT len (ForgetT t) = (t : TType len).
Proof. intros. unfold AssignT, ForgetT. auto. Qed.

Lemma ForgetTAssignT : forall (len : nat) (t : TTypes),
    ForgetT (AssignT len t) = (t : TTypes).
Proof. intros. unfold AssignT, ForgetT. auto. Qed.


Definition PtoT (P : Pauli) : TType 1%nat := (C1, [P]).
Coercion PtoT : Pauli >-> TType.


Definition defaultT_Z (n : nat) : TType n := (C1, repeat gZ n).
Definition defaultT_I (n : nat) : TType n := (C1, repeat gI n).


(* we define an error TType for when things go wrong *)
Definition ErrT : TType 0 := (C1, []).



Definition proper_length_TType_nil {n : nat} (t : TType n) : Prop := length (snd t) = n.
Definition proper_length_TType {n : nat} (t : TType n) : Prop := n <> O /\ length (snd t) = n.

Lemma proper_length_TType_implies_proper_length_TType_nil : forall {n} (t : TType n),
   proper_length_TType t -> proper_length_TType_nil t.
Proof.  intros. destruct H. auto. Qed.


Lemma proper_length_TType_defaultT_I : forall (n : nat),
    n <> 0%nat -> proper_length_TType (defaultT_I n).
Proof. intros n H.
  unfold proper_length_TType.
  split; auto.
  unfold defaultT_I.
  simpl. rewrite repeat_length; auto.
Qed.

Lemma proper_length_TType_defaultT_Z : forall (n : nat),
    n <> 0%nat -> proper_length_TType (defaultT_Z n).
Proof. intros n H.
  unfold proper_length_TType.
  split; auto.
  unfold defaultT_Z.
  simpl. rewrite repeat_length; auto.
Qed.




Definition gMulT {n} (A B : TType n) : TType n :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) =>(c1 * c2 * (cBigMul (zipWith gMul_Coef g1 g2)), 
                       zipWith gMul_base g1 g2)
    end
  end.

Definition gTensorT {n m} (A : TType n) (B : TType m) : TType (n + m) :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => (c1 * c2, g1 ++ g2)
    end
  end.

Definition gScaleT {n} (c : Coef) (A : TType n) : TType n :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.

Definition gScaleTTypes (c : Coef) (A : TTypes) : TTypes :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.

Definition translate {n} (A : TType n) : Square (2 ^ n)%nat := 
  (fst A) .* ⨂ (map translate_P (snd A)).

Lemma translate_defaultT_I : forall {n : nat},
    translate (defaultT_I n) = I (2 ^ n)%nat.
Proof. intros n. unfold translate. simpl. 
  rewrite Mscale_1_l.
  induction n; auto.
  replace (2 ^ (S n))%nat with (2 * (2 ^ n))%nat by (simpl; lia).
  rewrite <- id_kron. simpl. rewrite ! IHn. 
  rewrite map_length, repeat_length; auto.
Qed.
  
Lemma gScaleT_1 : forall n (A : TType n), gScaleT C1 A = A.
Proof. intros n A. destruct A. simpl. rewrite Cmult_1_l. reflexivity. Qed.

Lemma gScaleT_comm : forall {n} (c1 c2 : Coef) (t : TType n),
    gScaleT c1 (gScaleT c2 t) = gScaleT c2 (gScaleT c1 t).
Proof. intros n c1 c2 t.
  unfold gScaleT. destruct t. f_equal. lca.
Qed.

Lemma gScaleT_merge : forall {n} (c1 c2 : Coef) (t : TType n),
    gScaleT c1 (gScaleT c2 t) = gScaleT (c1 * c2)%C t.
Proof. intros n c1 c2 t.
  unfold gScaleT. destruct t. f_equal. lca.
Qed. 

Lemma gScaleTTypes_1 : forall (A : TTypes), gScaleTTypes C1 A = A.
Proof. intros A. destruct A. simpl. rewrite Cmult_1_l. reflexivity. Qed.

Lemma gScaleTTypes_comm : forall (c1 c2 : Coef) (t : TTypes),
    gScaleTTypes c1 (gScaleTTypes c2 t) = gScaleTTypes c2 (gScaleTTypes c1 t).
Proof. intros c1 c2 t.
  unfold gScaleTTypes. destruct t. f_equal. lca.
Qed.

Lemma gScaleTTypes_merge : forall (c1 c2 : Coef) (t : TTypes),
    gScaleTTypes c1 (gScaleTTypes c2 t) = gScaleTTypes (c1 * c2)%C t.
Proof. intros c1 c2 t.
  unfold gScaleTTypes. destruct t. f_equal. lca.
Qed. 


Lemma proper_length_TType_gScaleT : forall {n : nat} (c : Coef) (t : TType n),
  proper_length_TType t -> proper_length_TType (gScaleT c t).
Proof. intros n c t H. destruct t. unfold proper_length_TType in *. simpl in *. assumption.
Qed.


(* Additive Type: list elements are added to each other *)
(* len is the number of qubits (= number of tensoring elements) *)
Definition AType (len : nat) := list (TType len).

Definition TtoA {n : nat} (t : TType n) : AType n := [t].
Coercion TtoA : TType >-> AType.

Definition AtoT {n : nat} (a : AType n) : TType n :=
  hd (defaultT_I n) a.

(* we define an error AType for when things go wrong *)
Definition ErrA : AType 0 := [].

Definition defaultA_Z (n : nat) : AType n := [defaultT_Z n].
Definition defaultA_I (n : nat) : AType n := [defaultT_I n].


Inductive proper_length_AType_nil (n : nat) : AType n -> Prop :=
| proper_length_A_nil_Base : proper_length_AType_nil n nil
| proper_length_A_nil_Cons (t : TType n) (a : AType n) : proper_length_TType t -> proper_length_AType_nil n a -> proper_length_AType_nil n (t :: a).

Arguments proper_length_AType_nil {n}.


Inductive proper_length_AType (n : nat) : AType n -> Prop :=
| proper_length_A_Sing (t : TType n) : proper_length_TType t -> proper_length_AType n (cons t nil)
| proper_length_A_Cons (t : TType n) (a : AType n) : proper_length_TType t -> proper_length_AType n a -> proper_length_AType n (t :: a).

Arguments proper_length_AType {n}.


Lemma proper_length_AType_implies_proper_length_AType_nil : forall {n} (a : AType n),
   proper_length_AType a -> proper_length_AType_nil a.
Proof. intros. induction H; constructor; try easy; constructor. Qed.


Fixpoint gTensorA  {n m : nat} (a : AType n) (b : AType m) {struct a}: AType (n+m) :=
  match a with
  | [] => []
  | h :: t => map (fun x : TType m => gTensorT h x) b ++ gTensorA t b
  end.

Fixpoint gTensorA'  {n m : nat} (a : AType n) (b : AType m) {struct b}: AType (n+m) :=
  match b with
  | [] => []
  | h :: t => map (fun x : TType n => gTensorT x h) a ++ gTensorA' a t
  end.

Fixpoint gMulA {n : nat} (a b : AType n) {struct a} : AType n :=
  match a with
  | [] => []
  | h :: t => map (fun x : TType n => gMulT h x) b ++ gMulA t b
  end.

Fixpoint gMulA' {n : nat} (a b : AType n) {struct b} : AType n :=
  match b with
  | [] => []
  | h :: t => map (fun x : TType n => gMulT x h) a ++ gMulA' a t
  end.

Lemma gMulA_nil_r : forall n (a : AType n), gMulA a [] = [].
Proof. intros n a. induction a; try easy. Qed.

Lemma gMulA'_nil_l : forall n (a : AType n), gMulA [] a = [].
Proof. intros n a. induction a; try easy. Qed.


Definition gScaleA {n : nat} (c : Coef) (a : AType n) :=
  map (fun a' => gScaleT c a') a .

Definition gAddA {n : nat} (a b : AType n) : AType n :=  a ++ b.

Definition translateA {n} (a : AType n) : Square (2 ^ n) :=
  fold_left Mplus (map translate a) Zero.

Lemma translateA_defaultA_I : forall {n : nat}, translateA (defaultA_I n) = I (2 ^ n)%nat.
Proof. intros n. unfold translateA, defaultA_I. simpl.
  rewrite Mplus_0_l. apply translate_defaultT_I.
Qed.

Lemma translateA_app : forall {n} (a1 a2 : AType n),
translateA (a1 ++ a2) = (translateA a1) .+ (translateA a2).
Proof. intros. unfold translateA. rewrite map_app.
  rewrite fold_left_Mplus_app_Zero. reflexivity.
Qed.

Lemma gScaleA_1 : forall n (A : AType n), gScaleA C1 A = A.
Proof. intros n A. induction A; simpl; try easy. rewrite gScaleT_1. rewrite IHA. reflexivity. Qed.

Lemma gScaleA_dist_app : forall {n} (c : Coef) (a1 a2 : AType n),
    gScaleA c (a1 ++ a2) = (gScaleA c a1) ++ (gScaleA c a2).
Proof. intros n c a1 a2.
  unfold gScaleA. apply map_app.
Qed.

Lemma gScaleA_comm : forall {n} (c1 c2 : Coef) (a : AType n),
    gScaleA c1 (gScaleA c2 a) = gScaleA c2 (gScaleA c1 a).
Proof. intros n c1 c2 a.
  unfold gScaleA. rewrite ! map_map.
  f_equal. apply functional_extensionality.
  intros. rewrite gScaleT_comm.
  reflexivity.
Qed.

Lemma gScaleA_merge : forall {n} (c1 c2 : Coef) (a : AType n),
    gScaleA c1 (gScaleA c2 a) = gScaleA (c1 * c2)%C a.
Proof. intros n c1 c2 a. 
  unfold gScaleA. rewrite ! map_map.
  f_equal. apply functional_extensionality.
  intros. apply gScaleT_merge.
Qed.

Lemma in_gScaleTA_mult : forall {n} (c: Coef) (t : TType n) (a : AType n),
    In t a -> In (gScaleT c t) (gScaleA c a).
Proof. intros n c t a H.
  induction a.
  - inversion H.
  - inversion H; subst; clear H.
    + simpl; auto.
    + apply IHa in H0.
      simpl; auto.
Qed.

Lemma in_gScaleTA_mult_inv : forall {n} (c: Coef) (t : TType n) (a : AType n),
    c <> C0 -> In (gScaleT c t) (gScaleA c a) -> In t a.
Proof. intros n c t a H H0. 
  apply in_gScaleTA_mult with (c := /c) in H0.
  rewrite gScaleT_merge, gScaleA_merge in H0.
  rewrite Cinv_l in H0; auto.
  rewrite gScaleT_1, gScaleA_1 in H0; auto.
Qed.




Lemma proper_length_AType_nil_gScaleA : forall {n : nat} (c : Coef) (a : AType n),
    proper_length_AType_nil a -> proper_length_AType_nil (gScaleA c a).
Proof. intros n c a H. induction H.
  - constructor.
  - simpl in *. constructor.
    + apply proper_length_TType_gScaleT. assumption.
    + assumption.
Qed.

Lemma proper_length_AType_gScaleA : forall {n : nat} (c : Coef) (a : AType n),
    proper_length_AType a -> proper_length_AType (gScaleA c a).
Proof. intros n c a H. induction H.
  - constructor. apply proper_length_TType_gScaleT. assumption.
  - simpl in *. constructor.
    + apply proper_length_TType_gScaleT. assumption.
    + assumption.
Qed.

Lemma proper_length_AType_nil_App : forall {n : nat} (a1 a2 : AType n),
    proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    proper_length_AType_nil (a1 ++ a2).
Proof. intros n a1 a2 H H0.
  induction H; simpl; try constructor; assumption.
Qed.

Lemma proper_length_AType_App : forall {n : nat} (a1 a2 : AType n),
    proper_length_AType a1 -> proper_length_AType a2 ->
    proper_length_AType (a1 ++ a2).
Proof. intros n a1 a2 H H0.
  induction H; simpl; constructor; assumption.
Qed.


Inductive Predicate (n : nat) : Type :=
| AtoPred : AType n -> Predicate n
| Cap : list (AType n) -> Predicate n
| Sep : (list nat) * (list (list TTypes)) * (list nat) -> Predicate n
| Cup : Predicate n -> Predicate n -> Predicate n
| Err : Predicate n.

Coercion AtoPred : AType >-> Predicate.

Arguments AtoPred {n}.
Arguments Cap {n}.
Arguments Sep {n}.
Arguments Cup {n}.
Arguments Err {n}.


Definition defaultP_Z (n : nat) : Predicate n := AtoPred (defaultA_Z n).
Definition defaultP_I (n : nat) : Predicate n := AtoPred (defaultA_I n).


Fixpoint pad_Sep_listP (Lp : list Pauli) (Ln : list nat) (m : nat) :=
  match Ln with
  | [] => repeat gI m
  | n :: Ln' => 
    match Lp with
    | [] => repeat gI m
    | p :: Lp' => switch (pad_Sep_listP Lp' Ln' m) p n
    end
  end.

Lemma pad_Sep_listP_length : forall (Lp : list Pauli) (Ln : list nat) (m : nat),
    length (pad_Sep_listP Lp Ln m) = m.
Proof. intros Lp Ln m.
  gen Lp m.
  induction Ln.
  - induction Lp; intros; simpl; 
      rewrite repeat_length; auto.
  - induction Lp; intros; simpl;
      try rewrite repeat_length; auto.
    rewrite switch_len.
    apply IHLn.
Qed. 

Lemma pad_Sep_listP_nil_l : forall (Ln : list nat) (m : nat),
  pad_Sep_listP [] Ln m = repeat gI m.
Proof. intros Ln m.
  induction Ln; auto.
Qed.

Lemma pad_Sep_listP_nil_r : forall (Lp : list Pauli) (m : nat),
  pad_Sep_listP Lp [] m = repeat gI m.
Proof. intros Lp m.
  induction Lp; auto.
Qed.

Lemma pad_Sep_listP_nth : forall (i m : nat) (Ln : list nat) (Lp : list Pauli),
    NoDup Ln -> (i < length Ln)%nat -> length Ln = length Lp -> incl Ln (List.seq 0 m) ->
    nth (nth i Ln 0%nat) (pad_Sep_listP Lp Ln m) gI = nth i Lp gI.
Proof. intros i m Ln Lp H H0 H1 H2.
  gen Ln Lp i.
    induction m.
    - induction Ln; intros; simpl in *.
      + inversion H0.
      + apply incl_cons_inv in H2.
        destruct H2.
        inversion H2.
    - induction Ln; intros.
      + inversion H0.
      + destruct Lp.
        * rewrite pad_Sep_listP_nil_l.
          rewrite nth_repeat.
          destruct i; auto.
        * simpl.
          destruct i.
          -- rewrite nth_switch_hit; auto.
             rewrite pad_Sep_listP_length.
             apply incl_cons_inv in H2.
             destruct H2.
             rewrite in_seq in H2.
             lia.
          -- rewrite NoDup_cons_iff in H.
             destruct H.
             bdestruct (nth i Ln 0%nat =? a)%nat.
             ++ subst. 
                simpl in H0.
                rewrite <- Nat.succ_lt_mono in H0.
                assert (In (nth i Ln 0%nat) Ln).
                { apply nth_In; lia. }
                contradiction.
             ++ simpl in H0.
                rewrite <- Nat.succ_lt_mono in H0.
                rewrite nth_switch_miss; auto.
                rewrite IHLn; auto.
                apply incl_cons_inv in H2.
                destruct H2; auto.
Qed.

Lemma pad_Sep_listP_not_in : forall (m k : nat) (Ln : list nat) (Lp : list Pauli),
    NoDup Ln -> length Ln = length Lp -> incl Ln (List.seq 0 m) ->
    ~ In k Ln -> nth k (pad_Sep_listP Lp Ln m) gI = gI.
Proof. intros m k Ln Lp H H0 H1 H2.
  bdestruct (k <? m).
  - destruct Lp as [ | p Lp'].
    + rewrite pad_Sep_listP_nil_l.
      rewrite nth_repeat; auto.
    + destruct Ln as [ | n Ln'].
      * rewrite pad_Sep_listP_nil_r.
        rewrite nth_repeat; auto.
      * simpl.
        bdestruct (k =? n)%nat.
        -- subst.
           apply not_in_cons in H2.
           destruct H2. contradiction.
        -- rewrite nth_switch_miss; auto.
           apply incl_cons_inv in H1.
           destruct H1.
           apply not_in_cons in H2.
           destruct H2.
           rewrite NoDup_cons_iff in H.
           destruct H.
           clear H. simpl in H0. clear H2. clear H1. clear H4.
           clear n. clear p.
           apply Nat.succ_inj in H0.
           gen Lp'.
           induction Ln'; intros.
           ++ rewrite pad_Sep_listP_nil_r, nth_repeat; auto.
           ++ destruct Lp'.
              ** rewrite pad_Sep_listP_nil_l, nth_repeat; auto.
              ** simpl in H0. apply Nat.succ_inj in H0.
                 rewrite NoDup_cons_iff in H7.
                 destruct H7.
                 apply incl_cons_inv in H5.
                 destruct H5.
                 rewrite not_in_cons in H6.
                 destruct H6.
                 simpl. 
                 rewrite nth_switch_miss; auto.
  - rewrite nth_overflow; auto; rewrite pad_Sep_listP_length; lia.
Qed.

Lemma pad_Sep_listP_seq : forall (Lp : list Pauli) (m : nat),
    length Lp = m -> pad_Sep_listP Lp (List.seq 0 m) m = Lp.
Proof. intros Lp m H.
  apply nth_ext with (d := gI) (d' := gI).
  - rewrite pad_Sep_listP_length, H; auto.
  - intros. rewrite pad_Sep_listP_length in H0.
    assert (nth n (List.seq 0 m) 0%nat = n).
    { rewrite seq_nth; auto. }
    setoid_rewrite <- H1 at 1.
    rewrite pad_Sep_listP_nth; auto.
    apply seq_NoDup.
    rewrite seq_length; lia.
    rewrite seq_length, H; lia.
    apply incl_refl.
Qed.    


Definition unpad_Sep_listP (Lp : list Pauli) (Ln : list nat) := map (fun n => nth n Lp gI) Ln.

Lemma unpad_pad_Sep_listP : forall (Lp : list Pauli) (Ln : list nat) (m : nat),
    NoDup Ln -> length Ln = length Lp -> incl Ln (List.seq 0 m) ->
    unpad_Sep_listP (pad_Sep_listP Lp Ln m) Ln = Lp.
Proof. intros Lp Ln m H H0 H1. 
  unfold unpad_Sep_listP.
  apply nth_ext with (d := gI) (d' := gI).
  - rewrite map_length; auto.
  - intros n H2.
    rewrite map_length in H2.
    assert ((fun n0 : nat => nth n0 (pad_Sep_listP Lp Ln m) gI) m = gI).
    { assert (~ In m Ln).
      { intro. apply H1 in H3. rewrite in_seq in H3. lia. }
      rewrite pad_Sep_listP_not_in; auto. }
    rewrite <- H3 at 1.
    rewrite map_nth with (d := m).
    rewrite nth_indep with (d' := 0%nat); auto.
    rewrite pad_Sep_listP_nth; auto.
Qed.

Definition pad_Sep_TTypes (t : TTypes) (l : list nat) (m : nat) : TType m := 
  (fst t, pad_Sep_listP (snd t) l m).

Definition pad_Sep_TType {n : nat} (t : TType n) (l : list nat) (m : nat) : TType m := 
  (fst t, pad_Sep_listP (snd t) l m).

Lemma pad_Sep_TType_seq : forall {n : nat} (t : TType n) (m : nat),
    proper_length_TType t -> m = n -> pad_Sep_TType t (List.seq 0 m) m = t.
Proof. intros n t m H H0.
  subst.
  destruct t as [c l]; simpl in *.
  unfold pad_Sep_TType; simpl.
  rewrite pad_Sep_listP_seq; auto.
  destruct H as [H H']; simpl in *; auto.
Qed.

Lemma proper_length_TType_pad_Sep_TType : forall {n : nat} (t : TType n) (l : list nat) (m : nat),
    m <> 0%nat -> proper_length_TType (pad_Sep_TType t l m).
Proof. intros n t l m H.
  destruct t.
  unfold proper_length_TType, pad_Sep_TType in *.
  simpl in *.
  split; try rewrite pad_Sep_listP_length; auto.
Qed.


Definition unpad_Sep_TTypes (t : TTypes) (l : list nat) : TType (length l) :=
  (fst t, unpad_Sep_listP (snd t) l).

Definition unpad_Sep_TType {n : nat} (t : TType n) (l : list nat) : TType (length l) :=
  (fst t, unpad_Sep_listP (snd t) l).

Lemma unpad_pad_Sep_TType : forall {n : nat} (t : TType n) (l : list nat) (m : nat),
    proper_length_TType t ->
    NoDup l -> length l = n -> incl l (List.seq 0 m) ->
    unpad_Sep_TType (pad_Sep_TType t l m) l = t.
Proof. intros n t l m H H0 H1 H2.
  unfold unpad_Sep_TType, pad_Sep_TType.
  inversion H. subst. destruct t. simpl in *. f_equal.
  apply unpad_pad_Sep_listP; auto.
Qed.
  

Definition pad_Sep_AType {n : nat} (a : AType n) (l : list nat) (m : nat) : AType m := 
  map (fun t => pad_Sep_TType t l m) a.

Lemma pad_Sep_AType_seq_nil : forall {n : nat} (a : AType n) (m : nat),
    proper_length_AType_nil a -> m = n -> pad_Sep_AType a (List.seq 0 m) m = a.
Proof. intros n a m H H0.
  subst.
  unfold pad_Sep_AType.
  induction a; auto.
  inversion H; subst.
  simpl. f_equal; auto.
  apply pad_Sep_TType_seq; auto.
Qed.

Lemma pad_Sep_AType_seq : forall {n : nat} (a : AType n) (m : nat),
    proper_length_AType a -> m = n -> pad_Sep_AType a (List.seq 0 m) m = a.
Proof. intros. subst.
  apply pad_Sep_AType_seq_nil; auto.
  apply proper_length_AType_implies_proper_length_AType_nil; auto.
Qed.

Lemma proper_length_AType_nil_pad_Sep_AType : forall {n : nat} (a : AType n) (l : list nat) (m : nat),
    m <> 0%nat -> proper_length_AType_nil (pad_Sep_AType a l m).
Proof. intros n a l m H.
  unfold pad_Sep_AType in *.
  induction a.
  - simpl. constructor.
  - simpl. constructor; auto.
    apply proper_length_TType_pad_Sep_TType; auto.
Qed.

Lemma proper_length_AType_pad_Sep_AType : forall {n : nat} (a : AType n) (l : list nat) (m : nat),
    m <> 0%nat -> a <> [] -> proper_length_AType (pad_Sep_AType a l m).
Proof. intros n a l m H H0.
  unfold pad_Sep_AType in *.
  induction a.
  - simpl. contradiction.
  - simpl.
    destruct a0.
    + simpl. constructor. 
      apply proper_length_TType_pad_Sep_TType; auto.
    + constructor; auto.
      * apply proper_length_TType_pad_Sep_TType; auto.
      * assert (t :: a0 <> []). { intro. inversion H1. }
        apply IHa in H1; auto.
Qed.


Definition unpad_Sep_AType {n : nat} (a : AType n) (l : list nat) : AType (length l) :=
  map (fun t => unpad_Sep_TType t l) a.

Lemma unpad_pad_Sep_AType : forall {n : nat} (a : AType n) (l : list nat) (m : nat),
    proper_length_AType a ->
    NoDup l -> length l = n -> incl l (List.seq 0 m) ->
    unpad_Sep_AType (pad_Sep_AType a l m) l = a.
Proof. intros n a l m H H0 H1 H2.
  unfold unpad_Sep_AType, pad_Sep_AType.
  rewrite map_map.
  induction H; subst; simpl in *; f_equal; try apply unpad_pad_Sep_TType; auto.
Qed.


Definition translateP {n} (p : Predicate n) :=
  match p with
  | AtoPred a => translateA a
  | _ => Zero
  end.

Lemma translateP_defaultP_I : forall {n : nat}, 
    (0 < n)%nat ->  translateP (defaultP_I n) = I (2 ^ n)%nat.
Proof. intros n H. 
  unfold translateP, defaultP_I. 
  unfold defaultP_I.
  apply translateA_defaultA_I; auto.
Qed.

(* you cannot multiply cap or cup types 
   so any of these options returns Err *)
Definition mul {n} (A B : Predicate n) : Predicate n :=
  match A with
  | AtoPred a =>
    match B with
    | AtoPred b => AtoPred (gMulA a b)
    | _ => Err
    end
  | _ => Err
  end.

Definition add {n} (A B : Predicate n) : Predicate n :=
  match A with
  | AtoPred a =>
    match B with
    | AtoPred b => AtoPred (gAddA a b)
    | _ => Err
    end
  | _ => Err
  end.

Definition tensor {n m} (A : Predicate n) (B : Predicate m): Predicate (n + m) :=
  match A with
  | AtoPred a =>
      match B with
      | AtoPred b => AtoPred (gTensorA a b)
      | _ => Err
      end
  | _ => Err
  end.

(** We define scale to work for all predicate structures.
This will allow - - p = p for any predicate p. **)
Fixpoint scale {n} (c : Coef) (A : Predicate n) : Predicate n :=
  match A with
  | AtoPred a => AtoPred (gScaleA c a)
  | Cap la => Cap (map (gScaleA c) la)
  | Sep Ln_LLT_Perm => Sep (fst (fst Ln_LLT_Perm), (map (fun LT => map (fun T => gScaleTTypes c T) LT) (snd (fst Ln_LLT_Perm))), snd Ln_LLT_Perm)
  | Cup a b => Cup (scale c a) (scale c b)
  | Err => Err
  end.

Lemma scale_merge : forall {n : nat} (c1 c2 : Coef) (P : Predicate n),
    scale c2 (scale c1 P) = scale (c2 * c1) P.
Proof. intros n c1 c2 P.
  induction P; simpl; try rewrite gScaleA_merge; try rewrite IHP1, IHP2; auto.
  - rewrite map_map. do 2 f_equal.
    apply functional_extensionality; intros.
    rewrite gScaleA_merge; auto.
  - rewrite ! map_map. do 4 f_equal.
      apply functional_extensionality; intros.
      rewrite map_map. f_equal.
      apply functional_extensionality; intros.
      rewrite gScaleTTypes_merge; auto.
Qed.

#[export] Hint Rewrite gMulA_nil_r gMulA'_nil_l gScaleT_1 gScaleA_1 : typing_db.

Notation "- A" := (scale (Copp C1) A)  (at level 35, right associativity) : Predicate_scope.
Notation "+i A" := (scale Ci A)  (at level 35, right associativity) : Predicate_scope.
Notation "-i A" := (scale (Copp Ci) A)  (at level 35, right associativity) : Predicate_scope.

Lemma neg_inv : forall {n : nat} (p : Predicate n), (- (- p)) = p.
Proof. intros n p.  
  induction p; simpl; try (rewrite IHp1, IHp2); try rewrite IHp; auto.
  - rewrite gScaleA_merge.
    replace (- C1 * - C1) with C1 by lca.
    rewrite gScaleA_1; auto.
  - rewrite map_map. f_equal.
    assert (H : (fun x : AType n => gScaleA (- C1)%C (gScaleA (- C1)%C x)) 
                = (fun x : AType n => x)).
    { apply functional_extensionality. intros.
      rewrite gScaleA_merge.
      assert (H : (- C1 * - C1) = C1). { lca. }
      rewrite H, gScaleA_1. auto. }
    setoid_rewrite H. rewrite map_id. auto.
  - f_equal. do 2 destruct p. simpl. do 2 f_equal.
    rewrite ! map_map. setoid_rewrite <- map_id at 6.
    f_equal. apply functional_extensionality; intros.
    rewrite map_map. setoid_rewrite <- map_id at 3.
    f_equal. apply functional_extensionality; intros.
    rewrite gScaleTTypes_merge.
    replace ((- C1) * (- C1))%C with C1 by lca.
    rewrite gScaleTTypes_1. auto.
Qed.

Infix "⊗'" := tensor (at level 39, left associativity) : Predicate_scope.
Infix "*'" := mul (at level 40, left associativity) : Predicate_scope.
Infix "·'" := scale (at level 43, left associativity) : Predicate_scope.
Infix "+'" := add (at level 50, left associativity) : Predicate_scope.

Notation "⋂ la" := (Cap la) (at level 61, left associativity) : Predicate_scope.
Notation "A ⊍ B" := (Cup A B) (at level 61, left associativity) : Predicate_scope.
Notation "∩ Ln_LLT_Perm" := (Sep Ln_LLT_Perm) (at level 30, no associativity) : Predicate_scope.


Notation tI := (C1, [gI]).
Notation tX := (C1, [gX]).
Notation tY := (C1, [gY]).
Notation tZ := (C1, [gZ]).
Notation tII := (C1, [gI; gI]).
Notation tXI := (C1, [gX; gI]).
Notation tIX := (C1, [gI; gX]).
Notation tXX := (C1, [gX; gX]).
Notation tYI := (C1, [gY; gI]).
Notation tIY := (C1, [gI; gY]).
Notation tYY := (C1, [gY; gY]).
Notation tYX := (C1, [gY; gX]).
Notation tXY := (C1, [gX; gY]).
Notation tZY := (C1, [gZ; gY]).
Notation tYZ := (C1, [gY; gZ]).
Notation tXZ := (C1, [gX; gZ]).
Notation tZX := (C1, [gZ; gX]).
Notation tZI := (C1, [gZ; gI]).
Notation tIZ := (C1, [gI; gZ]).
Notation tZZ := (C1, [gZ; gZ]).
Notation mtI := ((- C1)%C, [gI]).
Notation mtX := ((- C1)%C, [gX]).
Notation mtY := ((- C1)%C, [gY]).
Notation mtZ := ((- C1)%C, [gZ]).
Notation mtII := ((- C1)%C, [gI; gI]).
Notation mtXI := ((- C1)%C, [gX; gI]).
Notation mtIX := ((- C1)%C, [gI; gX]).
Notation mtXX := ((- C1)%C, [gX; gX]).
Notation mtYI := ((- C1)%C, [gY; gI]).
Notation mtIY := ((- C1)%C, [gI; gY]).
Notation mtYY := ((- C1)%C, [gY; gY]).
Notation mtYX := ((- C1)%C, [gY; gX]).
Notation mtXY := ((- C1)%C, [gX; gY]).
Notation mtZY := ((- C1)%C, [gZ; gY]).
Notation mtYZ := ((- C1)%C, [gY; gZ]).
Notation mtXZ := ((- C1)%C, [gX; gZ]).
Notation mtZX := ((- C1)%C, [gZ; gX]).
Notation mtZI := ((- C1)%C, [gZ; gI]).
Notation mtIZ := ((- C1)%C, [gI; gZ]).
Notation mtZZ := ((- C1)%C, [gZ; gZ]).

Notation aI := [tI].
Notation aX := [tX].
Notation aY := [tY].
Notation aZ := [tZ].
Notation aII := [tII].
Notation aXI := [tXI].
Notation aIX := [tIX].
Notation aXX := [tXX].
Notation aYI := [tYI].
Notation aIY := [tIY].
Notation aYY := [tYY].
Notation aYX := [tYX].
Notation aXY := [tXY].
Notation aZY := [tZY].
Notation aYZ := [tYZ].
Notation aXZ := [tXZ].
Notation aZX := [tZX].
Notation aZI := [tZI].
Notation aIZ := [tIZ].
Notation aZZ := [tZZ].
Notation maI := [mtI].
Notation maX := [mtX].
Notation maY := [mtY].
Notation maZ := [mtZ].
Notation maII := [mtII].
Notation maXI := [mtXI].
Notation maIX := [mtIX].
Notation maXX := [mtXX].
Notation maYI := [mtYI].
Notation maIY := [mtIY].
Notation maYY := [mtYY].
Notation maYX := [mtYX].
Notation maXY := [mtXY].
Notation maZY := [mtZY].
Notation maYZ := [mtYZ].
Notation maXZ := [mtXZ].
Notation maZX := [mtZX].
Notation maZI := [mtZI].
Notation maIZ := [mtIZ].
Notation maZZ := [mtZZ].
Notation aXY2 := (gScaleA (C1/√2)%C [(C1, [gX]); (C1, [gY])]).
Notation aYX2 := (gScaleA (C1/√2)%C [(C1, [gY]); (C1, [gX])]).
Notation aX2Y2 := [((C1/√2)%C, [gX]); ((C1/√2)%C, [gY])].
Notation aY2X2 := [((C1/√2)%C, [gY]); ((C1/√2)%C, [gX])].
Notation aYmX2 := (gScaleA (C1/√2)%C [(C1, [gY]); ((- C1)%C, [gX])]).
Notation amXY2 := (gScaleA (C1/√2)%C [((- C1)%C, [gX]); (C1, [gY])]).
Notation aY2mX2 := [((C1/√2)%C, [gY]); (((C1/√2) * (- C1))%C, [gX])].
Notation amX2Y2 := [(((C1/√2) * (- C1))%C, [gX]); ((C1/√2)%C, [gY])].

Notation pI := (@AtoPred 1 aI).
Notation pX := (@AtoPred 1 aX).
Notation pY := (@AtoPred 1 aY).
Notation pZ := (@AtoPred 1 aZ).
Notation pII := (@AtoPred 2 aII).
Notation pXI := (@AtoPred 2 aXI).
Notation pIX := (@AtoPred 2 aIX).
Notation pXX := (@AtoPred 2 aXX).
Notation pYI := (@AtoPred 2 aYI).
Notation pIY := (@AtoPred 2 aIY).
Notation pYY := (@AtoPred 2 aYY).
Notation pYX := (@AtoPred 2 aYX).
Notation pXY := (@AtoPred 2 aXY).
Notation pZY := (@AtoPred 2 aZY).
Notation pYZ := (@AtoPred 2 aYZ).
Notation pXZ := (@AtoPred 2 aXZ).
Notation pZX := (@AtoPred 2 aZX).
Notation pZI := (@AtoPred 2 aZI).
Notation pIZ := (@AtoPred 2 aIZ).
Notation pZZ := (@AtoPred 2 aZZ).
Notation mpI := (@AtoPred 1 maI).
Notation mpX := (@AtoPred 1 maX).
Notation mpY := (@AtoPred 1 maY).
Notation mpZ := (@AtoPred 1 maZ).
Notation mpII := (@AtoPred 2 maII).
Notation mpXI := (@AtoPred 2 maXI).
Notation mpIX := (@AtoPred 2 maIX).
Notation mpXX := (@AtoPred 2 maXX).
Notation mpYI := (@AtoPred 2 maYI).
Notation mpIY := (@AtoPred 2 maIY).
Notation mpYY := (@AtoPred 2 maYY).
Notation mpYX := (@AtoPred 2 maYX).
Notation mpXY := (@AtoPred 2 maXY).
Notation mpZY := (@AtoPred 2 maZY).
Notation mpYZ := (@AtoPred 2 maYZ).
Notation mpXZ := (@AtoPred 2 maXZ).
Notation mpZX := (@AtoPred 2 maZX).
Notation mpZI := (@AtoPred 2 maZI).
Notation mpIZ := (@AtoPred 2 maIZ).
Notation mpZZ := (@AtoPred 2 maZZ).
Notation pXY2 := (@AtoPred 1 aXY2).
Notation pYX2 := (@AtoPred 1 aYX2).
Notation pX2Y2 := (@AtoPred 1 aX2Y2).
Notation pY2X2 := (@AtoPred 1 aY2X2).
Notation pYmX2 := (@AtoPred 1 aYmX2).
Notation pmXY2 := (@AtoPred 1 amXY2).
Notation pY2mX2 := (@AtoPred 1 aY2mX2).
Notation pmX2Y2 := (@AtoPred 1 amX2Y2).


Lemma Y_is_iXZ : pY = (+i (pX *' pZ)).
Proof. simpl.
  unfold gMulA; simpl. compute.
  autorewrite with R_db.
  assert (R0 = (-R0)%R). { lra. }
  rewrite <- H.
  constructor.
Qed.

#[export] Hint Resolve Y_is_iXZ : wfpt_db.





Lemma translate_gMulT: forall (l l0 : list Pauli) (a b : Coef), length l0 = length l -> translate (gMulT (a, l) (b, l0)) =  (a * b .* ((⨂ map translate_P l) × (⨂ map translate_P l0)))%M.
Proof. induction l.
    - intros. simpl in *. rewrite length_zero_iff_nil in H. rewrite H. simpl. unfold translate, cBigMul, gMul_Coef, zipWith. simpl. rewrite Cmult_1_r.  lma'.
    - intros. simpl in *. destruct l0; try discriminate.
      simpl in *. inversion H.
      rewrite ! map_length. 
      assert (2 ^ length l + (2 ^ length l + 0) = 2 ^ (S (length l)))%nat. { simpl. easy. }
      rewrite ! H1.
      rewrite H0.
      assert (@Mmult (2 ^ S (length l)) (2 ^ S (length l)) (2 ^ S (length l)) (translate_P a ⊗ (⨂ map translate_P l)) (translate_P p ⊗ (⨂ map translate_P l0)) =  (@Mmult 2 2 2 (translate_P a) (translate_P p)) ⊗ (@Mmult (2 ^ length l) (2 ^ length l) (2 ^ length l) (⨂ map translate_P l) (⨂ map translate_P l0))).
      { rewrite ! map_length. rewrite ! H1.
        apply kron_mixed_product' with (A:= translate_P a) (B:= big_kron (map translate_P l)) (C:= translate_P p) (D:= big_kron (map translate_P l0)); easy. } 
      rewrite ! map_length in H2.
      setoid_rewrite kron_mixed_product.
      rewrite ! map_length in IHl.
      setoid_rewrite <- Mscale_kron_dist_r with (x:= a0 * b) at 1.
      rewrite <- IHl; try easy.
      unfold translate, cBigMul, zipWith, gMul_Coef, uncurry. simpl. rewrite ! fold_left_Cmult.

      setoid_rewrite <- Mscale_kron_dist_r.
      rewrite <- Mscale_assoc.
      setoid_rewrite Mscale_kron_dist_r.
      setoid_rewrite <- Mscale_kron_dist_l.
      setoid_rewrite Mscale_kron_dist_r.
      rewrite <- Mscale_assoc.
      setoid_rewrite <- Mscale_kron_dist_r.
      setoid_rewrite Mscale_kron_dist_l.
      setoid_rewrite Mscale_assoc.
      setoid_rewrite <- Mscale_kron_dist_l.
      symmetry.
      rewrite <- Mscale_assoc.

assert (translate_P a × translate_P p
  ⊗ (a0 * b
     .* (fold_left Cmult
           (map
              (fun p0 : Pauli * Pauli =>
               let (x, y) := p0 in
               match x with
               | gI => C1
               | gX => match y with
                       | gY => Ci
                       | gZ => (- Ci)%C
                       | _ => C1
                       end
               | gY => match y with
                       | gX => (- Ci)%C
                       | gZ => Ci
                       | _ => C1
                       end
               | gZ => match y with
                       | gX => Ci
                       | gY => (- Ci)%C
                       | _ => C1
                       end
               end) (combine l l0)) C1
         .* (⨂ map translate_P
                 (map (fun p0 : Pauli * Pauli => let (x, y) := p0 in gMul_base x y)
                    (combine l l0)))))%M
        =
          ((a0 * b) .* (translate_P a × translate_P p)
  ⊗ ((fold_left Cmult
           (map
              (fun p0 : Pauli * Pauli =>
               let (x, y) := p0 in
               match x with
               | gI => C1
               | gX => match y with
                       | gY => Ci
                       | gZ => (- Ci)%C
                       | _ => C1
                       end
               | gY => match y with
                       | gX => (- Ci)%C
                       | gZ => Ci
                       | _ => C1
                       end
               | gZ => match y with
                       | gX => Ci
                       | gY => (- Ci)%C
                       | _ => C1
                       end
               end) (combine l l0)) C1
         .* (⨂ map translate_P
                 (map (fun p0 : Pauli * Pauli => let (x, y) := p0 in gMul_base x y)
                    (combine l l0))))))%M).
{ 
  rewrite Mscale_kron_dist_r.
  rewrite <- Mscale_kron_dist_l.
  easy.
}
rewrite ! map_length in H3.
rewrite ! combine_length in H3.
rewrite H1 in H3.
replace (Init.Nat.min (length l) (length l)) with (length l) in H3 by lia.
setoid_rewrite H3.
rewrite ! map_length.
rewrite ! combine_length.
rewrite H1.
replace (Init.Nat.min (length l) (length l)) with (length l) by lia.
f_equal.
destruct a, p; simpl; try lma'.
Qed.

Lemma translate_gMulT_mult : forall {n : nat} (t1 t2 : TType n), 
    proper_length_TType t1 -> proper_length_TType t2 -> 
    translate (gMulT t1 t2) =  translate t1 × translate t2.
Proof. intros n t1 t2 H H0.
  unfold translate at 2. unfold translate at 2. 
  destruct H, H0, t1, t2. 
  simpl in H1, H2. 
  pose translate_gMulT as e.
  rewrite <- H1 in H2.
  specialize (e l l0 c c0 H2).
  setoid_rewrite e.
  simpl. subst.
  rewrite <- Mscale_assoc.
  rewrite <- Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  f_equal. all: rewrite map_length; auto.
Qed.

Lemma translate_gTensorT : forall {n m : nat} (t1 : TType n) (t2 : TType m),
    length (snd t1) = n -> length (snd t2) = m ->
    translate (gTensorT t1 t2) = translate t1 ⊗ translate t2.
Proof. intros n m t1 t2 H H0.
  destruct t1, t2. simpl in *.
  unfold translate. simpl.
  rewrite ! map_length, ! H, ! H0, ! app_length.
  assert ((2 ^ n) * (2 ^ m) = 2 ^ (n + m))%nat.
  { rewrite <- Nat.pow_add_r. auto. }
  rewrite Mscale_kron_dist_l, Mscale_kron_dist_r.
  distribute_scale. f_equal.
  1-2: rewrite H, H0, H1; auto.
  rewrite map_app.
  rewrite big_kron_app; intros.
  - f_equal. all: rewrite map_length; try rewrite H; try rewrite H0; auto.
  - bdestruct (i <? n).
    + rewrite nth_indep with (d' := translate_P gI).
      2: rewrite map_length, H; lia.
      rewrite map_nth. 
      destruct (nth i l gI); simpl; auto with wf_db.
    + rewrite nth_overflow; auto with wf_db; rewrite map_length; lia.
  - bdestruct (i <? m).
    + rewrite nth_indep with (d' := translate_P gI).
      2: rewrite map_length, H0; lia.
      rewrite map_nth. 
      destruct (nth i l gI); simpl; auto with wf_db.
    + rewrite nth_overflow; auto with wf_db; rewrite map_length; lia.
Qed.

Lemma translate_gScaleT : forall {n} (c : Coef) (t : TType n),
    proper_length_TType t -> translate (gScaleT c t) = c .* translate t.
Proof. intros.  destruct H. destruct t. unfold gScaleT. unfold translate. simpl in *.
  rewrite map_length. rewrite H0. rewrite Mscale_assoc. reflexivity.
Qed.

Lemma WF_Matrix_translate_nil : forall {n : nat} (t : TType n), proper_length_TType_nil t -> WF_Matrix (translate t).
Proof. intros. destruct t. unfold translate. destruct H. simpl in *.
  rewrite map_length. apply WF_scale. 
  rewrite <- map_length with (f := translate_P).
  apply WF_big_kron with (A := I 2).
  intros.
  rewrite map_nth with (f := translate_P) (d := gI).
  auto with wf_db.
Qed.

Lemma WF_translate : forall {n : nat} (t : TType n), proper_length_TType t -> WF_Matrix (translate t).
Proof. intros. apply proper_length_TType_implies_proper_length_TType_nil in H.
  apply WF_Matrix_translate_nil.
  assumption.
Qed.

#[export] Hint Resolve WF_Matrix_translate_nil WF_translate : wf_db.





Inductive trace_zero_syntax : list Pauli -> Prop :=
| trace_zero_syntax_X : trace_zero_syntax [gX]
| trace_zero_syntax_Y : trace_zero_syntax [gY]
| trace_zero_syntax_Z : trace_zero_syntax [gZ]
| trace_zero_syntax_L : forall (A B : list Pauli), trace_zero_syntax A -> trace_zero_syntax (A++B)
| trace_zero_syntax_R : forall (A B : list Pauli), trace_zero_syntax B -> trace_zero_syntax (A++B).

Lemma trace_zero_syntax_implies_trace_zero : forall (A : list Pauli),
    trace_zero_syntax A -> trace (⨂ map translate_P A) = 0.
Proof. intros. induction H.
  1-3 : matrix_compute.
  1-2 : rewrite map_app; rewrite big_kron_app; try apply WF_Matrix_nth_Pauli;
  rewrite ! app_length;
  rewrite ! map_length;
  assert (H0 : (2 ^ (length A + length B))%nat = (2 ^ (length A) * 2 ^ (length B))%nat).
  1,3: rewrite Nat.pow_add_r; reflexivity.
  1-2: rewrite H0;
  rewrite trace_kron_dist;
  rewrite map_length in IHtrace_zero_syntax;
  try rewrite IHtrace_zero_syntax;
  try rewrite Cmult_0_l; try rewrite Cmult_0_r;
  try reflexivity.
  1-2: intro; rewrite Nat.pow_eq_0_iff in H1; destruct H1; lia.
Qed.
  
Definition coef_plus_minus_1 {n : nat} (t : TType n) := fst t = C1 \/ fst t = Copp C1.

Lemma translate_Hermitian : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t -> adjoint (translate t) = translate t.
Proof. intros n t H H0.
  destruct H, t. unfold translate. simpl in *.
  pose (list_Pauli_Hermitian l) as H2.
  rewrite map_length in *.
  rewrite H1 in *.
  rewrite Mscale_adj.
  rewrite H2.
  f_equal.
  destruct H0; simpl in *; subst; lca.
Qed.

Lemma coef_plus_minus_1_defaultT_I : forall (n : nat),
    coef_plus_minus_1 (defaultT_I n).
Proof. intros n.
  unfold coef_plus_minus_1, defaultT_I.
  left. auto.
Qed.

Lemma coef_plus_minus_1_defaultT_Z : forall (n : nat),
    coef_plus_minus_1 (defaultT_Z n).
Proof. intros n.
  unfold coef_plus_minus_1, defaultT_Z.
  left. auto.
Qed.

Definition coef_size_1 {n : nat} (t : TType n) := (fst t) * (fst t)^* = C1.

Lemma coef_plus_minus_1_implies_coef_size_1 : forall {n : nat} (t : TType n),
    coef_plus_minus_1 t -> coef_size_1 t.
Proof. intros n t H.
  unfold coef_plus_minus_1, coef_size_1 in *.
  destruct t. simpl in *.
  destruct H; subst; lca.
Qed.

Lemma coef_size_1_defaultT_I : forall (n : nat),
    coef_size_1 (defaultT_I n).
Proof. intros n.
  apply coef_plus_minus_1_implies_coef_size_1.
  apply coef_plus_minus_1_defaultT_I.
Qed.

Lemma coef_size_1_defaultT_Z : forall (n : nat),
    coef_size_1 (defaultT_Z n).
Proof. intros n.
  apply coef_plus_minus_1_implies_coef_size_1.
  apply coef_plus_minus_1_defaultT_Z.
Qed.

Lemma coef_size_1_gMultT_preserve : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    coef_size_1 t1 -> coef_size_1 t2 -> coef_size_1 (gMulT t1 t2).
Proof. intros n t1 t2 H H0 H1 H2.
  unfold coef_size_1, gMulT in *.
  destruct t1, t2; simpl in *.
  rewrite ! Cconj_mult_distr.
  setoid_rewrite Cmult_comm at 2.
  setoid_rewrite Cmult_comm at 5.
  assert (cBigMul (zipWith gMul_Coef l l0) * (c * c0) *
            (c0 ^* * c ^* * (cBigMul (zipWith gMul_Coef l l0)) ^* ) =
               cBigMul (zipWith gMul_Coef l l0) * (c * (c0 *
                 c0 ^* ) * c ^* ) * (cBigMul (zipWith gMul_Coef l l0)) ^* ).
  { rewrite ! Cmult_assoc. auto. }
  rewrite H3.
  rewrite H2. rewrite Cmult_1_r. rewrite H1. rewrite Cmult_1_r.
  destruct H, H0. simpl in H4, H5. rewrite <- H5 in H4, H.
  clear - H H4.
  gen l0. induction l; intros. destruct l0; try contradiction; try discriminate.
  destruct l0; try discriminate. clear H. simpl in H4. apply Nat.succ_inj in H4.
  destruct l. destruct l0; try discriminate.
  unfold cBigMul, zipWith, uncurry, gMul_Coef; destruct a, p; lca.
  destruct l0; try discriminate. simpl in H4. apply Nat.succ_inj in H4.
  assert (length (p1 :: l0) <> 0%nat) by (simpl; auto).
  assert (length (p0 :: l) = length (p1 :: l0)) by (simpl; lia).
  specialize (IHl (p1 :: l0) H H0).
  unfold zipWith in *. simpl in *. 
  unfold uncurry in *; simpl. 
  destruct a, p; unfold cBigMul in *; simpl in *; rewrite <- ! Cmult_assoc;
  rewrite fold_left_Cmult in *;  repeat rewrite Cmult_1_l; auto.
  all : try (rewrite <- IHl at 3; lca).
Qed.

Lemma translate_mult_adjoint_inv : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_size_1 t -> (translate t) × (translate t)† = I (2 ^ n)%nat.
Proof. intros n t H H0. 
  unfold translate.
  unfold proper_length_TType, coef_size_1 in *.
  destruct H, t.
  simpl in *. 
  rewrite ! map_length, ! H1.
  rewrite Mscale_adj.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  rewrite H0.
  rewrite Mscale_1_l.
  clear H0.
  gen n. induction l; intros.
  - simpl in *. subst. contradiction.
  - simpl in *. destruct n. contradiction. clear H.
    apply Nat.succ_inj in H1.
    destruct n.
    + rewrite length_zero_iff_nil in H1. subst. simpl.
      rewrite kron_1_r.
      destruct a; simpl; lma'.
    + rewrite ! map_length. rewrite ! H1.
      replace (2 ^ S (S n))%nat with (2 * (2 ^ S n))%nat by (simpl; lia).
      rewrite kron_adjoint.
      setoid_rewrite kron_mixed_product'; auto.
      rewrite IHl.
      assert (translate_P a × adjoint (translate_P a) = I 2) by (destruct a; simpl; lma').
      rewrite H. rewrite kron_2_l. auto.
      all : try rewrite H1; auto.
Qed.

Lemma translate_adjoint_mult_inv : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_size_1 t -> (translate t)† × (translate t) = I (2 ^ n)%nat.
Proof. intros n t H H0.
  apply Minv_flip.
  apply WF_translate; auto.
  apply WF_adjoint. apply WF_translate; auto.
  apply translate_mult_adjoint_inv; auto.
Qed.

Lemma translate_Minv : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_size_1 t -> Minv (translate t) ((translate t)†).
Proof. intros n t H H0.
  split. apply translate_mult_adjoint_inv; auto.
  apply translate_adjoint_mult_inv; auto.
Qed.

Lemma translate_invertible : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_size_1 t -> invertible (translate t).
Proof. intros n t H H0.
  unfold invertible.
  exists (translate t)†.
  split. apply WF_adjoint. apply WF_translate; auto.
  apply translate_Minv; auto.
Qed.

Lemma translate_adjoint_invertible : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_size_1 t -> invertible (adjoint (translate t)).
Proof. intros n t H H0.
  unfold invertible.
  exists (translate t).
  split. apply WF_translate; auto.
  apply Minv_symm.
  apply translate_Minv; auto.
Qed.

Lemma translate_adjoint_eq : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t -> (translate t) † = translate t.
Proof. intros n t H H1.
  destruct H.
  unfold coef_plus_minus_1 in H1.
  unfold translate. destruct t. simpl in *.
  rewrite ! map_length, ! H0.
  rewrite Mscale_adj.
  destruct H1; subst; f_equal; try lca.
  - induction l. simpl in H. contradiction.
    clear H. simpl. rewrite ! map_length. 
    assert ((2 ^ length l + (2 ^ length l + 0))%nat = 2 * (2 ^ (length l)))%nat by (simpl; auto).
    rewrite ! H.
    rewrite kron_adjoint.
    f_equal.
    + destruct a; simpl; lma'.
    + destruct l.
      * simpl. rewrite id_adjoint_eq. auto.
      * assert (length (p :: l) <> 0%nat) by (simpl; auto).
        apply IHl. auto.
  - induction l. simpl in H. contradiction.
    clear H. simpl. rewrite ! map_length. 
    assert ((2 ^ length l + (2 ^ length l + 0))%nat = 2 * (2 ^ (length l)))%nat by (simpl; auto).
    rewrite ! H.
    rewrite kron_adjoint.
    f_equal.
    + destruct a; simpl; lma'.
    + destruct l.
      * simpl. rewrite id_adjoint_eq. auto.
      * assert (length (p :: l) <> 0%nat) by (simpl; auto).
        apply IHl. auto.
Qed.


(** Coef = 1, -1, somewhere Pauli of trace zero
X, Y, Z, WF A -> A⊗B, WF A -> B⊗A **)
Inductive WF_TType {n : nat} (t : TType n) : Prop :=
  | WF_T : proper_length_TType t -> coef_plus_minus_1 t -> trace_zero_syntax (snd t) -> WF_TType t.


Lemma translate_mult_inv : forall {n : nat} (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t -> (translate t) × (translate t) = I (2 ^ n)%nat.
Proof. intros n t H H0. 
  unfold translate.
  unfold proper_length_TType, coef_plus_minus_1 in *.
  destruct H, t.
  simpl in *. 
  rewrite ! map_length, ! H1.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_assoc.
  replace (c * c) with C1 by (destruct H0 as [H0 | H0]; rewrite H0; lca).
  rewrite Mscale_1_l.
  clear H0.
  gen n. induction l; intros.
  - simpl in *. subst. contradiction.
  - simpl in *. destruct n. contradiction. clear H.
    apply Nat.succ_inj in H1.
    destruct n.
    + rewrite length_zero_iff_nil in H1. subst. simpl.
      rewrite kron_1_r.
      destruct a; simpl; lma'.
    + setoid_rewrite kron_mixed_product'; auto.
      rewrite IHl.
      rewrite map_length, H1.
      assert (translate_P a × translate_P a = I 2) by (destruct a; simpl; lma').
      rewrite H. rewrite kron_2_l. auto.
      all : rewrite map_length; try rewrite H1; auto.
Qed.

Lemma WF_ErrT : ~ @WF_TType 0 ErrT.
Proof. intros H.
       inversion H. simpl in *. destruct H0. contradiction.
Qed.
Lemma WF_ErrT_n : forall n : nat, ~ @WF_TType n ErrT.
Proof. intros n H. inversion H. destruct H0. unfold ErrT in *.
  simpl in *. rewrite <- H3 in H0. contradiction.
Qed.

Lemma WF_defaultT_Z : forall {n : nat}, n <> 0%nat -> WF_TType (defaultT_Z n).
Proof. intros n H.
  unfold defaultT_Z.
  constructor; auto.
  - constructor; simpl; try rewrite repeat_length; auto.
  - unfold coef_plus_minus_1. auto.
  - simpl.
    destruct n; try contradiction.
    replace (S n) with (1 + n)%nat by lia.
    rewrite repeat_app.
    apply trace_zero_syntax_L.
    simpl. constructor.
Qed.

#[export] Hint Resolve WF_defaultT_Z : wf_db.


Lemma zipWith_gMul_base_inv : forall (l : list Pauli),
    zipWith gMul_base l l = repeat gI (length l).
Proof. intros l. induction l.
  - unfold zipWith, gMul_base; easy.
  - unfold zipWith, gMul_base, uncurry in *; simpl.
    rewrite IHl. f_equal.
    destruct a; easy.
Qed.

Lemma cBigMul_zipWith_gMul_Coef_inv : forall (l : list Pauli),
    cBigMul (zipWith gMul_Coef l l) = C1.
Proof. intros l. induction l.
  - unfold cBigMul, zipWith, uncurry, gMul_Coef; easy.
  - unfold cBigMul, zipWith, uncurry, gMul_Coef in *; simpl.
    rewrite fold_left_Cmult.
    rewrite IHl.
    destruct a; lca.
Qed.

Lemma proper_length_TType_gMulT : forall {n} (t t0 : TType n),
    proper_length_TType t -> proper_length_TType t0
    -> proper_length_TType (gMulT t t0).
Proof. intros n t t0 H H0.
  destruct t, t0. simpl in *.
  destruct H, H0.
  constructor; auto.
  simpl in *.
  apply zipWith_len_pres; auto.
Qed.

Lemma gMulT_inv : forall {n} (t : TType n),
    proper_length_TType t -> coef_plus_minus_1 t -> gMulT t t = defaultT_I n.
Proof. intros n t H H0.
  unfold defaultT_I.
  unfold coef_plus_minus_1 in *.
  inversion H.
  destruct t. simpl in *.
  rewrite zipWith_gMul_base_inv.
  rewrite cBigMul_zipWith_gMul_Coef_inv.
  destruct H0; subst; f_equal; lca.
Qed.

Lemma gMulT_id_l : forall {n} (t : TType n),
    proper_length_TType t -> gMulT (defaultT_I n) t = t.
Proof. intros n t H.
  unfold defaultT_I.
  unfold gMulT.
  destruct t.
  inversion H; clear H.
  simpl in *.
  f_equal.
  - rewrite Cmult_1_l.
    rewrite <- Cmult_1_r with (x := c) at 2.
    f_equal.
    gen n.
    induction l; intros; simpl in *.
    + symmetry in H1. contradiction.
    + destruct n; try contradiction.
      apply Nat.succ_inj in H1.
      destruct n.
      * rewrite length_zero_iff_nil in H1.
        subst.
        unfold cBigMul, zipWith, gMul_Coef, uncurry; simpl.
        lca.
      * assert (S n <> 0)%nat by lia.
        specialize (IHl (S n) H H1).
        unfold cBigMul, zipWith, gMul_Coef, uncurry in *; simpl in *.
        rewrite Cmult_1_l.
        auto.
  - gen n.
    induction l; intros; simpl in *.
    + symmetry in H1. contradiction.
    + do 2 (destruct n; try contradiction).
      * apply Nat.succ_inj in H1.
        rewrite length_zero_iff_nil in H1.
        subst.
        unfold zipWith, gMul_base, uncurry.
        auto.
      * apply Nat.succ_inj in H1.
        assert (S n <> 0)%nat by lia.
        specialize (IHl (S n) H H1).
        unfold zipWith, gMul_base, uncurry in *; simpl in *.
        f_equal.
        auto. 
Qed.
        
Lemma gMulT_id_r : forall {n} (t : TType n),
    proper_length_TType t -> gMulT t (defaultT_I n) = t.
Proof. intros n t H.
  unfold defaultT_I.
  unfold gMulT.
  destruct t.
  inversion H; clear H.
  simpl in *.
  f_equal.
  - rewrite Cmult_1_r.
    rewrite <- Cmult_1_r with (x := c) at 2.
    f_equal.
    gen n.
    induction l; intros; simpl in *.
    + symmetry in H1. contradiction.
    + destruct n; try contradiction.
      apply Nat.succ_inj in H1.
      destruct n.
      * rewrite length_zero_iff_nil in H1.
        subst.
        unfold cBigMul, zipWith, gMul_Coef, uncurry; simpl.
        destruct a; lca.
      * assert (S n <> 0)%nat by lia.
        specialize (IHl (S n) H H1).
        unfold cBigMul, zipWith, gMul_Coef, uncurry in *; simpl in *.
        rewrite Cmult_1_l.
        destruct a; auto.
  - gen n.
    induction l; intros; simpl in *.
    + symmetry in H1. contradiction.
    + do 2 (destruct n; try contradiction).
      * apply Nat.succ_inj in H1.
        rewrite length_zero_iff_nil in H1.
        subst.
        unfold zipWith, gMul_base, uncurry.
        simpl.
        destruct a; auto.
      * apply Nat.succ_inj in H1.
        assert (S n <> 0)%nat by lia.
        specialize (IHl (S n) H H1).
        unfold zipWith, gMul_base, uncurry in *; simpl in *.
        f_equal;
        destruct a; auto.
Qed.

Lemma gMulT_reduce : forall (n : nat) (c1 c2 : Coef) (p1 p2 : Pauli) (l1 l2 : list Pauli),
  length l1 = n -> length l2 = n ->
  gMulT (c1, p1 :: l1) (c2, p2 :: l2) = 
  @gTensorT 1 n (gMul_Coef p1 p2, [gMul_base p1 p2]) (gMulT (c1, l1) (c2, l2)).
Proof. intros. simpl. rewrite zipWith_cons.
  apply injective_projections; try easy.
  simpl.
  unfold cBigMul.
  simpl.
  rewrite fold_left_Cmult.
  rewrite Cmult_assoc.
  replace (c1 * c2 * gMul_Coef p1 p2) with (gMul_Coef p1 p2 * (c1 * c2)) by lca.
  rewrite <- Cmult_assoc.
  reflexivity.
Qed.

Lemma gMulT_gTensorT_dist : forall {n m : nat} (t1 t2 : TType n) (t3 t4 : TType m),
    proper_length_TType t1 -> proper_length_TType t2 ->
    proper_length_TType t3 -> proper_length_TType t4 ->
  gMulT (gTensorT t1 t3) (gTensorT t2 t4) = gTensorT (gMulT t1 t2) (gMulT t3 t4).
Proof. intros. 
       destruct t1; destruct t2; destruct t3; destruct t4. 
       simpl gTensorT.
       inversion H; inversion H0; inversion H1; inversion H2. 
       simpl in *.
       bdestruct_all. simpl. 
       apply injective_projections; simpl. 
  - rewrite (Cmult_assoc).
    rewrite (Cmult_comm).
    symmetry.
    rewrite (Cmult_assoc).
    rewrite (Cmult_comm).
    rewrite (Cmult_comm ( c * c0 ) (cBigMul (zipWith gMul_Coef l l0))).
    rewrite (Cmult_assoc ).
    
    rewrite (Cmult_assoc (cBigMul (zipWith gMul_Coef l1 l2)) (cBigMul (zipWith gMul_Coef l l0)) (c * c0)).
    rewrite (Cmult_comm ( cBigMul (zipWith gMul_Coef l1 l2)) (cBigMul (zipWith gMul_Coef l l0))).
    rewrite (cBigMul_app).
    rewrite (zipWith_app_product _ n); try easy.
    rewrite <- 4 (Cmult_assoc).
    assert (c0 * (c1 * c2) = c1 * (c0 * c2)). { lca. }
    rewrite H11. reflexivity.
  - rewrite (zipWith_app_product _ n); try easy.
Qed.

Lemma gMulT_assoc : forall (n : nat) (t1 t2 t3 : TType n),
  proper_length_TType t1 -> proper_length_TType t2 -> proper_length_TType t3 ->
  gMulT (gMulT t1 t2) t3 = gMulT t1 (gMulT t2 t3).
Proof. intros n t1 t2 t3 H H0 H1.
  induction n; [| destruct n].
  - inversion H; inversion H0; inversion H1.
    destruct t1; destruct t2; destruct t3.
    destruct l; destruct l0; destruct l1; try easy.
  - inversion H; inversion H0; inversion H1.
    destruct t1; destruct t2; destruct t3.
    destruct l; destruct l0; destruct l1; try easy.
    simpl in H3; simpl in H5; simpl in H7.
    apply Nat.succ_inj in H3;
      apply Nat.succ_inj in H5;
      apply Nat.succ_inj in H7.
    rewrite length_zero_iff_nil in *.
    rewrite H3, H5, H7.
    simpl. unfold cBigMul, zipWith, gMul_Coef, uncurry; induction p, p0, p1; apply injective_projections; simpl; try easy; try lca.
  - destruct t1, t2, t3.
    destruct l, l0, l1; inversion H; inversion H0; inversion H1.
    1-7 : simpl in *; try discriminate.
    simpl in H3; simpl in H5; simpl in H7.
         apply Nat.succ_inj in H3;
         apply Nat.succ_inj in H5;
           apply Nat.succ_inj in H7.
         repeat rewrite gMulT_reduce; try easy.
         assert (H9 : (c1, p1 :: l1) = @gTensorT 1 n (C1, [p1]) (c1, l1)).
         { simpl. bdestruct_all. apply injective_projections; simpl; try easy. lca. }
         assert (H10 : (c, p :: l) = @gTensorT 1 n (C1, [p]) (c, l)).
         { simpl. bdestruct_all. apply injective_projections; simpl; try easy. lca. }
         rewrite H9, H10. 
         do 2 replace (S n) with (1 + n)%nat by lia.
         pose (@gMulT_gTensorT_dist 1 (S n) (gMul_Coef p p0, [gMul_base p p0])  (C1, [p1]) (gMulT (c, l) (c0, l0)) (c1, l1)) as e; rewrite e at 1.
         pose (@gMulT_gTensorT_dist 1 (S n) (C1, [p]) (gMul_Coef p0 p1, [gMul_base p0 p1]) (c, l) (gMulT (c0, l0) (c1, l1))) as w; rewrite w at 1.
         all : try easy.
         rewrite IHn; try easy.
         assert (H11 : (@gMulT 1 (gMul_Coef p p0, [gMul_base p p0]) (C1, [p1])) = 
                      (@gMulT 1 (C1, [p]) (gMul_Coef p0 p1, [gMul_base p0 p1]))).
         { destruct p; destruct p0; destruct p1; compute; autorewrite with R_db; replace R0 with 0 by lra; autorewrite with R_db; try easy. }
         rewrite H11; easy. 
         all : simpl; bdestruct_all; try constructor; simpl. 
         all : try rewrite (zipWith_len_pres _ (S n)); try easy.
Qed.


Lemma translateA_gScaleA_nil : forall {n} (c : Coef) (A : AType n),
    proper_length_AType_nil A -> translateA (gScaleA c A) = c .* (translateA A).
Proof. intros. induction A; simpl; unfold translateA in *; simpl.
  - rewrite Mscale_0_r. reflexivity.
  - unfold gScaleA in *. rewrite ! fold_left_Mplus. rewrite Mscale_plus_distr_r.
    rewrite IHA. f_equal. apply translate_gScaleT. inversion H; assumption.
    inversion H. assumption.
Qed.

Lemma translateA_gScaleA : forall {n} (c : Coef) (A : AType n),
    proper_length_AType A -> translateA (gScaleA c A) = c .* (translateA A).
Proof. intros. apply proper_length_AType_implies_proper_length_AType_nil in H.
  apply translateA_gScaleA_nil. assumption.
Qed.


Lemma WF_Matrix_translateA_nil : forall {n : nat} (a : AType n), proper_length_AType_nil a -> WF_Matrix (translateA a).
Proof. intros. unfold translateA.
  induction a; simpl.
  - auto with wf_db.
  - rewrite fold_left_Mplus.
    apply WF_plus.
    apply IHa.
    inversion H.
    assumption.
    apply WF_translate.
    inversion H.
    assumption.
Qed.

Lemma WF_Matrix_translateA : forall {n : nat} (a : AType n), proper_length_AType a -> WF_Matrix (translateA a).
Proof. intros.
  apply proper_length_AType_implies_proper_length_AType_nil in H.
  apply WF_Matrix_translateA_nil.
  assumption.
Qed.

#[export] Hint Resolve WF_Matrix_translateA_nil WF_Matrix_translateA : wf_db.







(** ** anticommutative / commutative TTypes ** *)
Local Open Scope C_scope.
Local Open Scope matrix_scope.



Definition anticommute_Pauli (A B : Pauli) : Prop :=
  translate_P A × translate_P B = - C1 .* translate_P B × translate_P A.

Definition commute_Pauli (A B : Pauli) : Prop :=
  translate_P A × translate_P B = translate_P B × translate_P A.

Definition anticommute_TType {n : nat} (t1 t2 : TType n) : Prop :=
  let (c1, Ps1) := t1 in
  let (c2, Ps2) := t2 in
  (cBigMul (zipWith gMul_Coef Ps1 Ps2)) = (- (cBigMul (zipWith gMul_Coef Ps2 Ps1)))%C.

Definition commute_TType {n : nat} (t1 t2 : TType n) : Prop :=
  let (c1, Ps1) := t1 in
  let (c2, Ps2) := t2 in
  (cBigMul (zipWith gMul_Coef Ps1 Ps2)) = (cBigMul (zipWith gMul_Coef Ps2 Ps1)).

Fixpoint anticommute_TType_AType {n : nat} (t : TType n) (a : AType n) : Prop :=
  match a with
  | t1 :: a1 => anticommute_TType t t1 /\ anticommute_TType_AType t a1
  | nil => True
  end. 
  
Fixpoint anticommute_AType_syntactic {n : nat} (a1 a2 : AType n) : Prop :=
  match a1 with
  | t1 :: a1' => anticommute_TType_AType t1 a2 /\ anticommute_AType_syntactic a1' a2
  | nil => True
  end.


Lemma gMul_Coef_comm_anticomm : forall (p1 p2 : Pauli),
    (gMul_Coef p1 p2 = gMul_Coef p2 p1) \/ (gMul_Coef p1 p2 = - gMul_Coef p2 p1)%C.
Proof. intros p1 p2. destruct p1, p2; unfold gMul_Coef; simpl; auto.
  all: right; lca.
Qed.

Lemma gMul_Coef_comm_1 : forall (p1 p2 : Pauli),
    (gMul_Coef p1 p2 = gMul_Coef p2 p1) -> gMul_Coef p1 p2 = C1.
Proof. intros p1 p2 H. destruct p1, p2; unfold gMul_Coef in *; auto.
  all: inversion H; lra.
Qed.

Lemma gMul_Coef_anticomm_plus_minus_i : forall (p1 p2 : Pauli),
    (gMul_Coef p1 p2 = - gMul_Coef p2 p1)%C -> (gMul_Coef p1 p2 = Ci \/ gMul_Coef p1 p2 = (- Ci)%C).
Proof. intros p1 p2 H. destruct p1, p2; unfold gMul_Coef in *; auto.
  all: inversion H; lra.
Qed.


Lemma anticommute_TType_gScaleT : forall {n} (c : Coef) (t1 t2 : TType n),
    anticommute_TType t1 (gScaleT c t2) <->  anticommute_TType t1 t2.
Proof. intros n c t1 t2.
  split; intros; destruct t1, t2; easy.
Qed.
  
Lemma anticommute_TType_AType_gScaleA : forall {n} (c : Coef) (t : TType n) (a : AType n),
    anticommute_TType_AType t (gScaleA c a) <-> anticommute_TType_AType t a.
Proof. intros n c t a.
  split; intros.
  - induction a; auto.
    simpl in *. destruct H.
    specialize (IHa H0).
    split; auto.
    rewrite anticommute_TType_gScaleT in H.
    easy.
  - induction a; auto.
    simpl in *. destruct H.
    specialize (IHa H0).
    split; auto.
    rewrite anticommute_TType_gScaleT.
    easy.
Qed.

Lemma anticommute_AType_syntactic_gScaleA : forall {n} (c : Coef) (a b : AType n),
    anticommute_AType_syntactic a (gScaleA c b) <-> anticommute_AType_syntactic a b.
Proof. intros n c a b.
  split; intros.
  - induction a; auto.
    simpl in *. destruct H.
    specialize (IHa H0).
    split; auto.
    rewrite anticommute_TType_AType_gScaleA in H.
    auto.
  - induction a; auto.
    simpl in *. destruct H.
    specialize (IHa H0).
    split; auto.
    rewrite anticommute_TType_AType_gScaleA.
    auto.
Qed.


Inductive restricted_addition_syntactic {n : nat} : AType n -> Prop :=
| add_restrict_base_syntactic : forall (t : TType n), WF_TType t -> restricted_addition_syntactic [t]
| add_restrict_inductive_syntactic : forall (a1 a2 : AType n),
    restricted_addition_syntactic a1 -> restricted_addition_syntactic a2 ->
    anticommute_AType_syntactic a1 a2  ->
    restricted_addition_syntactic (gScaleA (C1/√2)%C (a1 ++ a2)).

Lemma restricted_addition_syntactic_implies_not_nil : forall {n : nat} (a : AType n),
  restricted_addition_syntactic a -> a <> [].
Proof. intros n a H.
  induction H. 
  intro; discriminate.
  intro. unfold gScaleA in H2.
  apply map_eq_nil in H2.
  apply app_eq_nil in H2.
  destruct H2. auto.
Qed.

Lemma restricted_addition_syntactic_implies_proper_length_AType: forall {n : nat} (a : AType n),
  restricted_addition_syntactic a -> proper_length_AType a.
Proof. intros n a H. induction H.
  - constructor. inversion H. assumption.
  - apply proper_length_AType_gScaleA.
    apply proper_length_AType_App; assumption.
Qed.

Lemma restricted_addition_syntactic_defaultA : forall {n : nat},
    n <> 0%nat -> restricted_addition_syntactic (defaultA_Z n).
Proof. intros n.
  unfold defaultA_Z.
  constructor.
  auto with wf_db.
Qed.

#[export] Hint Resolve restricted_addition_syntactic_defaultA : wf_db.

Inductive WF_AType {n : nat} : AType n -> Prop :=
| WF_A_syntactic (a : AType n) : restricted_addition_syntactic a -> WF_AType a.

Lemma WF_AType_defaultA : forall {n : nat},
    n <> 0%nat -> WF_AType (defaultA_Z n).
Proof. intros n H.
  constructor.
  auto with wf_db.
Qed.

#[export] Hint Resolve WF_AType_defaultA : wf_db.
  
Lemma restricted_addition_syntactic_implies_WF_AType : forall {n} (a : AType n),
    restricted_addition_syntactic a -> WF_AType a.
Proof. intros n a H. constructor. auto. Qed.

Lemma WF_AType_implies_proper_length_AType : forall {n} (a : AType n),
    WF_AType a -> proper_length_AType a.
Proof. intros n a H. destruct H.
  apply restricted_addition_syntactic_implies_proper_length_AType; auto.
Qed.


Lemma proper_length_AType_implies_proper_length_TType : forall {n : nat} (t : TType n) (a : AType n),
    proper_length_AType a -> In t a -> proper_length_TType t.
Proof. intros n t a H H0.
  induction H.
  - inversion H0; subst; clear H0; auto.
    inversion H1.
  - inversion H0; subst; clear H0; auto.
Qed.

Lemma proper_length_AType_gMulA : forall {n} (a a0 : AType n),
    proper_length_AType a -> proper_length_AType a0
    -> proper_length_AType (gMulA a a0).
Proof. intros n a a0 H H0. induction H; simpl in *.
  - rewrite app_nil_r.
    induction H0; simpl in *.
    + constructor.
      apply proper_length_TType_gMulT; auto.
    + constructor; auto.
      apply proper_length_TType_gMulT; auto.
  - apply proper_length_AType_App; auto.
    clear IHproper_length_AType.
    induction H0; simpl in *.
    + constructor.
      apply proper_length_TType_gMulT; auto.
    + constructor; auto.
      apply proper_length_TType_gMulT; auto.
Qed.

Lemma proper_length_TType_gTensorT : forall {n m} (t : TType n) (t0 : TType m),
    proper_length_TType t -> proper_length_TType t0
    -> proper_length_TType (gTensorT t t0).
Proof. intros n m t t0 H H0.
  destruct H, H0.
  destruct t, t0.
  simpl in *.
  constructor.
  - lia.
  - simpl. rewrite app_length.
    rewrite H1, H2. auto.
Qed.

Lemma proper_length_AType_gTensorA : forall {n m} (a : AType n) (a0 : AType m),
    proper_length_AType a -> proper_length_AType a0
    -> proper_length_AType (gTensorA a a0).
Proof. intros n m a a0 H H0.
  induction H; simpl in *.
  - rewrite app_nil_r.
    induction H0; simpl in *.
    + constructor.
      apply proper_length_TType_gTensorT; auto.
    + constructor; auto.
      apply proper_length_TType_gTensorT; auto.
  - apply proper_length_AType_App; auto.
    clear IHproper_length_AType.
    induction H0; simpl in *.
    + constructor.
      apply proper_length_TType_gTensorT; auto.
    + constructor; auto.
      apply proper_length_TType_gTensorT; auto.
Qed.      
  

Lemma anticommute_AType_syntactic_nil_r : forall {n} (a : AType n), anticommute_AType_syntactic a [] <-> True.
Proof. intros n a.
  split.
  - intro.
    induction a; auto.
  - intro.
    induction a; auto.
    simpl.
    rewrite and_comm.
    rewrite kill_true.
    apply IHa.
Qed.

Lemma anticommute_TType_comm : forall {n} (a b : TType n), anticommute_TType a b -> anticommute_TType b a.
Proof. intros n a b H.
  destruct a,b; simpl in *.
  rewrite H.
  lca.
Qed.

Lemma anticommute_AType_syntactic_comm : forall {n} (a b : AType n), anticommute_AType_syntactic a b -> anticommute_AType_syntactic b a.
Proof. intros n a b H.
  induction a.
  - apply anticommute_AType_syntactic_nil_r. auto.
  - simpl in *.
    destruct H. specialize (IHa H0).
    clear H0.
    induction b.
    + simpl. auto.
    + simpl in *.
      destruct H, IHa.
      specialize (IHb H0 H2).
      repeat split; auto.
      apply anticommute_TType_comm.
      auto.
Qed.

Lemma anticommute_TType_AType_app_dist : forall {n} (t : TType n) (a1 a2 : AType n),
    anticommute_TType_AType t (a1 ++ a2) <-> anticommute_TType_AType t a1 /\ anticommute_TType_AType t a2.
Proof. intros n t a1 a2.
  split.
  - intro. split.
    + induction a1.
      * simpl. auto.
      * simpl in *. destruct H.
        specialize (IHa1 H0).
        split; auto.
    + induction a1.
      * simpl in *. auto.
      * simpl in *. destruct H.
        specialize (IHa1 H0).
        auto.
  - intro. destruct H.
    induction a1; auto.
    simpl in *. destruct H.
    specialize (IHa1 H1).
    split; auto.
Qed.

Lemma anticommute_TType_AType_app_comm : forall {n} (t : TType n) (a1 a2 : AType n),
    anticommute_TType_AType t (a1 ++ a2) <->  anticommute_TType_AType t (a2 ++ a1).
Proof. intros n t a1 a2.
  split; intro;
    rewrite anticommute_TType_AType_app_dist;
    rewrite and_comm;
    rewrite <- anticommute_TType_AType_app_dist;
    auto.
Qed.

Lemma anticommute_AType_syntactic_app_dist_l : forall {n} (a b c : AType n), anticommute_AType_syntactic (a ++ b) c <-> anticommute_AType_syntactic a c /\ anticommute_AType_syntactic b c.
Proof. intros n a b c.
  split.
  - intro. split.
    + induction a.
      * simpl. auto.
      * simpl in *. destruct H.
        specialize (IHa H0).
        split; auto.
    + induction a.
      * simpl in *. auto.
      * simpl in *. destruct H.
        apply (IHa H0).
  - intro. destruct H.
    induction a; auto.
    simpl in *. destruct H.
    specialize (IHa H1).
    split; auto.
Qed.

Lemma anticommute_AType_syntactic_app_comm_l : forall {n} (a b c : AType n), anticommute_AType_syntactic (a ++ b) c <-> anticommute_AType_syntactic (b ++ a) c.
Proof. intros n a b c. rewrite ! anticommute_AType_syntactic_app_dist_l. rewrite and_comm.
  split; auto.
Qed.

Lemma anticommute_AType_syntactic_app_dist_r : forall {n} (a b c : AType n), anticommute_AType_syntactic a (b ++ c) <-> anticommute_AType_syntactic a b /\ anticommute_AType_syntactic a c.
Proof. intros n a b c.
  split.
  - intros.
    apply anticommute_AType_syntactic_comm in H.
    rewrite anticommute_AType_syntactic_app_dist_l in H.
    destruct H.
    split; apply anticommute_AType_syntactic_comm; auto.
  - intros [H H0].
    apply anticommute_AType_syntactic_comm.
    rewrite anticommute_AType_syntactic_app_dist_l.
    apply anticommute_AType_syntactic_comm in H.
    apply anticommute_AType_syntactic_comm in H0.
    split; auto.
Qed.

Lemma anticommute_AType_syntactic_app_comm_r : forall {n} (a b c : AType n), anticommute_AType_syntactic a (b ++ c) <-> anticommute_AType_syntactic a (c ++ b).
Proof. intros n a b c. rewrite ! anticommute_AType_syntactic_app_dist_r. rewrite and_comm.
  split; auto.
Qed.



Inductive commute_P (P1 P2 : Pauli) : Prop :=
| commuting_P : P1 = gI \/ P2 = gI \/ P1 = P2 -> commute_P P1 P2.

Inductive anticommute_P (P1 P2 : Pauli) : Prop :=
| anticommuting_P : P1 <> gI -> P2 <> gI -> P1 <> P2 -> anticommute_P P1 P2.

Lemma commute_P_swap : forall (P1 P2 : Pauli),
    commute_P P1 P2 -> commute_P P2 P1.
Proof. intros P1 P2 H0.
  inversion H0.
  constructor.
  destruct H as [H | [H | H]]; auto.
Qed.

Lemma anticommute_P_swap : forall (P1 P2 : Pauli),
    anticommute_P P1 P2 -> anticommute_P P2 P1.
Proof. intros P1 P2 H0.
  inversion H0.
  constructor; auto.
Qed.

Lemma neg_commute_P : forall (P1 P2 : Pauli),
    ~ commute_P P1 P2 <-> anticommute_P P1 P2.
Proof. intros P1 P2.
  split; intros H0.
  - assert (~ (P1 = gI \/ P2 = gI \/ P1 = P2))
      by (intro H1; unfold "~" in H0, H1; apply (commuting_P P1 P2) in H1; auto).
    apply Classical_Prop.not_or_and in H.
    destruct H as [H1 H2].
    apply Classical_Prop.not_or_and in H2.
    destruct H2 as [H2 H3].
    constructor; auto.
  - intro H1.
    inversion H0.
    inversion H1.
    destruct H4 as [H4 | [H4 | H4]]; auto.
Qed.

Lemma neg_anticommute_P : forall (P1 P2 : Pauli),
    ~ anticommute_P P1 P2 <-> commute_P P1 P2.
Proof. intros P1 P2.
  split; intros H0.
  - assert (~ (P1 <> gI /\ P2 <> gI /\ P1 <> P2)).
    { intro H1.
      unfold "~" in H0.
      destruct H1 as [H1 [H2 H3]].
      pose (anticommuting_P P1 P2 H1 H2 H3) as E.
      apply H0 in E.
      auto. }
    do 2 (apply Classical_Prop.not_and_or in H;
          destruct H as [H | H];
          try (apply Classical_Prop.NNPP in H;
               constructor; auto)).
  - intro H1.
    inversion H0.
    inversion H1.
    destruct H as [H | [H | H]]; auto.
Qed.

Lemma anticommute_or_commute_P : forall (P1 P2 : Pauli),
    anticommute_P P1 P2 \/ commute_P P1 P2.
Proof. intros P1 P2.
  destruct (Classical_Prop.classic (commute_P P1 P2)) as [H0 | H0];
    try rewrite neg_commute_P in H0; auto.
Qed.

Lemma anticommute_commute_P_no_middle : forall (P1 P2 : Pauli),
    ~ anticommute_P P1 P2 \/ ~ commute_P P1 P2.
Proof. intros P1 P2.
  apply Classical_Prop.not_and_or.
  intros [H0 H1].
  rewrite <- neg_commute_P in H0.
  contradiction.
Qed.

Inductive commute_listP : list Pauli -> list Pauli -> Prop :=
| commuting_listP_base : forall (P1 P2 : Pauli),
    commute_P P1 P2 -> commute_listP [P1] [P2]
| commuting_listP_commP_commL : forall (P1 P2 : Pauli) (l1 l2 : list Pauli),
    commute_P P1 P2 -> commute_listP l1 l2 -> commute_listP (P1::l1) (P2::l2)
| commuting_listP_anticommP_anticommL : forall (P1 P2 : Pauli) (l1 l2 : list Pauli),
    anticommute_P P1 P2 -> anticommute_listP l1 l2 -> commute_listP (P1::l1) (P2::l2)

with anticommute_listP : list Pauli -> list Pauli -> Prop :=
| anticommuting_listP_base : forall (P1 P2 : Pauli),
    anticommute_P P1 P2 -> anticommute_listP [P1] [P2]
| anticommuting_listP_anticommP_commL : forall (P1 P2 : Pauli) (l1 l2 : list Pauli),
    anticommute_P P1 P2 -> commute_listP l1 l2 -> anticommute_listP (P1::l1) (P2::l2)
| anticommuting_listP_commP_anticommL : forall (P1 P2 : Pauli) (l1 l2 : list Pauli),
    commute_P P1 P2 -> anticommute_listP l1 l2 -> anticommute_listP (P1::l1) (P2::l2).

Scheme commute_listP_ind_dep := Induction for commute_listP Sort Prop
    with anticommute_listP_ind_dep := Induction for anticommute_listP Sort Prop.

Scheme commute_listP_ind' := Minimality for commute_listP Sort Prop
    with anticommute_listP_ind' := Minimality for anticommute_listP Sort Prop.

Lemma commute_listP_length : forall (l1 l2 : list Pauli),
    commute_listP l1 l2 -> length l1 = length l2 /\ l1 <> [].
Proof. intros l1 l2 H.
  induction H using commute_listP_ind' with (P0 := fun l1 l2 => length l1 = length l2 /\ l1 <> []);
    simpl; split; try destruct IHcommute_listP; f_equal; auto; intro H'; inversion H'.
Qed.

Lemma anticommute_listP_length : forall (l1 l2 : list Pauli),
    anticommute_listP l1 l2 -> length l1 = length l2 /\ l1 <> [].
Proof. intros l1 l2 H.
  induction H using anticommute_listP_ind' with (P := fun l1 l2 => length l1 = length l2 /\ l1 <> []);
    simpl; split; try destruct IHanticommute_listP; f_equal; auto; intro H'; inversion H'.
Qed.

Lemma commute_listP_repeat_gI : forall (m : nat) (l : list Pauli),
    length l = m -> l <> [] -> commute_listP l (repeat gI m).
Proof. intros m l H.
  gen l. induction m; intros.
  - rewrite length_zero_iff_nil in H. contradiction.
  - destruct l; try contradiction.
    simpl in *. apply Nat.succ_inj in H.
    destruct l.
    + subst. simpl in *. constructor. constructor. right. left. auto.
    + destruct m; try discriminate.
      assert (p0 :: l <> []) by (intro; discriminate).
      specialize (IHm (p0 :: l) H H1).
      constructor; auto.
      constructor. right. left. auto.
Qed.

Lemma commute_listP_swap : forall (l1 l2 : list Pauli),
    commute_listP l1 l2 -> commute_listP l2 l1.
Proof. intros l1 l2 H0.
  apply commute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) => commute_listP l2 l1)
         (P0 := fun (l1 l2 : list Pauli) => anticommute_listP l2 l1);
    intros; auto;
    try (constructor; try apply commute_P_swap; try apply anticommute_P_swap; easy).
Qed.

Lemma anticommute_listP_swap : forall (l1 l2 : list Pauli),
    anticommute_listP l1 l2 -> anticommute_listP l2 l1.
Proof. intros l1 l2 H0.
  apply anticommute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) => commute_listP l2 l1)
         (P0 := fun (l1 l2 : list Pauli) => anticommute_listP l2 l1);
    intros; auto;
    try (constructor; try apply anticommute_P_swap; try apply commute_P_swap; easy).
Qed.

Lemma anticommute_or_commute_listP : forall (l1 l2 : list Pauli),
    l1 <> [] \/ l2 <> [] -> length l1 = length l2 -> anticommute_listP l1 l2 \/ commute_listP l1 l2.
Proof. intros l1 l2 H0 H1.
  gen l2.
    induction l1 as [ | p1 l1]; intros.
    - simpl in H1.
      symmetry in H1.
      rewrite length_zero_iff_nil in H1.
      subst.
      destruct H0; contradiction.
    - destruct l2 as [ | p2 l2].
      + simpl in H1.
        inversion H1.
      + simpl in H1.
        inversion H1.
        destruct (list_eq_dec eqdec_Pauli l1 []) as [E | E].
        * subst.
        simpl in *.
        symmetry in H2.
        rewrite length_zero_iff_nil in H2.
        subst.
        destruct (anticommute_or_commute_P p1 p2).
           -- left; constructor; auto.
           -- right; constructor; auto.
        * assert (E' : l2 <> []).
           { intro H3; subst; simpl in H2;
               rewrite length_zero_iff_nil in H2; subst; contradiction. }
           assert (EE' : l1 <> [] \/ l2 <> []) by auto.
           destruct (IHl1 l2 EE' H2);
             destruct (anticommute_or_commute_P p1 p2).
           -- right. apply commuting_listP_anticommP_anticommL; auto.
           -- left. apply anticommuting_listP_commP_anticommL; auto.
           -- left. apply anticommuting_listP_anticommP_commL; auto.
           -- right. apply commuting_listP_commP_commL; auto.
Qed.
              
Lemma anticommute_listP_nonempty_equal_len : forall (l1 l2 : list Pauli),
    anticommute_listP l1 l2 -> l1 <> [] /\ l2 <> [] /\ length l1 = length l2.
Proof. intros l1 l2 H0.
  apply anticommute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) =>
                l1 <> [] /\ l2 <> [] /\ length l1 = length l2)
         (P0 := fun (l1 l2 : list Pauli) =>
                l1 <> [] /\ l2 <> [] /\ length l1 = length l2);
    intros; repeat split; auto; try (intro; discriminate); simpl;
    match goal with
    | H' : context [length _ = length _] |- _ =>
        destruct H' as [H'1 [H'2 H'3]]; rewrite H'3; auto
    end.
Qed.

Lemma commute_listP_nonempty_equal_len : forall (l1 l2 : list Pauli),
    commute_listP l1 l2 -> l1 <> [] /\ l2 <> [] /\ length l1 = length l2.
Proof. intros l1 l2 H0.
  apply commute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) =>
                l1 <> [] /\ l2 <> [] /\ length l1 = length l2)
         (P0 := fun (l1 l2 : list Pauli) =>
                l1 <> [] /\ l2 <> [] /\ length l1 = length l2);
    intros; repeat split; auto; try (intro; discriminate); simpl;
    match goal with
    | H' : context [length _ = length _] |- _ =>
        destruct H' as [H'1 [H'2 H'3]]; rewrite H'3; auto
    end.
Qed.

Lemma anticommute_commute_listP_no_middle : forall (l1 l2 : list Pauli),
    ~ anticommute_listP l1 l2 \/ ~ commute_listP l1 l2.
Proof. intros l1 l2.
  apply Classical_Prop.not_and_or.
  intros [H0 H1].
  gen l2.
  induction l1; intros.
  - destruct (anticommute_listP_nonempty_equal_len [] l2 H0) as [H' [H'' H''']];
      contradiction.
  - destruct l2.
    + destruct (anticommute_listP_nonempty_equal_len (a :: l1) [] H0) as [H' [H'' H''']];
        contradiction.
    + apply (IHl1 l2).
      * destruct (anticommute_or_commute_P a p).
        -- inversion H1; subst; auto.
           ++ rewrite <- neg_anticommute_P in H3; contradiction.
           ++ rewrite <- neg_anticommute_P in H5; contradiction.
        -- inversion H0; subst; auto.
           ++ rewrite <- neg_commute_P in H3; contradiction.
           ++ rewrite <- neg_commute_P in H5; contradiction.
      * destruct (anticommute_or_commute_P a p).
        -- inversion H0; subst; auto.
           ++ inversion H1; subst; auto.
              ** rewrite <- neg_anticommute_P in H5; contradiction.
              ** destruct (anticommute_listP_nonempty_equal_len [] [] H8) as [H' [H'' H''']];
                   contradiction.
           ++ rewrite <- neg_anticommute_P in H5; contradiction.
        -- inversion H1; subst; auto.
           ++ inversion H0; subst; auto.
              ** rewrite <- neg_commute_P in H5; contradiction.
              ** destruct (anticommute_listP_nonempty_equal_len [] [] H8) as [H' [H'' H''']];
                   contradiction.
           ++ rewrite <- neg_commute_P in H5; contradiction.
Qed.

Lemma anticommute_commute_listP_app_repeat_right : forall (m : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    (commute_listP (lp1 ++ repeat gI m) (lp2 ++ repeat gI m) ->
     commute_listP lp1 lp2) /\ 
      (anticommute_listP (lp1 ++ repeat gI m) (lp2 ++ repeat gI m) ->
       anticommute_listP lp1 lp2).
Proof. intros m lp1 lp2 H H0.
  gen lp2. induction lp1; intros;
    destruct lp2; try discriminate; try contradiction.
  split; intros.
  - remember H1 as H1'. clear HeqH1'.
    apply commute_listP_length in H1'. destruct H1'.
    rewrite ! app_length, ! repeat_length in H2.
    assert (length lp1 = length lp2) by (simpl in *; lia).
    clear H2.
    destruct lp1, lp2; try discriminate.
    + simpl in *. inversion H1; subst; constructor; auto.
      destruct m. inversion H9.
      assert (length (repeat gI (S m)) = S m) by (rewrite repeat_length; auto).
      assert (repeat gI (S m) <> []) by (intro H'; inversion H').
      pose (commute_listP_repeat_gI (S m) (repeat gI (S m)) H2 H5) as H6.
      destruct (anticommute_commute_listP_no_middle (repeat gI (S m)) (repeat gI (S m)));
        try contradiction.
    + simpl in *. apply Nat.succ_inj in H4.
      assert (p0 :: lp1 <> []) by (intro; discriminate).
      assert (p1 :: lp2 <> []) by (intro; discriminate).
      specialize (IHlp1 H2 (p1 :: lp2) H5).
      destruct IHlp1.
      inversion H1; subst.
      apply H6 in H13. apply commuting_listP_commP_commL; auto.
      apply H7 in H13. apply commuting_listP_anticommP_anticommL; auto.
  - remember H1 as H1'. clear HeqH1'.
    apply anticommute_listP_length in H1'. destruct H1'.
    rewrite ! app_length, ! repeat_length in H2.
    assert (length lp1 = length lp2) by (simpl in *; lia).
    clear H2.
    destruct lp1, lp2; try discriminate.
    + simpl in *. inversion H1; subst; constructor; auto.
      destruct m. inversion H9.
      assert (length (repeat gI (S m)) = S m) by (rewrite repeat_length; auto).
      assert (repeat gI (S m) <> []) by (intro H'; inversion H').
      pose (commute_listP_repeat_gI (S m) (repeat gI (S m)) H2 H5) as H6.
      destruct (anticommute_commute_listP_no_middle (repeat gI (S m)) (repeat gI (S m)));
        try contradiction.
    + simpl in *. apply Nat.succ_inj in H4.
      assert (p0 :: lp1 <> []) by (intro; discriminate).
      assert (p1 :: lp2 <> []) by (intro; discriminate).
      specialize (IHlp1 H2 (p1 :: lp2) H5).
      destruct IHlp1.
      inversion H1; subst.
      apply H6 in H13. apply anticommuting_listP_anticommP_commL; auto.
      apply H7 in H13. apply anticommuting_listP_commP_anticommL; auto.
Qed.

Lemma commute_listP_app_repeat_right : forall (m : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    commute_listP (lp1 ++ repeat gI m) (lp2 ++ repeat gI m) ->
     commute_listP lp1 lp2.
Proof. intros m lp1 lp2 H0 H1 H2.
  destruct (anticommute_commute_listP_app_repeat_right m lp1 lp2 H0 H1); auto.
Qed.

Lemma anticommute_listP_app_repeat_right : forall (m : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    anticommute_listP (lp1 ++ repeat gI m) (lp2 ++ repeat gI m) ->
     anticommute_listP lp1 lp2.
Proof. intros m lp1 lp2 H0 H1 H2.
  destruct (anticommute_commute_listP_app_repeat_right m lp1 lp2 H0 H1); auto.
Qed.

Lemma anticommute_commute_listP_app_repeat_left : forall (n : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    (commute_listP (repeat gI n ++ lp1) (repeat gI n ++ lp2) ->
     commute_listP lp1 lp2) /\ 
      (anticommute_listP (repeat gI n ++ lp1) (repeat gI n ++ lp2) ->
       anticommute_listP lp1 lp2).
Proof. intros n lp1 lp2 H H0.
  induction n; simpl; auto.
  destruct IHn.
  split; intros.
  - inversion H3; subst; auto.
    + contradict H.
      rewrite <- length_zero_iff_nil.
      symmetry in H6.
      rewrite <- length_zero_iff_nil in H6.
      rewrite app_length in H6. lia.
    + inversion H7. contradiction.
  - inversion H3; subst; auto.
    + contradict H.
      rewrite <- length_zero_iff_nil.
      symmetry in H6.
      rewrite <- length_zero_iff_nil in H6.
      rewrite app_length in H6. lia.
    + inversion H7. contradiction.
Qed.

Lemma commute_listP_app_repeat_left : forall (n : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    commute_listP (repeat gI n ++ lp1) (repeat gI n ++ lp2) ->
     commute_listP lp1 lp2.
Proof. intros n lp1 lp2 H H0 H1.
  destruct (anticommute_commute_listP_app_repeat_left n lp1 lp2 H H0); auto.
Qed.

Lemma anticommute_listP_app_repeat_left : forall (n : nat) (lp1 lp2 : list Pauli),
    lp1 <> [] -> lp2 <> [] ->
    anticommute_listP (repeat gI n ++ lp1) (repeat gI n ++ lp2) ->
     anticommute_listP lp1 lp2.
Proof. intros n lp1 lp2 H H0 H1.
  destruct (anticommute_commute_listP_app_repeat_left n lp1 lp2 H H0); auto.
Qed.

Inductive commute_T {n : nat} (t1 t2 : TType n) : Prop :=
| commuting_T : commute_listP (snd t1) (snd t2) -> commute_T t1 t2.

Lemma commute_T_defaultT_I : forall {n : nat} (t : TType n),
    proper_length_TType t -> commute_T t (defaultT_I n).
Proof. intros n t.
  constructor. destruct t. unfold defaultT_I. simpl.
  destruct H. simpl in H0.
  gen n. induction l; intros. simpl in *. subst. contradiction.
  destruct n. contradiction.
  simpl in *. apply Nat.succ_inj in H0. clear H.
  destruct l. destruct n; simpl in *; try discriminate.
  do 2 constructor. auto.
  constructor. constructor. auto.
  apply IHl; simpl in *; lia.
Qed.

Inductive anticommute_T {n : nat} (t1 t2 : TType n) : Prop :=
| anticommuting_T : anticommute_listP (snd t1) (snd t2) -> anticommute_T t1 t2.

Lemma commute_T_gTensorT_defaultT_I_right : forall {m n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    commute_T (gTensorT t1 (defaultT_I m)) (gTensorT t2 (defaultT_I m)) ->
    commute_T t1 t2.
Proof. intros m n t1 t2 H0 H1 H2.
  inversion H2. clear H2. constructor.
  destruct t1, t2. unfold defaultT_I in H.
  destruct H0, H1.
  simpl in *.
  apply commute_listP_app_repeat_right in H; auto.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
Qed.

Lemma anticommute_T_gTensorT_defaultT_I_right : forall {m n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    anticommute_T (gTensorT t1 (defaultT_I m)) (gTensorT t2 (defaultT_I m)) ->
    anticommute_T t1 t2.
Proof. intros m n t1 t2 H0 H1 H2.
  inversion H2. clear H2. constructor.
  destruct t1, t2. unfold defaultT_I in H.
  destruct H0, H1.
  simpl in *.
  apply anticommute_listP_app_repeat_right in H; auto.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
Qed.

Lemma commute_T_gTensorT_defaultT_I_left : forall {m n : nat} (t1 t2 : TType m),
    proper_length_TType t1 -> proper_length_TType t2 ->
    commute_T (gTensorT(defaultT_I n)  t1) (gTensorT (defaultT_I n) t2) ->
    commute_T t1 t2.
Proof. intros m n t1 t2 H H0 H1.
  inversion H1. clear H1. constructor.
  destruct t1, t2. unfold defaultT_I in H2.
  destruct H, H0.
  simpl in *.
  apply commute_listP_app_repeat_left in H2; auto.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
Qed.

Lemma anticommute_T_gTensorT_defaultT_I_left : forall {m n : nat} (t1 t2 : TType m),
    proper_length_TType t1 -> proper_length_TType t2 ->
    anticommute_T (gTensorT (defaultT_I n) t1) (gTensorT (defaultT_I n) t2) ->
    anticommute_T t1 t2.
Proof. intros m n t1 t2 H H0 H1.
  inversion H1. clear H1. constructor.
  destruct t1, t2. unfold defaultT_I in H2.
  destruct H, H0.
  simpl in *.
  apply anticommute_listP_app_repeat_left in H2; auto.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
  intro. rewrite <- length_zero_iff_nil in H4. lia.
Qed.


Lemma commute_T_swap : forall {n : nat} (t1 t2 : TType n),
    commute_T t1 t2 -> commute_T t2 t1.
Proof. intros n t1 t2 H.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  constructor. inversion H. simpl in *.
  inversion H0; subst; auto.
  - apply commute_listP_swap; auto.
  - apply commute_P_swap in H1.
    apply commute_listP_swap in H2.
    apply commuting_listP_commP_commL; auto.
  - apply anticommute_P_swap in H1.
    apply anticommute_listP_swap in H2.
    apply commuting_listP_anticommP_anticommL; auto.
Qed.

Lemma anticommute_T_swap : forall {n : nat} (t1 t2 : TType n),
    anticommute_T t1 t2 -> anticommute_T t2 t1.
Proof. intros n t1 t2 H.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  constructor. inversion H. simpl in *.
  inversion H0; subst; auto.
  - apply anticommute_listP_swap; auto.
  - apply anticommute_P_swap in H1.
    apply commute_listP_swap in H2.
    apply anticommuting_listP_anticommP_commL; auto.
  - apply commute_P_swap in H1.
    apply anticommute_listP_swap in H2.
    apply anticommuting_listP_commP_anticommL; auto.
Qed.

Lemma anticommute_or_commute_T : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    anticommute_T t1 t2 \/ commute_T t1 t2.
Proof. intros n t1 t2 H0 H1.
  destruct H0 as [A0 A1].
  destruct H1 as [B0 B1].
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  simpl in *.
  destruct(list_eq_dec eqdec_Pauli l1 []) as [E | E];
    try (rewrite <- length_zero_iff_nil in E; lia).
  destruct(list_eq_dec eqdec_Pauli l2 []) as [E' | E'];
    try (rewrite <- length_zero_iff_nil in E'; lia).
  rewrite <- B1 in A1.
  assert (H0 : l1 <> [] \/ l2 <> []) by auto.
  destruct (anticommute_or_commute_listP l1 l2 H0 A1);
    try (left; constructor; assumption);
    try (right; constructor; assumption).
Qed.

Lemma anticommute_commute_T_no_middle : forall {n : nat} (t1 t2 : TType n),
    ~ anticommute_T t1 t2 \/ ~ commute_T t1 t2.
Proof. intros n t1 t2.
  apply Classical_Prop.not_and_or.
  intros [H1 H2].
  inversion H1. inversion H2.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  simpl in *.
  destruct (anticommute_commute_listP_no_middle l1 l2); auto.
Qed.

Inductive commute_AT {n : nat} (a : AType n) (t : TType n) : Prop :=
| termwise_commute_AT : Forall (commute_T t) a -> commute_AT a t.

Inductive anticommute_AT {n : nat} (a : AType n) (t : TType n) : Prop :=
| termwise_anticommute_AT : Forall (anticommute_T t) a -> anticommute_AT a t.


Lemma commute_AT_app : forall {n : nat} (a1 a2 : AType n) (t : TType n),
    commute_AT (a1 ++ a2) t <-> commute_AT a1 t /\ commute_AT a2 t.
Proof. intros n a1 a2 t.
  split; intros.
  - inversion H; subst; clear H.
    split; constructor; rewrite Forall_app in H0; destruct H0; auto.
  - constructor. destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (Forall (commute_T t) a1 /\ Forall (commute_T t) a2) by auto.
    rewrite <- Forall_app in H0; auto.
Qed.

Lemma anticommute_AT_app : forall {n : nat} (a1 a2 : AType n) (t : TType n),
    anticommute_AT (a1 ++ a2) t <-> anticommute_AT a1 t /\ anticommute_AT a2 t.
Proof. intros n a1 a2 t.
  split; intros.
  - inversion H; subst; clear H.
    split; constructor; rewrite Forall_app in H0; destruct H0; auto.
  - constructor. destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (Forall (anticommute_T t) a1 /\ Forall (anticommute_T t) a2) by auto.
    rewrite <- Forall_app in H0; auto.
Qed.

Lemma commute_AT_gScaleA : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    commute_AT a t -> commute_AT (gScaleA c a) t.
Proof. intros n a t c H.
  constructor.
  inversion H; subst; clear H.
  induction H0.
  - simpl. constructor.
  - constructor; auto.
    destruct x; destruct t.
    simpl in *.
    constructor.
    inversion H; subst; clear H.
    simpl in *; auto.
Qed.

Lemma anticommute_AT_gScaleA : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    anticommute_AT a t -> anticommute_AT (gScaleA c a) t.
Proof. intros n a t c H.
  constructor.
  inversion H; subst; clear H.
  induction H0.
  - simpl. constructor.
  - constructor; auto.
    destruct x; destruct t.
    simpl in *.
    constructor.
    inversion H; subst; clear H.
    simpl in *; auto.
Qed.

Lemma commute_AT_gScaleA_inv : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    c <> C0 -> commute_AT (gScaleA c a) t -> commute_AT a t.
Proof. intros n a t c H0 H1.
  apply commute_AT_gScaleA with (c := (/c)%C) in H1.
  rewrite gScaleA_merge in H1.
  rewrite Cinv_l in H1; auto.
  rewrite gScaleA_1 in H1; auto.
Qed. 

Lemma anticommute_AT_gScaleA_inv : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    c <> C0 -> anticommute_AT (gScaleA c a) t -> anticommute_AT a t.
Proof. intros n a t c H0 H1.
  apply anticommute_AT_gScaleA with (c := (/c)%C) in H1.
  rewrite gScaleA_merge in H1.
  rewrite Cinv_l in H1; auto.
  rewrite gScaleA_1 in H1; auto.
Qed. 

Lemma commute_AT_gScaleT : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    commute_AT a t -> commute_AT a (gScaleT c t).
Proof. intros n a t c H.
  constructor.
  inversion H; subst; clear H.
  induction H0.
  - simpl. constructor.
  - constructor; auto.
    constructor. inversion H; subst; clear H.
    destruct t; destruct x; simpl; auto.
Qed.

Lemma anticommute_AT_gScaleT : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    anticommute_AT a t -> anticommute_AT a (gScaleT c t).
Proof. intros n a t c H.
  constructor.
  inversion H; subst; clear H.
  induction H0.
  - simpl. constructor.
  - constructor; auto.
    constructor. inversion H; subst; clear H.
    destruct t; destruct x; simpl; auto.
Qed.

Lemma commute_AT_gScaleT_inv : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    c <> C0 -> commute_AT a (gScaleT c t) -> commute_AT a t.
Proof. intros n a t c H H0.
  apply commute_AT_gScaleT with (c := (/c)%C) in H0.
  rewrite gScaleT_merge in H0.
  rewrite Cinv_l in H0; auto.
  rewrite gScaleT_1 in H0; auto.
Qed.

Lemma anticommute_AT_gScaleT_inv : forall {n : nat} (a : AType n) (t : TType n) (c : C),
    c <> C0 -> anticommute_AT a (gScaleT c t) -> anticommute_AT a t.
Proof. intros n a t c H H0.
  apply anticommute_AT_gScaleT with (c := (/c)%C) in H0.
  rewrite gScaleT_merge in H0.
  rewrite Cinv_l in H0; auto.
  rewrite gScaleT_1 in H0; auto.
Qed.
  
Lemma commute_AT_in_iff : forall {n : nat} (a : AType n) (t : TType n),
    commute_AT a t <-> (forall (t' : TType n), In t' a -> commute_T t t').
Proof. intros n a t.
  split; intros.
  - inversion H; subst; clear H.
    gen t'.
    induction H1; intros.
    + inversion H0.
    + inversion H0; subst; clear H0; auto.
  - constructor.
    induction a as [ | t'' a'']; constructor.
    + apply H; simpl; auto.
    + apply IHa''.
      intros t' H1.
      specialize (H t').
      assert (In t' (t'' :: a'')); simpl; auto.
Qed.
  
Lemma anticommute_AT_in_iff : forall {n : nat} (a : AType n) (t : TType n),
    anticommute_AT a t <-> (forall (t' : TType n), In t' a -> anticommute_T t t').
Proof. intros n a t.
  split; intros.
  - inversion H; subst; clear H.
    gen t'.
    induction H1; intros.
    + inversion H0.
    + inversion H0; subst; clear H0; auto.
  - constructor.
    induction a as [ | t'' a'']; constructor.
    + apply H; simpl; auto.
    + apply IHa''.
      intros t' H0.
      specialize (H t').
      assert (In t' (t'' :: a'')); simpl; auto.
Qed.

Inductive commute_A {n : nat} (a1 a2 : AType n) : Prop :=
| termwise_commute_A : Forall (commute_AT a2) a1 -> commute_A a1 a2.

Inductive anticommute_A {n : nat} (a1 a2 : AType n) : Prop :=
| termwise_anticommute_A : Forall (anticommute_AT a2) a1 -> anticommute_A a1 a2.

Lemma commute_A_in_iff : forall {n : nat} (a1 a2 : AType n),
    commute_A a1 a2 <->
    (forall (t1 t2 : TType n), In t1 a1 -> In t2 a2 -> commute_T t1 t2).
Proof. intros n a1 a2.
  split; intros.
  - gen t1 t2 a2. induction a1; intros.
    + inversion H0.
    + inversion H; clear H; auto.
      inversion H0; subst; clear H0.
      * inversion H2; subst; clear H2; auto.
        inversion H3; clear H3.
        inversion H; subst; clear H.
        -- inversion H1.
        -- inversion H1; subst; clear H1; auto.
           clear H4.
           induction H2.
           ++ inversion H.
           ++ inversion H; subst; auto.
      * inversion H2; subst; clear H2.
        apply termwise_commute_A in H5.
        apply (IHa1 t1 H t2 a2 H5 H1).
  - constructor.
    gen a2.
    induction a1 as [ | t3 a3]; intros; constructor.
    + rewrite commute_AT_in_iff.
      intros t' H0.
      apply H; simpl; auto.
    + apply IHa3.
      intros t1 t2 H0 H1.
      apply H; simpl; auto.
Qed.
    
Lemma anticommute_A_in_iff : forall {n : nat} (a1 a2 : AType n),
    anticommute_A a1 a2 <->
    (forall (t1 t2 : TType n), In t1 a1 -> In t2 a2 -> anticommute_T t1 t2).
Proof. intros n a1 a2.
  split; intros.
  - gen t1 t2 a2. induction a1; intros.
    + inversion H0.
    + inversion H; clear H; auto.
      inversion H0; subst; clear H0.
      * inversion H2; subst; clear H2; auto.
        inversion H3; clear H3.
        inversion H; subst; clear H.
        -- inversion H1.
        -- inversion H1; subst; clear H1; auto.
           clear H4.
           induction H2.
           ++ inversion H.
           ++ inversion H; subst; auto.
      * inversion H2; subst; clear H2.
        apply termwise_anticommute_A in H5.
        apply (IHa1 t1 H t2 a2 H5 H1).
  - constructor.
    gen a2.
    induction a1 as [ | t3 a3]; intros; constructor.
    + rewrite anticommute_AT_in_iff.
      intros t' H0.
      apply H; simpl; auto.
    + apply IHa3.
      intros t1 t2 H0 H1.
      apply H; simpl; auto.
Qed.

Lemma commute_A_swap : forall {n : nat} (a1 a2 : AType n),
    commute_A a1 a2 -> commute_A a2 a1.
Proof. intros n a1 a2 H.
  rewrite commute_A_in_iff.
  intros t1 t2 H0 H1.
  apply commute_T_swap.
  inversion H; clear H.
  gen t1 t2 a2.
  induction a1; intros.
  - inversion H1.
  - induction H2; intros.
    + inversion H1.
    + inversion H1; subst; clear H1; auto.
      inversion H; clear H.
      clear IHForall. clear H2.
      induction H1.
      * inversion H0.
      * inversion H0; subst; auto.
Qed.

Lemma anticommute_A_swap : forall {n : nat} (a1 a2 : AType n),
    anticommute_A a1 a2 -> anticommute_A a2 a1.
Proof. intros n a1 a2 H.
  rewrite anticommute_A_in_iff.
  intros t1 t2 H0 H1.
  apply anticommute_T_swap.
  inversion H; clear H.
  gen t1 t2 a2.
  induction a1; intros.
  - inversion H1.
  - induction H2; intros.
    + inversion H1.
    + inversion H1; subst; clear H1; auto.
      inversion H; clear H.
      clear IHForall. clear H2.
      induction H1.
      * inversion H0.
      * inversion H0; subst; auto.
Qed.

Lemma commute_T_helper : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    (commute_T t1 t2 -> commute_TType t1 t2).
Proof. intros n t1 t2 H0 H1 H2.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  inversion H2.
  gen n.
  apply commute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) =>
                forall n : nat,
                  @proper_length_TType n (c1, l1) ->
                  @proper_length_TType n (c2, l2) ->
                  @commute_T n (c1, l1) (c2, l2) -> @commute_TType n (c1, l1) (c2, l2))
         (P0 := fun (l1 l2 : list Pauli) =>
                 forall n : nat,
                   @proper_length_TType n (c1, l1) ->
                   @proper_length_TType n (c2, l2) ->
                   @anticommute_T n (c1, l1) (c2, l2) -> @anticommute_TType n (c1, l1) (c2, l2));
    intros; simpl in *; auto.
  - destruct H0.
    destruct H0 as [H0 | [H0 | H0]];
      unfold cBigMul, zipWith, gMul_Coef, uncurry;
      destruct P1; destruct P2; simpl; try lca; try discriminate.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (commute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@commute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct H13 as [H13 | [H13 | H13]];
      destruct P1; destruct P2; auto; discriminate.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (anticommute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@anticommute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite <- Copp_mult_distr_r, Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct P1; destruct P2; auto; try contradiction; try lca.
  - destruct H0.
    unfold cBigMul, zipWith, gMul_Coef, uncurry;
      destruct P1; destruct P2; simpl; try lca; try contradiction.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (commute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@commute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct P1; destruct P2; auto; try contradiction; try lca.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (anticommute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@anticommute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite <- Copp_mult_distr_r, ! Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct H13 as [H13 | [H13| H13]];
      destruct P1; destruct P2; auto; try discriminate; try lca.
Qed.

Lemma anticommute_T_helper : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    (anticommute_T t1 t2 -> anticommute_TType t1 t2).
Proof. intros n t1 t2 H0 H1 H2.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  inversion H2.
  gen n.
  apply anticommute_listP_ind'
    with (P := fun (l1 l2 : list Pauli) =>
                forall n : nat,
                  @proper_length_TType n (c1, l1) ->
                  @proper_length_TType n (c2, l2) ->
                  @commute_T n (c1, l1) (c2, l2) -> @commute_TType n (c1, l1) (c2, l2))
         (P0 := fun (l1 l2 : list Pauli) =>
                 forall n : nat,
                   @proper_length_TType n (c1, l1) ->
                   @proper_length_TType n (c2, l2) ->
                   @anticommute_T n (c1, l1) (c2, l2) -> @anticommute_TType n (c1, l1) (c2, l2));
    intros; simpl in *; auto.
  - destruct H0.
    destruct H0 as [H0 | [H0 | H0]];
      unfold cBigMul, zipWith, gMul_Coef, uncurry;
      destruct P1; destruct P2; simpl; try lca; try discriminate.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (commute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@commute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct H13 as [H13 | [H13 | H13]];
      destruct P1; destruct P2; auto; discriminate.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (anticommute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@anticommute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite <- Copp_mult_distr_r, Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct P1; destruct P2; auto; try contradiction; try lca.
  - destruct H0.
    unfold cBigMul, zipWith, gMul_Coef, uncurry;
      destruct P1; destruct P2; simpl; try lca; try contradiction.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (commute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@commute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct P1; destruct P2; auto; try contradiction; try lca.
  - unfold cBigMul, zipWith, uncurry in *; simpl.
    rewrite ! fold_left_Cmult.
    inversion H3; simpl in *.
    destruct n; try contradiction.
    apply Nat.succ_inj in H7.
    inversion H4; simpl in *.
    apply Nat.succ_inj in H9.
    destruct n.
    rewrite length_zero_iff_nil in H7, H9; subst.
    destruct (anticommute_listP_nonempty_equal_len [] [] H1) as [H' [H'' H''']];
      contradiction.
    assert (@proper_length_TType (S n) (c1, l0))
      by (unfold proper_length_TType; auto).
    assert (@proper_length_TType (S n) (c2, l3))
      by (unfold proper_length_TType; auto).
    assert (@anticommute_T (S n) (c1, l0) (c2, l3)) by (constructor; auto).
    specialize (H2 (S n) H10 H11 H12).
    rewrite H2.
    rewrite <- Copp_mult_distr_r, ! Copp_mult_distr_l.
    f_equal.
    inversion H0.
    unfold gMul_Coef;
      destruct H13 as [H13 | [H13 | H13]];
      destruct P1; destruct P2; auto; try discriminate; try lca.
Qed.

Lemma anticommute_commute_TType_no_middle : forall {n : nat} (t1 t2 : TType n),
    ~ anticommute_TType t1 t2 \/ ~ commute_TType t1 t2.
Proof. intros n t1 t2.
  apply Classical_Prop.not_and_or.
  intros [H0 H1].
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  unfold anticommute_TType, commute_TType in *.
  rewrite H1 in H0.
  destruct (cBigMul (zipWith gMul_Coef l2 l1)) eqn:E0.
  inversion H0.
  assert (r=0%R) by lra.
  assert (r0=0%R) by lra.
  subst. clear H0.
  unfold cBigMul, zipWith, uncurry in *; simpl in *.
  gen l2.
  induction l1; intros.
  - rewrite ! combine_nil in *; simpl in *.
    inversion E0.
    lra.
  -  destruct l2.
     + simpl in *.
       inversion E0.
       lra.
     + simpl in *.
       rewrite fold_left_Cmult in E0, H1.
       destruct (gMul_Coef_comm_anticomm p a).
       * pose (gMul_Coef_comm_1 p a H) as e.
         rewrite e in E0.
         rewrite <- H, e in H1.
         rewrite Cmult_1_l in E0, H1.
         apply (IHl1 l2); auto.
       * pose (gMul_Coef_anticomm_plus_minus_i p a H) as o.
         destruct o.
         -- rewrite H0 in H.
            rewrite <- Copp_opp in H.
            rewrite H0 in E0.
            rewrite <- H in H1.
            replace (0%R, 0%R) with (Ci * C0)%C in E0 by lca.
            apply Cmult_cancel_l in E0; try nonzero.
            replace (0%R, 0%R) with (- Ci * C0)%C in H1 by lca.
            apply Cmult_cancel_l in H1; try nonzero.
            apply (IHl1 l2); auto.
         -- rewrite H0 in H.
            rewrite <- Copp_opp, Copp_involutive in H.
            rewrite H0 in E0.
            rewrite <- H in H1.
            replace (0%R, 0%R) with (- Ci * C0)%C in E0 by lca.
            apply Cmult_cancel_l in E0; try nonzero.
            replace (0%R, 0%R) with (Ci * C0)%C in H1 by lca.
            apply Cmult_cancel_l in H1; try nonzero.
            apply (IHl1 l2); auto.
Qed.

Lemma logical_helper : forall (P1 P2 A A' B B' : Prop),
    (P1 -> P2 -> A -> A')  ->  (P1 -> P2 -> B -> B') ->
      (P1 -> P2 -> A \/ B) -> (~ A \/ ~ B) -> (~ A' \/ ~ B') ->
      (P1 -> P2 -> ((A <-> A') /\ (B <-> B') /\ (~ A <-> B) /\ (~ A' <-> B'))).
Proof. intros P1 P2 A A' B B' H0 H1 H2 H3 H4 H5 H6.
  repeat split; intros; auto.
  - destruct (H2 H5 H6); auto.
    pose (H1 H5 H6 H7); try contradiction.
    destruct H4; try contradiction.
  - destruct (H2 H5 H6); auto.
    pose (H0 H5 H6 H7); try contradiction.
    destruct H4; try contradiction.
  - destruct (H2 H5 H6); try contradiction; auto.
  - destruct H3; auto.
  - destruct (H2 H5 H6); auto.
    pose (H0 H5 H6 H7); try contradiction.
  - destruct H4; auto; try contradiction.
Qed.

Lemma anticommute_commute_T_TType_iff : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    ((anticommute_T t1 t2 <-> anticommute_TType t1 t2) /\
       (commute_T t1 t2 <-> commute_TType t1 t2) /\
       (~ anticommute_T t1 t2 <-> commute_T t1 t2) /\
       (~ anticommute_TType t1 t2 <-> commute_TType t1 t2)).
Proof. intros n t1 t2. 
  apply (logical_helper (proper_length_TType t1) (proper_length_TType t2)
           (anticommute_T t1 t2) (anticommute_TType t1 t2)
           (commute_T t1 t2) (commute_TType t1 t2)
           (anticommute_T_helper t1 t2) (commute_T_helper t1 t2)
           (anticommute_or_commute_T t1 t2)
           (anticommute_commute_T_no_middle t1 t2)
           (anticommute_commute_TType_no_middle t1 t2)).
Qed.

Lemma anticommute_AT_TType_AType_iff : forall {n : nat} (t : TType n) (a : AType n),
    proper_length_TType t -> proper_length_AType_nil a ->
    anticommute_AT a t <-> anticommute_TType_AType t a.
Proof. intros n t a H H0. 
  split; intros.
  - inversion H1. clear H1.
    induction H2; simpl; auto.
    inversion H0; subst; auto.
    split; auto.
    destruct (anticommute_commute_T_TType_iff t x H H5)
      as [H' [H'' [H''' H'''']]].
    rewrite <- H'; auto.
  - constructor.
    induction a.
    + constructor.
    + constructor.
      * simpl in *.
        destruct H1.
        inversion H0; subst; auto.
        destruct (anticommute_commute_T_TType_iff t a H H5)
          as [H' [H'' [H''' H'''']]].
        rewrite H'; auto.
      * apply IHa.
        -- inversion H0; subst; auto.
        -- destruct H1; auto.
Qed.

Lemma anticommute_A_AType_iff : forall {n : nat} (a1 a2 : AType n),
    proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_A a1 a2 <-> anticommute_AType_syntactic a1 a2.
Proof. intros n a1 a2 H H0.
  split; intros.
  - inversion H1. clear H1.
    induction H2; simpl; auto.
    + split.
      * inversion H; subst; auto.
        rewrite <- (anticommute_AT_TType_AType_iff x a2 H5 H0); auto.
      * apply IHForall.
        inversion H; subst; auto.
  - constructor.
    induction a1.
    + constructor.
    + constructor.
      * simpl in *.
        destruct H1.
        inversion H; subst; auto.
        rewrite (anticommute_AT_TType_AType_iff a a2 H5 H0); auto.
      * apply IHa1.
        -- inversion H; subst; auto.
        -- simpl in *.
           destruct H1; auto.
Qed.

Lemma anticommute_A_scale_l : forall {n : nat} (a1 a2 : AType n) (c : C),
    proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_A a1 a2 -> anticommute_A (gScaleA c a1) a2.
Proof. intros n a1 a2 c H0 H1 H2.
  remember H0 as H0'. clear HeqH0'.
  rewrite anticommute_A_AType_iff in H2; auto.
  apply (proper_length_AType_nil_gScaleA c a1) in H0.
  apply anticommute_A_swap.
  rewrite anticommute_A_AType_iff; auto.
  rewrite anticommute_AType_syntactic_gScaleA.
  rewrite <- anticommute_A_AType_iff; auto.
  apply anticommute_A_swap.
  rewrite anticommute_A_AType_iff; auto.
Qed.

Lemma anticommute_A_scale_r : forall {n : nat} (a1 a2 : AType n) (c : C),
    proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_A a1 a2 -> anticommute_A a1 (gScaleA c a2).
Proof. intros n a1 a2 c H0 H1 H2.
  apply anticommute_A_swap.
  apply anticommute_A_scale_l; auto.
  apply anticommute_A_swap; auto.
Qed.

Lemma anticommute_A_scale_inv_l : forall {n : nat} (a1 a2 : AType n) (c : C),
    c <> C0 -> proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_A (gScaleA c a1) a2 -> anticommute_A a1 a2.
Proof. intros n a1 a2 c H0 H1 H2 H3.
  apply anticommute_A_scale_l with (c := (/c)%C) in H3; auto.
  - rewrite gScaleA_merge in H3.
    rewrite Cinv_l in H3; auto.
    rewrite gScaleA_1 in H3; auto.
  - apply proper_length_AType_nil_gScaleA; auto.
Qed.

Lemma anticommute_A_scale_inv_r : forall {n : nat} (a1 a2 : AType n) (c : C),
    c <> C0 -> proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_A a1 (gScaleA c a2) -> anticommute_A a1 a2.
Proof. intros n a1 a2 c H0 H1 H2 H3.
  apply anticommute_A_scale_r with (c := (/c)%C) in H3; auto.
  - rewrite gScaleA_merge in H3.
    rewrite Cinv_l in H3; auto.
    rewrite gScaleA_1 in H3; auto.
  - apply proper_length_AType_nil_gScaleA; auto.
Qed.


Lemma WF_AType_anticommute : forall {n : nat} (a : AType n) (t1 t2 : TType n),
    WF_AType a -> In t1  a -> In t2  a -> t1 <> t2 -> anticommute_T t1 t2.
Proof. intros n a t1 t2 H H0 H1 H2.
  inversion H; subst; clear H.
  gen t1 t2.
  induction H3; intros.
  - inversion H0; subst; clear H0;
      inversion H1; subst; clear H1;
      contradiction.
  - rewrite gScaleA_dist_app in H0, H1.
    rewrite in_app_iff in H0, H1.
    destruct H0; destruct H1.
    + assert (C1 / √ 2 * (C1 * √ 2) = C1)%C by (field_simplify_eq; auto; nonzero).
      assert (t1 = gScaleT (C1 / √2)%C (gScaleT (C1 * √2)%C t1)).
      { rewrite gScaleT_merge.
        rewrite H3.
        rewrite gScaleT_1; auto. }
      rewrite H4 in H0.
      apply in_gScaleTA_mult_inv in H0.
      2:{ intro. apply Cmult_r with (c := (C1 * √2)%C) in H5.
          rewrite H3 in H5.
          rewrite Cmult_0_l in H5.
          inversion H5.
          lra. }
      assert (t2 = gScaleT (C1 / √2)%C (gScaleT (C1 * √2)%C t2)).
      { rewrite gScaleT_merge.
        rewrite H3.
        rewrite gScaleT_1; auto. }
      rewrite H5 in H1.
      apply in_gScaleTA_mult_inv in H1.
      2:{ intro. apply Cmult_r with (c := (C1 * √2)%C) in H6.
          rewrite H3 in H6.
          rewrite Cmult_0_l in H6.
          inversion H6.
          lra. }
      assert ((gScaleT (C1 * √ 2)%C t1) <> (gScaleT (C1 * √ 2)%C t2)).
      { intro. contradict H2.
        assert (forall {n : nat} (t1 t2 : TType n),
                   t1 = t2 -> gScaleT (C1 / √ 2)%C t1 = gScaleT (C1 / √ 2)%C t2)
          by (intros n' t' t'' H'; rewrite H'; auto).
        apply H2 in H6.
        rewrite ! gScaleT_merge in H6.
        rewrite ! H3 in H6.
        rewrite ! gScaleT_1 in H6.
        assumption. }
      pose (IHrestricted_addition_syntactic1 (gScaleT (C1 * √ 2)%C t1) H0
              (gScaleT (C1 * √ 2)%C t2) H1 H6) as H7.
      apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
      remember H3_ as H3_'. clear HeqH3_'.
      apply proper_length_AType_implies_proper_length_TType
        with (t := (gScaleT (C1 * √ 2)%C t1)) in H3_; auto.
      apply proper_length_AType_implies_proper_length_TType
        with (t := (gScaleT (C1 * √ 2)%C t2)) in H3_'; auto.
      destruct @anticommute_commute_T_TType_iff
        with (n := n) 
             (t1 := (gScaleT (C1 * √ 2)%C t1)) (t2 := (gScaleT (C1 * √ 2)%C t2))
        as [H' [H'' [H''' H'''']]]; auto.
      remember H7 as H7'. clear HeqH7'. clear H7.
      specialize (IHrestricted_addition_syntactic1
                    (gScaleT (C1 * √ 2)%C t1) H0
                    (gScaleT (C1 * √ 2)%C t2) H1
                    H6).
      rewrite H' in IHrestricted_addition_syntactic1.
      rewrite anticommute_TType_gScaleT in IHrestricted_addition_syntactic1.
      apply anticommute_TType_comm in IHrestricted_addition_syntactic1.
      rewrite anticommute_TType_gScaleT in IHrestricted_addition_syntactic1.
      apply anticommute_TType_comm in IHrestricted_addition_syntactic1.
      apply proper_length_TType_gScaleT
        with (t := (gScaleT (C1 * √ 2)%C t1)) (c := (C1 / √ 2)%C) in H3_.
      rewrite gScaleT_merge in H3_.
      rewrite H3 in H3_.
      rewrite gScaleT_1 in H3_.
      apply proper_length_TType_gScaleT
        with (t := (gScaleT (C1 * √ 2)%C t2)) (c := (C1 / √ 2)%C) in H3_'.
      rewrite gScaleT_merge in H3_'.
      rewrite H3 in H3_'.
      rewrite gScaleT_1 in H3_'.
      destruct @anticommute_commute_T_TType_iff
        with (n := n) 
             (t1 := t1) (t2 := t2)
        as [H0' [H0'' [H0''' H0'''']]]; auto.
      rewrite H0'; auto.
    + apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
      apply proper_length_AType_implies_proper_length_AType_nil in H3_, H3_0.
      rewrite <- anticommute_A_AType_iff in H; auto.
      apply anticommute_A_scale_l with (c := (C1 / √ 2)%C) in H; auto.
      apply anticommute_A_scale_r with (c := (C1 / √ 2)%C) in H; auto.
      2 : apply proper_length_AType_nil_gScaleA; auto.
      rewrite anticommute_A_in_iff in H.
      apply H; auto.
    + apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
      apply proper_length_AType_implies_proper_length_AType_nil in H3_, H3_0.
      rewrite <- anticommute_A_AType_iff in H; auto.
      apply anticommute_A_scale_l with (c := (C1 / √ 2)%C) in H; auto.
      apply anticommute_A_scale_r with (c := (C1 / √ 2)%C) in H; auto.
      2 : apply proper_length_AType_nil_gScaleA; auto.
      apply anticommute_A_swap in H.
      rewrite anticommute_A_in_iff in H.
      apply H; auto.
    + assert (C1 / √ 2 * (C1 * √ 2) = C1)%C by (field_simplify_eq; auto; nonzero).
      assert (t1 = gScaleT (C1 / √2)%C (gScaleT (C1 * √2)%C t1)).
      { rewrite gScaleT_merge.
        rewrite H3.
        rewrite gScaleT_1; auto. }
      rewrite H4 in H0.
      apply in_gScaleTA_mult_inv in H0.
      2:{ intro. apply Cmult_r with (c := (C1 * √2)%C) in H5.
          rewrite H3 in H5.
          rewrite Cmult_0_l in H5.
          inversion H5.
          lra. }
      assert (t2 = gScaleT (C1 / √2)%C (gScaleT (C1 * √2)%C t2)).
      { rewrite gScaleT_merge.
        rewrite H3.
        rewrite gScaleT_1; auto. }
      rewrite H5 in H1.
      apply in_gScaleTA_mult_inv in H1.
      2:{ intro. apply Cmult_r with (c := (C1 * √2)%C) in H6.
          rewrite H3 in H6.
          rewrite Cmult_0_l in H6.
          inversion H6.
          lra. }
      assert ((gScaleT (C1 * √ 2)%C t1) <> (gScaleT (C1 * √ 2)%C t2)).
      { intro. contradict H2.
        assert (forall {n : nat} (t1 t2 : TType n),
                   t1 = t2 -> gScaleT (C1 / √ 2)%C t1 = gScaleT (C1 / √ 2)%C t2)
          by (intros n' t' t'' H'; rewrite H'; auto).
        apply H2 in H6.
        rewrite ! gScaleT_merge in H6.
        rewrite ! H3 in H6.
        rewrite ! gScaleT_1 in H6.
        assumption. }
      pose (IHrestricted_addition_syntactic2 (gScaleT (C1 * √ 2)%C t1) H0
              (gScaleT (C1 * √ 2)%C t2) H1 H6) as H7.
      apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
      remember H3_0 as H3_0'. clear HeqH3_0'.
      apply proper_length_AType_implies_proper_length_TType
        with (t := (gScaleT (C1 * √ 2)%C t1)) in H3_0; auto.
      apply proper_length_AType_implies_proper_length_TType
        with (t := (gScaleT (C1 * √ 2)%C t2)) in H3_0'; auto.
      destruct @anticommute_commute_T_TType_iff
        with (n := n) 
             (t1 := (gScaleT (C1 * √ 2)%C t1)) (t2 := (gScaleT (C1 * √ 2)%C t2))
        as [H' [H'' [H''' H'''']]]; auto.
      remember H7 as H7'. clear HeqH7'. clear H7.
      specialize (IHrestricted_addition_syntactic2
                    (gScaleT (C1 * √ 2)%C t1) H0
                    (gScaleT (C1 * √ 2)%C t2) H1
                    H6).
      rewrite H' in IHrestricted_addition_syntactic2.
      rewrite anticommute_TType_gScaleT in IHrestricted_addition_syntactic2.
      apply anticommute_TType_comm in IHrestricted_addition_syntactic2.
      rewrite anticommute_TType_gScaleT in IHrestricted_addition_syntactic2.
      apply anticommute_TType_comm in IHrestricted_addition_syntactic2.
      apply proper_length_TType_gScaleT
        with (t := (gScaleT (C1 * √ 2)%C t1)) (c := (C1 / √ 2)%C) in H3_0.
      rewrite gScaleT_merge in H3_0.
      rewrite H3 in H3_0.
      rewrite gScaleT_1 in H3_0.
      apply proper_length_TType_gScaleT
        with (t := (gScaleT (C1 * √ 2)%C t2)) (c := (C1 / √ 2)%C) in H3_0'.
      rewrite gScaleT_merge in H3_0'.
      rewrite H3 in H3_0'.
      rewrite gScaleT_1 in H3_0'.
      destruct @anticommute_commute_T_TType_iff
        with (n := n) 
             (t1 := t1) (t2 := t2)
        as [H0' [H0'' [H0''' H0'''']]]; auto.
      rewrite H0'; auto.
Qed.

Lemma self_commute_P : forall (P : Pauli), commute_P P P.
Proof. intros P. constructor. do 2 right; auto. Qed.

Lemma self_commute_listP : forall (l : list Pauli), l <> [] -> commute_listP l l.
Proof. intros l. induction l; intros; try contradiction.
  destruct (list_eq_dec eqdec_Pauli l []).
  - subst. constructor. apply self_commute_P.
  - apply IHl in n.
    apply (commuting_listP_commP_commL a a l l (self_commute_P a) n).
Qed.

Lemma self_commute_T : forall {n : nat} (t : TType n),
    proper_length_TType t -> commute_T t t.
Proof. intros n t H0.
  constructor.
  destruct t as [c l].
  inversion H0.
  simpl in *.
  destruct (list_eq_dec eqdec_Pauli l []) as [H3 | H3].
  - rewrite <- length_zero_iff_nil in H3. lia.
  - apply self_commute_listP; auto.
Qed.

Lemma WF_MulTA_helper : forall {n : nat} (t : TType n) (a : AType n),
    WF_TType t -> WF_AType a -> commute_AT a t -> (forall c : C, a <> [(c, snd t)]) -> 
    Forall (fun t' => snd t' <> snd t) a.
Proof. intros n t a H H0 H1 H2.
  inversion H0; subst; clear H0.
  rewrite Forall_Exists_neg.
  intro.
  gen t.
  induction H3; intros.
  - destruct t as [c l].
    destruct t0 as [c0 l0]. 
    simpl in *.
    specialize (H2 c).
    assert (l <> l0) by (intro; subst; contradiction).
    inversion H3; subst; clear H3; auto.
    inversion H6.
  - clear H2.
    rewrite gScaleA_dist_app in H3.
    rewrite Exists_app in H3.
    destruct H3.
    + rewrite gScaleA_dist_app in H1.
      rewrite commute_AT_app in H1.
      destruct H1.
      rewrite Exists_exists in H2.
      destruct H2 as [t0 [t0_in equal_pauli]].
      destruct t as [c l].
      destruct t0 as [c0 l0].
      simpl in *.
      subst.
      remember H3_0 as H3_0'. clear HeqH3_0'.
      apply restricted_addition_syntactic_implies_proper_length_AType in H3_0'.
      destruct H3_0'.
      * apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
        remember H3_ as H3_'. clear HeqH3_'.
        remember H3_0 as H3_0'. clear HeqH3_0'.
        apply proper_length_AType_implies_proper_length_AType_nil in H3_', H3_0'.
        rewrite <- anticommute_A_AType_iff in H; auto.
        rewrite anticommute_A_in_iff in H.
        apply @in_gScaleTA_mult with (n := n) (c := (C1 * √2)%C) in t0_in; auto.
        rewrite gScaleA_merge in t0_in.
        assert ((C1 * √ 2 * (C1 / √ 2))%C = C1).
        { field_simplify_eq; auto; nonzero. }
        rewrite H4 in t0_in.
        rewrite gScaleA_1 in t0_in.
        assert (In t [t]) by (simpl;auto).
        specialize (H (gScaleT (C1 * √ 2)%C (c0, l)) t t0_in H5).
        assert (anticommute_T (c0,l) t).
        { constructor. inversion H; subst; clear H. destruct t. simpl in *. auto. }
        inversion H3; subst; clear H3.
        inversion H7; subst; clear H7.
        destruct t as [c' l'].
        assert (anticommute_listP l l').
        { inversion H6; subst; clear H6; simpl; auto. }
        assert (commute_listP l l').
        { inversion H9; subst; clear H9; simpl; auto. }
        destruct (anticommute_commute_listP_no_middle l l'); contradiction.
      * apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
        remember H3_ as H3_'. clear HeqH3_'.
        remember H3_0 as H3_00'. clear HeqH3_00'.
        apply proper_length_AType_implies_proper_length_AType_nil in H3_', H3_00'.
        rewrite <- anticommute_A_AType_iff in H; auto.
        rewrite anticommute_A_in_iff in H.
        apply @in_gScaleTA_mult with (n := n) (c := (C1 * √2)%C) in t0_in; auto.
        rewrite gScaleA_merge in t0_in.
        assert ((C1 * √ 2 * (C1 / √ 2))%C = C1).
        { field_simplify_eq; auto; nonzero. }
        rewrite H4 in t0_in.
        rewrite gScaleA_1 in t0_in.
        assert (In t (t :: a)) by (simpl;auto).
        specialize (H (gScaleT (C1 * √ 2)%C (c0, l)) t t0_in H5).
        assert (anticommute_T (c0,l) t).
        { constructor. inversion H; subst; clear H. destruct t. simpl in *. auto. }
        inversion H3; subst; clear H3.
        inversion H7; subst; clear H7.
        destruct t as [c' l'].
        assert (anticommute_listP l l').
        { inversion H6; subst; clear H6; simpl; auto. }
        assert (commute_listP l l').
        { inversion H9; subst; clear H9; simpl; auto. }
        destruct (anticommute_commute_listP_no_middle l l'); contradiction.
    + rewrite gScaleA_dist_app in H1.
      rewrite commute_AT_app in H1.
      destruct H1.
      rewrite Exists_exists in H2.
      destruct H2 as [t0 [t0_in equal_pauli]].
      destruct t as [c l].
      destruct t0 as [c0 l0].
      simpl in *.
      subst.
      remember H3_ as H3_'. clear HeqH3_'.
      apply restricted_addition_syntactic_implies_proper_length_AType in H3_'.
      destruct H3_'.
      * apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
        remember H3_ as H3__'. clear HeqH3__'.
        remember H3_0 as H3_0'. clear HeqH3_0'.
        apply proper_length_AType_implies_proper_length_AType_nil in H3__', H3_0'.
        rewrite <- anticommute_A_AType_iff in H; auto.
        rewrite anticommute_A_in_iff in H.
        apply @in_gScaleTA_mult with (n := n) (c := (C1 * √2)%C) in t0_in; auto.
        rewrite gScaleA_merge in t0_in.
        assert ((C1 * √ 2 * (C1 / √ 2))%C = C1).
        { field_simplify_eq; auto; nonzero. }
        rewrite H4 in t0_in.
        rewrite gScaleA_1 in t0_in.
        assert (In t [t]) by (simpl;auto).
        specialize (H t (gScaleT (C1 * √ 2)%C (c0, l)) H5 t0_in).
        assert (anticommute_T t (c0,l)).
        { constructor. inversion H; subst; clear H. destruct t. simpl in *. auto. }
        inversion H1; subst; clear H1.
        inversion H7; subst; clear H7.
        destruct t as [c' l'].
        assert (anticommute_listP l' l).
        { inversion H6; subst; clear H6; simpl; auto. }
        assert (commute_listP l l').
        { inversion H9; subst; clear H9; simpl; auto. }
        apply commute_listP_swap in H7.
        destruct (anticommute_commute_listP_no_middle l' l); contradiction.
      * apply restricted_addition_syntactic_implies_proper_length_AType in H3_, H3_0.
        remember H3_ as H3__'. clear HeqH3__'.
        remember H3_0 as H3_0'. clear HeqH3_0'.
        apply proper_length_AType_implies_proper_length_AType_nil in H3__', H3_0'.
        rewrite <- anticommute_A_AType_iff in H; auto.
        rewrite anticommute_A_in_iff in H.
        apply @in_gScaleTA_mult with (n := n) (c := (C1 * √2)%C) in t0_in; auto.
        rewrite gScaleA_merge in t0_in.
        assert ((C1 * √ 2 * (C1 / √ 2))%C = C1).
        { field_simplify_eq; auto; nonzero. }
        rewrite H4 in t0_in.
        rewrite gScaleA_1 in t0_in.
        assert (In t (t :: a)) by (simpl;auto).
        specialize (H t (gScaleT (C1 * √ 2)%C (c0, l)) H5 t0_in).
        assert (anticommute_T t (c0,l)).
        { constructor. inversion H; subst; clear H. destruct t. simpl in *. auto. }
        inversion H1; subst; clear H1.
        inversion H7; subst; clear H7.
        destruct t as [c' l'].
        assert (anticommute_listP l' l).
        { inversion H6; subst; clear H6; simpl; auto. }
        assert (commute_listP l l').
        { inversion H9; subst; clear H9; simpl; auto. }
        apply commute_listP_swap in H7.
        destruct (anticommute_commute_listP_no_middle l' l); contradiction.
Qed.

Lemma WF_AType_in_nonzero : forall {n : nat} (a : AType n) (t : TType n),
    WF_AType a -> In t a ->  fst t <> C0.
Proof. intros n a t H H0 H1.
  gen t.
  inversion H; subst; clear H.
  induction H0; intros.
  - inversion H0; subst; clear H0.
    + inversion H; subst; clear H.
      unfold coef_plus_minus_1 in H2.
      rewrite H1 in H2.
      destruct H2 as [H' | H']; inversion H'; lra.
    + inversion H2.
  - apply in_gScaleTA_mult with (c := (C1 * √ 2)%C) in H0.
    rewrite gScaleA_merge in H0.
    assert ((C1 * √ 2 * (C1 / √ 2))%C = C1) by (field_simplify_eq; auto; nonzero).
    rewrite H2 in H0.
    rewrite gScaleA_1 in H0.
    rewrite in_app_iff in H0.
    assert (fst (gScaleT (C1 * √ 2)%C t) = C0).
    { destruct t; simpl in *. rewrite H1. lca. }
    destruct H0.
    + apply (IHrestricted_addition_syntactic1 (gScaleT (C1 * √ 2)%C t)); auto.
    + apply (IHrestricted_addition_syntactic2 (gScaleT (C1 * √ 2)%C t)); auto.
Qed.




Definition anticommute_AType_semantic {n : nat} (a1 a2 : AType n) : Prop :=
  (translateA a1)×(translateA a2) = -C1 .* (translateA a2)×(translateA a1).

Inductive restricted_addition_semantic {n : nat}: AType n -> Prop :=
| add_restrict_base_semantic : forall (t : TType n), WF_TType t -> restricted_addition_semantic [t]
| add_restrict_inductive_semantic : forall (a1 a2 : AType n),
    restricted_addition_semantic a1 -> restricted_addition_semantic a2 ->
    anticommute_AType_semantic a1 a2 -> 
    restricted_addition_semantic (gScaleA (1/√2) (a1 ++ a2)).


Lemma restricted_addition_semantic_implies_proper_length_AType: forall {n : nat} (a : AType n),
  restricted_addition_semantic a -> proper_length_AType a.
Proof. intros n a H. induction H.
  - constructor. inversion H. assumption.
  - apply proper_length_AType_gScaleA.
    apply proper_length_AType_App; assumption.
Qed.



Lemma Pauli_anticomm_cons_comm_anticomm : forall (p p0 : Pauli) (l l0 : list Pauli),
    length l = length l0 ->
    cBigMul (zipWith gMul_Coef (p :: l) (p0 :: l0)) =
      (- cBigMul (zipWith gMul_Coef (p0 :: l0) (p :: l)))%C ->
    (gMul_Coef p p0 = (- gMul_Coef p0 p)%C ->
     cBigMul (zipWith gMul_Coef l l0) =
       cBigMul (zipWith gMul_Coef l0 l)) /\
      (gMul_Coef p p0 = gMul_Coef p0 p ->
       cBigMul (zipWith gMul_Coef l l0) =
         (- cBigMul (zipWith gMul_Coef l0 l))%C).
Proof. intros p p0 l l0 H H0. split.
  - intros H1. destruct p, p0; simpl in H1; inversion H1; try (contradict H1; lra);
      unfold cBigMul, gMul_Coef, zipWith, uncurry in *; simpl in *;
      rewrite ! fold_left_Cmult in H0; rewrite Copp_mult_distr_l in *;
      try rewrite ! Copp_involutive in H0; apply C_inv_l in H0; try nonzero; try easy; apply C0_snd_neq; simpl; lra.
  - intros H1. destruct p, p0; simpl in H1; inversion H1; try (contradict H1; lra);
      unfold cBigMul, gMul_Coef, zipWith, uncurry in *; simpl in *;
      rewrite ! fold_left_Cmult in H0; rewrite ! Cmult_1_l in H0; easy.
Qed.

Lemma Pauli_comm_cons_comm_anticomm : forall (p p0 : Pauli) (l l0 : list Pauli),
    length l = length l0 ->
    cBigMul (zipWith gMul_Coef (p :: l) (p0 :: l0)) =
      cBigMul (zipWith gMul_Coef (p0 :: l0) (p :: l)) ->
    (gMul_Coef p p0 =  gMul_Coef p0 p ->
     cBigMul (zipWith gMul_Coef l l0) =
       cBigMul (zipWith gMul_Coef l0 l)) /\
      (gMul_Coef p p0 = (- gMul_Coef p0 p)%C ->
       cBigMul (zipWith gMul_Coef l l0) =
         (- cBigMul (zipWith gMul_Coef l0 l))%C).
Proof. intros p p0 l l0 H H0. split.
  - intros H1. destruct p, p0; simpl in H1; inversion H1; try (contradict H1; lra);
      unfold cBigMul, gMul_Coef, zipWith, uncurry in *; simpl in *;
      rewrite ! fold_left_Cmult in H0; try rewrite ! Copp_involutive in H0;
      apply C_inv_l in H0; try nonzero; try easy; apply C0_snd_neq; simpl; lra.
  - intros H1. destruct p, p0; simpl in H1; inversion H1; try lra;
      unfold cBigMul, zipWith, uncurry in *; simpl in *;
      rewrite ! fold_left_Cmult in H0; try rewrite ! Cmult_1_l in H0;
      try rewrite <- ! Copp_mult_distr_l in H0; try rewrite ! Copp_mult_distr_r in H0;
      try apply C_inv_l in H0;
      try easy; try nonzero; try apply Copp_opp in H0; try easy.
Qed.

Lemma Pauli_comm_syntactic_implies_semantic : forall (p1 p2 : Pauli),
    gMul_Coef p1 p2 = gMul_Coef p2 p1 -> translate_P p1 × translate_P p2 = translate_P p2 × translate_P p1.
Proof. intros. destruct p1, p2; simpl in *; try lma'; inversion H; lra. Qed.

Lemma Pauli_anticomm_syntactic_implies_semantic : forall (p1 p2 : Pauli),
    gMul_Coef p1 p2 = (- gMul_Coef p2 p1)%C -> translate_P p1 × translate_P p2 = -C1 .* translate_P p2 × translate_P p1.
Proof. intros. destruct p1, p2; simpl in *; try lma'; inversion H; lra. Qed.

Lemma Pauli_comm_or_anticomm_syntactic : forall (p1 p2 : Pauli),
    gMul_Coef p1 p2 = gMul_Coef p2 p1 \/ gMul_Coef p1 p2 = (- gMul_Coef p2 p1)%C. 
Proof. intros. destruct p1, p2; simpl;
     [ left | left | left | left |
    left | left | right | right |
    left | right | left | right |
       left | right | right | left ];
    lca.
Qed.

Lemma Pauli_comm_or_anticomm_semantic : forall (p1 p2 : Pauli),
    translate_P p1 × translate_P p2 = translate_P p2 × translate_P p1
    \/
      translate_P p1 × translate_P p2 = -C1 .* translate_P p2 × translate_P p1.
Proof. intros. destruct p1, p2; simpl;
  [ left | left | left | left |
    left | left | right | right |
    left | right | left | right |
    left | right | right | left ];
    lma'.
Qed.

Lemma anticommute_commute_TType_syntactic_implies_semantic_nil : forall {n : nat} (t1 t2 : TType n),
    length (snd t1) = length (snd t2) ->
    proper_length_TType_nil t1 -> proper_length_TType_nil t2 ->
    ((anticommute_TType t1 t2 ->
      translate t1 × translate t2 .+ translate t2 × translate t1 = Zero)
     /\ (commute_TType t1 t2 ->
        translate t1 × translate t2 = translate t2 × translate t1)).
Proof. intros n t1 t2 H H0 H1. unfold anticommute_TType, commute_TType.
  destruct t1, t2.
  simpl in *.
  unfold translate. simpl.
  rewrite ! map_length.

  rewrite ! H.
  inversion H1.
  setoid_rewrite Mscale_mult_dist_l at 1.
  setoid_rewrite Mscale_mult_dist_r at 2.
  setoid_rewrite Mscale_mult_dist_l at 1.
  setoid_rewrite Mscale_mult_dist_r at 1.
  setoid_rewrite Mscale_mult_dist_l at 1.
  setoid_rewrite Mscale_mult_dist_r at 2.
  setoid_rewrite Mscale_mult_dist_l at 1.
  setoid_rewrite Mscale_mult_dist_r at 1.
  distribute_scale.
  setoid_rewrite <- Mscale_plus_distr_r.
  clear H2.

  gen n.
  gen l0. gen l.
  induction l; intros; simpl in *.
  - symmetry in H. rewrite length_zero_iff_nil in H. rewrite H.
    split; intros; lma'.
    unfold cBigMul, zipWith, gMul_Coef, uncurry in *; simpl in *.
    inversion H2. lra.
  - destruct l0; try discriminate.
    simpl in *.
    split; intros; simpl in *.
    + apply Pauli_anticomm_cons_comm_anticomm in H2; auto.
      destruct H2.
      destruct (Pauli_comm_or_anticomm_syntactic a p).
      * remember H4 as H5. clear HeqH5.
        apply H3 in H4.
        apply Pauli_comm_syntactic_implies_semantic in H5.
        inversion H.
        rewrite ! map_length. 
        rewrite ! H7.
        setoid_rewrite kron_mixed_product.
        rewrite H5.
        setoid_rewrite <- kron_plus_distr_l.
        assert (@proper_length_TType_nil (length l0) (c, l)). { easy. }
        assert (@proper_length_TType_nil (length l0) (c, l0)). { easy. }
        pose (IHl l0 H7  (length l0) H6 H8).
        destruct a0.
        apply H9 in H4.
        setoid_rewrite <- Mscale_kron_dist_r.
        rewrite H4.
        rewrite kron_0_r.
        reflexivity.
      * remember H4 as H5. clear HeqH5.
        apply H2 in H4.
        apply Pauli_anticomm_syntactic_implies_semantic in H5.
        inversion H.
        rewrite ! map_length. 
        rewrite ! H7.
        setoid_rewrite kron_mixed_product.
        rewrite H5.
        distribute_scale.
        rewrite <- Mscale_kron_dist_r.
        setoid_rewrite <- kron_plus_distr_l.
        assert (@proper_length_TType_nil (length l0) (c, l)). { easy. }
        assert (@proper_length_TType_nil (length l0) (c, l0)). { easy. }
        pose (IHl l0 H7  (length l0) H6 H8).
        destruct a0.
        apply H10 in H4.
        setoid_rewrite <- Mscale_kron_dist_r.
        rewrite Mscale_plus_distr_r.
        setoid_rewrite Mscale_assoc at 1.
        setoid_rewrite Cmult_comm at 1.
        setoid_rewrite <- Mscale_assoc at 1.
        rewrite H4.
        rewrite Mplus_opp_l.
        rewrite kron_0_r.
        reflexivity.
        apply WF_scale.
        apply WF_mult.
        rewrite <- map_length with (f := translate_P).
        apply WF_Matrix_Big_Pauli.
        rewrite <- H7.
        rewrite <- map_length with (f := translate_P).
        apply WF_Matrix_Big_Pauli.
    + apply Pauli_comm_cons_comm_anticomm in H2; auto.
      destruct H2.
      destruct (Pauli_comm_or_anticomm_syntactic a p).
      * remember H4 as H5. clear HeqH5.
        apply H2 in H4.
        apply Pauli_comm_syntactic_implies_semantic in H5.
        inversion H.
        rewrite ! map_length. 
        rewrite ! H7.
        setoid_rewrite kron_mixed_product.
        rewrite H5.
        assert (@proper_length_TType_nil (length l0) (c, l)). { easy. }
        assert (@proper_length_TType_nil (length l0) (c, l0)). { easy. }
        pose (IHl l0 H7  (length l0) H6 H8).
        destruct a0.
        apply H10 in H4.
        setoid_rewrite <- Mscale_kron_dist_r.
        rewrite H4.
        reflexivity.
      * remember H4 as H5. clear HeqH5.
        apply H3 in H4.
        apply Pauli_anticomm_syntactic_implies_semantic in H5.
        inversion H.
        rewrite ! map_length. 
        rewrite ! H7.
        setoid_rewrite kron_mixed_product.
        rewrite H5.
        distribute_scale.
        rewrite <- Mscale_kron_dist_r.
        assert (@proper_length_TType_nil (length l0) (c, l)). { easy. }
        assert (@proper_length_TType_nil (length l0) (c, l0)). { easy. }
        pose (IHl l0 H7  (length l0) H6 H8).
        destruct a0.
        apply H9 in H4.
        setoid_rewrite <- Mscale_kron_dist_r.
        setoid_rewrite Mscale_assoc at 1.
        setoid_rewrite Cmult_comm at 1.
        setoid_rewrite <- Mscale_assoc at 1.
        rewrite Mscale_plus_distr_r in H4.
        rewrite Mplus_comm in H4.
        rewrite Mplus_zero_iff_equals_minus in H4.
        rewrite <- H4.
        reflexivity.
        apply WF_scale.
        apply WF_mult.
        rewrite <- H7.
        rewrite <- map_length with (f := translate_P).
        apply WF_Matrix_Big_Pauli.
        rewrite <- map_length with (f := translate_P).
        apply WF_Matrix_Big_Pauli.
Qed.

Lemma anticommute_commute_TType_syntactic_implies_semantic: forall {n : nat} (t1 t2 : TType n),
    length (snd t1) = length (snd t2) ->
    proper_length_TType t1 -> proper_length_TType t2 ->
    ((anticommute_TType t1 t2 ->
      translate t1 × translate t2 .+ translate t2 × translate t1 = Zero)
     /\ (commute_TType t1 t2 ->
        translate t1 × translate t2 = translate t2 × translate t1)).
Proof. intros. apply proper_length_TType_implies_proper_length_TType_nil in H0.
  apply proper_length_TType_implies_proper_length_TType_nil in H1.
  apply anticommute_commute_TType_syntactic_implies_semantic_nil; auto.
Qed.

Lemma anticommute_AType_implies_semantic_anticommute_nil : forall {n : nat} (a1 a2 : AType n),
    proper_length_AType_nil a1 -> proper_length_AType_nil a2 ->
    anticommute_AType_syntactic a1 a2 -> anticommute_AType_semantic a1 a2.
Proof. intros n a1 a2 G1 G2 H. unfold anticommute_AType_semantic.
  induction a1.
  - unfold translateA. simpl in *. rewrite Mmult_0_l, Mmult_0_r. reflexivity.
  - unfold translateA in *. simpl in *.
    destruct H.
    inversion G1; subst.
    apply IHa1 in H0; auto.
    rewrite ! fold_left_Mplus. rewrite ! Mmult_plus_distr_l, ! Mmult_plus_distr_r.
    rewrite H0. f_equal.
    clear IHa1. clear H3. clear H4. clear H0.
    induction a2.
    + simpl in *. distribute_scale. rewrite Mmult_0_l, Mmult_0_r, Mscale_0_r. reflexivity.
    + simpl in *.
      destruct H.
      inversion G2; subst.
      apply IHa2 in H0; auto.
      rewrite ! fold_left_Mplus. distribute_scale.
      rewrite ! Mmult_plus_distr_l, ! Mmult_plus_distr_r.
      rewrite H0. rewrite Mscale_plus_distr_r, Mscale_mult_dist_l.
      f_equal.
      inversion G1; inversion G2.
      clear - n a a0 H H5 H9.
      inversion H5. inversion H9. rewrite <- H3 in H1.
      destruct (anticommute_commute_TType_syntactic_implies_semantic a a0 H1 H5 H9).
      apply H4 in H.
      rewrite <- Mplus_zero_iff_equals_minus.
      assumption.
      auto with wf_db.
Qed.

Lemma anticommute_AType_implies_semantic_anticommute : forall {n : nat} (a1 a2 : AType n),
    proper_length_AType a1 -> proper_length_AType a2 ->
    anticommute_AType_syntactic a1 a2 -> anticommute_AType_semantic a1 a2.
Proof. intros. apply proper_length_AType_implies_proper_length_AType_nil in H.
  apply proper_length_AType_implies_proper_length_AType_nil in H0.
  apply anticommute_AType_implies_semantic_anticommute_nil; auto.
Qed.

Lemma restricted_addition_syntactic_implies_semantic : forall {n : nat} (A : AType n),
    restricted_addition_syntactic A -> restricted_addition_semantic A.
Proof.
  intros n A H. induction H.
  - constructor. assumption.
  - constructor; try easy.
    apply restricted_addition_syntactic_implies_proper_length_AType in H.
    apply restricted_addition_syntactic_implies_proper_length_AType in H0.
    apply anticommute_AType_implies_semantic_anticommute in H1; auto.
Qed.
    

Lemma restricted_addition_semantic_implies_trace_zero : forall {n : nat} (A : AType n),
    restricted_addition_semantic A -> trace (translateA A) = C0.
Proof. intros. induction H.
  - do 2 destruct H. unfold translateA.
    destruct t. unfold translate.
    simpl in *. rewrite Mplus_0_l.
    rewrite map_length.
    rewrite H2.
    rewrite trace_mult_dist.
    rewrite <- H2.
    rewrite <- map_length with (f := translate_P).
    rewrite trace_zero_syntax_implies_trace_zero; auto; lca.
  - rewrite translateA_gScaleA.
    rewrite trace_mult_dist.
    rewrite translateA_app.
    rewrite trace_plus_dist.
    rewrite IHrestricted_addition_semantic1.
    rewrite IHrestricted_addition_semantic2.
    rewrite Cplus_0_l, Cmult_0_r.
    reflexivity.
    apply proper_length_AType_App.
    apply restricted_addition_semantic_implies_proper_length_AType in H.
    assumption.
    apply restricted_addition_semantic_implies_proper_length_AType in H0.
    assumption.
Qed.

Lemma restricted_addition_semantic_implies_Hermitian : forall {n : nat} (A : AType n),
    restricted_addition_semantic A -> (translateA A) † = (translateA A).
Proof. intros. 
  induction H.
  - unfold translateA. unfold translate. destruct t. simpl. rewrite ! Mplus_0_l.
    destruct H. simpl in *.
    destruct H0; simpl in H0; rewrite H0.
    + rewrite Mscale_1_l. apply list_Pauli_Hermitian.
    + rewrite map_length. destruct H. simpl in *.
      rewrite H2.
      rewrite Mscale_adj.
      replace  ((- C1) ^* ) with  (- C1)%C by lca.
      f_equal. apply list_Pauli_Hermitian.
  - rewrite translateA_gScaleA.
    rewrite Mscale_adj.
    replace ((C1 / √ 2) ^* ) with (C1 / √ 2) by lca.
    f_equal.
    rewrite translateA_app.
    rewrite Mplus_adjoint.
    rewrite IHrestricted_addition_semantic1.
    rewrite IHrestricted_addition_semantic2.
    reflexivity.
    apply proper_length_AType_App.
    apply restricted_addition_semantic_implies_proper_length_AType in H.
    assumption.
    apply restricted_addition_semantic_implies_proper_length_AType in H0.
    assumption.
Qed.


Lemma unit_Pauli : forall (p : Pauli), WF_Unitary (translate_P p).
Proof. intros. 
       destruct p; simpl; auto with unit_db.
Qed.

Lemma unit_list_Pauli : forall (l : list Pauli), WF_Unitary (⨂ map translate_P l).
Proof. intros.
  apply big_kron_unitary.
  intros a H.
  rewrite in_map_iff in H.
  do 2 destruct H.
  rewrite <- H.
  apply unit_Pauli.
Qed.

#[export] Hint Resolve unit_Pauli unit_list_Pauli : unit_db.


(* norm of coeff = 1, precondition *)
Lemma uni_TType : forall {n} (A : TType n), fst A * fst A ^* = C1 -> WF_TType A -> WF_Unitary (translate A). 
Proof. intros n A H H0. 
  unfold translate. pose (scale_unitary (2 ^ (length (snd A))) (fst A) (⨂ map translate_P (snd A))) as w.
  destruct A. inversion H0.
  unfold translate.
  rewrite map_length in *.
  destruct H1. simpl in *.
  subst. unfold WF_Unitary in *. show_dimensions.
  apply w.
  - pose (big_kron_unitary 2 (map translate_P l)) as w0.
    rewrite map_length in *.
    apply w0.
    intros a H4. 
    apply in_map_iff in H4.
    do 2 destruct H4.
    rewrite <- H4.
    apply unit_Pauli.
  - assumption.
Qed.

Lemma restricted_addition_semantic_implies_Unitary : forall {n : nat} (A : AType n),
    restricted_addition_semantic A -> WF_Unitary (translateA A).
Proof. intros. induction H.
  - unfold translateA. simpl. rewrite Mplus_0_l.
    apply uni_TType; auto.
    destruct H.
    destruct H0; rewrite H0; lca.
  - rewrite translateA_gScaleA.
    unfold WF_Unitary.
    split.
    destruct IHrestricted_addition_semantic1.
    destruct IHrestricted_addition_semantic2.
    rewrite translateA_app.
    auto with wf_db.
    destruct IHrestricted_addition_semantic1.
    destruct IHrestricted_addition_semantic2.
    rewrite ! translateA_app.
    setoid_rewrite restricted_addition_semantic_implies_Hermitian in H3; auto.
    setoid_rewrite restricted_addition_semantic_implies_Hermitian in H5; auto.
    rewrite Mscale_adj.
    replace ((C1 / √ 2) ^* ) with (C1 / √ 2) by lca.
    rewrite Mplus_adjoint.
    setoid_rewrite restricted_addition_semantic_implies_Hermitian; auto.
    distribute_scale.
    assert (C1 / √ 2 * (C1 / √ 2) = C1/C2).
    {  replace (C1 / √ 2) with (/ √ 2) by lca.
       rewrite Cinv_sqrt2_sqrt. lca. }
    rewrite H6.
    distribute_plus.
    rewrite H3, H5.
    unfold anticommute_AType_semantic in H1.
    rewrite H1.
    setoid_rewrite Mplus_comm at 3.
    setoid_rewrite Mplus_assoc.
    setoid_rewrite Mplus_comm at 2.
    setoid_rewrite Mplus_assoc.
    assert (- C1 .* translateA a2 × translateA a1
                .+ translateA a2 × translateA a1 = @Zero (2^n) (2^n)).
    { distribute_scale. apply Mplus_opp_l. auto with wf_db. }
    rewrite H7. rewrite Mplus_0_r.
    lma'.
    apply proper_length_AType_App.
    apply restricted_addition_semantic_implies_proper_length_AType in H.
    assumption.
    apply restricted_addition_semantic_implies_proper_length_AType in H0.
    assumption.
Qed.



Lemma trace_zero_syntax_nonempty :
  ~ trace_zero_syntax [].
Proof. intro. dependent induction H;
  apply IHtrace_zero_syntax;
  apply app_eq_nil in x;
    destruct x; auto.
Qed.

Lemma trace_zero_syntax_non_gI :
  ~ trace_zero_syntax [gI].
Proof. intro.
  dependent induction H.
  - apply app_eq_unit in x.
    destruct x.
    + destruct H0.
      subst.
      apply trace_zero_syntax_nonempty in H.
      contradiction.
    + destruct H0.
      apply IHtrace_zero_syntax.
      assumption.
  - apply app_eq_unit in x.
    destruct x.
    + destruct H0.
      apply IHtrace_zero_syntax.
      assumption.
    + destruct H0.
      subst.
      apply trace_zero_syntax_nonempty in H.
      contradiction.
Qed.

Lemma restricted_addition_semantic_non_nil : forall {n : nat},
    ~ (@restricted_addition_semantic n []).
Proof. intro. intro.
  dependent induction H.
  rewrite gScaleA_dist_app in x.
  apply app_eq_nil in x.
  destruct x.
  unfold gScaleA in *.
  apply map_eq_nil in H2, H3.
  subst.
  apply IHrestricted_addition_semantic1.
  apply eq_implies_JMeq.
  reflexivity.
Qed.

Lemma restricted_addition_syntactic_non_nil : forall {n : nat},
    ~ (@restricted_addition_syntactic n []).
Proof. intro. intro.
  dependent induction H.
  rewrite gScaleA_dist_app in x.
  apply app_eq_nil in x.
  destruct x.
  unfold gScaleA in *.
  apply map_eq_nil in H2, H3.
  subst.
  apply IHrestricted_addition_syntactic1.
  apply eq_implies_JMeq.
  reflexivity.
Qed.


Inductive WF_Predicate {n} : Predicate n -> Prop :=
| WF_AtoPred : forall a : AType n, WF_AType a -> WF_Predicate (AtoPred a)
| WF_Cap : forall (la : list (AType n)), Forall WF_AType la -> WF_Predicate (Cap la)
| WF_Sep : forall (Ln_LLT_Perm : (list nat) * (list (list TTypes)) * (list nat)),
    fold_right Nat.add 0%nat (fst (fst Ln_LLT_Perm)) = n ->
    Forall2 (fun n LT => Forall (fun T => WF_TType (AssignT n T)) LT) (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm)) ->
    WF_Predicate (Sep Ln_LLT_Perm)
| WF_Cup : forall P1 P2 : Predicate n, WF_Predicate P1 -> WF_Predicate P2 -> WF_Predicate (Cup P1 P2).


(* we are treating I as not well-formed *)
Lemma not_WF_I : ~ WF_Predicate pI.
Proof. intro. 
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H; subst; clear H.
  - inversion H1; subst.
    simpl in *.
    apply trace_zero_syntax_non_gI in H2.
    assumption. 
  - rewrite gScaleA_dist_app in H0.
    apply app_eq_unit in H0.
    destruct H0.
    + destruct H.
      apply map_eq_nil in H. subst.
      apply restricted_addition_syntactic_non_nil in H1.
      assumption.
    + destruct H.
      apply map_eq_nil in H0. subst.
      apply restricted_addition_syntactic_non_nil in H2.
      assumption.
Qed.

Lemma WF_X : WF_Predicate pX. 
Proof. do 2 constructor.
  repeat constructor; try lia; easy.
Qed.

Lemma WF_Z : WF_Predicate pZ. 
Proof. do 2 constructor.
  repeat constructor; try lia; easy.
Qed.

Lemma WF_Y : WF_Predicate pY. 
Proof. do 2 constructor.
  repeat constructor; try lia; easy.
Qed.


Lemma WF_TType_scale : forall {n} (a : TType n) (c : Coef),
    c = C1 \/ c = (- C1)%C -> WF_TType a -> WF_TType (gScaleT c a).
Proof. intros n a c H H0. inversion H0. constructor.
  - apply proper_length_TType_gScaleT. assumption.
  - destruct a. simpl in *.
    destruct H; destruct H2; simpl in H2; subst; autorewrite with C_db;
      [ left | right | right | left ]; reflexivity.
  - destruct a. simpl in *. assumption.
Qed.



Lemma WF_AType_scale : forall {n} (A : AType n) (c : Coef),
    c = C1 \/ c = (- C1)%C -> WF_AType A -> WF_AType (gScaleA c A).
Proof. intros n A c H H0. inversion H0; subst.
  constructor.
  induction H1; simpl in *.
  - constructor. apply WF_TType_scale; easy.
  - apply WF_A_syntactic in H1_, H1_0.
    remember H1_ as H1'. clear HeqH1'.
    remember H1_0 as H2'. clear HeqH2'.
    destruct H1', H2'.
    apply restricted_addition_syntactic_implies_proper_length_AType in H2, H3.
    apply IHrestricted_addition_syntactic1 in H1_.
    apply IHrestricted_addition_syntactic2 in H1_0.
    clear IHrestricted_addition_syntactic1. clear IHrestricted_addition_syntactic2.
    inversion H0; subst. clear H0.
    rewrite gScaleA_comm. rewrite gScaleA_dist_app.
    constructor; try easy.
    clear -H1.
    induction a; simpl in *.
    + apply Logic.I.
    + destruct H1. split.
      2: apply IHa; try assumption.
      clear -H.
      induction a0; simpl in *.
      * apply Logic.I.
      * destruct H. split.
        2: apply IHa0; try  assumption.
        destruct a, a0.
        simpl in *.
        assumption.
Qed.


Lemma WF_AType_app : forall {n} (a b : AType n),
    anticommute_AType_syntactic a b ->
    WF_AType a -> WF_AType b -> WF_AType (gScaleA (C1 / √ 2) (a ++ b)).
Proof. intros n a b H H0 H1.
  destruct H0, H1.
  repeat constructor; try easy.
Qed.


Lemma gMulT_gScaleT_l : forall {n} (a b : TType n) (c : Coef),
    gMulT (gScaleT c a) b = gScaleT c (gMulT a b).
Proof. intros n a b c. destruct a, b. simpl.
  f_equal. rewrite ! Cmult_assoc.
  reflexivity.
Qed.

Lemma gMulA_gScaleA_l : forall {n} (A B : AType n) (c : Coef),
    (gMulA (gScaleA c A) B) = gScaleA c (gMulA A B).
Proof. intros n A B c. induction A.
  - simpl. reflexivity.
  - simpl. rewrite gScaleA_dist_app.
    rewrite IHA. f_equal.
    unfold gScaleA.
    rewrite map_map.
    f_equal.
    apply functional_extensionality.
    intros. apply gMulT_gScaleT_l.
Qed.

Lemma gMulT_gScaleT_r : forall {n} (a b : TType n) (c : Coef),
    gMulT a (gScaleT c b) = gScaleT c (gMulT a b).
Proof. intros n a b c. destruct a, b. simpl.
  f_equal. rewrite ! Cmult_assoc.
  do 2 f_equal. rewrite Cmult_comm. reflexivity.
Qed.

Lemma gMulA_gScaleA_r : forall {n} (A B : AType n) (c : Coef),
    (gMulA A (gScaleA c B)) = gScaleA c (gMulA A B).
Proof. intros n A B c. induction A.
  - simpl. reflexivity.
  - simpl. rewrite gScaleA_dist_app.
    rewrite IHA. f_equal.
    unfold gScaleA.
    rewrite ! map_map.
    f_equal.
    apply functional_extensionality.
    intros. apply gMulT_gScaleT_r.
Qed.

Lemma proper_length_TType_zipWith_gMul_base : forall (n : nat) (c c0 c1 : Coef) (l l0 : list Pauli),
    @proper_length_TType n (c, l) ->
    @proper_length_TType n (c0, l0) ->
    @proper_length_TType n (c1, zipWith gMul_base l l0).
Proof. intros n c c0 c1 l l0 H H0.
  destruct H, H0. simpl in *.
  constructor; try assumption.
  simpl in *.
  apply zipWith_len_pres; try assumption.
Qed.

Lemma trace_zero_syntax_zipWith_gMul_base_anticomm : forall (l l0 : list Pauli),
    length l = length l0 ->
    cBigMul (zipWith gMul_Coef l l0) = (- cBigMul (zipWith gMul_Coef l0 l))%C ->
    trace_zero_syntax (zipWith gMul_base l l0).
Proof. induction l.
  - intros.
    simpl in *.
    symmetry in H. rewrite length_zero_iff_nil in H.
    rewrite H. subst.
    unfold zipWith, gMul_base, cBigMul in *. simpl in *.
    inversion H0. lra.
  - intros.
    destruct l0.
    + simpl in *. inversion H.
    + simpl in *. inversion H.
      unfold zipWith in *. simpl in *.
      apply Pauli_anticomm_cons_comm_anticomm in H0; try assumption.
      destruct H0.
      unfold zipWith in *.
      assert (C1 = C1). { easy. }
      assert (Ci = (- - Ci)%C). { rewrite Copp_involutive. easy. }
      assert ((- Ci)%C = (- Ci)%C). {easy. }
      destruct a, p; simpl in *;
        try (apply H1 in H3; clear H4; clear H5; rename H3 into anticomm);
        try (apply H0 in H4; clear H3; clear H5; rename H4 into comm);
        try (apply H0 in H5; clear H3; clear H4; rename H5 into comm).
      all : unfold gMul_base at 1; unfold uncurry at 1; simpl in *.
      2,3,4,5,7,8,9,10,12,13,14,15 : 
      rewrite cons_conc in *; apply trace_zero_syntax_L; constructor.
      all : rewrite cons_conc in *; apply trace_zero_syntax_R; apply IHl; assumption.
      all : apply IHl; try assumption.
Qed.




Lemma big_kron_map_translate_P_twice (l : list Pauli) :
  (⨂ map translate_P l) × (⨂ map translate_P l) = I (2 ^ (length l)).
Proof. induction l.
  - simpl. lma'.
  - simpl. setoid_rewrite kron_mixed_product.
    rewrite IHl.
    assert (2 ^ length l + (2 ^ length l + 0) =  2 ^ S (length l))%nat. { simpl; easy. }
    assert (I 2 × I 2 = I 2). { lma'. }
    assert (σx × σx = I 2). { lma'. }
    assert (σy × σy = I 2). { lma'. }
    assert (σz × σz = I 2). { lma'. }
    destruct a; simpl;
      try rewrite H0;
      try rewrite H1;
      try rewrite H2;
      try rewrite H3;
      try rewrite H4;
      show_dimensions;
      rewrite map_length;
      rewrite kron_2_l;
      reflexivity.
Qed.

Lemma translate_gMulT_split : forall {n} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    translate (gMulT t1 t2) = (translate t1) × (translate t2).
Proof. intros n t1 t2 H0 H1.
  destruct H0, H1.
  destruct t1, t2. simpl in *.
  setoid_rewrite translate_gMulT.
  2: subst; auto.
  unfold translate. simpl.
  show_dimensions.
  rewrite map_length.
  rewrite H0.
  rewrite <- Mscale_assoc.
  rewrite <- Mscale_mult_dist_r.
  rewrite <- Mscale_mult_dist_l.
  easy.
Qed.

(** prove stronger lemma: 
even occurrences of anticommuting Paulis have coefficients +1 or -1
odd occurrences of anticommuting Paulis have coefficients +I or -i **)
Lemma cBigMul_zipWith_gMul_Coef_comm_anticomm_plus_minus_1_i : forall (l l0 : list Pauli),
    length l = length l0 ->
    (cBigMul (zipWith gMul_Coef l l0) = cBigMul (zipWith gMul_Coef l0 l)
     -> cBigMul (zipWith gMul_Coef l l0) = C1 \/ cBigMul (zipWith gMul_Coef l l0) = (-C1)%C)
      /\ (cBigMul (zipWith gMul_Coef l l0) = (- (cBigMul (zipWith gMul_Coef l0 l)))%C
     -> cBigMul (zipWith gMul_Coef l l0) = Ci \/ cBigMul (zipWith gMul_Coef l l0) = (-Ci)%C).
Proof. induction l; intros.
  - simpl in *. symmetry in H. Search (length ?a = 0%nat). rewrite length_zero_iff_nil in H.
    subst.
    unfold cBigMul, zipWith, gMul_Coef; simpl.
    split; intros.
    + auto.
    + inversion H. lra.
  - destruct l0.
    + simpl in H. inversion H.
    + inversion H.
      simpl in *.
      destruct (IHl l0); auto.
      split; intros.
       * apply Pauli_comm_cons_comm_anticomm in H3; auto.
         destruct H3.
         unfold zipWith, cBigMul in *; simpl.
         rewrite fold_left_Cmult.
         unfold uncurry in *; simpl.
         destruct (gMul_Coef_comm_anticomm a p).
         -- specialize (H0 (H3 H5)).
            apply gMul_Coef_comm_1 in H5.
            rewrite H5.
            rewrite Cmult_1_l.
            auto.
         -- specialize (H2 (H4 H5)).
            apply gMul_Coef_anticomm_plus_minus_i in H5.
            destruct H2, H5; rewrite H2, H5;
              [ right | left | left | right ]; lca.
       * apply Pauli_anticomm_cons_comm_anticomm in H3; auto.
         destruct H3.
         unfold zipWith, cBigMul in *; simpl.
         rewrite fold_left_Cmult.
         unfold uncurry in *; simpl.
         destruct (gMul_Coef_comm_anticomm a p).
         -- specialize (H2 (H4 H5)).
            apply gMul_Coef_comm_1 in H5.
            rewrite H5.
            rewrite Cmult_1_l.
            auto.
         -- specialize (H0 (H3 H5)).
            apply gMul_Coef_anticomm_plus_minus_i in H5.
            destruct H0, H5; rewrite H0, H5;
              [ left | right | right | left ]; lca.
Qed.

Lemma cBigMul_zipWith_gMul_Coef_comm_plus_minus_1 : forall (l l0 : list Pauli),
    length l = length l0 ->
    cBigMul (zipWith gMul_Coef l l0) = cBigMul (zipWith gMul_Coef l0 l)
    -> cBigMul (zipWith gMul_Coef l l0) = C1 \/ cBigMul (zipWith gMul_Coef l l0) = (-C1)%C.
(** The number of the anticommuting paulis must be even, so the number of Ci coefficients in the multiplied tensor must also be even. Hence, the multiplication of all coefficients must be either 1 or -1 **)
Proof. apply cBigMul_zipWith_gMul_Coef_comm_anticomm_plus_minus_1_i. Qed.

Lemma trace_zero_syntax_zipWith_gMul_base_comm : forall (n : nat) (l l0 : list Pauli),
  cBigMul (zipWith gMul_Coef l l0) = cBigMul (zipWith gMul_Coef l0 l)
  -> length l = n -> length l0 = n ->
  zipWith gMul_base l l0 <> repeat gI n ->
  trace_zero_syntax (zipWith gMul_base l l0).
Proof. intros. gen l0 n.  induction l.
  - intros.
    simpl in *.
    rewrite <- H0 in H1.
    rewrite length_zero_iff_nil in H1.
    subst.
    unfold zipWith, gMul_base, cBigMul in *. simpl in *.
    contradiction.
  - intros.
    destruct l0.
    + simpl in *. rewrite <- H1 in H0. inversion H0.
    + simpl in *. destruct n; inversion H0; inversion H1.
      unfold zipWith in *. simpl in *.
      
      unfold cBigMul in *. simpl in *.
      rewrite ! fold_left_Cmult in H.
      unfold uncurry in *.
      simpl in *.
      destruct (gMul_base a p) eqn:base.
      * assert ( ~ (uncurry gMul_base (a, p) = gI /\ map (uncurry gMul_base) (combine l l0) = repeat gI n)).
      { generalize H2. apply not_iff_compat.
        split. intros. destruct H3. unfold uncurry in H3. simpl in *.
        f_equal. auto. intros. inversion H3. split; auto. }
        assert (gMul_Coef a p = C1).
        { destruct a, p; unfold gMul_Coef; simpl; auto.
          all: unfold gMul_base in base; simpl in base; inversion base. }
        assert (gMul_Coef p a = C1).
        { destruct a, p; unfold gMul_Coef; simpl; auto.
          all: unfold gMul_base in base; simpl in base; inversion base. }

        rewrite H6, H7 in *. rewrite ! Cmult_1_l in H.
        unfold "<>" in H3.
        unfold uncurry in H3.
        simpl in H3.
        assert ( map (uncurry gMul_base) (combine l l0) <> repeat gI n ).
        { intro.
          assert (gMul_base a p = gI /\ map (uncurry gMul_base) (combine l l0) = repeat gI n).
          { auto. }
          destruct (H3 H9). }
        specialize (IHl l0 H n H4 H5 H8).
        Search ([?a] ++ ?b). rewrite cons_conc.
        apply trace_zero_syntax_R. assumption.
      * rewrite cons_conc. do 2 constructor.
      * rewrite cons_conc. do 2 constructor.
      * rewrite cons_conc. do 2 constructor.
Qed.

Lemma zipWith_gMul_base_eq : forall (n : nat) (l l0 : list Pauli),
    length l = length l0 ->
    (zipWith gMul_base l l0 = repeat gI (length l) <-> l = l0).
Proof. intros n l l0 H.
  split; intro.
  - gen l0. induction l; intros; simpl in *.
    + inversion H.
      symmetry in H2. rewrite length_zero_iff_nil in H2.
      subst. easy.
    + destruct l0.
      * inversion H.
      * simpl in *. inversion H.
        inversion H0.
        f_equal.
        -- unfold uncurry, gMul_base in H3.
           destruct a, p; try easy; inversion H3.
        -- rewrite H3 in H4.
           unfold zipWith in IHl.
           specialize (IHl l0 H2 H4).
           easy.
  - rewrite H0. rewrite zipWith_gMul_base_inv. easy.
Qed.


Lemma zipWith_gMul_base_neq : forall (n : nat) (l l0 : list Pauli),
    length l = length l0 ->
    (zipWith gMul_base l l0 <> repeat gI (length l) <-> l <> l0).
Proof. intros n l l0 H.
  apply zipWith_gMul_base_eq in H; auto.
  apply not_iff_compat in H. easy.
Qed.
  

(** Precondition: Commute -> gMulT a b <> (c, gI^n) <- use repeat function **)
Lemma WF_TType_mul_commute : forall {n} (a b : TType n),
    commute_TType a b -> (snd (gMulT a b) <> repeat gI n) ->
    WF_TType a -> WF_TType b -> WF_TType (gMulT a b).
Proof. intros n a b H H0 H1 H2. 
  unfold gMulT. destruct a, b.
  unfold commute_TType in H.
  do 2 destruct H1, H2; simpl in *.
  constructor; simpl.
  simpl; split; try assumption.
  apply zipWith_len_pres; assumption.
  apply cBigMul_zipWith_gMul_Coef_comm_plus_minus_1 in H; subst; auto.
  destruct H, H3, H5; simpl in *; rewrite H, H3, H5; autorewrite with C_db;
    [ left | right | right | left | right | left | left | right ]; reflexivity.
  apply trace_zero_syntax_zipWith_gMul_base_comm with (n := n);
    try assumption.
Qed.

(** Precondition : commute -> a <> b **)
Lemma WF_TType_mul_commute' : forall {n} (a b : TType n),
    commute_TType a b -> snd a <> snd b ->
    WF_TType a -> WF_TType b -> WF_TType (gMulT a b).
Proof. intros n a b H H0 H1 H2.
  destruct a, b. simpl in H0.
  remember H1. remember H2. clear Heqw Heqw0.
  destruct w, w0. destruct H3, H6. simpl in H9, H10.
  rewrite <- zipWith_gMul_base_neq in H0; auto.
  2: subst; auto.
  apply WF_TType_mul_commute; simpl; subst; auto.
Qed.



Lemma cBigMul_zipWith_gMul_Coef_anticomm_plus_minus_i : forall (l l0 : list Pauli),
    length l = length l0 ->
    (cBigMul (zipWith gMul_Coef l l0) = (- (cBigMul (zipWith gMul_Coef l0 l)))%C
     -> cBigMul (zipWith gMul_Coef l l0) = Ci \/ cBigMul (zipWith gMul_Coef l l0) = (-Ci)%C).
Proof. apply cBigMul_zipWith_gMul_Coef_comm_anticomm_plus_minus_1_i. Qed.


Lemma WF_TType_mul_anticommute : forall {n} (a b : TType n),
    anticommute_TType a b ->
    WF_TType a -> WF_TType b -> WF_TType (gScaleT Ci (gMulT a b)).
Proof. intros n a b H H0 H1.
  unfold anticommute_TType in H.
  destruct a, b.
  unfold gMulT.
  destruct H0, H1.
  inversion H0; inversion H1.
  simpl in *.
  constructor; simpl.
  - constructor; auto.
    simpl.
    rewrite zipWith_len_pres with (n := n); auto.
  - subst.
    apply cBigMul_zipWith_gMul_Coef_anticomm_plus_minus_i in H; auto.
    destruct H, H2, H4; simpl in *; rewrite H, H2, H4;
      [ right | left | left | right | left | right | right | left ]; lca.
  - subst.
    apply trace_zero_syntax_zipWith_gMul_base_anticomm; auto.
Qed.


Lemma gMulA_dist_app_l : forall {n} (a a1 a2 : AType n),
    gMulA (a1 ++ a2) a = (gMulA a1 a) ++ (gMulA a2 a).
Proof. intros n a a1 a2.
  induction a1; auto.
  simpl. rewrite IHa1.
  rewrite app_assoc.
  auto.
Qed.



Lemma WF_AType_dist_app : forall {n} (a1 a2 : AType n),
    WF_AType a1 -> WF_AType a2 -> anticommute_AType_syntactic a1 a2 ->
    WF_AType (gScaleA (C1 / √ 2) (a1 ++ a2)).
Proof. intros n a1 a2 H H0 H1. 
  do 2 constructor; inversion H; inversion H0; auto.
Qed.



Lemma WF_TType_tensor : forall {n m} (a : TType n) (b : TType m), WF_TType a -> WF_TType b -> WF_TType (gTensorT a b).
Proof. intros n m a b H H0.
  destruct H, H0.
  constructor.
  - unfold proper_length_TType in *. destruct H, H0. split; try lia.
    unfold gTensorT. destruct a, b. simpl in *. rewrite app_length. subst. reflexivity.
  - destruct a, b. unfold gTensorT. simpl in *.
    destruct H1, H3; simpl in *; subst; autorewrite with C_db;
      [left | right | right | left]; reflexivity.
  - destruct a, b. unfold gTensorT. simpl in *.
    constructor. assumption.
Qed.

Lemma map_gTensorT_gScaleA : forall {n m} (c : Coef) (a : TType n) (A : AType m),
    map (fun x : TType m => gTensorT a x) (gScaleA c A) =
      gScaleA c (map (fun x : TType m => gTensorT a x) A).
Proof. intros n m c a A.
  induction A.
  - simpl. auto.
  - simpl. f_equal; auto.
    clear IHA.
    destruct a, a0. simpl.
    f_equal. lca.
Qed.



Lemma gTensorT_gScaleT_comm_l : forall {n m} (c : Coef) (a : TType n) (b : TType m), gTensorT (gScaleT c a) b = gScaleT c (gTensorT a b).
Proof. intros n m c a b.
  unfold gScaleT, gTensorT.
  destruct a, b.
  f_equal.
  lca.
Qed. 

Lemma gTensorA_gScaleA_comm_l : forall {n m} (c : Coef) (a : AType n) (b : AType m), gTensorA (gScaleA c a) b = gScaleA c (gTensorA a b).
Proof. intros n m c a b.
  induction a.
  - auto.
  - simpl.
    Search gScaleA.
    rewrite gScaleA_dist_app.
    rewrite IHa.
    f_equal.
    unfold gScaleA.
    rewrite map_map.
    f_equal.
    apply functional_extensionality.
    intros t.
    apply gTensorT_gScaleT_comm_l.
Qed.

Lemma gTensorT_gScaleT_comm_r : forall {n m} (c : Coef) (a : TType n) (b : TType m), gTensorT a (gScaleT c b) = gScaleT c (gTensorT a b).
Proof. intros n m c a b.
  unfold gScaleT, gTensorT.
  destruct a, b.
  f_equal.
  lca.
Qed. 

Lemma gTensorA_gScaleA_comm_r : forall {n m} (c : Coef) (a : AType n) (b : AType m), gTensorA a (gScaleA c b) = gScaleA c (gTensorA a b).
Proof. intros n m c a b.
  induction a.
  - auto.
  - simpl.
    Search gScaleA.
    rewrite gScaleA_dist_app.
    rewrite IHa.
    f_equal.
    unfold gScaleA.
    rewrite ! map_map.
    f_equal.
    apply functional_extensionality.
    intros t.
    apply gTensorT_gScaleT_comm_r.
Qed.

Lemma gTensorA_app_dist : forall {n m} (a1 a2 : AType n) (a0 : AType m), gTensorA (a1 ++ a2) a0 = (gTensorA a1 a0) ++ (gTensorA a2 a0).
Proof. intros n m a1 a2 a0.
  induction a1; auto.
  simpl.
  rewrite <- app_assoc.
  f_equal.
  auto.
Qed.


Lemma gTensorA_nil_r : forall {n m} (a : AType n), @gTensorA n m a [] = [].
Proof. intros n m a.
  induction a.
  - auto.
  - simpl.
    apply IHa.
Qed.

Lemma fold_left_Cmult_app : forall {l l0}, fold_left Cmult (l ++ l0) C1 = (fold_left Cmult l C1) * (fold_left Cmult l0 C1).
Proof. intros l l0.
  induction l.
  - simpl. lca.
  - simpl.
    rewrite ! fold_left_Cmult.
    rewrite IHl.
    lca.
Qed.

Lemma WF_AType_map_gTensorT : forall {n m} (a : TType n) (B : AType m),
    WF_TType a -> WF_AType B -> WF_AType (map (fun x : TType m => gTensorT a x) B).
Proof. intros n m a B0 H H0. 
  constructor.
  destruct H, H0. simpl in *.
  induction H0; simpl in *.
  - destruct a, t, H0. simpl in *.
    do 2 constructor; simpl in *.
    + constructor; destruct H, H0; simpl in *; try lia.
      rewrite app_length. subst. reflexivity.
    + destruct H1, H3; simpl in *; subst; autorewrite with C_db; [left | right | right | left]; reflexivity.
    + constructor. assumption.
  -  rewrite map_gTensorT_gScaleA.
     rewrite map_app.
     constructor; auto.
     clear IHrestricted_addition_syntactic1 IHrestricted_addition_syntactic2.
     clear -H0.
     induction a1.
     + simpl. auto.
     + simpl in *. destruct H0.
       split.
       2: apply IHa1; auto.
       clear IHa1.
       induction a2.
       * simpl. auto.
       * simpl in *. destruct H.
         apply anticommute_AType_syntactic_comm in H0.
         simpl in *.
         destruct H0.
         apply anticommute_AType_syntactic_comm in H2.
         split.
         2: apply IHa2; auto.
         clear IHa2.
         clear -H.
         destruct a, a0, a2.
         simpl in *.
         rewrite <- ! zipWith_app_product with (n:=length l); auto.
         unfold cBigMul in *.
         rewrite ! fold_left_Cmult_app.
         Search fold_left.
         rewrite H.
         lca.
Qed.

Lemma restricted_addition_syntactic_map_gTensorT : forall {n m} (a : TType n) (B : AType m),
    WF_TType a -> restricted_addition_syntactic B -> restricted_addition_syntactic (map (fun x : TType m => gTensorT a x) B).
Proof. intros n m a B0 H H0.
  destruct H. simpl in *.
  induction H0; simpl in *.
  - destruct a, t, H0. simpl in *.
    do 2 constructor; simpl in *.
    + constructor; destruct H, H0; simpl in *; try lia.
      rewrite app_length. subst. reflexivity.
    + destruct H1, H3; simpl in *; subst; autorewrite with C_db; [left | right | right | left]; reflexivity.
    + constructor. assumption.
  -  rewrite map_gTensorT_gScaleA.
     rewrite map_app.
     constructor; auto.
     
     clear -H0.
     induction a1.
     + simpl. auto.
     + simpl in *. destruct H0.
       split.
       2: apply IHa1; auto.
       clear IHa1.
       induction a2.
       * simpl. auto.
       * simpl in *. destruct H.
         apply anticommute_AType_syntactic_comm in H0.
         simpl in *.
         destruct H0.
         apply anticommute_AType_syntactic_comm in H2.
         split.
         2: apply IHa2; auto.
         clear IHa2.
         clear -H.
         destruct a, a0, a2.
         simpl in *.
         rewrite <- ! zipWith_app_product with (n:=length l); auto.
         unfold cBigMul in *.
         rewrite ! fold_left_Cmult_app.
         Search fold_left.
         rewrite H.
         lca.
Qed.

Lemma WF_AType_add : forall {n} (A B : AType n),
     anticommute_AType_syntactic A B ->
    WF_AType A -> WF_AType B -> WF_AType (gScaleA (C1 / √ 2) (gAddA A B)).
Proof. intros n A B H H0 H1.
  unfold gAddA.  apply WF_AType_app; easy.
Qed. 

Lemma WF_AType_neg : forall {n} (A : AType n),
    WF_AType A -> WF_AType (gScaleA (Copp C1) A).
Proof. intros n A H.  apply WF_AType_scale; try easy. right. reflexivity. Qed.

#[export] Hint Resolve WF_I WF_X WF_Z WF_Y WF_AType_scale WF_AType_add WF_AType_neg : wfpt_db.



Lemma fold_left_WF_Matrix_AType : forall {n} (a : TType n) (A : list (TType n)),  
    fold_left Mplus (map translate A) (Zero .+ translate a)%M
    =  (fold_left Mplus (map translate A) (Zero) .+  translate a)%M.
Proof. intros n a A. apply (fold_left_Mplus (translate a) Zero (map translate A)).
Qed.

Lemma WF_Matrix_AType : forall {n} (A : AType n), WF_AType A -> WF_Matrix (translateA A). 
Proof. intros n A H. destruct H.
  induction H.
  - destruct H.
    unfold translateA. simpl.
    rewrite Mplus_0_l.
    apply WF_translate; auto.
  - apply restricted_addition_syntactic_implies_proper_length_AType in H.
    apply restricted_addition_syntactic_implies_proper_length_AType in H0.
    rewrite translateA_gScaleA.
    2: apply proper_length_AType_App; auto.
    apply WF_scale.
    apply WF_Matrix_translateA.
    apply proper_length_AType_App; auto.
Qed.

#[export] Hint Resolve WF_Matrix_AType : wf_db wfpt_db.


(******************)
(* unitary lemmas *)
(******************)


Lemma unitary_two_pauli : forall (p1 p2 : Pauli),
    p1 <> p2 -> p1 <> gI -> p2 <> gI -> WF_Unitary (C1 / √ 2 .* translate_P p1 .+ C1 / √ 2 .* translate_P p2)%M /\ WF_Unitary (- C1 / √ 2 .* translate_P p1 .+ C1 / √ 2 .* translate_P p2)%M /\ WF_Unitary (C1 / √ 2 .* translate_P p1 .+ - C1 / √ 2 .* translate_P p2)%M.
Proof. intros. split; [ idtac | split ]; unfold translate_P, WF_Unitary;
  induction p1, p2; simpl; split; try contradiction; auto with wf_db;
    lma'; auto 15 with wf_db;
    autounfold with U_db; simpl;
    C_field_simplify; try nonzero;
    autorewrite with Cexp_db C_db;
    eapply c_proj_eq; simpl;
    repeat (autorewrite with R_db; field_simplify_eq; simpl);
    try easy.
Qed.


Lemma zipWith_gMul_base_symmetric : forall (l l0 : list Pauli), length l = length l0 -> zipWith gMul_base l l0 = zipWith gMul_base l0 l.
Proof. intros l. unfold zipWith, gMul_base, uncurry. induction l.
  - intros. rewrite combine_nil. simpl. easy.
  - intros. destruct l0; try discriminate. simpl. f_equal. destruct a, p; simpl; try easy. apply IHl. inversion H. easy.
Qed.

Lemma commute_TType_gMulT_swap : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    fst t1 <> C0 -> fst t2 <> C0 ->
    commute_TType t1 t2 <-> gMulT t1 t2 = gMulT t2 t1.
Proof. intros n t1 t2 H H0 H1 H2. 
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  split; intros.
  - unfold commute_TType in H3.
    unfold gMulT.
    rewrite (Cmult_comm c1 c2).
    f_equal.
    f_equal; auto.
    rewrite zipWith_gMul_base_symmetric; auto.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    simpl in *.
    auto.
  - unfold commute_TType.
    unfold gMulT in H3.
    rewrite (Cmult_comm c1 c2) in H3.
    assert (forall {A B : Type} (a a' : A) (b b' : B), (a,b) = (a',b') -> a=a').
    { intros. inversion H4. auto. }
    apply H4  in H3. 
    apply Cmult_cancel_l with (a := c2 * c1) in H3; auto.
    simpl in *.
    apply Cmult_neq_0; auto.
Qed.

Lemma anticommute_TType_gMulT_antiswap : forall {n : nat} (t1 t2 : TType n),
    proper_length_TType t1 -> proper_length_TType t2 ->
    fst t1 <> C0 -> fst t2 <> C0 ->
    anticommute_TType t1 t2 <-> gMulT t1 t2 = gScaleT (Copp C1) (gMulT t2 t1).
Proof. intros n t1 t2 H H0 H1 H2.
  destruct t1 as [c1 l1].
  destruct t2 as [c2 l2].
  split; intros.
  - unfold anticommute_TType in H3.
    unfold gMulT.
    rewrite (Cmult_comm c1 c2).
    simpl.
    rewrite ! Cmult_assoc.
    replace (- C1 * c2 * c1) with (c2 * c1 * (- C1)) by lca.
    rewrite <- ! Cmult_assoc.
    f_equal.
    do 2 f_equal.
    2: { inversion H. inversion H0.
         simpl in *.
         rewrite zipWith_gMul_base_symmetric;
           subst; auto. }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    simpl in *.
    rewrite H3.
    lca.
  - unfold anticommute_TType.
    unfold gMulT in H3.
    rewrite (Cmult_comm c1 c2) in H3.
    assert (forall {A B : Type} (a a' : A) (b b' : B), (a,b) = (a',b') -> a=a').
    { intros. inversion H4. auto. }
    apply H4  in H3.
    rewrite ! Cmult_assoc in H3.
    replace (- C1 * c2 * c1) with (c2 * c1 * (- C1)) in H3 by lca.
    rewrite <- ! Cmult_assoc in H3.
    apply Cmult_cancel_l with (a := c2) in H3; auto.
    apply Cmult_cancel_l with (a := c1) in H3; auto.
    simpl in *.
    rewrite H3.
    lca.
Qed.


(* same as unitary_two_tensored_paulis except that (fst t2 = - C1/√2). *)
Lemma unitary_two_tensored_paulis' : forall {n} (t1 t2 : TType n), 
    proper_length_TType t1 -> proper_length_TType t2 ->
    (fst t1 = C1/√2) -> (fst t2 = - C1/√2) ->
    anticommute_TType t1 t2 ->
    WF_Unitary (@translateA n (t1 :: t2 :: nil)). 
Proof. intros. destruct t1, t2. simpl in *.
  destruct H, H0. simpl in *.
  rewrite H1, H2 in *. clear H1. clear H2.
  inversion H3; subst.
  unfold translateA.
  simpl. rewrite Mplus_0_l.
  unfold translate. simpl  in *.
  setoid_rewrite Cmult_comm at 2.
  setoid_rewrite <- Cmult_1_l at 5.
  setoid_rewrite <- Mscale_assoc at 2.
  replace ( C1 * / √ 2 ) with ( C1 / √ 2) by lca.
  setoid_rewrite <- Mscale_plus_distr_r with (x:=C1 / √ 2) (A:=⨂ map translate_P l) (B:=(-C1 .*(⨂ map translate_P l0))%M).
  rewrite ! map_length.
  apply unitary_hermitian_anticommute_unitary.
  rewrite <- map_length with (f:=translate_P).
  apply unit_list_Pauli.
  rewrite <- H5.
  rewrite <- map_length with (f:=translate_P).
  apply scale_unitary; try lca.
  apply unit_list_Pauli.
  apply list_Pauli_Hermitian.
  setoid_rewrite Mscale_adj with (x := (-C1)%C) (A := (⨂ map translate_P l0)).
  replace ((- C1) ^* )%C with (-C1)%C by lca.
  rewrite map_length.
  rewrite H5.
  apply Mscale_inj with (c:= (-C1)%C).
  apply list_Pauli_Hermitian.
  apply Mscale_cancel with (c:= (-C1)%C).
  intro. inversion H1. lra.
  setoid_rewrite <- Mscale_mult_dist_r at 1.
  unfold Matrix.scale at 1.
  setoid_rewrite Mscale_assoc at 1.
  replace (- C1 * - C1)%C with (C1) by lca.
  rewrite Mscale_1_l.
  setoid_rewrite <- Mscale_mult_dist_l.
  unfold Matrix.scale at 2.
  setoid_rewrite Mscale_assoc.
  replace (-C1 * - C1)%C with (C1) by lca.
  rewrite Mscale_1_l.
  replace (Copp (RtoC (IZR (Zpos xH)))) with (RtoC (IZR (Zneg xH))) by lca.
  apply Mscale_cancel with (c:=C1/C2).
  - intros G. apply C_inj_r with (c:=C2) in G. unfold Cdiv in G. rewrite <- Cmult_assoc in G. rewrite Cinv_l in G; try nonzero. rewrite Cmult_0_l in G. rewrite Cmult_1_l in G. contradict G. nonzero.
  - rewrite Mscale_assoc. rewrite Cmult_comm. rewrite <- Mscale_assoc.
    replace (C1 / C2) with ((C1/√2) * (C1/√2)) by C_field.
    rewrite Mscale_assoc. rewrite Cmult_assoc. symmetry. rewrite Cmult_comm. symmetry.
    assert ((C1 / √ 2 * (C1 / √ 2) .* ((⨂ map translate_P l) × (⨂ map translate_P l0)))%M
            = (translate (gMulT  (C1 / √ 2, l) (C1 / √ 2, l0)))%M).
    { rewrite <- translate_gMulT; easy. }
      rewrite <- map_length with (f:=translate_P).
    rewrite H1.
    assert ((C1 / √ 2 * (-1 * (C1 / √ 2)) .* ((⨂ map translate_P l0) × (⨂ map translate_P l)))%M
            = (translate (gMulT  (C1 / √ 2, l0) (-1 * (C1 / √ 2), l)))%M).
    { rewrite <- translate_gMulT; easy. }
    show_dimensions.
    rewrite map_length.
    rewrite <- H5.
    rewrite <- map_length with (f:=translate_P).
    rewrite H4.
    simpl.
    assert (C1 / √ 2 * (C1 / √ 2) * - cBigMul (zipWith gMul_Coef l0 l)
            = C1 / √ 2 * (-1 * (C1 / √ 2)) * cBigMul (zipWith gMul_Coef l0 l)).
    { rewrite <- ! Cmult_assoc. apply C_inj_l. symmetry. 
      rewrite Cmult_comm. rewrite <- ! Cmult_assoc. apply C_inj_l.
      lca. }
    rewrite <- H6.
    rewrite H2.
    rewrite zipWith_gMul_base_symmetric; easy.
Qed.

Fixpoint uni_Predicate {n} (P : Predicate n) :=
  match P with
  | AtoPred _ => WF_Unitary (translateP P)
  | Cap la => Forall WF_Unitary (map translateA la)
  | Sep Ln_LLT_Perm => Forall2 (fun n LT => Forall (fun T => coef_size_1 (AssignT n T)) LT) (fst (fst Ln_LLT_Perm)) (snd (fst Ln_LLT_Perm))
  | Cup a b => (uni_Predicate a) /\ (uni_Predicate b)
  | Err => False
  end.

Lemma uni_vec_I : uni_Predicate pI.
Proof. simpl. unfold translateA, translate, translate_P. simpl.
       rewrite Mplus_0_l, Mscale_1_l, kron_1_r. unfold WF_Unitary.
       split. auto with wf_db. lma'.
Qed.
  
Lemma uni_vec_X : uni_Predicate pX.
Proof. simpl. unfold translateA, translate, translate_P. simpl.
       rewrite Mplus_0_l, Mscale_1_l, kron_1_r. unfold WF_Unitary.
       split. auto with wf_db. lma'.
Qed.

Lemma uni_vec_Y : uni_Predicate pY.
Proof.  simpl. unfold translateA, translate, translate_P. simpl.
       rewrite Mplus_0_l, Mscale_1_l, kron_1_r. unfold WF_Unitary.
       split. auto with wf_db. lma'.
Qed.

  Lemma uni_vec_Z : uni_Predicate pZ.
Proof.  simpl. unfold translateA, translate, translate_P. simpl.
       rewrite Mplus_0_l, Mscale_1_l, kron_1_r. unfold WF_Unitary.
       split. auto with wf_db. lma'.
Qed.


#[export] Hint Resolve unit_Pauli uni_vec_I uni_vec_X uni_vec_Y uni_vec_Z : wfpt_db.


(******************************************************)
(* Showing translations preserves relevent properties *)
(******************************************************)

(* we actually use this to prove translate_mult, so we prove it first *)
Lemma translate_kron : forall {n m} (g1 : TType n) (g2 : TType m),
    length (snd g1) = n -> length (snd g2) = m ->
    translate (gTensorT g1 g2) = (translate g1) ⊗ (translate g2).
Proof. intros n m g1 g2 H H0.  unfold translate.
         destruct g1; destruct g2.
         simpl in *.
         do 3 (rewrite map_length). 
         rewrite H, H0 in *.
         rewrite Mscale_kron_dist_r.
         rewrite Mscale_kron_dist_l.
         rewrite Mscale_assoc.
         bdestruct_all; simpl. 
         rewrite Cmult_comm.
         rewrite map_app. 
         assert (H3 : forall (l : list Pauli) (i0 : nat), WF_Matrix (nth i0 (map translate_P l) Zero)).
         { intros.  
           bdestruct (i0 <? length (map translate_P l1)).
           + apply (nth_In _ (@Zero 2 2)) in H1.
             apply in_map_iff in H1.
             destruct H1 as [x [H3 H4] ].
             rewrite <- H3; apply WF_Matrix_Pauli.
           + rewrite nth_overflow; try lia. 
             auto with wf_db. }
         rewrite big_kron_app; auto.
         do 2 (rewrite map_length).
         rewrite app_length.
         rewrite H, H0 in *.
         reflexivity.
Qed.


Lemma fold_left_translateA_kron : forall {n m} (a : TType n) (B : AType m),
 length (snd a) = n -> proper_length_AType B ->
    (fold_left Mplus (map (fun x : TType m => translate (gTensorT a x)) B) Zero
     =  translate a ⊗ fold_left Mplus (map translate B) Zero)%M.
Proof. intros n m a B H H0.  generalize dependent a. induction B.
  - intros a H.   simpl. lma.
  - intros a0 H.   simpl. rewrite 2 fold_left_Mplus. rewrite kron_plus_distr_l.
    inversion H0.
    + inversion H2. rewrite <- (translate_kron a0 a); try assumption. simpl.
      apply Zero_kron.
    + inversion H3. rewrite <- (translate_kron a0 a); try assumption.
      rewrite IHB; try assumption. reflexivity.
Qed.

Lemma translateA_kron : forall {n m} (a : AType n) (b : AType m),
    proper_length_AType a -> proper_length_AType b ->
    translateA (gTensorA a b) = (translateA a) ⊗ (translateA b).
Proof. intros n m a b H H0. induction H.
  - simpl. rewrite app_nil_r. unfold translateA. simpl. rewrite Mplus_0_l. rewrite <- fold_left_translateA_kron; inversion H; try assumption. rewrite map_map; reflexivity.
  - simpl. unfold translateA. simpl. rewrite fold_left_Mplus.
    unfold translateA in IHproper_length_AType. rewrite kron_plus_distr_r.  rewrite <- IHproper_length_AType.
    rewrite map_app. rewrite fold_left_Mplus_app_Zero.
    rewrite map_map. rewrite <- fold_left_translateA_kron; inversion H; try assumption. rewrite Mplus_comm. reflexivity.
Qed.
    

Lemma translate_reduce : forall (n : nat) (c : Coef) (p : Pauli) (l : list Pauli),
  length l = n -> 
  @translate (S n) (c, p :: l) = (translate_P p) ⊗ @translate n (c, l).
Proof. intros. 
       unfold translate. 
       simpl. 
       rewrite map_length.
       replace (2^(length l) + (2^(length l) + 0))%nat with (2 * 2^(length l))%nat by lia. 
       rewrite <- Mscale_kron_dist_r.
       rewrite H; easy. 
Qed.

Lemma translate_Mmult : forall {n} (g1 g2 : TType n),
    length (snd g1) = n -> length (snd g2) = n ->
    translate (gMulT g1 g2) = (translate g1) × (translate g2).
Proof. intros n g1 g2 H H0. induction n as [| n'].
       - destruct g1; destruct g2. 
         destruct l; destruct l0; try easy. 
         unfold translate. simpl. 
         distribute_scale.
         rewrite Mmult_1_r; auto with wf_db.
         unfold zipWith, cBigMul. simpl.
         destruct c; destruct c0; try easy.
         autorewrite with C_db.
         reflexivity.
       - destruct g1; destruct g2.
         destruct l; destruct l0; try easy. 
         simpl in H; simpl in H0.
         apply Nat.succ_inj in H.
         apply Nat.succ_inj in H0.
         rewrite gMulT_reduce; try easy.
         replace (S n') with (1 + n')%nat by lia.
         rewrite translate_kron; try easy.
         rewrite IHn'; try easy.
         rewrite (translate_reduce _ c), (translate_reduce _ c0); try easy.
         restore_dims.
         rewrite kron_mixed_product.
         assert (H' : @translate 1 (gMul_Coef p p0, [gMul_base p p0]) = 
                      translate_P p × translate_P p0).
         { destruct p; destruct p0; simpl. 
           all : unfold translate; simpl. 
           all : lma'. }
         rewrite H'; easy. 
         simpl. 
         bdestruct_all.
         simpl. 
         apply zipWith_len_pres; easy.
Qed.

Lemma fold_left_translateA_Mmult : forall {n} (a : TType n) (B : AType n),
    proper_length_TType a -> proper_length_AType B ->
    fold_left Mplus (map (fun x : TType n => translate (gMulT a x)) B) Zero =
      translate a × fold_left Mplus (map translate B) Zero.
Proof. intros n a B H H0.
  induction H0.
  - simpl. rewrite 2 Mplus_0_l. inversion H; inversion H0; rewrite translate_Mmult; easy.
  - simpl. rewrite 2 fold_left_Mplus. rewrite Mmult_plus_distr_l. rewrite <- translate_Mmult.
    rewrite IHproper_length_AType. reflexivity.
    + inversion H. assumption.
    + inversion H0. assumption.
Qed. 

Lemma translateA_Mmult : forall {n} (a b : AType n),
    proper_length_AType a -> proper_length_AType b ->
    translateA (gMulA a b) = (translateA a) × (translateA b).
Proof. intros n a b H H0.
  unfold translateA. induction H.
  - simpl. rewrite app_nil_r. rewrite map_map. rewrite Mplus_0_l.
    apply fold_left_translateA_Mmult; try assumption.
  - simpl. rewrite map_app. rewrite map_map. rewrite fold_left_Mplus_app_Zero.
    rewrite fold_left_Mplus. rewrite Mmult_plus_distr_r. rewrite <- IHproper_length_AType.
    rewrite fold_left_translateA_Mmult; try assumption. rewrite Mplus_comm. reflexivity.
Qed.

Lemma map_translate_gAddA : forall {n} (a b : AType n),
    proper_length_AType a -> proper_length_AType b ->
    map translate (gAddA a b) = ((map translate a) ++ (map translate b))%M.
Proof. intros n a b H H0.
       unfold gAddA. induction H.
       - simpl. reflexivity.
       - simpl. rewrite IHproper_length_AType. reflexivity.
Qed.

Lemma translateA_Add : forall {n} (a b : AType n),
    proper_length_AType a -> proper_length_AType b ->
    translateA (gAddA a b) = (translateA a .+ translateA b)%M.
Proof. intros n a b H H0.
       unfold translateA. induction H.
       - simpl. rewrite fold_left_Mplus. rewrite Mplus_0_l. rewrite Mplus_comm. reflexivity.
       - simpl. rewrite map_translate_gAddA; auto.
         rewrite ! fold_left_Mplus. rewrite fold_left_Mplus_app_Zero. rewrite ! Mplus_assoc. f_equal. rewrite Mplus_comm. reflexivity.
Qed. 

Lemma translate_scale : forall {n} (A : TType n) (c : Coef),
  translate (gScaleT c A) = (c .* (translate A))%M.
Proof. intros. 
       unfold translate. 
       destruct A. simpl. 
       rewrite <- Mscale_assoc.     
       reflexivity. 
Qed.

Lemma translateA_scale : forall {n} (A : AType n) (c : Coef),
    translateA (gScaleA c A) = (c .* (translateA A))%M.
Proof. intros n A c.
  unfold translateA. unfold gScaleA.
  rewrite map_map.
  induction A.
  - simpl. lma.
  - simpl. rewrite 2 fold_left_Mplus. rewrite Mscale_plus_distr_r.
    rewrite IHA. rewrite translate_scale. reflexivity.
Qed.


Declare Scope AType_scope.
Delimit Scope AType_scope with A.
Local Open Scope AType_scope.

Check EqdepFacts.eq_dep.
Inductive eq_AType {n1 n2} (A1 : AType n1) (A2 : AType n2) := 
| A_eq : n1 = n2 -> EqdepFacts.eq_dep nat (fun n => Square (2 ^ n)%nat) n1 (translateA A1) n2 (translateA A2) -> eq_AType A1 A2.
Infix "≡" := eq_AType (at level 70, no associativity): AType_scope.


(* will now show this is an equivalence relation *)
Lemma eq_AType_refl : forall {n} (A : AType n), A ≡ A.
Proof. intros. constructor; auto. Qed.

Lemma eq_AType_sym : forall {n1 n2} (A : AType n1) (B : AType n2), A ≡ B -> B ≡ A.
Proof. intros. inversion H; subst; constructor; auto. Qed.

Lemma eq_AType_trans : forall {n1 n2 n3} (A : AType n1) (B : AType n2) (C : AType n3),
    A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros.
  inversion H; inversion H0; subst; constructor; auto.
  apply eq_dep_eq in H2, H4.
  apply JMeq_eq_dep; auto. 
  apply eq_implies_JMeq.
  rewrite H2; auto.
  Qed.

Add Parametric Relation n : (AType n) eq_AType
  reflexivity proved by eq_AType_refl
  symmetry proved by eq_AType_sym
  transitivity proved by eq_AType_trans
    as eq_AType_rel.


Lemma permutation_preserves_eq_AType :
  forall {n} (A B : AType n),
    Permutation A B -> A ≡ B.
Proof. intros. constructor; auto.
  apply JMeq_eq_dep; auto. apply eq_implies_JMeq.
  induction H; simpl; auto;
  unfold translateA in *; simpl in *; 
    try rewrite ! fold_left_Mplus;
    try rewrite IHPermutation1; auto. 
  - rewrite IHPermutation; easy.
  - rewrite ! Mplus_assoc. f_equal. rewrite Mplus_comm. auto. 
Qed.

Lemma eq_AType_rel_app_translateA : forall {n} (a b c : AType n),
    a ++ b ≡ c <-> ((translateA a) .+ (translateA b))%M = translateA c.
Proof. intros. unfold translateA in *. 
       split; intros. 
      - rewrite <- fold_left_Mplus_app_Zero, <- map_app.
        inversion H; subst. apply eq_dep_eq in H1. auto.
      - rewrite <- fold_left_Mplus_app_Zero, <- map_app in H.
        constructor; auto. apply eq_eq_dep; auto.
Qed.

Lemma eq_AType_gScaleA_app_comm : forall {n} (a b : AType n) c, gScaleA c (a ++ b) ≡ gScaleA c (b ++ a).
Proof. intros. constructor; auto. 
  apply eq_eq_dep.
  induction a; simpl; try rewrite app_nil_r; try easy.
  unfold translateA in *; simpl.
  rewrite fold_left_Mplus. 
  rewrite IHa. clear IHa.
  induction b; simpl; rewrite fold_left_Mplus; try easy.
  rewrite fold_left_Mplus.
  rewrite <- IHb. clear IHb.
  rewrite ! Mplus_assoc.
  assert (translate (gScaleT c a1) .+ translate (gScaleT c a) = translate (gScaleT c a) .+ translate (gScaleT c a1))%M.
  { rewrite Mplus_comm. easy. }
  rewrite H.
  easy.
Qed.

Lemma eq_AType_gScaleA_gAddA_comm : forall {n} (a b : AType n) c, gScaleA c (gAddA a b) ≡ gScaleA c (gAddA b a).
Proof. intros n a b.
       unfold gAddA.
       apply eq_AType_gScaleA_app_comm.
Qed.

Lemma eq_Atype_gMulA_gMulA' : forall {n} (a b : AType n), gMulA a b ≡ gMulA' a b.
Proof.
  intros n a b.
  unfold gMulA, gMulA'.
  induction a.
  - induction b.
    + reflexivity.
    + simpl. easy.
  - rewrite eq_AType_rel_app_translateA.
    inversion IHa; subst; clear IHa.
    apply eq_dep_eq in H0.
    rewrite H0. clear H0.
    induction b.
    + compute. autorewrite with R_db. reflexivity.
    + simpl.
      unfold translateA in *. simpl in *. rewrite ! map_app in *. rewrite ! map_map in *.
      rewrite ! fold_left_Mplus. rewrite Mplus_assoc.
      assert ((translate (gMulT a a1)
                 .+ fold_left Mplus
                 (map (fun x : TType n => translate (gMulT x a1)) a0 ++
                    map translate (gMulA' a0 b)) Zero)
              =
                (fold_left Mplus
                  (map (fun x : TType n => translate (gMulT x a1)) a0 ++
                     map translate (gMulA' a0 b)) Zero) .+  translate (gMulT a a1) )%M.
      { rewrite Mplus_comm. easy. }
      setoid_rewrite H0.
      rewrite ! fold_left_Mplus_app_Zero.
      rewrite <- ! Mplus_assoc.
      assert (fold_left Mplus (map (fun x : TType n => translate (gMulT a x)) b) Zero
                .+ fold_left Mplus (map (fun x : TType n => translate (gMulT x a1)) a0) Zero
              =
                fold_left Mplus (map (fun x : TType n => translate (gMulT x a1)) a0) Zero
                  .+ fold_left Mplus (map (fun x : TType n => translate (gMulT a x)) b) Zero)%M.
      { rewrite Mplus_comm. easy. }
      rewrite H1. unfold gMulA'.
      unfold translateA in IHb.
      f_equal. rewrite Mplus_assoc. rewrite IHb.
      reflexivity.
Qed.

Lemma eq_AType_gTensorA_gTensorA' : forall {n m} (a : AType n) (b : AType m),
    gTensorA a b ≡ gTensorA' a b.
Proof. intros n m a b. 
  induction a.
  - induction b.
    + reflexivity.
    + simpl. easy. 
  - simpl.
    rewrite eq_AType_rel_app_translateA. 
    inversion IHa; subst; clear IHa.
    apply eq_dep_eq in H0.
    rewrite H0. clear H0.
    induction b.
    + compute. autorewrite with R_db. reflexivity.
    + simpl.
      unfold translateA in *. simpl. rewrite ! map_app in *. rewrite ! map_map in *.
      rewrite ! fold_left_Mplus. rewrite Mplus_assoc.
      assert ((translate (gTensorT a a1)
                 .+ fold_left Mplus
            (map (fun x : TType n => translate (gTensorT x a1)) a0 ++
                map translate (gTensorA' a0 b)) Zero)
             =
               (fold_left Mplus
            (map (fun x : TType n => translate (gTensorT x a1)) a0 ++
               map translate (gTensorA' a0 b)) Zero)
                 .+ translate (gTensorT a a1))%M.
      { rewrite Mplus_comm. easy. }
      setoid_rewrite H0.
      rewrite ! fold_left_Mplus_app_Zero.
      setoid_rewrite Mplus_assoc at 2.
      setoid_rewrite <- IHb.
      assert (fold_left Mplus (map (fun x : TType n => translate (gTensorT x a1)) a0) Zero
                .+ fold_left Mplus (map (fun x : TType n => translate (gTensorT a x)) b) Zero
              =
                fold_left Mplus (map (fun x : TType n => translate (gTensorT a x)) b) Zero
                  .+ fold_left Mplus (map (fun x : TType n => translate (gTensorT x a1)) a0) Zero)%M.
      { rewrite Mplus_comm. easy. }
      rewrite <- ! Mplus_assoc.
      symmetry.
      setoid_rewrite H1.
      f_equal.
Qed.




(***************************************************************************)
(* proving some preliminary lemmas on the TType level before we prove their 
                    counterparts on the Predicate level *)
(***************************************************************************)


Lemma gMulT_assoc_map : forall {n} (a a0 : TType n) (b : AType n),
    proper_length_AType b -> proper_length_TType a -> proper_length_TType a0 ->
    map (fun x : TType n => gMulT (gMulT a a0) x) b = map (fun x : TType n => gMulT a (gMulT a0 x)) b.
Proof. intros n a a0 b H H0 H1.
  induction H.
  - simpl. rewrite gMulT_assoc; try easy.
  - simpl. rewrite gMulT_assoc; try easy. rewrite IHproper_length_AType; easy.
Qed.


Lemma gMulA_map_app : forall {n} (b b0 b1 b2 : AType n) (a : TType n),
    proper_length_AType b -> proper_length_AType b0 ->
    proper_length_AType b1 -> proper_length_AType b2 ->
    proper_length_TType a ->
    gMulA (map (fun x : TType n => gMulT a x) b0 ++ gMulA b b1) b2
    = (map (fun x : TType n => gMulT a x) (gMulA b0 b2) ++ gMulA (gMulA b b1) b2).
Proof. intros n b b0 b1 b2 a H H0 H1 H2 H3. 
  induction H0.
  - simpl. rewrite app_nil_r. rewrite map_map.
    rewrite gMulT_assoc_map; try easy.
  - simpl. rewrite map_app. rewrite map_map. rewrite IHproper_length_AType. rewrite app_assoc.
    rewrite gMulT_assoc_map; try easy.
Qed. 

Lemma gMulA_assoc : forall (n : nat) (a1 a2 a3 : AType n),
  proper_length_AType a1 -> proper_length_AType a2 -> proper_length_AType a3 ->
  gMulA (gMulA a1 a2) a3 = gMulA a1 (gMulA a2 a3).
Proof. intros n a1 a2 a3 H H0 H1.
  induction H; induction H0; induction H1; simpl in *; rewrite gMulT_assoc; try rewrite IHproper_length_AType; try easy. 
  + rewrite map_app. rewrite map_map. rewrite 2 app_nil_r.
    rewrite gMulT_assoc_map; try easy.
  + rewrite app_nil_r in *. rewrite map_map.
    rewrite gMulT_assoc_map; try easy.
  + rewrite <- IHproper_length_AType.
    rewrite gMulA_map_app; try easy; try constructor; try easy.
  + rewrite <- IHproper_length_AType. rewrite gMulA_map_app; try easy; try constructor; try easy. 
    rewrite map_app. rewrite map_map. rewrite app_assoc. rewrite gMulT_assoc_map; try easy.
Qed.



Local Open Scope Predicate_scope.

Lemma Xsqr : pX *' pX = pI.
Proof. simpl. unfold zipWith, cBigMul, gMul_Coef, uncurry. simpl. unfold I.
  do 3 f_equal. repeat f_equal. lca. Qed.       

Lemma Zsqr : pZ *' pZ = pI.
Proof. simpl. unfold zipWith, cBigMul, gMul_Coef, uncurry. simpl. unfold I.
  do 3 f_equal. repeat f_equal. lca. Qed.

Lemma ZmulX : pZ *' pX = - (pX *' pZ).
Proof. simpl. do 3 f_equal.
  unfold zipWith, cBigMul, gMul_Coef, uncurry.  simpl. lca. Qed.



Lemma switch_neg : forall n (A : Predicate n) (c : Coef), - (c ·' A) = c ·' (- A).
Proof. intros n A c.
  induction A; simpl; try inversion H0; try rewrite IHA1, IHA2; try easy.
  - rewrite ! gScaleA_merge.
    rewrite Cmult_comm.
    auto.
  - f_equal. rewrite ! map_map.
    f_equal. apply functional_extensionality. intros.
    rewrite ! gScaleA_merge.
    rewrite Cmult_comm.
    auto.
  - do 2 destruct p. simpl.
    rewrite ! map_map. do 4 f_equal.
    apply functional_extensionality; intros. 
    rewrite ! map_map. f_equal.
    apply functional_extensionality; intros. 
    rewrite ! gScaleTTypes_merge.
    f_equal. lca.
Qed.

Lemma gMulT_gScaleT_map : forall {n} (a : TType n) (b : AType n),
    proper_length_TType a -> proper_length_AType b ->
    (map (fun x : TType n => gMulT (gScaleT (- C1)%C a) x) b)
    = (map (fun x : TType n => gScaleT (- C1)%C (gMulT a x)) b).
Proof. intros n a b H H0. induction H0.
  - simpl. f_equal. destruct a, t. simpl. f_equal. lca.
  - simpl. rewrite IHproper_length_AType. f_equal. destruct a, t. simpl. f_equal. lca.
Qed.


Lemma neg_dist_add : forall (n : nat) (A B : Predicate n), - (A +' B) = -A +' -B.
Proof. intros n A B.
  induction A; induction B; simpl; try easy.
  unfold gScaleA, gAddA.
  rewrite ! map_app.
  auto.
Qed. 

Lemma i_sqr : forall (n : nat) (A : Predicate n), +i (+i A) = -A.
Proof. intros. 
  induction A; simpl; auto; try rewrite IHA1, IHA2; try easy.
  - rewrite gScaleA_merge.
    do 2 f_equal.
    lca.
  - f_equal. rewrite ! map_map.
    f_equal. apply functional_extensionality. intros.
    rewrite gScaleA_merge.
    do 2 f_equal.
    lca.
  - do 2 destruct p. simpl.
    rewrite ! map_map. do 4 f_equal.
    apply functional_extensionality; intros. 
    rewrite ! map_map. f_equal.
    apply functional_extensionality; intros. 
    rewrite ! gScaleTTypes_merge.
    f_equal. lca.
Qed.



Lemma i_neg_comm : forall (n : nat) (A : Predicate n), +i (-A) = -i A.
Proof. intros.
  induction A; simpl; auto; try rewrite IHA1, IHA2; try easy.
  - rewrite gScaleA_merge.
    do 2 f_equal.
    lca.
  - f_equal. rewrite ! map_map.
    f_equal. apply functional_extensionality. intros.
    rewrite gScaleA_merge.
    do 2 f_equal.
    lca.
  - do 2 destruct p. simpl.
    rewrite ! map_map. do 4 f_equal.
    apply functional_extensionality; intros. 
    rewrite ! map_map. f_equal.
    apply functional_extensionality; intros. 
    rewrite ! gScaleTTypes_merge.
    f_equal. lca.
Qed.

#[export] Hint Resolve switch_neg neg_dist_add i_sqr i_neg_comm : typing_db.
#[export] Hint Rewrite switch_neg neg_dist_add i_sqr i_neg_comm : typing_db.



(** ** Tensor Laws *)


Lemma gTensorT_assoc : forall {n : nat} (t1 t2 t3 : TType n),
  proper_length_TType t1 -> proper_length_TType t2 -> proper_length_TType t3 ->
  gTensorT (gTensorT t1 t2) t3 = gTensorT t1 (gTensorT t2 t3).
Proof. intros n t1 t2 t3 H H0 H1.
  unfold gTensorT. destruct t1, t2, t3. f_equal. lca. rewrite app_assoc. easy.
Qed.


Lemma gTensorA_assoc_map : forall {n} (a : TType n) (b b0 b1 b2 : AType n),
    proper_length_TType a -> proper_length_AType b  -> proper_length_AType b0  -> proper_length_AType b1  -> proper_length_AType b2 ->
    gTensorA (map (fun x : TType n => gTensorT a x) b0 ++ gTensorA b b1) b2 =
      (map (fun x : TType n => gTensorT a x) (gTensorA b0 b2) ++ gTensorA (gTensorA b b1) b2).
Proof. intros n a b b0 b1 b2 H H0 H1 H2 H3.
  induction H1; simpl.
  - rewrite app_nil_r. f_equal. rewrite map_map. induction H3; simpl; try rewrite IHproper_length_AType; f_equal; destruct a, t, t0; simpl; f_equal; try lca; rewrite app_assoc; easy.
  - rewrite map_app, map_map. rewrite IHproper_length_AType, <- app_assoc. f_equal.
    clear IHproper_length_AType. induction H3; simpl; try rewrite IHproper_length_AType; f_equal; destruct a, t, t0; simpl; f_equal; try lca; rewrite app_assoc; easy.
Qed.


Lemma gTensorA_assoc : forall (n : nat) (a1 a2 a3 : AType n),
  proper_length_AType a1 -> proper_length_AType a2 -> proper_length_AType a3 ->
  gTensorA (gTensorA a1 a2) a3 = gTensorA a1 (gTensorA a2 a3).
Proof. intros n a1 a2 a3 H H0 H1. 
  induction H; induction H0; induction H1; simpl in *; f_equal; try apply (gTensorT_assoc t t0 t1); try rewrite IHproper_length_AType; try easy; repeat rewrite app_nil_r in *; try rewrite map_app; try rewrite map_map.
  1,2: f_equal; clear IHproper_length_AType; clear IHproper_length_AType0; induction H3; simpl; try rewrite IHproper_length_AType; f_equal; destruct t, t0, t2; simpl; f_equal; try lca; repeat rewrite app_assoc; easy.
  + rewrite <- IHproper_length_AType. rewrite gTensorA_assoc_map; try easy; constructor; easy.
  + clear IHproper_length_AType1. clear IHproper_length_AType0.
    rewrite <- IHproper_length_AType. rewrite <- app_assoc. f_equal.
    * clear IHproper_length_AType; induction H4; simpl; try rewrite IHproper_length_AType; f_equal; destruct t, t0, t2; simpl; f_equal; try lca; rewrite app_assoc; easy.
    * rewrite gTensorA_assoc_map; try easy; constructor; easy.
Qed.



Import my_H.




Lemma pad_Sep_listP_succ : forall (l0 : list Pauli) (l : list nat) (n : nat),
    length l0 = length l -> (length l <= n)%nat -> incl l (List.seq 0 n) ->
    (pad_Sep_listP l0 l (S n)) = (pad_Sep_listP l0 l n) ++ [gI].
Proof. intros l0 l n H0 H1 H2.
  gen l0 n.
  induction l; intros.
  - rewrite ! pad_Sep_listP_nil_r.
    simpl. rewrite repeat_cons. auto.
  - simpl in *.
    destruct l0; simpl in *; try lia.
    apply Nat.succ_inj in H0.
    assert (length l <= n)%nat by lia.
    apply incl_cons_inv in H2.
    destruct H2.
    specialize (IHl l0 H0 n H3 H4).
    rewrite IHl.
    rewrite in_seq in H2.
    rewrite switch_inc at 1.
    rewrite skipn_app.
    rewrite pad_Sep_listP_length.
    assert (S a - n = 0)%nat by lia.
    rewrite H5.
    rewrite skipn_O.
    rewrite firstn_app.
    rewrite pad_Sep_listP_length.
    assert (a - n = 0)%nat by lia.
    rewrite H6.
    rewrite firstn_O.
    rewrite app_nil_r.
    rewrite switch_inc.
    rewrite ! app_assoc.
    f_equal.
    rewrite pad_Sep_listP_length; lia.
    rewrite app_length, pad_Sep_listP_length; lia.
Qed.



Lemma WF_AType_in_trace_zero_syntax : forall {n : nat} (a : AType n) (t : TType n),
    WF_AType a -> In t a -> trace_zero_syntax (snd t).
Proof. intros n a t H0 H1.
  destruct t.
  simpl.
  gen c l.
  inversion H0; subst; clear H0.
  induction H1; intros.
  - inversion H1; subst; clear H1.
    + inversion H0; clear H0.
      auto.
    + inversion H2.
  - rewrite gScaleA_dist_app in H1.
    rewrite in_app_iff in H1.
    assert (H' : (C1 * √ 2 * (C1 / √ 2))%C = C1)
      by (field_simplify_eq; auto; nonzero).
    destruct H1 as [H1 | H1].
    + apply in_gScaleTA_mult with (c := (C1 * √2)%C) in H1.
      rewrite gScaleA_merge in H1.
      rewrite H' in H1.
      rewrite gScaleA_1 in H1.
      simpl in H1.
      specialize (IHrestricted_addition_syntactic1 (C1 * √ 2 * c)%C l H1); auto.
    + apply in_gScaleTA_mult with (c := (C1 * √2)%C) in H1.
      rewrite gScaleA_merge in H1.
      rewrite H' in H1.
      rewrite gScaleA_1 in H1.
      simpl in H1.
      specialize (IHrestricted_addition_syntactic2 (C1 * √ 2 * c)%C l H1); auto.
Qed.


Definition ith_TType {n} (bit : nat) (T : TType n) : Pauli :=
  match T with
  | (c, l) => nth bit l gI
  end.

Definition ith_switch_TType {n} (bit : nat) (T : TType n) (T' : TType 1) : TType n :=
  match T with
  | (c, l) => match T' with
              | (c', l') => ((c * c')%C, switch l (hd gI l') bit)
              end
  end.


Lemma WF_helper : forall (l : list Pauli) (i : nat),
  WF_Matrix (nth i (map translate_P l) Zero).
Proof. intros. 
       destruct (nth_in_or_default i (map translate_P l) Zero).
       - apply in_map_iff in i0.
         destruct i0 as [x [H H0] ].
         rewrite <- H.
         apply WF_Matrix_Pauli.
       - rewrite e. easy. 
Qed.

Lemma WF_helper2 : forall {bit} (l : list Pauli), 
  length l = bit ->
  @WF_Matrix (2^ bit) (2^ bit) (⨂ map translate_P l).
Proof. intros; subst.
       assert (H' := (WF_big_kron _ _ (map translate_P l) Zero)).
       rewrite map_length in H'.
       apply H'.
       intros; apply WF_helper.
Qed.

Hint Resolve WF_helper WF_helper2 : wf_db.