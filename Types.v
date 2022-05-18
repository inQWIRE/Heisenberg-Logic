Require Import Psatz. 
Require Import Reals.
 

Require Export Heisenberg. 


(* some prelim defs and lemmas *)



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


(* function to switch the nth elem of ls with x. Does this already exist?? *)
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
    (n < length ls)%nat ->
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
    (n < length ls)%nat -> switch ls x n = (firstn n ls) ++ switch (skipn n ls) x 0.
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
    skipn n ls = [] -> (length ls <= n)%nat. 
Proof. intros. 
       rewrite <- (firstn_skipn n ls).
       rewrite H. 
       rewrite <- app_nil_end.
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
    (n < length ls)%nat -> switch (skipn n ls) x 0 = [x] ++ (skipn (S n) ls).
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
    (n < length ls)%nat -> switch ls x n = (firstn n ls) ++ [x] ++ (skipn (S n) ls). 
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
    (n < length ls)%nat -> skipn n ls = [nth n ls x] ++ skipn (S n) ls.
Proof. induction n as [| n']. 
       - destruct ls. easy. easy. 
       - intros. destruct ls. 
         assert (H' : forall (n : nat), (S n < 0)%nat -> False). { nia. }
         apply H' in H. easy.
         rewrite skipn_cons.
         replace (nth (S n') (x0 :: ls) x) with (nth n' ls x) by easy.        
         rewrite (IHn' ls x). 
         easy. 
         simpl in H. 
         apply lt_S_n in H.
         easy.
Qed.
         


Lemma nth_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    (n < length ls)%nat -> ls = (firstn n ls) ++ [nth n ls x] ++ (skipn (S n) ls). 
Proof. intros.
       rewrite <- nth_helper.  
       rewrite (firstn_skipn n ls).
       reflexivity. easy. 
Qed.



(* a similar lemma to the one defined by Coq, but better for our purposes *)
Lemma skipn_length' : forall {X : Type} (n : nat) (ls : list X),
    length (skipn (S n) ls) = (length ls - n - 1)%nat.
Proof. intros. 
       rewrite skipn_length.
       nia. 
Qed.



(* how to make something not opaque? *)
Opaque skipn.



(************************)
(* Defining coeficients *)
(************************)


Inductive Coef :=
| p_1
| p_i
| n_1
| n_i.

Definition cNeg (c : Coef) : Coef :=
  match c with
  | p_1 => n_1
  | n_1 => p_1
  | p_i => n_i
  | n_i => p_i
  end.

Lemma cNeg_inv : forall (c : Coef), cNeg (cNeg c) = c.
Proof. destruct c; easy.
Qed.


Definition cMul (c1 c2 : Coef) : Coef :=
  match (c1, c2) with
  | (p_1, _) => c2
  | (_, p_1) => c1
  | (n_1, _) => cNeg c2
  | (_, n_1) => cNeg c1
  | (p_i, p_i) => n_1
  | (n_i, n_i) => n_1
  | (p_i, n_i) => p_1
  | (n_i, p_i) => p_1
  end.

Fixpoint cBigMul (cs : list Coef) : Coef := 
  match cs with
  | nil => p_1 
  | c :: cs' => cMul c (cBigMul cs')
  end. 


 
Infix "*" := cMul (at level 40, left associativity) : heisenberg_scope. 


Lemma cMul_comm : forall (c1 c2 : Coef), c1 * c2 = c2 * c1.
Proof. intros. 
       destruct c1;
       destruct c2;
       easy. 
Qed.

Lemma cMul_assoc : forall (c1 c2 c3 : Coef), (c1 * c2) * c3 = c1 * (c2 * c3).
Proof. intros. 
       destruct c1;
       destruct c2;
       destruct c3;
       easy. 
Qed.


Lemma cBigMul_app : forall (l1 l2 : list Coef),
  (cBigMul l1) * (cBigMul l2) = cBigMul (l1 ++ l2).
Proof. induction l1 as [| h]; try easy.
       intros. simpl. 
       rewrite cMul_assoc, IHl1; easy.
Qed.



Definition translate_coef (c : Coef) : C :=
  match c with
  | p_1 => C1
  | p_i => Ci
  | n_1 => -C1
  | n_i => -Ci
  end. 

Lemma translate_coef_cMul : forall (c1 c2 : Coef), 
    translate_coef (c1 * c2) = ((translate_coef c1) * (translate_coef c2))%C. 
Proof. intros.
       destruct c1; 
       destruct c2;
       unfold translate_coef;
       unfold cMul;
       unfold cNeg;
       try lca. 
Qed.

Lemma translate_coef_nonzero : forall (c : Coef), translate_coef c <> C0.
Proof. destruct c; simpl; 
         try (apply C0_fst_neq; simpl; lra);
         try (apply C0_snd_neq; simpl; lra).
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

Definition translate_P (g : Pauli) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gY => σy
  | gZ => σz
  end. 


Lemma WF_Unitary_Pauli : forall (g : Pauli), WF_Unitary (translate_P g).
Proof. intros. 
       destruct g; simpl; auto with unit_db.
Qed.

Hint Resolve WF_Unitary_Pauli : U_db.

(* Here we define a gMul to give Coef followed by a gMul to give the actual type *)
(* this allows for an easy zip in gMulT *)

Definition gMul_Coef (g1 g2 : Pauli) : Coef :=
  match g1, g2 with
  | gI, _ => p_1
  | _, gI => p_1
  | gX, gX => p_1
  | gY, gY => p_1
  | gZ, gZ => p_1
  | gX, gY => p_i
  | gY, gX => n_i
  | gX, gZ => n_i
  | gZ, gX => p_i
  | gY, gZ => p_i
  | gZ, gY => n_i
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



(* THIS IS THE FIRST IMPORTANT LAYER OF THE TYPE SYSTEM: TENSORING LAYER *)
(* scaling, multiplication, and tensoring done at this level *)
Definition TType (len : nat) := (Coef * (list Pauli))%type. 

(* we define an error TType for when things go wrong *)
Definition ErrT : TType 0 := (p_1, []).


Definition gMulT {n} (A B : TType n) : TType n :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if length g1 =? length g2 
                 then (c1 * c2 * (cBigMul (zipWith gMul_Coef g1 g2)), 
                       zipWith gMul_base g1 g2)
                 else ErrT
    end
  end.


Definition gTensorT {n m} (A : TType n) (B : TType m) : TType (n + m) :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if (length g1 =? n) && (length g2 =? m) 
                 then (c1 * c2, g1 ++ g2)
                 else ErrT
    end
  end.

Definition gScaleT {n} (c : Coef) (A : TType n) : TType n :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.


Definition translate {n} (A : TType n) : Square (2^n) := 
  (translate_coef (fst A)) .* ⨂ (map translate_P (snd A)).
  



(* THIS PART IS SUPER IMPORTANT AS IT DEFINES THE ENTIRE TYPE STRUCTURE *)
Inductive vType (n : nat) : Type :=
  | G : TType n -> vType n
  | Capv : vType n -> vType n -> vType n
  | Errv : vType n.

Arguments G {n}.
Arguments Capv {n}.
Arguments Errv {n}.

Inductive pType (n : nat) : Type :=
  | Arrow : vType n -> vType n -> pType n
  | Capp : pType n -> pType n -> pType n
  | Errp : pType n.

Arguments Arrow {n}.
Arguments Capp {n}.
Arguments Errp {n}.


(* you cannot multiply intersection or arrow types (for now) 
   so any of these options returns Err *)
Definition mul {n} (A B : vType n) : vType n :=
  match A with
  | G a =>
    match B with
    | G b => G (gMulT a b)
    | _ => Errv
    end
  | _ => Errv
  end.
                                       
Definition tensor {n m} (A : vType n) (B : vType m) : vType (n + m) :=
  match A with
  | G a =>
    match B with
    | G b => G (gTensorT a b)
    | _ => Errv 
    end
  | _ => Errv
  end.

(* since scaling intersections makes sense, we allow this *)
Fixpoint scale {n} (c : Coef) (A : vType n) : vType n :=
  match A with
  | G a => G (gScaleT c a)
  | Capv g1 g2 => Capv (scale c g1) (scale c g2)
  | _ => Errv
  end.


Definition i {n} (A : vType n) := scale p_i A.
Notation "- A" := (scale n_1 A).
Infix ".*" := mul (at level 40, left associativity).
Infix ".⊗" := tensor (at level 51, right associativity).



Notation "A ∩ B" := (Capv A B) (at level 52, no associativity).
Notation "A → B" := (Arrow A B) (at level 60, no associativity).
Notation "A ⩀ B" := (Capp A B) (at level 61, no associativity).

(******************************************************************************)
(* Defining different types of vTypes to ensure WF and Singleton translations *)
(******************************************************************************)


Inductive Sing_vt {n} : vType n -> Prop :=
| G_svt : forall tt : TType n, Sing_vt (G tt). 

Inductive Cap_vt {n} : vType n -> Prop :=
| G_cvt : forall tt : TType n, Cap_vt (G tt)
| Cap_cvt : forall T1 T2 : vType n, Cap_vt T1 -> Cap_vt T2 -> Cap_vt (Capv T1 T2). 

Lemma sing_implies_cap : forall {n} (T : vType n),
  Sing_vt T -> Cap_vt T.
Proof. intros. inversion H; apply G_cvt. Qed.

(* we also use a bool version of Cap_vt for matching *)
Fixpoint Cap_vt_bool {n} (A : vType n) : bool :=
  match A with
  | G _ => true
  | Capv v1 v2 => Cap_vt_bool v1 && Cap_vt_bool v2
  | _ => false
  end.

Lemma Cap_vt_conv : forall {n} (A : vType n),
  Cap_vt A <-> Cap_vt_bool A = true.
Proof. intros. split. 
       + induction A as [| |]; try easy.
         - intros.
           inversion H.
           simpl; rewrite IHA1, IHA2; try easy.
       + induction A as [| |]; try easy.
         - intros.
           apply G_cvt. 
         - intros. 
           simpl in *. 
           apply andb_true_iff in H.
           destruct H.
           apply Cap_cvt; 
           try (apply IHA1); 
           try (apply IHA2); 
           assumption.
Qed.         

Inductive Sing_pt {n} : pType n -> Prop :=
| Arrow_spt : forall T1 T2 : vType n, Cap_vt T1 -> Cap_vt T2 -> Sing_pt (Arrow T1 T2). 

Inductive Cap_pt {n} : pType n -> Prop :=
| Arrow_cpt : forall T : pType n, Sing_pt T -> Cap_pt T
| Cap_cpt : forall T1 T2 : pType n, Cap_pt T1 -> Cap_pt T2 -> Cap_pt (Capp T1 T2).

(*
Fixpoint translate_vecType {n} (A : vType n) : vecType (2^n) := 
  match Cap_vt_bool A with
  | false => []
  | true => 
    match A with
    | G g => [translate g]
    | Cap v1 v2 => translate_vecType v1 ++ translate_vecType v2
    | _ => []
    end
  end.
*)

(*
Lemma singleton_sing_vt : forall {n m} (A : vType n), 
  Sing_vt A -> @Singleton m (translate_vecType A).
Proof. intros. destruct A; easy. 
Qed.
*)

Lemma sing_vt_simplify : forall {n} (A : vType n),
  Sing_vt A -> (exists a, A = G a).
Proof. intros. destruct A; try easy.
       exists t. reflexivity. 
Qed. 


Definition I : vType 1 := G (p_1, [gI]).
Definition X : vType 1 := G (p_1, [gX]).
Definition Y : vType 1 := G (p_1, [gY]).
Definition Z : vType 1 := G (p_1, [gZ]).

(*
Lemma Itrans : translate_vecType I = I'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.

Lemma Xtrans : translate_vecType X = X'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.

Lemma Ytrans : translate_vecType Y = Y'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r, Y_eq_iXZ.
       distribute_scale.
       reflexivity. 
Qed.

Lemma Ztrans : translate_vecType Z = Z'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.
*)

Lemma Y_is_iXZ : Y = (i (X .* Z)).
Proof. easy. Qed.



(***************)
(* Sing Lemmas *)
(***************)

Lemma SI : Sing_vt I. Proof. easy. Qed.
Lemma SX : Sing_vt X. Proof. easy. Qed.
Lemma SZ : Sing_vt Z. Proof. easy. Qed.

Lemma S_scale : forall {n} (A : vType n) (c : Coef), Sing_vt A -> (Sing_vt (scale c A)).  
Proof. intros. destruct A; easy. Qed. 

Lemma S_neg : forall {n} (A : vType n), Sing_vt A -> Sing_vt (- A).
Proof. intros. destruct A; easy. Qed. 
 
Lemma S_i : forall {n} (A : vType n), Sing_vt A -> Sing_vt (i A).
Proof. intros. destruct A; easy. Qed. 

Lemma S_mul : forall {n} (A B : vType n), Sing_vt A -> Sing_vt B -> Sing_vt (A .* B).
Proof. intros.
       destruct A; destruct B; easy.
Qed.

Lemma S_tensor : forall {n m} (A : vType n) (B : vType m), Sing_vt A -> Sing_vt B -> Sing_vt (A .⊗ B).
Proof. intros.
       destruct A; destruct B; easy.
Qed.

Hint Resolve sing_implies_cap SI SX SZ S_scale S_neg S_i S_mul S_tensor : wfvt_db.

Lemma SY : Sing_vt Y.
Proof. rewrite Y_is_iXZ. auto with wfvt_db. Qed.




(**************************)
(* Well Formedness Lemmas *)
(**************************)

 
Inductive WF_TType {len : nat} : TType len -> Prop :=
| WF_tt : forall tt : TType len, length (snd tt) = len -> WF_TType tt.

Inductive WF_vType {n} : vType n -> Prop :=
| WF_G : forall tt : TType n, WF_TType tt -> WF_vType (G tt)
| WF_Capv : forall T1 T2 : vType n, WF_vType T1 -> WF_vType T2 -> WF_vType (Capv T1 T2).


Inductive WF_pType {n} : pType n -> Prop :=
| WF_Arrow : forall T1 T2 : vType n, WF_vType T1 -> WF_vType T2 -> WF_pType (Arrow T1 T2)
| WF_Capp : forall T1 T2 : pType n, WF_pType T1 -> WF_pType T2 -> WF_pType (Capp T1 T2).


Lemma WF_I : WF_vType I. Proof. apply WF_G; easy. Qed.
Lemma WF_X : WF_vType X. Proof. apply WF_G; easy. Qed.
Lemma WF_Z : WF_vType Z. Proof. apply WF_G; easy. Qed.

Lemma WF_scale : forall {n} (A : vType n) (c : Coef), 
  Sing_vt A -> WF_vType A ->
  (WF_vType (scale c A)).  
Proof. intros. 
       destruct A; try easy.
       apply WF_G.
       apply WF_tt.
       inversion H0. 
       inversion H2. 
       destruct t; easy.
Qed.

Lemma WF_mul : forall {n} (A B : vType n),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .* B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct t;
       destruct t0. simpl.  
       inversion H1; inversion H2; inversion H4; inversion H6.       
       simpl in *; rewrite H7, H9; bdestruct_all.
       apply WF_G; apply WF_tt.
       simpl. 
       rewrite (zipWith_len_pres _ n); easy.
Qed.


Lemma WF_tensor : forall {n m} (A : vType n) (B : vType m),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .⊗ B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct t;
       destruct t0.
       simpl in *. 
       inversion H1; inversion H2; inversion H4; inversion H6.       
       simpl in *; rewrite H7, H9; bdestruct_all.
       apply WF_G; apply WF_tt.
       simpl. 
       rewrite app_length;
       lia. 
Qed.


Lemma WF_neg : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (- A). 
Proof. intros. 
       destruct A; try easy.
       inversion H0; inversion H2.
       apply WF_G; apply WF_tt.
       destruct t; easy.
Qed.
   
Lemma WF_i : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (i A). 
Proof. intros. 
       destruct A; try easy.
       inversion H0; inversion H2.
       apply WF_G; apply WF_tt.
       destruct t; easy.
Qed.


Hint Resolve SI SX SZ WF_I WF_X WF_Z WF_mul WF_scale WF_tensor WF_neg WF_i : wfvt_db.


Lemma WF_Y : WF_vType Y.
Proof. rewrite Y_is_iXZ. auto with wfvt_db. Qed.



(******************)
(* unitary lemmas *)
(******************)



Lemma unitary_Pauli : forall (p : Pauli), WF_Unitary (translate_P p).
Proof. intros. 
       destruct p; simpl; auto with unit_db.
Qed.


Lemma unitary_TType : forall {n} (A : TType n), WF_TType A -> WF_Unitary (translate A). 
Proof. intros. destruct A.
       unfold translate; simpl. 
       inversion H; simpl in *.
       rewrite map_length, <- H0.
       apply scale_unitary.
       apply big_kron_unitary'.
       apply map_length.
       intros. 
       apply in_map_iff in H2.
       destruct H2 as [x [H2 H3]].
       rewrite <- H2; auto with unit_db.
       apply unitary_Pauli.
       destruct c; try lca.
Qed.       
       
Hint Resolve unitary_Pauli unitary_TType : unit_db.



(*************)
(* WFS types *)
(*************)

Inductive WFS_vType {n} : vType n -> Prop :=
| WFS : forall T : vType n, Sing_vt T -> WF_vType T -> WFS_vType T.


Lemma WFS_I : WFS_vType I. Proof. apply WFS; auto with wfvt_db. Qed.
Lemma WFS_X : WFS_vType X. Proof. apply WFS; auto with wfvt_db. Qed.
Lemma WFS_Z : WFS_vType Z. Proof. apply WFS; auto with wfvt_db. Qed.


Lemma WFS_mul : forall {n} (A B : vType n),
  WFS_vType A -> WFS_vType B -> 
  WFS_vType (A .* B). 
Proof. intros n A B H H0. 
       inversion H; inversion H0.
       apply WFS; auto with wfvt_db.
Qed.


Lemma WFS_tensor : forall {n m} (A : vType n) (B : vType m),
  WFS_vType A -> WFS_vType B ->
  WFS_vType (A .⊗ B). 
Proof. intros n m A B H H0. 
       inversion H; inversion H0.
       apply WFS; auto with wfvt_db.
Qed.


Lemma WFS_scale : forall {n} (A : vType n) (c : Coef),
  WFS_vType A ->  WFS_vType (scale c A). 
Proof. intros n A c H.
       inversion H.
       apply WFS; auto with wfvt_db.
Qed.

Lemma WFS_neg : forall {n} (A : vType n),
  WFS_vType A ->  WFS_vType (- A). 
Proof. intros n A [H H0]. 
       apply WFS_scale; easy. 
Qed.
   
Lemma WFS_i : forall {n} (A : vType n),
  WFS_vType A ->  WFS_vType (i A). 
Proof. intros n A H.
       unfold i. 
       apply WFS_scale; easy. 
Qed.

Hint Resolve WFS_I WFS_X WFS_Z WFS_scale WFS_mul WFS_tensor WFS_neg WFS_i : wfvt_db.


(******************************************************)
(* Showing translations preserves relevent properties *)
(******************************************************)

(* we actually use this to prove translate_mult, so we prove it first *)
Lemma translate_kron : forall {n m} (g1 : TType n) (g2 : TType m),
    length (snd g1) = n -> length (snd g2) = m ->
    translate (gTensorT g1 g2) = (translate g1) ⊗ (translate g2).
Proof. intros. unfold translate.
         destruct g1; destruct g2.
         simpl in *.
         do 3 (rewrite map_length). 
         rewrite H, H0 in *.
         rewrite Mscale_kron_dist_r.
         rewrite Mscale_kron_dist_l.
         rewrite Mscale_assoc.
         bdestruct_all; simpl. 
         rewrite translate_coef_cMul.
         rewrite Cmult_comm.
         rewrite map_app. 
         assert (H3 : forall (l : list Pauli) (i0 : nat), WF_Matrix (nth i0 (map translate_P l) Zero)).
         { intros. 
           bdestruct (i0 <? length (map translate_P l1)).
           + apply (nth_In _ (@Zero 2 2)) in H3.
             apply in_map_iff in H3.
             destruct H3 as [x [H3 H4]].
             rewrite <- H3; apply WF_Unitary_Pauli.
           + rewrite nth_overflow; try lia. 
             auto with wf_db. }
         rewrite big_kron_app; auto.
         do 2 (rewrite map_length).
         rewrite app_length.
         rewrite H, H0 in *.
         reflexivity.
Qed.


Lemma gMulT_reduce : forall (n : nat) (c1 c2 : Coef) (p1 p2 : Pauli) (l1 l2 : list Pauli),
  length l1 = n -> length l2 = n ->
  gMulT (c1, p1 :: l1) (c2, p2 :: l2) = 
  @gTensorT 1 n (gMul_Coef p1 p2, [gMul_base p1 p2]) (gMulT (c1, l1) (c2, l2)).
Proof. intros. simpl.
       rewrite H, H0.
       bdestruct (n =? n); try lia. 
       rewrite (zipWith_len_pres _ n); try easy.
       bdestruct (n =? n); try lia. 
       rewrite zipWith_cons.
       apply injective_projections; try easy.
       simpl.
       unfold zipWith. 
       rewrite <- (cMul_assoc (c1 * c2)), (cMul_comm (c1 * c2)). 
       replace (uncurry gMul_Coef (p1, p2)) with (gMul_Coef p1 p2) by easy.
       rewrite cMul_assoc; easy. 
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
Proof. intros. induction n as [| n'].
       - destruct g1; destruct g2. 
         destruct l; destruct l0; try easy. 
         unfold translate. simpl. 
         distribute_scale.
         rewrite Mmult_1_r; auto with wf_db.
         rewrite <- translate_coef_cMul.
         destruct c; destruct c0; try easy.
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
         rewrite H, H0; bdestruct_all.
         simpl. 
         apply zipWith_len_pres; easy.
Qed.


(*
Lemma translate_vecType_mMult : forall {n} (A B : vType n),
  WFS_vType A -> WFS_vType B -> 
  translate_vecType (A .* B) = (translate_vecType A) *' (translate_vecType B).
Proof. intros n A B H H0.  
       inversion H; inversion H0.
       destruct A; destruct B; try easy.
       simpl.
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       rewrite translate_Mmult; try easy.
Qed.
*)

Lemma translate_scale : forall {n} (A : TType n) (c : Coef),
  translate (gScaleT c A) = Matrix.scale (translate_coef c) (translate A).
Proof. intros. 
       unfold translate. 
       destruct A. simpl. 
       rewrite translate_coef_cMul.
       rewrite <- Mscale_assoc.     
       reflexivity. 
Qed.



Lemma Cap_vt_scale : forall {n} (A : vType n) (c : Coef), 
    Cap_vt_bool (scale c A) = Cap_vt_bool A.
Proof. intros. induction A as [| |]; try easy.
       simpl. rewrite IHA1, IHA2.
       reflexivity.
Qed.       

(*
Lemma translate_vecType_scale : forall {n} (A : vType n) (c : Coef),
  translate_vecType (scale c A) = (translate_coef c) · (translate_vecType A).
Proof. intros. induction A; try easy.
       - simpl. rewrite translate_scale.
         reflexivity. 
       - simpl translate_vecType.
         do 2 (rewrite Cap_vt_scale).
         destruct (Cap_vt_bool A1 && Cap_vt_bool A2); try easy.
         rewrite IHA1, IHA2.
         rewrite concat_into_scale.
         reflexivity.
Qed.
*)




(**************************)
(* Defining vector typing *)
(**************************)

(*
(* we need this for now. should eventually rewrite defs to make proofs easier *)
Lemma fgt_conv : forall {n m} (A B : vecType n), [(A, B)] = @formGateType m A B.
Proof. easy. Qed.
*)


Lemma ite_conv : forall {X : Type} (x1 x2 : X), (if true && true then x1 else x2) = x1.
Proof. easy. Qed.


Definition vecPair (prg_len : nat) := (Vector (2^prg_len) * C)%type.


Inductive vecHasType {prg_len : nat} : vecPair prg_len -> vType prg_len -> Prop :=
| VHST : forall vp tt, pairHasType vp (translate tt) -> vecHasType vp (G tt)
| VHT : forall vp T1 T2, vecHasType vp T1 -> vecHasType vp T2 -> vecHasType vp (Capv T1 T2).  
  

Notation "p ;' T" := (vecHasType p T) (at level 61, no associativity).



Lemma cap_elim_l_vec : forall {n} (v : vecPair n) (A B : vType n), v ;' (A ∩ B) -> v ;' A.
Proof. intros. 
       inversion H; easy.
Qed.       


Lemma cap_elim_r_vec : forall {n} (v : vecPair n) (A B : vType n), v ;' A ∩ B -> v ;' B.
Proof. intros. 
       inversion H; easy.
Qed.      


Hint Resolve cap_elim_l_vec cap_elim_r_vec : subtype_db.


(***************************************************************************)
(* proving some preliminary lemmas on the TType level before we prove their 
                    counterparts on the vType level *)
(***************************************************************************)


Lemma gMulT_gTensorT_dist : forall {n m : nat} (t1 t2 : TType n) (t3 t4 : TType m),
  WF_TType t1 -> WF_TType t2 -> WF_TType t3 -> WF_TType t4 ->
  gMulT (gTensorT t1 t3) (gTensorT t2 t4) = gTensorT (gMulT t1 t2) (gMulT t3 t4).
Proof. intros. 
       destruct t1; destruct t2; destruct t3; destruct t4. 
       simpl gTensorT.
       inversion H; inversion H0; inversion H1; inversion H2. 
       simpl in *.
       rewrite H3, H5, H7, H9.
       bdestruct_all. simpl. 
       rewrite (zipWith_len_pres _ n), (zipWith_len_pres _ m); try easy.
       do 2 rewrite app_length. 
       rewrite H3, H5, H7, H9.
       bdestruct_all. simpl. 
       apply injective_projections; simpl. 
       - rewrite (cMul_assoc (c * c0)). 
         rewrite (cMul_comm (cBigMul (zipWith gMul_Coef l l0))).
         rewrite (cMul_assoc (c1 * c2)). 
         rewrite (cMul_comm (cBigMul (zipWith gMul_Coef l1 l2))).
         rewrite cBigMul_app.
         rewrite (zipWith_app_product _ n); try easy.
         rewrite (cMul_assoc c), <- (cMul_assoc c1), (cMul_comm c1 c0).
         repeat rewrite cMul_assoc; easy.
       - rewrite (zipWith_app_product _ n); easy.
Qed.


Lemma gMulT_assoc : forall (n : nat) (t1 t2 t3 : TType n),
  WF_TType t1 -> WF_TType t2 -> WF_TType t3 ->
  gMulT (gMulT t1 t2) t3 = gMulT t1 (gMulT t2 t3).
Proof. induction n as [| n']. 
       - intros.
         inversion H; inversion H0; inversion H1.
         destruct t1; destruct t2; destruct t3.
         destruct l; destruct l0; destruct l1; try easy.
         destruct c; destruct c0; destruct c1; easy.
       - intros. 
         inversion H; inversion H0; inversion H1.
         destruct t1; destruct t2; destruct t3.
         destruct l; destruct l0; destruct l1; try easy.
         simpl in H2; simpl in H4; simpl in H6.
         apply Nat.succ_inj in H2;
         apply Nat.succ_inj in H4;
         apply Nat.succ_inj in H6.
         repeat rewrite gMulT_reduce; try easy.
         assert (H8 : (c1, p1 :: l1) = @gTensorT 1 n' (p_1, [p1]) (c1, l1)).
         { simpl. bdestruct_all. easy. }
         assert (H9 : (c, p :: l) = @gTensorT 1 n' (p_1, [p]) (c, l)).
         { simpl. bdestruct_all. easy. }
         rewrite H8, H9. 
         do 2 replace (S n') with (1 + n')%nat by lia.
         rewrite gMulT_gTensorT_dist, gMulT_gTensorT_dist; try easy. 
         rewrite IHn'; try easy.
         assert (H10 : (@gMulT 1 (gMul_Coef p p0, [gMul_base p p0]) (p_1, [p1])) = 
                      (@gMulT 1 (p_1, [p]) (gMul_Coef p0 p1, [gMul_base p0 p1]))).
         { destruct p; destruct p0; destruct p1; easy. }
         rewrite H10; easy. 
         all : simpl; bdestruct_all; apply WF_tt; simpl. 
         all : rewrite (zipWith_len_pres _ n'); easy.
Qed.


(* Multiplication laws *)

Lemma mul_assoc : forall {n} (A B C : vType n), 
  WFS_vType A -> WFS_vType B -> WFS_vType C -> 
  A .* (B .* C) = A .* B .* C. 
Proof. intros. 
       destruct A; destruct B; destruct C; try easy.
       inversion H; inversion H0; inversion H1.
       unfold mul.
       inversion H3; inversion H6; inversion H9.
       rewrite gMulT_assoc; easy. 
Qed.


Lemma mul_I_l : forall (A : vType 1), WFS_vType A -> I .* A = A.
Proof. intros A H.
       inversion H. 
       destruct A; try easy.
       inversion H1; inversion H4.
       destruct t. 
       do 2 (destruct l; try easy).
       simpl. 
       destruct c; easy.
Qed.

Lemma mul_I_r : forall (A : vType 1), WFS_vType A -> A .* I = A.
Proof. intros A H.
       inversion H. 
       destruct A; try easy.
       inversion H1; inversion H4.
       destruct t. 
       do 2 (destruct l; try easy).
       simpl. 
       destruct p; destruct c; easy.
Qed.

Lemma Xsqr : X .* X = I.
Proof. easy. Qed.       

Lemma Zsqr : Z .* Z = I.
Proof. easy. Qed.

Lemma ZmulX : Z .* X = - (X .* Z).
Proof. easy. Qed.


Lemma neg_inv : forall (n : nat) (A : vType n), WFS_vType A -> - - A = A.
Proof. intros n A H. 
       inversion H.
       destruct A; try easy.
       simpl. 
       unfold gScaleT. 
       destruct t; destruct c; easy.  
Qed.


Lemma neg_dist_l : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  -A .* B = - (A .* B).
Proof. intros. 
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       simpl in *.
       rewrite H11, H13.
       bdestruct_all; try easy.
       unfold gScaleT.
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma neg_dist_r : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  A .* (-B) = - (A .* B).
Proof. intros. 
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       simpl in *.
       rewrite H11, H13.
       bdestruct_all; try easy.
       unfold gScaleT.
       rewrite <- cMul_assoc, (cMul_comm c).
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_sqr : forall (n : nat) (A : vType n), i (i A) = -A.
Proof. intros. 
       induction A; try easy. 
       - destruct t. simpl.          
         destruct c; easy.
       - simpl. unfold i in *.
         simpl. 
         rewrite IHA1, IHA2.
         reflexivity. 
Qed.

Lemma i_dist_l : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  i A .* B = i (A .* B).
Proof. intros. 
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       simpl in *.   
       bdestruct_all; try easy.
       unfold gScaleT.
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_dist_r : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  A .* i B = i (A .* B).
Proof. intros. 
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       simpl in *.
       rewrite H11, H13.
       bdestruct_all; try easy.
       unfold gScaleT.
       rewrite <- cMul_assoc, (cMul_comm c).
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_neg_comm : forall (n : nat) (A : vType n), i (-A) = -i A.
Proof. intros.
       induction A; try easy. 
       - destruct t. simpl. 
         destruct c; easy.
       - simpl. unfold i in *.
         simpl. 
         rewrite IHA1, IHA2.
         reflexivity. 
Qed.


(** ** Tensor Laws *)

(*
Lemma tensor_assoc : forall {n m o : nat} (A : vType n) (B : vType m) (C : vType o), 
  eq_vType' (A .⊗ (B .⊗ C)) ((A .⊗ B) .⊗ C).  
Proof. intros. unfold eq_vType'.
       destruct A; destruct B; destruct C; try easy.
       destruct t; destruct t0; destruct t1; simpl.
       rewrite app_ass.
       rewrite cMul_assoc. 
       reflexivity. 
Qed.       
*)


Lemma neg_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  -A .⊗ B = - (A .⊗ B).
Proof. intros.
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       bdestruct_all; try easy; simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma neg_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  A .⊗ (-B) = - (A .⊗ B).
Proof. intros. 
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       bdestruct_all; try easy; simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma i_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  i A .⊗ B = i (A .⊗ B).
Proof. intros.
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       bdestruct_all; try easy; simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma i_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  A .⊗ i B = i (A .⊗ B).
Proof. intros.
       inversion H; inversion H0.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       inversion H2; inversion H5.
       inversion H8; inversion H10.
       bdestruct_all; try easy; simpl. 
       destruct c; destruct c0; easy. 
Qed.



(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Lemma mul_tensor_dist : forall {n m} (A C : vType n) (B D : vType m),
  WFS_vType A -> WFS_vType B -> WFS_vType C -> WFS_vType D ->
  (A .⊗ B) .* (C .⊗ D) = (A .* C) .⊗ (B .* D).
Proof. intros.
       destruct A; destruct B; destruct C; destruct D; try easy.
       inversion H; inversion H0; inversion H1; inversion H2.
       inversion H4; inversion H7; inversion H10; inversion H13.       
       inversion H16; inversion H18; inversion H20; inversion H22.       
       unfold mul, tensor. 
       rewrite gMulT_gTensorT_dist; easy. 
Qed.



Lemma decompose_tensor : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  A .⊗ B = (A .⊗ I) .* (I .⊗ B).
Proof.
  intros A B H H0.  
  rewrite mul_tensor_dist; auto with wfvt_db.
  rewrite mul_I_r, mul_I_l; easy.
Qed.


Lemma decompose_tensor_mult_l : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  (A .* B) .⊗ I = (A .⊗ I) .* (B .⊗ I).
Proof.
  intros. 
  rewrite mul_tensor_dist; auto with wfvt_db.
Qed.


Lemma decompose_tensor_mult_r : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  I .⊗ (A .* B) = (I .⊗ A) .* (I .⊗ B).
Proof.
  intros. 
  rewrite mul_tensor_dist; auto with wfvt_db.
Qed.
  

(*********************)
(* defining programs *)
(*********************)

Inductive prog :=
| H' (n : nat)
| S' (n : nat)
| T' (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).

Infix ";;" := seq (at level 51, right associativity).


(* application def's from pad.v *)
Fixpoint translate_prog (prg_len : nat) (p : prog) : Square (2^prg_len) :=
  match p with 
  | H' n => (prog_smpl_app prg_len n hadamard)
  | S' n => (prog_smpl_app prg_len n Sgate)
  | T' n => (prog_smpl_app prg_len n Tgate)
  | CNOT n1 n2 => (prog_ctrl_app prg_len n1 n2 σx)
  | seq p1 p2 => (translate_prog prg_len p1) ; (translate_prog prg_len p2)
  end.


Lemma unitary_prog : forall (prg_len : nat) (p : prog), 
  WF_Unitary (translate_prog prg_len p).
Proof. intros. 
       induction p as [| | | |]; 
       try (apply unit_prog_smpl_app; auto with unit_db);
       try (apply unit_prog_ctrl_app; auto with unit_db).
       simpl. apply Mmult_unitary; easy. 
Qed.      

Lemma WF_prog : forall (prg_len : nat) (p : prog),
  WF_Matrix (translate_prog prg_len p).
Proof. intros. 
       destruct (unitary_prog prg_len p); easy. 
Qed.

Hint Resolve unitary_prog : unit_db.
Hint Resolve WF_prog : wf_db.


(* note that if things are out of bounds, then things completely fail. *)
(* might want to enforce WFS_vtype *)
Inductive progHasType {prg_len : nat} : prog -> pType prg_len -> Prop :=
| PHST : forall p vt1 vt2, (forall vp, vp ;' vt1 -> 
                            ((translate_prog prg_len p) × (fst vp), snd vp) ;' vt2) ->
                            progHasType p (vt1 → vt2)
| PHT : forall p pt1 pt2, progHasType p pt1 -> progHasType p pt2 -> progHasType p (Capp pt1 pt2).
  

Notation "p :' T" := (progHasType p T) (at level 62, no associativity).


Lemma Hsem_implies_Esem : forall prg_len prog tt1 tt2, 
  translate_prog prg_len prog × translate tt1 = translate tt2 × translate_prog prg_len prog ->
  prog :' (G tt1 → G tt2).
Proof. intros. 
       apply PHST; intros. 
       apply VHST; inversion H0; subst.
       unfold pairHasType in *. 
       split; destruct H3; destruct vp; simpl in *.
       apply WF_mult; auto.
       apply unitary_prog.
       unfold Eigenpair in *; simpl in *.
       rewrite <- Mmult_assoc, <- H, Mmult_assoc, H2.
       distribute_scale.
       easy. 
Qed.


Lemma Esem_implies_Hsem : forall prg_len prog tt1 tt2, 
  WF_TType tt1 -> WF_TType tt2 ->
  prog :' (G tt1 → G tt2) ->  
  translate_prog prg_len prog × translate tt1 = translate tt2 × translate_prog prg_len prog.
Proof. intros. 
       replace (translate tt1) with (fst (translate tt1, translate tt2)) by easy.
       replace (translate tt2) with (snd (translate tt1, translate tt2)) by easy.
       apply Heisenberg.Esem_implies_Hsem; simpl; auto with unit_db.
       inversion H1.
       unfold progHasType_E; intros.
       assert (H' : (v, c) ;' G tt1).
       { apply VHST; apply H6. }
       apply H4 in H'.
       inversion H'; subst.
       easy. 
Qed.



(* 
Inductive progHasType_H {prg_len : nat} : prog -> pType prg_len -> Prop :=
| PHST_H : forall p tt tt, (forall vp, vp ;' vt1 -> 
                            ((translate_prog prg_len p) × (fst vp), snd vp) ;' vt2) ->
                            progHasType p (Arrow vt1 vt2)

*)


(********************)
(* Base type lemmas *)
(********************)


Lemma Hsimp : prog_smpl_app 1 0 hadamard = hadamard.
Proof. unfold prog_smpl_app, pad_u, pad. 
       rewrite kron_1_r, kron_1_l.
       reflexivity. 
       auto with wf_db.
Qed.

Lemma Ssimp : prog_smpl_app 1 0 Sgate = Sgate.
Proof. unfold prog_smpl_app, pad_u, pad. 
       rewrite kron_1_r, kron_1_l.
       reflexivity. 
       auto with wf_db.
Qed.

Lemma adj_ctrlX_is_cnot1 : prog_ctrl_app 2 0 1 σx = cnot.
Proof. unfold prog_ctrl_app, pad_ctrl, pad; simpl. 
       solve_matrix.
Qed.

Lemma Isimp : @translate 1 (p_1, [gI]) = Matrix.I 2. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Xsimp : @translate 1 (p_1, [gX]) = σx. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Zsimp : @translate 1 (p_1, [gZ]) = σz. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Ysimp : @translate 1 (p_1, [gY]) = σy. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.


Lemma kron_simp : forall (g1 g2 : Pauli), 
    @translate 2 (p_1 * p_1, g1 :: [g2]) = (translate_P g1) ⊗ (translate_P g2).  
Proof. intros. 
       unfold translate; simpl. 
       autorewrite with C_db.
       rewrite Mscale_1_l. 
       rewrite kron_1_r. 
       reflexivity. 
Qed.



Hint Rewrite Ssimp Hsimp Isimp Xsimp Zsimp Ysimp adj_ctrlX_is_cnot1 kron_simp : simp_db.

(*
Ltac solve_ground_type := repeat (apply Cap_pht); try apply Arrow_pht; 
                          try apply PHST; try apply G_cvt; simpl; 
                          autorewrite with simp_db;
                          repeat split;
                          repeat (apply sgt_implies_sgt'; try easy; 
                                  apply singleton_simplify2;
                                  unfold translate; simpl; auto with id_db).
*)


Lemma HTypes : H' 0 :' (X → Z) ⩀ (Z → X).
Proof. apply PHT;
       apply Hsem_implies_Esem;
       unfold translate; simpl; unfold prog_smpl_app, pad_u, pad; simpl;
       solve_matrix.
Qed.


Lemma HTypes_not : ~ (H' 0 :' X → X).
Proof. unfold not. 
       intros. 
       apply Esem_implies_Hsem in H; auto with wfvt_db.
       assert (H0' : translate_prog 1 (H' 0) = hadamard).
       { simpl. unfold prog_smpl_app, pad_u, pad; simpl;
       solve_matrix. }
       assert (H1' : σx = @translate 1 (p_1, [gX])).
       { unfold translate. solve_matrix. }
       rewrite H0', <- H1' in H.
       assert (H'' : forall (m1 m2 : Square 2), m1 = m2 -> m1 1%nat 0%nat = m2 1%nat 0%nat). 
       { intros. rewrite H0. reflexivity. }
       apply H'' in H. 
       unfold Mmult in H. simpl in H.
       replace (C0 + C1 * (C1 / √ 2) + C0 * (C1 / √ 2)) with (C1 / √ 2) in H by lca. 
       replace (C0 + C1 / √ 2 * C0 + Copp (C1 / √ 2) * C1) with (Copp (C1 / √ 2)) in H by lca. 
       unfold Cdiv in H.
       rewrite Copp_mult_distr_l in H.
       assert (H10 : forall c1 c2 , (c1 = c2 -> c1 * √ 2 = c2 * √ 2)%C). 
       { intros. rewrite H0. easy. }
       apply H10 in H.
       do 2 (rewrite <- Cmult_assoc in H).
       rewrite (Cinv_l (√ 2)) in H.
       do 2 (rewrite Cmult_1_r in H).
       assert (H11: forall {X} (p1 p2 : X * X), p1 = p2 -> fst p1 = fst p2). 
       { intros. rewrite H0. easy. }
       apply H11 in H. simpl in H.
       lra. 
       apply C0_fst_neq. simpl. 
       apply sqrt_neq_0_compat. 
       lra. 
       autorewrite with simp_db; auto with unit_db.
       all : apply WF_tt; easy.
Qed.

Lemma STypes : S' 0 :' (X → Y) ⩀ (Z → Z).
Proof. apply PHT;
       apply Hsem_implies_Esem;
       unfold translate; simpl; unfold prog_smpl_app, pad_u, pad; simpl;
       solve_matrix.
       all : rewrite Cexp_PI2; lca.
Qed.
 

Lemma CNOTTypes : CNOT 0 1 :' (X .⊗ I → X .⊗ X) ⩀ (I .⊗ X → I .⊗ X) ⩀ 
                             (Z .⊗ I → Z .⊗ I) ⩀ (I .⊗ Z → Z .⊗ Z).
Proof. repeat apply PHT; 
         apply Hsem_implies_Esem;  
         unfold translate; simpl; unfold prog_smpl_app, pad_u, pad; simpl. 
       all : rewrite adj_ctrlX_is_cnot1, Mscale_1_l, kron_1_r.
       all : try rewrite kron_1_r; try rewrite Mscale_1_l.
       all : solve_matrix.
Qed.


(*************************)
(* Proving typing lemmas *)
(*************************)


(* in what follows, A B C will be used for vTypes and T1, T2 will be used for ptypes *)

Lemma SeqTypes : forall {n} (g1 g2 : prog) (A B C : vType n),
  g1 :' A → B ->
  g2 :' B → C ->
  (g1 ;; g2) :' A → C.
Proof. intros.
       inversion H; inversion H0; subst.
       apply PHST.
       intros. 
       apply H3 in H1.
       simpl.
       unfold Heisenberg.seq.
       rewrite Mmult_assoc.
       destruct vp; simpl in *. 
       replace (translate_prog n g1 × m) with (fst ((translate_prog n g1 × m), c)) by easy.
       replace c with (snd ((translate_prog n g1 × m), c)) by easy.    
       apply H7.
       easy. 
Qed.


Lemma seq_assoc : forall {n} (g1 g2 g3 : prog) (T : pType n),
    g1 ;; (g2 ;; g3) :' T <-> (g1 ;; g2) ;; g3 :' T.
Proof. induction T as [| |]; try easy. 
       - simpl. split. 
         all : intros;
         inversion H; subst;
         apply PHST;
         intros;
         simpl in *;
         unfold Heisenberg.seq in *.
         rewrite <- Mmult_assoc; apply H2; easy. 
         rewrite (Mmult_assoc (translate_prog n g3)); apply H2; easy. 
       - split; intros;
         inversion H; inversion H2; subst;
         apply PHT; try (apply IHT1; easy); apply IHT2; easy.
Qed.


(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI : forall (p : prog), p :' I → I.
Proof. intros. 
       apply Hsem_implies_Esem.
       unfold translate; simpl.
       rewrite Mscale_1_l, kron_1_r, Mmult_1_l, Mmult_1_r; try easy.
       all : assert (H' := WF_prog 1 p).
       all : simpl in *; auto.
Qed.

  

Lemma TypesI2 : forall (p : prog), p :' I .⊗ I → I .⊗ I.
Proof. intros. 
       apply Hsem_implies_Esem; simpl. 
       unfold translate; simpl.
       rewrite Mscale_1_l, kron_1_r, id_kron, Mmult_1_l, Mmult_1_r; try easy.
       all : assert (H' := WF_prog 2 p).
       all : simpl in *; auto.
Qed.


Hint Resolve TypesI TypesI2 : base_types_db.


(** Structural rules *)

(* Subtyping rules *)
Lemma cap_elim_l : forall {n} (g : prog) (T1 T2 : pType n), g :' T1 ⩀ T2 -> (g :' T1).
Proof. intros. inversion H; easy. Qed.

Lemma cap_elim_r : forall {n} (g : prog) (T1 T2 : pType n), g :' T1 ⩀ T2 -> g :' T2.
Proof. intros. inversion H; easy. Qed.

Lemma cap_intro : forall {n} (g : prog) (T1 T2 : pType n), g :' T1 -> g :' T2 -> g :' T1 ⩀ T2.
Proof. intros. apply PHT; easy.
Qed.

Lemma cap_arrow : forall {n} (g : prog) (A B C : vType n),
  g :' ((A → B) ⩀ (A → C)) ->
  g :' A → (B ∩ C).
Proof. intros. 
       inversion H; subst.
       apply PHST; intros. 
       inversion H3; inversion H4; subst.
       apply VHT.
       apply H5; easy.
       apply H9; easy.
Qed.



Lemma arrow_sub : forall {n} g (A A' B B' : vType n),
  (forall l, l ;' A' -> l ;' A) ->
  (forall r, r ;' B -> r ;' B') ->
  g :' A → B ->
  g :' A' → B'.
Proof. intros. 
       apply PHST; intros. 
       inversion H1; subst.
       destruct vp; simpl in *.
       apply H in H2.
       apply H5 in H2.
       simpl in *.
       apply H0; easy.
Qed.


Hint Resolve cap_elim_l cap_elim_r cap_intro cap_arrow arrow_sub : subtype_db.

Lemma cap_elim : forall {n} g (T1 T2 : pType n), g :' T1 ⩀ T2 -> g :' T1 /\ g :' T2.
Proof. eauto with subtype_db. Qed.


Lemma input_cap_l : forall {n} g (A A' B : vType n), 
  g :' A → B -> g :' (A ∩ A') → B. 
Proof. intros. 
       inversion H.
       apply PHST.
       intros. 
       apply H2.
       inversion H4; easy.
Qed.

Lemma input_cap_r : forall {n} g (A A' B : vType n), 
  g :' A → B -> g :' (A' ∩ A) → B. 
Proof. intros. 
       inversion H.
       apply PHST.
       intros. 
       apply H2.
       inversion H4; easy.
Qed.

Lemma cap_arrow_distributes : forall {n} g (A A' B B' : vType n),
  g :' (A → A') ⩀ (B → B') ->
  g :' (A ∩ B) → (A' ∩ B').
Proof.
  intros; apply cap_arrow.
  apply cap_intro; eauto with subtype_db.
Qed.


(* Full explicit proof *)
Lemma cap_arrow_distributes' : forall {n} g (A A' B B' : vType n),
  g :' (A → A') ⩀ (B → B') ->
  g :' (A ∩ B) → (A' ∩ B').
Proof. intros.       
       inversion H; subst.
       apply PHST; intros.
       inversion H0; subst.
       apply VHT.
       - inversion H3; subst.
         apply H5; easy.
       - inversion H4; subst.
         apply H5; easy.
Qed.


(***************************************************)
(* Prelim lemmas for tensoring in the next section *)
(***************************************************)


Local Open Scope nat_scope. 

Notation s := Datatypes.S.


Definition smpl_prog_H (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = H' n).
Definition smpl_prog_S (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = S' n).

Definition smpl_prog_T (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = T' n).
        
Definition smpl_prog (p : nat -> prog) : Prop := 
  smpl_prog_H p \/ smpl_prog_S p \/ smpl_prog_T p.


Definition ctrl_prog (p : prog) : Prop :=
  match p with 
  | CNOT _ _ => True 
  | _ => False
  end.


Lemma smpl_prog_H_ver : smpl_prog H'. Proof. left. easy. Qed.
Lemma smpl_prog_S_ver : smpl_prog S'. Proof. right. left. easy. Qed.
Lemma smpl_prog_T_ver : smpl_prog T'. Proof. right. right. easy. Qed.

Hint Resolve smpl_prog_H_ver smpl_prog_S_ver smpl_prog_T_ver : wfvt_db.


Lemma prog_smpl_inc_reduce : forall (p : nat -> prog) (prg_len bit : nat),
  smpl_prog p -> bit < prg_len ->
  translate_prog prg_len (p bit) = 
  (Matrix.I (2^bit)) ⊗ translate_prog 1 (p 0) ⊗ (Matrix.I (2^(prg_len - bit - 1))).
Proof. intros.    
       destruct H.
       - do 2 (rewrite H). 
         simpl.
         unfold prog_smpl_app, pad_u, pad.
         bdestruct_all; subst. 
         replace (1 - (0 + 1))%nat with 0 by lia.
         rewrite kron_1_l, kron_1_r; auto with wf_db.
         replace (prg_len - (bit + 1)) with (prg_len - bit - 1) by lia.
         apply f_equal_gen; easy.
       - destruct H.
         + do 2 (rewrite H). 
           simpl.
           unfold prog_smpl_app, pad_u, pad.
           bdestruct_all; subst. 
           replace (1 - (0 + 1))%nat with 0 by lia.
           rewrite kron_1_l, kron_1_r; auto with wf_db.
           replace (prg_len - (bit + 1)) with (prg_len - bit - 1) by lia.
           apply f_equal_gen; easy.
         + do 2 (rewrite H). 
           simpl.
           unfold prog_smpl_app, pad_u, pad.
           bdestruct_all; subst. 
           replace (1 - (0 + 1))%nat with 0 by lia.
           rewrite kron_1_l, kron_1_r; auto with wf_db.
           replace (prg_len - (bit + 1)) with (prg_len - bit - 1) by lia.
           apply f_equal_gen; easy.
Qed.


Lemma prog_ctrl_reduce : forall (prg_len ctrl targ : nat),
  translate_prog (s prg_len) (CNOT (s ctrl) (s targ)) = 
  (Matrix.I 2) ⊗ translate_prog prg_len (CNOT ctrl targ).
Proof. Admitted.

(*  intros.    
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
Qed. *)


(*
Lemma WF_helper : forall (l : list Pauli) (i : nat),
  WF_Matrix (nth i (map translate_P l) Zero).
Proof. intros. 
       destruct (nth_in_or_default i0 (map translate_P l) Zero).
       - apply in_map_iff in i1.
         destruct i1 as [x [H H0]].
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
*)


Lemma tensor_smpl_ground : forall (prg_len bit : nat) (p : nat -> prog)
                             (l : list Pauli) (a : Pauli) (c1 c2 : Coef),
    smpl_prog p -> bit < prg_len ->
    prg_len = length l -> 
    (p 0) :' @G 1 (p_1, [nth bit l gI]) → @G 1 (c2, [a])  ->
    (p bit) :'  @G prg_len (c1, l) → @G prg_len (cMul c1 c2, switch l a bit).
Proof. intros.
       apply Hsem_implies_Esem.
       apply Esem_implies_Hsem in H2; try easy.
       rewrite switch_inc; try (subst; easy).
       replace (c1, l) with (c1, (firstn bit l) ++ [nth bit l gI] ++ (skipn (S bit) l))
         by (rewrite <- nth_inc; subst; easy).
       rewrite prog_smpl_inc_reduce; auto.
       unfold translate; simpl in *.
       repeat rewrite map_app; simpl. 
       repeat rewrite big_kron_app. 
       simpl. 
       unfold translate in H2; simpl in H2.
       rewrite prog_smpl_inc_reduce in H2; auto.
       replace (1 - 0 - 1) with 0 in H2 by lia.
       rewrite Mscale_1_l, kron_1_l in H2; auto with wf_db.
       do 3 rewrite kron_1_r in H2.
       Admitted. 



(*
       repeat rewrite app_length.
       repeat rewrite map_length.
       rewrite firstn_length_le, skipn_length; try lia.
       do 4 rewrite Nat.pow_add_r.
       do 2 rewrite <- Mscale_kron_dist_r, <- Mscale_kron_dist_l. 
       rewrite prog_smpl_inc_reduce; auto.
       rewrite kron_assoc; auto with wf_db.
       replace (length l - bit - 1) with (length l - s bit) by lia. 
       repeat rewrite (kron_mixed_product' _ _ _ _ _ _ _ _ (2 ^ (length l))); 
         try (simpl; lia).         
       apply kron_simplify.
       rewrite Mmult_1_l, Mmult_1_r; try easy; try apply WF_helper2.
       all : try (apply firstn_length_le; lia).
       repeat rewrite (kron_mixed_product' _ _ _ _ _ _ _ _ ((2^1) * (2^(length l - s bit)))); 
         try (simpl; lia).  
       apply kron_simplify. simpl. 
       rewrite Mscale_mult_dist_r, (H1 _ (translate_coef c2 .* (translate_P a ⊗ Matrix.I 1))%M).
       rewrite Mscale_mult_dist_l, Mscale_assoc, <- translate_coef_cMul, Mscale_mult_dist_l; easy.
       all : try (left; try rewrite Mscale_1_l; easy).
       assert (H' := (WF_big_kron _ _ (map translate_P (skipn (s bit) l)))).
       rewrite map_length, skipn_length in H'; try lia. 
       rewrite Mmult_1_l, Mmult_1_r; try easy.
       all : try apply (H' Zero); intros. 
       all : try apply WF_helper.
       all : try (simpl length; do 2 rewrite <- Nat.pow_add_r; apply pow_components; lia).  
       apply unit_prog. 
       all : try (rewrite <- map_app; apply WF_helper). 
       rewrite <- (Nat.pow_1_r 2); apply unit_prog.
       simpl; split; apply (@univ_TType 1); apply WF_tt; easy. 
Qed.
 *)



Lemma tensor_ctrl_zero : forall (l : list Pauli) (prg_len targ : nat)
                           (a b : Pauli) (c1 c2 : Coef),
    targ < prg_len -> 0 <> targ -> 
    prg_len = length l -> 
    (CNOT 0 1) :' @G 2 (p_1, (nth 0 l gI) :: [nth targ l gI]) → @G 2 (c2, a :: [b])  ->
    (CNOT 0 targ) :'  @G prg_len (c1, l) → 
                         @G prg_len (cMul c1 c2, switch (switch l a 0) b targ).
Proof. Admitted. 

(*
intros. destruct targ; try easy.
       inversion H2; inversion H5; subst. 
       apply Arrow_pht; apply PHST; try apply G_cvt.
       destruct l; try easy.
       simpl in *. destruct H9; split; try easy.
       apply sgt_implies_sgt'; try easy. 
       apply sgt'_implies_sgt in H1; try easy. 
       unfold singGateType in *; intros; simpl in *.
       destruct H4; destruct H6; try easy. 
       rewrite <- H4, <- H6.
       unfold translate in *; simpl in *. 
       bdestruct (targ <? length l); try lia. 
       rewrite (nth_inc targ l gI); auto.
       repeat rewrite map_app.  
       rewrite <- (nth_inc targ l gI); auto.
       rewrite switch_inc; auto.
       repeat rewrite map_app.
       repeat rewrite big_kron_app; try (intros; apply WF_helper).
       repeat rewrite app_length.
       repeat rewrite map_length.
       rewrite firstn_length_le, skipn_length; try lia.
       do 4 rewrite Nat.pow_add_r.
       do 3 rewrite Nat.add_0_r, double_mult. 
       do 2 rewrite <- Mscale_kron_dist_l.
       unfold prog_ctrl_app; bdestruct_all; rewrite ite_conv.
       rewrite Nat.pow_0_r, mult_1_l, kron_1_l; auto with wf_db.
       repeat rewrite <- kron_assoc. 
       replace (length (cons (nth targ l gI) nil)) with 1 by easy. 
       replace (length (cons b nil)) with 1 by easy. 
       replace (s (length l) - s targ - 1) with (length l - s targ) by lia. 
       rewrite Nat.pow_1_r. 
       assert (H' : ((2 * 2^targ) * 2) = (2 * 2 ^ (S targ - 0))). 
       { rewrite <- (Nat.pow_1_r 2).
         repeat rewrite <- Nat.pow_add_r. 
         rewrite (Nat.pow_1_r 2).
         apply pow_components; try lia. } 
       rewrite H'. 
       assert (H'' : 2 * 2^(length l) = 
                   ((2 * 2^(s targ - 0))) * (2 ^ ((length l) - s targ))).
      { replace 2 with (2^1) by easy.
        repeat rewrite <- Nat.pow_add_r.
        apply pow_components; try lia. } 
      rewrite H''.
      do 2 rewrite (kron_mixed_product).
      rewrite Mmult_1_l, Mmult_1_r. 
      apply kron_simplify; try easy. 
      rewrite adj_ctrlX_is_cnot1 in H1.
      simpl; rewrite Nat.add_0_r, double_mult, Nat.sub_0_r, kron_1_r.
      rewrite Nat.add_0_r, double_mult.
      replace (2 * (2 * 2^targ)) with (2 * 2^targ * 2) by lia. 
      apply cnot_conv_inc; auto with wf_db.
      all : try (apply WF_helper2; apply firstn_length_le; lia).
      distribute_scale.
      rewrite (H1 _ (translate_coef c2 .* (translate_P a ⊗ (translate_P b ⊗ Matrix.I 1)))%M); 
        try left; try easy. 
      rewrite kron_1_r, Mscale_mult_dist_l, Mscale_assoc, translate_coef_cMul.
      distribute_scale; easy.
      rewrite kron_1_r, Mscale_1_l; easy. 
      all : try apply WF_kron; try lia. 
      all : try (apply WF_helper2); try easy. 
      all : try apply skipn_length.
      all : try apply WF_kron; try lia; auto with wf_db. 
      all : try (apply firstn_length_le; lia).
      all : intros; try (rewrite <- map_app; apply WF_helper). 
      rewrite adj_ctrlX_is_cnot1; auto with unit_db.
      simpl; split; apply (@univ_TType 2); apply WF_tt; easy. 
Qed.
*)

Lemma tensor_targ_zero : forall (l : list Pauli) (prg_len ctrl : nat)
                             (a b : Pauli) (c1 c2 : Coef),
    ctrl < prg_len -> ctrl <> 0 -> 
    prg_len = length l -> 
    (CNOT 0 1) :' @G 2 (p_1, (nth ctrl l gI) :: [nth 0 l gI]) → @G 2 (c2, a :: [b])  ->
    (CNOT ctrl 0) :'  @G prg_len (c1, l) → 
                         @G prg_len (cMul c1 c2, switch (switch l a ctrl) b 0).
Proof. Admitted. 


(* 
intros. destruct ctrl; try easy.
       inversion H2; inversion H5; subst. 
       apply Arrow_pht; apply PHST; try apply G_cvt.
       destruct l; try easy.
       simpl in *. destruct H9; split; try easy.
       apply sgt_implies_sgt'; try easy. 
       apply sgt'_implies_sgt in H1; try easy. 
       unfold singGateType in *; intros; simpl in *.
       destruct H4; destruct H6; try easy. 
       rewrite <- H4, <- H6.
       unfold translate in *; simpl in *. 
       bdestruct (ctrl <? length l); try lia. 
       rewrite (nth_inc ctrl l gI); auto.
       repeat rewrite map_app.  
       rewrite <- (nth_inc ctrl l gI); auto.
       rewrite switch_inc; auto.
       repeat rewrite map_app.
       repeat rewrite big_kron_app; try (intros; apply WF_helper).
       repeat rewrite app_length.
       repeat rewrite map_length.
       rewrite firstn_length_le, skipn_length; try lia.
       do 4 rewrite Nat.pow_add_r.
       do 3 rewrite Nat.add_0_r, double_mult. 
       do 2 rewrite <- Mscale_kron_dist_l.
       unfold prog_ctrl_app; bdestruct_all; rewrite ite_conv.
       rewrite Nat.pow_0_r, mult_1_l, kron_1_l; auto with wf_db.
       repeat rewrite <- kron_assoc. 
       replace (length (cons (nth ctrl l gI) nil)) with 1 by easy. 
       replace (length (cons b nil)) with 1 by easy. 
       replace (s (length l) - s ctrl - 1) with (length l - s ctrl) by lia. 
       rewrite Nat.pow_1_r. 
       assert (H' : ((2 * 2^ctrl) * 2) = (2 * 2 ^ (S ctrl - 0))). 
       { rewrite <- (Nat.pow_1_r 2).
         repeat rewrite <- Nat.pow_add_r.
         rewrite (Nat.pow_1_r 2).
         apply pow_components; try lia. } 
       rewrite H'. 
       assert (H'' : 2 * 2^(length l) = 
                   ((2 * 2^(s ctrl - 0))) * (2 ^ ((length l) - s ctrl))).
      { replace 2 with (2^1) by easy.
        repeat rewrite <- Nat.pow_add_r.
        apply pow_components; try lia. } 
      rewrite H''.
      rewrite (mult_comm 2 _).
      do 2 rewrite (kron_mixed_product).
      rewrite Mmult_1_l, Mmult_1_r. 
      apply kron_simplify; try easy. 
      rewrite adj_ctrlX_is_cnot1 in H1.
      simpl; rewrite Nat.add_0_r, double_mult, Nat.sub_0_r, kron_1_r.
      rewrite Nat.add_0_r, double_mult.
      replace (2 * (2 * 2^ctrl)) with (2 * 2^ctrl * 2) by lia. 
      apply notc_conv_inc; auto with wf_db.
      all : try (apply WF_helper2; apply firstn_length_le; lia).
      distribute_scale.
      rewrite (H1 _ (translate_coef c2 .* (translate_P a ⊗ (translate_P b ⊗ Matrix.I 1)))%M); 
        try left; try easy. 
      rewrite kron_1_r, kron_1_r, Mscale_mult_dist_l, Mscale_assoc, translate_coef_cMul.
      distribute_scale; easy.
      rewrite kron_1_r, Mscale_1_l; easy. 
      all : try apply WF_kron; try lia. 
      all : try (apply WF_helper2); try easy. 
      all : try apply skipn_length.
      all : try apply WF_kron; try lia; auto with wf_db. 
      all : try (apply firstn_length_le; lia).
      all : intros; try (rewrite <- map_app; apply WF_helper). 
      rewrite adj_ctrlX_is_cnot1; auto with unit_db.
      simpl; split; apply (@univ_TType 2); apply WF_tt; easy. 
Qed.
*)

Lemma tensor_ctrl_reduce : forall (l1 l2 : list Pauli) (prg_len ctrl targ : nat)
                             (a : Pauli) (c1 c2 : Coef),
  prg_len = length l1 -> prg_len = length l2 -> 
  (CNOT ctrl targ) :' @G prg_len (c1, l1) → @G prg_len (c2, l2)  ->
  (CNOT (s ctrl) (s targ)) :' @G (s prg_len) (c1, a :: l1) → @G (s prg_len) (c2, a :: l2).
Proof. intros. Admitted. 
(*
       inversion H1; inversion H4; subst. 
       apply Arrow_pht; apply PHST; try apply G_cvt.
       rewrite prog_ctrl_reduce.
       simpl in *. destruct H8; split; try easy.
       apply sgt_implies_sgt'; try easy. 
       apply sgt'_implies_sgt in H; try easy. 
       unfold singGateType in *; intros; simpl in *.
       destruct H3; destruct H5; try easy. 
       rewrite <- H3, <- H5.
       unfold translate in *; simpl in *. 
       do 2 rewrite map_length, Nat.add_0_r, double_mult, <- Mscale_kron_dist_r.
       rewrite <- H0.
       do 2 rewrite kron_mixed_product. 
       rewrite (H _ (translate_coef c2 .* (⨂ map translate_P l2))%M);
         try (left; easy). 
       rewrite Mmult_1_r, Mmult_1_l; auto with wf_db.
       apply unit_prog_ctrl_app; auto with unit_db.
       simpl; split; apply (@univ_TType (length l1)); apply WF_tt; easy. 
Qed. *)


Lemma tensor_ctrl_ground : forall (l : list Pauli) (prg_len ctrl targ : nat)
                             (a b : Pauli) (c1 c2 : Coef),
    ctrl < prg_len -> targ < prg_len -> ctrl <> targ -> 
    prg_len = length l -> 
    (CNOT 0 1) :' @G 2 (p_1, (nth ctrl l gI) :: [nth targ l gI]) → @G 2 (c2, a :: [b])  ->
    (CNOT ctrl targ) :'  @G prg_len (c1, l) → 
                         @G prg_len (cMul c1 c2, switch (switch l a ctrl) b targ).
Proof. induction l.  
       - intros; subst; simpl in *; lia. 
       - intros. 
         destruct ctrl; try (apply tensor_ctrl_zero; auto).
         destruct targ; try (apply tensor_targ_zero; auto). 
         subst; simpl in *. 
         apply tensor_ctrl_reduce; auto. 
         do 2 rewrite switch_len; easy. 
         apply IHl; auto; lia.  
Qed.


(****************)
(* tensor rules *)
(****************)


Definition nth_vType {n} (bit : nat) (A : vType n) : vType 1 :=
  match A with 
  | G g => G (p_1, [nth bit (snd g) gI])         
  | _ => Errv
  end. 


Definition switch_vType {n} (A : vType n) (a : vType 1) (bit : nat) : vType n :=
  match A with 
  | G g =>
    match a with
    | G g0 => G (cMul (fst g) (fst g0), switch (snd g) (hd gI (snd g0))  bit)
    | _ => Errv
    end
  | _ => Errv
  end.



Lemma WFS_nth_vType : forall {n} (A : vType n) (bit : nat),
  WFS_vType A -> WFS_vType (nth_vType bit A).
Proof. intros.
       inversion H; subst. 
       destruct A; try easy.
       apply WFS.
       apply G_svt.
       apply WF_G; apply WF_tt.
       easy. 
Qed.       


Lemma WFS_switch_vType : forall {n} (A : vType n) (a : vType 1) (bit : nat),
  WFS_vType A -> WFS_vType a -> WFS_vType (switch_vType A a bit).
Proof. intros.
       inversion H; inversion H0; subst. 
       destruct A; destruct a; try easy.
       apply WFS.
       apply G_svt.
       apply WF_G; apply WF_tt.
       simpl. rewrite switch_len.
       inversion H2; inversion H6; 
       easy. 
Qed.       


Hint Resolve WFS_nth_vType WFS_switch_vType : wfvt_db.



Lemma tensor_smpl : forall (prg_len bit : nat) (p : nat -> prog)
                           (A : vType prg_len) (a : vType 1),
    WFS_vType A -> WFS_vType a -> 
    smpl_prog p -> bit < prg_len ->
    (p 0) :' (nth_vType bit A) → a ->
    (p bit) :'  A → (switch_vType A a bit).
Proof. intros.
       inversion H; inversion H0; subst.
       inversion H4; inversion H7; subst.
       destruct tt; destruct tt0; simpl. 
       inversion H5; inversion H9; subst.
       apply tensor_smpl_ground; auto.
       simpl in *.
       inversion H8; inversion H10; subst.
       do 2 (destruct l0; try easy).       
Qed.



Lemma tensor_ctrl : forall (prg_len ctrl targ : nat)   
                           (A : vType prg_len) (a b : vType 1),
  WFS_vType A -> WFS_vType a -> WFS_vType b -> 
  ctrl < prg_len -> targ < prg_len -> ctrl <> targ -> 
  (CNOT 0 1) :' (nth_vType ctrl A) .⊗ (nth_vType targ A) → a .⊗ b ->
  (CNOT ctrl targ) :'  A → switch_vType (switch_vType A a ctrl) b targ.
Proof. intros. 
       inversion H; inversion H0; inversion H1; subst.
       inversion H6; inversion H9; inversion H12; subst; try easy. 
       destruct tt; destruct tt0; destruct tt1; simpl. 
       inversion H7; inversion H10; inversion H13; subst. 
       inversion H11; inversion H15; inversion H17; simpl in *; subst. 
       rewrite cMul_assoc.
       apply tensor_ctrl_ground; auto; simpl in *.
       rewrite H16, H19 in H5; simpl in H5.
       do 2 (destruct l0; destruct l1; try easy).
Qed.


(***************)
(* Arrow rules *)
(***************)


Lemma arrow_mul : forall {n} g (A A' B B' : vType n),
    WFS_vType A -> WFS_vType A' ->
    WFS_vType B -> WFS_vType B' ->
    g :' A → A' ->
    g :' B → B' ->
    g :' A .* B → A' .* B'.
Proof. intros; simpl in *.       
       inversion H; inversion H0; inversion H1; inversion H2;  
       inversion H5; inversion H8; inversion H11; inversion H14; subst; simpl in *.
       apply Hsem_implies_Esem.
       inversion H6; inversion H9; inversion H12; inversion H15; subst.
       inversion H10; inversion H16; inversion H18; inversion H20.
       repeat rewrite translate_Mmult; try easy.
       apply Esem_implies_Hsem in H3; auto.
       apply Esem_implies_Hsem in H4; auto.
       rewrite Mmult_assoc, <- H4, <- Mmult_assoc, H3, Mmult_assoc; easy.
Qed. 
  

Lemma mul_simp : forall (a b : Pauli),
  @G 1 (gMul_Coef a b, [gMul_base a b]) = @G 1 (p_1, [a]) .* @G 1 (p_1, [b]). 
Proof. intros. 
       simpl. 
       destruct a; destruct b; try easy. 
Qed.


Lemma arrow_mul_1 : forall g (a a' b b' : Pauli),
    g :' @G 1 (p_1, [a]) → @G 1 (p_1, [a']) ->
    g :' @G 1 (p_1, [b]) → @G 1 (p_1, [b']) ->
    g :' @G 1 (gMul_Coef a b, [gMul_base a b]) → @G 1 (gMul_Coef a' b', [gMul_base a' b']).
Proof. intros. 
       do 2 rewrite mul_simp. 
       apply arrow_mul; try easy; apply WFS; try apply G_svt. 
       all : apply WF_G; apply WF_tt; easy. 
Qed.



Lemma arrow_scale : forall {n} (p : prog) (A A' : vType n) (c : Coef),
  p :' A → A' -> p :' (scale c A) → (scale c A').
Proof. intros. 
       inversion H; inversion H2; subst.
       apply Cap_vt_conv in H4; apply Cap_vt_conv in H5.
       apply Arrow_pht; apply PHST; auto with wfvt_db. 
       all : try (apply Cap_vt_conv; rewrite Cap_vt_scale; easy).
       rewrite fgt_conv in *.
       do 2 (rewrite translate_vecType_scale).
       apply Heisenberg.arrow_scale; try easy.
       apply translate_coef_nonzero.
Qed.


Lemma arrow_i : forall {n} (p : prog) (A A' : vType n),
  p :' A → A' ->
  p :' i A → i A'.
Proof. intros;
       apply arrow_scale;
       assumption.
Qed.


Lemma arrow_neg : forall {n} (p : prog) (A A' : vType n),
  p :' A → A' ->
  p :' -A → -A'.
Proof. intros;
       apply arrow_scale;
       assumption.
Qed.



Hint Resolve HTypes STypes TTypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l cap_elim_r : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.



(* basically just eq_type_conv_output but with different order hypotheses *)
Lemma eq_arrow_r : forall {n} (g : prog) (A B B' : vType n),
    g :' A → B ->
    B = B' ->
    g :' A → B'.
Proof. intros. subst; easy. Qed.

(* Tactics *)


Ltac is_I A :=
  match A with
  | I => idtac 
  end.

Ltac is_prog1 A :=
 match A with 
  | H' _ => idtac
  | S' _ => idtac
  | T' _ => idtac
  end.
              
Ltac is_prog2 A :=
  match A with
  | CNOT _ _ => idtac
  end.



Ltac expand_prog := match goal with
                    | |- ?p1 ;; ?p2 :' ?T => eapply SeqTypes
                    end.

(* Reduces to sequence of H, S and CNOT *)


Ltac  solve_smpl := apply tensor_smpl;
                    try (solve [eauto with base_types_db]); auto with wfvt_db.


Ltac  solve_ctrl := apply tensor_ctrl;
                    try (solve [eauto with base_types_db]); auto with wfvt_db.


Lemma CZTypes : CZ 0 1 :' (X .⊗ I → X .⊗ Z) ∩ (I .⊗ X → Z .⊗ X) ∩
                          (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → I .⊗ Z).
Proof. repeat apply cap_intro;
         repeat expand_prog.
       solve_smpl.
       solve_ctrl.
       eapply eq_arrow_r.
       solve_smpl.
       easy. 
       simpl.
       
       apply tensor_smpl; auto with wfvt_db.
       2 : solve [eauto with base_types_db].
       auto with wfvt_db.
       solve [eauto with base_types_db].
       eapply eq_arrow_r.
       apply tensor_smpl; auto with wfvt_db.
       2 : solve [eauto with base_types_db].
       auto with wfvt_db.
       easy. 
       apply tensor_smpl; auto with wfvt_db.
       2 : solve [eauto with base_types_db].
       auto with wfvt_db.

       


apply 
       




       rewrite (decompose_tensor) by (auto 50 with wfvt_db).
       eapply eq_arrow_r.
       apply arrow_mul.

       apply tensor_ctrl_base.
       solve [eauto with base_types_db].
       
Qed.



Ltac type_check_base :=
  repeat apply cap_intro;
  repeat expand_prog; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply 4tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end; auto with wfvt_db; try easy.



Opaque progHasType.


Lemma CZTypes : CZ 0 1 :' (X .⊗ I → X .⊗ Z) ∩ (I .⊗ X → Z .⊗ X) ∩
                          (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → I .⊗ Z).
Proof. type_check_base.   
Qed.



Notation bell00 := ((H' 2);; (CNOT 2 3)).

Notation encode := ((CZ 0 2);; (CNOT 1 2)).

Notation decode := ((CNOT 2 3);; (H' 2)).

Notation superdense := (bell00;; encode;; decode).



Lemma superdenseTypesQPL : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base.
       type_check_base.
       type_check_base. 
       simpl. compute.
       rewrite mul_tensor_dist; auto with wfvt_db.
       type_check_base.
       type_check_base.
       type_check_base.
       type_check_base.
       type_check_base.
Qed.


       rewrite mul_tensor_dist; auto with wfvt_db.



match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.
6 : match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.


6 : match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.
       type_check_base. easy. 
       6 : {  rewrite mul_tensor_dist; auto with wfvt_db.
               rewrite mul_tensor_dist; auto with wfvt_db.
match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => idtac 4
                                           end.


rewrite decompose_tensor_mult_r.
             apply arrow_mul; type_check_base.
       3 : {


match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) -> _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) -> _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

       3 : {

         match goal with
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         end; auto with wfvt_db; try easy.


       type_check_base'.       
       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.
       kill_switch2.


       repeat (repeat (rewrite switch_vType_inc; auto with gt_db); 
         try rewrite switch_vType_base; try rewrite switch_vType_base_one;
           auto with gt_db).





       
       kill_

       
       type_check_base'.
       type_check_base'.
       


apply evSuper_ev; auto 50 with wfvt_db.
       unfold eq_vType; simpl.
       apply hd_inj; unfold uncurry; simpl. 
       apply TType_compare; auto; simpl.
       repeat (split; try lma').
       unfold translate






       

Check hd_inj.

       repeat (apply wfs_switch_vType'; auto 50 with wfvt_db).
       apply wfs_switch_vType'; auto 50 with wfvt_db.
       apply wfs_switch_vType'; auto with wfvt_db.


3 : {
         unfold eq_vType. simpl. 
         unfold translate. simpl. 
         unfold translate_vecType


       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.      
       type_check_base'.
       type_check_base'.
       type_check_base'.

rewrite mul_tensor_dist; auto with wfvt_db.
             easy. 

type_check_base'.
       type_check_base'.
       3 : { rewrite mul_compat.
              try rewrite mul_tensor_dist;
              try easy; auto with wfvt_db.


pushA. 
       all : auto with gt_db.
       type_check_base'.
       type_check_base'.
       all : try pushA. 
       all : try pushA. 
       
        3 :  { pushA. 
               3 : pushA.
               all : auto with wfvt_db. }
        all : auto with gt_db.
        type_check_base'.
        3 : { pushA rewrite mul_compat;
             try rewrite mul_tensor_dist;
             try easy; auto with wfvt_db. 
              3 : { rewrite mul_compat;
                    try rewrite mul_tensor_dist;
                    try easy; auto with wfvt_db. 
                    3 : rewrite mul_compat;
                      try rewrite mul_tensor_dist;
                      try easy; auto with wfvt_db. 
                    all : auto with wfvt_db. }
              all : auto with wfvt_db. }
        all : auto with gt_db.
        type_check_base'.
        unfold eq_vType.
        simpl switch_vType'.
        unfold translate. simpl.
        apply hd_inj.
        crunch_matrix.
try easy.

       type_check_base'.

       2 : { simp_switch.


rewrite nth_vswitch_hit. try easy; try lia; auto with gt_db).
  repeat (rewrite nth_vswitch_miss; try easy; try lia; auto with gt_db). 

match goal with
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?n) → _ => 
                rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db 
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?m) → _ => 
                rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db
end.
match goal with
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?n) → _ => 
                rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db 
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?m) → _ => 
                rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db
end.



nth_vType bit (switch_vType' A a bit) = a.


       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗



       econstructor; reflexivity.


       rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db.
       rewrite nth_vswitch_hit; [| nia | | |]. try easy; try nia; auto with gt_db. 
       


rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db. 


       simpl nth_vType.
       apply arrow_mul_1.
       solve [eauto with base_types_db].  
       solve [eauto with base_types_db].
       eapply tensor_ctrl. 
       simpl nth_vType. 
       type_check_base'.

       2 : { simp_switch.


solve [eauto with base_types_db].  type_check_base'. }
       all : try type_check_base'
 try rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db; 
         try rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
       2 : { type_check_base'. }
       type_check_base'.

       type_check_base'.


       3 : {  rewrite mul_tensor_dist. easy. 


       type_check_base.

       simpl nth_vType. 
       assert (H : G 1 (p_1, [gMul gX gZ]) = X .* Z). 
       { easy. }
       rewrite H.
       type_check_base.
       eapply tensor_ctrl.
       apply prog_decompose_tensor; auto with wfvt_db.
       eapply eq_arrow_r.
       apply arrow_mul; auto with wfvt_db; try solve [eauto with base_types_db].
       5 : { simpl nth_vType.

       type_check_base.

repeat match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; auto with wfvt_db.





       match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.
match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.



match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; auto with wfvt_db.
 

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end;

try match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; 

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.  easy.
 

match goal with
         | |- Sing_vt _       => tryif is_evar A then fail else auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.

        type_check_base.


Lemma superdenseTypesQPL' : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base'.
       
       eapply tensor_ctrl'; try (apply prog_decompose_tensor); try easy;
         try (eapply eq_arrow_r; apply arrow_mul; try (solve [eauto with base_types_db])).
       
       3: { eapply eq_arrow_r. apply arrow_mul; try (solve [eauto with base_types_db]);
                                 try (auto with wfvt_db).
         rewrite mul_tensor_dist; 
         auto with wfvt_db; easy. }
         auto with gt_db.
       auto with gt_db.
         
         eapply tensor_smpl.
         simpl. easy.
         auto with wfvt_db.
         rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db. 
         rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
         eapply eq_arrow_r.
         apply arrow_mul; try (solve [eauto with base_types_db]); try (auto with wfvt_db).
         easy. 
         solve [eauto with base_types_db].
         9: { solve [eauto with base_types_db]. }

Lemma superdenseTypesQPL' : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base'.
       
       eapply tensor_ctrl'; try (apply prog_decompose_tensor); try easy;
         try (eapply eq_arrow_r; apply arrow_mul; try (solve [eauto with base_types_db])).
       
       3: { eapply eq_arrow_r. apply arrow_mul; try (solve [eauto with base_types_db]);
                                 try (auto with wfvt_db).
         rewrite mul_tensor_dist; 
         auto with wfvt_db; easy. }
         auto with gt_db.
       auto with gt_db.
         
         eapply tensor_smpl.
         simpl. easy.
         auto with wfvt_db.
         rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db. 
         rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
         eapply eq_arrow_r.
         apply arrow_mul; try (solve [eauto with base_types_db]); try (auto with wfvt_db).
         easy. 
         solve [eauto with base_types_db].
         9: { solve [eauto with base_types_db]. }


       
  repeat expand_prog.
  repeat match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => eapply (tensor_smpl (S n) _ _ _)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.
  eapply (tensor_ctrl 2 3 _ _ _). 
 match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => idtac 4
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.








repeat apply cap_intro;
  repeat expand_prog; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => eapply (tensor_smpl (S n) _ _ _)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.


repeat match goal with
              | |- ?p1 ;; ?p2 :' ?T => eapply SeqTypes
              end.
       eapply (tensor_smpl 2 _ _ _).
       solve [eauto with base_types_db]. 
       eapply (tensor_ctrl 4 2 3 _ _ _).
       simpl nth_vType.
       apply prog_decompose_tensor; try easy.
       eapply eq_arrow_r.
       apply arrow_mul; 
         try (solve [eauto with base_types_db]);
         try easy.
       rewrite mul_tensor_dist; try easy.
       eapply (tensor_ctrl 2 _ _ _).
       simpl. 
       solve [eauto with base_types_db]. 



reflexivity. 
try easy.
       5: { solve [eauto with base_types_db]. }
       5: { solve [eauto with base_types_db]. }
       



    auto with univ_db.
       auto with univ_db.
       nia. 
       easy. 
       eapply (tensor_ctrl 4 2 3 _ _ _).
       rewrite CX_is_CNOT.
       rewrite decompose_tensor.
       eapply eq_arrow_r.
       apply arrow_mul.
       auto with sing_db.
       auto with sing_db.
       auto with unit_db.
       auto with univ_db.
       4: { solve [eauto with base_types_db]. }
       auto with univ_db.
       auto with univ_db.



emma prog_decompose_tensor : forall (p : prog) (A B : vType 1) (T : vType 2),
  Sing_vt A -> WF_vType A ->
  Sing_vt B -> WF_vType B ->
  p :' ((A .⊗ I) .* (I .⊗ B)) → T -> p :' (A .⊗ B) → T.
Proof. intros. 
       apply (eq_type_conv_input p ((A .⊗ I) .* (I .⊗ B)) (A .⊗ B) T); try easy.
       rewrite <- decompose_tensor; easy.
Qed.


       
       rewrite decompose_tensor.
       eapply eq_arrow_r.
       apply arrow_mul.
       auto with sing_db.
       auto with sing_db.
       auto with unit_db.
       auto with univ_db.



       assert (H : G 1 (p_1, [gX]) = X). { easy. }
       assert (H' : G 1 (p_1, [gZ]) = Z). { easy. }
       rewrite H, H'.
                                         

solve [eauto with base_types_db]. }
       auto with univ_db.
       auto with univ_db.
       2: { solve [eauto with base_types_db]. }
       auto with univ_db.
       rewrite mul_tensor_dist.
       reflexivity.
       auto with sing_db.
       auto with sing_db.
       auto with sing_db.
       auto with sing_db.
       eapply (tensor_ctrl 4 0 2 _ _ _).
       rewrite decompose_tensor.
       eapply eq_arrow_r.


Ltac is_I A :=
  match A with


Definition vecTypeT (len : nat) := (list (vecType 2)).

| tensor : GType -> GType -> GType
| cap : GType -> GType -> GType
| arrow : GType -> GType -> GType. 

Notation "- T" := (neg T).
Infix ".*" := mul (at level 40, left associativity).
Infix ".⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X .* Z)).


Fixpoint singGType (g : GType) := 
  match g with
  | I => 
  | X => 
  | Z => 
  | i g => 
  | neg g => 
  | mul g1 g2 => 
  | tensor g1 g2 =>
  | 



Fixpoint translate (g : GType) :=
  match g with
  | gI => I''
  | gX => X''
  | gZ => Z''
  | gmul g1 g2 => mulT' (translate g1) (translate g2)
  | gtensor g1 g2 => tensorT (translate g1) (translate g2)
  | gi g => scaleT Ci (translate g)
  | gneg g => scaleT (Copp C1) (translate g)
  | _ => I''
  end. 



Parameter GType : Type.
Parameter I : GType.
Parameter X : GType.
Parameter Z : GType.
Parameter i : GType -> GType.
Parameter neg : GType -> GType.
Parameter mul : GType -> GType -> GType.
Parameter tensor : GType -> GType -> GType.
Parameter cap : GType -> GType -> GType.
Parameter arrow : GType -> GType -> GType.


(*
Parameter toGType : Matrix 2 2 -> GType.
Axiom ItoG : toGType (Matrix.I 2) = I.
Axiom XtoG : toGType σx  = X.
Axiom ZtoG : toGType σz  = Z.
*)


Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
Infix "⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X * Z)).

(* Singleton Types *)
(* Could probably safely make this inductive. Can't do inversion on GTypes anyhow. *)

Parameter Singleton : GType -> Prop.
Axiom SI: Singleton I.
Axiom SX : Singleton X.
Axiom SZ : Singleton Z.
Axiom S_neg : forall A, Singleton A -> Singleton (neg A).
Axiom S_i : forall A, Singleton A -> Singleton (i A).
Axiom S_mul : forall A B, Singleton A -> Singleton B -> Singleton (A * B).

Hint Resolve SI SX SZ S_neg S_i S_mul : sing_db.

Lemma SY : Singleton Y.
Proof. auto with sing_db. Qed.

(* Multiplication laws *)

Axiom mul_assoc : forall A B C, A * (B * C) = A * B * C.
Axiom mul_I_l : forall A, I * A = A.
Axiom mul_I_r : forall A, A * I = A.
Axiom Xsqr : X * X = I.
Axiom Zsqr : Z * Z = I.
Axiom ZmulX : Z * X = - (X * Z).

Axiom neg_inv : forall A, - - A = A.
Axiom neg_dist_l : forall A B, -A * B = - (A * B).
Axiom neg_dist_r : forall A B, A * -B = - (A * B).

Axiom i_sqr : forall A, i (i A) = -A.
Axiom i_dist_l : forall A B, i A * B = i (A * B).
Axiom i_dist_r : forall A B, A * i B = i (A * B).

Axiom i_neg_comm : forall A, i (-A) = -i A.

Hint Rewrite mul_I_l mul_I_r Xsqr Zsqr ZmulX neg_inv neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.

(** ** Tensor Laws *)

Axiom tensor_assoc : forall A B C, A ⊗ (B ⊗ C) = (A ⊗ B) ⊗ C.  

Axiom neg_tensor_dist_l : forall A B, -A ⊗ B = - (A ⊗ B).
Axiom neg_tensor_dist_r : forall A B, A ⊗ -B = - (A ⊗ B).
Axiom i_tensor_dist_l : forall A B, i A ⊗ B = i (A ⊗ B).
Axiom i_tensor_dist_r : forall A B, A ⊗ i B = i (A ⊗ B).

(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Axiom mul_tensor_dist : forall A B C D,
    Singleton A ->
    Singleton C ->
    (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D).

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗ B = (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall A B,
    Singleton A ->
    Singleton B ->
    (A * B) ⊗ I = (A ⊗ I) * (B ⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall A B,
    I ⊗ (A * B) = (I ⊗ A) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.
  
Hint Rewrite neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.

(** ** Intersection Laws *)

Axiom cap_idem : forall A, A ∩ A = A.

Axiom cap_comm : forall A B, A ∩ B = B ∩ A.

Axiom cap_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.

Axiom cap_I_l : forall A,
  Singleton A ->
  I ∩ A = A.

Lemma cap_I_r : forall A,
  Singleton A ->
  A ∩ I = A.
Proof. intros; rewrite cap_comm, cap_I_l; easy. Qed.


(* Note: I haven't proven that this works or terminates.
   An anticommutative monoidal solver would be ideal here. *)
Ltac normalize_mul :=
  repeat match goal with
  | |- context[(?A ⊗ ?B) ⊗ ?C] => rewrite <- (tensor_assoc A B C)
  end;
  repeat (rewrite mul_tensor_dist by auto with sing_db);
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc X Z _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc ).



Lemma Ysqr : Y * Y = I. Proof. 
autorewrite with mul_db.
try rewrite mul_assoc.
try rewrite <- (mul_assoc X Z _).
autorewrite with mul_db.
try rewrite mul_assoc.
try rewrite <- (mul_assoc X Z _).
autorewrite with mul_db.

  reflexivity. Qed.
Lemma XmulZ : X * Z = - Z * X. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulY : X * Y = i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulX : Y * X = -i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma ZmulY : Z * Y = -i X. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulZ : Y * Z = i X. Proof. normalize_mul. reflexivity. Qed.



Fixpoint zipWith {X : Type} (f : X -> X -> X) (As Bs : list X) : list X :=
  match As with 
  | [] => Bs
  | a :: As' => 
    match Bs with
    | [] => As
    | b :: Bs' => f a b :: zipWith f As' Bs'
    end
  end.  


Lemma zipWith_len_pres : forall {X : Type} (f : X -> X -> X) (n : nat) 
                                (As : list X) (Bs : list X),
  length As = n -> length Bs = n -> length (zipWith f As Bs) = n.
Proof. induction n as [| n'].
       - intros. 
         destruct As; destruct Bs; easy. 
       - intros. 
         destruct As; destruct Bs; try easy.
         simpl in *.
         apply Nat.succ_inj in H; apply Nat.succ_inj in H0.
         rewrite IHn'; easy. 
Qed.


Lemma zipWith_app_product : forall {X : Type} (f : X -> X -> X) (n : nat) 
                               (l0s l2s : list X) (l1s l3s : list X),
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
