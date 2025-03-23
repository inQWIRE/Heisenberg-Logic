Require Export OrdersFacts.
Require Export Mergesort.
Require Export HeisenbergFoundations.Predicates.


Module PauliOrdering <: UsualOrderedTypeFull'.
Definition t := Pauli.
Definition eq := @eq t.
Definition eq_equiv : Equivalence eq := eq_equivalence.

Definition eqb (a b : t) : bool :=
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

Definition lt (p1 p2 : t) := 
  match p1 with
  | gI => match p2 with
         | gI => False
         | gZ => False
         | gY => False
         | gX => False
         end
  | gZ => match p2 with
         | gI => True
         | gZ => False
         | gY => False
         | gX => False
         end
  | gY => match p2 with
         | gI => True
         | gZ => True
         | gY => False
         | gX => False
         end
  | gX => match p2 with
         | gI => True
         | gZ => True
         | gY => True
         | gX => False
         end
  end.
Lemma lt_strorder : StrictOrder lt.
Proof. constructor. 
  - unfold Irreflexive, Reflexive, complement.
    intro x; destruct x; simpl; auto.
  - unfold Transitive.
    intros x y z; destruct x, y, z; simpl; auto.
Qed.
Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt. Proof. constructor; subst; auto. Qed.
Definition compare (p1 p2 : t) : comparison := 
  match p1 with
  | gI => match p2 with
         | gI => Eq
         | gZ => Gt
         | gY => Gt
         | gX => Gt
         end
  | gZ => match p2 with
         | gI => Lt
         | gZ => Eq
         | gY => Gt
         | gX => Gt
         end
  | gY => match p2 with
         | gI => Lt
         | gZ => Lt
         | gY => Eq
         | gX => Gt
         end
  | gX => match p2 with
         | gI => Lt
         | gZ => Lt
         | gY => Lt
         | gX => Eq
         end
  end.
Lemma compare_spec :
  forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Proof. intros x y; destruct x, y;
    try (apply CompEq; simpl; easy);
    try (apply CompLt; simpl; easy);
    try (apply CompGt; simpl; easy).
Qed.
Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
Proof. destruct x, y;
    try (left; reflexivity); 
    try (right; intro; discriminate).
Qed.
Definition le (p1 p2 : t) := 
  match p1 with
  | gI => match p2 with
         | gI => True
         | gZ => False
         | gY => False
         | gX => False
         end
  | gZ => match p2 with
         | gI => True
         | gZ => True
         | gY => False
         | gX => False
         end
  | gY => match p2 with
         | gI => True
         | gZ => True
         | gY => True
         | gX => False
         end
  | gX => match p2 with
         | gI => True
         | gZ => True
         | gY => True
         | gX => True
         end
  end.
Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ x = y.
Proof. intros x y. split; intros;
    destruct x, y; simpl in *;
    try contradiction;
    try (left; easy);
    try (right; easy);
    auto; destruct H;
    try discriminate;
    try contradiction.
Qed.

Definition leb (p1 p2 : t) := 
  match p1 with
  | gI => match p2 with
         | gI => true
         | gZ => false
         | gY => false
         | gX => false
         end
  | gZ => match p2 with
         | gI => true
         | gZ => true
         | gY => false
         | gX => false
         end
  | gY => match p2 with
         | gI => true
         | gZ => true
         | gY => true
         | gX => false
         end
  | gX => match p2 with
         | gI => true
         | gZ => true
         | gY => true
         | gX => true
         end
  end.
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y. destruct x, y; simpl; auto. Qed.  
Lemma leb_trans : Transitive (fun x y => leb x y = true).
Proof. intros x y z H0 H1. destruct x, y, z; simpl; auto. Qed.  

End PauliOrdering.

Module POrd := PauliOrdering <+ OrderedTypeFullFacts(PauliOrdering) <+ Sort(PauliOrdering).




Module TTypeOrdering <: OrderedTypeFull'.

Definition t : Type := C * (list Pauli).
Definition eq (x y : t) := (eq (snd x) (snd y)).
Lemma eq_equiv : Equivalence eq.
Proof. repeat constructor.
  - unfold Symmetric, eq.
    intros x y H; destruct x, y; simpl in *; auto.
  - unfold Transitive, eq.
    intros x y z H H0; destruct x, y, z; simpl in *.
    apply eq_trans with (y := l0); auto.
Qed.

Fixpoint lt_listP (l1 l2 : list Pauli) :=
  match l1 with
  | [] => match l2 with
         | [] => False
         | _ :: _ => True
         end
  | h1 :: t1 => match l2 with
              | [] => False
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => True
                  | Eq => lt_listP t1 t2
                  | Gt => False
                  end
              end
  end.

Lemma lt_listP_nil_r : forall (l : list Pauli), lt_listP l [] = False.
Proof. intros l. destruct l; auto. Qed. 

Definition lt (x y : t) := lt_listP (snd x) (snd y).
Lemma lt_strorder : StrictOrder lt.
Proof. constructor.
  - unfold Irreflexive, Reflexive, complement, lt in *.
    intros x H. destruct x. simpl in *.
    induction l; simpl in *; auto.
    destruct a; simpl in *; auto.
  - unfold Transitive, lt in *.
    intros x y z H H0.
    destruct x, y, z; simpl in *; auto.
    gen l0 l1.
    induction l; intros; simpl in *.
    + destruct l1; auto.
      rewrite lt_listP_nil_r in H0; contradiction.
    + destruct l0; simpl in *; try contradiction.
      destruct (POrd.compare a p) eqn:E;
        try contradiction.
      * rewrite POrd.compare_eq_iff in E.
        subst.
        destruct l1; try contradiction.
        destruct (POrd.compare p p0) eqn:E;
          try contradiction; auto.
        apply IHl with (l0 := l0); auto.
      * destruct l1; try contradiction.
        destruct (POrd.compare p p0) eqn:E0;
          try contradiction;
          destruct (POrd.compare a p0) eqn:E1;
          auto.
        -- rewrite POrd.compare_eq_iff in E0, E1.
           subst.
           rewrite POrd.compare_lt_iff in E.
           destruct p0; simpl in *; contradiction.
        -- rewrite POrd.compare_eq_iff in E0.
           subst.
           rewrite POrd.compare_lt_iff in E.
           rewrite POrd.compare_gt_iff in E1.
           destruct a, p0; simpl in *; try contradiction.
        -- rewrite POrd.compare_eq_iff in E1.
           subst.
           rewrite POrd.compare_lt_iff in E, E0.
           destruct p, p0; simpl in *; try contradiction.
        -- rewrite POrd.compare_lt_iff in E, E0.
           rewrite POrd.compare_gt_iff in E1.
           destruct a, p, p0; simpl in *; try contradiction.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. constructor; intros; 
    destruct x, y, x0, y0;
    unfold eq, lt in *;
    simpl in *;
    subst; auto.
Qed.

Fixpoint ltb_listP (l1 l2 : list Pauli) : bool :=
  match l1 with
  | [] => match l2 with
         | [] => false
         | _ :: _ => true
         end
  | h1 :: t1 => match l2 with
              | [] => false
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => true
                  | Eq => ltb_listP t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma ltb_listP_nil_r : forall (l : list Pauli),  ltb_listP l [] = false.
Proof. intros l. destruct l; simpl; auto. Qed. 

Definition ltb (x y : t) := ltb_listP (snd x) (snd y).

Fixpoint eqb_listP (l1 l2 : list Pauli) : bool :=
  match l1 with
  | [] => match l2 with
         | [] => true
         | _ :: _ => false
         end
  | h1 :: t1 => match l2 with
              | [] => false
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => false
                  | Eq => eqb_listP t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma eqb_listP_refl : forall (l : list Pauli),  eqb_listP l l = true.
Proof. intros l. induction l; simpl; auto. 
  destruct a; simpl; apply IHl.
Qed. 

Lemma eqb_listP_neq_false : forall (l1 l2 : list Pauli),  l1 <> l2 <-> eqb_listP l1 l2 = false.
Proof. intros l1 l2. split; intro H.
  - gen l2.
    induction l1; intros.
    + destruct l2; try contradiction; simpl; auto.
    + simpl. 
      destruct l2; auto.
      destruct (POrd.compare a p) eqn:E; auto.
      rewrite POrd.compare_eq_iff in E; subst.
      assert (l1 <> l2).
      { intro; subst; contradiction. }
      apply IHl1; auto.
  - intro. subst.
    rewrite eqb_listP_refl in H.
    discriminate.
Qed.

Lemma eqb_listP_eq_true : forall (l1 l2 : list Pauli),  l1 = l2 <-> eqb_listP l1 l2 = true.
Proof. intros l1 l2. split; intro H.
  - gen l2.
    induction l1; intros.
    + destruct l2; auto; discriminate.
    + simpl. 
      destruct l2; try discriminate.
      destruct (POrd.compare a p) eqn:E; 
        inversion H; subst;
        unfold POrd.compare in E; 
        rewrite POrd.compare_refl in E;
        try discriminate;
        try rewrite eqb_listP_refl; auto.
  - gen l2. induction l1; intros.
    + destruct l2; simpl in *; auto; discriminate.
    + destruct l2.
      * simpl in *; discriminate.
      * simpl in *.
        destruct (POrd.compare a p) eqn:E;
          simpl in *; try discriminate.
        rewrite POrd.compare_eq_iff in E; subst.
        f_equal.
        apply IHl1; auto.
Qed.
  
Lemma ltb_listP_neq_or : forall (l1 l2 : list Pauli), 
    l1 <> l2 -> (ltb_listP l1 l2) = true \/ (ltb_listP l2 l1) = true.
Proof. intros l1 l2 H.
  gen l2.
  induction l1; intros.
  - destruct l2; try contradiction; simpl; auto.
  - destruct l2; simpl in *; auto.
    destruct (POrd.compare a p) eqn:E; auto.
    + rewrite POrd.compare_eq_iff in E; subst.
      assert (l1 <> l2).
      { intro; subst; contradiction. }
      assert (POrd.compare p p = Eq).
      { unfold POrd.compare. rewrite POrd.compare_refl. auto. }
      rewrite H1.
      apply IHl1; auto.
    + right. 
      assert (POrd.compare p a = Lt).
      { unfold POrd.compare in *.
        rewrite POrd.compare_antisym.
        destruct a, p; try discriminate; auto. }
      rewrite H0; auto.
Qed.

Lemma ltb_listP_neq_nor : forall (l1 l2 : list Pauli), 
    l1 <> l2 -> (ltb_listP l1 l2) = false \/ (ltb_listP l2 l1) = false.
Proof. intros l1 l2 H.
    gen l2.
  induction l1; intros.
  - destruct l2; try contradiction; simpl; auto.
  - destruct l2; simpl in *; auto.
    destruct (POrd.compare a p) eqn:E; auto.
    + rewrite POrd.compare_eq_iff in E; subst.
      assert (l1 <> l2).
      { intro; subst; contradiction. }
      assert (POrd.compare p p = Eq).
      { unfold POrd.compare. rewrite POrd.compare_refl. auto. }
      rewrite H1.
      apply IHl1; auto.
    + right. 
      assert (POrd.compare p a = Gt).
      { unfold POrd.compare in *.
        rewrite POrd.compare_antisym.
        unfold CompOpp in *.
        destruct a, p; try discriminate; auto. }
      rewrite H0; auto.
Qed.

Lemma lt_listP_iff_ltb_listP : forall (l1 l2 : list Pauli), 
    lt_listP l1 l2 <-> ltb_listP l1 l2 = true.
Proof. intros l1 l2. split; intro H;
    gen l2; induction l1; intros;
    destruct l2; simpl in *; auto; 
    try contradiction; try discriminate;
    destruct (POrd.compare a p) eqn:E;
    auto; try contradiction; try discriminate.
Qed. 

Definition eqb (x y : t) := eqb_listP (snd x) (snd y).

Definition compare (x y : t) : comparison :=
  if eqb x y then Eq else if ltb x y then Lt else Gt.

Lemma compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. destruct x, y; unfold eq, lt, compare; simpl.
  unfold eqb, ltb; simpl.
  destruct (eqb_listP l l0) eqn:E;
    try rewrite eqb_listP_eq_true in E; subst;
    try rewrite <- eqb_listP_neq_false in E;
    try constructor.
  - rewrite <- eqb_listP_eq_true in E; auto.
  - remember E as E'. clear HeqE'.
    apply ltb_listP_neq_or in E.
    apply ltb_listP_neq_nor in E'.
    destruct E; destruct E'; try rewrite H in *; try discriminate.
    + constructor.
      rewrite <- lt_listP_iff_ltb_listP in H; auto.
    + rewrite H0. constructor.
      rewrite <- lt_listP_iff_ltb_listP in H; auto.
Qed.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. intros x y.
  destruct x, y; unfold eq; simpl.
  apply (list_eq_dec POrd.eq_dec).
Qed.

Fixpoint le_listP (l1 l2 : list Pauli) :=
  match l1 with
  | [] => match l2 with
         | [] => True
         | _ :: _ => True
         end
  | h1 :: t1 => match l2 with
              | [] => False
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => True
                  | Eq => le_listP t1 t2
                  | Gt => False
                  end
              end
  end.

Lemma le_listP_refl : forall (l : list Pauli), le_listP l l.
Proof. intros l. induction l; simpl; auto. 
  destruct a; simpl; apply IHl.
Qed. 

Definition le (x y : t) := le_listP (snd x) (snd y).
Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
Proof. intros x y.
  unfold le, lt, eq in *; 
    destruct x, y;
    simpl in *.
  split; intro H.
  - gen l0. induction l; intros; auto.
    + destruct l0; auto.
    + simpl. destruct l0; simpl in *; try contradiction.
      destruct (POrd.compare a p) eqn:E; auto.
      rewrite POrd.compare_eq_iff in E; subst.
      destruct (IHl l0 H); subst; auto.
  - destruct H.
    + gen l0. induction l; intros;
        destruct l0; simpl in *; auto.
      destruct (POrd.compare a p) eqn:E; auto.
    + subst. apply le_listP_refl.
Qed.
(* Not needed
Fixpoint leb_listP (l1 l2 : list Pauli) :=
  match l1 with
  | [] => match l2 with
         | [] => true
         | _ :: _ => true
         end
  | h1 :: t1 => match l2 with
              | [] => false
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => true
                  | Eq => leb_listP t1 t2
                  | Gt => false
                  end
              end
  end.

Definition leb' (x y : t) := leb_listP (snd x) (snd y). *)

Definition leb (x y : t) := orb (eqb x y) (ltb x y).
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y.
  unfold "<=?".
  destruct x, y; unfold eqb, ltb; simpl.
  destruct (eqb_listP l l0) eqn:E.
  - rewrite <- eqb_listP_eq_true in E; subst.
    left. auto.
  - rewrite <- eqb_listP_neq_false in E.
    remember E as E'. clear HeqE'.
    apply ltb_listP_neq_or in E.
    apply ltb_listP_neq_nor in E'.
    destruct E, E'; rewrite H in *; 
      try discriminate; rewrite H0 in *; auto.
    right. destruct (eqb_listP l0 l); auto.
Qed.

Lemma ltb_listP_trans : forall (l0 l1 l2 : list Pauli),
    ltb_listP l0 l1 = true -> ltb_listP l1 l2 = true -> ltb_listP l0 l2 = true.
Proof. intros l0 l1 l2 H H0.
  gen l1 l2.
  induction l0; intros.
  - simpl. destruct l2; auto.
    simpl in *. 
    rewrite ltb_listP_nil_r in H0.
    discriminate.
  - destruct l2.
    + rewrite ltb_listP_nil_r in *.
      discriminate.
    + simpl in *.
      destruct l1; try discriminate.
      simpl in *.
      destruct (POrd.compare a p0) eqn:E;
        simpl in *; try discriminate.
      * rewrite POrd.compare_eq_iff in E.
        subst.
        destruct (POrd.compare p0 p) eqn:E;
          auto; try discriminate.
        rewrite POrd.compare_eq_iff in E;
          subst.
        apply (IHl0 l1); auto.
      * destruct (POrd.compare p0 p) eqn:E';
          try discriminate.
        -- rewrite POrd.compare_eq_iff in E';
             subst.
           rewrite E in *. auto.
        -- destruct a, p0, p; simpl in *;
             auto; try discriminate.
Qed.
 
Lemma leb_trans : Transitive (fun x y => leb x y = true).
Proof. unfold Transitive, "<=?".
  intros x y z H H0.
  rewrite orb_true_iff in *.
  destruct x, y, z; 
    unfold eqb, ltb in *;
    simpl in *.
  destruct H, H0;
    try rewrite <- eqb_listP_eq_true in *;
    subst; auto.
  right. apply ltb_listP_trans with (l1 := l0); auto.
Qed.

End TTypeOrdering.

Module TOrd := TTypeOrdering <+ OrderedTypeFullFacts(TTypeOrdering) <+ Sort (TTypeOrdering).

Definition lexicographic {n : nat} (Lt : list (TType n)) : list (TType n) := rev (TOrd.sort Lt).




(*** Normalization ***)
(*
(** ** Version with more fixed points ** **)
(* Prove that this version is equivalent with the less fixpointed version later on *)
(** k := lenL   < fuel >
     nth_j_L_defaultT := nth j L (defaultT_I n)   < fixed >
     initL := L   < fixed >
     n, i, j, lenL   < fixed > **)
Fixpoint loop_replaceT_XY_fixed (n i j k lenL : nat) (nth_j_L_defaultT : TType n) (initL L : list (TType n)) {struct k} : list (TType n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb (lenL - k) j
    then loop_replaceT_XY_fixed n i j k' lenL nth_j_L_defaultT initL L
    else 
      match nth i (snd (nth (lenL - k) initL (defaultT_I n))) gI with
      | gX | gY => loop_replaceT_XY_fixed n i j k' lenL nth_j_L_defaultT initL (switch L (gMulT nth_j_L_defaultT (nth (lenL - k) initL (defaultT_I n))) (lenL - k))
      | _ => loop_replaceT_XY_fixed n i j k' lenL nth_j_L_defaultT initL L
      end
end.

(** k := lenL   < fuel >
     nth_j_L_defaultT := nth j L (defaultT_I n)   < fixed >
     initL := L   < fixed >
     n, i, j, lenL   < fixed > **)
Fixpoint loop_replaceT_Z_fixed (n i j k lenL : nat) (nth_j_L_defaultT : TType n) (initL L : list (TType n)) {struct k} : list (TType n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb (lenL - k) j
    then loop_replaceT_Z_fixed n i j k' lenL nth_j_L_defaultT initL L
    else 
      match nth i (snd (nth (lenL - k) initL (defaultT_I n))) gI with
      | gZ => loop_replaceT_Z_fixed n i j k' lenL nth_j_L_defaultT initL (switch L (gMulT nth_j_L_defaultT (nth (lenL - k) initL (defaultT_I n))) (lenL - k))
      | _ => loop_replaceT_Z_fixed n i j k' lenL nth_j_L_defaultT initL L
      end
end.

(** j := lenL   < fuel >
     Lz := []
     n, i, lenL   < fixed > **)
Fixpoint loop_j_return_PL_fixed (n i j lenL : nat) (P : list nat) (L : list (TType n)) (Lz : list nat) : (list nat) * (list (TType n)) := 
  match j with
  | S j' => 
      if (existsb (fun p : nat => Nat.eqb p (lenL - j)%nat) P) 
      then
        (* loop on next j *)
        loop_j_return_PL_fixed n i j' lenL P L Lz
      else 
        match nth i (snd (nth (lenL - j)%nat L (defaultT_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_PL_fixed n i j' lenL P L Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_PL_fixed n i j' lenL P L ((lenL - j)%nat :: Lz)
        | _ => 
            (* add j to P and return P, (loop_replaceT_XY n i j (length L) L) *)
            (((lenL - j)%nat :: P), (loop_replaceT_XY_fixed n i (lenL - j)%nat lenL lenL (nth (lenL - j)%nat L (defaultT_I n)) L L))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return P, L *)
          (P, L)
      | h :: _ => 
          (* add j to P and return P, (loop_replaceT_Z n i j (length L) L) *)
          ((h :: P), (loop_replaceT_Z_fixed n i h lenL lenL (nth (lenL - j)%nat L (defaultT_I n)) L L))
      end
  end.

(** i := n   < fuel >
     lenL := length L   < fixed >
     n := initialized from input   < fixed >
     P := []
     L := initialized from input **)
Fixpoint loop_normalization_fixed (n i lenL : nat) (P : list nat) (L : list (TType n)) {struct i} : list (TType n)  :=
  match i with
  | S i' =>
      (* do loop_j_return_PL and get (P, L), recurse on next i *)
      let (P', L') := loop_j_return_PL_fixed n (n - i)%nat lenL lenL P L [] in
      loop_normalization_fixed n i' lenL P' L'
  | 0%nat =>
      (* Final Ordering with rev P *)
      (map (fun p : nat => nth p L (defaultT_I n)) (rev P)) ++ 
        lexicographic (map (fun q : nat => nth q L (defaultT_I n))
                     (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P))
                        (List.seq 0 (lenL))))
  end.

(**  : list (TType n) **)
Definition normalize_fixed {n : nat} (L : list (TType n)) := loop_normalization_fixed n n (length L) [] L.

*)

(** ** Version with less fixpoints ** **)
(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceT_XY (n i j k : nat) (L : list (TType n)) {struct k} : list (TType n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb ((length L) - k) j
    then loop_replaceT_XY n i j k' L
    else 
      match nth i (snd (nth ((length L) - k) L (defaultT_I n))) gI with
      | gX | gY => loop_replaceT_XY n i j k' (switch L (gMulT (nth j L (defaultT_I n)) (nth ((length L) - k) L (defaultT_I n))) ((length L) - k))
      | _ => loop_replaceT_XY n i j k' L
      end
end.

(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceT_Z (n i j k : nat) (L : list (TType n)) {struct k} : list (TType n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb ((length L) - k) j
    then loop_replaceT_Z n i j k' L
    else 
      match nth i (snd (nth ((length L) - k) L (defaultT_I n))) gI with
      | gZ => loop_replaceT_Z n i j k' (switch L (gMulT (nth j L (defaultT_I n)) (nth ((length L) - k) L (defaultT_I n))) ((length L) - k))
      | _ => loop_replaceT_Z n i j k' L
      end
end.

(** j := length L
     Lz := []
     n, i   < fixed > **)
Fixpoint loop_j_return_PL (n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat) : (list nat) * (list (TType n)) := 
  match j with
  | S j' => 
      if (existsb (fun p : nat => Nat.eqb p ((length L) - j)%nat) P) 
      then
        (* loop on next j *)
        loop_j_return_PL n i j' P L Lz
      else 
        match nth i (snd (nth ((length L) - j)%nat L (defaultT_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_PL n i j' P L Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_PL n i j' P L (((length L) - j)%nat :: Lz)
        | _ => 
            (* add j to P and return P, (loop_replaceT_XY n i j (length L) L) *)
            ((((length L) - j)%nat :: P), (loop_replaceT_XY n i ((length L) - j)%nat (length L) L))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return P, L *)
          (P, L)
      | h :: _ => 
          (* add j to P and return P, (loop_replaceT_Z n i j (length L) L) *)
          ((h :: P), (loop_replaceT_Z n i h (length L) L))
      end
  end.

(** i := n
     n := initialized from input   < fixed >
     P := []
     L := initialized from input **)
Fixpoint loop_normalization (n i : nat) (P : list nat) (L : list (TType n)) {struct i} : list (TType n)  :=
  match i with
  | S i' =>
      (* do loop_j_return_PL and get (P, L), recurse on next i *)
      let (P', L') := loop_j_return_PL n (n - i)%nat (length L) P L [] in
      loop_normalization n i' P' L'
  | 0%nat =>
      (* Final Ordering with rev P *)
      (map (fun p : nat => nth p L (defaultT_I n)) (rev P)) ++ 
        lexicographic (map (fun q : nat => nth q L (defaultT_I n))
                     (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P))
                        (List.seq 0 (length L))))
  end.

(**  : list (TType n) **)
Definition normalize {n : nat} (L : list (TType n)) := loop_normalization n n [] L.

Lemma loop_replaceT_XY_nil : forall (n i j k : nat), loop_replaceT_XY n i j k [] = [].
Proof. intros n i j k. gen i j.
  induction k; intros;
    unfold loop_replaceT_XY; auto.
  bdestruct_all; simpl in *; subst.
  rewrite IHk; auto.
  destruct (nth i (repeat gI n) gI) eqn:E; try rewrite IHk; auto.
Qed.

Lemma loop_replaceT_Z_nil : forall (n i j k : nat), loop_replaceT_Z n i j k [] = [].
Proof. intros n i j k. gen i j.
  induction k; intros;
    unfold loop_replaceT_Z; auto.
  bdestruct_all; simpl in *; subst.
  rewrite IHk; auto.
  destruct (nth i (repeat gI n) gI) eqn:E; try rewrite IHk; auto.
Qed.

Lemma loop_j_return_PL_nil : forall (n i j : nat) (P : list nat) (Lz : list nat),
    snd (loop_j_return_PL n i j P [] Lz) = [].
Proof. intros n i j P Lz.
  gen i P Lz. induction j; intros; 
    unfold loop_j_return_PL.
  destruct (rev Lz); simpl; auto.
  destruct (existsb (fun p : nat => p =? length [] - S j)%nat P) eqn:E.
  rewrite IHj; auto.
  destruct (nth i (snd (nth (length [] - S j) [] (defaultT_I n))) gI) eqn:E';
    try rewrite IHj; auto.
Qed.

Lemma loop_normalization_nil : forall (n i : nat), loop_normalization n i [] [] = [].
Proof. intros n i. 
  induction i;
    unfold loop_normalization; simpl;
    unfold lexicographic; simpl; auto.
Qed.

Lemma normalize_nil : forall {n : nat}, @normalize n [] = [].
Proof. intros n.
  unfold normalize.
  apply loop_normalization_nil.
Qed.




(** ** Fuel based admissibility proof ** **)
(** Assuming that Permutation on intersections is provably admissible *) 

(** ** Lemma 1 ** **)
Lemma Permutation_filter_existsb_eqdec : 
  forall {A : Type} (eq_dec : (forall x y : A, {x = y} + {x <> y})) (L P : list A),
    NoDup L -> NoDup P -> incl P L ->
    Permutation P (filter (fun a => existsb (fun p => if eq_dec p a then true else false) P) L).
Proof. intros A eq_dec L P H H0 H1.
  gen P.
  induction L; intros.
  - destruct P; auto.
    simpl in *.
    assert (In a (a :: P)) by (simpl; auto).
    apply H1 in H2.
    contradiction.
  - destruct (in_dec eq_dec a P).
    + apply In_nth with (d := a) in i.
      destruct i as [n [H2 H3]].
      pose (nth_inc n P a H2).
      rewrite H3 in e.

      assert (Permutation P ([a] ++ firstn n P ++ skipn (S n) P)).
      { rewrite e at 1.  rewrite ! app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm. }
      apply Permutation_trans with (l' := [a] ++ firstn n P ++ skipn (S n) P); auto.
      
      assert ((filter (fun a0 : A =>
                         existsb (fun p : A => if eq_dec p a0 then true else false) P) (a :: L)) =
                a :: (filter (fun a : A =>
                               existsb (fun p : A => if eq_dec p a then true else false) P) L)).
      { simpl. 
        destruct (existsb (fun p : A => if eq_dec p a then true else false) P) eqn:E; auto.
        rewrite e in E.
        rewrite existsb_app in E.
        simpl in E.
        destruct (eq_dec a a); try contradiction.
        simpl in E.
        rewrite orb_true_r in E.
        discriminate. }
      rewrite H5.
      replace ([a] ++ firstn n P ++ skipn (S n) P) 
        with (a :: (firstn n P ++ skipn (S n) P)) by auto.
      constructor.
      rewrite NoDup_cons_iff in H.
      destruct H.

      assert ((filter (fun a0 : A => existsb 
                                    (fun p : A => if eq_dec p a0 then true else false) 
                                    P) L) = 
                (filter (fun a0 : A => existsb 
                                      (fun p : A => if eq_dec p a0 then true else false) 
                                      (firstn n P ++ skipn (S n) P)) L)).
      { replace (fun a0 : A => existsb (fun p : A => if eq_dec p a0 then true else false) P)
                  with (fun a0 : A => existsb (fun p : A => if eq_dec p a0 then true else false) 
                                     (firstn n P ++ [a] ++ skipn (S n) P))
          by (rewrite <- e; auto).
        apply filter_ext_in.
        intros a0 H7.
        rewrite ! existsb_app.
        f_equal.
        setoid_rewrite <- orb_false_l at 6.
        f_equal.
        simpl.
        destruct (eq_dec a a0) eqn:E; auto.
        subst. contradiction. }
      rewrite H7.
      replace ([a] ++ skipn (S n) P) with (a :: skipn (S n) P) in e by auto.
      apply (IHL H6 (firstn n P ++ skipn (S n) P)).
      * rewrite e in H0.
        apply NoDup_remove_1 in H0.
        auto.
      * unfold incl. intros.
        assert (incl (firstn n P ++ skipn (S n) P) P).
        { unfold incl. intros.
          rewrite e.
          rewrite in_app_iff.
          rewrite in_app_iff in H9.
          destruct H9.
          - left; auto.
          - right; apply in_cons; auto. } 
        rewrite e in H0.
        apply NoDup_remove in H0.
        destruct H0.
        destruct (eq_dec a a0).
        -- subst. contradiction.
        -- apply H9 in H8.
           apply H1 in H8.
           destruct H8; try contradiction; auto.
    + assert (incl P L).
      { unfold incl. intros.
        destruct (eq_dec a a0).
        - subst. contradiction.
        - apply H1 in H2.
          destruct H2; try contradiction; auto. }
      rewrite NoDup_cons_iff in H.
      destruct H.
      specialize (IHL H3 P H0 H2).
      assert ((filter (fun a : A => 
                         existsb (fun p : A => if eq_dec p a then true else false) P) L)
              = (filter (fun a0 : A =>
                           existsb (fun p : A => if eq_dec p a0 then true else false) P) (a :: L))).
      { simpl.
        destruct (existsb (fun p : A => if eq_dec p a then true else false) P) eqn:E; auto.
        rewrite existsb_exists in E.
        destruct E as [x [H4 H5]].
        destruct (eq_dec x a) eqn:E; try discriminate.
        subst. contradiction. }
      rewrite <- H4; auto.
Qed.

(** ** Corollary 1 ** **)
Lemma Permutation_filter_existsb_eqdec_seq : forall (k : nat) (P : list nat),
    NoDup P -> incl P (List.seq 0 k) ->
    Permutation P (filter (fun a => existsb (fun p => if Nat.eq_dec p a then true else false) P) (List.seq 0 k)).
Proof. intros k P H H0. 
  apply Permutation_filter_existsb_eqdec; auto.
  apply seq_NoDup.
Qed.


(** ** Lemma 2 ** **)
Lemma Permutation_map_nth : forall {A : Type} (default : A) (L : list A),
    L = (map (fun q : nat => nth q L default) (List.seq 0 (length L))).
Proof. intros A default L.
  induction L; auto.
  simpl. f_equal.
  rewrite IHL at 1.
  apply nth_ext with (d := nth 0%nat L default) (d' := a).
  - rewrite ! map_length, ! seq_length; auto.
  - intros n H.
     rewrite ! map_length, ! seq_length in H.
     rewrite ! map_nth with (d := 0%nat).
     rewrite ! seq_nth; auto.
Qed.

(** ** Lemma 3 ** **)
Lemma Permutation_map_nth_seq : forall {A : Type} (L : list A) (default : A) (S : list nat),
    Permutation (seq 0 (length L)) S ->
    Permutation L (map (fun p : nat => nth p L default) S).
Proof. intros A L default S H.
  rewrite (Permutation_map_nth default L) at 1.
  apply Permutation_map; auto.
Qed.

(** ** Lemma 4 ** **)
Lemma final_ordering_Permutation : forall (n : nat) (P : list nat) (L : list (TType n)) ,
    NoDup P -> incl P (seq 0 (length L)) ->
    Permutation L ((map (fun p : nat => nth p L (defaultT_I n)) (rev P)) ++ 
                     lexicographic (map (fun q : nat => nth q L (defaultT_I n))
                                      (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)) (List.seq 0 (length L))))).
Proof. intros n P L H H0.
  unfold lexicographic.
  rewrite map_rev.
  rewrite <- rev_app_distr.
  apply Permutation_trans with (l' := (TOrd.sort
                                        (map (fun q : nat => nth q L (defaultT_I n))
                                           (filter
                                              (fun a : nat =>
                                                 ¬ existsb
                                                   (fun p : nat =>
                                                      if Nat.eq_dec p a then true else false) P)
                                              (seq 0 (length L)))) ++
                                        map (fun p : nat => nth p L (defaultT_I n)) P));
    try apply Permutation_rev.

  assert (Permutation
            ((map (fun q : nat => nth q L (defaultT_I n))
                (filter
                   (fun a : nat =>
                      ¬ existsb
                        (fun p : nat => if Nat.eq_dec p a then true else false)
                        P) (seq 0 (length L)))) ++
               map (fun p : nat => nth p L (defaultT_I n)) P)
            (TOrd.sort
               (map (fun q : nat => nth q L (defaultT_I n))
                  (filter
                     (fun a : nat =>
                        ¬ existsb
                          (fun p : nat => if Nat.eq_dec p a then true else false)
                          P) (seq 0 (length L)))) ++
               map (fun p : nat => nth p L (defaultT_I n)) P)).
  { apply Permutation_app_tail.
    apply TOrd.Permuted_sort. }
  apply Permutation_trans with (l' := (map (fun q : nat => nth q L (defaultT_I n))
                                        (filter (fun a : nat =>
                                                   ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)
                                           (seq 0 (length L))) ++ map (fun p : nat => nth p L (defaultT_I n)) P));
    auto.
  rewrite <- map_app.

  assert (Permutation (seq 0 (length L))
            (filter
               (fun a : nat =>
                  ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)
               (seq 0 (length L)) ++ P)).
  { apply Permutation_trans with (l' := (P ++ filter
       (fun a : nat =>
        ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)
       (seq 0 (length L)))); try apply Permutation_app_comm.
    
    assert (Permutation
              ((filter (fun a => existsb (fun p => if Nat.eq_dec p a then true else false) P) (List.seq 0 (length L))) ++ (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)) (seq 0 (length L))))
              (P ++ (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)) (seq 0 (length L))))).
    { apply Permutation_app_tail.
      apply Permutation_sym.
      apply Permutation_filter_existsb_eqdec_seq; auto. }
    
    apply Permutation_trans with (l' := 
                                    (filter
                                       (fun a : nat =>
                                          existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)
                                       (seq 0 (length L)) ++
                                       filter
                                       (fun a : nat =>
                                          ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) P)
                                       (seq 0 (length L))));
      auto.
    apply filter_orth_app_permutation. }
  apply Permutation_map_nth_seq; auto.
Qed.


(** ** Fueled version with less fixpoints ** **)
(** k := length L   < fuel >
     n, i, j   < fixed > **)
Fixpoint loop_replaceT_XY_fuel (kfuel n i j k : nat) (L : list (TType n)) {struct kfuel} : list (TType n) :=
  match kfuel with
  | S kfuel' =>
      match k with
      | 0%nat => L
      | S k' => 
          if Nat.eqb ((length L) - k) j
          then loop_replaceT_XY_fuel kfuel' n i j k' L
          else 
            match nth i (snd (nth ((length L) - k) L (defaultT_I n))) gI with
            | gX | gY => loop_replaceT_XY_fuel kfuel' n i j k' (switch L (gMulT (nth j L (defaultT_I n)) (nth ((length L) - k) L (defaultT_I n))) ((length L) - k))
            | _ => loop_replaceT_XY_fuel kfuel' n i j k' L
            end
      end
  | 0%nat => L
  end.

Lemma loop_replaceT_XY_length : forall (n i j k : nat) (L : list (TType n)),
    length (loop_replaceT_XY n i j k L) = length L.
Proof. intros n i j k L.
  gen L.
  induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
  all: rewrite IHk; rewrite switch_len; auto.
Qed.

Lemma loop_replaceT_XY_fuel_length : forall (kfuel n i j k : nat) (L : list (TType n)),
    length (loop_replaceT_XY_fuel kfuel n i j k L) = length L.
Proof. intros kfuel n i j k L.
  gen k L.
  induction kfuel; intros; simpl; auto.
  destruct k; auto.
  bdestruct_all; simpl; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
  all: rewrite IHkfuel; rewrite switch_len; auto.
Qed.

Lemma loop_replaceT_XY_fuel_saturated_base : forall (n i j k : nat) (L : list (TType n)),
    loop_replaceT_XY_fuel k n i j k L = loop_replaceT_XY n i j k L.
Proof. intros n i j k L.
  gen L. induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
Qed.

Lemma loop_replaceT_XY_fuel_saturated : forall (kfuel n i j k : nat) (L : list (TType n)),
    (kfuel >= k)%nat -> 
    loop_replaceT_XY_fuel kfuel n i j k L = loop_replaceT_XY n i j k L.
Proof. intros kfuel n i j k L H. 
  gen kfuel L. induction k; intros.
  - destruct kfuel; auto.
  - destruct kfuel; try lia.
    assert (kfuel >= k)%nat by lia.
    simpl. bdestruct_all; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
Qed.


(** k := length L   < fuel >
     n, i, j   < fixed > **)
Fixpoint loop_replaceT_Z_fuel (kfuel n i j k : nat) (L : list (TType n)) {struct kfuel} : list (TType n) :=
  match kfuel with
  | S kfuel' =>
      match k with
      | 0%nat => L
      | S k' => 
          if Nat.eqb ((length L) - k) j
          then loop_replaceT_Z_fuel kfuel' n i j k' L
          else 
            match nth i (snd (nth ((length L) - k) L (defaultT_I n))) gI with
            | gZ => loop_replaceT_Z_fuel kfuel' n i j k' (switch L (gMulT (nth j L (defaultT_I n)) (nth ((length L) - k) L (defaultT_I n))) ((length L) - k))
            | _ => loop_replaceT_Z_fuel kfuel' n i j k' L
            end
      end
  | 0%nat => L
  end.

Lemma loop_replaceT_Z_length : forall (n i j k : nat) (L : list (TType n)),
    length (loop_replaceT_Z n i j k L) = length L.
Proof. intros n i j k L.
  gen L.
  induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
  all: rewrite IHk; rewrite switch_len; auto.
Qed.

Lemma loop_replaceT_Z_fuel_length : forall (kfuel n i j k : nat) (L : list (TType n)),
    length (loop_replaceT_Z_fuel kfuel n i j k L) = length L.
Proof. intros kfuel n i j k L.
  gen k L.
  induction kfuel; intros; simpl; auto.
  destruct k; auto.
  bdestruct_all; simpl; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
  all: rewrite IHkfuel; rewrite switch_len; auto.
Qed.

Lemma loop_replaceT_Z_fuel_saturated_base : forall (n i j k : nat) (L : list (TType n)),
    loop_replaceT_Z_fuel k n i j k L = loop_replaceT_Z n i j k L.
Proof. intros n i j k L.
  gen L. induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
Qed.

Lemma loop_replaceT_Z_fuel_saturated : forall (kfuel n i j k : nat) (L : list (TType n)),
    (kfuel >= k)%nat -> 
    loop_replaceT_Z_fuel kfuel n i j k L = loop_replaceT_Z n i j k L.
Proof. intros kfuel n i j k L H. 
  gen kfuel L. induction k; intros.
  - destruct kfuel; auto.
  - destruct kfuel; try lia.
    assert (kfuel >= k)%nat by lia.
    simpl. bdestruct_all; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E; auto.
Qed.


(** j := length L   < fuel >
     Lz := []
     n, i   < fixed > **)
Fixpoint loop_j_return_PL_fuel (jfuel kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat) {struct jfuel} : (list nat) * (list (TType n)) := 
match jfuel with
| S jfuel' =>
  match j with
  | S j' => 
      if (existsb (fun p : nat => Nat.eqb p ((length L) - j)%nat) P) 
      then
        (* loop on next j *)
        loop_j_return_PL_fuel jfuel' kfuel n i j' P L Lz
      else 
        match nth i (snd (nth ((length L) - j)%nat L (defaultT_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_PL_fuel jfuel' kfuel n i j' P L Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_PL_fuel jfuel' kfuel n i j' P L (((length L) - j)%nat :: Lz)
        | _ => 
            (* add j to P and return P, (loop_replaceT_XY n i j (length L) L) *)
            ((((length L) - j)%nat :: P), (loop_replaceT_XY_fuel kfuel n i ((length L) - j)%nat (length L) L))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return P, L *)
          (P, L)
      | h :: _ => 
          (* add j to P and return P, (loop_replaceT_Z n i j (length L) L) *)
          ((h :: P), (loop_replaceT_Z_fuel kfuel n i h (length L) L))
      end
  end
| 0%nat => 
    match rev Lz with
    | [] => 
        (* return P, L *)
        (P, L)
    | h :: _ => 
        (* add j to P and return P, (loop_replaceT_Z n i j (length L) L) *)
        ((h :: P), (loop_replaceT_Z_fuel kfuel n i h (length L) L))
    end
end.

Lemma loop_j_return_PL_length : 
  forall (n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    length (snd (loop_j_return_PL n i j P L Lz)) = length L.
Proof. intros n i j P L Lz.
  gen L Lz. 
  induction j; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceT_Z_length; auto.
  - destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
    all : try rewrite loop_replaceT_XY_length; auto.
Qed.

Lemma loop_j_return_PL_fuel_length : 
  forall (jfuel kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    length (snd (loop_j_return_PL_fuel jfuel kfuel n i j P L Lz)) = length L.
Proof. intros jfuel kfuel n i j P L Lz.
  gen L Lz j. 
  induction jfuel; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceT_Z_fuel_length; auto.
  - destruct j.
    + destruct (rev Lz); simpl; auto.
      rewrite loop_replaceT_Z_fuel_length; auto.
    + destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
      all : try rewrite loop_replaceT_XY_fuel_length; auto.
Qed.

Lemma loop_j_return_PL_fuel_saturated_base : 
  forall (kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    (kfuel >= length L)%nat ->
    loop_j_return_PL_fuel j kfuel n i j P L Lz = loop_j_return_PL n i j P L Lz.
Proof. intros kfuel n i j P L Lz H.
  gen L Lz. induction j; intros; simpl.
  - destruct (rev Lz); auto.
    f_equal. apply loop_replaceT_Z_fuel_saturated; auto.
  - destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto;
      f_equal; apply loop_replaceT_XY_fuel_saturated; auto.
Qed.

Lemma loop_j_return_PL_fuel_saturated : 
  forall (jfuel kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    (kfuel >= length L)%nat -> (jfuel >= j)%nat ->
    loop_j_return_PL_fuel jfuel kfuel n i j P L Lz = loop_j_return_PL n i j P L Lz.
Proof. intros jfuel kfuel n i j P L Lz H H0.
  gen L Lz jfuel. induction j; intros.
  - destruct jfuel.
    + apply loop_j_return_PL_fuel_saturated_base; auto.
    + unfold loop_j_return_PL_fuel, loop_j_return_PL.
      destruct (rev Lz); auto.
      f_equal. apply loop_replaceT_Z_fuel_saturated; auto.
  - destruct jfuel; try lia.
    assert (jfuel >= j)%nat by lia. simpl.
    destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; auto;
      f_equal; apply loop_replaceT_XY_fuel_saturated; auto. 
Qed.

Lemma loop_j_return_PL_fuel_NoDup_P : 
  forall (jfuel kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    (forall (x : nat), In x Lz -> forall (m d : nat), (m < length P)%nat -> (nth m P d <> x)) -> 
    NoDup P -> NoDup (fst (loop_j_return_PL_fuel jfuel kfuel n i j P L Lz)).
Proof. intros jfuel kfuel n i j P L Lz H H0.
  gen kfuel j P L Lz.
  induction jfuel; intros; simpl; auto.
  - destruct (rev Lz) eqn:E; auto; simpl.
    assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
    rewrite <- in_rev in H1.
    specialize (H n0 H1).
    assert (~ In n0 P).
    { intro.
      apply In_nth with (d := 0%nat) in H2.
      destruct H2 as [x [H2 H3]].
      specialize (H x 0%nat H2).
      contradiction. }
    pose (NoDup_cons n0 H2 H0).
    auto.
  - destruct j.
    + destruct (rev Lz) eqn:E; auto; simpl.
      assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
      rewrite <- in_rev in H1.
      specialize (H n0 H1).
      assert (~ In n0 P).
      { intro.
        apply In_nth with (d := 0%nat) in H2.
        destruct H2 as [x [H2 H3]].
        specialize (H x 0%nat H2).
        contradiction. }
      pose (NoDup_cons n0 H2 H0).
      auto.
    + destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
      * assert (~ In ((length L) - S j)%nat P).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          pose (existsb_nth (fun p : nat => p =? (length L) - S j)%nat P 0%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * assert (~ In ((length L) - S j)%nat P).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          pose (existsb_nth (fun p : nat => p =? (length L) - S j)%nat P 0%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * apply IHjfuel; auto.
        intros x H1 m d H2.
        intro. subst.
        inversion H1.
        -- rewrite H3 in E.
           pose (existsb_nth (fun p : nat => p =? nth m P d)%nat P d H2 E) as E0.
           simpl in E0.
           rewrite Nat.eqb_neq in E0.
           contradiction.
        -- specialize (H (nth m P d) H3 m d H2).
           contradiction.
Qed.

Lemma loop_j_return_PL_NoDup_P : 
  forall (n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    (forall (x : nat), In x Lz -> forall (m d : nat), (m < length P)%nat -> (nth m P d <> x)) -> 
    NoDup P -> NoDup (fst (loop_j_return_PL n i j P L Lz)).
Proof. intros n i j P L Lz H H0. 
  rewrite <- loop_j_return_PL_fuel_saturated_base with (kfuel := length L); auto.
  apply loop_j_return_PL_fuel_NoDup_P; auto.
Qed.

Lemma loop_j_return_PL_fuel_incl_P_seq_0_length_L : 
  forall (jfuel kfuel n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0%nat (length L)) -> incl P (seq 0%nat (length L)) -> 
    incl (fst (loop_j_return_PL_fuel jfuel kfuel n i j P L Lz)) (seq 0%nat (length L)).
Proof. intros jfuel kfuel n i j P L Lz H H0 H1. 
  gen kfuel j P L Lz.
  induction jfuel; intros; simpl; auto.
  - destruct (rev Lz) eqn:E; auto; simpl.
    unfold incl; intros.
    inversion H2; subst; clear H2.
    + assert (In a Lz). { rewrite in_rev, E. constructor. auto. }
      apply H0 in H2; auto.
    + apply H1 in H3; auto.
  - destruct j.
    + destruct (rev Lz) eqn:E; auto; simpl.
      unfold incl; intros.
      inversion H2; subst; clear H2.
      * assert (In a Lz). { rewrite in_rev, E. constructor. auto. }
        apply H0 in H2; auto.
      * apply H1 in H3; auto.
    + destruct (existsb (fun p : nat => p =? (length L) - S j)%nat P) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; auto; simpl.
      * unfold incl; intros.
        inversion H2; subst; clear H2.
        -- rewrite in_seq; lia.
        -- apply H1 in H3; auto.
      * unfold incl; intros.
        inversion H2; subst; clear H2.
        -- rewrite in_seq; lia.
        -- apply H1 in H3; auto.
      * apply IHjfuel; auto.
        unfold incl; intros.
        inversion H2; subst; clear H2.
        -- rewrite in_seq; lia.
        -- apply H0 in H3; auto.
Qed.

Lemma loop_j_return_PL_incl_P_seq_0_length_L : 
  forall (n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0%nat (length L)) -> incl P (seq 0%nat (length L)) -> 
    incl (fst (loop_j_return_PL n i j P L Lz)) (seq 0%nat (length L)).
Proof. intros n i j P L Lz H H0 H1. 
  rewrite <- loop_j_return_PL_fuel_saturated_base with (kfuel := length L); auto.
  apply loop_j_return_PL_fuel_incl_P_seq_0_length_L; auto.
Qed.


(** i := n   < fuel >
     n := initialized from input   < fixed >
     P := []
     L := initialized from input **)
Fixpoint loop_normalization_fuel (ifuel jfuel kfuel n i : nat) (P : list nat) (L : list (TType n)) {struct ifuel} : list (TType n)  :=
  match ifuel with
  | S ifuel' =>
      match i with
      | S i' =>
          (* do loop_j_return_PL and get (P, L), recurse on next i *)
          let (P', L') := loop_j_return_PL_fuel jfuel kfuel n (n - i)%nat (length L) P L [] in
          loop_normalization_fuel ifuel' jfuel kfuel n i' P' L'
      | 0%nat =>
          (* Final Ordering with rev P *)
          (map (fun p : nat => nth p L (defaultT_I n)) (rev P)) ++ 
            lexicographic (map (fun q : nat => nth q L (defaultT_I n))
                             (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P))
                                (List.seq 0 (length L))))
      end
  | 0%nat => 
      (* Final Ordering with rev P *)
      (map (fun p : nat => nth p L (defaultT_I n)) (rev P)) ++ 
        lexicographic (map (fun q : nat => nth q L (defaultT_I n))
                         (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) P))
                            (List.seq 0 (length L))))
  end.

Lemma loop_normalization_fuel_saturated_base : 
  forall (jfuel kfuel n i : nat) (P : list nat) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> 
    loop_normalization_fuel i jfuel kfuel n i P L = loop_normalization n i P L.
Proof. intros jfuel kfuel n i P L H H0.
  gen jfuel kfuel P L.
  induction i; intros; simpl; auto.
  destruct (loop_j_return_PL_fuel jfuel kfuel n (n - S i) (length L) P L) eqn:E.
  destruct (loop_j_return_PL n (n - S i) (length L) P L []) eqn:E'.
  rewrite loop_j_return_PL_fuel_saturated in E; auto.
  rewrite E in E'.
  inversion E'; subst; clear E'.
  pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E'.
  rewrite E in E'.
  simpl in E'.
  apply IHi; rewrite E'; auto.
Qed.

Lemma loop_normalization_fuel_saturated : 
  forall (ifuel jfuel kfuel n i : nat) (P : list nat) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= i)%nat ->
    loop_normalization_fuel ifuel jfuel kfuel n i P L = loop_normalization n i P L.
Proof. intros ifuel jfuel kfuel n i P L H H0 H1.
   gen ifuel jfuel kfuel P L.
   induction i; intros; simpl.
  - destruct ifuel; auto.
  - destruct ifuel; try lia.
    assert (ifuel >= i)%nat by lia.
    simpl.
    rewrite loop_j_return_PL_fuel_saturated; auto.
    destruct (loop_j_return_PL n (n - S i) (length L) P L []) eqn:E.
    pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E'.
    rewrite E in E'.
    simpl in E'.
    apply IHi; try rewrite E'; auto.
Qed.


(**  : list (TType n) **)
Definition normalize_fuel (ifuel jfuel kfuel : nat) {n : nat} (L : list (TType n)) := loop_normalization_fuel ifuel jfuel kfuel n n [] L.

Lemma normalize_fuel_saturated : forall (ifuel jfuel kfuel : nat) {n : nat} (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= n)%nat ->
    normalize_fuel ifuel jfuel kfuel L = normalize L.
Proof. intros ifuel jfuel kfuel n L H H0 H1.
  unfold normalize_fuel, normalize.
  apply loop_normalization_fuel_saturated; auto.
Qed.


(** ** Property assumed to be provably admissible ** **)

Inductive PauliMult_listT {n : nat} (Lt1 Lt2 : list (TType n)) : Prop :=
| PauliMult_listT_step : length Lt1 = length Lt2 -> length Lt1 <> 0%nat ->
                (exists j k : nat, (j <> k) /\ (j < length Lt1)%nat /\ (k < length Lt1)%nat /\
                              (Lt2 = (switch Lt1 
                                        (gMulT (nth j Lt1 (defaultT_I n)) (nth k Lt1 (defaultT_I n))) k))) ->
              PauliMult_listT Lt1 Lt2.

Lemma PauliMult_listT_preserves_proper_length_TType : 
  forall {n : nat} (Lt1 Lt2 : list (TType n)),
    PauliMult_listT Lt1 Lt2 -> Forall proper_length_TType Lt1 -> 
    Forall proper_length_TType Lt2.
Proof. intros n Lt1 Lt2 H H0.
  inversion H.
  destruct H3 as [j [k [H3 [H4 [H5 H6]]]]].
  rewrite Forall_forall in H0.
  rewrite Forall_forall. intros x H7.
  apply In_nth with (d := defaultT_I n) in H7.
  destruct H7 as [i [H7 H8]].
  rewrite <- H1 in H7.
  subst.
  bdestruct (i =? k)%nat.
  - subst. rewrite nth_switch_hit; auto.
    apply proper_length_TType_gMulT; apply H0; apply nth_In; auto.
  - rewrite nth_switch_miss; auto.
    apply H0; apply nth_In; auto.
Qed.

Lemma PauliMult_listT_swap : forall {n : nat} (Lt1 Lt2 : list (TType n)),
    Forall proper_length_TType Lt1 -> 
    Forall coef_plus_minus_1 Lt1 ->
    PauliMult_listT Lt1 Lt2 -> PauliMult_listT Lt2 Lt1.
Proof. intros n Lt1 Lt2 PLLt1 UHLt1 H.
  assert (PLnth : forall i : nat, (i < length Lt1)%nat -> proper_length_TType (nth i Lt1 (defaultT_I n))).
  { intros. apply Forall_nth; auto. }
  assert (UHnth : forall i : nat, (i < length Lt1)%nat -> coef_plus_minus_1 (nth i Lt1 (defaultT_I n))).
  { intros. apply Forall_nth; auto. }
  inversion H.
  destruct H2 as [j [k [H2 [H3 [H4 H5]]]]].
  constructor; auto.
  lia.
  exists j. exists k.
  split; auto.
  split; try lia.
  split; try lia.
  assert (H6 : nth j Lt2 (defaultT_I n) = nth j Lt1 (defaultT_I n)).
  { rewrite H5. 
    rewrite nth_switch_miss; auto. }
  rewrite H6.
  rewrite H5.
  rewrite nth_switch_hit; auto.
  rewrite <- gMulT_assoc.
  rewrite gMulT_inv.
  rewrite gMulT_id_l.
  rewrite switch_switch_overshadow.
  rewrite switch_inc; auto.
  rewrite nth_inc with (n := k) (x := (defaultT_I n)) at 1; auto.
  all : auto.
Qed.

Inductive PauliMult_listT_chain {n : nat} : list (TType n) -> list (TType n) -> Prop :=
| PauliMult_listT_chain_id : forall (Lt1 Lt2 : list (TType n)), 
    Lt1 = Lt2 -> PauliMult_listT_chain Lt1 Lt2
| PauliMult_listT_chain_base : forall (Lt1 Lt2 : list (TType n)), 
    PauliMult_listT Lt1 Lt2 -> PauliMult_listT_chain Lt1 Lt2
| PauliMult_listT_chain_append : forall (Lt1 Lt2 Lt3 : list (TType n)),
    PauliMult_listT_chain Lt1 Lt2 -> PauliMult_listT_chain Lt2 Lt3 ->
    PauliMult_listT_chain Lt1 Lt3.

Lemma PauliMult_listT_chain_preserves_proper_length_TType : 
  forall {n : nat} (Lt1 Lt2 : list (TType n)),
    PauliMult_listT_chain Lt1 Lt2 -> Forall proper_length_TType Lt1 -> 
    Forall proper_length_TType Lt2.
Proof. intros n Lt1 Lt2 H H0.
  induction H; subst; auto.
  apply PauliMult_listT_preserves_proper_length_TType with (Lt1 := Lt1); auto.
Qed.

Inductive PauliMult_listT_chain_Permutation {n : nat} (Lt1 Lt3 : list (TType n)) : Prop :=
| exists_middle_PauliMult_listT_chain_Permutation : 
  (exists (Lt2 : list (TType n)), PauliMult_listT_chain Lt1 Lt2 /\ Permutation Lt2 Lt3) ->
  PauliMult_listT_chain_Permutation Lt1 Lt3.

Lemma PauliMult_listT_chain_Permutation_append : forall {n : nat} (Lt1 Lt2 Lt3 : list (TType n)),
    PauliMult_listT_chain Lt1 Lt2 -> PauliMult_listT_chain_Permutation Lt2 Lt3 ->
    PauliMult_listT_chain_Permutation Lt1 Lt3.
Proof. intros n Lt1 Lt2 Lt3 H H0.
  inversion H0; clear H0.
  destruct H1 as [Lt4 [H1 H2]].
  assert (PauliMult_listT_chain Lt1 Lt4) 
    by (apply PauliMult_listT_chain_append with (Lt2 := Lt2); auto).
  constructor. exists Lt4. split; auto.
Qed.


Lemma loop_replaceT_XY_fuel_PauliMult_listT : 
  forall (kfuel n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    (loop_replaceT_XY_fuel kfuel n i j k L) =
      (loop_replaceT_XY_fuel (S kfuel) n i j k L) \/
      PauliMult_listT 
        (loop_replaceT_XY_fuel kfuel n i j k L)
        (loop_replaceT_XY_fuel (S kfuel) n i j k L).
Proof. intros kfuel n i j k L H H0 H1.
  gen k L.
  induction kfuel; intros.
  - simpl. destruct k; auto.
    destruct ((length L) - S k =? j)%nat eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E'; auto.
    + right. apply PauliMult_listT_step; auto.
      * rewrite switch_len; auto.
      * exists j. exists ((length L) - S k)%nat.
        repeat (split; auto; try lia).
        intro. rewrite <- H2 in E.
        rewrite Nat.eqb_neq in E.
        contradiction.
    + right. apply PauliMult_listT_step; auto.
      * rewrite switch_len; auto.
      * exists j. exists ((length L) - S k)%nat.
        repeat (split; auto; try lia).
        intro. rewrite <- H2 in E.
        rewrite Nat.eqb_neq in E.
        contradiction.
  - simpl. destruct k; auto.
    destruct ((length L) - S k =? j)%nat eqn:E.
    + rewrite Nat.eqb_eq in E.
      assert (k <= length L)%nat by lia.
      destruct (IHkfuel k L H H0 H2); auto.
    + destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E';
        simpl in IHkfuel; apply IHkfuel; try rewrite switch_len; auto; try lia.
Qed.

Lemma loop_replaceT_XY_fuel_PauliMult_listT_chain : 
  forall (kfuel n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    PauliMult_listT_chain L (loop_replaceT_XY_fuel kfuel n i j k L).
Proof. intros kfuel n i j k L H H0 H1.
  induction kfuel.
  - simpl. apply PauliMult_listT_chain_id; auto.
  - pose (loop_replaceT_XY_fuel_PauliMult_listT kfuel n i j k L H H0 H1) as E.
    destruct E;
      apply PauliMult_listT_chain_append with (Lt2 := loop_replaceT_XY_fuel kfuel n i j k L);
      auto.
    + apply PauliMult_listT_chain_id; auto.
    + apply PauliMult_listT_chain_base; auto.
Qed.

Lemma loop_replaceT_XY_PauliMult_listT_chain : 
  forall (n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    PauliMult_listT_chain L (loop_replaceT_XY n i j k L).
Proof. intros n i j k L H H0 H1.
  rewrite <- loop_replaceT_XY_fuel_saturated_base.
  apply loop_replaceT_XY_fuel_PauliMult_listT_chain; auto.
Qed.

Lemma loop_replaceT_Z_fuel_PauliMult_listT : 
  forall (kfuel n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    (loop_replaceT_Z_fuel kfuel n i j k L) =
      (loop_replaceT_Z_fuel (S kfuel) n i j k L) \/
      PauliMult_listT 
        (loop_replaceT_Z_fuel kfuel n i j k L)
        (loop_replaceT_Z_fuel (S kfuel) n i j k L).
Proof. intros kfuel n i j k L H H0 H1.
  gen k L.
  induction kfuel; intros.
  - simpl. destruct k; auto.
    destruct ((length L) - S k =? j)%nat eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E'; auto.
    + right. apply PauliMult_listT_step; auto.
      * rewrite switch_len; auto.
      * exists j. exists ((length L) - S k)%nat.
        repeat (split; auto; try lia).
        intro. rewrite <- H2 in E.
        rewrite Nat.eqb_neq in E.
        contradiction.
  - simpl. destruct k; auto.
    destruct ((length L) - S k =? j)%nat eqn:E.
    + rewrite Nat.eqb_eq in E.
      assert (k <= length L)%nat by lia.
      destruct (IHkfuel k L H H0 H2); auto.
    + destruct (nth i (snd (nth ((length L) - S k) L (defaultT_I n))) gI) eqn:E';
        simpl in IHkfuel; apply IHkfuel; try rewrite switch_len; auto; try lia.
Qed.

Lemma loop_replaceT_Z_fuel_PauliMult_listT_chain : 
  forall (kfuel n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    PauliMult_listT_chain L (loop_replaceT_Z_fuel kfuel n i j k L).
Proof. intros kfuel n i j k L H H0 H1.
  induction kfuel.
  - simpl. apply PauliMult_listT_chain_id; auto.
  - pose (loop_replaceT_Z_fuel_PauliMult_listT kfuel n i j k L H H0 H1) as E.
    destruct E;
      apply PauliMult_listT_chain_append with (Lt2 := loop_replaceT_Z_fuel kfuel n i j k L);
      auto.
    + apply PauliMult_listT_chain_id; auto.
    + apply PauliMult_listT_chain_base; auto.
Qed.

Lemma loop_replaceT_Z_PauliMult_listT_chain : 
  forall (n i j k : nat) (L : list (TType n)),
    length L <> 0%nat -> (j < length L)%nat -> (k <= length L)%nat ->
    PauliMult_listT_chain L (loop_replaceT_Z n i j k L).
Proof. intros n i j k L H H0 H1.
  rewrite <- loop_replaceT_Z_fuel_saturated_base.
  apply loop_replaceT_Z_fuel_PauliMult_listT_chain; auto.
Qed.


Lemma loop_j_return_PL_PauliMult_listT_chain : 
  forall (n i j : nat) (P : list nat) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0 (length L)) ->
    PauliMult_listT_chain L (snd (loop_j_return_PL n i j P L Lz)).
Proof. intros n i j P L Lz H H0.
  gen P L Lz. induction j; intros; simpl.
  - destruct (rev Lz) eqn:E; simpl.
    + apply PauliMult_listT_chain_id; auto.
    + assert (In n0 Lz).
      { rewrite in_rev, E; constructor; auto. }
      apply H0 in H1.
      rewrite in_seq in H1.
      apply loop_replaceT_Z_PauliMult_listT_chain; auto; lia.
  - destruct (existsb (fun p : nat => p =? length L - S j)%nat P) eqn:E; auto.
    destruct (nth i (snd (nth (length L - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
    + apply loop_replaceT_XY_PauliMult_listT_chain; auto; lia.
    + apply loop_replaceT_XY_PauliMult_listT_chain; auto; lia.
    + apply IHj; auto.
      unfold incl; intros.
      inversion H1; subst; clear H1; auto.
      rewrite in_seq; lia.
Qed.

Lemma loop_normalization_fuel_PauliMult_listT_chain_Permutation : 
  forall (ifuel jfuel kfuel n i : nat) (P : list nat) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat ->
    NoDup P -> incl P (seq 0 (length L)) -> length L <> 0%nat ->
    PauliMult_listT_chain_Permutation L (loop_normalization_fuel ifuel jfuel kfuel n i P L).
Proof. intros ifuel jfuel kfuel n i P L H H0 H1 H2 H3.
  gen jfuel kfuel i P L. induction ifuel; intros.
  - simpl. constructor.
    exists L. split; try apply PauliMult_listT_chain_id; auto.
    apply final_ordering_Permutation; auto.
  - simpl. destruct i.
    + constructor.
      exists L. split; try apply PauliMult_listT_chain_id; auto.
      apply final_ordering_Permutation; auto.
    + destruct (loop_j_return_PL_fuel jfuel kfuel n (n - S i) (length L) P L []) eqn:E.
      pose (loop_j_return_PL_PauliMult_listT_chain n (n - S i) (length L) P L []) as E'.
      rewrite loop_j_return_PL_fuel_saturated in E; auto.
      rewrite E in E'. simpl in E'. 
      apply PauliMult_listT_chain_Permutation_append with (Lt2 := l0).
      * apply E'; auto; apply incl_nil_l.
      * apply IHifuel.
        -- pose (loop_j_return_PL_NoDup_P n (n - S i) (length L) P L []) as E''.
           rewrite E in E''. simpl in E''. apply E''; auto.
        -- pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
        -- pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
        -- pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''.
           pose (loop_j_return_PL_incl_P_seq_0_length_L n (n - S i) (length L) P L []) as E'''.
           rewrite E in E'''. simpl in E'''. apply E'''; auto; apply incl_nil_l.
        -- pose (loop_j_return_PL_length n (n - S i) (length L) P L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
Qed.

Lemma loop_normalization_PauliMult_listT_chain_Permutation : 
  forall (n i : nat) (P : list nat) (L : list (TType n)),
    NoDup P -> incl P (seq 0 (length L)) -> length L <> 0%nat ->
    PauliMult_listT_chain_Permutation L (loop_normalization n i P L).
Proof. intros n i P L H H0 H1. 
  rewrite <- loop_normalization_fuel_saturated_base with (kfuel := length L) (jfuel := length L);
    auto.
  apply loop_normalization_fuel_PauliMult_listT_chain_Permutation; auto.
Qed.

Lemma normalize_PauliMult_listT_chain_Permutation : forall (n : nat) (L : list (TType n)),
    length L <> 0%nat -> PauliMult_listT_chain_Permutation L (normalize L).
Proof. intros n L H. unfold normalize.
  apply loop_normalization_PauliMult_listT_chain_Permutation; auto.
  - apply NoDup_nil.
  - apply incl_nil_l.
Qed.
