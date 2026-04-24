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



Module listPauliOrdering <: UsualOrderedTypeFull'.
Definition t : Type := list Pauli.
Definition eq := @eq t.
Definition eq_equiv : Equivalence eq := eq_equivalence.

Fixpoint eqb (a b : t) : bool :=
  match a with
  | [] => match b with
         | [] => true
         | _ :: _ => false
         end
  | h1 :: t1 => match b with
              | [] => false
              | h2 :: t2 => 
                  match POrd.compare h1 h2 with
                  | Lt => false
                  | Eq => eqb t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma eqb_refl : forall (l : list Pauli),  eqb l l = true.
Proof. intros l. induction l; simpl; auto. 
  destruct a; simpl; apply IHl.
Qed. 

Lemma eqb_neq_false : forall (l1 l2 : list Pauli),  l1 <> l2 <-> eqb l1 l2 = false.
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
    rewrite eqb_refl in H.
    discriminate.
Qed.

Lemma eqb_eq_true : forall (l1 l2 : list Pauli),  l1 = l2 <-> eqb l1 l2 = true.
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
        try rewrite eqb_refl; auto.
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

Lemma eqb_sym : forall (l1 l2 : list Pauli), eqb l1 l2 = eqb l2 l1.
Proof. intros l1 l2.
  destruct (eqb l2 l1) eqn:E.
  - rewrite <- eqb_eq_true in E.
    rewrite <- eqb_eq_true.
    auto.
  - rewrite <- eqb_neq_false in E.
    rewrite <- eqb_neq_false.
    auto.
Qed.

Fixpoint lt (l1 l2 : list Pauli) :=
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
                  | Eq => lt t1 t2
                  | Gt => False
                  end
              end
  end.

Lemma lt_nil_r : forall (l : list Pauli), lt l [] = False.
Proof. intros l. destruct l; auto. Qed. 

Lemma lt_strorder : StrictOrder lt.
Proof. constructor.
  - unfold Irreflexive, Reflexive, complement in *.
    intros x H.
    induction x; simpl in *; auto.
    destruct a; simpl in *; auto.
  - unfold Transitive in *.
    intros x y z H H0.
    gen y z.
    induction x; intros; simpl in *.
    + destruct z; auto.
      rewrite lt_nil_r in H0; contradiction.
    + destruct y; simpl in *; try contradiction.
      destruct (POrd.compare a p) eqn:E;
        try contradiction.
      * rewrite POrd.compare_eq_iff in E.
        subst.
        destruct z; try contradiction.
        destruct (POrd.compare p p0) eqn:E;
          try contradiction; auto.
        apply IHx with (y := y); auto.
      * destruct z; try contradiction.
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

Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt. Proof. constructor; subst; auto. Qed.

Fixpoint ltb (l1 l2 : list Pauli) : bool :=
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
                  | Eq => ltb t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma ltb_nil_r : forall (l : list Pauli),  ltb l [] = false.
Proof. intros l. destruct l; simpl; auto. Qed. 
  
Lemma ltb_neq_or : forall (l1 l2 : list Pauli), 
    l1 <> l2 -> (ltb l1 l2) = true \/ (ltb l2 l1) = true.
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

Lemma ltb_neq_nor : forall (l1 l2 : list Pauli), 
    l1 <> l2 -> (ltb l1 l2) = false \/ (ltb l2 l1) = false.
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

Lemma lt_iff_ltb : forall (l1 l2 : list Pauli), 
    lt l1 l2 <-> ltb l1 l2 = true.
Proof. intros l1 l2. split; intro H;
    gen l2; induction l1; intros;
    destruct l2; simpl in *; auto; 
    try contradiction; try discriminate;
    destruct (POrd.compare a p) eqn:E;
    auto; try contradiction; try discriminate.
Qed. 

Definition compare (x y : t) : comparison :=
  if eqb x y then Eq else if ltb x y then Lt else Gt.

Lemma compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. unfold compare.
  destruct (eqb x y) eqn:E;
    try rewrite eqb_eq_true in E; subst;
    try rewrite <- eqb_neq_false in E;
    try constructor.
  - rewrite <- eqb_eq_true in E; auto.
  - remember E as E'. clear HeqE'.
    apply ltb_neq_or in E.
    apply ltb_neq_nor in E'.
    destruct E; destruct E'; try rewrite H in *; try discriminate.
    + constructor.
      rewrite <- lt_iff_ltb in H; auto.
    + rewrite H0. constructor.
      rewrite <- lt_iff_ltb in H; auto.
Qed.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. intros x y.
  apply (list_eq_dec POrd.eq_dec).
Qed.

Fixpoint le (l1 l2 : list Pauli) :=
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
                  | Eq => le t1 t2
                  | Gt => False
                  end
              end
  end.

Lemma le_refl : forall (l : list Pauli), le l l.
Proof. intros l. induction l; simpl; auto. 
  destruct a; simpl; apply IHl.
Qed. 

Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
Proof. intros x y. unfold eq.
  split; intro H.
  - gen y. induction x; intros.
    + destruct y; auto.
    + simpl. destruct y; simpl in *; try contradiction.
      destruct (POrd.compare a p) eqn:E; auto.
      rewrite POrd.compare_eq_iff in E; subst.
      destruct (IHx y H); subst; auto. 
  - destruct H.
    + gen y. induction x; intros;
        destruct y; simpl in *; auto.
      destruct (POrd.compare a p) eqn:E; auto.
    + subst. apply le_refl.
Qed.
(* Not needed
Fixpoint leb (l1 l2 : list Pauli) :=
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
                  | Eq => leb t1 t2
                  | Gt => false
                  end
              end
  end.
*)

Definition leb (x y : t) := orb (eqb x y) (ltb x y).
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y.
  unfold "<=?".
  destruct (eqb x y) eqn:E.
  - rewrite <- eqb_eq_true in E; subst.
    left. auto.
  - rewrite <- eqb_neq_false in E.
    remember E as E'. clear HeqE'.
    apply ltb_neq_or in E.
    apply ltb_neq_nor in E'.
    destruct E, E'; rewrite H in *; 
      try discriminate; rewrite H0 in *; auto.
    right. destruct (eqb y x); auto.
Qed.

Lemma ltb_trans : Transitive (fun x y => ltb x y = true).
Proof. unfold Transitive.
  intros l0 l1 l2 H H0.
  gen l1 l2.
  induction l0; intros.
  - simpl. destruct l2; auto.
    simpl in *. 
    rewrite ltb_nil_r in H0.
    discriminate.
  - destruct l2.
    + rewrite ltb_nil_r in *.
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
  destruct H, H0;
    try rewrite <- eqb_eq_true in *;
    subst; auto.
  right. apply ltb_trans with (y := y); auto.
Qed.

End listPauliOrdering.

Module listPOrd := listPauliOrdering <+ OrderedTypeFullFacts(listPauliOrdering) <+ Sort(listPauliOrdering).


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
Definition lt (x y : t) := listPOrd.lt (snd x) (snd y).
Lemma lt_strorder : StrictOrder lt.
Proof. destruct (listPOrd.lt_strorder).
  constructor.
  - unfold Irreflexive, Reflexive, complement, lt in *.
    intros x H. destruct x. simpl in *.
    apply (StrictOrder_Irreflexive l).
    auto.
  - unfold Transitive, lt in *.
    intros x y z H H0.
    destruct x, y, z; simpl in *; auto.
    apply (StrictOrder_Transitive _ l0 _); auto.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. constructor; intros; 
    destruct x, y, x0, y0;
    unfold eq, lt in *;
    simpl in *;
    subst; auto.
Qed.

Definition ltb (x y : t) := listPOrd.ltb (snd x) (snd y).

Definition eqb (x y : t) := listPOrd.eqb (snd x) (snd y).

Definition compare (x y : t) : comparison :=
  if eqb x y then Eq else if ltb x y then Lt else Gt.

Lemma compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. destruct x, y; unfold eq, lt, compare; simpl.
  unfold eqb, ltb; simpl.
  apply listPOrd.compare_spec.
Qed.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. intros x y.
  destruct x, y; unfold eq; simpl.
  apply listPOrd.eq_dec.
Qed.

Definition le (x y : t) := listPOrd.le (snd x) (snd y).

Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
Proof. intros x y.
  unfold le, lt, eq in *; 
    destruct x, y;
    simpl in *.
  apply listPOrd.le_lteq.
Qed.

Definition leb (x y : t) := orb (eqb x y) (ltb x y).
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y.
  unfold "<=?".
  destruct x, y; unfold eqb, ltb; simpl.
  apply listPOrd.leb_total.
Qed.

Lemma leb_trans : Transitive (fun x y => leb x y = true).
Proof. unfold Transitive, "<=?".
  intros x y z H H0. 
  destruct x, y, z; 
    unfold eqb, ltb in *;
    simpl in *.
  apply (listPOrd.leb_trans _ l0 _);
    unfold listPOrd.leb; auto.
Qed.

End TTypeOrdering.

Module TOrd := TTypeOrdering <+ OrderedTypeFullFacts(TTypeOrdering) <+ Sort (TTypeOrdering).

Definition lexicographic {n : nat} (Lt : list (TType n)) : list (TType n) := rev (TOrd.sort Lt).



Module ATypeOrdering <: OrderedTypeFull'.

Definition t : Type := list (C * (list Pauli)).
Definition eq (x y : t) := (eq (map snd x) (map snd y)).
Lemma eq_equiv : Equivalence eq.
Proof. repeat constructor.
  - unfold Symmetric, eq.
    intros x y H; destruct x, y; simpl in *; auto.
  - unfold Transitive, eq.
    intros x y z H H0.
    apply eq_trans with (y := map snd y); auto.
Qed.
Fixpoint lt (l1 l2 : t) :=
  match l1 with
  | [] => match l2 with
         | [] => False
         | _ :: _ => True
         end
  | h1 :: t1 => match l2 with
              | [] => False
              | h2 :: t2 => 
                  match TOrd.compare h1 h2 with
                  | Lt => True
                  | Eq => lt t1 t2
                  | Gt => False
                  end
              end
  end.
Lemma lt_nil_r : forall (l : t), lt l [] = False.
Proof. intros l. destruct l; auto. Qed. 
Lemma lt_strorder : StrictOrder lt.
Proof. constructor.
  - unfold Irreflexive, Reflexive, complement in *.
    intros x H.
    induction x; simpl in *; auto.
    destruct (TOrd.compare a a) eqn:E; auto.
    unfold TOrd.compare in *.
    unfold TOrd.eqb in E.
    destruct a; simpl in *.
    rewrite listPOrd.eqb_refl in E.
    discriminate.
  - unfold Transitive in *.
    intros x y z H H0.
    gen y z.
    induction x; intros; simpl in *.
    + destruct z; auto.
      rewrite lt_nil_r in H0; contradiction.
    + destruct y; simpl in *; try contradiction.
      destruct (TOrd.compare a p) eqn:E;
        try contradiction.
      * destruct a, p.
        unfold TOrd.compare in E.
        unfold TOrd.eqb in E.
        simpl in *.
        destruct (listPOrd.eqb l l0) eqn:E'.
        -- rewrite <- listPOrd.eqb_eq_true in E'. subst.
           destruct z; simpl in *; auto.
           unfold TOrd.compare in *.
           unfold TOrd.eqb, TOrd.ltb in *; simpl in *.
           destruct (listPOrd.eqb l0 (snd p)).
           ++ apply (IHx y H z H0).
           ++ destruct (listPOrd.ltb l0 (snd p)); auto.
        --  destruct (TOrd.ltb (c, l) (c0, l0)); simpl in *; discriminate.
      * destruct z; try contradiction.
        destruct (TOrd.compare p p0) eqn:E0;
          destruct (TOrd.compare a p0) eqn:E1;
          auto; try contradiction.
        -- destruct a, p, p0.
           unfold TOrd.compare in *.
           unfold TOrd.eqb in *.
           unfold TOrd.ltb in *.
           simpl in *.
           destruct (listPOrd.eqb l0 l1) eqn:E0'. 
           2: destruct (listPOrd.ltb l0 l1); discriminate.
           destruct (listPOrd.eqb l l1) eqn:E1'. 
           2: destruct (listPOrd.ltb l l1); discriminate.
           rewrite <- listPOrd.eqb_eq_true in *.
           subst.
           destruct (listPOrd.eqb l1 l1); try discriminate.
           destruct (listPOrd.ltb l1 l1) eqn:E'; try discriminate.
           pose listPOrd.lt_strorder as H1.
           inversion H1.
           unfold Irreflexive in StrictOrder_Irreflexive.
           unfold Reflexive, complement in StrictOrder_Irreflexive.
           rewrite <- listPOrd.lt_iff_ltb in E'. 
           apply StrictOrder_Irreflexive in E'.
           contradiction.
        -- destruct a, p, p0.
           unfold TOrd.compare in *.
           unfold TOrd.eqb in *.
           unfold TOrd.ltb in *.
           simpl in *.
           destruct (listPOrd.eqb l0 l1) eqn:E0'. 
           2: destruct (listPOrd.ltb l0 l1); discriminate.
           rewrite <- listPOrd.eqb_eq_true in *.
           subst.
           destruct (listPOrd.eqb l l1); try discriminate.
           destruct (listPOrd.ltb l l1); try discriminate.
        -- destruct a, p, p0.
           unfold TOrd.compare in *.
           unfold TOrd.eqb in *.
           unfold TOrd.ltb in *.
           simpl in *.
           destruct (listPOrd.eqb l l1) eqn:E1'. 
           2: destruct (listPOrd.ltb l l1); discriminate.
           rewrite <- listPOrd.eqb_eq_true in *.
           subst.
           rewrite listPOrd.eqb_sym in E.
           destruct (listPOrd.eqb l0 l1); try discriminate.
           destruct (listPOrd.ltb l1 l0) eqn:E'; try discriminate.
           destruct (listPOrd.ltb l0 l1) eqn:E''; try discriminate.
           rewrite <- listPOrd.lt_iff_ltb in E', E''.
           pose listPOrd.lt_strorder as H1.
           inversion H1.
           unfold Irreflexive, Transitive in *.
           unfold Reflexive, complement in *.
           specialize (StrictOrder_Transitive l1 l0 l1 E' E'').
           apply StrictOrder_Irreflexive in StrictOrder_Transitive.
           contradiction.
        -- destruct a, p, p0.
           unfold TOrd.compare in *.
           unfold TOrd.eqb in *.
           unfold TOrd.ltb in *.
           simpl in *.
           destruct (listPOrd.eqb l0 l1) eqn:E0'; try discriminate. 
           destruct (listPOrd.ltb l0 l1) eqn:E0''; try discriminate.
           destruct (listPOrd.eqb l l0) eqn:E'; try discriminate. 
           destruct (listPOrd.ltb l l0) eqn:E''; try discriminate.
           destruct (listPOrd.eqb l l1) eqn:E1'; try discriminate. 
           destruct (listPOrd.ltb l l1) eqn:E1''; try discriminate.
           rewrite <- listPOrd.lt_iff_ltb in *.
           pose listPOrd.lt_strorder as H1.
           inversion H1.
           unfold Irreflexive, Transitive in *.
           unfold Reflexive, complement in *.
           specialize (StrictOrder_Transitive l l0 l1 E'' E0'').
           rewrite listPOrd.lt_iff_ltb in StrictOrder_Transitive.
           rewrite E1'' in StrictOrder_Transitive.
           discriminate.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. constructor; unfold eq in *.
  - gen x0 y y0.
    induction x; intros.
    + simpl in*.
      symmetry in H.
      apply map_eq_nil in H.
      subst.
      simpl.
      destruct x0; try contradiction.
      rewrite map_cons in H0.
      destruct y0; simpl in *; try discriminate.
      auto.
    + rewrite map_cons in H.
      destruct y; simpl in *; try discriminate.
      destruct x0; simpl in *; try contradiction.
      destruct y0; simpl in *; try discriminate.
      inversion H.
      inversion H0.
      unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct a, p, p0, p1.
      simpl in *.
      subst.
      destruct (listPOrd.eqb l0 l2) eqn:E.
      * specialize (IHx x0 y H4 y0 H6 H1).
        auto.
      * destruct (listPOrd.ltb l0 l2) eqn:E'; try contradiction; auto.
  - gen y0 x x0.
    induction y; intros.
    + simpl in*.
      apply map_eq_nil in H.
      subst.
      simpl.
      destruct y0; try contradiction.
      rewrite map_cons in H0.
      destruct x0; simpl in *; try discriminate.
      auto.
    + rewrite map_cons in H.
      destruct x; simpl in *; try discriminate.
      destruct y0; simpl in *; try contradiction.
      destruct x0; simpl in *; try discriminate.
      inversion H.
      inversion H0.
      unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct a, p, p0, p1.
      simpl in *.
      subst.
      destruct (listPOrd.eqb l l1) eqn:E.
      * specialize (IHy y0 x H4 x0 H6 H1).
        auto.
      * destruct (listPOrd.ltb l l1) eqn:E'; try contradiction; auto.
Qed.

Fixpoint ltb (l1 l2 : t) :=
  match l1 with
  | [] => match l2 with
         | [] => false
         | _ :: _ => true
         end
  | h1 :: t1 => match l2 with
              | [] => false
              | h2 :: t2 => 
                  match TOrd.compare h1 h2 with
                  | Lt => true
                  | Eq => ltb t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma ltb_nil_r : forall (l : t),  ltb l [] = false.
Proof. intros l. destruct l; simpl; auto. Qed. 

Lemma lt_iff_ltb : forall (l1 l2 : t), 
    lt l1 l2 <-> ltb l1 l2 = true.
Proof. intros l1 l2. split; intro H;
    gen l2; induction l1; intros;
    destruct l2; simpl in *; auto; 
    try contradiction; try discriminate;
    destruct (TOrd.compare a p) eqn:E;
    auto; try contradiction; try discriminate.
Qed. 

Lemma ltb_neq_or : forall (l1 l2 : t), 
    map snd l1 <> map snd l2 -> (ltb l1 l2) = true \/ (ltb l2 l1) = true.
Proof. intros l1 l2 H.
  gen l2.
  induction l1; intros.
  - destruct l2; try contradiction; simpl; auto.
  - destruct l2; simpl in *; auto.
    destruct (TOrd.compare a p) eqn:E; auto.
    + unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'.
      2: destruct ( listPOrd.ltb (snd a) (snd p)); try discriminate.
      rewrite <- listPOrd.eqb_eq_true in E'.
      rewrite E' in *.
      rewrite listPOrd.eqb_refl.
      apply IHl1.
      intro H'. rewrite H' in *. contradiction.
    + right. 
      unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'; try discriminate.
      destruct (listPOrd.eqb (snd p) (snd a)) eqn:E''.
      * rewrite <- listPOrd.eqb_eq_true in E''.
        rewrite E'' in *.
        rewrite listPOrd.eqb_refl in E'.
        discriminate.
      * assert (snd a <> snd p).
        { intro H'; rewrite H' in *; rewrite listPOrd.eqb_refl in *; discriminate. }
        remember H0 as H0'. clear HeqH0'.
        apply listPOrd.ltb_neq_or in H0.
        apply listPOrd.ltb_neq_nor in H0'.
        destruct H0, H0'; rewrite H0 in *; try discriminate; auto.
Qed.

Lemma ltb_neq_nor : forall (l1 l2 : t), 
    map snd l1 <> map snd l2 -> (ltb l1 l2) = false \/ (ltb l2 l1) = false.
Proof. intros l1 l2 H.
    gen l2.
  induction l1; intros.
  - destruct l2; try contradiction; simpl; auto.
  - destruct l2; simpl in *; auto.
    destruct (TOrd.compare a p) eqn:E; auto.
    + unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'.
      2: destruct ( listPOrd.ltb (snd a) (snd p)); try discriminate.
      rewrite <- listPOrd.eqb_eq_true in E'.
      rewrite E' in *.
      rewrite listPOrd.eqb_refl.
      apply IHl1.
      intro H'. rewrite H' in *. contradiction.
    + right. 
      unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'; try discriminate.
      destruct (listPOrd.eqb (snd p) (snd a)) eqn:E''.
      * rewrite <- listPOrd.eqb_eq_true in E''.
        rewrite E'' in *.
        rewrite listPOrd.eqb_refl in E'.
        discriminate.
      * assert (snd a <> snd p).
        { intro H'; rewrite H' in *; rewrite listPOrd.eqb_refl in *; discriminate. }
        remember H0 as H0'. clear HeqH0'.
        apply listPOrd.ltb_neq_or in H0.
        apply listPOrd.ltb_neq_nor in H0'.
        destruct H0, H0'; rewrite H1 in *; try discriminate; auto.
Qed.


Fixpoint eqb (a b : t) : bool :=
  match a with
  | [] => match b with
         | [] => true
         | _ :: _ => false
         end
  | h1 :: t1 => match b with
              | [] => false
              | h2 :: t2 => 
                  match TOrd.compare h1 h2 with
                  | Lt => false
                  | Eq => eqb t1 t2
                  | Gt => false
                  end
              end
  end.

Lemma eqb_refl : forall (l : t),  eqb l l = true.
Proof. intros l. induction l; simpl; auto.
  destruct a.
  unfold TOrd.compare.
  unfold TOrd.eqb, TOrd.ltb.
  simpl.
  rewrite listPOrd.eqb_refl.
  apply IHl.
Qed. 

Lemma eqb_neq_false : forall (l1 l2 : t),  map snd l1 <> map snd l2 <-> eqb l1 l2 = false.
Proof. intros l1 l2. split; intro H.
  - gen l2.
    induction l1; intros.
    + destruct l2; try contradiction; simpl; auto.
    + simpl. 
      destruct l2; auto.
      destruct (TOrd.compare a p) eqn:E; auto.
      unfold TOrd.compare in E.
      unfold TOrd.eqb, TOrd.ltb in E.
      destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'.
      2: destruct (listPOrd.ltb (snd a) (snd p)); discriminate.
      rewrite <- listPOrd.eqb_eq_true in E'; subst.
      rewrite ! map_cons in *.
      rewrite E' in *.
      assert (map snd l1 <> map snd l2).
      { intro H'; rewrite H' in *; contradiction. }
      apply IHl1; auto.
  - intro.
    gen l2. induction l1; intros; simpl in *.
    + destruct l2; try discriminate.
    + destruct l2; simpl in *; try discriminate.
      inversion H0.
      destruct (TOrd.compare a p) eqn:E.
      * specialize (IHl1 l2 H H3).
        contradiction.
      * unfold TOrd.compare in *.
        unfold TOrd.eqb, TOrd.ltb in *.
        rewrite H2 in *.
        rewrite listPOrd.eqb_refl in E.
        discriminate.
      * unfold TOrd.compare in *.
        unfold TOrd.eqb, TOrd.ltb in *.
        rewrite H2 in *.
        rewrite listPOrd.eqb_refl in E.
        discriminate.
Qed.

Lemma eqb_eq_true : forall (l1 l2 : t),  map snd l1 = map snd l2 <-> eqb l1 l2 = true.
Proof. intros l1 l2. split; intro H.
  - gen l2.
    induction l1; intros.
    + destruct l2; auto; discriminate.
    + simpl. 
      destruct l2; try discriminate.
      inversion H.
      unfold TOrd.compare in *.
      unfold TOrd.eqb, TOrd.ltb in *.
      rewrite H1.
      rewrite listPOrd.eqb_refl.
      apply IHl1; auto.
  - gen l2. induction l1; intros.
    + destruct l2; simpl in *; auto; discriminate.
    + destruct l2.
      * simpl in *; discriminate.
      * simpl in *.
        destruct (TOrd.compare a p) eqn:E;
          simpl in *; try discriminate.
        unfold TOrd.compare in E.
        unfold TOrd.eqb, TOrd.ltb in *.
        destruct (listPOrd.eqb (snd a) (snd p)) eqn:E'.
        2: destruct (listPOrd.ltb (snd a) (snd p)); discriminate.
        rewrite <- listPOrd.eqb_eq_true in E'.
        rewrite E'.
        f_equal.
        apply IHl1; auto.
Qed.

Lemma eqb_sym : forall (l1 l2 : t), eqb l1 l2 = eqb l2 l1.
Proof. intros l1 l2.
  destruct (eqb l2 l1) eqn:E.
  - rewrite <- eqb_eq_true in E.
    rewrite <- eqb_eq_true.
    auto.
  - rewrite <- eqb_neq_false in E.
    rewrite <- eqb_neq_false.
    auto.
Qed.

Definition compare (x y : t) : comparison :=
  if eqb x y then Eq else if ltb x y then Lt else Gt.

Lemma compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. unfold compare.
  destruct (eqb x y) eqn:E;
    try rewrite eqb_eq_true in E; subst;
    try rewrite <- eqb_neq_false in E;
    try constructor.
  - rewrite <- eqb_eq_true in E; auto.
  - remember E as E'. clear HeqE'.
    apply ltb_neq_or in E.
    apply ltb_neq_nor in E'.
    destruct E; destruct E'; try rewrite H in *; try discriminate.
    + constructor.
      rewrite <- lt_iff_ltb in H; auto.
    + rewrite H0. constructor.
      rewrite <- lt_iff_ltb in H; auto.
Qed.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. intros x y.
  apply list_eq_dec.
  apply listPOrd.eq_dec.
Qed.

Fixpoint le (l1 l2 : t) :=
  match l1 with
  | [] => match l2 with
         | [] => True
         | _ :: _ => True
         end
  | h1 :: t1 => match l2 with
              | [] => False
              | h2 :: t2 => 
                  match TOrd.compare h1 h2 with
                  | Lt => True
                  | Eq => le t1 t2
                  | Gt => False
                  end
              end
  end.

Lemma le_refl : forall (l1 l2 : t), map snd l1 = map snd l2 -> le l1 l2.
Proof. induction l1; intros; destruct l2; simpl in *; try discriminate; auto.
  inversion H.
  unfold TOrd.compare.
  unfold TOrd.eqb, TOrd.ltb.
  rewrite H1 in *.
  rewrite listPOrd.eqb_refl.
  auto.
Qed. 

Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
Proof. intros x y. unfold eq.
  split; intro H.
  - gen y. induction x; intros.
    + destruct y; auto.
    + simpl. destruct y; simpl in *; try contradiction.
      destruct (TOrd.compare a p) eqn:E; auto.
      rewrite TOrd.compare_eq_iff in E; subst.
      destruct (IHx y H); auto.
      right. rewrite E, H0; auto.
  - destruct H.
    + gen y. induction x; intros;
        destruct y; simpl in *; auto.
      destruct (TOrd.compare a p) eqn:E; auto.
    + apply le_refl; auto.
Qed.

Definition leb (x y : t) := orb (eqb x y) (ltb x y).
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y.
  unfold "<=?".
  destruct (eqb x y) eqn:E.
  - rewrite <- eqb_eq_true in E; subst.
    left. auto.
  - rewrite <- eqb_neq_false in E.
    remember E as E'. clear HeqE'.
    apply ltb_neq_or in E.
    apply ltb_neq_nor in E'.
    destruct E, E'; rewrite H in *; 
      try discriminate; rewrite H0 in *; auto.
    right. destruct (eqb y x); auto.
Qed.

Lemma ltb_trans : Transitive (fun x y => ltb x y = true).
Proof. unfold Transitive.
  intros l0 l1 l2 H H0.
  gen l1 l2.
  induction l0; intros.
  - simpl. destruct l2; auto.
    simpl in *. 
    rewrite ltb_nil_r in H0.
    discriminate.
  - destruct l2.
    + rewrite ltb_nil_r in *.
      discriminate.
    + simpl in *.
      destruct l1; try discriminate.
      simpl in *.
      destruct (TOrd.compare a p0) eqn:E;
        simpl in *; try discriminate.
      * rewrite TOrd.compare_eq_iff in E.
        destruct (TOrd.compare p0 p) eqn:E';
          auto; try discriminate.
        -- rewrite TOrd.compare_eq_iff in E'.
           rewrite E' in E.
           unfold TOrd.compare.
           unfold TOrd.eqb, TOrd.ltb.
           rewrite E.
           rewrite listPOrd.eqb_refl.
           apply (IHl0 l1); auto.
        -- rewrite TOrd.compare_lt_iff in E'.
           unfold TOrd.compare.
           unfold TOrd.eqb, TOrd.ltb.
           rewrite E.
           destruct (listPOrd.eqb (snd p0) (snd p)) eqn:E''.
           ++ rewrite <- listPOrd.eqb_eq_true in E''.
              rewrite E'' in *.
              pose listPOrd.lt_strorder as H'.
              inversion H'.
              unfold Irreflexive in *.
              unfold Reflexive, complement in *.
              apply StrictOrder_Irreflexive in E'.
              contradiction.
           ++ rewrite listPOrd.lt_iff_ltb in E'.
              rewrite E'.
              auto.
      * destruct (TOrd.compare p0 p) eqn:E';
          try discriminate.
        -- rewrite TOrd.compare_eq_iff in E'.
           rewrite TOrd.compare_lt_iff in E.
           rewrite E' in *.
           unfold TOrd.compare in *.
           unfold TOrd.eqb, TOrd.ltb in *.
           destruct (listPOrd.eqb (snd a) (snd p)) eqn:E''.
           ++ rewrite <- listPOrd.eqb_eq_true in E''.
              rewrite E'' in *.
              pose listPOrd.lt_strorder as H'.
              inversion H'.
              unfold Irreflexive in *.
              unfold Reflexive, complement in *.
              apply StrictOrder_Irreflexive in E.
              contradiction.
           ++ rewrite listPOrd.lt_iff_ltb in E.
              rewrite E. auto.
        -- rewrite TOrd.compare_lt_iff in *.
           pose listPOrd.ltb_trans as H1.
           unfold Transitive in H1.
           rewrite listPOrd.lt_iff_ltb in *.
           specialize (H1 (snd a) (snd p0) (snd p) E E').
           unfold TOrd.compare in *.
           unfold TOrd.eqb, TOrd.ltb in *.
           destruct (listPOrd.eqb (snd a) (snd p)) eqn:E''.
           ++ rewrite <- listPOrd.eqb_eq_true in E''.
              rewrite E'' in *.
              rewrite <- listPOrd.lt_iff_ltb in *.
              pose listPOrd.lt_strorder as H'.
              inversion H'.
              unfold Irreflexive in *.
              unfold Reflexive, complement in *.
              apply StrictOrder_Irreflexive in H1.
              contradiction.
           ++ rewrite H1. auto.
Qed.

Lemma leb_trans : Transitive (fun x y => leb x y = true).
Proof. unfold Transitive, "<=?".
  intros x y z H H0.
  rewrite orb_true_iff in *.
  destruct H as [H | H']; destruct H0 as [H0 | H0'];
    try rewrite <- eqb_eq_true in *;
    try rewrite <- lt_iff_ltb in *;
    try rewrite H, H0 in *; auto.
  - right. 
    assert (H1 : map snd z = map snd z) by auto.
    apply (lt_compat x y H z z H1); auto.
  - right. 
    assert (H1 : map snd x = map snd x) by auto.
    apply (lt_compat x x H1 y z H0); auto.
  - right.
    pose lt_strorder as H1.
    inversion H1.
    unfold Transitive in *.
    apply StrictOrder_Transitive with (y := y); auto.
Qed.

End ATypeOrdering.

Module AOrd := ATypeOrdering <+ OrderedTypeFullFacts(ATypeOrdering) <+ Sort (ATypeOrdering).






(*** Normalization ***)


(*** Development of TTypeB ***)

(*
(a,b) => (-1)^a * (Ci)^b
(false,false) => C1
(true,false) => -C1
(false,true) => Ci
(true,true) => -Ci
*)
Inductive CB : Set :=
| cb (a b : bool).

Definition CBmult (a b : CB) : CB :=
  match a, b with
  | (cb false false), (cb false false) => cb false false
  | (cb false false), (cb true false) => cb true false
  | (cb false false), (cb false true) => cb false true
  | (cb false false), (cb true true) => cb true true

  | (cb true false), (cb false false) => cb true false
  | (cb true false), (cb true false) => cb false false
  | (cb true false), (cb false true) => cb true true
  | (cb true false), (cb true true) => cb false true

  | (cb false true), (cb false false) => cb false true
  | (cb false true), (cb true false) => cb true true
  | (cb false true), (cb false true) => cb true false
  | (cb false true), (cb true true) => cb false false

  | (cb true true), (cb false false) => cb true true
  | (cb true true), (cb true false) => cb false true
  | (cb true true), (cb false true) => cb false false
  | (cb true true), (cb true true) => cb true false
  end. 

Definition CBopp (a : CB) : CB :=
  match a with
  | cb false false => cb true false
  | cb true false => cb false false
  | cb false true => cb true true
  | cb true true => cb false true
  end. 

Definition CBtoC (a : CB) : C :=
  match a with
  | cb false false => C1
  | cb true false => - C1
  | cb false true => Ci
  | cb true true => - Ci
  end. 

Lemma CBtoC_respects_mult (a b : CB) :
  (CBtoC (CBmult a b)) = (CBtoC a) * (CBtoC b).
Proof. destruct a as [a0 a1]; 
    destruct b as [b0 b1];
    destruct a0, a1, b0, b1;
    simpl; lca.
Qed.

Lemma CBtoC_respects_opp (a : CB) :
  (CBtoC (CBopp a)) = (Copp (CBtoC a)).
Proof. destruct a as [a0 a1]; 
    destruct a0, a1;
    simpl; lca.
Qed.

Definition TTypeB (n : nat) := (CB * list Pauli)%type.

Definition TTypeBtoTType {n : nat} (tb : TTypeB n) : TType n := (CBtoC (fst tb), snd tb).

Definition gMul_CB (g1 g2 : Pauli) : CB :=
  match g1, g2 with
  | gI, _ => cb false false
  | _, gI => cb false false
  | gX, gX => cb false false
  | gY, gY => cb false false
  | gZ, gZ => cb false false
  | gX, gY => cb false true
  | gY, gX => cb true true
  | gX, gZ => cb true true
  | gZ, gX => cb false true
  | gY, gZ => cb false true
  | gZ, gY => cb true true
  end.

Lemma CBtoC_respects_gMul_C (p p' : Pauli):
  CBtoC (gMul_CB p p') = gMul_Coef p p'.
Proof. destruct p, p'; auto. Qed.

Definition cbBigMul (cbs : list CB) : CB :=
  fold_right CBmult (cb false false) cbs.

Definition gMulTB {n : nat} (tb tb' : TTypeB n) : TTypeB n :=
  (CBmult (CBmult (fst tb) (fst tb')) (cbBigMul (zipWith gMul_CB (snd tb) (snd  tb'))),
    zipWith gMul_base (snd tb) (snd tb')).

Lemma TTypeBtoTType_respects_mult {n : nat} (tb tb' : TTypeB n):
  TTypeBtoTType (gMulTB tb tb') = gMulT (TTypeBtoTType tb) (TTypeBtoTType tb').
Proof. destruct tb as [cb ps];
    destruct tb' as [cb' ps'].
  unfold TTypeBtoTType. simpl.
  f_equal.
  rewrite ! CBtoC_respects_mult.
  do 2 f_equal.
  gen ps'. induction ps; intros; auto.
  destruct ps'; auto.
  unfold zipWith in *. simpl.
  rewrite CBtoC_respects_mult.
  rewrite CBtoC_respects_gMul_C.
  unfold cBigMul in *. simpl.
  rewrite fold_left_Cmult.
  f_equal.
  unfold cbBigMul in *. auto.
Qed.

Definition defaultTB_I (n : nat) := (cb false false, repeat gI n).




Module TTypeBOrdering <: OrderedTypeFull'.

Definition t : Type := CB * (list Pauli).
Definition eq (x y : t) := (eq (snd x) (snd y)).
Lemma eq_equiv : Equivalence eq.
Proof. repeat constructor.
  - unfold Symmetric, eq.
    intros x y H; destruct x, y; simpl in *; auto.
  - unfold Transitive, eq.
    intros x y z H H0; destruct x, y, z; simpl in *.
    apply eq_trans with (y := l0); auto.
Qed.
Definition lt (x y : t) := listPOrd.lt (snd x) (snd y).
Lemma lt_strorder : StrictOrder lt.
Proof. destruct (listPOrd.lt_strorder).
  constructor.
  - unfold Irreflexive, Reflexive, complement, lt in *.
    intros x H. destruct x. simpl in *.
    apply (StrictOrder_Irreflexive l).
    auto.
  - unfold Transitive, lt in *.
    intros x y z H H0.
    destruct x, y, z; simpl in *; auto.
    apply (StrictOrder_Transitive _ l0 _); auto.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof. constructor; intros; 
    destruct x, y, x0, y0;
    unfold eq, lt in *;
    simpl in *;
    subst; auto.
Qed.

Definition ltb (x y : t) := listPOrd.ltb (snd x) (snd y).

Definition eqb (x y : t) := listPOrd.eqb (snd x) (snd y).

Definition compare (x y : t) : comparison :=
  if eqb x y then Eq else if ltb x y then Lt else Gt.

Lemma compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. destruct x, y; unfold eq, lt, compare; simpl.
  unfold eqb, ltb; simpl.
  apply listPOrd.compare_spec.
Qed.

Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. intros x y.
  destruct x, y; unfold eq; simpl.
  apply listPOrd.eq_dec.
Qed.

Definition le (x y : t) := listPOrd.le (snd x) (snd y).

Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
Proof. intros x y.
  unfold le, lt, eq in *; 
    destruct x, y;
    simpl in *.
  apply listPOrd.le_lteq.
Qed.

Definition leb (x y : t) := orb (eqb x y) (ltb x y).
Infix "<=?" := leb (at level 70).
Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
Proof. intros x y.
  unfold "<=?".
  destruct x, y; unfold eqb, ltb; simpl.
  apply listPOrd.leb_total.
Qed.

Lemma leb_trans : Transitive (fun x y => leb x y = true).
Proof. unfold Transitive, "<=?".
  intros x y z H H0. 
  destruct x, y, z; 
    unfold eqb, ltb in *;
    simpl in *.
  apply (listPOrd.leb_trans _ l0 _);
    unfold listPOrd.leb; auto.
Qed.

End TTypeBOrdering.

Module TBOrd := TTypeBOrdering <+ OrderedTypeFullFacts(TTypeBOrdering) <+ Sort (TTypeBOrdering).

Definition lexicographicB {n : nat} (LtB : list (TTypeB n)) : list (TTypeB n) := rev (TBOrd.sort LtB).


Lemma merge_helper1 (l0 : list (CB * list Pauli)) (l : list (CB * list Pauli)):
  map (fun a : CB * list Pauli => (CBtoC (fst a), snd a)) (TBOrd.merge l0 l) =
  TOrd.merge (map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb)) l0)
    (map (fun a : CB * list Pauli => (CBtoC (fst a), snd a)) l).
Proof. gen l. induction l0; intros; simpl; auto.
  - assert ((fix merge_aux (l2 : list (CB * list Pauli)) : list (CB * list Pauli) := l2) = (fun t => t)).
    { apply functional_extensionality. intros. destruct x; auto. }
    assert ((fix merge_aux (l2 : list (C * list Pauli)) : list (C * list Pauli) := l2) = (fun t => t)).
    { apply functional_extensionality. intros. destruct x; auto. }
    rewrite H, H0. auto.
  - unfold TTypeBOrdering.eqb, TTypeBOrdering.ltb, TTypeOrdering.eqb, TTypeOrdering.ltb.
    induction l; simpl; auto.
    destruct (listPOrd.eqb (snd a) (snd a0) || listPOrd.ltb (snd a) (snd a0)) eqn:E; simpl; auto.
    + f_equal. auto.
    + f_equal. auto.
Qed.

Lemma merge_helper2 (stack : list (option (list (CB * list Pauli)))) l:
  map
    (fun t : option (list (CB * list Pauli)) =>
     match t with
     | Some LTB =>
         Some (map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb)) LTB)
     | None => None
     end) (TBOrd.merge_list_to_stack stack l) =
  TOrd.merge_list_to_stack
    (map
       (fun t : option (list (CB * list Pauli)) =>
        match t with
        | Some LTB =>
            Some (map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb)) LTB)
        | None => None
        end) stack) (map (fun a => (CBtoC (fst a), snd a)) l).
Proof. gen l. induction stack; intros; simpl; auto.
  destruct a; simpl; auto.
  f_equal. rewrite IHstack.
  f_equal. clear IHstack.
  apply merge_helper1.
Qed.

Lemma merge_helper3 (a : CB * list Pauli) (l : list (CB * list Pauli)) l0:
  map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb))
    ((fix merge_aux (l2 : list (CB * list Pauli)) : list (CB * list Pauli) :=
        match l2 with
        | [] => a :: l
        | a2 :: l2' =>
            if listPOrd.eqb (snd a) (snd a2) || listPOrd.ltb (snd a) (snd a2)
            then a :: TBOrd.merge l l2
            else a2 :: merge_aux l2'
        end) l0) =
  (fix merge_aux (l2 : list (C * list Pauli)) : list (C * list Pauli) :=
     match l2 with
     | [] =>
         (CBtoC (fst a), snd a)
         :: map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb)) l
     | a2 :: l2' =>
         if
          listPOrd.eqb (snd (CBtoC (fst a), snd a)) (snd a2)
          || listPOrd.ltb (snd (CBtoC (fst a), snd a)) (snd a2)
         then
          (CBtoC (fst a), snd a)
          :: TOrd.merge
               (map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb)) l) l2
         else a2 :: merge_aux l2'
     end)
    (map (fun tb : CB * list Pauli => (CBtoC (fst tb), snd tb))
       l0).
Proof. gen a l. induction l0; intros; simpl; auto.
  destruct (listPOrd.eqb (snd a0) (snd a) || listPOrd.ltb (snd a0) (snd a)) eqn:E; simpl; auto.
  - f_equal. 
    gen a l0. induction l; intros; simpl; auto.
    unfold TTypeBOrdering.eqb, TTypeBOrdering.ltb, TTypeOrdering.eqb, TTypeOrdering.ltb.
    simpl.
    destruct (listPOrd.eqb (snd a) (snd a1) || listPOrd.ltb (snd a) (snd a1)) eqn:E'; simpl; auto.
    + f_equal. auto.
    + f_equal. auto.
  - f_equal. auto.
Qed.

Definition stack_map_helper (stack : list (option (list (CB * list Pauli)))) : list (option (list (C * list Pauli))) :=
  map (fun t => match t with None => None | Some LTB => Some (map (fun tb => (CBtoC (fst tb), snd tb)) LTB) end) stack.

Lemma merge_helper4 (LtB : list (CB * list Pauli)) (stack : list (option (list (CB * list Pauli)))):
 map (fun tb => (CBtoC (fst tb), snd tb)) (TBOrd.iter_merge stack LtB) =
   TOrd.iter_merge (stack_map_helper stack) (map (fun tb => (CBtoC (fst tb), snd tb)) LtB).
Proof. gen stack. unfold stack_map_helper.
  induction LtB; intros; simpl; auto.
  - induction stack; simpl; auto.
    destruct a; simpl; auto.
    induction l; simpl; auto.
    + assert ((fix merge_aux (l2 : list (CB * list Pauli)) : list (CB * list Pauli) := l2) = (fun t => t)).
      { apply functional_extensionality. intros. destruct x; auto. }
      assert ((fix merge_aux (l2 : list (C * list Pauli)) : list (C * list Pauli) := l2) = (fun t => t)).
      { apply functional_extensionality. intros. destruct x; auto. }
      rewrite ! H, ! H0. auto.
    + unfold TTypeBOrdering.eqb, TTypeBOrdering.ltb, TTypeOrdering.eqb, TTypeOrdering.ltb.
      rewrite <- IHstack.
      clear IHstack.
      apply merge_helper3.
  - rewrite IHLtB.
    f_equal.
    clear IHLtB.
    apply merge_helper2.
Qed.

Lemma TTypeBtoTType_respects_lexicographic {n : nat} (LtB : list (TTypeB n)):
  map TTypeBtoTType (lexicographicB LtB) = lexicographic (map TTypeBtoTType LtB).
Proof. unfold lexicographic, lexicographicB.
  rewrite map_rev. f_equal.
  unfold TOrd.sort, TBOrd.sort.
  unfold TTypeBtoTType.
  induction LtB; auto.
  simpl. destruct a. simpl.
  apply merge_helper4.
Qed.



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



(** ** Version with TTypeB and gMulTB ** **)
(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceTB_XY (n i j k  : nat) (L : list (TTypeB n)) {struct k} : list (TTypeB n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb ((length L) - k) j
    then loop_replaceTB_XY n i j k' L
    else 
      match nth i (snd (nth ((length L) - k) L (defaultTB_I n))) gI with
      | gX | gY => loop_replaceTB_XY n i j k' (switch L (gMulTB (nth j L (defaultTB_I n)) (nth ((length L) - k) L (defaultTB_I n))) ((length L) - k))
      | _ => loop_replaceTB_XY n i j k' L
      end
end.

(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceTB_Z (n i j k : nat) (L : list (TTypeB n)) {struct k} : list (TTypeB n) :=
match k with
| 0%nat => L
| S k' => 
    if Nat.eqb ((length L) - k) j
    then loop_replaceTB_Z n i j k' L
    else 
      match nth i (snd (nth ((length L) - k) L (defaultTB_I n))) gI with
      | gZ => loop_replaceTB_Z n i j k' (switch L (gMulTB (nth j L (defaultTB_I n)) (nth ((length L) - k) L (defaultTB_I n))) ((length L) - k))
      | _ => loop_replaceTB_Z n i j k' L
      end
end.

(** j := length L
     Lz := []
     n, i   < fixed > **)
Fixpoint loop_j_return_QPLB (n i j : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) (Lz : list nat) : (list (nat * nat)) * (list (TTypeB n)) := 
  match j with
  | S j' => 
      if (existsb (fun qp : nat * nat => Nat.eqb (snd qp) ((length LB) - j)%nat) QP) 
      then
        (* loop on next j *)
        loop_j_return_QPLB n i j' QP LB Lz
      else 
        match nth i (snd (nth ((length LB) - j)%nat LB (defaultTB_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_QPLB n i j' QP LB Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_QPLB n i j' QP LB (((length LB) - j)%nat :: Lz)
        | _ => 
            (* add j to QP and return QP, (loop_replaceTB_XY n i j (length LB) LB) *)
            (((i,((length LB) - j)%nat) :: QP), (loop_replaceTB_XY n i ((length LB) - j)%nat (length LB) LB))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return QP, LB *)
          (QP, LB)
      | h :: _ => 
          (* add j to QP and return QP, (loop_replaceTB_Z n i j (length LB) LB) *)
          (((i,h) :: QP), (loop_replaceTB_Z n i h (length LB) LB))
      end
  end.

(** lq := qubit_order <fixed>
              ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n)))
     i := n
     n := initialized from input   < fixed >
     QP := []
     L := initialized from input **)
Fixpoint loop_normalizationB (lq : list nat) (n i : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) {struct i} : (list (nat * nat)) * (list (TTypeB n)) :=
  match i with
  | S i' =>
      (* do loop_j_return_QPLB and get (QP, LB), recurse on next i *)
      let (QP', LB') := loop_j_return_QPLB n (nth (n - i)%nat lq 0%nat) (length LB) QP LB [] in
      loop_normalizationB lq n i' QP' LB'
  | 0%nat => (QP, LB)
  end.

Definition loop_normalizationB_final (lq : list nat) (n i : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) : list ((option nat) * TTypeB n)  :=
  let (QP, LB) := loop_normalizationB lq n i QP LB in
  let noP := (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP))) (List.seq 0 (length LB))) in
  (* Final Ordering with rev QP *)
  (map (fun qp : nat * nat => (Some (fst qp), nth (snd qp) LB (defaultTB_I n))) (rev QP)) ++ 
    combine (repeat None (length noP)) (lexicographicB (map (fun p : nat => nth p LB (defaultTB_I n)) noP)).


(** Generalized version of normalization: 
Can change where to start the loop in the qubits.
start=0: qubit order -> 0,1,2,3,4,5,...,n-1
start=a: qubit order -> a,a+1,...,n-1,0,1,2,...,a-1 **)
(**  : list (TType n) 
      start := where to start loop
**)
Definition pivots_normalizeB (start : nat) {n : nat} (LB : list (TTypeB n)) : list ((option nat) * TTypeB n)  := 
  loop_normalizationB_final ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n))) n n [] LB.

Definition normalizeB (start : nat) {n : nat} (LB : list (TTypeB n)) := 
  map snd (pivots_normalizeB start LB).

Definition pivot_searchB {n} (lqtb : list ((option nat) * (TTypeB n))) (i : nat) : Pauli :=
  match find (fun qtb =>
                match fst qtb with
                | Some q => Nat.eqb i q
                | None => false
                end) lqtb 
  with
  | None => gI
  | Some qtb => nth i (snd (snd qtb)) gI
  end.

Definition pivotsB (start : nat) {n : nat} (LB : list (TTypeB n)) : list (nat * Pauli) :=
  let LQTB := (pivots_normalizeB start LB) in
  map 
    (fun i => (i, pivot_searchB LQTB i))
    (List.seq 0 (length LB)).


Lemma loop_replaceTB_XY_nil : forall (n i j k : nat), loop_replaceTB_XY n i j k [] = [].
Proof. intros n i j k. gen i j.
  induction k; intros;
    unfold loop_replaceTB_XY; auto.
  bdestruct_all; simpl in *; subst.
  rewrite IHk; auto.
  destruct (nth i (repeat gI n) gI) eqn:E; try rewrite IHk; auto.
Qed.

Lemma loop_replaceTB_Z_nil : forall (n i j k : nat), loop_replaceTB_Z n i j k [] = [].
Proof. intros n i j k. gen i j.
  induction k; intros;
    unfold loop_replaceTB_Z; auto.
  bdestruct_all; simpl in *; subst.
  rewrite IHk; auto.
  destruct (nth i (repeat gI n) gI) eqn:E; try rewrite IHk; auto.
Qed.

Lemma loop_j_return_QPLB_nil : forall (n i j : nat) (QP : list (nat * nat)) (Lz : list nat),
    snd (loop_j_return_QPLB n i j QP [] Lz) = [].
Proof. intros n i j QP Lz.
  gen i QP Lz. induction j; intros; 
    unfold loop_j_return_QPLB.
  destruct (rev Lz); simpl; auto.
  destruct (existsb (fun qp : nat * nat => snd qp =? length [] - S j)%nat QP) eqn:E.
  rewrite IHj; auto.
  destruct (nth i (snd (nth (@length (TTypeB n) [] - S j) [] (defaultTB_I n))) gI) eqn:E';
    setoid_rewrite E';
    try rewrite IHj; auto.
Qed.

Lemma loop_normalizationB_nil : forall (lq : list nat) (n i : nat), loop_normalizationB lq n i [] [] = ([], []).
Proof. intros lq n i. 
  induction i;
    unfold loop_normalizationB; simpl; auto.
Qed.

Lemma loop_normalizationB_final_nil : forall (lq : list nat) (n i : nat), loop_normalizationB_final lq n i [] [] = [].
Proof. intros lq n i.
  unfold loop_normalizationB_final.
  destruct (loop_normalizationB lq n i [] []) eqn:E.
  rewrite loop_normalizationB_nil in E.
  inversion E.
  simpl; auto.
Qed.

Lemma pivots_normalizeB_nil : forall (start : nat) {n : nat}, @pivots_normalizeB start n [] = [].
Proof. intros start n.
  unfold pivots_normalizeB.
  apply loop_normalizationB_final_nil.
Qed.

Lemma normalizeB_nil : forall (start : nat) {n : nat}, @normalizeB start n [] = [].
Proof. intros start n.
  unfold normalizeB.
  rewrite pivots_normalizeB_nil; auto.
Qed.

Lemma pivotsB_nil : forall (start : nat) {n : nat}, @pivotsB start n [] = [].
Proof. intros start n.
  unfold pivotsB.
  rewrite pivots_normalizeB_nil; auto.
Qed.


(** ** Fueled version with TTypeB and gMulTB ** **)
(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceTB_XY_fuel (kfuel n i j k  : nat) (L : list (TTypeB n)) {struct kfuel} : list (TTypeB n) :=
  match kfuel with
  | S kfuel' =>
      match k with
      | 0%nat => L
      | S k' => 
          if Nat.eqb ((length L) - k) j
          then loop_replaceTB_XY_fuel kfuel' n i j k' L
          else 
            match nth i (snd (nth ((length L) - k) L (defaultTB_I n))) gI with
            | gX | gY => loop_replaceTB_XY_fuel kfuel' n i j k' (switch L (gMulTB (nth j L (defaultTB_I n)) (nth ((length L) - k) L (defaultTB_I n))) ((length L) - k))
            | _ => loop_replaceTB_XY_fuel kfuel' n i j k' L
            end
      end
  | 0%nat => L
  end.


Lemma loop_replaceTB_XY_length : forall (n i j k : nat) (L : list (TTypeB n)),
    length (loop_replaceTB_XY n i j k L) = length L.
Proof. intros n i j k L.
  gen L.
  induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
  all: rewrite IHk; rewrite switch_len; auto.
Qed.

Lemma loop_replaceTB_XY_fuel_length : forall (kfuel n i j k : nat) (L : list (TTypeB n)),
    length (loop_replaceTB_XY_fuel kfuel n i j k L) = length L.
Proof. intros kfuel n i j k L.
  gen k L.
  induction kfuel; intros; simpl; auto.
  destruct k; auto.
  bdestruct_all; simpl; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
  all: rewrite IHkfuel; rewrite switch_len; auto.
Qed.

Lemma loop_replaceTB_XY_fuel_saturated_base : forall (n i j k : nat) (L : list (TTypeB n)),
    loop_replaceTB_XY_fuel k n i j k L = loop_replaceTB_XY n i j k L.
Proof. intros n i j k L.
  gen L. induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
Qed.

Lemma loop_replaceTB_XY_fuel_saturated : forall (kfuel n i j k : nat) (L : list (TTypeB n)),
    (kfuel >= k)%nat -> 
    loop_replaceTB_XY_fuel kfuel n i j k L = loop_replaceTB_XY n i j k L.
Proof. intros kfuel n i j k L H. 
  gen kfuel L. induction k; intros.
  - destruct kfuel; auto.
  - destruct kfuel; try lia.
    assert (kfuel >= k)%nat by lia.
    simpl. bdestruct_all; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
Qed.

(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceTB_Z_fuel (kfuel n i j k : nat) (L : list (TTypeB n)) {struct kfuel} : list (TTypeB n) :=
  match kfuel with
  | S kfuel' =>
      match k with
      | 0%nat => L
      | S k' => 
          if Nat.eqb ((length L) - k) j
          then loop_replaceTB_Z_fuel kfuel' n i j k' L
          else 
            match nth i (snd (nth ((length L) - k) L (defaultTB_I n))) gI with
            | gZ => loop_replaceTB_Z_fuel kfuel' n i j k' (switch L (gMulTB (nth j L (defaultTB_I n)) (nth ((length L) - k) L (defaultTB_I n))) ((length L) - k))
            | _ => loop_replaceTB_Z_fuel kfuel' n i j k' L
            end
      end
  | 0%nat => L
  end.


Lemma loop_replaceTB_Z_length : forall (n i j k : nat) (L : list (TTypeB n)),
    length (loop_replaceTB_Z n i j k L) = length L.
Proof. intros n i j k L.
  gen L.
  induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
  all: rewrite IHk; rewrite switch_len; auto.
Qed.

Lemma loop_replaceTB_Z_fuel_length : forall (kfuel n i j k : nat) (L : list (TTypeB n)),
    length (loop_replaceTB_Z_fuel kfuel n i j k L) = length L.
Proof. intros kfuel n i j k L.
  gen k L.
  induction kfuel; intros; simpl; auto.
  destruct k; auto.
  bdestruct_all; simpl; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
  all: rewrite IHkfuel; rewrite switch_len; auto.
Qed.

Lemma loop_replaceTB_Z_fuel_saturated_base : forall (n i j k : nat) (L : list (TTypeB n)),
    loop_replaceTB_Z_fuel k n i j k L = loop_replaceTB_Z n i j k L.
Proof. intros n i j k L.
  gen L. induction k; intros; simpl; auto.
  bdestruct_all; auto.
  destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
Qed.

Lemma loop_replaceTB_Z_fuel_saturated : forall (kfuel n i j k : nat) (L : list (TTypeB n)),
    (kfuel >= k)%nat -> 
    loop_replaceTB_Z_fuel kfuel n i j k L = loop_replaceTB_Z n i j k L.
Proof. intros kfuel n i j k L H. 
  gen kfuel L. induction k; intros.
  - destruct kfuel; auto.
  - destruct kfuel; try lia.
    assert (kfuel >= k)%nat by lia.
    simpl. bdestruct_all; auto.
    destruct (nth i (snd (nth ((length L) - S k) L (defaultTB_I n))) gI) eqn:E; auto.
Qed.


(** j := length L
     Lz := []
     n, i   < fixed > **)
Fixpoint loop_j_return_QPLB_fuel (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) (Lz : list nat) {struct jfuel} : (list (nat * nat)) * (list (TTypeB n)) := 
  match jfuel with
  | S jfuel' =>
      match j with
      | S j' => 
          if (existsb (fun qp : nat * nat => Nat.eqb (snd qp) ((length LB) - j)%nat) QP) 
          then
            (* loop on next j *)
            loop_j_return_QPLB_fuel jfuel' kfuel n i j' QP LB Lz
          else 
            match nth i (snd (nth ((length LB) - j)%nat LB (defaultTB_I n))) gI with
            | gI => 
                (* loop on next j *)
                loop_j_return_QPLB_fuel jfuel' kfuel n i j' QP LB Lz
            | gZ => 
                (* add j to Lz and loop on next j *)
                loop_j_return_QPLB_fuel jfuel' kfuel n i j' QP LB (((length LB) - j)%nat :: Lz)
            | _ => 
                (* add j to QP and return QP, (loop_replaceTB_XY n i j (length LB) LB) *)
                (((i,((length LB) - j)%nat) :: QP), (loop_replaceTB_XY_fuel kfuel n i ((length LB) - j)%nat (length LB) LB))
            end
      | 0%nat =>
          match rev Lz with
          | [] => 
              (* return QP, LB *)
              (QP, LB)
          | h :: _ => 
              (* add j to QP and return QP, (loop_replaceTB_Z n i j (length LB) LB) *)
              (((i,h) :: QP), (loop_replaceTB_Z_fuel kfuel n i h (length LB) LB))
          end
      end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return QP, LB *)
          (QP, LB)
      | h :: _ => 
          (* add j to QP and return QP, (loop_replaceTB_Z n i j (length LB) LB) *)
          (((i,h) :: QP), (loop_replaceTB_Z_fuel kfuel n i h (length LB) LB))
      end
  end.


Lemma loop_j_return_QPLB_length : 
  forall (n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    length (snd (loop_j_return_QPLB n i j QP L Lz)) = length L.
Proof. intros n i j QP L Lz.
  gen L Lz. 
  induction j; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceTB_Z_length; auto.
  - destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; simpl; auto.
    all : try rewrite loop_replaceTB_XY_length; auto.
Qed.

Lemma loop_j_return_QPLB_fuel_length : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    length (snd (loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz)) = length L.
Proof. intros jfuel kfuel n i j QP L Lz.
  gen L Lz j. 
  induction jfuel; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceTB_Z_fuel_length; auto.
  - destruct j.
    + destruct (rev Lz); simpl; auto.
      rewrite loop_replaceTB_Z_fuel_length; auto.
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; simpl; auto.
      all : try rewrite loop_replaceTB_XY_fuel_length; auto.
Qed.

Lemma loop_j_return_QPLB_fuel_NoDup_QP : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    (forall (x : nat), In x Lz -> forall (m : nat), (m < length QP)%nat -> forall (d : nat * nat), (snd (nth m QP d) <> x)) -> 
    NoDup (map snd QP) -> NoDup (map snd (fst (loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz))).
Proof. intros jfuel kfuel n i j QP L Lz H H0.
  gen kfuel j QP L Lz.
  induction jfuel; intros; simpl; auto.
  - destruct (rev Lz) eqn:E; auto; simpl.
    assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
    rewrite <- in_rev in H1.
    specialize (H n0 H1).
    assert (~ In n0 (map snd QP)).
    { intro.
      apply In_nth with (d := 0%nat) in H2.
      destruct H2 as [x [H2 H3]].
      rewrite map_length in H2.
      specialize (H x H2 (0,0)%nat).
      rewrite map_nth with (d := (0,0)%nat) in H3.
      contradiction. }
    pose (NoDup_cons n0 H2 H0).
    auto.
  - destruct j.
    + destruct (rev Lz) eqn:E; auto; simpl.
    assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
    rewrite <- in_rev in H1.
    specialize (H n0 H1).
    assert (~ In n0 (map snd QP)).
    { intro.
      apply In_nth with (d := 0%nat) in H2.
      destruct H2 as [x [H2 H3]].
      rewrite map_length in H2.
      specialize (H x H2 (0,0)%nat).
      rewrite map_nth with (d := (0,0)%nat) in H3.
      contradiction. }
    pose (NoDup_cons n0 H2 H0).
    auto.
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; simpl; auto.
      * assert (~ In ((length L) - S j)%nat (map snd QP)).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          rewrite map_length in H1.
          pose (existsb_nth (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP (i,0)%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          rewrite map_nth with (d := (i,0)%nat) in H2.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * assert (~ In ((length L) - S j)%nat (map snd QP)).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          rewrite map_length in H1.
          pose (existsb_nth (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP (i,0)%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          rewrite map_nth with (d := (i,0)%nat) in H2.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * apply IHjfuel; auto.
        intros x H1 m H2 d.
        intro. subst.
        inversion H1.
        -- rewrite H3 in E.
           pose (existsb_nth (fun qp : nat * nat => (snd qp =? snd (nth m QP d))%nat) QP d H2 E) as E0.
           simpl in E0.
           rewrite Nat.eqb_neq in E0.
           contradiction.
        -- specialize (H (snd (nth m QP d)) H3 m H2 d).
           contradiction.
Qed.

Lemma loop_j_return_QPLB_fuel_incl_QP_seq_0_length_L : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0%nat (length L)) -> incl (map snd QP) (seq 0%nat (length L)) -> 
    incl (map snd (fst (loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz))) (seq 0%nat (length L)).
Proof. intros jfuel kfuel n i j QP L Lz H H0 H1. 
  gen kfuel j QP L Lz.
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
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; auto; simpl.
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

Lemma loop_j_return_QPLB_fuel_saturated_base : 
  forall (kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    (kfuel >= length L)%nat ->
    loop_j_return_QPLB_fuel j kfuel n i j QP L Lz = loop_j_return_QPLB n i j QP L Lz.
Proof. intros kfuel n i j QP L Lz H.
  gen L Lz. induction j; intros; simpl.
  - destruct (rev Lz); auto.
    f_equal. apply loop_replaceTB_Z_fuel_saturated; auto.
  - destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; simpl; auto;
      f_equal; apply loop_replaceTB_XY_fuel_saturated; auto.
Qed.

Lemma loop_j_return_QPLB_fuel_saturated : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (Lz : list nat),
    (kfuel >= length L)%nat -> (jfuel >= j)%nat ->
    loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz = loop_j_return_QPLB n i j QP L Lz.
Proof. intros jfuel kfuel n i j QP L Lz H H0.
  gen L Lz jfuel. induction j; intros.
  - destruct jfuel.
    + apply loop_j_return_QPLB_fuel_saturated_base; auto.
    + unfold loop_j_return_QPLB_fuel, loop_j_return_QPLB.
      destruct (rev Lz); auto.
      f_equal. apply loop_replaceTB_Z_fuel_saturated; auto.
  - destruct jfuel; try lia.
    assert (jfuel >= j)%nat by lia. simpl.
    destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultTB_I n))) gI) eqn:E'; auto;
      f_equal; apply loop_replaceTB_XY_fuel_saturated; auto. 
Qed.


(** lq := qubit_order <fixed>
              ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n)))
     i := n
     n := initialized from input   < fixed >
     QP := []
     L := initialized from input **)
Fixpoint loop_normalizationB_fuel (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) {struct ifuel} : (list (nat * nat)) * (list (TTypeB n))  :=
  match ifuel with
  | S ifuel' =>
      match i with
      | S i' =>
          (* do loop_j_return_QPLB and get (QP, LB), recurse on next i *)
          let (QP', LB') := loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - i)%nat lq 0%nat) (length LB) QP LB [] in
          loop_normalizationB_fuel ifuel' jfuel kfuel lq n i' QP' LB'
      | 0%nat => (QP, LB)
      end
  | 0%nat => (QP, LB)
  end.

Lemma loop_normalizationB_fuel_length (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)):
  length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
  length (snd (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L)) = length L.
Proof. gen QP L. gen jfuel kfuel lq n i. induction ifuel; intros; simpl in *; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPLB_fuel_length jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H'.
  rewrite E in H'. simpl in H'. rewrite <- H'. apply IHifuel; auto.
  rewrite <- H' in H. auto.
  pose (loop_j_return_QPLB_fuel_NoDup_QP jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H''.
  assert (forall x : nat,
             In x [] -> forall m : nat, (m < length QP)%nat -> forall d : nat * nat, snd (nth m QP d) <> x).
  { intros x H2 m H3 d. inversion H2. }
  specialize (H'' H2 H0).
  rewrite E in H''. simpl in H''. auto.
  pose (loop_j_return_QPLB_fuel_incl_QP_seq_0_length_L jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H''.
  specialize (H'' H).
  assert (incl [] (seq 0 (length L))). { unfold incl. intros a H2. inversion H2. }
  specialize (H'' H2 H1).
  rewrite E in H''. simpl in H''. rewrite H'. auto.
Qed.

Lemma loop_normalizationB_fuel_NoDup_QP (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)):
  NoDup (map snd QP) -> NoDup (map snd (fst (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L))).
Proof. intros H.
  gen jfuel kfuel lq QP L. gen n i. induction ifuel; intros; simpl; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPLB_fuel_NoDup_QP jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H0.
  assert (forall x : nat, In x [] -> forall m : nat, (m < length QP)%nat -> forall d : nat * nat, snd (nth m QP d) <> x).
  { intros x H1 m H2 d. inversion H1. }
  specialize (H0 H1 H).
  rewrite E in H0.
  simpl in H0.
  apply IHifuel; auto.
Qed.

Lemma loop_normalizationB_fuel_incl_QP_seq_0_length_L (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)):
  length L <> 0%nat -> incl (map snd QP) (seq 0 (length L)) ->
  incl (map snd (fst (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L))) (List.seq 0%nat (length L)).
Proof. intros H H0.
  gen jfuel kfuel lq QP L. gen n i. induction ifuel; intros; simpl; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPLB_fuel_incl_QP_seq_0_length_L jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H1.
  assert (incl [] (seq 0 (length L))).
  { unfold incl. intros a H2. inversion H2. }
  specialize (H1 H H2 H0).
  rewrite E in H1. simpl in H1.
  pose (loop_j_return_QPLB_fuel_length jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H3.
  rewrite E in H3. simpl in H3.
  rewrite <- H3.
  apply IHifuel; try rewrite H3; auto.
Qed.

Lemma loop_normalizationB_fuel_saturated_base : 
  forall (jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> 
    loop_normalizationB_fuel i jfuel kfuel lq n i QP L = loop_normalizationB lq n i QP L.
Proof. intros jfuel kfuel lq n i QP L H H0.
  gen jfuel kfuel lq QP L.
  induction i; intros; simpl; auto.
  destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L) eqn:E.
  destruct (loop_j_return_QPLB n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E'.
  rewrite loop_j_return_QPLB_fuel_saturated in E; auto.
  rewrite E in E'.
  inversion E'; subst; clear E'.
  pose (loop_j_return_QPLB_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'.
  rewrite E in E'.
  simpl in E'.
  apply IHi; rewrite E'; auto.
Qed.

Lemma loop_normalizationB_fuel_saturated : 
  forall (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= i)%nat ->
    loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L = loop_normalizationB lq n i QP L.
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1.
   gen L. gen ifuel jfuel kfuel lq QP.
   induction i; intros; simpl.
  - destruct ifuel; auto.
  - destruct ifuel; try lia.
    assert (ifuel >= i)%nat by lia.
    simpl.
    rewrite loop_j_return_QPLB_fuel_saturated; auto.
    destruct (loop_j_return_QPLB n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
    pose (loop_j_return_QPLB_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'.
    rewrite E in E'.
    simpl in E'.
    apply IHi; try rewrite E'; auto.
Qed.

(** Generalized version of normalization: 
Can change where to start the loop in the qubits.
start=0: qubit order -> 0,1,2,3,4,5,...,n-1
start=a: qubit order -> a,a+1,...,n-1,0,1,2,...,a-1 **)
(**  : list (TType n) 
      start := where to start loop
**)

Definition loop_normalizationB_final_fuel (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (LB : list (TTypeB n)) : list ((option nat) * TTypeB n)  :=
  let (QP, LB) := loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP LB in
  let noP := (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP))) (List.seq 0 (length LB))) in
  (* Final Ordering with rev QP *)
  (map (fun qp : nat * nat => (Some (fst qp), nth (snd qp) LB (defaultTB_I n))) (rev QP)) ++ 
    combine (repeat None (length noP)) (lexicographicB (map (fun p : nat => nth p LB (defaultTB_I n)) noP)).

Lemma loop_normalizationB_final_fuel_length (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)):
  length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
  length (loop_normalizationB_final_fuel ifuel jfuel kfuel lq n i QP L) = length L.
Proof. intros H H0 H1.
  unfold loop_normalizationB_final_fuel.
  destruct (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  pose (loop_normalizationB_fuel_length ifuel jfuel kfuel lq n i QP L H H0 H1) as H2.
  rewrite E in H2. simpl in H2.
  rewrite H2.
  rewrite app_length. rewrite map_length. rewrite rev_length.
  rewrite combine_length. rewrite repeat_length.
  unfold lexicographicB. rewrite rev_length.
  pose (TBOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultTB_I n))
              (filter
                 (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l))
                 (seq 0 (length L))))) as H'.
  apply Permutation_length in H'. rewrite <- H'.
  rewrite map_length. minmax_breakdown.
  rewrite <- map_length with (f := snd).
  rewrite <- (seq_length (length L) 0%nat) at 2.
  rewrite <- filter_length with (l := seq 0 (length L)) (f := (fun a : nat => existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l))).
  f_equal.
  pose (Permutation_filter_existsb_eqdec_seq (length L) (map snd l)) as H''.
  pose (loop_normalizationB_fuel_NoDup_QP ifuel jfuel kfuel lq n i QP L H0) as H'''.
  rewrite E in H'''. simpl in H'''.
  pose (loop_normalizationB_fuel_incl_QP_seq_0_length_L ifuel jfuel kfuel lq n i QP L H H1) as H''''.
  rewrite E in H''''. simpl in H''''.
  specialize (H'' H''' H'''').
  apply Permutation_length in H''.
  auto.
Qed.

Lemma loop_normalizationB_final_fuel_saturated_base : 
  forall (jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> 
    loop_normalizationB_final_fuel i jfuel kfuel lq n i QP L = loop_normalizationB_final lq n i QP L.
Proof. intros jfuel kfuel lq n i QP L H H0.
  unfold loop_normalizationB_final, loop_normalizationB_final_fuel.
  destruct (loop_normalizationB_fuel i jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalizationB lq n i QP L) eqn:E'.
  rewrite loop_normalizationB_fuel_saturated_base in E; auto.
  rewrite E in E'.
  inversion E'.
  auto.
Qed.

Lemma loop_normalizationB_final_fuel_saturated : 
  forall (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= i)%nat ->
    loop_normalizationB_final_fuel ifuel jfuel kfuel lq n i QP L = loop_normalizationB_final lq n i QP L.
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1.
  unfold loop_normalizationB_final, loop_normalizationB_final_fuel.
  destruct (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalizationB lq n i QP L) eqn:E'.
  rewrite loop_normalizationB_fuel_saturated in E; auto.
  rewrite E in E'.
  inversion E'.
  auto.
Qed.

Definition pivots_normalizeB_fuel (ifuel jfuel kfuel start : nat) {n : nat} (LB : list (TTypeB n)) : list ((option nat) * TTypeB n)  := 
  loop_normalizationB_final_fuel ifuel jfuel kfuel ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n))) n n [] LB.

Lemma pivots_normalizeB_fuel_saturated : forall (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= n)%nat ->
    pivots_normalizeB_fuel ifuel jfuel kfuel start L = pivots_normalizeB start L.
Proof. intros ifuel jfuel kfuel start n L H H0 H1.
  unfold pivots_normalizeB_fuel, pivots_normalizeB.
  apply loop_normalizationB_final_fuel_saturated; auto.
Qed.

Definition normalizeB_fuel (ifuel jfuel kfuel start : nat) {n : nat} (LB : list (TTypeB n)) := 
  map snd (pivots_normalizeB_fuel ifuel jfuel kfuel start LB).

Lemma normalizeB_fuel_saturated : forall (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TTypeB n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= n)%nat ->
    normalizeB_fuel ifuel jfuel kfuel start L = normalizeB start L.
Proof. intros ifuel jfuel kfuel start n L H H0 H1.
  unfold normalizeB_fuel, normalizeB. f_equal.
  apply pivots_normalizeB_fuel_saturated; auto.
Qed.






(** ** Original version ** **)
(** k := length L
     n, i, j   < fixed > **)
Fixpoint loop_replaceT_XY (n i j k  : nat) (L : list (TType n)) {struct k} : list (TType n) :=
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
Fixpoint loop_j_return_QPL (n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat) : (list (nat * nat)) * (list (TType n)) := 
  match j with
  | S j' => 
      if (existsb (fun qp : nat * nat => Nat.eqb (snd qp) ((length L) - j)%nat) QP) 
      then
        (* loop on next j *)
        loop_j_return_QPL n i j' QP L Lz
      else 
        match nth i (snd (nth ((length L) - j)%nat L (defaultT_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_QPL n i j' QP L Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_QPL n i j' QP L (((length L) - j)%nat :: Lz)
        | _ => 
            (* add j to QP and return QP, (loop_replaceT_XY n i j (length L) L) *)
            (((i,((length L) - j)%nat) :: QP), (loop_replaceT_XY n i ((length L) - j)%nat (length L) L))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return QP, L *)
          (QP, L)
      | h :: _ => 
          (* add j to QP and return QP, (loop_replaceT_Z n i j (length L) L) *)
          (((i,h) :: QP), (loop_replaceT_Z n i h (length L) L))
      end
  end.

(** lq := qubit_order <fixed>
              ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n)))
     i := n
     n := initialized from input   < fixed >
     P := []
     L := initialized from input **)
Fixpoint loop_normalization (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) {struct i} : (list (nat * nat)) * (list (TType n))  :=
  match i with
  | S i' =>
      (* do loop_j_return_QPL and get (QP, L), recurse on next i *)
      let (QP', L') := loop_j_return_QPL n (nth (n - i)%nat lq 0%nat) (length L) QP L [] in
      loop_normalization lq n i' QP' L'
  | 0%nat => (QP, L)
  end.

Definition loop_normalization_final (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) : list ((option nat) * (TType n))  :=
  let (QP, L) := loop_normalization lq n i QP L in
  let noP := (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP))) (List.seq 0 (length L))) in
      (* Final Ordering with rev P *)
      (map (fun qp : nat * nat => (Some (fst qp), nth (snd qp) L (defaultT_I n))) (rev QP)) ++ 
        combine (repeat None (length noP)) (lexicographic (map (fun p : nat => nth p L (defaultT_I n)) noP)).

(** Generalized version of normalization: 
Can change where to start the loop in the qubits.
start=0: qubit order -> 0,1,2,3,4,5,...,n-1
start=a: qubit order -> a,a+1,...,n-1,0,1,2,...,a-1 **)
(**  : list (TType n) 
      start := where to start loop
**)
Definition pivots_normalize (start : nat) {n : nat} (L : list (TType n)) := 
  loop_normalization_final ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n))) n n [] L.

Definition normalize (start : nat) {n : nat} (L : list (TType n)) := 
  map snd (pivots_normalize start L).

Definition pivot_search {n} (lqt : list ((option nat) * (TType n))) (i : nat) : Pauli :=
  match find (fun qt =>
                match fst qt with
                | Some q => Nat.eqb i q
                | None => false
                end) lqt 
  with
  | None => gI
  | Some qt => nth i (snd (snd qt)) gI
  end.

Definition pivots (start : nat) {n : nat} (L : list (TType n)) : list (nat * Pauli) :=
  let LQT := (pivots_normalize start L) in
  map 
    (fun i =>  (i, pivot_search LQT i))
    (List.seq 0 (length L)).



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

Lemma loop_j_return_QPL_nil : forall (n i j : nat) (QP : list (nat * nat)) (Lz : list nat),
    snd (loop_j_return_QPL n i j QP [] Lz) = [].
Proof. intros n i j QP Lz.
  gen i QP Lz. induction j; intros; 
    unfold loop_j_return_QPL.
  destruct (rev Lz); simpl; auto.
  destruct (existsb (fun qp : nat * nat => snd qp =? length [] - S j)%nat QP) eqn:E.
  rewrite IHj; auto.
  destruct (nth i (snd (nth (length [] - S j) [] (defaultT_I n))) gI) eqn:E';
    try rewrite IHj; auto.
Qed.

Lemma loop_normalization_nil : forall (lq : list nat) (n i : nat), loop_normalization lq n i [] [] = ([], []).
Proof. intros lq n i. 
  induction i;
    unfold loop_normalization; simpl; auto.
Qed.

Lemma loop_normalization_final_nil : forall (lq : list nat) (n i : nat), loop_normalization_final lq n i [] [] = [].
Proof. intros lq n i. 
  unfold loop_normalization_final.
  destruct (loop_normalization lq n i [] []) eqn:E.
  rewrite loop_normalization_nil in E.
  inversion E.
  simpl; auto.
Qed.

Lemma pivots_normalize_nil : forall (start : nat) {n : nat}, @pivots_normalize start n [] = [].
Proof. intros start n.
  unfold pivots_normalize.
  apply loop_normalization_final_nil.
Qed.

Lemma normalize_nil : forall (start : nat) {n : nat}, @normalize start n [] = [].
Proof. intros start n.
  unfold normalize.
  rewrite pivots_normalize_nil; auto.
Qed.

Lemma pivots_nil : forall (start : nat) {n : nat}, @pivots start n [] = [].
Proof. intros start n.
  unfold pivots.
  rewrite pivots_normalize_nil; auto.
Qed.





(** ** Fuel based admissibility proof ** **)
(** Assuming that Permutation on intersections is provably admissible *) 

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


(** ** Fueled version of original ** **)
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
Fixpoint loop_j_return_QPL_fuel (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat) {struct jfuel} : (list (nat * nat)) * (list (TType n)) := 
match jfuel with
| S jfuel' =>
  match j with
  | S j' => 
      if (existsb (fun qp : nat * nat => Nat.eqb (snd qp) ((length L) - j)%nat) QP) 
      then
        (* loop on next j *)
        loop_j_return_QPL_fuel jfuel' kfuel n i j' QP L Lz
      else 
        match nth i (snd (nth ((length L) - j)%nat L (defaultT_I n))) gI with
        | gI => 
            (* loop on next j *)
            loop_j_return_QPL_fuel jfuel' kfuel n i j' QP L Lz
        | gZ => 
            (* add j to Lz and loop on next j *)
            loop_j_return_QPL_fuel jfuel' kfuel n i j' QP L (((length L) - j)%nat :: Lz)
        | _ => 
            (* add j to QP and return QP, (loop_replaceT_XY n i j (length L) L) *)
            (((i,((length L) - j)%nat) :: QP), (loop_replaceT_XY_fuel kfuel n i ((length L) - j)%nat (length L) L))
        end
  | 0%nat =>
      match rev Lz with
      | [] => 
          (* return QP, L *)
          (QP, L)
      | h :: _ => 
          (* add j to QP and return QP, (loop_replaceT_Z n i j (length L) L) *)
          (((i,h) :: QP), (loop_replaceT_Z_fuel kfuel n i h (length L) L))
      end
  end
| 0%nat => 
    match rev Lz with
    | [] => 
        (* return QP, L *)
        (QP, L)
    | h :: _ => 
        (* add j to QP and return QP, (loop_replaceT_Z n i j (length L) L) *)
        (((i,h) :: QP), (loop_replaceT_Z_fuel kfuel n i h (length L) L))
    end
end.

Lemma loop_j_return_QPL_length : 
  forall (n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    length (snd (loop_j_return_QPL n i j QP L Lz)) = length L.
Proof. intros n i j QP L Lz.
  gen L Lz. 
  induction j; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceT_Z_length; auto.
  - destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
    all : try rewrite loop_replaceT_XY_length; auto.
Qed.

Lemma loop_j_return_QPL_fuel_length : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    length (snd (loop_j_return_QPL_fuel jfuel kfuel n i j QP L Lz)) = length L.
Proof. intros jfuel kfuel n i j QP L Lz.
  gen L Lz j. 
  induction jfuel; intros; simpl.
  - destruct (rev Lz); simpl; auto.
    rewrite loop_replaceT_Z_fuel_length; auto.
  - destruct j.
    + destruct (rev Lz); simpl; auto.
      rewrite loop_replaceT_Z_fuel_length; auto.
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
      all : try rewrite loop_replaceT_XY_fuel_length; auto.
Qed.

Lemma loop_j_return_QPL_fuel_saturated_base : 
  forall (kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    (kfuel >= length L)%nat ->
    loop_j_return_QPL_fuel j kfuel n i j QP L Lz = loop_j_return_QPL n i j QP L Lz.
Proof. intros kfuel n i j QP L Lz H.
  gen L Lz. induction j; intros; simpl.
  - destruct (rev Lz); auto.
    f_equal. apply loop_replaceT_Z_fuel_saturated; auto.
  - destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto;
      f_equal; apply loop_replaceT_XY_fuel_saturated; auto.
Qed.

Lemma loop_j_return_QPL_fuel_saturated : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    (kfuel >= length L)%nat -> (jfuel >= j)%nat ->
    loop_j_return_QPL_fuel jfuel kfuel n i j QP L Lz = loop_j_return_QPL n i j QP L Lz.
Proof. intros jfuel kfuel n i j QP L Lz H H0.
  gen L Lz jfuel. induction j; intros.
  - destruct jfuel.
    + apply loop_j_return_QPL_fuel_saturated_base; auto.
    + unfold loop_j_return_QPL_fuel, loop_j_return_QPL.
      destruct (rev Lz); auto.
      f_equal. apply loop_replaceT_Z_fuel_saturated; auto.
  - destruct jfuel; try lia.
    assert (jfuel >= j)%nat by lia. simpl.
    destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; auto;
      f_equal; apply loop_replaceT_XY_fuel_saturated; auto. 
Qed.

Lemma loop_j_return_QPL_fuel_NoDup_QP : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    (forall (x : nat), In x Lz -> forall (m : nat), (m < length QP)%nat -> forall (d : nat * nat), (snd (nth m QP d) <> x)) -> 
    NoDup (map snd QP) -> NoDup (map snd (fst (loop_j_return_QPL_fuel jfuel kfuel n i j QP L Lz))).
Proof. intros jfuel kfuel n i j QP L Lz H H0.
  gen kfuel j QP L Lz.
  induction jfuel; intros; simpl; auto.
  - destruct (rev Lz) eqn:E; auto; simpl.
    assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
    rewrite <- in_rev in H1.
    specialize (H n0 H1).
    assert (~ In n0 (map snd QP)).
    { intro.
      apply In_nth with (d := 0%nat) in H2.
      destruct H2 as [x [H2 H3]].
      rewrite map_length in H2.
      specialize (H x H2 (0,0)%nat).
      rewrite map_nth with (d := (0,0)%nat) in H3.
      contradiction. }
    pose (NoDup_cons n0 H2 H0).
    auto.
  - destruct j.
    + destruct (rev Lz) eqn:E; auto; simpl.
    assert (In n0 (rev Lz)). { rewrite E. constructor. auto. }
    rewrite <- in_rev in H1.
    specialize (H n0 H1).
    assert (~ In n0 (map snd QP)).
    { intro.
      apply In_nth with (d := 0%nat) in H2.
      destruct H2 as [x [H2 H3]].
      rewrite map_length in H2.
      specialize (H x H2 (0,0)%nat).
      rewrite map_nth with (d := (0,0)%nat) in H3.
      contradiction. }
    pose (NoDup_cons n0 H2 H0).
    auto.
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
      destruct (nth i (snd (nth ((length L) - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
      * assert (~ In ((length L) - S j)%nat (map snd QP)).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          rewrite map_length in H1.
          pose (existsb_nth (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP (i,0)%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          rewrite map_nth with (d := (i,0)%nat) in H2.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * assert (~ In ((length L) - S j)%nat (map snd QP)).
        { intro.
          apply In_nth with (d := 0%nat) in H1.
          destruct H1 as [x [H1 H2]].
          rewrite map_length in H1.
          pose (existsb_nth (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP (i,0)%nat H1 E) as E0.
          simpl in E0.
          rewrite Nat.eqb_neq in E0.
          rewrite map_nth with (d := (i,0)%nat) in H2.
          contradiction. }
        pose (NoDup_cons ((length L) - S j)%nat H1 H0); auto.
      * apply IHjfuel; auto.
        intros x H1 m H2 d.
        intro. subst.
        inversion H1.
        -- rewrite H3 in E.
           pose (existsb_nth (fun qp : nat * nat => (snd qp =? snd (nth m QP d))%nat) QP d H2 E) as E0.
           simpl in E0.
           rewrite Nat.eqb_neq in E0.
           contradiction.
        -- specialize (H (snd (nth m QP d)) H3 m H2 d).
           contradiction.
Qed.

Lemma loop_j_return_QPL_NoDup_QP : 
  forall (n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    (forall (x : nat), In x Lz -> forall (m : nat), (m < length QP)%nat -> forall (d : nat * nat), (snd (nth m QP d) <> x)) -> 
    NoDup (map snd QP) -> NoDup (map snd (fst (loop_j_return_QPL n i j QP L Lz))).
Proof. intros n i j QP L Lz H H0. 
  rewrite <- loop_j_return_QPL_fuel_saturated_base with (kfuel := length L); auto.
  apply loop_j_return_QPL_fuel_NoDup_QP; auto.
Qed.

Lemma loop_j_return_QPL_fuel_incl_QP_seq_0_length_L : 
  forall (jfuel kfuel n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0%nat (length L)) -> incl (map snd QP) (seq 0%nat (length L)) -> 
    incl (map snd (fst (loop_j_return_QPL_fuel jfuel kfuel n i j QP L Lz))) (seq 0%nat (length L)).
Proof. intros jfuel kfuel n i j QP L Lz H H0 H1. 
  gen kfuel j QP L Lz.
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
    + destruct (existsb (fun qp : nat * nat => snd qp =? (length L) - S j)%nat QP) eqn:E; auto.
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

Lemma loop_j_return_QPL_incl_QP_seq_0_length_L : 
  forall (n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0%nat (length L)) -> incl (map snd QP) (seq 0%nat (length L)) -> 
    incl (map snd (fst (loop_j_return_QPL n i j QP L Lz))) (seq 0%nat (length L)).
Proof. intros n i j P L Lz H H0 H1. 
  rewrite <- loop_j_return_QPL_fuel_saturated_base with (kfuel := length L); auto.
  apply loop_j_return_QPL_fuel_incl_QP_seq_0_length_L; auto.
Qed.


(** lq := qubit_order <fixed>
              ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n)))
      i := n   < fuel >
     n := initialized from input   < fixed >
     P := []
     L := initialized from input **)
Fixpoint loop_normalization_fuel (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) {struct ifuel} : (list (nat * nat) * list (TType n))  :=
  match ifuel with
  | S ifuel' =>
      match i with
      | S i' =>
          (* do loop_j_return_QPL and get (QP, L), recurse on next i *)
          let (QP', L') := loop_j_return_QPL_fuel jfuel kfuel n (nth (n - i)%nat lq 0%nat) (length L) QP L [] in
          loop_normalization_fuel ifuel' jfuel kfuel lq n i' QP' L'
      | 0%nat => (QP, L)
      end
  | 0%nat => (QP, L)
  end.

Lemma loop_normalization_fuel_length (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)):
  length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
  length (snd (loop_normalization_fuel ifuel jfuel kfuel lq n i QP L)) = length L.
Proof. gen QP L. gen jfuel kfuel lq n i. induction ifuel; intros; simpl in *; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPL_fuel_length jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H'.
  rewrite E in H'. simpl in H'. rewrite <- H'. apply IHifuel; auto.
  rewrite <- H' in H. auto.
  pose (loop_j_return_QPL_fuel_NoDup_QP jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H''.
  assert (forall x : nat,
             In x [] -> forall m : nat, (m < length QP)%nat -> forall d : nat * nat, snd (nth m QP d) <> x).
  { intros x H2 m H3 d. inversion H2. }
  specialize (H'' H2 H0).
  rewrite E in H''. simpl in H''. auto.
  pose (loop_j_return_QPL_fuel_incl_QP_seq_0_length_L jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H''.
  specialize (H'' H).
  assert (incl [] (seq 0 (length L))). { unfold incl. intros a H2. inversion H2. }
  specialize (H'' H2 H1).
  rewrite E in H''. simpl in H''. rewrite H'. auto.
Qed.

Lemma loop_normalization_fuel_NoDup_QP (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)):
  NoDup (map snd QP) -> NoDup (map snd (fst (loop_normalization_fuel ifuel jfuel kfuel lq n i QP L))).
Proof. intros H.
  gen jfuel kfuel lq QP L. gen n i. induction ifuel; intros; simpl; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPL_fuel_NoDup_QP jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H0.
  assert (forall x : nat, In x [] -> forall m : nat, (m < length QP)%nat -> forall d : nat * nat, snd (nth m QP d) <> x).
  { intros x H1 m H2 d. inversion H1. }
  specialize (H0 H1 H).
  rewrite E in H0.
  simpl in H0.
  apply IHifuel; auto.
Qed.

Lemma loop_normalization_fuel_incl_QP_seq_0_length_L (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)):
  length L <> 0%nat -> incl (map snd QP) (seq 0 (length L)) ->
  incl (map snd (fst (loop_normalization_fuel ifuel jfuel kfuel lq n i QP L))) (List.seq 0%nat (length L)).
Proof. intros H H0.
  gen jfuel kfuel lq QP L. gen n i. induction ifuel; intros; simpl; auto.
  destruct i; simpl; auto.
  destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
  pose (loop_j_return_QPL_fuel_incl_QP_seq_0_length_L jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H1.
  assert (incl [] (seq 0 (length L))).
  { unfold incl. intros a H2. inversion H2. }
  specialize (H1 H H2 H0).
  rewrite E in H1. simpl in H1.
  pose (loop_j_return_QPL_fuel_length jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) as H3.
  rewrite E in H3. simpl in H3.
  rewrite <- H3.
  apply IHifuel; try rewrite H3; auto.
Qed.

Lemma loop_normalization_fuel_saturated_base : 
  forall (jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> 
    loop_normalization_fuel i jfuel kfuel lq n i QP L = loop_normalization lq n i QP L.
Proof. intros jfuel kfuel lq n i QP L H H0.
  gen jfuel kfuel lq QP L.
  induction i; intros; simpl; auto.
  destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L) eqn:E.
  destruct (loop_j_return_QPL n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E'.
  rewrite loop_j_return_QPL_fuel_saturated in E; auto.
  rewrite E in E'.
  inversion E'; subst; clear E'.
  pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'.
  rewrite E in E'.
  simpl in E'.
  apply IHi; rewrite E'; auto.
Qed.

Lemma loop_normalization_fuel_saturated : 
  forall (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= i)%nat ->
    loop_normalization_fuel ifuel jfuel kfuel lq n i QP L = loop_normalization lq n i QP L.
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1.
   gen L. gen ifuel jfuel kfuel lq QP.
   induction i; intros; simpl.
  - destruct ifuel; auto.
  - destruct ifuel; try lia.
    assert (ifuel >= i)%nat by lia.
    simpl.
    rewrite loop_j_return_QPL_fuel_saturated; auto.
    destruct (loop_j_return_QPL n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
    pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'.
    rewrite E in E'.
    simpl in E'.
    apply IHi; try rewrite E'; auto.
Qed.


Lemma loop_normalization_length (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)):
  length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
  length (snd (loop_normalization lq n i QP L)) = length L.
Proof. intros H H0 H1.
  rewrite <- (loop_normalization_fuel_saturated i (length L) (length L)); try lia.
  apply loop_normalization_fuel_length; auto.
Qed.

Lemma loop_normalization_NoDup_map_snd
  (lq : list nat) (n i : nat)
  (QP : list (nat*nat)) (L : list (TType n)) :
  NoDup (map snd QP) ->
  NoDup (map snd (fst (loop_normalization lq n i QP L))).
Proof.
  intros Hnd.
  (* fuel에서 NoDup 얻고 saturated로 rewrite *)
  pose proof (loop_normalization_fuel_NoDup_QP i%nat (length L)%nat (length L)%nat lq n i QP L Hnd) as Hnd_fuel.
  (* loop_normalization_fuel = loop_normalization *)
  pose (loop_normalization_fuel_saturated i%nat (length L)%nat (length L)%nat lq n i QP L) as temp.
  rewrite temp in Hnd_fuel; try lia.
  exact Hnd_fuel.
Qed.

Lemma loop_normalization_incl_map_snd_seq
  (lq : list nat) (n i : nat)
  (QP : list (nat*nat)) (L : list (TType n)) :
  length L <> 0%nat ->
  incl (map snd QP) (seq 0 (length L)) ->
  incl (map snd (fst (loop_normalization lq n i QP L))) (seq 0 (length L)).
Proof.
  intros HlenL Hincl0.
  pose proof (loop_normalization_fuel_incl_QP_seq_0_length_L
                i%nat (length L)%nat (length L)%nat lq n i QP L HlenL Hincl0) as Hincl_fuel.
  pose (loop_normalization_fuel_saturated i%nat (length L)%nat (length L)%nat lq n i QP L) as temp.
  rewrite temp in Hincl_fuel; try lia.
  exact Hincl_fuel.
Qed.

Definition loop_normalization_final_fuel (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)) : list ((option nat) * (TType n))  :=
  let (QP, L) := loop_normalization_fuel ifuel jfuel kfuel lq n i QP L in
  let noP := (filter (fun a : nat => negb (existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd QP))) (List.seq 0 (length L))) in
  (* Final Ordering with rev P *)
  (map (fun qp : nat * nat => (Some (fst qp), nth (snd qp) L (defaultT_I n))) (rev QP)) ++ 
    combine (repeat None (length noP)) (lexicographic (map (fun p : nat => nth p L (defaultT_I n)) noP)).

Lemma loop_normalization_final_fuel_length (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)):
  length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
  length (loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP L) = length L.
Proof. intros H H0 H1.
  unfold loop_normalization_final_fuel.
  destruct (loop_normalization_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  pose (loop_normalization_fuel_length ifuel jfuel kfuel lq n i QP L H H0 H1) as H2.
  rewrite E in H2. simpl in H2.
  rewrite H2.
  rewrite app_length. rewrite map_length. rewrite rev_length.
  rewrite combine_length. rewrite repeat_length.
  unfold lexicographic. rewrite rev_length.
  pose (TOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultT_I n))
              (filter
                 (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l))
                 (seq 0 (length L))))) as H'.
  apply Permutation_length in H'. rewrite <- H'.
  rewrite map_length. minmax_breakdown.
  rewrite <- map_length with (f := snd).
  rewrite <- (seq_length (length L) 0%nat) at 2.
  rewrite <- filter_length with (l := seq 0 (length L)) (f := (fun a : nat => existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l))).
  f_equal.
  pose (Permutation_filter_existsb_eqdec_seq (length L) (map snd l)) as H''.
  pose (loop_normalization_fuel_NoDup_QP ifuel jfuel kfuel lq n i QP L H0) as H'''.
  rewrite E in H'''. simpl in H'''.
  pose (loop_normalization_fuel_incl_QP_seq_0_length_L ifuel jfuel kfuel lq n i QP L H H1) as H''''.
  rewrite E in H''''. simpl in H''''.
  specialize (H'' H''' H'''').
  apply Permutation_length in H''.
  auto.
Qed.

Lemma loop_normalization_final_fuel_saturated_base : 
  forall (jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> 
    loop_normalization_final_fuel i jfuel kfuel lq n i QP L = loop_normalization_final lq n i QP L.
Proof. intros jfuel kfuel lq n i QP L H H0.
  unfold loop_normalization_final, loop_normalization_final_fuel.
  destruct (loop_normalization_fuel i jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalization lq n i QP L) eqn:E'.
  rewrite loop_normalization_fuel_saturated_base in E; auto.
  rewrite E in E'.
  inversion E'.
  auto.
Qed.

Lemma loop_normalization_final_fuel_saturated : 
  forall (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= i)%nat ->
    loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP L = loop_normalization_final lq n i QP L.
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1.
  unfold loop_normalization_final, loop_normalization_final_fuel.
  destruct (loop_normalization_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalization lq n i QP L) eqn:E'.
  rewrite loop_normalization_fuel_saturated in E; auto.
  rewrite E in E'.
  inversion E'.
  auto.
Qed.

(**  : list (TType n) **)
Definition pivots_normalize_fuel (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TType n)) := loop_normalization_final_fuel ifuel jfuel kfuel ((skipn start (List.seq 0%nat n)) ++ (firstn start (List.seq 0%nat n))) n n [] L.

Lemma pivots_normalize_fuel_saturated : forall (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= n)%nat ->
    pivots_normalize_fuel ifuel jfuel kfuel start L = pivots_normalize start L.
Proof. intros ifuel jfuel kfuel start n L H H0 H1.
  unfold pivots_normalize_fuel, pivots_normalize.
  apply loop_normalization_final_fuel_saturated; auto.
Qed.

Definition normalize_fuel (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TType n)) := 
  map snd (pivots_normalize_fuel ifuel jfuel kfuel start L).

Lemma normalize_fuel_saturated : forall (ifuel jfuel kfuel start : nat) {n : nat} (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat -> (ifuel >= n)%nat ->
    normalize_fuel ifuel jfuel kfuel start L = normalize start L.
Proof. intros ifuel jfuel kfuel start n L H H0 H1.
  unfold normalize_fuel, normalize. f_equal.
  apply pivots_normalize_fuel_saturated; auto.
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

Lemma loop_j_return_QPL_PauliMult_listT_chain : 
  forall (n i j : nat) (QP : list (nat * nat)) (L : list (TType n)) (Lz : list nat),
    length L <> 0%nat -> incl Lz (seq 0 (length L)) ->
    PauliMult_listT_chain L (snd (loop_j_return_QPL n i j QP L Lz)).
Proof. intros n i j QP L Lz H H0.
  gen QP L Lz. induction j; intros; simpl.
  - destruct (rev Lz) eqn:E; simpl.
    + apply PauliMult_listT_chain_id; auto.
    + assert (In n0 Lz).
      { rewrite in_rev, E; constructor; auto. }
      apply H0 in H1.
      rewrite in_seq in H1.
      apply loop_replaceT_Z_PauliMult_listT_chain; auto; lia.
  - destruct (existsb (fun qp : nat * nat => snd qp =? length L - S j)%nat QP) eqn:E; auto.
    destruct (nth i (snd (nth (length L - S j) L (defaultT_I n))) gI) eqn:E'; simpl; auto.
    + apply loop_replaceT_XY_PauliMult_listT_chain; auto; lia.
    + apply loop_replaceT_XY_PauliMult_listT_chain; auto; lia.
    + apply IHj; auto.
      unfold incl; intros.
      inversion H1; subst; clear H1; auto.
      rewrite in_seq; lia.
Qed.

Lemma loop_normalization_final_fuel_PauliMult_listT_chain_Permutation : 
  forall (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    (kfuel >= length L)%nat -> (jfuel >= length L)%nat ->
    NoDup (map snd QP) -> incl (map snd QP) (seq 0 (length L)) -> length L <> 0%nat ->
    PauliMult_listT_chain_Permutation L (map snd (loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP L)).
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1 H2 H3.
  unfold loop_normalization_final_fuel.
  gen L. gen jfuel kfuel lq i QP. induction ifuel; intros.
  - simpl. constructor.
    exists L. split; try apply PauliMult_listT_chain_id; auto.
    rewrite map_app.
    rewrite map_map.
    simpl.
    rewrite <- map_map with (g := fun x => nth x L (defaultT_I n)) (f := snd) (l := rev QP).
    rewrite map_rev.
    rewrite map_snd_combine.
    2: { rewrite repeat_length. unfold lexicographic.
         rewrite rev_length. 
         pose (TOrd.Permuted_sort (map (fun p : nat => nth p L (defaultT_I n))
          (filter
             (fun a : nat =>
              ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                  (map snd QP)) (seq 0 (length L))))) as H4.
         apply Permutation_length in H4.
         rewrite <- H4.
         rewrite map_length; auto. }
    apply final_ordering_Permutation; auto.
  - simpl. destruct i.
    + constructor.
      exists L. split; try apply PauliMult_listT_chain_id; auto.
      rewrite map_app.
    rewrite map_map.
    simpl.
    rewrite <- map_map with (g := fun x => nth x L (defaultT_I n)) (f := snd) (l := rev QP).
    rewrite map_rev.
    rewrite map_snd_combine.
    2: { rewrite repeat_length. unfold lexicographic.
         rewrite rev_length. 
         pose (TOrd.Permuted_sort (map (fun p : nat => nth p L (defaultT_I n))
          (filter
             (fun a : nat =>
              ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false)
                  (map snd QP)) (seq 0 (length L))))) as H4.
         apply Permutation_length in H4.
         rewrite <- H4.
         rewrite map_length; auto. }
      apply final_ordering_Permutation; auto.
    + destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
      pose (loop_j_return_QPL_PauliMult_listT_chain n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'.
      rewrite loop_j_return_QPL_fuel_saturated in E; auto.
      rewrite E in E'. simpl in E'. 
      apply PauliMult_listT_chain_Permutation_append with (Lt2 := l0).
      * apply E'; auto; apply incl_nil_l.
      * apply IHifuel.
        -- pose (loop_j_return_QPL_NoDup_QP n (nth (n - S i) lq 0%nat) (length L) QP L []) as E''.
           rewrite E in E''. simpl in E''. apply E''; auto.
        -- pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
        -- pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
        -- pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''.
           pose (loop_j_return_QPL_incl_QP_seq_0_length_L n (nth (n - S i) lq 0%nat) (length L) QP L []) as E'''.
           rewrite E in E'''. simpl in E'''. apply E'''; auto; apply incl_nil_l.
        -- pose (loop_j_return_QPL_length n (nth (n - S i) lq 0%nat) (length L) QP L []) as E''.
           rewrite E in E''. simpl in E''. rewrite E''; auto.
Qed.

Lemma loop_normalization_final_PauliMult_listT_chain_Permutation : 
  forall (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TType n)),
    NoDup (map snd QP) -> incl (map snd QP) (seq 0 (length L)) -> length L <> 0%nat ->
    PauliMult_listT_chain_Permutation L (map snd (loop_normalization_final lq n i QP L)).
Proof. intros lq n i QP L H H0 H1. 
  rewrite <- loop_normalization_final_fuel_saturated_base with (kfuel := length L) (jfuel := length L);
    auto.
  apply loop_normalization_final_fuel_PauliMult_listT_chain_Permutation; auto.
Qed.

Lemma normalize_PauliMult_listT_chain_Permutation : forall (start : nat) {n : nat} (L : list (TType n)),
    length L <> 0%nat -> PauliMult_listT_chain_Permutation L (normalize start L).
Proof. intros start n L H. unfold normalize.
  apply loop_normalization_final_PauliMult_listT_chain_Permutation; auto.
  - apply NoDup_nil.
  - apply incl_nil_l.
Qed.



(*** TTypeBtoTType respects normalize ***)


Lemma TTypeBtoTType_respects_loop_j_return_QPL_fuel_fst (n : nat) (L : list (TTypeB n)) (jfuel : nat) (i j : nat) (QP l l1 : list (nat * nat)) (Lz : list nat):
  forall (kfuel : nat) (l0 : list (TTypeB n)),
  loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz = (l, l0) ->
  forall l2 : list (TType n),
  loop_j_return_QPL_fuel jfuel kfuel n i j QP (map TTypeBtoTType L) Lz = (l1, l2) 
  -> l = l1.
Proof. gen Lz QP i j L. gen l l1.
  induction jfuel; intros; simpl in *; auto.
  - destruct (rev Lz) eqn:E; simpl in *; auto.
    + inversion H. inversion H0. subst. auto.
    + inversion H. inversion H0. subst. auto.
  - destruct j.
    + destruct (rev Lz) eqn:E; simpl in *; auto.
      * inversion H. inversion H0. subst. auto.
      * inversion H. inversion H0. subst. auto.
    + rewrite ! map_length in *.
      destruct (existsb (fun qp : nat * nat => (snd qp =? length L - S j)%nat) QP) eqn:E; simpl in *; auto.
      * eapply IHjfuel.
        -- apply H.
        -- apply H0.
      * rewrite map_nth with (d := defaultTB_I n) in *.
        destruct (nth i (snd (nth (length L - S j) L (defaultTB_I n))) gI) eqn:E1;
          try setoid_rewrite E1 in H;
        destruct (nth i (snd (TTypeBtoTType (nth (length L - S j) L (defaultTB_I n)))) gI) eqn:E2;
          try setoid_rewrite E2 in H0;
          unfold TTypeBtoTType in E2; simpl in E2; rewrite E1 in E2; try discriminate.
        -- eapply IHjfuel.
           ++ apply H.
           ++ apply H0.
        -- inversion H. inversion H0. subst. auto.
        -- inversion H. inversion H0. subst. auto.
        -- eapply IHjfuel.
           ++ apply H.
           ++ apply H0.
Qed.

Lemma TTypeBtoTType_respects_loop_replaceT_Z_fuel (kfuel n i j k : nat) (L : list (TTypeB n)):
  map TTypeBtoTType (loop_replaceTB_Z_fuel kfuel n i j k L) =
  loop_replaceT_Z_fuel kfuel n i j k (map TTypeBtoTType L).
Proof. gen i j k L. induction kfuel; intros; simpl in *; auto.
  destruct k; simpl; auto.
  rewrite ! map_length.
  destruct (length L - S k =? j)%nat; simpl; auto.
  destruct (nth i (snd (nth (length L - S k) L (defaultTB_I n))) gI) eqn:E1;
    destruct (nth i (snd (nth (length L - S k) (map TTypeBtoTType L) (defaultT_I n))) gI) eqn:E2;
    rewrite map_nth with (d := defaultTB_I n) in E2;
    unfold TTypeBtoTType in E2; simpl in E2; setoid_rewrite E1 in E2; try discriminate; simpl; auto.
  rewrite ! map_nth with (d := defaultTB_I n).
  setoid_rewrite <- TTypeBtoTType_respects_mult.
  rewrite <- switch_map.
  auto.
Qed.

Lemma TTypeBtoTType_respects_loop_replaceT_XY_fuel (kfuel n i j k : nat) (L : list (TTypeB n)):
  map TTypeBtoTType (loop_replaceTB_XY_fuel kfuel n i j k L) =
  loop_replaceT_XY_fuel kfuel n i j k (map TTypeBtoTType L).
Proof. gen i j k L. induction kfuel; intros; simpl in *; auto.
  destruct k; simpl; auto.
  rewrite ! map_length.
  destruct (length L - S k =? j)%nat; simpl; auto.
  destruct (nth i (snd (nth (length L - S k) L (defaultTB_I n))) gI) eqn:E1;
    destruct (nth i (snd (nth (length L - S k) (map TTypeBtoTType L) (defaultT_I n))) gI) eqn:E2;
    rewrite map_nth with (d := defaultTB_I n) in E2;
    unfold TTypeBtoTType in E2; simpl in E2; setoid_rewrite E1 in E2; try discriminate; simpl; auto.
  - rewrite ! map_nth with (d := defaultTB_I n).
    setoid_rewrite <- TTypeBtoTType_respects_mult.
    rewrite <- switch_map.
    auto.
  - rewrite ! map_nth with (d := defaultTB_I n).
    setoid_rewrite <- TTypeBtoTType_respects_mult.
    rewrite <- switch_map.
    auto.
Qed.

Lemma TTypeBtoTType_respects_loop_j_return_QPL_fuel_snd (n : nat) (L : list (TTypeB n)) (jfuel : nat) (i j : nat) (QP : list (nat * nat)) (l0 : list (TTypeB n)) (l2 : list (TType n)) (Lz : list nat):
  forall (kfuel : nat) (l : list (nat * nat)),
  loop_j_return_QPLB_fuel jfuel kfuel n i j QP L Lz = (l, l0) ->
  forall  l1 : list (nat * nat),
  loop_j_return_QPL_fuel jfuel kfuel n i j QP (map TTypeBtoTType L) Lz = (l1, l2) 
  -> map TTypeBtoTType l0 = l2.
Proof. gen Lz QP i j L. gen l0 l2.
  induction jfuel; intros; simpl in *; auto.
  - destruct (rev Lz) eqn:E; simpl in *; auto.
    + inversion H. inversion H0. subst. auto.
    + inversion H. inversion H0. subst.
      rewrite map_length.
      apply TTypeBtoTType_respects_loop_replaceT_Z_fuel.
  - destruct j.
    + destruct (rev Lz) eqn:E; simpl in *; auto.
      * inversion H. inversion H0. subst. auto.
      * inversion H. inversion H0. subst.
        rewrite map_length.
        apply TTypeBtoTType_respects_loop_replaceT_Z_fuel.
    + rewrite ! map_length in *.
      destruct (existsb (fun qp : nat * nat => (snd qp =? length L - S j)%nat) QP) eqn:E; simpl in *; auto.
      * eapply IHjfuel.
        -- apply H.
        -- apply H0.
      * rewrite map_nth with (d := defaultTB_I n) in *.
        destruct (nth i (snd (nth (length L - S j) L (defaultTB_I n))) gI) eqn:E1;
          try setoid_rewrite E1 in H;
        destruct (nth i (snd (TTypeBtoTType (nth (length L - S j) L (defaultTB_I n)))) gI) eqn:E2;
          try setoid_rewrite E2 in H0;
          unfold TTypeBtoTType in E2; simpl in E2; rewrite E1 in E2; try discriminate.
        -- eapply IHjfuel.
           ++ apply H.
           ++ apply H0.
        -- inversion H. inversion H0. subst.
           apply TTypeBtoTType_respects_loop_replaceT_XY_fuel.
        -- inversion H. inversion H0. subst.
           apply TTypeBtoTType_respects_loop_replaceT_XY_fuel.
        -- eapply IHjfuel.
           ++ apply H.
           ++ apply H0.
Qed.

Lemma TTypeBtoTType_respects_loop_normalization_fuel_fst (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP l l1 : list (nat * nat)) (L : list (TTypeB n)):
  forall (l0 : list (TTypeB n)),
  loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L = (l, l0) ->
  forall l2 : list (TType n),
   loop_normalization_fuel ifuel jfuel kfuel lq n i QP (map TTypeBtoTType L) = (l1, l2) 
  -> l = l1.
Proof. intros l0 H l2 H0.
  gen jfuel kfuel lq i QP. gen l l1 L l0 l2.
  induction ifuel; intros. 
  - simpl in *.
    inversion H.
    inversion H0.
    subst. auto.
  - simpl in *.
    destruct i.
    + inversion H.
      inversion H0.
      subst. auto.
    + rewrite map_length in H0.
      destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
      destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP (map TTypeBtoTType L) []) eqn:E'.
      pose (TTypeBtoTType_respects_loop_j_return_QPL_fuel_fst n L jfuel (nth (n - S i) lq 0%nat) (length L) QP l3 l5 [] kfuel l4 E l6 E') as H1.
      pose (TTypeBtoTType_respects_loop_j_return_QPL_fuel_snd n L jfuel (nth (n - S i) lq 0%nat) (length L) QP l4 l6 [] kfuel l3 E l5 E') as H2.
      remember H1 as H1'. clear H1 HeqH1'. 
      remember H2 as H2'. clear H2 HeqH2'.
      subst.
      specialize (IHifuel l l1 l4 l0 l2 jfuel kfuel lq i  l5 H H0).
      auto.
Qed.

Lemma TTypeBtoTType_respects_loop_normalization_fuel_snd (ifuel jfuel kfuel : nat) (lq : list nat) (n i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)) (l0 : list (TTypeB n)) (l2 : list (TType n)):
  forall l : list (nat * nat),
  loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L = (l, l0) ->
  forall l1 : list (nat * nat),
   loop_normalization_fuel ifuel jfuel kfuel lq n i QP (map TTypeBtoTType L) = (l1, l2) 
  -> map TTypeBtoTType l0 = l2.
Proof. intros l H l1 H0. 
  gen jfuel kfuel lq i QP. gen L l0 l2 l l1.
  induction ifuel; intros. 
  - simpl in *.
    inversion H.
    inversion H0.
    subst. auto.
  - simpl in *.
    destruct i.
    + inversion H.
      inversion H0.
      subst. auto.
    + rewrite map_length in H0.
      destruct (loop_j_return_QPLB_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP L []) eqn:E.
      destruct (loop_j_return_QPL_fuel jfuel kfuel n (nth (n - S i) lq 0%nat) (length L) QP (map TTypeBtoTType L) []) eqn:E'.
      pose (TTypeBtoTType_respects_loop_j_return_QPL_fuel_fst n L jfuel (nth (n - S i) lq 0%nat) (length L) QP l3 l5 [] kfuel l4 E l6 E') as H1.
      pose (TTypeBtoTType_respects_loop_j_return_QPL_fuel_snd n L jfuel (nth (n - S i) lq 0%nat) (length L) QP l4 l6 [] kfuel l3 E l5 E') as H2.
      remember H1 as H1'. clear H1 HeqH1'. 
      remember H2 as H2'. clear H2 HeqH2'.
      subst.
      specialize (IHifuel l4 l0 l2 l l1 jfuel kfuel lq i l5 H H0).
      auto.
Qed.

Lemma TTypeBtoTType_respects_normalize_fuel : forall (ifuel jfuel kfuel: nat) (lq : list nat) {n : nat} (i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    map TTypeBtoTType
      (map snd
         (loop_normalizationB_final_fuel ifuel jfuel kfuel lq n i QP L)) =
      map snd
        (loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP
           (map TTypeBtoTType L)).
Proof. intros ifuel jfuel kfuel lq n i QP L. 
  unfold loop_normalizationB_final_fuel, loop_normalization_final_fuel.
  destruct (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalization_fuel ifuel jfuel kfuel lq n i QP (map TTypeBtoTType L)) eqn:E'.
  pose (TTypeBtoTType_respects_loop_normalization_fuel_fst ifuel jfuel kfuel lq n i QP l l1 L l0 E l2 E') as H.
  pose (TTypeBtoTType_respects_loop_normalization_fuel_snd ifuel jfuel kfuel lq n i QP L l0 l2 l E l1 E') as H0.
  remember H as H'. clear H HeqH'. remember H0 as H0'. clear H0 HeqH0'.
  subst. 
  rewrite ! map_app.
  rewrite ! map_snd_combine. 
  - rewrite TTypeBtoTType_respects_lexicographic.
    rewrite ! map_length.
    rewrite ! map_map.
    f_equal.
    + f_equal.
      apply functional_extensionality; intros.
      simpl. unfold TTypeBtoTType.
      rewrite map_nth with (d := defaultTB_I n). auto.
    + f_equal. f_equal.
      apply functional_extensionality; intros.
      unfold TTypeBtoTType.
      rewrite map_nth with (d := defaultTB_I n); auto.
  - rewrite repeat_length.
    unfold lexicographic.
    rewrite rev_length.
    pose (TOrd.Permuted_sort (map (fun p : nat => nth p (map TTypeBtoTType l0) (defaultT_I n))
          (filter (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l1))
             (seq 0 (length (map TTypeBtoTType l0)))))) as H0.
    apply Permutation_length in H0.
    rewrite <- H0.
    rewrite ! map_length. auto.
  - unfold lexicographicB.
    rewrite repeat_length.
    rewrite rev_length.
    pose (TBOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultTB_I n))
          (filter (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l1))
             (seq 0 (length l0))))) as H0.
    apply Permutation_length in H0.
    rewrite <- H0.
    rewrite map_length. auto.
Qed.

Lemma fst_preserves_loop_normalizationB_final_fuel : forall (ifuel jfuel kfuel: nat) (lq : list nat) {n : nat} (i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    map fst (loop_normalizationB_final_fuel ifuel jfuel kfuel lq n i QP L) =
        map fst (loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP
                   (map TTypeBtoTType L)).
Proof. intros ifuel jfuel kfuel lq n i QP L. 
  unfold loop_normalizationB_final_fuel, loop_normalization_final_fuel.
  destruct (loop_normalizationB_fuel ifuel jfuel kfuel lq n i QP L) eqn:E.
  destruct (loop_normalization_fuel ifuel jfuel kfuel lq n i QP (map TTypeBtoTType L)) eqn:E'.
  pose (TTypeBtoTType_respects_loop_normalization_fuel_fst ifuel jfuel kfuel lq n i QP l l1 L l0 E l2 E') as H.
  pose (TTypeBtoTType_respects_loop_normalization_fuel_snd ifuel jfuel kfuel lq n i QP L l0 l2 l E l1 E') as H0.
  remember H as H'. clear H HeqH'. remember H0 as H0'. clear H0 HeqH0'.
  subst.
  rewrite ! map_app.
  rewrite ! map_fst_combine. 
  - rewrite ! map_length.
    rewrite ! map_map. simpl. auto.
  - rewrite repeat_length.
    unfold lexicographic.
    rewrite rev_length.
    pose (TOrd.Permuted_sort (map (fun p : nat => nth p (map TTypeBtoTType l0) (defaultT_I n))
          (filter (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l1))
             (seq 0 (length (map TTypeBtoTType l0)))))) as H0.
    apply Permutation_length in H0.
    rewrite <- H0.
    rewrite ! map_length. auto.
  - unfold lexicographicB.
    rewrite repeat_length.
    rewrite rev_length.
    pose (TBOrd.Permuted_sort (map (fun p : nat => nth p l0 (defaultTB_I n))
          (filter (fun a : nat => ¬ existsb (fun p : nat => if Nat.eq_dec p a then true else false) (map snd l1))
             (seq 0 (length l0))))) as H0.
    apply Permutation_length in H0.
    rewrite <- H0.
    rewrite map_length. auto.
Qed.

Lemma TTypeBtoTType_respects_loop_normalizationB_final : forall (ifuel jfuel kfuel: nat) (lq : list nat) {n : nat} (i : nat) (QP : list (nat * nat)) (L : list (TTypeB n)),
    length L <> 0%nat -> NoDup (map snd QP) -> incl (map snd QP) (List.seq 0%nat (length L)) ->
    map (fun p => (fst p, TTypeBtoTType (snd p))) (loop_normalizationB_final_fuel ifuel jfuel kfuel lq n i QP L) =
      (loop_normalization_final_fuel ifuel jfuel kfuel lq n i QP (map TTypeBtoTType L)).
Proof. intros ifuel jfuel kfuel lq n i QP L H H0 H1. 
  apply nth_ext with (d := (None, defaultT_I n)) (d' := (None, defaultT_I n)).
  - rewrite map_length.
    rewrite loop_normalization_final_fuel_length; try rewrite map_length; auto.
    rewrite loop_normalizationB_final_fuel_length; auto.
  - intros n0 H2. 
    assert ((fun p : option nat * TTypeB n => (fst p, TTypeBtoTType (snd p))) (None, defaultTB_I n) = (None, defaultT_I n)).
    { simpl. f_equal. }
    rewrite <- H3.
    rewrite map_nth with (f := (fun p : option nat * TTypeB n => (fst p, TTypeBtoTType (snd p)))) (d := (None, defaultTB_I n)).
    simpl. replace (TTypeBtoTType (defaultTB_I n)) with (defaultT_I n) by auto.
    rewrite <- map_nth with (f := fst). rewrite <- map_nth with (f := snd). 
    rewrite <- map_nth with (f := TTypeBtoTType). simpl. 
    replace (TTypeBtoTType (defaultTB_I n)) with (defaultT_I n) by auto.
    rewrite fst_preserves_loop_normalizationB_final_fuel.
    rewrite TTypeBtoTType_respects_normalize_fuel.
    replace None with (fst (@None nat, defaultT_I n)) by auto.
    replace (defaultT_I n) with (snd (@None nat, defaultT_I n)) by auto.
    rewrite ! map_nth with (d := (None, defaultT_I n)).
    rewrite <- surjective_pairing. simpl. auto.
Qed.

Lemma TTypeBtoTType_respects_pivots_normalizeB (start n : nat) (L : list (TTypeB n)):
  map (fun p => (fst p, TTypeBtoTType (snd p))) (pivots_normalizeB start L) =
    pivots_normalize start (map TTypeBtoTType L).
Proof. bdestruct (length L =? 0)%nat.
  - rewrite length_zero_iff_nil in H.
    subst.
    rewrite pivots_normalize_nil.
    rewrite pivots_normalizeB_nil.
    simpl. auto.
  - unfold pivots_normalize, pivots_normalizeB.
    rewrite <- loop_normalizationB_final_fuel_saturated_base with (jfuel := length L) (kfuel := length L); try lia.
    rewrite <- loop_normalization_final_fuel_saturated_base with (jfuel := length L) (kfuel := length L); try rewrite map_length; try lia.
    apply TTypeBtoTType_respects_loop_normalizationB_final; auto.
    simpl. apply NoDup_nil. simpl. apply incl_nil_l.
Qed.

Lemma TTypeBtoTType_respects_normalize : forall (start : nat) {n : nat} (LB : list (TTypeB n)),
    map TTypeBtoTType (normalizeB start LB) = normalize start (map TTypeBtoTType LB).
Proof. intros start n LB.
  unfold normalizeB, normalize.
  rewrite <- TTypeBtoTType_respects_pivots_normalizeB.
  rewrite ! map_map. simpl. auto.
Qed.
  

(** ** Parsing using typeclasses ** **)

Class ParseCB (b : CB) (c : C) := {
  parsecb : CBtoC b = c
}.
Global Hint Mode ParseCB - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance ParseCB_mult (a b : CB) (c d : C):
  ParseCB a c -> ParseCB b d ->
  ParseCB (CBmult a b) (Cmult c d).
Proof. intros H H0. 
  constructor.
  inversion H. inversion H0.
  rewrite <- parsecb0, <- parsecb1.
  apply CBtoC_respects_mult.
Qed.

#[export]
Instance ParseCB_opp (a : CB) (c : C):
  ParseCB a c ->
  ParseCB (CBopp a) (Copp c).
Proof. intros H.
  inversion H.
  rewrite <- parsecb0.
  constructor.
  apply CBtoC_respects_opp.
Qed.

#[export]
Instance ParseCB_mCi:
  ParseCB (cb true true) (Copp Ci).
Proof. constructor. auto. Qed.

#[export]
Instance ParseCB_mC1:
  ParseCB (cb true false) (Copp C1).
Proof. constructor. auto. Qed.

#[export]
Instance ParseCB_Ci:
  ParseCB (cb false true) Ci.
Proof. constructor. auto. Qed.

#[export]
Instance ParseCB_C1:
  ParseCB (cb false false) C1.
Proof. constructor. auto. Qed.

Unset Typeclasses Unique Instances.



Class ParseTB {n : nat} (TB : TTypeB n) (T : TType n) := {
  parsetb : TTypeBtoTType TB = T
}.
Global Hint Mode ParseTB - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance ParseTB_coef {n : nat} (a : CB) (c : C) (lp : list Pauli):
  ParseCB a c ->
  @ParseTB n (a, lp) (c, lp).
Proof. intros H.
  inversion H.
  rewrite <- parsecb0.
  constructor.
  unfold TTypeBtoTType.
  simpl. auto.
Qed.

Unset Typeclasses Unique Instances.




Class ParseNorm {n : nat} (LB : list (TTypeB n)) (L : list (TType n)) := {
  parsenorm : map TTypeBtoTType LB = L
}.
Global Hint Mode ParseNorm - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance ParseNorm_cons {n : nat} (LB : list (TTypeB n)) (L : list (TType n)) (tb : TTypeB n) (t : TType n) :
  ParseTB tb t ->
  ParseNorm LB L -> 
  ParseNorm (tb :: LB) (t :: L).
Proof. intros H H0.
  constructor.
  simpl.
  f_equal.
  inversion H; auto.
  inversion H0; auto.
Qed.

#[export]
Instance ParseNorm_nil {n : nat}: 
  @ParseNorm n [] [].
Proof. constructor. auto. Qed.

Unset Typeclasses Unique Instances.

(*
Class ParseNorm {n : nat} (LB : list (TTypeB n)) (L : list (TType n)) := {
  parsenorm : map TTypeBtoTType LB = L
}.
Global Hint Mode ParseNorm - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance ParseNorm_cons {n : nat} (LB : list (TTypeB n)) (L : list (TType n)) (a : CB) (c : C) (lp : list Pauli) :
  ParseCB a c ->
  ParseNorm LB L -> 
  @ParseNorm n ((a,lp) :: LB) ((c,lp) :: L).
Proof. intros H H0.
  constructor.
  simpl.
  f_equal.
  inversion H; auto.
  unfold TTypeBtoTType. simpl. rewrite parsecb0. auto.
  inversion H0; auto.
Qed.

#[export]
Instance ParseNorm_nil {n : nat}: 
  @ParseNorm n [] [].
Proof. constructor. auto. Qed.

Unset Typeclasses Unique Instances.
*)


Lemma parse_norm_eq {n : nat} (LB : list (TTypeB n)) (L : list (TType n)) : 
  ParseNorm LB L ->
  L = map TTypeBtoTType LB.
Proof. intros H.
  inversion H.
  auto.
Qed.

(*
(*** This needs to be in Automation.v ***)
Ltac solveNormalize :=
  repeat match goal with
    | |- context [normalize _ ?a] => 
        rewrite (parse_norm_eq _ a _); 
        rewrite <- ! TTypeBtoTType_respects_normalize
    end;
  lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt Q2R IZR Cexp PI sin cos Copp (* triple *)].




(*** Example ***)

Definition bg1' : TTypeB 9 := (cb false false, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]).
Definition bg2' : TTypeB 9 := (cb false false, [gI; gZ; gZ; gI; gI; gI; gI; gI; gI]).
Definition bg3' : TTypeB 9 := (cb false false, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]).
Definition bg4' : TTypeB 9 := (cb false false, [gI; gI; gI; gI; gZ; gZ; gI; gI; gI]).
Definition bg5' : TTypeB 9 := (cb false false, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]).
Definition bg6' : TTypeB 9 := (cb false false, [gI; gI; gI; gI; gI; gI; gI; gZ; gZ]).
Definition bg7' : TTypeB 9 := (cb false false, [gX; gX; gX; gX; gX; gX; gI; gI; gI]).
Definition bg8' : TTypeB 9 := (cb false false, [gI; gI; gI; gX; gX; gX; gX; gX; gX]).
Definition bXbar' : TTypeB 9 := (cb false false, [gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ]).
Definition bZbar' : TTypeB 9 := (cb false false, [gX; gX; gX; gX; gX; gX; gX; gX; gX]).
Definition bZL' : list (TTypeB 9) := [bg1'; bg2'; bg3'; bg4'; bg5'; bg6'; bg7'; bg8'; bZbar'].
Definition bXL' : list (TTypeB 9) := [bg1'; bg2'; bg3'; bg4'; bg5'; bg6'; bg7'; bg8'; bXbar'].

Compute pivotsB 0 bXL'.
(*   = [(0%nat, gX); (1%nat, gZ); (2%nat, gZ); (3%nat, gX); (
        4%nat, gZ); (5%nat, gZ); (6%nat, gZ); (7%nat, gZ); (
        8%nat, gZ)] *)
Compute normalizeB 0 bXL'.
(*      = [(cb false false, [gX; gX; gX; gI; gI; gI; gX; gX; gX]);
        (cb false false, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]);
        (cb false false, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI]);
        (cb false false, [gI; gI; gI; gX; gX; gX; gX; gX; gX]);
        (cb false false, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]);
        (cb false false, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI]);
        (cb false false, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI]);
        (cb false false, [gZ; gI; gI; gZ; gI; gI; gI; gZ; gI]);
        (cb false false, [gZ; gI; gI; gZ; gI; gI; gI; gI; gZ])] *)

Goal (@normalizeB 0 9
([
(cb false false, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI]);
(cb false false, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]);
(cb false false, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI]);
(cb false false, [gX; gX; gX; gX; gX; gX; gI; gI; gI]);
(cb false false, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]);
(cb false false, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI]);
(cb false false, [gX; gX; gX; gI; gI; gI; gX; gX; gX]);
(cb false false, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]);
(cb false false, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])
]) = normalizeB 0 bXL').
time compute. 
(* time compute
Tactic call ran for 0.021 secs (0.02u,0.s) (success) *)
reflexivity.
Qed.


Definition g1' : TType 9 := (C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]).
Definition g2' : TType 9 := (C1, [gI; gZ; gZ; gI; gI; gI; gI; gI; gI]).
Definition g3' : TType 9 := (C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]).
Definition g4' : TType 9 := (C1, [gI; gI; gI; gI; gZ; gZ; gI; gI; gI]).
Definition g5' : TType 9 := (C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]).
Definition g6' : TType 9 := (C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gZ]).
Definition g7' : TType 9 := (C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI]).
Definition g8' : TType 9 := (C1, [gI; gI; gI; gX; gX; gX; gX; gX; gX]).
Definition Xbar' : TType 9 := (C1, [gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ]).
Definition Zbar' : TType 9 := (C1, [gX; gX; gX; gX; gX; gX; gX; gX; gX]).
Definition ZL' : list (TType 9) := [g1'; g2'; g3'; g4'; g5'; g6'; g7'; g8'; Zbar'].
Definition XL' : list (TType 9) := [g1'; g2'; g3'; g4'; g5'; g6'; g7'; g8'; Xbar'].

(*
Goal (@normalize 0 9
([
(C1, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI]);
(C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI]);
(C1, [gX; gX; gX; gI; gI; gI; gX; gX; gX]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])
]) = normalize 0 XL').
time (lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt Q2R IZR Cexp PI sin cos Copp (* triple *)]; Csimpl).
(* Tactic call ran for 0.577 secs (0.571u,0.002s) (success) *)
reflexivity.
Qed.
*)

Goal (@normalize 0 9
([
(C1, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI]);
(C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]);
(C1, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI]);
(C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]);
(C1, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI]);
(C1, [gX; gX; gX; gI; gI; gI; gX; gX; gX]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]);
(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])
]) = normalize 0 XL').
time solveNormalize.
(* time solveNormalize
Tactic call ran for 0.043 secs (0.042u,0.s) (success) *)
reflexivity.
Qed.

*)
