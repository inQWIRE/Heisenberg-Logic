Require Import Complex.
Require Import QArith Qreals.

(* A computational subset of the complex numbers, 
  where [(a,b,c,d)] represents [a + b * Ci + c / √2 + d * Ci / √2 ] *)
Inductive QC : Set := 
  | mkQC (a b c d : Q) : QC.

Definition QC2C (q : QC) : C :=
  let '(mkQC a b c d) := q in 
  (Q2R a + Q2R b / √ 2, Q2R c + Q2R d / √ 2)%R.

Definition Q2QC (q : Q) : QC :=
  mkQC q 0 0 0.

Definition QCeq : relation QC := 
  fun q q' => 
  let '(mkQC a b c d) := q in 
  let '(mkQC a' b' c' d') := q' in 
  Qeq a a' /\ Qeq b b' /\ Qeq c c' /\ Qeq d d'.

Definition QCeqb (q r : QC) : bool :=
  let '(mkQC a b c d) := q in 
  let '(mkQC a' b' c' d') := r in 
  Qeq_bool a a' && Qeq_bool b b' && Qeq_bool c c' && Qeq_bool d d'.

Definition QCplus (q q' : QC) : QC :=
  let '(mkQC a b c d) := q in 
  let '(mkQC a' b' c' d') := q' in 
  mkQC (a + a') (b + b') (c + c') (d + d').

Definition QCopp (q : QC) : QC :=
  let '(mkQC a b c d) := q in 
  mkQC (-a) (-b) (-c) (-d).

Definition QCminus q r : QC := QCplus q (QCopp r).

Definition QCmult (q q' : QC) : QC :=
  let '(mkQC a b c d) := q in 
  let '(mkQC a' b' c' d') := q' in 
  mkQC 
    (a * a' + b * b' / 2 - c * c' - d * d' / 2) 
    (a * b' + b * a'     - c * d' - d * c')
    (a * c' + b * d' / 2 + c * a' + d * b' / 2)
    (a * d' + b * c'     + c * b' + d * a').

Definition QCinv (q : QC) : QC :=
  let '(mkQC a b c d) := q in 
  let q_den_terms := (a * a + b * b / 2 + c * c + d * d / 2)%Q in 
  let root2_den_terms := (2 * a * b + 2 * c * d)%Q in 
  let den_fact := (q_den_terms * q_den_terms - root2_den_terms * root2_den_terms / 2) in 
  QCmult (mkQC a b (-c) (-d)) (
    mkQC (q_den_terms / den_fact) (-root2_den_terms / den_fact) 
    0 0
  ).

Definition QCdiv (q r : QC) : QC := QCmult q (QCinv r).

Definition QCconj (q : QC) : QC :=
  let '(mkQC a b c d) := q in 
  mkQC a b (-c) (-d).

Declare Scope QC_scope.
Delimit Scope QC_scope with QC.
Bind Scope QC_scope with QC.

(* Levels for these notations are inherited from existing definitions 
  in other scopes *)
Notation "q == r" := (QCeq q r) : QC_scope. 
Notation "q + r" := (QCplus q r) : QC_scope. 
Notation "q - r" := (QCminus q r) : QC_scope. 
Notation "q * r" := (QCmult q r) : QC_scope. 
Notation "q / r" := (QCdiv q r) : QC_scope. 
Notation "- q" := (QCopp q) : QC_scope.
Notation "/ q" := (QCinv q) : QC_scope.
Notation "q ^*" := (QCconj q) : QC_scope.

Open Scope QC_scope.

Lemma QCeq_refl q : q == q.
Proof.
  destruct q as [a b c d].
  repeat split.
Qed.

Lemma QCeq_sym q r : q == r -> r == q.
Proof.
  destruct q as [a b c d].
  destruct r as [a' b' c' d'].
  cbn.
  intros (? & ? & ? & ?);
  repeat split; now symmetry.
Qed.

Lemma QCeq_trans q r s : q == r -> r == s -> q == s.
Proof.
  destruct q as [a b c d].
  destruct r as [a' b' c' d'].
  destruct s as [a'' b'' c'' d''].
  cbn.
  intros (? & ? & ? & ?) (? & ? & ? & ?).
  repeat split; now etransitivity; eauto.
Qed.

Add Parametric Relation : QC QCeq 
  reflexivity proved by QCeq_refl
  symmetry proved by QCeq_sym
  transitivity proved by QCeq_trans
  as QCeq_setoid.

Lemma Qeq_bool_spec q r : reflect (Qeq q r) (Qeq_bool q r).
Proof. 
  apply iff_reflect; now rewrite Qeq_bool_iff. 
Qed.

Lemma QCeqb_spec q r : reflect (q == r) (QCeqb q r).
Proof.
  destruct q as [a b c d], r as [a' b' c' d'].
  cbn.
  apply iff_reflect.
  rewrite 3!andb_true_iff, 4 Qeq_bool_iff.
  firstorder.
Qed.

#[export] Hint Resolve Qeq_bool_spec QCeqb_spec : bdestruct.

Lemma QCeqb_iff q r : QCeqb q r = true <-> q == r.
Proof.
  symmetry.
  apply reflect_iff, QCeqb_spec.
Qed.

Lemma QCeqb_eq q r : QCeqb q r = true -> q == r.
Proof.
  apply QCeqb_iff.
Qed.

Add Parametric Morphism : QC2C with signature
  QCeq ==> eq as QC2C_mor.
Proof.
  intros [a b c d] [a' b' c' d'] (Ha & Hb & Hc & Hd).
  cbn.
  now rewrite Ha, Hb, Hc, Hd.
Qed.

Add Parametric Morphism : mkQC with signature
  Qeq ==> Qeq ==> Qeq ==> Qeq ==> QCeq as mkQC_mor.
Proof.
  cbn.
  easy.
Qed.

Add Parametric Morphism : QCeqb with signature
  QCeq ==> QCeq ==> eq as QCeqb_mor.
Proof.
  intros x x' H y y' H'.
  apply Bool.eq_iff_eq_true.
  rewrite 2 QCeqb_iff.
  now rewrite H, H'.
Qed.

Add Parametric Morphism : QCplus with signature
  QCeq ==> QCeq ==> QCeq as QCplus_mor.
Proof.
  intros [] [] Heqs [] [] Heqs'.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCmult with signature
  QCeq ==> QCeq ==> QCeq as QCmult_mor.
Proof.
  intros [] [] Heqs [] [] Heqs'.
  cbn in *.
  repeat split; repeat f_equiv; easy.
Qed.

Add Parametric Morphism : QCopp with signature
  QCeq ==> QCeq as QCopp_mor.
Proof.
  intros [] [] Heqs.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCconj with signature
  QCeq ==> QCeq as QCconj_mor.
Proof.
  intros [] [] Heqs.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCinv with signature
  QCeq ==> QCeq as QCinv_mor.
Proof.
  intros [] [] Heqs.
  unfold QCinv.
  destruct Heqs as (Ha & Hb & Hc & Hd).
  now rewrite Ha, Hb, Hc, Hd.
Qed.

Add Parametric Morphism : QCminus with signature
  QCeq ==> QCeq ==> QCeq as QCminus_mor.
Proof.
  intros ? ? H ? ? H'.
  unfold QCminus.
  now rewrite H, H'.
Qed.

Add Parametric Morphism : QCdiv with signature
  QCeq ==> QCeq ==> QCeq as QCdiv_mor.
Proof.
  intros ? ? H ? ? H'.
  unfold QCdiv.
  now rewrite H, H'.
Qed.

Coercion Q2QC : Q >-> QC.

Lemma QCeq_iff_QCminus_eq_0 q r : q == r <-> q - r == 0.
Proof.
  destruct q, r.
  cbn.
  lra.
Qed.

Section QC2C.

Local Open Scope C_scope.
Local Coercion QC2C : QC >-> C.

Lemma QC2C_plus q r : QC2C (q + r) = q + r.
Proof.
  destruct q, r.
  cbn.
  rewrite !Q2R_plus.
  lca.
Qed.

Lemma QC2C_mult q r : QC2C (q * r) = q * r.
Proof.
  destruct q, r.
  cbn.
  rewrite !Q2R_minus, !Q2R_plus, !(Q2R_div _ 2), !Q2R_mult by lra.
  replace (Q2R 2) with (2%R) by lra.
  pose proof sqrt2_neq_0.
  apply c_proj_eq; cbn; R_field.
Qed.

Lemma QC2C_opp q : QC2C (- q) = - q.
Proof.
  destruct q.
  cbn.
  rewrite !Q2R_opp.
  lca.
Qed.

Lemma QC2C_minus q r : QC2C (q - r) = q - r.
Proof.
  unfold QCminus.
  rewrite QC2C_plus, QC2C_opp.
  reflexivity.
Qed.

Section Irrational.
Local Open Scope R_scope.
Local Lemma Q2R_0 : Q2R 0 = 0.
Proof. lra. Qed.
Local Lemma Q2R_0' q : (q == 0)%Q -> Q2R q = 0.
Proof. intros ->; apply Q2R_0. Qed.
Local Lemma Q2R_inv' q : Q2R (/q) = / Q2R q.
Proof.
  bdestruct (Qeq_bool q 0).
  - rewrite H.
    rewrite 2 Q2R_0' by reflexivity.
    now rewrite Rinv_0.
  - now apply Q2R_inv.
Qed.
Local Lemma Q2R_div' q r : Q2R (q / r) = Q2R q / Q2R r.
Proof.
  unfold Qdiv, Rdiv.
  now rewrite Q2R_mult, Q2R_inv'.
Qed.
Local Lemma Q2R_0_inv : forall q, Q2R q = 0%R -> Qeq q 0.
Proof.
  intros ?.
  rewrite <- RMicromega.Q2R_0.
  apply eqR_Qeq.
Qed.

Local Lemma sqrt2_irrational' q : √ 2 <> Q2R q.
Proof.
  pose proof (sqrt2_irrational (Qnum q) (Z.pos (Qden q)) ltac:(lia)) as Hne.
  intros Heq.
  apply Hne.
  rewrite Heq.
  unfold Q2R.
  field.
  apply eq_IZR_contrapositive.
  lia.
Qed.

Local Lemma sqrt2_irrational'' q r : (Q2R q * √ 2 + Q2R r = 0%R <-> 
  q == 0 /\ r == 0)%R%Q.
Proof.
  split.
  - bdestruct (Qeq_bool q 0).
    1: {
      rewrite H, Q2R_0, Rmult_0_l, Rplus_0_l.
      now intros ->%Q2R_0_inv.
    }
    bdestruct (Qeq_bool r 0).
    1: {
      rewrite H0, Q2R_0, Rplus_0_r.
      intros Hprod%Rmult_integral.
      now destruct Hprod as [->%Q2R_0_inv | Hf%sqrt2_neq_0].
    }
    intros Heq.
    assert (Hsqrt2 : √ 2 = Q2R (- r / q)). 1: {
      rewrite Q2R_div', Q2R_opp.
      replace (Q2R r) with (- (Q2R q * √ 2)) by lra.
      field.
      now intros ?%Q2R_0_inv.
    }
    now apply sqrt2_irrational' in Hsqrt2.
  - intros [-> ->]; lra.
Qed.

(* Local Lemma sqrt2_irrational''' (a b : Q) : 
  Q2R a * Q2R a * 2 + Q2R b * Q2R b = 0 <-> Qeq a 0 /\ Qeq b 0.
Proof.
  split; [|intros [-> ->]; lra].
  intros Heq.
  assert (Q2R a = 0) by nra.
  lra. *)

End Irrational.

Local Lemma Q2R_sqrt2_inj q r : (Q2R q + Q2R r / √2)%R = 0%R <->
  (q == 0 /\ r == 0)%Q.
Proof.
  split.
  - intros Hz.
    apply sqrt2_irrational''.
    replace (Q2R q) with (- Q2R r / √ 2)%R by lra.
    field.
    apply sqrt2_neq_0.
  - intros [-> ->].
    lra.
Qed.

Lemma eqC0_QCeq0 q : QC2C q = C0 -> q == 0.
Proof.
  intros Heq.
  pose proof Heq as Hfst%(f_equal fst).
  pose proof Heq as Hsnd%(f_equal snd).
  destruct q as [a b c d].
  cbn in Hfst, Hsnd.
  apply Q2R_sqrt2_inj in Hfst, Hsnd.
  cbn.
  easy.
Qed.

Lemma eqC_QCeq q r : QC2C q = QC2C r -> q == r.
Proof.
  intros HQCeq.
  apply QCeq_iff_QCminus_eq_0.
  apply eqC0_QCeq0.
  rewrite QC2C_minus.
  rewrite HQCeq.
  lca.
Qed.

Lemma QCneq_0_neq_C0 q : ~ (q == 0) -> QC2C q <> C0.
Proof.
  now intros Hne Heq%eqC0_QCeq0.
Qed.

Lemma QC2C_conj q : QC2C (q ^*) = q ^*.
Proof.
  destruct q.
  cbn.
  rewrite !Q2R_opp.
  lca.
Qed.

Lemma Cinv_alt (c : C) : / c = c ^* * RtoC (/ (fst c * fst c + snd c * snd c)).
Proof.
  unfold Cinv, Cmult, Cconj;
  cbn.
  rewrite 2!Rmult_1_r, 2!Rmult_0_r, Rplus_0_l, Rminus_0_r.
  reflexivity.
Qed.

Section Rops.

Lemma Rmult_plus_div_sqrt2 (a b c d : R) : 
  ((a + b / √2) * (c + d / √ 2) = (a * c + b * d / 2) + (a * d + c * b) / √ 2)%R.
Proof.
  pose proof sqrt2_neq_0.
  R_field.
Qed.


Lemma Rplus_plus_div_sqrt2 (a b c d : R) : 
  ((a + b / √2) + (c + d / √ 2) = (a + c) + (b + d) / √ 2)%R.
Proof.
  lra.
Qed.

Lemma sqrt_square_abs (r : R) : √ (r * r) = Rabs r.
Proof.
  unfold Rabs.
  destruct (Rcase_abs r) as [Hneg | Hnneg].
  - replace (r * r)%R with ((-r)*(-r))%R by lra.
    apply sqrt_square; lra.
  - apply sqrt_square; lra.
Qed.


Local Open Scope R_scope.
Lemma Rdiv_le_Rdiv_iff a b c d : 
  0 < b -> 0 < d -> 
  a / b <= c / d <-> a * d <= c * b.
Proof.
  intros Hb Hd.
  split.
  - intros Hdivs.
    replace (a * d) with (a / b * d * b) by (field; lra).
    apply Rmult_le_compat_r; [lra|].
    replace c with (c / d * d) by (field; lra).
    nra.
  - intros Hle.
    replace (a / b) with (a * d / b / d) by (field; lra).
    replace (c / d) with (c * b / b / d) by (field; lra).
    unfold Rdiv.
    apply Rmult_le_compat_r; [apply Rinv_0_lt_compat in Hd; lra|].
    apply Rmult_le_compat_r; [apply Rinv_0_lt_compat in Hb; lra|].
    lra.
Qed.

Lemma Q2R_le_iff q r : (Q2R q <= Q2R r)%R <-> (q <= r)%Q.
Proof.
  destruct q as [qnum qden], r as [rnum rden].
  unfold Qle.
  cbn.
  unfold Q2R.
  rewrite <- 2 Rdiv_unfold.
  cbn.
  rewrite Rdiv_le_Rdiv_iff by (apply IZR_lt; lia).
  rewrite <- 2 mult_IZR, IZR_le_iff.
  reflexivity.
Qed.

Lemma Q2R_lt_iff q r : (Q2R q < Q2R r)%R <-> (q < r)%Q.
Proof.
  split. 
  - intros Hgt%Rlt_not_le.
    rewrite Q2R_le_iff in Hgt.
    lra.
  - intros Hgt%Qlt_not_le.
    apply Rnot_le_lt.
    now rewrite Q2R_le_iff.
Qed.

Lemma Qabs_pos q : Qle 0 q -> (Qabs.Qabs q == q)%Q.
Proof.
  intros Hq.
  refine (Qabs.Qabs_case q (fun x => x == q)%Q _ _); lra.
Qed.

Lemma Qabs_neg q : Qle q 0 -> (Qabs.Qabs q == - q)%Q.
Proof.
  intros Hq.
  refine (Qabs.Qabs_case q (fun x => x == - q)%Q _ _); lra.
Qed.

Lemma Qabs_0_iff q : (Qabs.Qabs q == 0 <-> q == 0)%Q.
Proof.
  refine (Qabs.Qabs_case q (fun x => x == 0 <-> q == 0)%Q _ _); lra.
Qed.

Lemma Qopp_0_iff q : (- q == 0 <-> q == 0)%Q.
Proof. lra. Qed.

Lemma Q2R_abs q : Q2R (Qabs.Qabs q) = Rabs (Q2R q).
Proof.
  unfold Rabs.
  destruct (Rcase_abs) as [Hneg | Hpos].
  - rewrite <- Q2R_opp.
    rewrite <- !Q2R_0, Q2R_lt_iff in Hneg.
    now rewrite Qabs_neg by lra.
  - apply Rge_le in Hpos.
    rewrite <- !Q2R_0, Q2R_le_iff in Hpos.
    now rewrite Qabs_pos by lra.
Qed.

Lemma Rinv_plus_div_sqrt2 (a b : Q) :
  (* (Q2R a + Q2R b / √ 2 <> 0)%R -> *)
  (/ (Q2R a + Q2R b / √2) = (Q2R a + (- Q2R b) / √ 2) * 
    (/ (Q2R a * Q2R a - Q2R b * Q2R b / 2)))%R.
Proof.
  destruct (Req_dec (Q2R a + Q2R b / √ 2) 0) as [Hz | Hnz].
  - rewrite Hz, Rinv_0.
    apply Q2R_sqrt2_inj in Hz as [-> ->].
    lra.
  - R_field_simplify; [lra|].
    repeat split; [|apply sqrt2_neq_0|].
    + enough (Q2R a * Q2R a <> Q2R b * Q2R b / 2)%R by lra.
      intros Heq%(f_equal sqrt).
      rewrite sqrt_div, 2 sqrt_square_abs in Heq by nra.
      rewrite <- 2 Q2R_abs in Heq.
      assert (Heq' : Q2R (Qabs.Qabs a) + Q2R (-Qabs.Qabs b) / √2 = 0)
        by (rewrite Heq, Q2R_opp; lra).
      apply Q2R_sqrt2_inj in Heq'.
      rewrite Qopp_0_iff, 2 Qabs_0_iff in Heq'.
      rewrite Q2R_sqrt2_inj in Hnz.
      easy.
    + intros Heq%(f_equal (fun x => Rdiv x (√2))).
      rewrite Rdiv_0_l in Heq.
      apply Hnz.
      rewrite <- Heq.
      field.
      apply sqrt2_neq_0.
Qed.

Open Scope Q_scope.
Open Scope QC_scope.
Open Scope C_scope.

Lemma QC2C_inv q : QC2C (/ q) = / QC2C q.
Proof.
  bdestruct (QCeqb q 0).
  - rewrite H.
    rewrite (QCeqb_eq (/ 0) 0 eq_refl).
    replace (QC2C 0) with C0 by lca.
    now rewrite Cinv_0.
  - cbv delta [QCinv] beta.
    destruct q as [a b c d].
    set (q_den_terms := (a * a + b * b / 2 + c * c + d * d / 2)%Q).
    set (root2_den_terms := (2 * a * b + 2 * c * d)%Q).
    cbv zeta.
    set (den_fact := (q_den_terms * q_den_terms - 
      root2_den_terms * root2_den_terms / 2)%Q).
    
    rewrite QC2C_mult.
    rewrite Cinv_alt.
    f_equal.
    1: {
      rewrite <-QC2C_conj; reflexivity.
    }
    apply c_proj_eq; [|cbn; lra].
    cbn.
    rewrite 2 Rmult_plus_div_sqrt2.
    rewrite <- !Q2R_mult.
    replace 2%R with (Q2R 2) by lra.
    rewrite <- !Q2R_div', <- !Q2R_plus.
    replace (Q2R 2) with 2%R by lra.
    rewrite Rplus_plus_div_sqrt2, <- 2 Q2R_plus.
    rewrite Rinv_plus_div_sqrt2.
    transitivity ((Q2R q_den_terms + Q2R (- root2_den_terms) / √ 2) * / Q2R den_fact)%R.
    1: {
      rewrite 2 Rdiv_unfold, Rmult_plus_distr_r.
      rewrite !(Rmult_comm _ (/√2)), Rmult_assoc.
      rewrite 2 Q2R_div', Q2R_opp.
      lra.
    }
    f_equal.
    + f_equal; [|f_equal]; [f_equiv; unfold q_den_terms; lra|].
      rewrite <- Q2R_opp.
      f_equiv.
      unfold root2_den_terms.
      lra.
    + f_equal.
      rewrite <- 2 Q2R_mult.
      replace 2%R with (Q2R 2) by lra.
      rewrite <- Q2R_div', <- Q2R_minus.
      f_equiv.
      unfold den_fact, q_den_terms, root2_den_terms.
      field.
Qed.

Lemma QC2C_div q r : QC2C (q / r) = QC2C q / QC2C r.
Proof.
  unfold QCdiv.
  rewrite QC2C_mult, QC2C_inv; reflexivity.
Qed.

(* FIXME: Move *)
Lemma Q2QC_correct (q : Q) : QC2C (Q2QC q) = Q2R q.
Proof.
  lca.
Qed.


Definition Q2R' (q : Q) : option R :=
  let q' := Qred q in 
  match Qnum q' with 
  | Z0 => None
  | Zpos p => 
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with 
    | true, true => (* q = 1 / 1 *) (1%R)
    | false, true => (* q = +p / 1 *) (IZR (Z.pos p))
    | true, false => (* q = 1 / _ *) (/ IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q'%R)
    end
  | Zneg p => 
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with 
    | true, true => (* q = -1 / 1 *) (- 1%R)%R
    | false, true => (* q = -p / 1 *) (- IZR (Z.pos p))%R
    | true, false => (* q = -1 / _ *) (- / IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q')
    end
  end.

Hint Resolve Pos.eqb_spec Z.eqb_spec : bdestruct.

Lemma Q2R'_correct q : 
  maybe (Q2R' q) 0%R = Q2R q.
Proof.
  rewrite <- (Qred_correct q) at 2.
  cbv delta [Q2R'] beta iota.
  generalize (Qred q); cbv zeta.
  clear q.
  intros q.
  destruct q as [num den].
  cbn.
  destruct num.
  - unfold Q2R. cbn; lra.
  - bdestruct (1 =? p)%positive; 
    bdestruct (1 =? den)%positive; 
    subst; unfold Q2R; cbn; lra.
  - bdestruct (1 =? p)%positive; 
    bdestruct (1 =? den)%positive; 
    subst; unfold Q2R; cbn; try lra.
    change (Z.neg p) with (- Z.pos p)%Z.
    rewrite opp_IZR.
    lra.
Qed.

Definition Q2C' (q : Q) : option C :=
  let q' := Qred q in 
  match Qnum q' with 
  | Z0 => None
  | Zpos p => 
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with 
    | true, true => (* q = 1 / 1 *) (C1)
    | false, true => (* q = +p / 1 *) (IZR (Z.pos p))
    | true, false => (* q = 1 / _ *) Cinv (IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q'%R)
    end
  | Zneg p => 
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with 
    | true, true => (* q = -1 / 1 *) (Copp C1)
    | false, true => (* q = -p / 1 *) Copp (IZR (Z.pos p))%R
    | true, false => (* q = -1 / _ *) Copp (Cinv (IZR (Z.pos (Qden q')))%R)
    | false, false => (* general case *) (Q2R q')
    end
  end.

Hint Resolve Pos.eqb_spec Z.eqb_spec : bdestruct.

Lemma Q2C'_correct q : 
  maybe (Q2C' q) C0 = Q2R q.
Proof.
  rewrite <- (Qred_correct q) at 2.
  cbv delta [Q2C'] beta iota.
  generalize (Qred q); cbv zeta.
  clear q.
  intros q.
  destruct q as [num den].
  cbn.
  destruct num.
  - unfold Q2R. cbn; lca.
  - bdestruct (1 =? p)%positive; 
    bdestruct (1 =? den)%positive; 
    subst; unfold Q2R; cbn; [|rewrite <- RtoC_inv|..]; lca.
  - bdestruct (1 =? p)%positive; 
    bdestruct (1 =? den)%positive; 
    subst; unfold Q2R; cbn; [|rewrite <- RtoC_inv, <- RtoC_opp|..]; try lca.
    change (Z.neg p) with (- Z.pos p)%Z.
    rewrite opp_IZR.
    lca.
Qed.

Definition omap {A B} (f : A -> B) (ma : option A) : option B :=
  match ma with 
  | Some a => Some (f a)
  | None => None
  end.

Definition omap2 {A} (f : A -> A -> A) (ma ma' : option A) : option A :=
  match ma, ma' with 
  | Some a, Some a' => Some (f a a')
  | Some a, None => Some a
  | None, Some a' => Some a'
  | None, None => None
  end.


Fixpoint ofold {A} (f : A -> A -> A) (mas : list (option A)) : option A :=
  match mas with 
  | [] => None
  | ma :: mas => omap2 f ma (ofold f mas)
  end.

Definition QC2C' (q : QC) :=
  let '(mkQC a b c d) := q in 
  let ma := (* omap RtoC *) (Q2C' a) in 
  let mb := (* omap RtoC *) (Q2C' b) in 
  let mc := (* omap RtoC *) (Q2C' c) in 
  let md := (* omap RtoC *) (Q2C' d) in 
  maybe (ofold Cplus [
    ma;
    omap (fun x => x / √2)%C mb;
    omap (fun x => x * Ci)%C mc;
    omap (fun x => x * Ci / √ 2)%C md
  ]) C0.

Lemma maybe_omap2 {A} (f : A -> A -> A) d : 
  (forall a, f d a = a) -> (forall a, f a d = a) -> 
  forall ma ma',
  maybe (omap2 f ma ma') d = f (maybe ma d) (maybe ma' d).
Proof.
  intros Hl Hr [a|] [a'|]; cbn; auto.
Qed.

Lemma maybe_omap {A B} d' (f : A -> B) d : 
  (f d' = d) -> forall ma,
  maybe (omap f ma) d = f (maybe ma d').
Proof.
  intros Hd [a|]; cbn; auto.
Qed.

Lemma omap_omap {A B D} (f : A -> B) (g : B -> D) ma : 
  omap g (omap f ma) = omap (fun x => g (f x)) ma.
Proof. now destruct ma. Qed.

Lemma QC2C'_correct q : 
  QC2C' q = QC2C q.
Proof.
  destruct q as [a b c d].
  cbn.
  rewrite !(maybe_omap2 Cplus 0%R Cplus_0_l Cplus_0_r).
  (* rewrite !omap_omap. *)
  rewrite !(maybe_omap C0) by lca.
  rewrite !Q2C'_correct.
  cbn.
  pose proof sqrt2_neq_0.
  apply c_proj_eq; cbn; R_field.
Qed.




Definition QCred (q : QC) : QC :=
  let '(mkQC a b c d) := q in 
  mkQC (Qred a) (Qred b) (Qred c) (Qred d).

Lemma QCred_correct q : QC2C (QCred q) = QC2C q.
Proof.
  destruct q.
  cbn.
  now rewrite 4 Qred_correct.
Qed.

Class ParseQC (q : QC) (c : C) := {
  parseqc : QC2C q = c
}.
Hint Mode ParseQC ! - : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance parseQC_mult q r c d : 
  ParseQC q c -> ParseQC r d -> 
  ParseQC (q * r) (c * d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_mult, Hq, Hr.
Qed.

#[export]
Instance parseQC_div q r c d : 
  ParseQC q c -> ParseQC r d -> 
  ParseQC (q / r) (c / d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_div, Hq, Hr.
Qed.

#[export]
Instance parseQC_plus q r c d : 
  ParseQC q c -> ParseQC r d -> 
  ParseQC (q + r) (c + d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_plus, Hq, Hr.
Qed.

#[export]
Instance parseQC_minus q r c d : 
  ParseQC q c -> ParseQC r d -> 
  ParseQC (q - r) (c - d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_minus, Hq, Hr.
Qed.

#[export]
Instance parseQC_opp q c : 
  ParseQC q c -> ParseQC (-q) (-c).
Proof.
  intros [Hq].
  constructor.
  now rewrite QC2C_opp, Hq.
Qed.

#[export]
Instance parseQC_inv q c : 
  ParseQC q c -> ParseQC (/ q) (/ c).
Proof.
  intros [Hq].
  constructor.
  now rewrite QC2C_inv, Hq.
Qed.


#[export]
Instance parseQC_0 : 
  ParseQC (0) (C0).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_1 : 
  ParseQC (1) (C1).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_2 : 
  ParseQC (2) (C2).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_inv_sqrt2 : 
  ParseQC (mkQC 0 1 0 0) (/√ 2).
Proof.
  constructor.
  rewrite <- RtoC_inv.
  lca.
Qed.

#[export]
Instance parseQC_Rinv_sqrt2 : 
  ParseQC (mkQC 0 1 0 0) (Rinv (√ 2)).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_1_div_sqrt2 : 
  ParseQC (mkQC 0 1 0 0) (C1 / √ 2).
Proof.
  constructor.
  rewrite <- RtoC_div.
  lca.
Qed.

#[export]
Instance parseQC_sqrt2 : 
  ParseQC (mkQC 0 2 0 0) (√ 2).
Proof.
  constructor.
  cbn.
  apply c_proj_eq; [|cbn; lra].
  cbn.
  rewrite Q2R_0.
  replace (Q2R 2) with (2%R) by lra.
  R_field_simplify; nonzero.
Qed.


#[export]
Instance parseQC_Ropp q (r : R) : 
  ParseQC q r -> 
  ParseQC (QCopp q) (Ropp r).
Proof.
  intros [Hq].
  constructor.
  rewrite QC2C_opp, Hq.
  lca.
Qed.

Unset Typeclasses Unique Instances.


Lemma solve_C_eq qc qc' c c' : 
  ParseQC qc c -> ParseQC qc' c' -> 
  QCeqb qc qc' = true -> 
  c = c'.
Proof.
  intros [<-] [<-].
  now intros ->%QCeqb_eq.
Qed.



End Rops.
End QC2C.

Coercion QC2C : QC >-> C.

Require Import HeisenbergFoundations.Automation.

(* Import TTypeOrdering TOrd. *)

(* (* Redefinition because the definition in Predicates is opaque, 
  so won't reduce *)
Definition Peq_dec (p q : Pauli) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

Definition lPeq_dec (ps qs : list Pauli) : {ps = qs} + {ps <> qs}.
Proof. apply list_eq_dec, Peq_dec. Defined.

Definition Peqb (p q : Pauli) : bool := beq_Pauli p q.

Lemma Peqb_spec (p q : Pauli) : reflect (p = q) (Peqb p q).
Proof. 
  apply iff_reflect. 
  destruct p, q; easy.
Qed.

Definition lPeqb (ps qs : list Pauli) : bool :=
  eqb_listP ps qs
  list_equal§§§ {ps = qs} + {ps <> qs}.
Proof. apply list_eq_dec, Peq_dec. Defined. *)

Notation eqb_listP := TOrd.eqb_listP.

Lemma eqb_listP_reflect (ps qs : list Pauli) : 
  reflect (ps = qs) (eqb_listP ps qs).
Proof. 
  apply iff_reflect.
  apply TOrd.eqb_listP_eq_true.
Qed.

#[export] Hint Resolve eqb_listP_reflect : bdestruct.

Definition oQC_mult (q r : option QC) : option QC :=
  match q, r with 
  | Some q, Some r => Some (q * r)%QC
  | Some q, None => Some q
  | None, Some r => Some r
  | None, None => None
  end.

Lemma oQC_mult_correct q r : 
  QC2C (maybe (oQC_mult q r) 1%Q) = maybe q 1%Q * maybe r 1%Q.
Proof.
  destruct q, r; cbn; [apply QC2C_mult|lca..].
Qed.

Definition QTType (n : nat) : Type := option QC * list Pauli.

Definition QAType (n : nat) : Type := list (QTType n).

Definition QTType_to_TType {n} (t : QTType n) : TType n :=
  (QC2C (maybe (fst t) 1%Q), snd t).

Definition QAType_to_AType {n} (t : QAType n) : AType n :=
  map QTType_to_TType t.

Definition translateQ {n} (t : QTType n) : Square (2^n) :=
  translate (QTType_to_TType t).

(* Use a fixpoint rather than fold_left to make reduction nicer *)
Fixpoint translateQA {n} (t : QAType n) : Square (2^n) :=
  match t with 
  | [] => Zero
  | q :: t => Mplus (translateQ q) (translateQA t)
  end.


Definition QTType_to_TType' {n} (t : QTType n) : TType n :=
  (QC2C' (maybe (fst t) 1%Q), snd t).

Definition QAType_to_AType' {n} (t : QAType n) : AType n :=
  map QTType_to_TType' t.


Arguments QTType_to_TType {_} !_ /.
Arguments QTType_to_TType' {_} !_ /.
Arguments QAType_to_AType' {_} !_ /.
Arguments translateQ {_} !_ /.
Arguments Matrix.scale {_ _} !_ _ _ /.

Lemma QTType_to_TType'_correct {n} (t : QTType n) : 
  translate (QTType_to_TType' t) = translate (QTType_to_TType t).
Proof.
  destruct t.
  cbn.
  unfold translate.
  cbn.
  now rewrite QC2C'_correct.
Qed.

Lemma translateA_alt {n} (ts : AType n) : 
  translateA ts = fold_right Mplus Zero (map translate ts).
Proof.
  apply fold_symmetric; intros; lma.
Qed.

Lemma QAType_to_AType'_correct {n} (t : QAType n) : 
  translateA (QAType_to_AType' t) = translateA (QAType_to_AType t).
Proof.
  rewrite 2 translateA_alt.
  induction t; [easy|].
  cbn.
  rewrite QTType_to_TType'_correct.
  f_equal.
  apply IHt.
Qed.

  


Lemma translateQA_correct {n} (t : QAType n) :
  translateQA t = translateA (QAType_to_AType t).
Proof.
  unfold translateA.
  rewrite fold_symmetric by (intros; lma).
  induction t; [reflexivity|].
  cbn.
  rewrite IHt.
  reflexivity.
Qed.


Fixpoint QT_QA_plus {n} (q : QTType n) (qs : QAType n) : QAType n :=
  match qs with 
  | [] => [q]
  | q' :: qs => 
    if eqb_listP (snd q) (snd q') then 
      (Some (QCplus (maybe (fst q) 1%Q) (maybe (fst q') 1%Q)), (snd q')) :: qs
    else q' :: QT_QA_plus q qs
  end.

Lemma QT_QA_plus_correct {n} (q : QTType n) (qs : QAType n) : 
  translateQA (QT_QA_plus q qs) = translateQA (q :: qs).
Proof.
  induction qs; [reflexivity|].
  cbn.
  bdestruct (eqb_listP (snd q) (snd a)); [|cbn; rewrite IHqs; cbn; lma].
  cbn.
  destruct q as [q t], a as [q' t'].
  cbn. 
  rewrite QC2C_plus.
  rewrite <- Mplus_assoc, Mscale_plus_distr_l.
  cbn in *; subst t'.
  reflexivity.
Qed.


Fixpoint QT_QA_minus {n} (q : QTType n) (qs : QAType n) : QAType n :=
  match qs with 
  | [] => [(Some (QCopp (maybe (fst q) 1%Q)), snd q)]
  | q' :: qs => 
    if eqb_listP (snd q) (snd q') then 
      (Some (QCminus (maybe (fst q') 1%Q) (maybe (fst q) 1%Q)), (snd q')) :: qs
    else q' :: QT_QA_minus q qs
  end.

Lemma QT_QA_minus_correct {n} (q : QTType n) (qs : QAType n) : 
  translateQA (QT_QA_minus q qs) = translateQA qs .+ (- C1 .* translateQ q).
Proof.
  induction qs.
  - cbn.
    destruct q.
    cbn.
    rewrite QC2C_opp.
    lma.
  - cbn.
    bdestruct (eqb_listP (snd q) (snd a)); [|cbn; rewrite IHqs; cbn; lma].
    
    destruct q as [q t], a as [q' t'].
    cbn. 
    rewrite QC2C_minus.
    rewrite Cminus_unfold, Mscale_plus_distr_l.
    cbn in *; subst t'.
    lma.
Qed.

Definition P_mult (p q : Pauli) : option QC * Pauli :=
  match p, q with 
  | gI, q => (None, q)
  | p, gI => (None, p)
  | gX, gX | gY, gY | gZ, gZ => (None, gI)
  | gX, gY => (Some (mkQC 0 0 1 0), gZ)
  | gX, gZ => (Some (mkQC 0 0 (-1) 0), gY)
  | gY, gZ => (Some (mkQC 0 0 1 0), gX)
  | gY, gX => (Some (mkQC 0 0 (-1) 0), gZ)
  | gZ, gX => (Some (mkQC 0 0 1 0), gY)
  | gZ, gY => (Some (mkQC 0 0 (-1) 0), gX)
  end.

Lemma P_mult_correct p q : 
  QC2C (maybe (fst (P_mult p q)) 1%Q) .* translate_P (snd (P_mult p q)) = 
  translate_P p × translate_P q.
Proof.
  destruct p, q; cbn; lma'.
Qed.


Definition lP_mult (ps qs : list Pauli) : option QC * list Pauli :=
  fold_right (fun '(p, q) mq'rs => 
    (oQC_mult (fst (P_mult p q)) (fst mq'rs), 
    snd (P_mult p q) :: snd mq'rs)) (None, []) (combine ps qs).

Lemma length_lP_mult ps qs : 
  length (snd (lP_mult ps qs)) = min (length ps) (length qs).
Proof.
  unfold lP_mult.
  rewrite <- combine_length.
  generalize (combine ps qs).
  intros l.
  induction l as [|[]]; [easy|cbn; rewrite IHl; easy]. 
Qed.

Lemma lP_mult_correct ps qs : length ps = length qs -> 
  QC2C (maybe (fst (lP_mult ps qs)) 1%Q) .* (⨂ map translate_P (snd (lP_mult ps qs))) =
  @Mmult _ (2^length ps) _ (⨂ map translate_P ps) (⨂ map translate_P qs).
Proof.
  revert qs; 
  induction ps; intros qs Hlen; destruct qs; try easy.
  - cbn.
    lma'.
  - cbn.
    rewrite oQC_mult_correct.
    cbn in Hlen.
    apply Nat.succ_inj in Hlen.
    rewrite <- Mscale_assoc.
    etransitivity; [progress restore_dims; reflexivity|].
    rewrite <- Mscale_kron_dist_r, <- Mscale_kron_dist_l.
    unfold lP_mult in IHps.
    rewrite IHps by easy.
    rewrite P_mult_correct.
    rewrite <- kron_mixed_product.
    do 2 f_equal; simpl_list; try unify_pows_two;
    fold (lP_mult ps qs); rewrite length_lP_mult, Hlen; lia.
Qed.

Definition QT_mult {n} (ps qs : QTType n) : QTType n :=
  (oQC_mult (oQC_mult (fst ps) (fst qs)) 
    (fst (lP_mult (snd ps) (snd qs))),
    snd (lP_mult (snd ps) (snd qs))).

Definition proper_length_QTType {n} (q : QTType n) : Prop := 
  length (snd q) = n.
Definition proper_length_QAType {n} (q : QAType n) : Prop := 
  Forall proper_length_QTType q.

Lemma QT_mult_correct {n} (ps qs : QTType n) : 
  proper_length_QTType ps -> proper_length_QTType qs -> 
  translateQ (QT_mult ps qs) = translateQ ps × translateQ qs.
Proof.
  unfold proper_length_QTType.
  intros Hlenps Hlenqs.
  unfold QT_mult.
  cbn.
  rewrite 2!oQC_mult_correct, <- Mscale_assoc.
  rewrite lP_mult_correct by congruence.
  rewrite <- Mscale_assoc, <- Mscale_mult_dist_r, 
    <- Mscale_mult_dist_l.
  destruct ps as [p ps], qs as [q qs].
  cbn in *.
  fold (lP_mult ps qs).
  rewrite map_length, length_lP_mult.
  f_equal; unify_pows_two; lia.
Qed.

Fixpoint QA_plus {n} (ps qs : QAType n) : QAType n :=
  match ps with 
  | [] => qs
  | p :: ps => QA_plus ps (QT_QA_plus p qs)
  end.

Lemma QA_plus_correct {n} (ps qs : QAType n) : 
  translateQA (QA_plus ps qs) = 
  translateQA ps .+ translateQA qs.
Proof.
  revert qs;
  induction ps; intros qs.
  - cbn.
    lma.
  - cbn.
    rewrite IHps, QT_QA_plus_correct.
    cbn.
    lma.
Qed.

Fixpoint QA_minus {n} (ps qs : QAType n) : QAType n :=
  match qs with 
  | [] => ps
  | q :: qs => QA_minus (QT_QA_minus q ps) qs
  end.

Lemma QA_minus_correct {n} (ps qs : QAType n) : 
  translateQA (QA_minus ps qs) = 
  translateQA ps .+ (-C1) .* translateQA qs.
Proof.
  revert ps;
  induction qs; intros ps.
  - cbn.
    lma.
  - cbn.
    rewrite IHqs, QT_QA_minus_correct.
    cbn.
    lma.
Qed.

Fixpoint QT_QA_mult {n} (p : QTType n) (qs : QAType n) :=
  match qs with 
  | [] => []
  | q :: qs => QT_mult p q :: QT_QA_mult p qs
  end.

Arguments QT_mult {_} !_ !_ /.

Lemma QT_QA_mult_correct {n} (p : QTType n) (qs : QAType n) : 
  proper_length_QTType p -> proper_length_QAType qs ->
  translateQA (QT_QA_mult p qs) = 
  translateQ p × translateQA qs.
Proof.
  intros Hp Hqs.
  induction Hqs.
  - cbn.
    now rewrite Mmult_0_r.
  - cbn.
    rewrite IHHqs.
    rewrite Mmult_plus_distr_l.
    now rewrite QT_mult_correct by easy.
Qed.

Fixpoint QA_mult {n} (ps qs : QAType n) : QAType n :=
  match ps with 
  | [] => []
  | p :: ps =>
    QA_plus (QT_QA_mult p qs) (QA_mult ps qs)
  end.

Lemma QA_mult_correct {n} (ps qs : QAType n) : 
  proper_length_QAType ps -> proper_length_QAType qs ->
  translateQA (QA_mult ps qs) = 
  translateQA ps × translateQA qs.
Proof.
  intros Hps Hqs.
  induction Hps.
  - cbn.
    now rewrite Mmult_0_l.
  - cbn.
    rewrite QA_plus_correct, QT_QA_mult_correct, IHHps by easy.
    now rewrite Mmult_plus_distr_r.
Qed.

Definition QT_reduce {n} (p : QTType n) : QTType n :=
  let '(mq, p) := p in 
  match mq with 
  | None => (None, p)
  | Some q => (Some (QCred q), p)
  end.

Lemma QT_reduce_correct {n} (p : QTType n) : 
  translateQ (QT_reduce p) = translateQ p.
Proof.
  destruct p as [[mq|] p]; [|reflexivity].
  cbn.
  now rewrite QCred_correct.
Qed.

Fixpoint QA_reduce {n} (ps : QAType n) : QAType n :=
  match ps with 
  | [] => []
  | p :: ps => 
    if QCeqb (maybe (fst p) 1%Q) 0%Q then QA_reduce ps
    else QT_reduce p :: QA_reduce ps
  end.


Lemma QA_reduce_correct {n} (ps : QAType n) : 
  translateQA (QA_reduce ps) = translateQA ps.
Proof.
  induction ps; [easy|].
  cbn.
  bdestruct (QCeqb (maybe (fst a) 1%Q) 0%Q).
  - destruct a; cbn in *. 
    rewrite H.
    rewrite Q2QC_correct, Q2R_0, Mscale_0_l, IHps.
    lma.
  - cbn.
    now rewrite IHps, QT_reduce_correct.
Qed.

Lemma QA_reflexive_solve_lemma {n} (qs ps : QAType n) : 
  QA_reduce (QA_minus qs ps) = [] -> 
  translateQA qs = translateQA ps.
Proof.
  intros Heq%(f_equal translateQA).
  rewrite QA_reduce_correct, QA_minus_correct in Heq.
  cbn in Heq.
  rewrite <- (Mplus_0_l _ _ (translateQA ps)).
  rewrite <- Heq.
  lma.
Qed.


Definition QT_scale {n} (q : QC) (ts : QTType n) : QTType n :=
  (Some (QCmult q (maybe (fst ts) 1%Q)), snd ts).

Lemma QT_scale_correct {n} (q : QC) (ts : QTType n) : 
  translateQ (QT_scale q ts) = q .* translateQ ts.
Proof.
  unfold translateQ, QTType_to_TType.
  unfold translate.
  cbn.
  restore_dims.
  now rewrite Mscale_assoc, QC2C_mult.
Qed.

Lemma QT_scale_correct' {n} (q : QC) (t : QTType n) : 
  QTType_to_TType (QT_scale q t) = gScaleT (QC2C q) (QTType_to_TType t).
Proof.
  destruct t as [q' ps].
  cbn.
  now rewrite QC2C_mult.
Qed.

Definition QA_scale {n} (q : QC) (ts : QAType n) : QAType n :=
  map (QT_scale q) ts.

Lemma QA_scale_correct' {n} (q : QC) (t : QAType n) : 
  QAType_to_AType (QA_scale q t) = gScaleA (QC2C q) (QAType_to_AType t).
Proof.
  unfold QAType_to_AType, QA_scale, gScaleA.
  rewrite 2 map_map.
  apply map_ext.
  intros; apply QT_scale_correct'.
Qed.

Class ParseAType {n} (ps : QAType n) (ts : AType n) := {
  parseatype : QAType_to_AType ps = ts
}.
Hint Mode ParseAType - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance parseAT_nil {n} : @ParseAType n [] []. 
Proof.
  constructor. reflexivity.
Qed.

#[export]
Instance parseAT_cons {n} q c ps qs ts : 
  ParseQC q c -> @ParseAType n qs ts -> 
  @ParseAType n ((Some q, ps) :: qs) ((c, ps) :: ts).
Proof.
  intros [Hq] [Hqs].
  constructor. 
  unfold translateA.
  cbn.
  rewrite <- Hqs.
  rewrite Hq.
  reflexivity.
Qed.


#[export]
Instance parseAT_scale {n} q c qs ts : 
  ParseQC q c -> @ParseAType n qs ts -> 
  @ParseAType n (QA_scale q qs) (gScaleA c ts).
Proof.
  intros [Hq] [Hqs].
  constructor.
  rewrite QA_scale_correct'.
  congruence.
Qed.

Unset Typeclasses Unique Instances.


Lemma AType_reflexive_solve_lemma {n} qs qs' (ts ts' : AType n) : 
  ParseAType qs ts -> ParseAType qs' ts' -> 
  QA_reduce (QA_minus (QA_plus qs []) qs') = [] -> 
  translateA ts = translateA ts'.
Proof.
  intros [Hqs] [Hqs'] Hred%QA_reflexive_solve_lemma.
  rewrite QA_plus_correct in Hred.
  cbn in Hred.
  rewrite Mplus_0_r in Hred.
  rewrite <- Hqs, <- Hqs'.
  now rewrite 2 translateQA_correct in Hred.
Qed.

Lemma AType_base_reduce_lemma {n} qs (ts : AType n) : 
  ParseAType qs ts -> 
  translateA ts = translateQA (QA_reduce (QA_plus qs [])).
Proof.
  intros [Hqs].
  rewrite QA_reduce_correct, QA_plus_correct.
  cbn.
  rewrite Mplus_0_r.
  now rewrite translateQA_correct, Hqs.
Qed.

Lemma AType_reduce_lemma {n} qs (ts : AType n) : 
  ParseAType qs ts -> 
  translateA ts = translateA 
  (QAType_to_AType' (QA_reduce (QA_plus qs []))).
Proof.
  intros Hqs.
  rewrite QAType_to_AType'_correct.
  rewrite <- translateQA_correct.
  now apply AType_base_reduce_lemma.
Qed.


(* 
Goal True. 
set (ts := 
  [(C1 / √ 2 * (C1 / √ 2), [gX]); (C1 / √ 2 * (C1 / √ 2), [gY]); (C1 / √ 2 * (C1 / √ 2), [gY]); (- C1 * (C1 / √ 2) * (C1 / √ 2), [gX])] : AType 1).
cbn in ts.
assert (translateA ts = Zero).
erewrite AType_reduce_lemma by apply _.
cbn -[translateA].

match goal with 
|- context G [mkQC ?a ?b ?c ?d] => 
  let a' := eval cbv in a in 
  let b' := eval cbv in b in 
  let c' := eval cbv in c in 
  let d' := eval cbv in d in 
  let newgoal := context G [mkQC a' b' c' d'] in 
  change newgoal
end.

eassert (Hts : ParseAType _ ts) by apply _.




Lemma QT_mult {n} (q r : QTType n) : QTType n :=
  combine

Search "sort" -"permutation". *)

Definition pred_eq {n} : relation (Predicate n) :=
  fun P P' => forall v, vecSatisfiesP v P <-> vecSatisfiesP v P'.

Lemma pred_eq_refl {n} : Reflexive (@pred_eq n).
Proof.
  easy.
Qed.

Lemma pred_eq_symm {n} : Symmetric (@pred_eq n).
Proof.
  intros P Q HPQ v; symmetry; apply HPQ.
Qed.

Lemma pred_eq_trans {n} : Transitive (@pred_eq n).
Proof.
  intros P P' P''.
  unfold pred_eq.
  intros Hl Hr v.
  rewrite Hl; apply Hr.
Qed.

Add Parametric Relation {n} : (Predicate n) pred_eq 
  reflexivity proved by pred_eq_refl
  symmetry proved by pred_eq_symm
  transitivity proved by pred_eq_trans
  as pred_eq_setoid.

Add Parametric Morphism {n} v : (vecSatisfiesP v) with signature
  @pred_eq n ==> iff as vecSatisfiesP_mor.
Proof.
  intros P Q HPQ; apply HPQ. 
Qed.

Add Parametric Morphism {n} : (@triple n) with signature
  @pred_eq n ==> Logic.eq ==> pred_eq ==> iff as triple_mor.
Proof.
  intros P P' HP t Q Q' HQ.
  unfold triple.
  setoid_rewrite HP.
  setoid_rewrite HQ.
  reflexivity.
Qed.

Definition atype_eq {n} : relation (AType n) :=
  fun ts ts' => translateA ts = translateA ts'.

Add Parametric Relation {n} : (AType n) (@atype_eq n)
  reflexivity proved by ltac:(unfold atype_eq; hnf; intros **; reflexivity)
  symmetry proved by ltac:(unfold atype_eq; hnf; intros **; now symmetry)
  transitivity proved by ltac:(unfold atype_eq; hnf; intros **; now etransitivity; eauto)
  as atype_eq_setoid.


Add Parametric Morphism {n} : (@AtoPred n) with signature 
  atype_eq ==> pred_eq as AtoPred_mor.
Proof.
  intros ts ts' Hts v.
  cbn.
  now rewrite Hts.
Qed.

Lemma AType_reduce_lemma' {n} qs (ts : AType n) : 
  ParseAType qs ts -> 
  atype_eq ts
  (QAType_to_AType' (QA_reduce (QA_plus qs []))).
Proof.
  apply AType_reduce_lemma.
Qed.

Lemma AType_reduce_both_lemma {n} qs qs' (ts ts' : AType n)
  (p : prog) : 
  ParseAType qs ts -> ParseAType qs' ts' -> 
  {{ts}} p {{ts'}} <-> 
  {{(QAType_to_AType' (QA_reduce (QA_plus qs [])))}} p 
  {{(QAType_to_AType' (QA_reduce (QA_plus qs' [])))}}.
Proof.
  now intros ->%AType_reduce_lemma' ->%AType_reduce_lemma'.
Qed.

Lemma prep_validate_lemma {n} (ps ts ts' : AType n) t : 
  atype_eq ts ts' -> 
  {{ps}} t {{ts}} <-> {{ps}} t {{ts'}}.
Proof.
  now intros ->.
Qed.


(* Predicate *)
(* Search triple Proper. *)

Lemma solve_not_gI' (p : Pauli) : 
  (match p with |gI => False | _ => True end) -> not_gI p.
Proof.
  unfold not_gI.
  now destruct p; auto.
Qed.

Lemma solve_anticommute_Pauli (p q : Pauli) : 
  (match p, q with 
  | gI, _ => False
  | _, gI => False
  | gX, gX => False
  | gY, gY => False
  | gZ, gZ => False
  | _, _ => True
  end) -> anticommute_Pauli p q.
Proof.
  destruct p, q; try easy; intros; WF_auto.
Qed.

Definition QT_eqb {n} (qs qs' : QTType n) : bool :=
  QCeqb (maybe (fst qs) 1%Q) (maybe (fst qs') 1%Q) &&
  eqb_listP (snd qs) (snd qs').

Lemma QT_eqb_eq {n} (qs qs' : QTType n) : 
  QT_eqb qs qs' = true -> translateQ qs = translateQ qs'.
Proof.
  unfold QT_eqb.
  rewrite andb_true_iff.
  intros [Hfst%QCeqb_eq Hsnd%TTypeOrdering.eqb_listP_eq_true].
  unfold translateQ, QTType_to_TType.
  unfold translate.
  cbn.
  now rewrite Hfst, Hsnd.
Qed.

Lemma cBigMul_alt (l : list C) : 
  cBigMul l = fold_right Cmult C1 l.
Proof.
  apply fold_symmetric; intros; lca.
Qed.

Lemma fst_QT_mult_Nones n (ts ts' : list Pauli) : 
  length ts = n -> length ts' = n -> 
  QC2C (maybe (fst (@QT_mult n (None, ts) (None, ts'))) 1%Q) =
  cBigMul (zipWith gMul_Coef ts ts').
Proof.
  unfold QT_mult.
  cbn [fst snd].
  rewrite 2 oQC_mult_correct.
  cbn [maybe].
  rewrite Q2QC_correct.
  replace (Q2R 1) with 1%R by lra.
  rewrite 2 Cmult_1_l, cBigMul_alt.
  unfold lP_mult.
  revert ts ts';
  induction n; intros ts ts'.
  - destruct ts, ts'; [|easy..].
    cbn.
    intros; lca.
  - destruct ts as [|p ts]; [easy|]; 
    destruct ts' as [|p' ts']; [easy|].
    cbn.
    intros [= Hts] [= Hts'].
    specialize (IHn _ _ Hts Hts').
    rewrite oQC_mult_correct.
    f_equal; [|apply IHn].
    destruct p, p'; lca.
Qed.

Definition is_anticommute_TType_base {n} (ts ts' : TType n) : bool :=
  QCeqb (maybe (fst (lP_mult (snd ts) (snd ts'))) 1%Q)
    (- maybe (fst (@lP_mult (snd ts') (snd ts))) 1%Q).

Lemma solve_anticommute_TType {n} (ts ts' : TType n) :
  Nat.eqb (length (snd ts)) n &&
  Nat.eqb (length (snd ts')) n &&
  is_anticommute_TType_base ts ts' = true ->
  anticommute_TType ts ts'.
Proof.
  unfold is_anticommute_TType_base.
  rewrite 2 andb_true_iff, 2 Nat.eqb_eq.
  intros [[Hlen Hlen'] Heq%QCeqb_eq%QC2C_mor].
  rewrite QC2C_opp in Heq by easy.
  unfold anticommute_TType.
  destruct ts as [c ts], ts' as [c' ts'].
  cbn [fst snd] in *.
  rewrite <- 2 (fst_QT_mult_Nones n) by easy.
  unfold QT_mult.
  cbn [fst snd].
  rewrite 4 oQC_mult_correct, Heq.
  lca.
Qed.

Lemma anticommute_TType_AType_iff_Forall {n} (t : TType n) (ts : AType n) : 
  anticommute_TType_AType t ts <-> Forall (anticommute_TType t) ts.
Proof.
  induction ts.
  - cbn; intuition.
  - cbn.
    rewrite Forall_cons_iff, IHts.
    reflexivity.
Qed. 

Lemma solve_anticommute_TType_AType {n} (t : TType n) (ts : AType n) : 
  Nat.eqb (length (snd t)) n &&
  forallb (fun t' => Nat.eqb (length (snd t')) n && 
  is_anticommute_TType_base t t') ts = true -> 
  anticommute_TType_AType t ts.
Proof.
  rewrite andb_true_iff, forallb_forall.
  intros [Ht Hts].
  rewrite anticommute_TType_AType_iff_Forall, Forall_forall.
  intros t' Ht'%Hts.
  apply solve_anticommute_TType.
  rewrite Ht, andb_true_l.
  apply Ht'.
Qed.

Lemma is_simpl_prog_T : simpl_prog T.
Proof. right; right; easy. Qed.
Lemma is_simpl_prog_S : simpl_prog S.
Proof. right; left; easy. Qed.
Lemma is_simpl_prog_H : simpl_prog H.
Proof. left; easy. Qed.

Lemma anticommute_AType_syntactic_iff_Forall {n} (ts ts' : AType n) : 
  anticommute_AType_syntactic ts ts' <->
  Forall (fun t => anticommute_TType_AType t ts') ts.
Proof.
  induction ts.
  - cbn; intuition.
  - rewrite Forall_cons_iff.
    cbn.
    now rewrite IHts.
Qed.




Definition is_anticommute_AType_syntactic {n} (ts ts' : AType n) : bool :=
  forallb (fun t' => Nat.eqb (length (snd t')) n) ts' && 
  forallb (fun t => Nat.eqb (length (snd t)) n &&
  forallb (fun t' => is_anticommute_TType_base t t') ts') ts.

Lemma solve_anticommute_AType_syntactic {n} (ts ts' : AType n) : 
  is_anticommute_AType_syntactic ts ts' = true ->
    anticommute_AType_syntactic ts ts'.
Proof.
  unfold is_anticommute_AType_syntactic.
  rewrite andb_true_iff, 2 forallb_forall, anticommute_AType_syntactic_iff_Forall, Forall_forall.
  intros Hall t Ht%Hall%andb_true_iff.
  apply solve_anticommute_TType_AType.
  rewrite andb_true_iff.
  split; [apply Ht|].
  rewrite forallb_forall.
  destruct Ht as [Ht Hforall].
  rewrite forallb_forall in Hforall.
  intros t' Ht'. 
  rewrite andb_true_iff.
  split; [|now apply Hforall].
  now apply Hall.
Qed.

Definition is_trace_zero_syntax (ts : list Pauli) : bool :=
  fold_right (fun p acc => 
    match p with 
    | gI => acc
    | _ => true
    end) false ts.

Lemma solve_trace_zero_syntax (ts : list Pauli) : 
  is_trace_zero_syntax ts = true -> 
    trace_zero_syntax ts.
Proof.
  unfold is_trace_zero_syntax.
  induction ts; [easy|].
  cbn.
  change (a :: ts) with ([a] ++ ts).
  destruct a; [|intros; now apply trace_zero_syntax_L; constructor..].
  intros ?%IHts.
  now apply trace_zero_syntax_R.
Qed.

Lemma restricted_addition_syntactic_ne {n} (ts : AType n) : 
  restricted_addition_syntactic ts -> 
  ts <> [].
Proof.
  intros Hras.
  induction Hras; [easy|].
  destruct a1; easy. 
Qed.

Local Notation ras t := (restricted_addition_syntactic t).

(* NB: this can actually be made constructive! *)
Lemma restricted_addition_syntactic_inv {n} (ts : AType n) : 
  restricted_addition_syntactic ts ->
  (exists t, WF_TType t /\ ts = [t]) \/
  (exists l r, ras l /\ ras r /\ anticommute_AType_syntactic l r /\ 
    ts = gScaleA (C1 / √ 2) (l ++ r)).
Proof.
  intros Hts; inversion Hts; [left | right; eexists; eexists]; eauto.
Qed.

Lemma gScaleA_eq_iff_inv {n} (ts ts' : AType n) c : c <> C0 -> 
  ts = gScaleA c ts' <-> ts' = gScaleA (/ c) ts.
Proof.
  intros Hc.
  split; intros ->; unfold gScaleA; rewrite map_map; 
    rewrite <- map_id at 1; apply map_ext; intros [d t]; cbn;
    f_equal; unfold Coef in *; C_field.
Qed.



Fixpoint ne_list_app_partitions_core {A} (h l : list A) : list (list A * list A) :=
  match l with 
  | [] => []
  | a :: l => (h, a :: l) :: ne_list_app_partitions_core (h ++ [a]) l
  end.

Lemma app_inj_eq_length_l {A} (a b x y : list A) : 
  length a = length x -> 
  a ++ b = x ++ y -> 
  a = x /\ b = y.
Proof.
  intros Hlen Happs.
  apply (f_equal (firstn (length a))) in Happs as Htakes.
  rewrite 2 firstn_app, <- Hlen, Nat.sub_diag in Htakes.
  cbn in Htakes.
  rewrite 2 app_nil_r, 2 firstn_all2 in Htakes by lia.
  apply (f_equal (skipn (length a))) in Happs as Hskips.
  rewrite 2 skipn_app, <- Hlen, Nat.sub_diag in Hskips.
  cbn in Hskips.
  rewrite 2 skipn_all2 in Hskips by lia.
  cbn in Hskips.
  easy.
Qed.




Lemma In_ne_list_app_partitions_core {A} (h l x y : list A) : h <> [] ->
  In (x, y) (ne_list_app_partitions_core h l) <-> 
  x <> [] /\ y <> [] /\ x ++ y = h ++ l /\ le (length h) (length x).
Proof.
  revert h x y; induction l as [|a l IHl]; intros h x y Hh.
  - cbn.
    split; [easy|].
    intros (Hx & Hy & Hxy & Hlen).
    assert (Hx' : (0 < length x)%nat) by (destruct x; cbn in *; easy + lia).
    assert (Hy' : (0 < length y)%nat) by (destruct y; cbn in *; easy + lia).
    rewrite app_nil_r in Hxy.
    apply (f_equal (@length _)) in Hxy.
    rewrite app_length in Hxy.
    lia.
  - cbn.
    rewrite IHl by now destruct h.
    split; [intros [(<- & <-)%pair_equal_spec | Hr]|].
    + easy. 
    + rewrite <- app_assoc in Hr; cbn in Hr. repeat split; [easy..|].
      rewrite app_length in Hr.
      cbn in Hr.
      lia.
    + intros (Hx & Hy & Hxy & Hlen).
      bdestruct (length h =? length x)%nat.
      * apply app_inj_eq_length_l in Hxy as [-> ->]; [|easy].
        now left.
      * right.
        repeat split; [easy..|rewrite <- app_assoc; apply Hxy|].
        rewrite app_length.
        cbn. lia.
Qed.

Definition ne_list_app_partitions {A} (l : list A) : list (list A * list A) :=
  match l with 
  | [] => []
  | a :: l => ne_list_app_partitions_core [a] l
  end.


Lemma In_ne_list_app_partitions {A} (l x y : list A) :
  In (x, y) (ne_list_app_partitions l) <-> 
  x <> [] /\ y <> [] /\ x ++ y = l.
Proof.
  destruct l.
  - cbn.
    split; [easy|].
    now destruct x.
  - cbn.
    rewrite In_ne_list_app_partitions_core by easy.
    cbn.
    firstorder.
    now destruct x; cbn; try lia.
Qed.

Definition is_WF_QTType {n} (t : QTType n) : bool :=
  ((¬ n =? 0) && (length (snd t) =? n))%nat &&
  maybe (omap (fun q => QCeqb q (1%Q) || QCeqb q ((-1)%Q)) (fst t)) true &&
  is_trace_zero_syntax (snd t).

Lemma is_WF_QTType_correct {n} (t : QTType n) : 
  is_WF_QTType t = true -> WF_TType (QTType_to_TType t).
Proof.
  unfold is_WF_QTType.
  rewrite 3 andb_true_iff, Nat.eqb_eq, negb_true_iff, Nat.eqb_neq.
  intros [[Hlen Hcoeff] Htrace%solve_trace_zero_syntax].
  destruct t as [q ps].
  constructor; cbn; [apply Hlen|..|easy].
  hnf.
  cbn.
  destruct q; [|left; lca].
  cbn -[Q2QC] in Hcoeff |- *.
  rewrite orb_true_iff, 2 QCeqb_iff in Hcoeff.
  destruct Hcoeff as [-> | ->]; [left | right]; lca.
Qed.



Definition is_anticommute_QAType_syntactic {n} (ts ts' : QAType n) : bool :=
  forallb (fun t' => Nat.eqb (length (snd t')) n) ts' && 
  forallb (fun t => Nat.eqb (length (snd t)) n &&
  forallb (fun t' => is_anticommute_TType_base 
    (QTType_to_TType t) (QTType_to_TType t')) ts') ts.

Lemma is_anticommute_QAType_syntactic_correct {n} (ts ts' : QAType n) : 
  is_anticommute_QAType_syntactic ts ts' = true -> 
  anticommute_AType_syntactic (QAType_to_AType ts) (QAType_to_AType ts').
Proof.
  intros His.
  apply solve_anticommute_AType_syntactic; revert His.
  unfold is_anticommute_AType_syntactic, is_anticommute_QAType_syntactic, 
    QAType_to_AType.
  rewrite 2! andb_true_iff, 4 forallb_forall, <- 4 Forall_forall,
    2 Forall_map.
  intros [Hlens Hall].
  split.
  - apply Hlens. 
  - revert Hall. 
    apply Forall_impl.
    intros t.
    rewrite 2 andb_true_iff, 2 forallb_forall, <- 2 Forall_forall, 
      Forall_map.
    intros H; apply H.
Qed.

Fixpoint is_WF_QAType (depth : nat) {n} (ts : QAType n) : bool :=
  match ts with 
  | [] => false
  | [t] => is_WF_QTType t
  | ts => 
    match depth with 
    | 0 => false
    | s depth => 
      existsb (fun x_y => 
        is_anticommute_QAType_syntactic (fst x_y) (snd x_y) &&
        is_WF_QAType depth (QA_scale (mkQC 0 2 0 0) (fst x_y)) && 
        is_WF_QAType depth (QA_scale (mkQC 0 2 0 0) (snd x_y)))
        (ne_list_app_partitions ts)
    end
  end.

Lemma is_WF_QAType_correct depth {n} (ts : QAType n) : 
  is_WF_QAType depth ts = true -> WF_AType (QAType_to_AType ts).
Proof.
  revert ts; induction depth; intros ts.
  - destruct ts; [easy|]; destruct ts; [|easy].
    cbn.
    intros Ht%is_WF_QTType_correct.
    now do 2 constructor.
  - destruct ts as [|t ts]; [easy|]; destruct ts as [|t' ts].
    1:{
      cbn.
      intros Ht%is_WF_QTType_correct.
      now do 2 constructor.
    }
    cbn [is_WF_QAType].
    generalize (t :: t' :: ts).
    clear ts.
    intros ts.
    rewrite existsb_exists.
    do 2 setoid_rewrite andb_true_iff.
    intros ((l & r) & Hin & 
      (Hanti%is_anticommute_QAType_syntactic_correct
      & Hl%IHdepth) & Hr%IHdepth).
    apply In_ne_list_app_partitions in Hin.
    destruct Hin as (Hlnn & Hrnn & Hlr).
    cbn [fst snd] in *.
    rewrite QA_scale_correct' in *.
    rewrite (@parseqc _ _ parseQC_sqrt2) in Hl, Hr.
    assert (Hscaled : (QAType_to_AType ts) = 
      gScaleA (C1 / √ 2) (
        gScaleA (RtoC (√ 2)) (QAType_to_AType l) ++ 
        gScaleA (RtoC (√ 2)) (QAType_to_AType r)
      )). 1:{ 
      rewrite <- Hlr.
      rewrite gScaleA_eq_iff_inv by (apply Cdiv_nonzero; nonzero).
      rewrite Cdiv_unfold, Cmult_1_l, Cinv_inv.
      unfold QAType_to_AType, gScaleA.
      now rewrite 2 map_app.
    } 
    rewrite Hscaled.
    do 2 constructor.
    + now destruct Hl.
    + now destruct Hr.
    + rewrite anticommute_AType_syntactic_gScaleA; 
      apply anticommute_AType_syntactic_comm;
      rewrite anticommute_AType_syntactic_gScaleA; 
      apply anticommute_AType_syntactic_comm;
      easy.
Qed.

Lemma solve_WF_AType {n} qs (ts : AType n) : 
  ParseAType qs ts -> 
  is_WF_QAType (length ts) qs = true -> 
  WF_AType ts.
Proof.
  intros [<-].
  apply is_WF_QAType_correct.
Qed.


Inductive Aeq : forall {n}, relation (AType n) :=
  | Aeq_nil {n} : @Aeq n [] []
  | Aeq_skip {n} (t : TType n) (a a' : AType n) : 
      Aeq a a' -> Aeq (t :: a) (t :: a')
  | Aeq_swap {n} (t t' : TType n) (a : AType n) : 
      Aeq (t :: t' :: a) (t' :: t :: a)
  | Aeq_join {n} (c d : C) (ps : list Pauli) (a : AType n) : 
      @Aeq n ((c, ps) :: (d, ps) :: a) ((c + d, ps) :: a)
  | Aeq_zero {n} (ps : list Pauli) (a : AType n) : 
      (* length ps = n ->  *)Aeq ((C0, ps) :: a) a
  | Aeq_symm {n} (a a' : AType n) : Aeq a a' -> Aeq a' a
  | Aeq_trans {n} (a b c : AType n) : Aeq a b -> Aeq b c -> Aeq a c.

Notation "a ≈ b" := (Aeq a b) (at level 70).

Lemma Aeq_refl {n} (a : AType n) : a ≈ a.
Proof.
  induction a; now constructor.
Qed.

Lemma Permutation_Aeq {n} (a a' : AType n) : Permutation a a' -> a ≈ a'.
Proof.
  intros HP.
  induction HP; solve [econstructor; eauto using Aeq].
Qed.

Lemma Aeq_join' {n} (t t' : TType n) (a : AType n) : 
  snd t = snd t' -> (t :: t' :: a) ≈ ((fst t + fst t', snd t) :: a).
Proof.
  destruct t as [c ps], t' as [d ?]; cbn.
  intros <-.
  constructor.
Qed.

Lemma Aeq_zero' {n} (t : TType n) (a : AType n) : 
  fst t = C0 -> (* length (snd t) = n ->  *)(t :: a) ≈ a.
Proof.
  destruct t as [c ps]; cbn.
  intros ->.
  now constructor.
Qed.

Add Parametric Relation {n} : (AType n) Aeq 
  reflexivity proved by Aeq_refl
  symmetry proved by Aeq_symm
  transitivity proved by Aeq_trans
  as Aeq_setoid.

#[export] Instance Permutation_Aeq_subrel {n} : 
  subrelation (@Permutation _) (@Aeq n).
Proof.
  exact Permutation_Aeq.
Qed.

Add Parametric Morphism {n} : (@cons (TType n)) 
  with signature eq ==> @Aeq n ==> @Aeq n as cons_Aeq.
Proof.
  solve [now constructor].
Qed.

Lemma Aeq_app_l {n} (a b b' : AType n) : 
  b ≈ b' -> a ++ b ≈ a ++ b'.
Proof.
  now induction a; intros ?; cbn; f_equiv; auto.
Qed.

Lemma Aeq_app_r {n} (a a' b : AType n) : 
  a ≈ a' -> a ++ b ≈ a' ++ b.
Proof.
  intros Ha.
  induction Ha; cbn; try solve [f_equiv; now constructor | now constructor].
  etransitivity; eauto.
Qed.

Add Parametric Morphism {n} : (@app (TType n)) 
  with signature @Aeq n ==> @Aeq n ==> @Aeq n as app_Aeq.
Proof.
  intros a a' Ha b b' Hb.
  transitivity (a' ++ b).
  - now apply Aeq_app_r.
  - now apply Aeq_app_l.
Qed.

Lemma Aeq_swap' {n} (a a' b : AType n) : 
  a ++ a' ++ b ≈ a' ++ a ++ b.
Proof.
  apply Permutation_Aeq.
  apply Permutation_app_swap_app.
Qed.

Lemma Aeq_app_comm {n} (a b : AType n) : 
  a ++ b ≈ b ++ a.
Proof.
  apply Permutation_Aeq.
  apply Permutation_app_comm.
Qed.

Definition TLinear {n m} (f : TType n -> TType m) :=
  forall c t, f (gScaleT c t) = gScaleT c (f t).

Lemma TLinear_eq {n m} (f : TType n -> TType m) (Hf : TLinear f) t : 
  f t = gScaleT (fst t) (f (C1, snd t)).
Proof.
  rewrite <- Hf.
  f_equal.
  destruct t.
  cbn.
  now rewrite Cmult_1_r.
Qed.

Lemma TLinear_0 {n m} (f : TType n -> TType m) (Hf : TLinear f) ps : 
  f (C0, ps) = (C0, snd (f (C1, ps))).
Proof.
  rewrite (TLinear_eq f Hf).
  cbn.
  destruct (f (C1, ps)).
  cbn.
  now rewrite Cmult_0_l.
Qed.

Lemma TLinear_plus {n m} (f : TType n -> TType m) (Hf : TLinear f) c d ps : 
  f (c + d, ps) = ((c + d) * (fst (f (C1, ps))), snd (f (C1, ps))).
Proof.
  rewrite (TLinear_eq f Hf).
  cbn.
  rewrite (surjective_pairing (f (C1, ps))).
  reflexivity.
Qed.

(* 
Lemma Aeq_map_proper' {n} (f : TType n -> TType n)
  (Hf : TLinear f) a a'
  (Hfl : forall t, In t a -> length (snd (f t)) = length (snd t))
  (Hfr : forall t, In t a' -> length (snd (f t)) = length (snd t)) : 
  a ≈ a' -> map f a ≈ map f a'.
Proof.
  intros Ha.
  induction Ha; [..|now eauto using Aeq_trans]; 
  cbn; try solve [f_equiv; now constructor | constructor; auto].
  - rewrite TLinear_plus, Cmult_plus_distr_r, (TLinear_eq _ Hf (c, ps)),
      (TLinear_eq _ Hf (d, ps)) by easy.
    cbn.
    rewrite (surjective_pairing (f (C1, ps))); cbn.
    constructor.
  - rewrite (TLinear_0 _ Hf).
    constructor.
    now rewrite Hfl. *)

Lemma Aeq_map_proper {n m} (f : TType n -> TType m)
  (Hf : TLinear f) (* (Hfl : forall t, length (snd (f t)) = length (snd t)) *) : 
  forall a a', a ≈ a' -> map f a ≈ map f a'.
Proof.
  intros a a' Ha.
  induction Ha; [..|now eauto using Aeq_trans]; 
  cbn; try solve [f_equiv; now constructor | constructor; auto].
  - rewrite TLinear_plus, Cmult_plus_distr_r, (TLinear_eq _ Hf (c, ps)),
      (TLinear_eq _ Hf (d, ps)) by easy.
    cbn.
    rewrite (surjective_pairing (f (C1, ps))); cbn.
    constructor.
  - rewrite (TLinear_0 _ Hf).
    constructor.
    (* now rewrite Hfl. *)
Qed.

Add Parametric Morphism {n} : gScaleA with signature
  eq ==> @Aeq n ==> @Aeq n as gScaleA_mor.
Proof.
  intros c.
  apply Aeq_map_proper.
  unfold TLinear.
  intros d [e ps].
  cbn.
  f_equal; ring.
Qed.

Definition Aminus {n} (a a' : AType n) : AType n := 
  a ++ gScaleA (- C1) a'.

(* Definition make_length {A} n (a : A) (l : list A) :=
  firstn n l ++ repeat a (n - length l).

Lemma length_make_length {A} n (a : A) l : 
  length (make_length n a l) = n.
Proof.
  unfold make_length.
  simpl_list.
  rewrite firstn_length, repeat_length.
  lia.
Qed.

Lemma make_length_eq {A} n (a : A) l : 
  length l = n -> make_length n a l = l.
Proof.
  intros Hl.
  unfold make_length.
  rewrite Hl, Nat.sub_diag.
  cbn.
  rewrite firstn_all2 by lia.
  apply app_nil_r.
Qed.

Lemma make_length_le {A} n (a : A) l : le (length l) n -> 
  make_length n a l = l ++ repeat a (n - length l).
Proof.
  intros Hl.
  unfold make_length.
  now rewrite firstn_all2 by auto.
Qed.


Lemma make_length_ge {A} n (a : A) l : le n (length l) -> 
  make_length n a l = firstn n l.
Proof.
  intros Hl.
  unfold make_length.
  replace (n - length l)%nat with O by lia.
  apply app_nil_r.
Qed.


Definition TmakeWF {n} (t : TType n) : TType n := 
    (fst t, make_length n gI (snd t)).

Lemma proper_length_TType_TmakeWF {n} (t : TType n) : n <> O ->
  proper_length_TType (TmakeWF t).
Proof.
  intros Hn; split; [easy|]; apply length_make_length.
Qed. *)

(* Definition AmakeWF {n} (t : TType n)  *)

(* Definition Amult {n} (a a' : AType n) : AType n := 
  gMulA a a'. *)

Definition Aanticomm {n} (a a' : AType n) := 
  (gMulA a a') ++ (gMulA a' a) ≈ [].

Add Parametric Morphism {n} : (@Aminus n) with signature 
  Aeq ==> Aeq ==> Aeq as Aminus_mor.
Proof. 
  unfold Aminus. 
  intros ? ? ? ? ? ->.
  now f_equiv.
Qed.

Lemma Aeq_gMulA_r {n} (a b b' : AType n) : 
  b ≈ b' -> gMulA a b ≈ gMulA a b'.
Proof.
  intros Hbb'.
  assert (forall t, map (gMulT t) b ≈ map (gMulT t) b'). 1:{
    intros t.
    apply Aeq_map_proper; [..|easy].
    intros c [d ps].
    destruct t as [ca qs].
    cbn.
    f_equal; ring.
  }
  induction a; cbn; f_equiv; auto.
Qed.

Lemma Aeq_gMulA_l {n} (a a' b : AType n) : 
  a ≈ a' -> gMulA a b ≈ gMulA a' b.
Proof.
  intros Ha.
  induction Ha; [..|now eauto using Aeq_trans]; 
  cbn; try solve [f_equiv; now constructor | constructor; auto].
  - apply Aeq_swap'.
  - rewrite app_assoc. 
    f_equiv.
    induction b as [|[cb t] b]; [reflexivity|]; cbn.
    do 2 change (?x :: ?y) with ([x] ++ y).
    rewrite 2 app_nil_r.
    rewrite 2 app_assoc.
    rewrite (Aeq_app_comm _ [_]).
    rewrite <- 2 app_assoc, (app_assoc [_] [_]).
    rewrite IHb.
    f_equiv.
    cbn.
    rewrite Aeq_join.
    f_equiv.
    f_equal.
    ring.
  - change (gMulA ?a ?b) with ([] ++ gMulA a b) at 2.
    f_equiv.
    induction b as [|[cb qs] b]; [reflexivity|].
    cbn.
    rewrite IHb.
    apply Aeq_zero'.
    cbn. 
    lca.
Qed.

Add Parametric Morphism {n} : (@gMulA n) with signature 
  Aeq ==> Aeq ==> Aeq as gMulA_mor.
Proof. 
  intros a a' Ha b b' Hb.
  transitivity (gMulA a' b).
  - now apply Aeq_gMulA_l.
  - now apply Aeq_gMulA_r.
Qed.

Add Parametric Morphism {n} : (@Aanticomm n) with signature
  Aeq ==> Aeq ==> iff as Aanticomm_mor.
Proof.
  unfold Aanticomm.
  intros ? ? Ha ? ? Hb.
  now rewrite Ha, Hb.
Qed.



(* Lemma Aeq_total {n} (a a' : AType n) : a ≈ a' <-> translateA a = translateA a'.
Abort. *)


Fixpoint Alift {n} (P : TType n -> AType n) (a : AType n) : AType n :=
  match a with 
  | [] => []
  | t :: a => gScaleA (fst t) (P (C1, snd t)) ++ Alift P a
  end.

Lemma Alift_eq_concat_map {n} (P : TType n -> AType n) (a : AType n) :
  Alift P a = concat (map (fun t => gScaleA (fst t) (P (C1, snd t))) a).
Proof.
  induction a; cbn; congruence.
Qed.

Lemma Aeq_join_gScaleA {n} (c d : C) (a : AType n) : 
  gScaleA c a ++ gScaleA d a ≈ gScaleA (c + d) a.
Proof.
  induction a; [reflexivity|].
  cbn.
  rewrite <- IHa.
  do 2 change (?x :: ?y) with ([x] ++ y).
  rewrite 2 app_assoc, 2 app_nil_r.
  rewrite (Aeq_app_comm _ [_]).
  rewrite <- 2 app_assoc, (app_assoc [_] [_]).
  f_equiv.
  destruct a; cbn.
  rewrite Aeq_join' by reflexivity.
  f_equiv. cbn. f_equal. lca.
Qed.

Lemma Aeq_gScaleA_0 {n} (a : AType n) : 
  gScaleA C0 a ≈ [].
Proof.
  induction a; [reflexivity|].
  cbn.
  destruct a; cbn.
  now rewrite Aeq_zero' by lca.
Qed.

Lemma Aeq_Alift_l {n} (P Q : TType n -> AType n) 
  (HPQ : forall t, P t ≈ Q t) a : 
  Alift P a ≈ Alift Q a.
Proof.
  induction a; [reflexivity|].
  cbn.
  now rewrite IHa, HPQ.
Qed.

Lemma Aeq_Alift_r {n} (P : TType n -> AType n) a a' : a ≈ a' ->
  Alift P a ≈ Alift P a'.
Proof.
  intros Ha.
  induction Ha; [..|now eauto using Aeq_trans]; 
  cbn; try solve [f_equiv; now constructor | constructor; auto].
  - apply Aeq_swap'. 
  - rewrite app_assoc, Aeq_join_gScaleA.
    reflexivity.
  - now rewrite Aeq_gScaleA_0.
Qed.

Add Parametric Morphism {n} : (@Alift n) with signature
  pointwise_relation (TType n) Aeq ==> Aeq ==> Aeq as Alift_mor.
Proof.
  intros P Q HPQ a b Hab.
  etransitivity; [apply Aeq_Alift_l | apply Aeq_Alift_r]; auto.
Qed.

Add Parametric Morphism {n X} : (@map X (@TType n)) with signature 
  pointwise_relation _ (fun t t' => [t] ≈ [t']) ==> eq ==> Aeq
  as Aeq_map_pointwise_mor.
Proof.
  intros f g Hfg b.
  induction b; [reflexivity|].
  cbn.
  rewrite IHb.
  change (?x :: ?y) with ([x] ++ y).
  f_equiv.
  apply Hfg.
Qed.

Lemma Aeq_map_pointwise_In {n X} (f g : X -> TType n) (l : list X) 
  (Hfg : forall x, In x l -> f x ≈ g x) : 
  map f l ≈ map g l.
Proof.
  induction l; [reflexivity|].
  cbn.
  rewrite IHl by (intros; apply Hfg; cbn; auto).
  change (?x :: ?y) with ([x] ++ y).
  f_equiv.
  now apply Hfg; left.
Qed.


Lemma gScaleA_dist_Aminus {n} (c : C) (a b : AType n) : 
  gScaleA c (Aminus a b) = Aminus (gScaleA c a) (gScaleA c b).
Proof.
  unfold Aminus.
  now rewrite gScaleA_dist_app, gScaleA_comm.
Qed.

Lemma Aanticomm_gScale_l {n} (c : C) (a b : AType n) : 
  Aanticomm a b -> Aanticomm (gScaleA c a) b.
Proof.
  intros Hab.
  unfold Aanticomm in *.
  rewrite gMulA_gScaleA_l, gMulA_gScaleA_r.
  rewrite <- gScaleA_dist_app, Hab.
  reflexivity.
Qed.

Lemma Aanticomm_gScale_r {n} (c : C) (a b : AType n) : 
  Aanticomm a b -> Aanticomm a (gScaleA c b).
Proof.
  intros Hab.
  unfold Aanticomm in *.
  rewrite gMulA_gScaleA_l, gMulA_gScaleA_r.
  rewrite <- gScaleA_dist_app, Hab.
  reflexivity.
Qed.

Lemma Alift_app {n} (P : TType n -> AType n) a b : 
  Alift P (a ++ b) = Alift P a ++ Alift P b.
Proof.
  rewrite 3 Alift_eq_concat_map.
  now rewrite map_app, concat_app.
Qed.

Lemma Alift_gScaleA_comm {n} (P : TType n -> AType n) c a : 
  Alift P (gScaleA c a) = gScaleA c (Alift P a).
Proof.
  rewrite 2 Alift_eq_concat_map.
  unfold gScaleA at 2 3.
  rewrite map_map, concat_map, map_map.
  f_equal.
  apply map_ext.
  intros [ct ps].
  cbn.
  rewrite <- gScaleA_merge.
  reflexivity.
Qed.

Lemma gMulA_eq_map_list_prod {n} (a b : AType n) : 
  gMulA a b = map (uncurry gMulT) (list_prod a b).
Proof.
  induction a; [reflexivity|].
  cbn.
  rewrite map_app, IHa, map_map.
  reflexivity.
Qed.

Lemma Aeq_gMulA_dist_app_r {n} (a b b' : AType n) : 
  gMulA a (b ++ b') ≈ gMulA a b ++ gMulA a b'.
Proof.
  induction a; [reflexivity|].
  cbn.
  rewrite map_app, IHa.
  rewrite app_assoc, (Aeq_app_comm (map _ _ ++ _)).
  rewrite app_assoc, (Aeq_app_comm (gMulA _ _)).
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma Alift_gMulA {n} (P : TType n -> AType n) 
  (HP_mul : forall (t t' : TType n), 
    gScaleA (fst (gMulT t t')) (P (C1, snd (gMulT t t'))) 
    ≈ gMulA (gScaleA (fst t) (P (C1, snd t)))
      (gScaleA (fst t') (P (C1, snd t')))) a a' : 
  Alift P (gMulA a a') ≈ gMulA (Alift P a) (Alift P a').
Proof.
  (* rewrite 2 gMulA_eq_map_list_prod./ *)
  induction a; [reflexivity|].
  cbn.
  rewrite Alift_app, gMulA_dist_app_l.
  rewrite IHa.
  f_equiv.
  clear -HP_mul.
  induction a'; [now rewrite gMulA_nil_r|].
  cbn.
  rewrite HP_mul.
  rewrite IHa', Aeq_gMulA_dist_app_r.
  reflexivity.
Qed.

Definition proper_TType {n} (t : TType n) :=
  fst t = C0 \/ length (snd t) = n.

Definition proper_AType {n} (a : AType n) :=
  Forall proper_TType a.

Lemma proper_TType_gScaleT {n} (c : C) (t : TType n) : 
  proper_TType t -> proper_TType (gScaleT c t).
Proof.
  intros [Hc | Hlen]; [left | right].
  - destruct t; cbn in *; subst; lca.
  - destruct t; now cbn in *.
Qed.

Lemma proper_AType_gScaleA {n} (c : C) (a : AType n) : 
  proper_AType a -> proper_AType (gScaleA c a).
Proof.
  unfold proper_AType, gScaleA.
  rewrite Forall_map.
  apply Forall_impl.
  apply proper_TType_gScaleT.
Qed.

Lemma proper_AType_app {n} (a b : AType n) : 
  proper_AType a -> proper_AType b -> proper_AType (a ++ b).
Proof.
  intros; now apply Forall_app.
Qed.


Lemma Alift_gMulA_lengths {n} (P : TType n -> AType n) 
  (HP_mul : forall (t t' : TType n), 
    proper_TType t -> proper_TType t' -> 
    gScaleA (fst (gMulT t t')) (P (C1, snd (gMulT t t'))) 
    ≈ gMulA (gScaleA (fst t) (P (C1, snd t)))
      (gScaleA (fst t') (P (C1, snd t')))) a a' : 
  proper_AType a -> proper_AType a' -> 
  Alift P (gMulA a a') ≈ gMulA (Alift P a) (Alift P a').
Proof.
  intros Ha Ha'.
  induction Ha as [|ta a Hta]; [reflexivity|].
  cbn.
  rewrite Alift_app, gMulA_dist_app_l.
  rewrite IHHa.
  f_equiv.
  clear -HP_mul Ha' Hta.
  induction Ha'; [now rewrite gMulA_nil_r|].
  cbn.
  rewrite HP_mul by auto.
  rewrite IHHa', Aeq_gMulA_dist_app_r.
  reflexivity.
Qed.






Inductive WF_AType' {n} : AType n -> Prop :=
  | WFA_T (t : TType n) : WF_TType t -> WF_AType' t
  | WFA_Aeq (a a' : AType n) : a ≈ a' -> proper_AType a' -> 
      WF_AType' a -> WF_AType' a'
  | WFA_plus (a a' : AType n) : WF_AType' a -> WF_AType' a' -> 
    Aanticomm a a' -> WF_AType' (gScaleA (C1 / √ 2) (a ++ a')).

Lemma WF_AType'_proper {n} (a : AType n) : WF_AType' a -> proper_AType a.
Proof.
  induction 1 as [t Ht|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - apply Forall_cons; [|constructor].
    right.
    apply Ht.
  - easy.
  - now apply proper_AType_gScaleA, proper_AType_app.
Qed.

(* Add Parametric Morphism {n} : WF_AType' with signature
  @Aeq n ==> iff as WF_AType'_mor.
Proof.
  intros a a' Ha; split; apply WFA_Aeq; easy.
Qed. *)

Lemma WF_gScaleA_pm_1 {n} (c : C) (a : AType n) : 
  c = C1 \/ c = - C1 -> WF_AType' a -> WF_AType' (gScaleA c a).
Proof.
  intros Hc Ha.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - constructor.
    destruct t as [ct ps].
    cbn.
    destruct Ht as [Hlen Hcoeff Htrace].
    constructor; try assumption.
    unfold coef_plus_minus_1 in *.
    cbn in *.
    destruct Hc as [-> | ->], Hcoeff as [-> | ->]; 
    [left | right.. | left]; lca.
  - econstructor; [..|apply IHHa]; [now rewrite Ha|].
    now apply proper_AType_gScaleA.
  - rewrite gScaleA_comm, gScaleA_dist_app.
    constructor; [auto..|].
    now apply Aanticomm_gScale_l, Aanticomm_gScale_r.
Qed.

Lemma proper_AType_gScaleA_0 {n} (a : AType n) : 
  proper_AType (gScaleA C0 a).
Proof.
  induction a; [constructor|].
  constructor; [|auto].
  left.
  destruct a; lca.
Qed.

Lemma proper_AType_Alift {n} (P : TType n -> AType n)
  (HP : forall ps, length ps = n -> proper_AType (P (C1, ps))) 
  (a : AType n) : 
  proper_AType a -> proper_AType (Alift P a).
Proof.
  intros Ha.
  induction Ha as [|ta a Ht IHa]; [constructor|].
  cbn.
  apply proper_AType_app; [|auto].
  revert Ht.
  unfold proper_TType.
  intros [->|]; [|
  auto using proper_AType_gScaleA].
  apply proper_AType_gScaleA_0.
Qed.




Lemma Alift_WF {n} (P : TType n -> AType n) 
  (HPprop : forall ps, length ps = n -> proper_AType (P (C1, ps)))
  (HPWF : forall ps, length ps = n ->
    trace_zero_syntax ps -> WF_AType' (P (C1, ps)))
  (* (HPWF : forall t, WF_TType t -> WF_AType' (P t)) *)
  (* (HPscale : forall t, P t = gScaleA (fst t) (P (C1, snd t))) *)
  (* (HP_mul : forall t t', P (gMulT t t') = gMulA (P t) (P t')) *)
  (HP_mul : forall (t t' : TType n), 
    proper_TType t -> proper_TType t' -> 
    gScaleA (fst (gMulT t t')) (P (C1, snd (gMulT t t'))) 
    ≈ gMulA (gScaleA (fst t) (P (C1, snd t)))
      (gScaleA (fst t') (P (C1, snd t')))) : 
  forall a, WF_AType' a -> WF_AType' (Alift P a).
Proof.
  intros a Ha.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - cbn. rewrite app_nil_r.
    apply WF_gScaleA_pm_1; [apply Ht|].
    apply HPWF; apply Ht.
  - econstructor; [..|apply IHHa]; [now rewrite Ha|].
    apply proper_AType_Alift; [|easy].
    auto.
  - rewrite Alift_gScaleA_comm, Alift_app.
    constructor; [auto..|].
    unfold Aanticomm, Aminus in *.
    rewrite <- 2 Alift_gMulA_lengths by auto using WF_AType'_proper.
    rewrite <- Alift_app.
    now rewrite Hacomm.
Qed.

Lemma Aeq_zero_lr_T {n} c c' ps qs : 
  c = C0 -> c' = C0 -> @Aeq n [(c, ps)] [(c', qs)].
Proof.
  intros -> ->.
  now rewrite 2 Aeq_zero.
Qed.

Lemma Aeq_gMulT_gTensorT_dist {n m : nat} (t1 t2 : TType n) (t3 t4 : TType m) :
  proper_TType t1 -> proper_TType t2 -> proper_TType t3 -> proper_TType t4 -> 
  gMulT (gTensorT t1 t3) (gTensorT t2 t4) ≈
  gTensorT (gMulT t1 t2) (gMulT t3 t4).
Proof.
  pose proof (gMulT_gTensorT_dist t1 t2 t3 t4) as Hbase.
  destruct t1 as [c1 ps1], t2 as [c2 ps2].
  destruct t3 as [c3 ps3], t4 as [c4 ps4].
  cbn.
  unfold proper_TType.
  cbn.
  intros [-> | Hps1]; [intros; apply Aeq_zero_lr_T; lca|].
  intros [-> | Hps2]; [intros; apply Aeq_zero_lr_T; lca|].
  intros [-> | Hps3]; [intros; apply Aeq_zero_lr_T; lca|].
  intros [-> | Hps4]; [intros; apply Aeq_zero_lr_T; lca|].
  
  bdestruct (n =? 0)%nat. 1: {
    destruct n; [|easy].
    destruct ps1; [|easy].
    destruct ps2; [|easy].
    cbn.
    f_equiv.
    f_equal.
    rewrite !Cmult_assoc.
    f_equal.
    lca.
  }
  bdestruct (m =? 0)%nat. 1: {
    destruct m; [|easy].
    destruct ps3; [|easy].
    destruct ps4; [|easy].
    cbn.
    rewrite !app_nil_r.
    f_equiv.
    f_equal.
    lca.
  }
  cbn in Hbase.
  now rewrite Hbase by easy.
Qed.

Lemma Aeq_gMulA_gTensorA {n m} (a1 a2 : AType n) (a3 a4 : AType m) :
  proper_AType a1 -> proper_AType a2 -> proper_AType a3 -> proper_AType a4 -> 
  gMulA (gTensorA a1 a3) (gTensorA a2 a4) ≈
  gTensorA (gMulA a1 a2) (gMulA a3 a4).
Proof.
  intros Ha1 Ha2 Ha3 Ha4.
  induction Ha1; [reflexivity|].
  cbn.
  rewrite gMulA_dist_app_l, gTensorA_app_dist.
  rewrite IHHa1.
  f_equiv.
  clear IHHa1.
  induction Ha2; [cbn; now rewrite gMulA_nil_r|].
  cbn.
  rewrite Aeq_gMulA_dist_app_r, IHHa2.
  f_equiv.
  clear IHHa2.
  induction Ha3; [reflexivity|].
  cbn.
  rewrite IHHa3, map_app.
  f_equiv.
  clear IHHa3.
  induction Ha4; [reflexivity|].
  cbn.
  rewrite IHHa4.
  change (?x :: ?y) with (TtoA x ++ y).
  f_equiv.
  now rewrite Aeq_gMulT_gTensorT_dist by auto.
Qed.

Definition TpadA {n} (bit : nat) (t : TType n) (a : AType 1) : AType n :=
  let '(_, ps) := t in 
  @gTensorA (bit + 1) (n - (bit + 1)) (
    @gTensorA bit 1 [(C1, firstn bit ps)] a)
    [(C1, skipn (bit + 1) ps)].

Lemma switch_to_app {A} (l : list A) (a : A) (n : nat) : 
  lt n (length l) -> 
  switch l a n = firstn n l ++ [a] ++ skipn (n + 1) l.
Proof.
  revert n; induction l; [cbn; lia|].
  intros [|n] Hn; [reflexivity|].
  cbn in *.
  now rewrite IHl by lia.
Qed.

Lemma Aeq_TpadA_T {n} (bit : nat) (t : TType n) (t' : TType 1) : lt bit n ->
  length (snd t) = n -> proper_TType t' ->
  TpadA bit t [t'] ≈ 
  [(fst t', switch (snd t) (hd gI (snd t')) bit)].
Proof.
  intros Hbit.
  destruct t as [ct ps].
  destruct t' as [ct' ps'].
  unfold proper_TType.
  cbn.
  intros Hps.
  intros [-> | Hps']; [intros; apply Aeq_zero_lr_T; lca|].
  rewrite switch_to_app by lia.
  replace ps' with [hd gI ps']; 
  [now rewrite Cmult_1_r, Cmult_1_l, app_assoc|].
  destruct ps' as [|? []]; easy.
Qed.

Lemma TpadA_switch {n} bit (t : TType n) a : lt bit n ->
  length (snd t) = n -> proper_AType a ->
  TpadA bit t a ≈ 
    map (fun t' =>
      (fst t', switch (snd t) (hd gI (snd t')) bit)) a.
Proof.
  intros Hbit Ht Ha.
  induction Ha; [now destruct t|].
  cbn.
  change (?x :: ?y) with ([x] ++ y).
  rewrite <- Aeq_TpadA_T by auto.
  rewrite <- IHHa.
  destruct t.
  unfold TpadA.
  rewrite <- gTensorA_app_dist.
  reflexivity.
Qed.

Lemma gMulT_proper {n} (t t' : TType n) : 
  proper_TType t -> proper_TType t' -> proper_TType (gMulT t t').
Proof.
  destruct t as [c ps], t' as [c' ps'].
  unfold proper_TType.
  cbn.
  intros [->|Hps]; [left; lca|].
  intros [->|Hps']; [left; lca|].
  right.
  unfold zipWith.
  simpl_list.
  rewrite combine_length.
  lia.
Qed.

Lemma gMulA_proper {n} (a a' : AType n) : 
  proper_AType a -> proper_AType a' -> proper_AType (gMulA a a').
Proof.
  intros Ha Ha'.
  induction Ha; [constructor|].
  cbn.
  apply proper_AType_app; [|auto].
  clear IHHa.
  induction Ha'; constructor; auto using gMulT_proper.
Qed.

Lemma list_prod_map_map {A B C D} (f : A -> B) (g : C -> D) l l' : 
  list_prod (map f l) (map g l') = 
    map (fun ab => (f (fst ab), g (snd ab))) (list_prod l l').
Proof.
  induction l; [reflexivity|].
  cbn.
  rewrite map_app.
  f_equal; [|auto].
  clear IHl.
  induction l'; [reflexivity|].
  cbn.
  congruence.
Qed.

Lemma in_list_prod_iff {A B} (l : list A) (l' : list B) a b : 
  In (a, b) (list_prod l l') <-> 
  In a l /\ In b l'.
Proof.
  induction l; [easy|].
  cbn.
  rewrite in_app_iff, IHl.
  enough (Hen : In (a, b) (map (fun y => (a0, y)) l')
    <-> (a0 = a /\ In b l')) by (rewrite Hen; tauto).
  rewrite in_map_iff.
  firstorder congruence.
Qed.

Definition Tswitch {n} (t : TType n) (p : Pauli) (bit : nat) : TType n :=
  (fst t, switch (snd t) p bit).

Lemma Tswitch_proper {n} (t : TType n) p bit : 
  proper_TType t -> proper_TType (Tswitch t p bit).
Proof.
  intros [Hc | Hlen]; [left; apply Hc|right].
  cbn.
  now rewrite switch_len.
Qed.

Lemma gMulT_length {n} (t t' : TType n) : length (snd (gMulT t t')) = 
  min (length (snd t)) (length (snd t')).
Proof.
  unfold gMulT.
  destruct t, t'.
  cbn.
  unfold zipWith.
  simpl_list.
  apply combine_length.
Qed.

Lemma Tswitch_length {n} (t : TType n) p bit : 
  length (snd (Tswitch t p bit)) = length (snd t).
Proof.
  unfold Tswitch.
  cbn.
  apply switch_len.
Qed.

Lemma TpadA_to_snd {n} bit (t : TType n) a : 
  TpadA bit t a = TpadA bit (C1, snd t) a.
Proof.
  now destruct t.
Qed.

Ltac split_Forall :=
  repeat first [apply List.Forall_cons | apply List.Forall_nil].

Lemma gTensorT_proper {n m} (a : TType n) (b : TType m) : 
  proper_TType a -> proper_TType b -> 
  proper_TType (gTensorT a b).
Proof.
  unfold proper_TType.
  destruct a as [ca psa], b as [cb psb].
  cbn.
  intros [->|Hpsa]; [intros; left; lca|].
  intros [->|Hpsb]; [left; lca|].
  right.
  simpl_list.
  congruence.
Qed.

Lemma gTensorA_proper {n m} (a : AType n) (b : AType m) : 
  proper_AType a -> proper_AType b -> 
  proper_AType (gTensorA a b).
Proof.
  intros Ha Hb.
  induction Ha; [constructor|].
  cbn.
  apply Forall_app; split; [|apply IHHa].
  clear Ha IHHa.
  induction Hb; [constructor|].
  cbn; constructor; [|apply IHHb].
  now apply gTensorT_proper.
Qed.

Lemma Aeq_swap_heads {n} (h h' : TType n) (a a' : AType n) : 
  h :: a ++ h' :: a' ≈ h :: h' :: (a ++ a').
Proof.
  change (?x :: ?y) with ([x] ++ y).
  change (?x :: ?y) with ([x] ++ y).
  rewrite app_nil_r.
  rewrite 2 app_assoc, (Aeq_app_comm _ [h']).
  rewrite <- 2 app_assoc, (app_assoc [h']), (app_assoc [h]).
  f_equiv.
  apply Aeq_app_comm.
Qed.

Lemma Aeq_gTensorA_l {n m} (a a' : AType n) (b : AType m) : 
  a ≈ a' -> gTensorA a b ≈ gTensorA a' b.
Proof.
  intros Ha.
  induction Ha; [..|now eauto using Aeq_trans]; 
  cbn; try solve [f_equiv; now constructor | constructor; auto].
  - apply Aeq_swap'.
  - rewrite app_assoc; f_equiv.
    induction b; [reflexivity|].
    cbn.
    rewrite Aeq_swap_heads.
    change (@cons) with (fun A (a : A) l => [a] ++ l); cbv beta.
    rewrite app_assoc.
    f_equiv; [|assumption].
    cbn.
    destruct a0.
    rewrite Aeq_join.
    f_equiv; f_equal; lca.
  - rewrite <- (app_nil_l (gTensorA a b)) at 2.
    f_equiv.
    induction b; [reflexivity|].
    cbn.
    destruct a0; rewrite Aeq_zero' by lca.
    assumption.
Qed.

Lemma Aeq_gTensorA_r {n m} (a : AType n) (b b' : AType m) : 
  b ≈ b' -> gTensorA a b ≈ gTensorA a b'.
Proof.
  intros Hb.
  induction a; [reflexivity|].
  cbn.
  rewrite IHa; f_equiv.
  apply Aeq_map_proper; [|assumption].
  intros c [d ps].
  destruct a as [ca psa].
  cbn.
  f_equal; lca.
Qed.

Add Parametric Morphism {n m} : (@gTensorA n m) with signature
  Aeq ==> Aeq ==> Aeq as gTensorA_mor.
Proof.
  intros a a' Ha b b' Hb.
  transitivity (gTensorA a' b).
  - now apply Aeq_gTensorA_l.
  - now apply Aeq_gTensorA_r.
Qed.

Lemma switch_overflow {X} (l : list X) (x : X) k : 
  le (length l) k -> 
  switch l x k = l.
Proof.
  intros Hk.
  apply (nth_ext _ _ x x); [now rewrite switch_len|].
  rewrite switch_len. 
  intros ? ?.
  now rewrite nth_switch_miss by lia.
Qed.

Lemma firstn_switch {X} (l : list X) (x : X) k n : 
  firstn n (switch l x k) = switch (firstn n l) x k.
Proof.
  revert n k; induction l; intros n k; [now destruct n|].
  destruct n; [easy|].
  destruct k; [easy|].
  cbn.
  f_equal.
  apply IHl.
Qed.


Lemma skipn_switch {X} (l : list X) (x : X) k n : le n k ->
  skipn n (switch l x k) = switch (skipn n l) x (k - n).
Proof.
  revert n k; induction l; intros n k; [now destruct n|].
  destruct n, k; [easy..|].
  intros Hnk%Nat.succ_le_mono.
  cbn.
  now apply IHl.
Qed.

Lemma skipn_switch_overflow {X} (l : list X) (x : X) k n : lt k n ->
  skipn n (switch l x k) = skipn n l.
Proof.
  revert n k; induction l; intros n k; [now destruct n|].
  destruct n, k; [easy..|].
  intros Hnk%Nat.succ_lt_mono.
  cbn.
  now apply IHl.
Qed.

Lemma combine_skipn {A B} (l : list A) (l' : list B) k : 
  skipn k (combine l l') = combine (skipn k l) (skipn k l').
Proof.
  revert k l'; induction l; [cbn; intros []; reflexivity|].
  intros [|k] [|a' l']; cbn; [reflexivity..|now rewrite combine_nil|].
  auto.
Qed.

Lemma Aeq_gMulA_TpadA {n} bit (t t' : TType n) a a' : lt bit n ->
  length (snd t) = n -> length (snd t') = n -> proper_AType a -> proper_AType a' ->
  gMulA (TpadA bit t a) (TpadA bit t' a') ≈ 
  gScaleA (cBigMul (zipWith gMul_Coef (firstn bit (snd t)) (firstn bit (snd t'))) * 
    cBigMul (zipWith gMul_Coef (skipn (bit+1) (snd t)) (skipn (bit+1) (snd t')))) (TpadA bit 
    (gMulT (Tswitch t gI bit) (Tswitch t' gI bit)) (gMulA a a')).
Proof.
  intros Hbit Ht Ht' Ha Ha'.
  rewrite (TpadA_to_snd _ t), (TpadA_to_snd _ t'), 
    (TpadA_to_snd bit (gMulT _ _)).
  unfold TpadA.
  replace (@gMulA n) with (@gMulA (bit + 1 + (n - (bit + 1)))) by (f_equal; lia).
  replace (@Aeq n) with (@Aeq (bit + 1 + (n - (bit + 1)))) by (f_equal; lia).
  replace (@gScaleA n) with (@gScaleA (bit + 1 + (n - (bit + 1)))) by (f_equal; lia).
  
  rewrite Aeq_gMulA_gTensorA by (try (apply gTensorA_proper; [|assumption]); split_Forall;
    right; cbn; rewrite 1?firstn_length, 1?skipn_length; lia).
  rewrite Aeq_gMulA_gTensorA by first [assumption | split_Forall;
    right; cbn; rewrite 1?firstn_length, 1?skipn_length; lia].
  rewrite <- gScaleA_merge, <- gTensorA_gScaleA_comm_r, 
    <- 2 gTensorA_gScaleA_comm_l.
  cbn -[gTensorA].
  rewrite !Cmult_1_l, !Cmult_1_r.
  f_equiv; [f_equiv|]; do 2 f_equal.
  - unfold zipWith.
    rewrite firstn_map, combine_firstn.
    rewrite 2 firstn_switch, 2 switch_overflow by (rewrite firstn_length; lia).
    reflexivity.
  - unfold zipWith.
    rewrite skipn_map, combine_skipn.
    now rewrite 2 skipn_switch_overflow by lia.
Qed. (* 

    rewrite 2 switch_to_app by lia.

    rewrite firstn_app_l.

  
    try (constructor;[right; cbn; rewrite skipn_length; lia|constructor]).
  
  cbn -[gTensorA gMulT].
  rewrite 3 TpadA_switch by
    solve [auto using gMulT_proper, gMulA_proper, Tswitch_proper |
      cbn -[gMulT]; rewrite gMulT_length, 2Tswitch_length; lia].
  cbn -[gMulT].
  rewrite 2 gMulA_eq_map_list_prod, map_map.
  rewrite list_prod_map_map, map_map.
  cbn.
  apply Aeq_map_pointwise_In.
  intros (ta & ta').
  cbn.
  rewrite in_list_prod_iff.
  intros [Hta Hta'].
  destruct ta as [ca psa], ta' as [ca' psa'], 
      t as [c ps], t' as [c' ps'].
  cbn -[cBigMul].
  unfold proper_AType in Ha, Ha'.
  rewrite Forall_forall in Ha, Ha'.
  apply Ha in Hta.
  apply Ha' in Hta'.
  revert Ht Ht' Hta Hta'.
  unfold proper_TType; cbn.
  intros Hps.
  intros Hps'.
  intros [->|Hpas]; [intros; apply Aeq_zero_lr_T; lca|].
  intros [->|Hpas']; [intros; apply Aeq_zero_lr_T; lca|].
  replace psa with [hd gI psa] by now destruct psa as [|? [|]].
  replace psa' with [hd gI psa'] by now destruct psa' as [|? [|]].
  cbn.
  f_equiv.
  f_equal.
  - f_equal.
    rewrite Cmult_1_l.
    clear Ha Ha' Hpas Hpas'.
    subst n.
    unfold cBigMul.
    rewrite fold_symmetric by (intros; lca).
    revert bit Hbit ps' Hps';
    induction ps as [|p ps]; [cbn in *; lia|].
    intros bit Hbit [|p' ps'] Hps'; [easy|].
    destruct bit; cbn. [lca|].
    rewrite <- IHps by now cbn in *; lia.
    lca.
  - clear Ha Ha' Hpas Hpas'.
    subst n.
    revert bit Hbit ps' Hps';
    induction ps as [|p ps]; [cbn in *; lia|].
    intros bit Hbit [|p' ps'] Hps'; [easy|].
    destruct bit; cbn; [reflexivity|].
    rewrite <- IHps by now cbn in *; lia.
    reflexivity.
Qed. *)

(* 
Lemma Aeq_gMulA_TpadA {n} bit (t t' : TType n) a a' : lt bit n ->
  proper_TType t -> proper_TType t' -> proper_AType a -> proper_AType a' ->
  gMulA (TpadA bit t a) (TpadA bit t' a') ≈ TpadA bit (gMulT t t') (gMulA a a').
Proof.
  intros Hbit Ht Ht' Ha Ha'.
  rewrite 3 TpadA_switch by auto using gMulT_proper, gMulA_proper.
  rewrite 2 gMulA_eq_map_list_prod, map_map.
  rewrite list_prod_map_map, map_map.
  cbn.
  apply Aeq_map_pointwise_In.
  intros (ta & ta').
  cbn.
  rewrite in_list_prod_iff.
  intros [Hta Hta'].
  
  f_equiv.
  f_equal.
  - destruct ta as [ca psa], ta' as [ca' psa'], 
      t as [c ps], t' as [c' ps'].
    cbn -[cBigMul].
    unfold proper_AType in Ha, Ha'.
    rewrite Forall_forall in Ha, Ha'.
    apply Ha in Hta.
    apply Ha' in Hta'.
    revert Ht Ht' Hta Hta'.
    unfold proper_TType; cbn.
    intros [->|Hps]; [intros; lca|].
    intros [->|Hps']; [intros; lca|].
    intros [->|Hpas]; [intros; lca|].
    intros [->|Hpas']; [intros; lca|].
    replace (cBigMul (map (uncurry gMul_Coef) (combine (switch ps (hd gI psa) bit)
        (switch ps' (hd gI psa') bit)))) with 
      (cBigMul (zipWith gMul_Coef psa psa') * cBigMul (zipWith gMul_Coef ps ps'));
        [lca|].
    replace psa with [hd gI psa] by now destruct psa as [|? [|]].
    replace psa' with [hd gI psa'] by now destruct psa' as [|? [|]].
    cbn.

    

    
  destruct ta, ta', t, t'; cbn; try lca.

  rewrite (surjective_pairing t), (surjective_pairing t').
  cbn.
  replace (@gMulA n) with (@gMulA (s bit + (n - s bit))) by (f_equal; lia).
  replace (@Aeq n) with (@Aeq (s bit + (n - s bit))) by (f_equal; lia).
  rewrite 2 app_nil_r.
  rewrite Aeq_gMulA_gTensorA.
  2: {
    induction Ha as [|ta a Hta Ha IHHa]; [constructor|].
    cbn.
    constructor.
    - destruct ta as [ca psa].
      revert Hta.
      unfold proper_TType.
      cbn.
      intros [->|Hpsa]; [left; lca|].
      revert Ht.
      unfold proper_TType.
      cbn.
      intros [->|Ht]; [left; lca|].
      right.
      rewrite app_length, Hpsa.
      rewrite firstn_length.
      lia.
    - apply IHHa.
  }
  2: {
    clear a Ha.
    induction Ha' as [|ta a Hta Ha IHHa]; [constructor|].
    cbn.
    constructor.
    - destruct ta as [ca psa].
      revert Hta.
      unfold proper_TType.
      cbn.
      intros [->|Hpsa]; [left; lca|].
      revert Ht'.
      unfold proper_TType.
      cbn.
      intros [->|Ht']; [left; lca|].
      right.
      rewrite app_length, Hpsa.
      rewrite firstn_length.
      lia.
    - apply IHHa.
  }
  2: {
    constructor; [|constructor].
    right.
  } *)

Definition Pon {n} (P : Pauli -> AType 1) (bit : nat) 
  (t : TType n) : AType n :=
  gScaleA (fst t) (TpadA bit t (P (nth bit (snd t) gI))).

Lemma Aeq_gTensorA_cons_r {n m} (a : AType n) (t : TType m) (b : AType m) : 
  gTensorA a (t :: b) ≈ gTensorA a [t] ++ gTensorA a b.
Proof.
  induction a; [reflexivity|].
  cbn.
  rewrite IHa.
  f_equiv.
  now rewrite Permutation_app_swap_app.
Qed.

(* Add Parametric Morphism {n m} : (@gTensorA n m) with signature
  Aeq ==> Aeq ==> Aeq as gTensorA_mor.
Proof.
  intros a a' Ha b b' Hb.
  transitivity (gTensorA a b').
  - clear a' Ha.
    induction Hb; [..|now eauto using Aeq_trans]; 
      cbn; 
      repeat match goal with
      |- context [gTensorA ?a (?t :: ?b)] => 
        lazymatch b with 
        | [] => fail
        | _ => rewrite (Aeq_gTensorA_cons_r a t b)
        end
      end;
      try solve [f_equiv; now constructor | constructor; auto].
    + apply Aeq_swap'.
    + rewrite app_assoc. 
      f_equiv.
      induction a as [|[ca psa] a]; [reflexivity|].
      cbn.
      rewrite Cmult_plus_distr_l.
      rewrite <- Aeq_join.
      f_equiv.
      rewrite Aeq_app_comm; cbn.
      f_equiv.
      now rewrite Aeq_app_comm.
    + replace (@cons (TType n0) (C0, ps) nil) with (@gScaleA n0 C0 [(C0, ps)]) 
        by (cbn; do 2 f_equal; lca).
      rewrite gTensorA_gScaleA_comm_r.
      rewrite Aeq_gScaleA_0.
      reflexivity.
  - clear b Hb.
    induction Ha; [..|now eauto using Aeq_trans]; 
      try solve [cbn; f_equiv; now constructor | constructor; auto].
    + apply Aeq_swap'.
    + cbn.
      rewrite app_assoc. 
      f_equiv.
      induction b' as [|[cb psb] b]; [reflexivity|].
      cbn.
      rewrite Cmult_plus_distr_r.
      rewrite <- Aeq_join.
      f_equiv.
      rewrite Aeq_app_comm; cbn.
      f_equiv.
      now rewrite Aeq_app_comm.
    + change (?x :: ?y) with ([x] ++ y). 
      rewrite (gTensorA_app_dist _ a).
      replace [(C0, ps)] with (@gScaleA n C0 [(C0, ps)]) 
        by (cbn; do 2 f_equal; lca).
      rewrite gTensorA_gScaleA_comm_l.
      rewrite Aeq_gScaleA_0.
      reflexivity.
Qed. *)

Lemma Aeq_dim_indep {k} n m (a a' : AType k) : 
  @Aeq n a a' <-> @Aeq m a a'.
Proof.
  split; intros Ha; (induction Ha; 
  unfold AType, TType in *; cbn;  [..|now eapply Aeq_trans; eauto];
      try solve [f_equiv; now constructor | constructor; auto]).
Qed.

Add Parametric Morphism {n} bit t : (@TpadA n bit t) with signature 
  Aeq ==> Aeq as TpadA_mor.
Proof.
  intros a a' Ha.
  unfold TpadA.
  destruct t.
  rewrite (Aeq_dim_indep n ((bit + 1) + (n - (bit + 1)))).
  now rewrite Ha.
Qed.

Lemma TpadA_t_ext {n} bit (t t' : TType n) (a : AType n) : 
  firstn bit (snd t) = firstn bit (snd t') -> 
  skipn (bit + 1) (snd t) = skipn (bit + 1) (snd t') -> 
  TpadA bit t a ≈ TpadA bit t' a.
Proof.
  unfold TpadA.
  destruct t, t'; cbn [fst snd].
  now intros -> ->.
Qed.

Lemma TpadA_ext {n} bit (t t' : TType n) (a a' : AType 1) : 
  firstn bit (snd t) = firstn bit (snd t') -> 
  skipn (bit + 1) (snd t) = skipn (bit + 1) (snd t') -> 
  a ≈ a' -> 
  TpadA bit t a ≈ TpadA bit t' a'.
Proof.
  intros Hf Hs ->.
  erewrite TpadA_t_ext; [reflexivity|..]; assumption.
Qed.

Lemma cBigMul_split k (l : list C) : 
  cBigMul l = cBigMul (firstn k l) * nth k l 1 * cBigMul (skipn (k + 1) l).
Proof.
  rewrite 3 cBigMul_alt.
  revert k; induction l; intros k; [destruct k; try lca|].
  destruct k; [cbn; try lca|].
  cbn.
  rewrite (IHl k).
  lca.
Qed.

Lemma snd_gMulT {n} (t t' : TType n) : 
  snd (gMulT t t') = zipWith gMul_base (snd t) (snd t').
Proof.
  now destruct t, t'.
Qed.

Lemma firstn_zipWith {A B C} (f : A -> B -> C) l l' k : 
  firstn k (zipWith f l l') = zipWith f (firstn k l) (firstn k l').
Proof.
  unfold zipWith.
  rewrite firstn_map, combine_firstn.
  reflexivity.
Qed.

Lemma skipn_zipWith {A B C} (f : A -> B -> C) l l' k : 
  skipn k (zipWith f l l') = zipWith f (skipn k l) (skipn k l').
Proof.
  unfold zipWith.
  rewrite skipn_map, combine_skipn.
  reflexivity.
Qed.

Lemma zipWith_nth {A B C} (f : A -> B -> C) (l : list A) (l' : list B) k x y : 
  length l = length l' -> 
  nth k (zipWith f l l') (f x y) = f (nth k l x) (nth k l' y).
Proof.
  unfold zipWith.
  intros Hl.
  rewrite (map_nth (uncurry f) _ (x, y)).
  rewrite combine_nth by auto.
  reflexivity.
Qed.

Lemma TpadA_gScaleA_dist {n} bit (t : TType n) (a : AType 1) c : 
  TpadA bit t (gScaleA c a) = gScaleA c (TpadA bit t a).
Proof.
  unfold TpadA; destruct t.
  now rewrite gTensorA_gScaleA_comm_r, 
    gTensorA_gScaleA_comm_l.
Qed.

Lemma gMul_Coef_nonzero (p q : Pauli) : 
  gMul_Coef p q <> C0.
Proof.
  destruct p; cbn; [nonzero|..];
  destruct q; nonzero.
Qed.

Definition Pmult (P : Pauli -> AType 1) : Prop :=
  forall p q, P (gMul_base p q) ≈ 
    gScaleA (/ gMul_Coef p q) (gMulA (P p) (P q)).

Lemma Aeq_gMulT_Pon {n} P bit (t t' : TType n) 
  (HPprop : forall p, proper_AType (P p))
  (HP : Pmult P) : lt bit n ->
  proper_TType t -> proper_TType t' ->
  Pon P bit (gMulT t t') ≈ 
    (* gScaleA (gMul_Coef (nth bit (snd t) gI) (nth bit (snd t') gI)) *)
      (gMulA (Pon P bit t) (Pon P bit t')).
Proof.
  unfold Pmult in HP.
  intros Hbit.
  intros [Hsnd | Ht]; [|intros [Hsnd | Ht']].
  - destruct t as [c ps], t' as [c' ps']; cbn [gMulT Pon].
    cbn in Hsnd.
    rewrite Hsnd; Csimpl.
    unfold Pon.
    cbn [fst].
    rewrite 2 Aeq_gScaleA_0.
    reflexivity.
  - destruct t as [c ps], t' as [c' ps']; cbn [gMulT Pon].
    cbn in Hsnd.
    rewrite Hsnd; Csimpl.
    unfold Pon.
    cbn [fst].
    rewrite 2 Aeq_gScaleA_0.
    rewrite gMulA_nil_r.
    reflexivity.
  - unfold Pon.
    rewrite gMulA_gScaleA_l, gMulA_gScaleA_r.
    rewrite Aeq_gMulA_TpadA by auto.
    rewrite !gScaleA_merge.
    rewrite snd_gMulT.
    change gI with (gMul_base gI gI) at 1.
    rewrite zipWith_nth by lia.
    rewrite HP, TpadA_gScaleA_dist, gScaleA_merge.

    apply gScaleA_mor.
    + destruct t as [c ps], t' as [c' ps']; cbn in *.
      rewrite (cBigMul_split bit).
      rewrite <- (Cmult_assoc (c * c')).
      f_equal.
      rewrite firstn_zipWith, skipn_zipWith.
      change C1 with (gMul_Coef gI gI).
      rewrite zipWith_nth by lia.
      C_field.
      apply gMul_Coef_nonzero.
    + apply TpadA_ext; [..|reflexivity].
      * rewrite 2 snd_gMulT.
        rewrite 2 firstn_zipWith.
        unfold Tswitch; cbn.
        rewrite 2 firstn_switch, 2 switch_overflow by (rewrite firstn_length; lia).
        reflexivity.
      * rewrite 2 snd_gMulT.
        rewrite 2 skipn_zipWith.
        unfold Tswitch; cbn.
        rewrite 2 skipn_switch_overflow by lia.
        reflexivity.
Qed.


Class ParseAType' {n} (ps : QAType n) (ts : AType n) := {
  parseatype' : QAType_to_AType ps ≈ ts
}.
Hint Mode ParseAType' - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance parseAT'_nil {n} : @ParseAType' n [] []. 
Proof.
  constructor. reflexivity.
Qed.

#[export]
Instance parseAT'_cons {n} q c ps qs ts : 
  ParseQC q c -> @ParseAType' n qs ts -> 
  @ParseAType' n ((Some q, ps) :: qs) ((c, ps) :: ts).
Proof.
  intros [Hq] [Hqs].
  constructor.
  cbn.
  rewrite Hq.
  f_equiv.
  apply Hqs.
Qed.

Identity Coercion Coef_C_id : Coef >-> C.

Lemma QT_scale_correct'' {n} (q : QC) (t : QTType n) : 
  QTType_to_TType (QT_scale q t) = gScaleT q (QTType_to_TType t).
Proof.
  destruct t; cbn.
  now rewrite QC2C_mult.
Qed.

Lemma QA_scale_correct'' {n} (q : QC) (t : QAType n) : 
  QAType_to_AType (QA_scale q t) ≈
    gScaleA q (QAType_to_AType t).
Proof.
  induction t; [reflexivity|].
  cbn.
  rewrite <- QT_scale_correct''.
  cbn.
  f_equiv.
  apply IHt.
Qed.


#[export]
Instance parseAT'_scale {n} q c qs ts : 
  ParseQC q c -> @ParseAType' n qs ts -> 
  @ParseAType' n (QA_scale q qs) (gScaleA c ts).
Proof.
  intros [Hq] [Hqs].
  constructor.
  rewrite QA_scale_correct'.
  rewrite Hq.
  now rewrite Hqs.
Qed.

Unset Typeclasses Unique Instances.

Lemma QT_reduce_correct' {n} (p : QTType n) : 
  QTType_to_TType (QT_reduce p) = 
  QTType_to_TType p.
Proof.
  destruct p; cbn.
  destruct o; cbn; [|reflexivity].
  now rewrite QCred_correct.
Qed.

Lemma QA_reduce_correct' {n} (ps : QAType n) : 
  QAType_to_AType (QA_reduce ps) ≈
  QAType_to_AType ps.
Proof.
  induction ps; [reflexivity|].
  cbn.
  bdestruct (QCeqb (maybe (fst a) 1%Q) 0%Q).
  - rewrite Aeq_zero'; [apply IHps|].
    unfold QTType_to_TType; cbn.
    now rewrite H; lca.
  - cbn.
    now rewrite QT_reduce_correct', IHps.
Qed.

Lemma QT_QA_minus_correct' {n} (a : QTType n) (ps : QAType n) : 
  QAType_to_AType (QT_QA_minus a ps) ≈
  QAType_to_AType ps ++ gScaleA (- C1) (QTType_to_TType a).
Proof.
  induction ps.
  - cbn.
    unfold QTType_to_TType.
    cbn.
    f_equiv.
    f_equal.
    destruct (fst a); cbn.
    + rewrite QC2C_opp; lca.
    + try lca.
      change (- 0)%Q with 0%Q.
      rewrite Q2R_0, Q2R_opp.
      lca.
  - cbn.
    bdestruct (eqb_listP (snd a) (snd a0)).
    + rewrite Aeq_app_comm.
      unfold QTType_to_TType.
      cbn.
      replace <- (snd a0).
      rewrite Aeq_join.
      f_equiv.
      f_equal.
      rewrite QC2C_minus.
      lca.
    + cbn.
      rewrite IHps.
      reflexivity.
Qed.

Lemma QA_minus_correct' {n} (ps qs : QAType n) : 
  QAType_to_AType (QA_minus ps qs) ≈
  Aminus (QAType_to_AType ps) (QAType_to_AType qs).
Proof.
  revert ps;
  induction qs; intros ps.
  - cbn.
    unfold Aminus.
    cbn.
    now rewrite app_nil_r.
  - cbn.
    unfold Aminus.
    cbn.
    unfold QAType_to_AType in IHqs.
    rewrite IHqs.
    fold (QAType_to_AType (QT_QA_minus a ps)).
    rewrite QT_QA_minus_correct'.
    unfold Aminus.
    rewrite <- app_assoc.
    reflexivity.
Qed.


Lemma QT_QA_plus_correct' {n} (p : QTType n) (qs : QAType n) : 
  QAType_to_AType (QT_QA_plus p qs) ≈
  QTType_to_TType p :: QAType_to_AType qs.
Proof.
  induction qs; [reflexivity|].
  cbn.
  bdestruct (eqb_listP (snd p) (snd a)).
  - cbn.
    unfold QTType_to_TType at 2 3.
    replace -> (snd p).
    rewrite Aeq_join, QC2C_plus.
    reflexivity.
  - cbn.
    change (@cons) with (fun A (a : A) l => [a] ++ l); cbv beta.
    rewrite app_assoc, (Aeq_app_comm [_] [_]).
    cbn.
    f_equiv.
    apply IHqs.
Qed.

Lemma QA_plus_correct' {n} (ps qs : QAType n) : 
  QAType_to_AType (QA_plus ps qs) ≈
  QAType_to_AType ps ++ QAType_to_AType qs.
Proof.
  unfold QAType_to_AType.
  revert qs; induction ps; intros qs; [reflexivity|].
  cbn.
  rewrite IHps.
  fold (QAType_to_AType (QT_QA_plus a qs)).
  rewrite QT_QA_plus_correct'.
  rewrite Aeq_app_comm; cbn.
  rewrite Aeq_app_comm.
  reflexivity.
Qed.



Lemma Aminus_diag {n} (ps : AType n) : 
  Aminus ps ps ≈ [].
Proof.
  unfold Aminus.
  induction ps; [reflexivity|].
  cbn.
  rewrite Aeq_swap_heads, IHps.
  destruct a; cbn.
  rewrite Aeq_join, Aeq_zero'; [reflexivity|].
  lca.
Qed.

Lemma Aeq_of_Aminus_0 {n} (ps qs : AType n) : 
  Aminus ps qs ≈ [] -> ps ≈ qs.
Proof.
  intros Hpq.
  rewrite <- (app_nil_l qs).
  rewrite <- Hpq.
  unfold Aminus.
  rewrite <- app_assoc, (Aeq_app_comm _ qs).
  fold (Aminus qs qs).
  rewrite Aminus_diag.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma QA_reflexive_solve_lemma' {n} (qs ps : QAType n) : 
  QA_reduce (QA_minus qs ps) = [] -> 
  QAType_to_AType qs ≈ QAType_to_AType ps.
Proof.
  intros Heq.
  apply Aeq_of_Aminus_0.
  rewrite <- QA_minus_correct'.
  rewrite <- QA_reduce_correct'.
  rewrite Heq.
  reflexivity.
Qed.

Lemma AType_Aeq_reflexive_solve_lemma {n : nat} 
  (qs qs' : QAType n) (ts ts' : AType n) : 
  ParseAType' qs ts ->
  ParseAType' qs' ts' ->
  QA_reduce (QA_minus (QA_plus qs []) qs') = [] ->
  ts ≈ ts'.
Proof.
  intros [Hqs] [Hqs'] Hred%QA_reflexive_solve_lemma'.
  rewrite <- Hqs, <- Hqs'.
  rewrite QA_plus_correct', app_nil_r in Hred.
  assumption.
Qed.










Definition S_P (p : Pauli) : AType 1 :=
  match p with
  | gI => aI
  | gX => aY
  | gY => maX
  | gZ => aZ
  end.

Definition H_P (p : Pauli) : AType 1 :=
  match p with
  | gI => aI
  | gX => aZ
  | gY => maY
  | gZ => aX
  end.

Definition T_P (p : Pauli) : AType 1 :=
  match p with
  | gI => aI
  | gX => [(C1 / √ 2, [gX]); (C1 / √ 2, [gY])]
  | gY => [(- C1 / √ 2, [gX]); (C1 / √ 2, [gY])]
  | gZ => aZ
  end.

Lemma S_P_mult : Pmult S_P. 
Proof.
  intros p q.
  destruct p, q; solve [cbn; f_equiv; f_equal; C_field].
Qed.

Lemma H_P_mult : Pmult H_P. 
Proof.
  intros p q.
  destruct p, q; solve [cbn; f_equiv; f_equal; C_field].
Qed.

Lemma Cinv_1 : / C1 = C1.
Proof.
  C_field.
Qed.

#[export]
Instance parseqc_Ci : ParseQC (mkQC 0 0 1 0) Ci.
Proof.
  constructor.
  lca.
Qed.


Ltac validate_red := 
  lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt 
    Q2R IZR QC2C Cexp PI sin cos atype_eq Copp
    triple pred_eq].

Lemma T_P_mult : Pmult T_P. 
Proof.
  intros p q.
  destruct p, q; cbn;
  apply (AType_Aeq_reflexive_solve_lemma _ _ _ _ _ _); reflexivity.
Qed.

Definition Topp {n} (t : TType n) : TType n :=
  (Copp (fst t), snd t).

Arguments Topp {_} !_ /.

Lemma Topp_eq_scale {n} (t : TType n) : 
  Topp t = gScaleT (-C1) t.
Proof.
  destruct t; cbn; f_equal; lca.
Qed.

Definition CNOT_P {n} (ctrl targ : nat) (t : TType n) : AType n :=
  let l := snd t in 
  match nth ctrl l gI with 
  | gI => 
    match nth targ l gI with 
    | gY | gZ => [Tswitch t gZ ctrl]
    | _ => [t]
    end
  | gX => 
    match nth targ l gI with 
    | gI => [Tswitch (Tswitch t gX ctrl) gX targ]
    | gX => [Tswitch (Tswitch t gX ctrl) gI targ]
    | gY => [Tswitch (Tswitch t gY ctrl) gZ targ]
    | gZ => [Topp (Tswitch (Tswitch t gY ctrl) gY targ)]
    end
  | gY => 
    match nth targ l gI with 
    | gI => [Tswitch (Tswitch t gY ctrl) gX targ]
    | gX => [Tswitch (Tswitch t gY ctrl) gI targ]
    | gY => [Topp (Tswitch (Tswitch t gX ctrl) gZ targ)]
    | gZ => [Tswitch (Tswitch t gX ctrl) gY targ]
    end
  | gZ => 
    match nth targ l gI with 
    | gY | gZ => [Tswitch t gI ctrl]
    | _ => [t]
    end
  end.

Arguments CNOT_P {_} _ _ !_ /.

Lemma switch_same {A} (l : list A) (a : A) (k : nat) (d : A) : 
  nth k l d = a -> 
  switch l a k = l.
Proof.
  revert k; induction l; intros k; [reflexivity|].
  destruct k.
  - cbn.
    now intros ->.
  - cbn.
    now intros ->%IHl.
Qed.

Lemma CNOT_P_implements_computeHT {n} ctrl targ (t : TType n) : ctrl <> targ -> 
  CNOT_P ctrl targ t = computeFinalStep (CNOT ctrl targ) n [t].
Proof.
  intros Hct.
  destruct t as [c l].
  cbn.
  destruct (nth ctrl l gI) eqn:Hctrl;
  destruct (nth targ l gI) eqn:Htarg; cbn; 
  rewrite <- ?Copp_mult_distr_r, 1?Cmult_1_r; try reflexivity.
  all: erewrite switch_same by 
    (rewrite nth_switch_miss by lia; eassumption);
    reflexivity.
Qed.

(* 
Lemma P_mul_of_base {n} (P : TType n -> AType n) 
  (HP : forall ) *)

Lemma fst_gMulT {n} (t t' : TType n) : 
  fst (gMulT t t') = fst t * fst t' * 
    cBigMul (zipWith gMul_Coef (snd t) (snd t')).
Proof.
  destruct t, t'; reflexivity.
Qed.

Lemma zipWith_switch_r {A B C} (f : A -> B -> C) l l' a b k : 
  zipWith f l (switch l' b k) = switch (zipWith f l l') (f (nth k l a) b) k.
Proof.
  revert k l'; induction l as [|al l]; [reflexivity|]; 
  intros k [|bl' l']; [reflexivity|].
  destruct k; [reflexivity|].
  cbn.
  f_equal.
  apply IHl.
Qed.

Lemma zipWith_switch_l {A B C} (f : A -> B -> C) l l' a b k : 
  zipWith f (switch l a k) l' = switch (zipWith f l l') (f a (nth k l' b)) k.
Proof.
  revert k l'; induction l as [|al l]; [reflexivity|]; 
  intros k [|bl' l']; [cbn; now rewrite combine_nil|].
  destruct k; [reflexivity|].
  cbn.
  f_equal.
  apply IHl.
Qed.

Lemma zipWith_switch_r' {A C} (f : A -> A -> C) l l' b k : 
  zipWith f l (switch l' b k) = switch (zipWith f l l') (f (nth k l b) b) k.
Proof.
  apply zipWith_switch_r.
Qed.

Lemma zipWith_switch_l' {A C} (f : A -> A -> C) l l' a k : 
  zipWith f (switch l a k) l' = switch (zipWith f l l') (f a (nth k l' a)) k.
Proof.
  apply zipWith_switch_l.
Qed.

Lemma cBigMul_switch (l : list C) (c : C) k : lt k (length l) -> 
  nth k l C1 <> C0 -> 
  cBigMul (switch l c k) = c / nth k l C1 * cBigMul l.
Proof.
  intros Hk Hkl.
  rewrite switch_inc, <- 2!cBigMul_app, (cBigMul_split k l) by auto.
  cbn -[skipn].
  replace (s k) with (k + 1)%nat by lia.
  unfold Coef.
  C_field.
Qed.

Lemma cBigMul_switch_zipWith_gMul_Coef (ps qs : list Pauli) 
  (c : C) k : length ps = length qs -> lt k (length ps) -> 
  cBigMul (switch (zipWith gMul_Coef ps qs) c k) = 
  c / gMul_Coef (nth k ps gI) (nth k qs gI) * cBigMul (zipWith gMul_Coef ps qs).
Proof.
  intros Hpq Hkp.
  rewrite cBigMul_switch.
  2: {
    erewrite zipWith_len_pres; eauto.
  }
  2: {
    change C1 with (gMul_Coef gI gI).
    rewrite zipWith_nth by auto.
    apply gMul_Coef_nonzero.
  }
  change C1 with (gMul_Coef gI gI).
  rewrite zipWith_nth by auto.
  reflexivity.
Qed.


Lemma cBigMul_switch_zipWith_gMul_Coef_2 (ps qs : list Pauli) 
  (c c' : C) k k' : length ps = length qs -> lt k (length ps) -> 
  lt k' (length ps) -> k <> k' ->
  cBigMul (switch (switch (zipWith gMul_Coef ps qs) c' k') c k)  = 
  c * c' / (gMul_Coef (nth k ps gI) (nth k qs gI) * 
    gMul_Coef (nth k' ps gI) (nth k' qs gI)) * 
  cBigMul (zipWith gMul_Coef ps qs).
Proof.
  intros Hpq Hkp Hk'p Hkk'.
  rewrite cBigMul_switch.
  2: {
    erewrite switch_len, zipWith_len_pres; eauto.
  }
  2: {
    change C1 with (gMul_Coef gI gI).
    rewrite nth_switch_miss by auto.
    rewrite zipWith_nth by auto.
    apply gMul_Coef_nonzero.
  }
  rewrite cBigMul_switch_zipWith_gMul_Coef by auto.
  unfold Cdiv.
  change C1 with (gMul_Coef gI gI).
  rewrite nth_switch_miss, zipWith_nth by auto.
  rewrite Cinv_mult_distr.
  lca.
Qed.

Lemma Copp_inv_distr (c : C) : / - c = - / c.
Proof.
  destruct (Ceq_dec c C0) as [->|].
  - now rewrite Copp_0, Cinv_0, Copp_0.
  - C_field; auto using Copp_neq_0_compat.
Qed.

Lemma Copp_div_distr_r (c d : C) : c / - d = - (c / d).
Proof.
  rewrite Cdiv_unfold, Copp_inv_distr; lca.
Qed.

Lemma Copp_div_distr_l (c d : C) : (- c) / d = - (c / d).
Proof.
  lca.
Qed.


Lemma CNOT_P_mult {n} (ctrl targ : nat) (t t' : TType n) : 
  lt ctrl n -> lt targ n -> ctrl <> targ ->
    let P := @CNOT_P n ctrl targ in  
    proper_TType t -> proper_TType t' -> 
    gScaleA (fst (gMulT t t')) (P (C1, snd (gMulT t t'))) 
    ≈ gMulA (gScaleA (fst t) (P (C1, snd t)))
      (gScaleA (fst t') (P (C1, snd t'))).
Proof.
  intros Hctrl Htarg Hct.
  cbv zeta.
  unfold proper_TType.
  intros [Hfst | Ht]; [intros _; destruct t, t'; cbn [fst snd gMulT] in *;
    rewrite Hfst; rewrite ?Cmult_0_l, ?Aeq_gScaleA_0; reflexivity|].
  intros [Hfst | Ht']; [destruct t, t'; cbn [fst snd gMulT] in *;
    rewrite Hfst; rewrite Cmult_0_r, ?Cmult_0_l, ?Aeq_gScaleA_0, gMulA_nil_r; 
      reflexivity|].
  rewrite snd_gMulT.
  rewrite gMulA_gScaleA_l, gMulA_gScaleA_r, gScaleA_merge.
  rewrite fst_gMulT, <- gScaleA_merge.
  apply gScaleA_mor; [reflexivity|].
  unfold CNOT_P; cbn.
  change gI with (gMul_base gI gI).
  rewrite 2!zipWith_nth by lia.
  cbn [gMul_base].
  assert (Hc_t : lt ctrl (length (snd t))) by lia.
  assert (Hc_t' : lt ctrl (length (snd t'))) by lia.
  assert (Ht_t : lt targ (length (snd t))) by lia.
  assert (Ht_t' : lt targ (length (snd t'))) by lia.
  assert (Htt' : length (snd t) = length (snd t')) by lia.
  assert (Ht_c : targ <> ctrl) by easy.
  destruct (nth ctrl (snd t) gI) eqn:Hctrl_t;
  destruct (nth targ (snd t) gI) eqn:Htarg_t;
  destruct (nth ctrl (snd t') gI) eqn:Hctrl_t';
  destruct (nth targ (snd t') gI) eqn:Htarg_t'; 
  cbn [gMul_base map gScaleT gMulA gMulT app Tswitch fst snd];
  rewrite ?Cmult_1_r, ?Cmult_1_l; 
  match goal with
  | |- ?x ≈ ?x => reflexivity
  | _ => idtac
  end.
  all:
  rewrite 4?(zipWith_switch_l _ _ _ _ gI), 4?(zipWith_switch_r _ _ _ gI),
    1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t';
  cbn [gMul_Coef gMul_base].
  all:  repeat progress
      rewrite 1?nth_switch_hit, 1?nth_switch_miss,
        1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t' by (rewrite 1?switch_len; lia); cycle 78.
  all: rewrite ?switch_switch_overshadow, 
    2?(switch_switch_diff ctrl targ _ _ _ Hct), 
    2?switch_switch_overshadow,
    2?(switch_switch_diff ctrl targ _ _ _ Hct),
    2?switch_switch_overshadow,
    2?(switch_switch_diff ctrl targ _ _ _ Hct),
    2?switch_switch_overshadow.
  all: tryif rewrite (cBigMul_switch_zipWith_gMul_Coef_2 
    _ _ _ _ _ _ Htt' Hc_t Ht_t Hct) then 
    rewrite 1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t'; cbn [gMul_Coef] 
    else idtac.
  all: f_equiv; f_equal; [Csimpl; 
    (repeat progress rewrite 1?Ci2, 1?Copp_div_distr_r, 1?Copp_div_distr_l, 
      <- 2?Copp_mult_distr_l, <- 1?Copp_mult_distr_r, 
      1?Copp_involutive);
    try (rewrite Cdiv_unfold, Cinv_r, ?Cmult_1_l, ?Cmult_1_r by nonzero); 
    reflexivity || 
     (* ||  *)
    idtac
    |..].
  all: try first [apply (f_equal cBigMul) | apply (f_equal (fun x => switch x _ _))];
    symmetry.
  all: try (apply (switch_same _ _ _ gI); 
    rewrite (zipWith_nth gMul_base _ _ _ gI gI) by auto;
    rewrite 1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t'; cbn [gMul_Coef];
    reflexivity).
  all: try (apply (switch_same _ _ _ C1);
    rewrite (zipWith_nth gMul_Coef _ _ _ gI gI) by auto;
    rewrite 1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t'; cbn [gMul_Coef];
    reflexivity).
  
  all: rewrite (switch_same _ _ _ gI) by
     (rewrite nth_switch_miss, (zipWith_nth gMul_base _ _ _ gI gI),
       1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t' by auto;
       reflexivity).
    
  all: apply (switch_same _ _ _ gI); 
    rewrite (zipWith_nth gMul_base _ _ _ gI gI) by auto;
    rewrite 1?Hctrl_t, 1?Htarg_t, 1?Hctrl_t', 1?Htarg_t'; cbn [gMul_Coef];
    reflexivity.
Qed.


Definition S_A {n} (bit : nat) (a : AType n) : AType n :=
  Alift (Pon S_P bit) a.

Definition H_A {n} (bit : nat) (a : AType n) : AType n :=
  Alift (Pon H_P bit) a.

Definition T_A {n} (bit : nat) (a : AType n) : AType n :=
  Alift (Pon T_P bit) a.

Lemma WF_TType_proper {n} (t : TType n) : WF_TType t -> proper_TType t.
Proof.
  intros [[] ? ?]; now right.
Qed.

Lemma Aeq_gTensorA_app_r {n m} (a : AType n) (b b' : AType m) : 
  gTensorA a (b ++ b') ≈ gTensorA a b ++ gTensorA a b'.
Proof.
  induction a; [reflexivity|].
  cbn.
  rewrite map_app, IHa.
  rewrite 2 app_assoc.
  f_equiv.
  rewrite 2 (Aeq_app_comm _ (gTensorA _ b)).
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma gTensorA_WF {n m} (a : AType n) (b : AType m) : 
  WF_AType' a -> WF_AType' b -> 
  WF_AType' (gTensorA a b).
Proof.
  intros Ha;
  revert b.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - intros b Hb.
    induction Hb as [t' Ht'|b b' Hb HWF'|b b' Hb IHb' Hb' IHb Hbcomm].
    + cbn.
      constructor.
      now apply WF_TType_tensor.
    + econstructor; 
      [rewrite <- Hb; reflexivity|..|assumption].
      apply gTensorA_proper; split_Forall; auto using WF_TType_proper.
    + rewrite gTensorA_gScaleA_comm_r.
      assert (proper_AType b) by now apply WF_AType'_proper.
      assert (proper_AType b') by now apply WF_AType'_proper.
      assert (proper_AType t) by now apply WF_AType'_proper, WFA_T.
      

      econstructor; 
      [apply gScaleA_mor; [reflexivity|now rewrite Aeq_gTensorA_app_r]
        |..].
      1: 
        apply proper_AType_gScaleA, gTensorA_proper;
          [auto using WFA_T, WF_TType_proper, WF_AType'_proper|];
        now apply Forall_app; split; apply WF_AType'_proper.
      constructor; [auto..|].
      unfold Aanticomm.
      rewrite 2 Aeq_gMulA_gTensorA by auto using WF_AType'_proper.
      rewrite <- Aeq_gTensorA_app_r.
      unfold Aanticomm, Aminus in Hbcomm.
      rewrite Hbcomm.
      now rewrite gTensorA_nil_r.
  - intros b Hb.
    econstructor; [now rewrite <- Ha|
      auto using gTensorA_proper, WF_AType'_proper|].
    auto.
  - intros b Hb.
    rewrite gTensorA_gScaleA_comm_l, gTensorA_app_dist.
    constructor; auto.
    unfold Aanticomm.
    rewrite 2 Aeq_gMulA_gTensorA by auto using WF_AType'_proper.
    rewrite <- gTensorA_app_dist.
    unfold Aanticomm, Aminus in Hacomm.
    now rewrite Hacomm.
Qed.


Lemma TpadA_WF {n} k (t : TType n) (a : AType 1) : lt k n ->
  length (snd t) = n -> WF_AType' a -> 
  WF_AType' (TpadA k t a).
Proof.
  intros Hkn Ht Ha.
  unfold TpadA.
  destruct t; cbn [fst snd] in *.
  replace (@WF_AType' n) with
    (@WF_AType' (k + 1 + (n - (k + 1)))) by (f_equal; lia).
  induction Ha as [t' Ht'|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - cbn.
    destruct t' as [c' ps'].
    destruct Ht' as [[Hlen' Hlen] Hc' Htrace].
    unfold coef_plus_minus_1 in Hc'.
    cbn in *.
    Csimpl.
    do 2 constructor.
    + split; [lia|].
      cbn.
      simpl_list;
      rewrite firstn_length, skipn_length; lia.
    + destruct Hc' as [-> | ->]; [left|right]; easy.
    + now apply trace_zero_syntax_L, trace_zero_syntax_R.
  - econstructor;
    [now rewrite <- Ha|..|assumption].
    repeat apply gTensorA_proper; auto; split_Forall;
    right; cbn.
    + rewrite firstn_length; lia.
    + rewrite skipn_length; lia.
  - rewrite gTensorA_gScaleA_comm_r, gTensorA_gScaleA_comm_l.
    econstructor.
    + rewrite Aeq_gTensorA_app_r, gTensorA_app_dist.
      reflexivity.
    + apply proper_AType_gScaleA, gTensorA_proper;
      [|split_Forall; right; cbn; rewrite skipn_length; lia].
      apply gTensorA_proper;
      [split_Forall; right; cbn; rewrite firstn_length; lia|].
      apply Forall_app; split; apply WF_AType'_proper; auto.
    + constructor; [auto..|].
    
      assert (proper_AType a) by now apply WF_AType'_proper.
      assert (proper_AType a') by now apply WF_AType'_proper.
      assert (@proper_AType (n - (k+1)) [(C1, skipn (k + 1) l)]) by
        (split_Forall; right; cbn; rewrite skipn_length; lia).
      assert (@proper_AType k [(C1, firstn k l)]) by
        (split_Forall; right; cbn; rewrite firstn_length; lia).
      

      (* assert (proper_AType t) by now apply WF_AType'_proper, WFA_T. *)
      
      unfold Aanticomm, Aminus.
      rewrite 4 Aeq_gMulA_gTensorA by
        auto using gTensorA_proper.
      rewrite <- gTensorA_app_dist, <- Aeq_gTensorA_app_r.
      unfold Aanticomm, Aminus in Hacomm.
      rewrite Hacomm.
      rewrite gTensorA_nil_r.
      reflexivity.
Qed.

Local Hint Rewrite skipn_length firstn_length combine_length 
  @switch_len @gMulT_length : list.

Lemma trace_zero_syntax_iff_Exists ps : 
  trace_zero_syntax ps <-> Exists not_gI ps.
Proof.
  split.
  - intros Htr.
    induction Htr; [constructor; WF_auto..| |];
    rewrite Exists_app; eauto.
  - intros Hex.
    induction Hex; change (?x :: ?y) with ([x] ++ y);
    [|auto using trace_zero_syntax_R].
    apply trace_zero_syntax_L.
    destruct H as [| [|]]; subst;
    constructor.
Qed.

Lemma Exists_singleton {A} (P : A -> Prop) a : 
  Exists P [a] <-> P a.
Proof.
  rewrite Exists_cons, Exists_nil.
  intuition fail.
Qed.


Lemma Pon_WF {n} (P : Pauli -> AType 1) bit 
  (HP : forall p, not_gI p -> WF_AType' (P p))
  (HPI : P gI = gI) ps : lt bit n -> 
  length ps = n -> trace_zero_syntax ps ->
  WF_AType' (@Pon n P bit (C1, ps)).
Proof.
  intros Hbit Hps Htrace.
  unfold Pon.
  cbn [fst snd].
  rewrite gScaleA_1.
  destruct (nth bit ps gI) eqn:Hnth; 
  [|apply TpadA_WF; auto; apply HP; WF_auto..].
  rewrite HPI.
  cbn.
  Csimpl.
  refine (WFA_T _ _).
  constructor; [split; [lia|cbn; simpl_list; cbn; lia]|now left|cbn].
  (* rewrite trace_zero_syntax_iff_Exists in *. *)
  erewrite <- switch_same in Htrace by eauto.
  rewrite switch_inc in Htrace by lia.
  rewrite <- app_assoc.
  rewrite Nat.add_comm; cbn [Nat.add].
  assumption.
Qed.

Definition CNOT_A {n} (ctrl targ : nat) (a : AType n) : AType n :=
  Alift (CNOT_P ctrl targ) a.

Lemma P_mul_of_base_linear {n} (P : TType n -> AType n) 
  (HP : forall t t' : TType n, proper_TType t -> proper_TType t' ->
    P (gMulT t t') ≈ 
    gMulA (P t) (P t'))
  (HPlin : forall t : TType n, gScaleA (fst t) (P (C1, snd t)) ≈ P t)
  : forall t t' : TType n,
    proper_TType t -> proper_TType t' ->
    gScaleA (fst (gMulT t t')) (P (C1, snd (gMulT t t')))
    ≈ gMulA (gScaleA (fst t) (P (C1, snd t)))
        (gScaleA (fst t') (P (C1, snd t'))).
Proof.
  intros.
  rewrite 3!HPlin; auto.
Qed.

Lemma Pon_mul_of_base {n} (P : Pauli -> AType 1) bit (Hbit : lt bit n) 
  (HPWF : forall p, proper_AType (P p))
  (HP : forall p q, 
    P (gMul_base p q) ≈ 
    gScaleA (/ gMul_Coef p q) (gMulA (P p) (P q)))
  : forall t t' : TType n,
    proper_TType t -> proper_TType t' ->
    gScaleA (fst (gMulT t t')) (@Pon n P bit (C1, snd (gMulT t t')))
    ≈ gMulA (gScaleA (fst t) (Pon P bit (C1, snd t)))
        (gScaleA (fst t') (Pon P bit (C1, snd t'))).
Proof.
  apply P_mul_of_base_linear.
  - intros t t' Ht Ht'.
    rewrite Aeq_gMulT_Pon by solve [hnf; assumption].
    reflexivity.
  - intros t.
    unfold Pon.
    rewrite gScaleA_merge, Cmult_1_r.
    cbn [fst snd].
    apply gScaleA_mor; [reflexivity|].
    apply TpadA_ext; reflexivity.
Qed.

Lemma TpadA_proper {n} bit (Hbit : lt bit n) (t : TType n) (a : AType 1) : 
  length (snd t) = n -> proper_AType a ->
  proper_AType (TpadA bit t a).
Proof.
  intros Ht Ha.
  unfold TpadA.
  destruct t as [c ps].
  cbn [snd] in *.
  replace (@proper_AType n) with (@proper_AType (bit + 1 + (n - (bit + 1))))
    by (f_equal; lia).
  apply gTensorA_proper; [|split_Forall; right; cbn; simpl_list; lia].
  apply gTensorA_proper; [split_Forall; right; cbn; simpl_list; lia|].
  auto.
Qed.


Lemma Alift_Pon_WF {n} (P : Pauli -> AType 1) bit (Hbit : lt bit n) 
  (HPWF : forall p, not_gI p -> WF_AType' (P p))
  (HPI : P gI = aI)
  (HP : forall p q, P (gMul_base p q) ≈ 
    gScaleA (/ gMul_Coef p q) (gMulA (P p) (P q))) : 
    forall a, WF_AType' a -> WF_AType' (Alift (@Pon n P bit) a).
Proof.
  apply Alift_WF.
  - intros ps Hps.
    unfold Pon.
    apply proper_AType_gScaleA.
    apply TpadA_proper; [auto..|].
    cbn.
    destruct (nth bit ps gI) eqn:Hnth; [|apply WF_AType'_proper, HPWF; WF_auto..].
    rewrite HPI.
    split_Forall.
    right; easy.
  - intros ps Hps.
    apply Pon_WF; auto.
  - apply Pon_mul_of_base; auto using WF_AType'_proper.
    intros []; [|apply WF_AType'_proper, HPWF; WF_auto..].
    rewrite HPI.
    split_Forall.
    right; easy.
Qed.



Lemma Aanticomm_iff_eq_minus {n} (a b : AType n) : 
  Aanticomm a b <-> gMulA a b ≈ gScaleA (-C1) (gMulA b a).
Proof.
  unfold Aanticomm.
  split.
  - intros Hplus.
    apply Aeq_of_Aminus_0.
    unfold Aminus.
    rewrite gScaleA_merge.
    replace (- C1 * - C1) with C1 by lca.
    rewrite gScaleA_1.
    assumption.
  - intros ->.
    rewrite Aeq_app_comm.
    apply Aminus_diag.
Qed.

Lemma anticommute_TType_Aanticomm {n} 
  (t t' : TType n) : 
  proper_TType t -> proper_TType t' -> 
  anticommute_TType t t' ->
  Aanticomm t t'.
Proof.
  unfold anticommute_TType.
  destruct t as [c ps], t' as [c' ps'].
  unfold proper_TType, Aanticomm.
  cbn.
  intros [->|Hps]; [intros; now rewrite 2 Aeq_zero' by lca|].
  intros [->|Hps']; [intros; now rewrite 2 Aeq_zero' by lca|].
  rewrite zipWith_gMul_base_symmetric by lia.
  intros ->.
  now rewrite Aeq_join, Aeq_zero' by lca.
Qed.

Lemma anticommute_TType_AType_Aanticomm {n} 
  (t : TType n) (a : AType n) : 
  proper_TType t -> proper_AType a ->
  anticommute_TType_AType t a ->
  Aanticomm t a.
Proof.
  unfold Aanticomm.
  intros Ht Ha Hanti.
  induction Ha; [now rewrite gMulA_nil_r|].
  cbn.
  rewrite Aeq_swap_heads.
  rewrite IHHa by (now destruct Hanti).
  cbn in Hanti.
  apply anticommute_TType_Aanticomm; now destruct Hanti.
Qed.

Lemma anticommute_AType_syntactic_Aanticomm {n} 
  (a b : AType n) : 
  proper_AType a -> proper_AType b -> 
  anticommute_AType_syntactic a b -> Aanticomm a b.
Proof.
  rewrite anticommute_AType_syntactic_iff_Forall.
  intros Haprop Hb Ha.
  unfold Aanticomm.
  induction Ha; [now rewrite gMulA_nil_r|].
  cbn [gMulA].
  rewrite (Aeq_gMulA_dist_app_r b [x] l).
  rewrite Aeq_swap'.
  apply Forall_cons_iff in Haprop.
  rewrite <- app_assoc, IHHa, app_nil_r by easy.
  rewrite Aeq_app_comm.
  pose proof (anticommute_TType_AType_Aanticomm x b) as Hen.
  unfold Aanticomm in Hen.
  cbn in Hen.
  unfold TtoA in Hen.
  rewrite app_nil_r in Hen.
  apply Hen; now destruct Haprop.
Qed.

Lemma WF_AType_WF_AType' {n} (a : AType n) : 
  WF_AType a -> WF_AType' a.
Proof.
  rename a into a'.
  intros [a Ha].
  induction Ha; [now constructor|].
  constructor; [auto..|].
  apply anticommute_AType_syntactic_Aanticomm; 
  auto using WF_AType'_proper.
Qed.



Lemma WF_TType_Tswitch {n} (t : TType n) p k : 
  not_gI p -> WF_TType t -> WF_TType (Tswitch t p k).
Proof.
  intros Hp Ht.
  constructor.
  - split; [apply Ht|].
    cbn.
    simpl_list; apply Ht.
  - apply Ht.
  - cbn.
    destruct Ht as [_ _ Ht].
    destruct t as [c ps].
    cbn in *.
    clear c.
    rewrite trace_zero_syntax_iff_Exists in *.
    revert k;
    induction Ht; intros k.
    + destruct k; now constructor.
    + destruct k; now constructor.
Qed.



Fixpoint prog_A {n} (p : prog) (a : AType n) : AType n :=
  match p with 
  | H i => H_A i a
  | S i => S_A i a
  | T i => T_A i a
  | CNOT ctrl targ => CNOT_A ctrl targ a
  | seq p p' => 
    prog_A p' (prog_A p a)
  end.



(* Need to prove this to proceed *)


#[export] 
Instance Aeq_atype_eq_subrelation {n} : subrelation (@Aeq n) atype_eq.
Proof.
  intros a a' Ha.
  induction Ha.
  - reflexivity.
  - unfold atype_eq.
    rewrite 2 translateA_alt.
    cbn.
    rewrite <- 2 translateA_alt.
    rewrite IHHa.
    reflexivity.
  - unfold atype_eq.
    rewrite 2 translateA_alt.
    cbn.
    lma.
  - unfold atype_eq.
    rewrite 2 translateA_alt.
    cbn.
    lma.
  - unfold atype_eq.
    rewrite 2 translateA_alt.
    cbn.
    lma.
  - now symmetry.
  - now etransitivity; eauto.
Qed.

Lemma translate_gScaleT' {n} (c : C) (t : TType n) : 
  translate (gScaleT c t) = c .* translate t.
Proof.
  destruct t as [d ps].
  cbn.
  unfold translate.
  cbn.
  lma.
Qed.

Lemma translateA_gScaleA' {n} (c : C) (A : AType n) : 
  translateA (gScaleA c A) = c .* translateA A.
Proof.
  rewrite 2 translateA_alt.
  unfold gScaleA.
  induction A.
  - cbn.
    lma.
  - cbn.
    rewrite IHA.
    rewrite translate_gScaleT'.
    lma.
Qed.

(* Lemma Eigenpair_scale_l_iff {n} (U : Square n) (v : Vector n) (c d : C) : 
  Eigenpair (c .* U) (v, d) <-> Eigenpair U (/c .* v, d).
Proof.
  unfold Eigenpair; cbn.

Lemma vecSatisfies_scale_r {n} (A : Square n) (v : Vector n) c : 
  vecSatisfies v (c .* A) <-> vecSatisfies  *)

Lemma WF_AType'_Aeq_proper_length {n} (a : AType n) : 
  WF_AType' a -> exists a', Aeq a a' /\ proper_length_AType_nil a'.
Proof.
  intros Ha.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa Ha' IHa' Hacomm].
  - exists t.
    split; [reflexivity|constructor; [|constructor]].
    apply Ht.
  - destruct IHHa as (a'' & Ha'' & Hlen).
    exists a''.
    split; [now rewrite <- Ha|assumption].
  - destruct IHa as (b & Hab & Hb), IHa' as (b' & Hab' & Hb').
    exists (gScaleA (C1 / √ 2) (b ++ b')).
    split.
    + now rewrite Hab, Hab'.
    + now apply proper_length_AType_nil_gScaleA, 
        proper_length_AType_nil_App.
Qed.

Add Parametric Morphism {n} : (@translateA n)
  with signature Aeq ==> eq as translateA_mor.
Proof.
  intros ? ? Happ%Aeq_atype_eq_subrelation; apply Happ.
Qed.

Lemma WF_Unitary_lincomb {n} (A B : Square n) c d : 
  WF_Unitary A -> WF_Unitary B -> 
  (* A † = A -> B † = B -> *)
  A † × B = -C1 .* (B † × A) ->  
  c ^* * c + d ^* * d = 1 ->
  d ^* * c = c ^* * d ->
  (* snd c = 0 -> snd d = 0 ->  *)
  WF_Unitary (c .* A .+ d .* B).
Proof.
  intros [HWFA HA] [HWFB HB] (* HAadj HBadj *) HAB Hcd Hcd' (* Hc hd *).
  split; [auto_wf|].
  rewrite Mplus_adjoint, 2 Mscale_adj.
  distribute_plus; distribute_scale.
  rewrite HA, HB, HAB.
  transitivity ((c ^* * c + d ^* * d) .* I n); 
  [|now rewrite Hcd, Mscale_1_l].
  rewrite Mscale_assoc, Hcd'.
  lma.
Qed.

Lemma translateA_gMulA' {n} (a b : AType n) : 
  proper_AType a -> proper_AType b ->
  translateA (gMulA a b) = 
  translateA a × translateA b.
Proof.
  intros Ha Hb.
  (* rewrite 3 translateA_alt. *)
  induction Ha; [cbn; now rewrite Mmult_0_l|].
  (* cbn. *)
  
  cbn -[translateA].
  rewrite translateA_app.
  simpl_rewrite (translateA_app [x] l).
  distribute_plus.
  rewrite IHHa.
  f_equal.
  clear Ha IHHa.
  induction Hb; [cbn; now rewrite Mmult_0_r|].
  cbn [map].
  etransitivity; 
  [apply (translateA_app [_] _)|].
  simpl_rewrite (translateA_app [x0] l0).
  distribute_plus.
  rewrite IHHb.
  f_equal.
  cbn.
  Msimpl.
  destruct x as [c ps], x0 as [d qs].
  clear IHHb.
  revert H H0.
  unfold proper_TType.
  cbn -[gMulT].
  intros [-> | Hps]; [cbn; intros; Csimpl; unfold translate;
    rewrite ?Mscale_0_l; symmetry; unfold Zero; apply Mmult_0_l|].
  intros [-> | Hqs]; [cbn; intros; Csimpl; unfold translate;
    rewrite ?Mscale_0_l; symmetry; unfold Zero; apply Mmult_0_r|].
  destruct n.
  - destruct ps; [|easy].
    destruct qs; [|easy].
    cbn.
    unfold translate.
    cbn.
    lma'.
  - apply translate_gMulT_mult; split; easy.
Qed.

Lemma Aanticomm_semantic {n} (a a' : AType n) : 
  proper_AType a -> proper_AType a' ->
  Aanticomm a a' -> 
  translateA a × translateA a' = 
  -C1.* (translateA a' × translateA a).
Proof.
  rewrite Aanticomm_iff_eq_minus.
  intros Ha Ha' Hsem%Aeq_atype_eq_subrelation.
  unfold atype_eq in Hsem.
  now rewrite translateA_gScaleA', 
    2 translateA_gMulA' in Hsem by auto.
Qed.


Lemma WF_AType'_UHT {n} (a : AType n) : 
  WF_AType' a -> 
  WF_Unitary (translateA a) /\ 
  (translateA a) † = translateA a /\
  trace (translateA a) = C0.
Proof.
  intros Ha.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa Ha' IHa' Hacomm].
  - split; [|split].
    + apply restricted_addition_semantic_implies_Unitary. 
      now constructor.
    + apply restricted_addition_semantic_implies_Hermitian.
      now constructor.
    + apply restricted_addition_semantic_implies_trace_zero.
      now constructor.
  - rewrite <- Ha.
    apply IHHa.
  - rewrite translateA_gScaleA', translateA_app.
    split; [|split].
    + restore_dims.
      rewrite Mscale_plus_distr_r.
      apply WF_Unitary_lincomb; [apply IHa | apply IHa' | 
        rewrite (proj1 (proj2 IHa)), 
          (proj1 (proj2 IHa')); apply Aanticomm_semantic;
          auto using WF_AType'_proper|..];
      rewrite <- RtoC_div, Cconj_R, RtoC_div; C_field; lca.
    + rewrite Mscale_adj, Mplus_adjoint.
      rewrite (proj1 (proj2 IHa)), (proj1 (proj2 IHa')).
      now rewrite <- RtoC_div, Cconj_R, RtoC_div.
    + rewrite trace_mult_dist, trace_plus_dist.
      rewrite (proj2 (proj2 IHa)), (proj2 (proj2 IHa')).
      lca.
Qed.


Lemma WF_AType'_Unitary {n} (a : AType n) : 
  WF_AType' a -> WF_Unitary (translateA a).
Proof.
  apply WF_AType'_UHT.
Qed.

Lemma WF_AType'_hermitian {n} (a : AType n) : 
  WF_AType' a -> (translateA a) † = translateA a.
Proof.
  apply WF_AType'_UHT.
Qed.

Lemma WF_AType'_trace_zero {n} (a : AType n) : 
  WF_AType' a -> trace (translateA a) = C0.
Proof.
  apply WF_AType'_UHT.
Qed.

Lemma Eigenvector_Heisenberg_semantics_WF_AType' {n : nat} 
  (a b : AType n) (g : prog) : 
  WF_AType' a -> WF_AType' b -> 
  {{a}} g {{b}} ->
  translate_prog n g × translateA a = translateA b × translate_prog n g.
Proof.
  intros Ha Hb Hgab.
  pose proof Ha as (a' & Haa' & Ha')%WF_AType'_Aeq_proper_length.
  pose proof Hb as (b' & Hbb' & Hb')%WF_AType'_Aeq_proper_length.
  rewrite Haa', Hbb' in Hgab.

  
  apply Eigenvector_Heisenberg_semantics in Hgab;
  [|assumption|assumption| rewrite <- 1?Haa', <- 1?Hbb';
    now apply WF_AType'_UHT..].
  rewrite Haa', Hbb'.
  assumption.
Qed.

Lemma SCALE' : forall {n : nat} (c : Coef) (a a' : AType n) (g : prog),
    WF_AType' a -> WF_AType' a' ->
    {{ AtoPred a }} g {{ AtoPred a' }} -> 
    {{ Predicates.scale c (AtoPred a) }} g {{ Predicates.scale c (AtoPred a') }}.
Proof. intros n c a a' g Ha Ha' Hgaa'.
  pose proof Ha as H0. 
  pose proof Ha' as H1.
  pose proof Hgaa' as H2.

  apply Heisenberg_Eigenvector_semantics.
  rewrite 2 translateA_gScaleA'.
  distribute_scale.
  f_equal.
  now apply Eigenvector_Heisenberg_semantics_WF_AType' in Hgaa'.
Qed.

Lemma UNFLIP' {n} (a a' a0 a0' : AType n) {g : prog} : 
  WF_AType' a -> WF_AType' a' -> 
  a0 = gScaleA (- C1) a -> a0' = gScaleA (- C1) a' -> 
  {{a}} g {{a'}} -> {{a0}} g {{a0'}}.
Proof.
  intros; subst.
  now apply SCALE'.
Qed.


Lemma SCALE'_pm_1 {n} (pre post : AType n) c p : 
  WF_AType' pre -> WF_AType' post ->
  c = C1 \/ c = -C1 -> 
  {{pre}} p {{post}} -> 
  {{AtoPred (gScaleA c pre)}} p {{AtoPred (gScaleA c post)}}.
Proof.
  intros Hpre Hpost [-> | ->].
  - rewrite 2 gScaleA_1.
    easy.
  - now apply UNFLIP'.
Qed.

Lemma TtoA_decomp {n} (t : TType n) : 
  TtoA t = gScaleA (fst t) (TtoA (C1, snd t)).
Proof.
  destruct t; cbn; now rewrite Cmult_1_r.
Qed.


Lemma ADD' : forall {n : nat} (a a' b b' : AType n) (g : prog),
    WF_AType' a -> WF_AType' a' -> WF_AType' b -> WF_AType' b' ->
    {{ AtoPred a }} g {{ AtoPred b }} -> {{ AtoPred a' }} g {{ AtoPred b' }} -> 
    {{ add (AtoPred a) (AtoPred a') }} g {{ add (AtoPred b) (AtoPred b') }}.
Proof. intros n a b a' b' g Ha Hb Ha' Hb' Haa' Hbb'. 
  apply Heisenberg_Eigenvector_semantics.
  unfold gAddA.
  rewrite 2 translateA_app.
  distribute_plus.
  f_equal.
  - now apply Eigenvector_Heisenberg_semantics_WF_AType' in Haa'.
  - now apply Eigenvector_Heisenberg_semantics_WF_AType' in Hbb'.
Qed.

Lemma LINCOMB_2_alt {n} (g : prog)
  (P P' Q Q' : AType n) : 
    WF_AType' P -> WF_AType' Q -> WF_AType' P' -> WF_AType' Q' -> 
    {{P}} g {{Q}} -> {{P'}} g {{Q'}} ->
  {{AtoPred (gScaleA (C1 / √ 2) (P ++ P'))}} g 
    {{AtoPred (gScaleA (C1 / √ 2) (Q ++ Q'))}}.
Proof.
  intros HP HQ HP' HQ' HPQ HPQ'.
  apply Heisenberg_Eigenvector_semantics.
  apply Eigenvector_Heisenberg_semantics_WF_AType' in HPQ; [|assumption..].
  apply Eigenvector_Heisenberg_semantics_WF_AType' in HPQ'; [|assumption..].
  rewrite 2 translateA_gScaleA', 2 translateA_app.
  distribute_scale; distribute_plus.
  now rewrite HPQ, HPQ'.
Qed.


Lemma Alift_correct {n} (P : TType n -> AType n) 
  (HWFA : forall (a : AType n), WF_AType' a -> WF_AType' (Alift P a))
  (g : prog) (HP : forall t, WF_TType t -> {{t}} g {{P t}}) :
  forall a, WF_AType' a -> {{a}} g {{Alift P a}}.
Proof.
  intros a Ha.
  induction Ha as [t Ht|a a' Ha HWF|a a' Ha IHa' Ha' IHa Hacomm].
  - cbn. 
    rewrite app_nil_r, (TtoA_decomp t).
    (* rewrite <- HPlin, <- TtoA_decomp; apply HP. *)
    
    apply SCALE'.
    + constructor.
      split; try apply Ht; now left.
    + specialize (HWFA (TtoA (C1, snd t))).
      cbn in HWFA.
      rewrite gScaleA_1, app_nil_r in HWFA.
      apply HWFA.
      constructor.
      split; try apply Ht; now left.
    + apply HP.
      split; try apply Ht; now left.
  - now rewrite <- Ha.
  - rewrite Alift_gScaleA_comm, Alift_app. 
    apply LINCOMB_2_alt; auto.
Qed.


Lemma S_P_proper p : proper_AType (S_P p).
Proof.
  destruct p; cbn; split_Forall; right; reflexivity.
Qed.

Lemma H_P_proper p : proper_AType (H_P p).
Proof.
  destruct p; cbn; split_Forall; right; reflexivity.
Qed.

Lemma T_P_proper p : proper_AType (T_P p).
Proof.
  destruct p; cbn; split_Forall; right; reflexivity.
Qed.

Lemma S_P_WF p : not_gI p -> WF_AType' (S_P p).
Proof.
  intros [-> | [-> | ->]]; cbn; constructor; WF_auto.
Qed.

Lemma H_P_WF p : not_gI p -> WF_AType' (H_P p).
Proof.
  intros [-> | [-> | ->]]; cbn; constructor; WF_auto.
Qed.

Lemma T_P_WF p : not_gI p -> WF_AType' (T_P p).
Proof.
  intros [-> | [-> | ->]]; cbn;
  apply WF_AType_WF_AType'; WF_auto.
  pose proof (@add_restrict_inductive_syntactic 1 (maX) aY) as 
    HWF.
  cbn in HWF.
  rewrite <- !Copp_mult_distr_r, !Copp_mult_distr_l,
    <- Copp_div_distr_l, 2Cmult_1_r in HWF.
  constructor.
  apply HWF; [constructor..|]; WF_auto.
Qed.

Lemma S_A_WF {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> WF_AType' (S_A bit a).
Proof.
  apply Alift_Pon_WF; [auto|..].
  - apply S_P_WF. 
  - reflexivity.
  - apply S_P_mult.
Qed.

Lemma H_A_WF {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> WF_AType' (H_A bit a).
Proof.
  apply Alift_Pon_WF; [auto|..].
  - apply H_P_WF.
  - reflexivity.
  - apply H_P_mult.
Qed.

Lemma T_A_WF {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> WF_AType' (T_A bit a).
Proof.
  apply Alift_Pon_WF; [auto|..].
  - apply T_P_WF. 
  - reflexivity.
  - apply T_P_mult.
Qed.

Lemma CNOT_P_proper {n} ctrl targ ps : 
  length ps = n -> proper_AType (@CNOT_P n ctrl targ (C1, ps)).
Proof.
  intros Hps.
  cbn.
  destruct (nth ctrl ps gI), (nth targ ps gI); split_Forall;
  right; cbn; 
  now rewrite ?switch_len.
Qed.

Lemma CNOT_P_WF {n} ctrl targ (Hctrl : lt ctrl n)
  (Htarg : lt targ n) (Hct : ctrl <> targ) ps : n <> O ->
  length ps = n -> trace_zero_syntax ps -> 
  WF_AType' (@CNOT_P n ctrl targ (C1, ps)).
Proof.
  intros Hn Hps Htr.
  assert (Hps' : @WF_TType n (C1, ps)) by WF_auto.
  cbn.
  destruct (nth ctrl ps gI) eqn:Hctrln, (nth targ ps gI) eqn:Htargn; 
    constructor;
  (repeat (apply WF_TType_Tswitch; [solve [WF_auto]|])); try assumption;
  (constructor; [split; [apply Hn|cbn; simpl_list; lia]|
    first[left; reflexivity|right; reflexivity]|..]); cbn;
  rewrite trace_zero_syntax_iff_Exists, Exists_nth;
  simpl_list; [
  first [exists ctrl, gI;
    rewrite 1?nth_switch_miss, 1?nth_switch_hit by lia;
    split; WF_auto | 
    exists targ, gI;
    rewrite 1?nth_switch_miss, 1?nth_switch_hit by lia;
    split; WF_auto].. | |].
  - exists targ, gI.
    rewrite nth_switch_miss, Htargn by lia.
    WF_auto.
  - exists targ, gI.
    rewrite nth_switch_miss, Htargn by lia.
    WF_auto.
Qed.

Lemma CNOT_A_WF {n} ctrl targ (Hctrl : lt ctrl n)
  (Htarg : lt targ n) (Hct : ctrl <> targ) : 
  forall (a : AType n), WF_AType' a -> WF_AType' (CNOT_A ctrl targ a).
Proof.
  apply Alift_WF.
  - intros ps Hps.
    now apply CNOT_P_proper.
  - intros; apply CNOT_P_WF; auto with zarith.
  - intros ? ?; now apply CNOT_P_mult.
Qed.

Lemma prog_A_WF {n} (p : prog) (Hp : prog_bound n p) :
  forall (a : AType n), WF_AType' a -> WF_AType' (prog_A p a).
Proof.
  induction Hp as [bit Hbit | bit Hbit | bit Hbit | ctrl targ
    Hctrl Htarg Hct | p1 p2 Hp1 Hp2].
  - now apply H_A_WF.
  - now apply S_A_WF.
  - now apply T_A_WF.
  - now apply CNOT_A_WF.
  - cbn; auto.
Qed.




Lemma S_P_Pon_correct {n} bit (Hbit : lt bit n) (t : TType n) : 
  WF_TType t -> 
  {{t}} S bit {{Pon S_P bit t}}.
Proof.
  intros Ht.
  unfold Pon.
  rewrite TpadA_switch by (apply Ht || 
    auto using S_P_proper).
  destruct t as [c ps].
  cbn.
  destruct Ht as [[Hn Hlen] Hcoef Htr].
  cbn in *.
  rewrite <- Hlen.
  unfold TtoA.
  destruct (nth bit ps gI) eqn:Hnth; cbn;
  [|apply TEN1; rewrite ?Hnth; WF_auto..].
  rewrite (switch_same _ _ _ gI), Cmult_1_r by assumption.
  apply TEN_ID; WF_auto.
Qed.

Lemma H_P_Pon_correct {n} bit (Hbit : lt bit n) (t : TType n) : 
  WF_TType t -> 
  {{t}} H bit {{Pon H_P bit t}}.
Proof.
  intros Ht.
  unfold Pon.
  rewrite TpadA_switch by (apply Ht || 
    auto using H_P_proper).
  destruct t as [c ps].
  cbn.
  destruct Ht as [[Hn Hlen] Hcoef Htr].
  cbn in *.
  rewrite <- Hlen.
  unfold TtoA.
  destruct (nth bit ps gI) eqn:Hnth; cbn;
  [|apply TEN1; rewrite ?Hnth; WF_auto..].
  rewrite (switch_same _ _ _ gI), Cmult_1_r by assumption.
  apply TEN_ID; WF_auto.
Qed.

Lemma T_P_Pon_correct {n} bit (Hbit : lt bit n) (t : TType n) : 
  WF_TType t -> 
  {{t}} T bit {{Pon T_P bit t}}.
Proof.
  intros Ht.
  unfold Pon.
  rewrite TpadA_switch by (apply Ht || 
    auto using T_P_proper).
  destruct t as [c ps].
  cbn.
  destruct Ht as [[Hn Hlen] Hcoef Htr].
  cbn in *.
  rewrite <- Hlen.
  unfold TtoA.
  destruct (nth bit ps gI) eqn:Hnth; cbn.
  - rewrite (switch_same _ _ _ gI), Cmult_1_r by assumption.
    apply TEN_ID; WF_auto.
  - rewrite (Cmult_comm c).
    rewrite <- (Cmult_1_r c) at 3.
    apply TEN3; rewrite 1?Hnth; WF_auto.
  - epose proof (Aeq_app_comm [_] [_]) as Hrw.
    cbn in Hrw.
    rewrite Hrw.
    clear Hrw.
    replace (c * (-C1 / √ 2)) with (C1 / √ 2 * (c * (-C1)))
      by lca.
    rewrite (Cmult_comm c).
    apply TEN3; rewrite 1?Hnth; WF_auto.
  - apply TEN1; rewrite 1?Hnth; WF_auto.
Qed.

Lemma CNOT_P_correct {n} ctrl targ (Hctrl : lt ctrl n)
  (Htarg : lt targ n) (Hct : ctrl <> targ) (t : TType n) : 
  WF_TType t -> {{t}} CNOT ctrl targ {{CNOT_P ctrl targ t}}.
Proof.
  destruct t as [c ps].
  intros [[Hn Hlen] Hc Htrace].
  rewrite CNOT_P_implements_computeHT by auto.
  cbn in *.
  destruct (nth ctrl ps gI) eqn:Hctrln, (nth targ ps gI) eqn:Htargn; cbn; Csimpl.
  3-7,9,10,12,15,16: solve [eapply (TEN2' C1 _ _ _ _); 
    try solve [symmetry; eassumption]; auto; WF_auto].
  3,4: solve [eapply (TEN2' (-C1) _ _ _ _); 
    try solve [symmetry; eassumption]; auto; WF_auto].
  - eapply TEN_ID2'; auto.
  - eapply (TEN2' C1 _ _  gI gX); 
    try solve [symmetry; eassumption]; WF_auto.
    rewrite 2 (switch_same _ _ _ gI); [auto..|].
    now rewrite nth_switch_miss.
  - eapply (TEN2' C1 _ _  gZ gI); 
    try solve [symmetry; eassumption]; WF_auto.
    rewrite 2 (switch_same _ _ _ gI); [auto..|].
    now rewrite nth_switch_miss.
  - eapply (TEN2' C1 _ _  gZ gX); 
    try solve [symmetry; eassumption]; WF_auto.
    rewrite 2 (switch_same _ _ _ gI); [auto..|].
    now rewrite nth_switch_miss.
Qed.

Lemma S_A_correct {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> {{a}} S bit {{S_A bit a}}.
Proof.
  apply Alift_correct.
  - now apply S_A_WF.
  - now apply S_P_Pon_correct.
Qed.

Lemma H_A_correct {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> {{a}} H bit {{H_A bit a}}.
Proof.
  apply Alift_correct.
  - now apply H_A_WF.
  - now apply H_P_Pon_correct.
Qed.

Lemma T_A_correct {n} bit (Hbit : lt bit n) (a : AType n) : 
  WF_AType' a -> {{a}} T bit {{T_A bit a}}.
Proof.
  apply Alift_correct.
  - now apply T_A_WF.
  - now apply T_P_Pon_correct.
Qed.

Lemma CNOT_A_correct {n} ctrl targ (Hctrl : lt ctrl n)
  (Htarg : lt targ n) (Hct : ctrl <> targ) (a : AType n) : 
  WF_AType' a -> {{a}} CNOT ctrl targ {{CNOT_A ctrl targ a}}.
Proof.
  apply Alift_correct.
  - now apply CNOT_A_WF.
  - now apply CNOT_P_correct.
Qed.

Lemma prog_A_correct {n : nat} (p : prog) (Hp : prog_bound n p) : 
  forall (a : AType n), WF_AType' a -> {{a}} p {{prog_A p a}}.
Proof.
  induction Hp.
  - now apply H_A_correct.
  - now apply S_A_correct.
  - now apply T_A_correct.
  - now apply CNOT_A_correct.
  - intros a Ha.
    cbn.
    eapply SEQ.
    + now apply IHHp1.
    + apply IHHp2.
      now apply prog_A_WF.
Qed.

Fixpoint WF_AdditivePredicate {n} (P : Predicate n) : Prop :=
  match P with 
  | AtoPred a => WF_AType' a 
  | Cap a_s => Forall WF_AType' a_s
  | Cup P Q => WF_AdditivePredicate P /\ WF_AdditivePredicate Q 
  | Sep _ => False
  | Err => True
  end.

Fixpoint compute_PC {n} (p : prog) (P : Predicate n) : Predicate n :=
  match P with
  | AtoPred a => AtoPred (prog_A p a)
  | Cap a_s => Cap (map (prog_A p) a_s)
  | Cup P Q => Cup (compute_PC p P) (compute_PC p Q)
  | Sep data => Sep data
  | Err => Err
  end.

Lemma compute_PC_correct {n} (p : prog) (P : Predicate n) : 
  prog_bound n p ->
  WF_AdditivePredicate P -> 
  {{P}} p {{compute_PC p P}}.
Proof.
  induction P.
  - intros Hp Ha.
    apply prog_A_correct; assumption.
  - cbn.
    intros Hp Has.
    apply CAP; [now simpl_list|].
    rewrite Forall_nth in *.
    intros i (d & d'). 
    simpl_list. 
    rewrite Nat.min_l by lia.
    intros Hi.
    rewrite combine_nth by now simpl_list.
    rewrite (map_nth_small d) by auto.
    cbn.
    apply prog_A_correct; auto.
  - easy.
  - cbn.
    intros ? [? ?].
    apply CUP; auto.
  - easy.
Qed.

Definition AtoQ {n} {qa : QAType n} (a : AType n)
  `{ParseAType' n qa a} : QAType n := qa.

Lemma AtoQ_correct {n} {qa : QAType n} (a : AType n)
  `{HP : ParseAType' n qa a} : 
  QAType_to_AType (AtoQ a) ≈ a.
Proof.
  apply HP.
Qed.

Definition S_PQ (p : Pauli) : QAType 1 :=
  match p with
  | gI => AtoQ aI
  | gX => AtoQ aY
  | gY => AtoQ maX
  | gZ => AtoQ aZ
  end.

Definition H_PQ (p : Pauli) : QAType 1 :=
  match p with
  | gI => AtoQ aI
  | gX => AtoQ aZ
  | gY => AtoQ maY
  | gZ => AtoQ aX
  end.

Definition T_PQ (p : Pauli) : QAType 1 :=
  match p with
  | gI => AtoQ aI
  | gX => AtoQ [(C1 / √ 2, [gX]); (C1 / √ 2, [gY])]
  | gY => AtoQ [(- C1 / √ 2, [gX]); (C1 / √ 2, [gY])]
  | gZ => AtoQ aZ
  end.

Definition QTswitch {n} (t : QTType n) (p : Pauli) (bit : nat) : QTType n :=
  (fst t, switch (snd t) p bit).

Definition QTopp {n} (t : QTType n) : QTType n :=
  (Some (QCopp (maybe (fst t) 1%Q)), snd t).

(* #[export]
Instance parseAT'_Tswitch {n} {t : TType} *)

Definition CNOT_PQ {n} (ctrl targ : nat) (t : QTType n) : QAType n :=
  let l := snd t in 
  match nth ctrl l gI with 
  | gI => 
    match nth targ l gI with 
    | gY | gZ => [QTswitch t gZ ctrl]
    | _ => [t]
    end
  | gX => 
    match nth targ l gI with 
    | gI => [QTswitch (QTswitch t gX ctrl) gX targ]
    | gX => [QTswitch (QTswitch t gX ctrl) gI targ]
    | gY => [QTswitch (QTswitch t gY ctrl) gZ targ]
    | gZ => [QTopp (QTswitch (QTswitch t gY ctrl) gY targ)]
    end
  | gY => 
    match nth targ l gI with 
    | gI => [QTswitch (QTswitch t gY ctrl) gX targ]
    | gX => [QTswitch (QTswitch t gY ctrl) gI targ]
    | gY => [QTopp (QTswitch (QTswitch t gX ctrl) gZ targ)]
    | gZ => [QTswitch (QTswitch t gX ctrl) gY targ]
    end
  | gZ => 
    match nth targ l gI with 
    | gY | gZ => [QTswitch t gI ctrl]
    | _ => [t]
    end
  end.

Arguments CNOT_PQ {_} _ _ !_ /.

Definition gTensorQT {n m} (t : QTType n) (t' : QTType m) : QTType (n + m) :=
  (oQC_mult (fst t) (fst t'), snd t ++ snd t').

Fixpoint gTensorQA {n m} (a : QAType n) (b : QAType m) : QAType (n + m) :=
  match a with 
  | [] => []
  | t :: a => 
    map (gTensorQT t) b ++
    gTensorQA a b
  end.


Definition QTpadA {n} (bit : nat) (t : QTType n) (a : QAType 1) : QAType n :=
  let '(_, ps) := t in 
  @gTensorQA (bit + 1) (n - (bit + 1)) (
    @gTensorQA bit 1 [(None, firstn bit ps)] a)
    [(None, skipn (bit + 1) ps)].

Definition QPon {n} (P : Pauli -> QAType 1) bit (t : QTType n) : QAType n :=
  QA_scale (maybe (fst t) 1%Q) (QTpadA bit t (P (nth bit (snd t) gI))).

Fixpoint QAlift {n} (P : QTType n -> QAType n) (a : QAType n) : QAType n :=
  match a with 
  | [] => []
  | t :: a => 
    QA_plus (QA_reduce (QA_scale (maybe (fst t) 1%Q) (P (None, snd t))))
    (QAlift P a)
  end.



Definition S_AQ {n} bit (a : QAType n) : QAType n :=
  QAlift (QPon S_PQ bit) a.

Definition H_AQ {n} bit (a : QAType n) : QAType n :=
  QAlift (QPon H_PQ bit) a.

Definition T_AQ {n} bit (a : QAType n) : QAType n :=
  QAlift (QPon T_PQ bit) a.

Definition CNOT_AQ {n} ctrl targ (a : QAType n) : QAType n :=
  QAlift (CNOT_PQ ctrl targ) a.

Fixpoint prog_AQ {n} (p : prog) (a : QAType n) : QAType n :=
  match p with 
  | H i => H_AQ i a
  | S i => S_AQ i a
  | T i => T_AQ i a
  | CNOT ctrl targ => CNOT_AQ ctrl targ a
  | seq p q => prog_AQ q (prog_AQ p a)
  end.

#[local]
Instance parse_AT'_S_P p : ParseAType' (S_PQ p) (S_P p).
Proof.
  destruct p; apply _.
Qed.

#[local]
Instance parse_AT'_H_P p : ParseAType' (H_PQ p) (H_P p).
Proof.
  destruct p; apply _.
Qed.

#[local]
Instance parse_AT'_T_P p : ParseAType' (T_PQ p) (T_P p).
Proof.
  destruct p; apply _.
Qed.

#[local]
Instance parse_AT'_gTensorA {n m} (a : AType n) (b : AType m) 
  (qa : QAType n) (qb : QAType m) : 
  ParseAType' qa a -> ParseAType' qb b ->
  ParseAType' (gTensorQA qa qb) (gTensorA a b).
Proof.
  intros [Ha] [Hb].
  constructor.
  rewrite <- Ha, <- Hb.
  clear a b Ha Hb.
  unfold QAType_to_AType.
  induction qa; [reflexivity|].
  cbn.
  rewrite map_app.
  rewrite IHqa.
  f_equiv.
  clear IHqa.
  induction qb; [reflexivity|].
  cbn.
  rewrite IHqb.
  f_equiv.
  rewrite (surjective_pairing (QTType_to_TType a)), 
    (surjective_pairing (QTType_to_TType a0)); cbn.
  rewrite oQC_mult_correct.
  reflexivity.
Qed.

#[export]
Instance parseAT'_cons_none {n} ps (qs : QAType n) ts : 
  ParseAType' qs ts ->
  @ParseAType' n ((None, ps) :: qs) ((C1, ps) :: ts).
Proof.
  intros [Hqs].
  constructor.
  cbn.
  rewrite Hqs.
  f_equiv.
  f_equal.
  lca.
Qed.

#[export]
Instance parseAT'_cons' {n} qc c ps (qs : QAType n) ts : 
  ParseQC (maybe qc (mkQC 1 0 0 0)) c ->
  ParseAType' qs ts ->
  @ParseAType' n ((qc, ps) :: qs) ((c, ps) :: ts).
Proof.
  destruct qc; cbn; [apply _|].
  intros [<-].
  change (mkQC 1 0 0 0) with (Q2QC 1).
  rewrite Q2QC_correct.
  replace (Q2R 1) with (1%R) by lra.
  apply _.
Qed.

Lemma QAType_to_AType_dim_indep {n n'} (qa : QAType n) : 
  @QAType_to_AType n qa = @QAType_to_AType n' qa.
Proof.
  reflexivity.
Qed.

Lemma parse_AT'_indep {n n'} (qa : QAType n) (a : AType n) : 
  @ParseAType' n' qa a -> 
  ParseAType' qa a.
Proof.
  intros [Hqa].
  apply (Aeq_dim_indep n n') in Hqa.
  constructor.
  apply Hqa.
Qed.

#[local]
Instance parse_AT'_Pon {n} (P : Pauli -> AType 1) (QP : Pauli -> QAType 1) bit
  qc c ps :
    (forall q, ParseAType' (QP q) (P q)) ->
    ParseQC qc c ->
  @ParseAType' n (QPon QP bit (Some qc, ps)) (Pon P bit (c, ps)).
Proof.
  intros HQP Hqc.
  constructor.
  unfold QPon, Pon.
  apply parseAT'_scale; [apply _|].
  eapply parse_AT'_indep.
  cbn -[gTensorA gTensorQA].
  apply _.
Qed.

#[local]
Instance parse_AT'_Pon' {n} (P : Pauli -> AType 1) (QP : Pauli -> QAType 1) bit
  qc c ps :
    (forall q, ParseAType' (QP q) (P q)) ->
    ParseQC (maybe qc (mkQC 1 0 0 0)) c ->
  @ParseAType' n (QPon QP bit (qc, ps)) (Pon P bit (c, ps)).
Proof.
  destruct qc.
  - apply _.
  - intros HQP Hc.
    cbn in Hc.
    constructor.
    unfold QPon.
    cbn [maybe fst snd].
    apply parse_AT'_Pon; apply _.
Qed.

Lemma QAType_to_AType_defn {n} (qa : QAType n) : 
  QAType_to_AType qa = map QTType_to_TType qa.
Proof.
  reflexivity.
Qed.

#[local]
Instance parse_AT'_QAlift {n} 
  (P : TType n -> AType n) (QP : QTType n -> QAType n) qa a :
    (forall qc c ps, ParseQC (maybe qc (mkQC 1 0 0 0)) c -> ParseAType' (QP (qc, ps)) (P (c, ps))) ->
    ParseAType' qa a ->
  @ParseAType' n (QAlift QP qa) (Alift P a).
Proof.
  intros HQP [Hqa].
  constructor.
  rewrite <- Hqa.
  clear a Hqa.
  induction qa; [reflexivity|].
  cbn.
  rewrite <- QAType_to_AType_defn.
  rewrite QA_plus_correct'.
  rewrite IHqa. f_equiv.
  rewrite QA_reduce_correct'.
  destruct a; cbn.
  apply parseAT'_scale; [now constructor|].
  apply HQP.
  constructor.
  lca.
Qed.

#[local] 
Instance parse_AT'_CNOT_P {n} ctrl targ 
  qc c ps : 
  ParseQC (maybe qc (mkQC 1 0 0 0)) c ->
  ParseAType' (@CNOT_PQ n ctrl targ (qc, ps)) (CNOT_P ctrl targ (c, ps)).
Proof.
  intros Hc.
  constructor.
  unfold CNOT_PQ, CNOT_P.
  cbn [fst snd].
  destruct (nth ctrl ps gI), (nth targ ps gI); apply parseatype'.
Qed.

(* #[local] 
Instance parse_AT'_CNOT_A {n} ctrl targ 
  qc c ps : 
  ParseQC (maybe qc (mkQC 1 0 0 0)) c ->
  ParseAType' (@CNOT_PQ n ctrl targ (qc, ps)) (CNOT_P ctrl targ (c, ps)).
Proof.
  intros Hc.
  constructor.
  unfold CNOT_PQ, CNOT_P.
  cbn [fst snd].
  destruct (nth ctrl ps gI), (nth targ ps gI); apply parseatype'.
Qed. *)

#[export]
Instance parse_AT'_prog_A {n} (p : prog) (qa : QAType n) (a : AType n) : 
  ParseAType' qa a ->
  ParseAType' (prog_AQ p qa) (prog_A p a).
Proof.
  revert qa a.
  induction p; cbn; apply _.
Qed.


Lemma pred_eq_Cap {n} (l l' : list (AType n)) : 
  Forall2 atype_eq l l' -> pred_eq (Cap l) (Cap l').
Proof.
  unfold pred_eq.
  cbn.
  intros Hll' v.
  enough (Hen : Forall (fun a => vecSatisfies v (translateA a)) l <-> 
    Forall (fun a => vecSatisfies v (translateA a)) l') by now rewrite Hen.
  induction Hll' as [| a a' l l' Ha].
  - split; constructor.
  - rewrite 2 Forall_cons_iff, IHHll'.
    now rewrite Ha.
Qed.

Lemma pred_eq_Cup {n} (P P' Q Q' : Predicate n) : 
  pred_eq P P' -> pred_eq Q Q' -> pred_eq (Cup P Q) (Cup P' Q').
Proof.
  unfold pred_eq.
  cbn.
  intros HP HQ v.
  now rewrite HP, HQ.
Qed.

Lemma pred_eq_AType {n} (a a' : AType n) : 
  atype_eq a a' -> pred_eq a a'.
Proof.
  now intros ->.
Qed.

Lemma prep_validate_refl_lemma {n} (P Q Q' : Predicate n) p : 
  {{P}} p {{Q'}} -> pred_eq Q' Q -> {{P}} p {{Q}}.
Proof.
  now intros ? <-.
Qed.

(* Splits a goal [Forall2 P l l'] according to the structure of [l]. 
  In particular, if [l] is concrete and [l'] is an evar, [l'] will be 
  filled with evars to match the length of [l] *)
Ltac split_forall2 := match goal with 
  | |- Forall2 _ (cons _ _) _ => apply Forall2_cons; [|split_forall2]
  | |- Forall2 _ nil _ => apply Forall2_nil
  | _ => idtac
  end.

(* Splits a goal [Forall2 P l l'] according to the structure of [l']. 
  In particular, if [l'] is concrete and [l] is an evar, [l] will be 
  filled with evars to match the length of [l'] *)
Ltac split_forall2_r := match goal with 
  | |- Forall2 _ _ (cons _ _) => apply Forall2_cons; [|split_forall2_r]
  | |- Forall2 _ _ nil => apply Forall2_nil
  | _ => idtac
  end.

Inductive QPredicate n :=
  | QAtoPred (qa : QAType n) : QPredicate n
  | QCap (qas : list (QAType n)) : QPredicate n
  | QSep : list nat * list (list TTypes) * list nat -> QPredicate n
  | QCup (P Q : QPredicate n) : QPredicate n
  | QErr : QPredicate n.

Arguments QAtoPred {_} _ : assert.
Arguments QCap {_} _ : assert.
Arguments QSep {_} _ : assert.
Arguments QCup {_} _ _ : assert.
Arguments QErr {_} : assert.

Fixpoint translateQP {n} (qp : QPredicate n) : Predicate n :=
  match qp with 
  | QAtoPred qa => AtoPred (QAType_to_AType qa)
  | QCap qas => Cap (map QAType_to_AType qas)
  | QSep ls => Sep ls
  | QCup P Q => Cup (translateQP P) (translateQP Q)
  | QErr => Err
  end.

Definition QAType_to_AType_simpl {n} (qa : QAType n) : AType n :=  
  QAType_to_AType' (QA_reduce (QA_plus qa [])).



Lemma QTType_to_TType'_correct' {n} (qt : QTType n) : 
  QTType_to_TType' qt = QTType_to_TType qt.
Proof.
  unfold QTType_to_TType, QTType_to_TType'.
  f_equal.
  now rewrite QC2C'_correct.
Qed.

Lemma QAType_to_AType'_correct' {n} (qa : QAType n) : 
  QAType_to_AType' qa = QAType_to_AType qa.
Proof.
  apply map_ext, QTType_to_TType'_correct'.
Qed.

Lemma QAType_to_AType_simpl_correct {n} (qa : QAType n) : 
  QAType_to_AType_simpl qa ≈ QAType_to_AType qa.
Proof.
  unfold QAType_to_AType_simpl.
  rewrite QAType_to_AType'_correct', QA_reduce_correct', QA_plus_correct'.
  now rewrite app_nil_r.
Qed.

Fixpoint translateQP' {n} (qp : QPredicate n) : Predicate n :=
  match qp with 
  | QAtoPred qa => AtoPred (QAType_to_AType_simpl qa)
  | QCap qas => Cap (map QAType_to_AType_simpl qas)
  | QSep ls => Sep ls
  | QCup P Q => Cup (translateQP' P) (translateQP' Q)
  | QErr => Err
  end.

Inductive pred_eq_struct {n} : relation (Predicate n) :=
  | pes_A (a b : AType n) (Hab : a ≈ b) : pred_eq_struct a b
  | pes_Cap (a_s b_s : list (AType n)) (Hab_s : Forall2 Aeq a_s b_s)
    : pred_eq_struct (Cap a_s) (Cap b_s)
  | pes_Sep l : pred_eq_struct (Sep l) (Sep l)
  | pes_Cup (P P' Q Q' : Predicate n) : 
    pred_eq_struct P P' -> pred_eq_struct Q Q' ->
    pred_eq_struct (Cup P Q) (Cup P' Q')
  | pes_Err : @pred_eq_struct n Err Err.

Lemma translateQP'_correct {n} (qp : QPredicate n) : 
  pred_eq_struct (translateQP' qp) (translateQP qp).
Proof.
  induction qp; cbn; constructor; [| |auto..].
  - apply QAType_to_AType_simpl_correct.
  - induction qas; constructor; [|auto].
    apply QAType_to_AType_simpl_correct.
Qed.

#[export]
Instance pred_eq_struct_subrelation {n} : subrelation (@pred_eq_struct n) pred_eq.
Proof.
  intros P Q HPQ.
  induction HPQ.
  - now rewrite Hab.
  - apply pred_eq_Cap.
    revert Hab_s.
    apply Forall2_impl.
    now intros ? ? ->.
  - reflexivity.
  - now apply pred_eq_Cup.
  - reflexivity.
Qed.

Class ParseQPred {n} (qp : QPredicate n) (p : Predicate n) := {
  parseqpred : pred_eq_struct (translateQP qp) p
}.

Global Hint Mode ParseQPred - - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance parseQP_A {n} qa (a : AType n) : 
  ParseAType' qa a -> ParseQPred (QAtoPred qa) (AtoPred a).
Proof.
  intros [Hqa].
  constructor.
  cbn.
  constructor.
  now rewrite Hqa.
Qed.

Lemma Forall2_map_l {A B C} (P : B -> C -> Prop) (f : A -> B) l l' : 
  Forall2 P (map f l) l' <-> Forall2 (fun a b => P (f a) b) l l'.
Proof.
  split; (
  revert l'; induction l; intros [|a' l']; 
  [constructor|intros Hall; inversion Hall..|
    cbn]);
  rewrite ?Forall2_cons_iff; intros [? ?%IHl]; 
  split; assumption.
Qed.


Lemma Forall2_map_r {A B C} (P : A -> C -> Prop) (f : B -> C) l l' : 
  Forall2 P l (map f l') <-> Forall2 (fun a b => P a (f b)) l l'.
Proof.
  split; intros Hen%Forall2_flip; apply Forall2_flip; 
    now rewrite Forall2_map_l in *.
Qed.

#[export]
Instance parseQP_Cap {n} qa_s (a_s : list (AType n)) :
  Forall2 ParseAType' qa_s a_s -> ParseQPred (QCap qa_s) (Cap a_s).
Proof.
  intros Hall.
  constructor.
  constructor.
  revert Hall.
  rewrite Forall2_map_l.
  apply Forall2_impl.
  now intros ? ? [].
Qed.

#[export] 
Hint Extern 0 (Forall2 ParseAType' _ _) => split_forall2_r : typeclass_instances.

#[export]
Instance parseQP_Cup {n} (qP qQ : QPredicate n) (P Q : Predicate n) : 
  ParseQPred qP P -> ParseQPred qQ Q ->
  ParseQPred (QCup qP qQ) (Cup P Q).
Proof.
  intros [HP] [HQ].
  constructor.
  cbn.
  now constructor.
Qed.

#[export]
Instance parseQP_Sep {n} l : 
  @ParseQPred n (QSep l) (Sep l).
Proof.
  constructor.
  constructor.
Qed.

#[export]
Instance parseQP_Err {n} : 
  @ParseQPred n QErr Err.
Proof.
  constructor.
  constructor.
Qed.


Unset Typeclasses Unique Instances.


Fixpoint compute_PCQ {n} (p : prog) (P : QPredicate n) : QPredicate n :=
  match P with
  | QAtoPred a => QAtoPred (prog_AQ p a)
  | QCap a_s => QCap (map (prog_AQ p) a_s)
  | QCup P Q => QCup (compute_PCQ p P) (compute_PCQ p Q)
  | QSep data => QSep data
  | QErr => QErr
  end.


#[export]
Instance parse_QP_compute_PCQ {n} (QP : QPredicate n) P p : 
  ParseQPred QP P -> 
  ParseQPred (compute_PCQ p QP) (compute_PC p P).
Proof.
  intros [HQP].
  remember (translateQP QP) as tQP.
  constructor.
  revert QP HeqtQP;
  induction HQP; intros QP HeqtQP; (destruct QP; try easy).
  - cbn.
    constructor.
    apply parse_AT'_prog_A.
    cbn in HeqtQP.
    constructor. 
    injection HeqtQP.
    now intros <-.
  - constructor.
    cbn.
    cbn in HeqtQP.
    rewrite Forall2_map_l, Forall2_map_r.
    injection HeqtQP.
    intros ->.
    rewrite ?Forall2_map_l in *.
    revert Hab_s.
    apply Forall2_impl.
    intros a b ?.
    apply parse_AT'_prog_A.
    now constructor.
  - cbn in *.
    injection HeqtQP.
    intros <-.
    now constructor.
  - cbn.
    cbn in HeqtQP.
    injection HeqtQP.
    intros.
    constructor; auto.
  - constructor.
Qed.



Local Open Scope nat_scope.

Fixpoint is_prog_bound n (p : prog) : bool :=
  match p with 
  | H i => i <? n
  | S i => i <? n
  | T i => i <? n
  | CNOT ctrl targ => (ctrl <? n) && (targ <? n) && ¬ (ctrl =? targ)
  | seq p q => is_prog_bound n p && is_prog_bound n q
  end.

Lemma is_prog_bound_correct n p : 
  is_prog_bound n p = true -> prog_bound n p.
Proof.
  induction p; cbn -[Nat.ltb];
  rewrite ?andb_true_iff, ?negb_true_iff, 
    ?Nat.ltb_lt, ?Nat.eqb_eq, ?Nat.eqb_neq; 
    solve [constructor; easy |
    intros []; constructor; auto].
Qed.

Lemma prep_solve_placeholder_refl_lemma
  {n : nat} (P Q : Predicate n) (qP : QPredicate n) 
  `{ParseQPred n qP P} (p : prog) : 
  is_prog_bound n p = true ->
  WF_AdditivePredicate P -> (* TODO: Make reflexive *)
  translateQP' (compute_PCQ p qP) = Q ->
  {{P}} p {{Q}}.
Proof.
  intros Hp%is_prog_bound_correct HP HQ.
  eapply prep_validate_refl_lemma.
  - now apply compute_PC_correct.
  - subst Q.
    symmetry.
    rewrite translateQP'_correct.
    apply pred_eq_struct_subrelation.
    apply parseqpred.
Qed.

Lemma AType_Aeq_simplify_lemma {n} (qa : QAType n) (a : AType n) : 
  ParseAType' qa a -> 
  a ≈ QAType_to_AType' (QA_reduce (QA_plus qa [])).
Proof.
  intros [Hqa].
  rewrite QAType_to_AType'_correct', 
    QA_reduce_correct', QA_plus_correct', Hqa, app_nil_r.
  reflexivity.
Qed.

(* Lemma validate_prep_lemma {n} (P ts ts') *)

(* Fixpoint is_WF_AdditivePredicate  *)

(* Lemma solve_validate_lemma  *)

Ltac refl_validate := 
  erewrite prep_validate_lemma;
  [match goal with 
  |- {{?P}} ?p {{_}} =>
    apply (compute_PC_correct p P); 
    [apply is_prog_bound_correct; reflexivity|
    repeat first [split | split_Forall]; 
    apply WF_AType_WF_AType'; WF_auto]
  end|];
  validate_red;
  Csimpl; try reflexivity.

(* Ltac validate_refl := 
  rewrite prep_validate_lemma;
  [match goal with
  | |- {{?P}} ?p {{_}} =>
          apply (compute_PC_correct p P);
          [ apply is_prog_bound_correct; reflexivity
          | repeat (first [ split | split_Forall ]);
              apply WF_AType_WF_AType'; WF_auto ]
  end|];
  apply Aeq_atype_eq_subrelation;
  apply (AType_Aeq_reflexive_solve_lemma _ _ _ _ _ _);
  vm_compute; reflexivity. *)


Lemma prep_validate_refl_lemma'
  {n : nat} (P Q : Predicate n) (qP : QPredicate n) 
  `{ParseQPred n qP P} (p : prog) : 
  is_prog_bound n p = true ->
  WF_AdditivePredicate P -> (* TODO: Make reflexive *)
  pred_eq (translateQP' (compute_PCQ p qP)) Q ->
  {{P}} p {{Q}}.
Proof.
  intros Hp%is_prog_bound_correct HP HQ.
  eapply prep_validate_refl_lemma.
  - now apply compute_PC_correct.
  - rewrite <- HQ.
    symmetry.
    rewrite translateQP'_correct.
    apply pred_eq_struct_subrelation.
    apply parseqpred.
Qed.

Global Typeclasses Opaque QAType_to_AType.

#[export] 
Instance parse_AT'_translate {n} (qa : QAType n) : 
  ParseAType' qa (QAType_to_AType qa).
Proof.
  constructor; reflexivity.
Qed.

#[export] 
Instance parse_AT'_translate' {n} (qa : QAType n) : 
  ParseAType' qa (QAType_to_AType' qa).
Proof.
  constructor; rewrite QAType_to_AType'_correct'; reflexivity.
Qed.

#[export] 
Instance parse_AT'_translate_simpl {n} (qa : QAType n) : 
  ParseAType' qa (QAType_to_AType_simpl qa).
Proof.
  constructor; rewrite QAType_to_AType_simpl_correct; reflexivity.
Qed.

Ltac split_pred_eq :=
  lazymatch goal with 
  | |- pred_eq (Cap _) (Cap _) => apply pred_eq_Cap; 
      split_forall2_r; split_forall2
  | |- pred_eq (Cup _ _) (Cup _ _) => apply pred_eq_Cup; split_pred_eq
  | |- pred_eq (AtoPred _) (AtoPred _) => apply pred_eq_AType
  | |- pred_eq (Sep _) (Sep _) => 
    reflexivity || 
    lazymatch goal with |- ?G => 
      fail 1 "Couldn't solve Sep equivalence in split_pred_eq! Goal: " G
    end
  | |- pred_eq Err Err => reflexivity
  | |- pred_eq ?LHS ?RHS => 
    is_evar RHS; 
    lazymatch LHS with 
    | Cap _ => apply pred_eq_Cap; 
      split_forall2_r; split_forall2
    | Cup _ _ => 
      apply pred_eq_Cup; split_pred_eq
    | AtoPred _ => apply pred_eq_AType
    | Sep _ => reflexivity
    | Err => reflexivity
    end
  | |- ?G => fail 1 "Unrecognized / unsolvable condition in split_pred_eq! Goal: " G
  end.


Fixpoint is_WF_AdditivePredicate {n} (P : QPredicate n) : bool :=
  match P with 
  | QAtoPred a => is_WF_QAType (length a) a
  | QCap a_s => forallb (is_WF_QAType (list_max (map (@length _) a_s))) a_s
  | QSep _ => false
  | QCup P Q => is_WF_AdditivePredicate P && is_WF_AdditivePredicate Q
  | QErr => true
  end.

Lemma is_WF_AdditivePredicate_correct {n} (QP : QPredicate n) : 
  is_WF_AdditivePredicate QP = true -> 
  WF_AdditivePredicate (translateQP QP).
Proof.
  induction QP; cbn.
  - now intros ?%is_WF_QAType_correct%WF_AType_WF_AType'.
  - rewrite forallb_forall, Forall_map, Forall_forall.
    now intros Hall q Hq%Hall%is_WF_QAType_correct%WF_AType_WF_AType'.
  - easy.
  - rewrite andb_true_iff. intros []; auto.
  - easy.
Qed.

Fixpoint ProperAdditivePredicate {n} (P : Predicate n) : Prop :=
  match P with
  | AtoPred a => proper_AType a
  | Cap a_s => Forall proper_AType a_s
  | Sep _ => False
  | Cup P Q => ProperAdditivePredicate P /\ ProperAdditivePredicate Q
  | Err => True
  end.

Definition is_properAType_len {n} (a : AType n) : bool :=
  forallb (fun t => length (snd t) =? n)%nat a.

Lemma is_properAType_len_correct {n} (a : AType n) : 
  is_properAType_len a = true -> proper_AType a.
Proof.
  unfold is_properAType_len, proper_AType.
  rewrite forallb_forall, Forall_forall.
  intros Hall t Ht%Hall%Nat.eqb_eq; now right.
Qed.

(* NB : This is an underapproximation, and only allows ATypes all of 
  whose TTypes have the right length (disallowing those with incorrect
  length but coefficient 0). *)
Fixpoint is_ProperAdditivePredicate {n} (P : Predicate n) : bool :=
  match P with 
  | AtoPred a => is_properAType_len a
  | Cap a_s => forallb is_properAType_len a_s
  | Sep _ => false
  | Cup P Q => is_ProperAdditivePredicate P && is_ProperAdditivePredicate Q
  | Err => true
  end.

Lemma is_ProperAdditivePredicate_correct {n} (P : Predicate n) : 
  is_ProperAdditivePredicate P = true -> ProperAdditivePredicate P.
Proof.
  induction P; cbn.
  - apply is_properAType_len_correct.
  - rewrite forallb_forall, <- Forall_forall.
    apply Forall_impl.
    apply is_properAType_len_correct.
  - easy.
  - rewrite andb_true_iff.
    intuition fail.
  - easy.
Qed.

(* Lemma Forall_Forall2 {A}  *)

Lemma Forall_impl_l {A} {P Q : A -> Prop} l : 
  Forall (fun a => P a -> Q a) l -> Forall P l -> Forall Q l.
Proof.
  induction l; [constructor|].
  rewrite ?Forall_cons_iff.
  intuition fail.
Qed.

Lemma Forall2_impl_l {A B} {P : A -> Prop} {Q : B -> Prop} l l' : 
  Forall2 (fun a b => P a -> Q b) l l' -> Forall P l -> Forall Q l'.
Proof.
  intros Hall.
  induction Hall; [constructor|].
  rewrite ?Forall_cons_iff.
  intuition fail.
Qed.


Lemma WF_AdditivePredicate_pred_eq_struct {n} (P Q : Predicate n) : 
  pred_eq_struct P Q -> ProperAdditivePredicate Q -> 
  WF_AdditivePredicate P -> WF_AdditivePredicate Q.
Proof.
  intros HPQ.
  induction HPQ; cbn.
  - econstructor; eauto.
  - intros Hb Ha.
    revert Hb.
    apply Forall_impl_l.
    revert Ha.
    apply Forall2_impl_l.
    revert Hab_s.
    apply Forall2_impl.
    econstructor; eauto.
  - easy.
  - intuition fail.
  - easy.
Qed.

Lemma prep_validate_refl_lemma'' {n} {P Q : Predicate n} {qP} 
  `{ParseQPred n qP P} {p} : is_prog_bound n p = true -> 
  is_ProperAdditivePredicate P = true -> 
  is_WF_AdditivePredicate qP = true -> 
  pred_eq (translateQP' (compute_PCQ p qP)) Q -> 
  {{P}} p {{Q}}.
Proof.
  intros Hp HP HPWF.
  apply prep_validate_refl_lemma'.
  - apply _.
  - auto.
  - apply is_WF_AdditivePredicate_correct in HPWF.
    revert HPWF.
    apply WF_AdditivePredicate_pred_eq_struct.
    + apply parseqpred.
    + now apply is_ProperAdditivePredicate_correct.
Qed.


Ltac validate_refl :=
  apply prep_validate_refl_lemma'';
  [lazy; reflexivity..|];
  cbn [compute_PCQ translateQP' map];
  split_pred_eq; 
  (apply Aeq_atype_eq_subrelation;
  apply (AType_Aeq_reflexive_solve_lemma _ _ _ _ _ _);
  [vm_compute; reflexivity]).

Ltac solvePlaceholder_refl_internal := 
  apply prep_validate_refl_lemma'';
  [lazy; reflexivity..|];
  validate_red; reflexivity.

Ltac solvePlaceholder_refl := 
  let G := fresh "G" in 
  eexists;
  match goal with 
  |- ?g => assert (G : g);
    [solvePlaceholder_refl_internal|]
  end.

(* TODO: Integrate reflexive WF_AType test *)

Ltac validateCapImpliesSep' :=
  repeat
  match goal with
  | |- _ ⇒ (∩ _)%P =>
      validate_red; Csimpl; eapply CaptoSep; validate_red; Csimpl; auto;
          repeat (constructor; try split; intros; try lia; auto)
  | |- Permutation _ _ =>
        try
          (apply Permutation_sym; apply sort_seq_Permutation; compute; easy);
          try (apply sort_seq_Permutation; compute; easy)
  end.

Ltac validateCaptoSep' := 
  match goal with
  | |- {{(⋂ _)%P}} _ {{(∩ _)%P}} =>
	    eapply CONS;
      ([> validate_red; Csimpl; compute; Rsimpl; apply ID_implies
      | validateCapImpliesSep'
      | eapply CONS; 
        ([>apply ID_implies | idtac | 
          solvePlaceholder_refl_internal ]);
        compute; Rsimpl; validateCapImpliesCap
      ])
  end.