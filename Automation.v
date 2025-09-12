Require Export HeisenbergFoundations.HoareHeisenbergLogic.


Local Open Scope nat_scope.



(** ** Definitions and tactics for automation. ** **)

Definition extractC {n : nat} (a : AType n) : list Coef := map fst a.
Definition extractA {n : nat} (a : AType n) : list (AType n) := map (fun t => [(C1, snd t)]) a.
Fixpoint computeHT (g : prog) {n : nat} (a : AType n) : list (AType n) :=
  match a with
  | [] => []
  | t :: a' => match t with
             | (_, l) => match g with
                        | CNOT ctrl targ => match nth ctrl l gI with
                                           | gI => match nth targ l gI with
                                                  | gI => [(C1, l)] :: (computeHT g a')
                                                  | gX => [(C1, l)] :: (computeHT g a')
                                                  | gZ => [(C1, switch (switch l gZ ctrl) gZ targ)] :: (computeHT g a')
                                                  | gY => [(C1, switch (switch l gZ ctrl) gY targ)] :: (computeHT g a')
                                                  end
                                           | gX => match nth targ l gI with
                                                  | gI => [(C1, switch (switch l gX ctrl) gX targ)] :: (computeHT g a')
                                                  | gX => [(C1, switch (switch l gX ctrl) gI targ)] :: (computeHT g a')
                                                  | gZ => [((- C1)%C, switch (switch l gY ctrl) gY targ)] :: (computeHT g a')
                                                  | gY => [(C1, switch (switch l gY ctrl) gZ targ)] :: (computeHT g a')
                                                  end
                                           | gZ => match nth targ l gI with
                                                  | gI => [(C1, l)] :: (computeHT g a')
                                                  | gX => [(C1, l)] :: (computeHT g a')
                                                  | gZ => [(C1, switch (switch l gI ctrl) gZ targ)] :: (computeHT g a')
                                                  | gY => [(C1, switch (switch l gI ctrl) gY targ)] :: (computeHT g a')
                                                  end
                                           | gY => match nth targ l gI with
                                                  | gI => [(C1, switch (switch l gY ctrl) gX targ)] :: (computeHT g a')
                                                  | gX => [(C1, switch (switch l gY ctrl) gI targ)] :: (computeHT g a')
                                                  | gZ => [(C1, switch (switch l gX ctrl) gY targ)] :: (computeHT g a')
                                                  | gY => [((- C1)%C, switch (switch l gX ctrl) gZ targ)] :: (computeHT g a')
                                                  end
                                           end
                        | H n => match nth n l gI with
                                | gI => [(C1, l)] :: (computeHT g a')
                                | gX => [(C1, switch l gZ n)] :: (computeHT g a')
                                | gZ => [(C1, switch l gX n)] :: (computeHT g a')
                                | gY => [((- C1)%C, l)] :: (computeHT g a')
                                end
                        | S n => match nth n l gI with
                                | gI => [(C1, l)] :: (computeHT g a')
                                | gX => [(C1, switch l gY n)] :: (computeHT g a')
                                | gZ => [(C1, l)] :: (computeHT g a')
                                | gY => [((- C1)%C, switch l gX n)] :: (computeHT g a')
                                end
                        | T n => match nth n l gI with
                                | gI => [(C1, l)] :: (computeHT g a')
                                | gX => [((C1/√2)%C, l); ((C1/√2)%C, switch l gY n)] :: (computeHT g a')
                                | gZ => [(C1, l)] :: (computeHT g a')
                                | gY => [((C1/√2)%C, l); (((- C1) * (C1/√2))%C, switch l gX n)] :: (computeHT g a')
                                end
                        | _ ;; _ => []
                        end
             end
  end.

Definition computeFinalStep (g : prog) (n : nat) (a : AType n) :=
  lincombCA (@extractC n a) (@computeHT g n a).

Ltac  BASE_auto_loop n p l g :=
  match n with
  | 0%nat =>  
      match p with
      | gI => eapply TEN_ID'
      | gX => match g with
             | H => eapply (TEN1' C1 p gZ)
             | S => eapply (TEN1' C1 p gY)
             | T => eapply (TEN3' C1 p gX gY)
             end
      | gY => match g with
             | H => eapply (TEN1' (- C1)%C p gY)
             | S => eapply (TEN1' (- C1)%C p gX)
             | T => eapply (TEN3' (- C1)%C p gY gX)
             end
      | gZ => match g with
             | H => eapply (TEN1' C1 p gX)
             | _ => eapply (TEN1' C1 p gZ)
             end
      end
  | s ?m => 
      match l with
      | ?h :: ?t => BASE_auto_loop m h t g
      | nil => idtac
      end
  end.

Ltac CNOT_auto_loop ctrl p1 l1 targ p2 l2 :=
  match ctrl with
  | 0%nat => 
      match targ with
      | 0%nat => 
          match p1 with
          | gI => match p2 with
                 | gI => eapply TEN_ID2'
                 | gX => eapply (TEN2' C1 p1 p2 gI gX)
                 | gY => eapply (TEN2' C1 p1 p2 gZ gY)
                 | gZ => eapply (TEN2' C1 p1 p2 gZ gZ)
                 end
          | gX => match p2 with
                 | gI => eapply (TEN2' C1 p1 p2 gX gX)
                 | gX => eapply (TEN2' C1 p1 p2 gX gI)
                 | gY => eapply (TEN2' C1 p1 p2 gY gZ)
                 | gZ => eapply (TEN2' (- C1)%C p1 p2 gY gY)
                 end
          | gY => match p2 with
                 | gI => eapply (TEN2' C1 p1 p2 gY gX)
                 | gX => eapply (TEN2' C1 p1 p2 gY gI)
                 | gY => eapply (TEN2' (- C1)%C p1 p2 gX gZ)
                 | gZ => eapply (TEN2' C1 p1 p2 gX gY)
                 end
          | gZ => match p2 with
                 | gI => eapply (TEN2' C1 p1 p2 gZ gI)
                 | gX => eapply (TEN2' C1 p1 p2 gZ gX)
                 | gY => eapply (TEN2' C1 p1 p2 gI gY)
                 | gZ => eapply (TEN2' C1 p1 p2 gI gZ)
                 end
          end
      | s ?t => match l2 with
               | ?h2 :: ?t2 => CNOT_auto_loop ctrl p1 l1 t h2 t2 
               | nil => idtac
               end
      end
  | s ?c => match l1 with
           | ?h1 :: ?t1 => CNOT_auto_loop c h1 t1 targ p2 l2
           | nil => idtac
           end
  end.

Ltac simplify_kth_Coef n k final :=
  let coef := fresh "coef" in
  pose (fst (nth k final (defaultT_Z n))) as coef; simpl in coef;
  let Htemp'' := fresh "Htemp''" in
  assert (Htemp'' : (C0, coef) = (C0, coef)) by reflexivity;
  unfold coef in Htemp'';
  match goal with
  | _ : (C0, ?cf) = (C0, ?cf) |- _ => field_simplify cf in final
  end;
  clear coef; clear Htemp''.

Ltac simplifyCoef_loop n k final :=
  match k with
  | 0%nat => idtac
  | s ?k' =>  try simplify_kth_Coef n k' final; simplifyCoef_loop n k' final
  end.

Ltac simplifyCoef n final :=
  let len := fresh "len" in
  pose (length final) as len; simpl in len;
  let Htemp' := fresh "Htemp'" in
  assert (Htemp' : (0%nat, len) = (0%nat, len)) by reflexivity;
  unfold len in Htemp';
  match goal with
  | _ : (0%nat, ?k) = (0%nat, ?k) |- _ => simplifyCoef_loop n k final
  end;
  clear len; clear Htemp'.

Ltac validateU :=
  repeat (simpl; Csimpl; repeat rewrite Cmult_assoc; repeat rewrite Cmult_neg1_mult; repeat rewrite Copp_involutive);
  match goal with
  | |- {{ AtoPred [(?c, ?l)] }} CNOT ?ctrl ?targ {{ _ }} => 
      match l with
      | ?h :: ?t => CNOT_auto_loop ctrl h t targ h t; 
                  repeat (simpl; Csimpl; repeat rewrite Cmult_assoc; repeat rewrite Cmult_neg1_mult; repeat rewrite Copp_involutive);
                  WF_auto;
                  let final := fresh "final" in
                  pose (computeFinalStep (CNOT ctrl targ) (length l) [(c, l)]) as final;
                  unfold computeFinalStep, lincombCA in final; simpl in final;
                  simplifyCoef (length l) final
      | nil => idtac
      end
  | |- {{ AtoPred [(?c, ?l)] }} ?g ?n {{ _ }} => 
      match l with
      | ?h :: ?t => BASE_auto_loop n h t g; 
                  repeat (simpl; Csimpl; repeat rewrite Cmult_assoc; repeat rewrite Cmult_neg1_mult; repeat rewrite Copp_involutive);
                  WF_auto;
                  let final := fresh "final" in
                  pose (computeFinalStep (g n) (length l) [(c, l)]) as final;
                  unfold computeFinalStep, lincombCA in final; simpl in final;
                  simplifyCoef (length l) final
      | nil => idtac
      end
  end.

Ltac loopHT n Lc Lpre Lpost prg listApre listApost listHT :=
  match listApre with
  | ?hpr :: ?tpr =>
      match listApost with
      | ?hpo :: ?tpo =>
          let pfHT := fresh "pfHT" in
          assert (pfHT : @triple n (AtoPred hpr) (prg) (AtoPred hpo));
          [auto with ht_db; try validateU | loopHT n Lc Lpre Lpost prg tpr tpo ((packHT hpr prg hpo pfHT) :: listHT)]
      | [] => let Lht := fresh "Lht" in (pose (rev listHT) as Lht); simpl in Lht;
                                      eapply (LINCOMB' Lc Lpre Lpost Lht)
      end
  | [] => let Lht := fresh "Lht" in (pose (rev listHT) as Lht); simpl in Lht;
                                  eapply (LINCOMB' Lc Lpre Lpost Lht)
  end.

Ltac validateLC :=
  repeat (simpl; Csimpl; repeat rewrite Cmult_assoc; repeat rewrite Cmult_neg1_mult; repeat rewrite Copp_involutive);
  unfold lincombCA; simpl;
  match goal with
  | |- @triple ?n _ (_ ;; _) _ => idtac
  | |- @triple ?n (AtoPred ?a) (?g) (?B) => 
      let listC := fresh "listC" in
      pose (@extractC n a) as listC; simpl in listC;
      let listApre := fresh "listApre" in
      pose (@extractA n a) as listApre; simpl in listApre;
      let listApost := fresh "listApost" in
      pose (@computeHT g n a) as listApost; simpl in listApost;
      let Htemp := fresh "Htemp" in
      assert (Htemp : (listApre, listApost, listC) = (listApre, listApost, listC)) by reflexivity;
      unfold listApre, listApost, listC in Htemp;
      match goal with
      | _ : (?Lpre, ?Lpost, ?Lc) = (?Lpre, ?Lpost, ?Lc) |- @triple n (AtoPred a) (g) (B) => 
          clear listC; clear listApre; clear listApost; clear Htemp;
          loopHT n Lc Lpre Lpost g Lpre Lpost (@nil (HoareTriple n));
          repeat (simpl; Csimpl; repeat rewrite Cmult_assoc; repeat rewrite Cmult_neg1_mult; repeat rewrite Copp_involutive);
          WF_auto;
          let final := fresh "final" in
          pose (computeFinalStep g n a) as final;
          unfold computeFinalStep, lincombCA in final; simpl in final;
          simplifyCoef n final
      end
  end.

Ltac simplifyCoefLC_C_loop base init final :=
  match final with
  | (Cdiv (RtoC (IZR (Zpos xH)))  (*  this is (C1 / √2)%C  *)
       (RtoC (sqrt (IZR (Zpos (xO xH)))))) => 
      match init with
      | (?c1 * ?c2)%C => simplifyCoefLC_C_loop init c1 c2
      | _ => repeat rewrite Cmult_assoc; repeat (try rewrite Cmult_neg1_mult; Csimpl)
      end
  | (- C1)%C => 
      replace base with (final * init)%C by (rewrite Cmult_comm; reflexivity);
      match init with
      | (?c1 * ?c2)%C => simplifyCoefLC_C_loop init c1 c2
      | _ => repeat rewrite Cmult_assoc; repeat (try rewrite Cmult_neg1_mult; Csimpl)
      end
  | _ => repeat rewrite Cmult_assoc; repeat (try rewrite Cmult_neg1_mult; Csimpl)
  end.  

Ltac simplifyCoefLC_C C := 
  repeat rewrite Cmult_assoc;
  match C with
  | (?c1 * ?c2)%C => simplifyCoefLC_C_loop C c1 c2
  | _ => idtac
  end.

Ltac simplifyCoefLC_loop a :=
  match a with
  | (?c, ?l) :: ?a' => simplifyCoefLC_C c; simplifyCoefLC_loop a'
  | [] => idtac 
  end.

Ltac simplifyCoefLC :=
  match goal with
  | |- {{ _ }} _ {{ AtoPred ?a }} => 
      match a with
      | (?c, ?l) :: ?a' => simplifyCoefLC_C c; repeat simplifyCoefLC_loop a'
      | [] => idtac 
      end
  | |- _ => idtac
  end.

Ltac simplifyCoefLC_C_loop_context H base init final :=
  match final with
  | (Cdiv (RtoC (IZR (Zpos xH)))  (*  this is (C1 / √2)%C  *)
       (RtoC (sqrt (IZR (Zpos (xO xH)))))) => 
      match init with
      | (?c1 * ?c2)%C => simplifyCoefLC_C_loop_context H init c1 c2
      | _ => repeat rewrite Cmult_assoc in H; repeat (try rewrite Cmult_neg1_mult in H; Csimpl_context H)
      end
  | (- C1)%C => 
      replace base with (final * init)%C in H by (rewrite Cmult_comm; reflexivity);
      match init with
      | (?c1 * ?c2)%C => simplifyCoefLC_C_loop_context H init c1 c2
      | _ => repeat rewrite Cmult_assoc in H; repeat (try rewrite Cmult_neg1_mult in H; Csimpl_context H)
      end
  | _ => repeat rewrite Cmult_assoc in H; repeat (try rewrite Cmult_neg1_mult in H; Csimpl_context H)
  end.  

Ltac simplifyCoefLC_C_context H C := 
  repeat rewrite Cmult_assoc in H;
  match C with
  | (?c1 * ?c2)%C => simplifyCoefLC_C_loop_context H C c1 c2
  | _ => idtac
  end.

Ltac simplifyCoefLC_loop_context H a :=
  match a with
  | (?c, ?l) :: ?a' => simplifyCoefLC_C_context H c; simplifyCoefLC_loop_context H a'
  | [] => idtac 
  end.

Ltac simplifyCoefLC_context :=
  match goal with
  | [H : {{ _ }} _ {{ AtoPred ?a }} |- _ ] => 
      match a with
      | (?c, ?l) :: ?a' => simplifyCoefLC_C_context H c; repeat simplifyCoefLC_loop_context H a'
      | [] => idtac 
      end
  |  _ => idtac
  end.

Ltac validate_single := 
  repeat (try eapply CAP'; try eapply split_Forall2;
          repeat
            (simpl; Csimpl; repeat rewrite Cmult_assoc;
             repeat rewrite Cmult_neg1_mult;
             repeat rewrite Copp_involutive); 
          try validateU; try validateLC;
          WF_auto).

Ltac validate :=
  repeat (tryif eapply SEQ then [> (*repeat eapply SEQ*)validate; validate_single | idtac] else validate_single).

Ltac solvePlaceholder :=
  intros;
  eexists ?[Ph];
  match goal with
  | |- ?g => let G := fresh "G" in assert (G : g);
                                [> validate | idtac ];
                                simpl in *; Csimpl; Csimpl_context G;
                                repeat simplifyCoefLC; repeat simplifyCoefLC_context
  end.



Ltac validateCapImpliesSep :=
  repeat 
    match goal with 
    | |- _ ⇒ Sep _ => compute; Rsimpl; eapply CaptoSep; compute; Rsimpl; auto;
                    repeat (constructor; try split; intros; try lia; auto)
    | |- Permutation _ _ => try (apply Permutation_sym; apply sort_seq_Permutation; compute;  easy); try (apply sort_seq_Permutation; compute;  easy)
    end.

Ltac validateCapImpliesCap :=
  apply CapElim;
  unfold incl;
  let a := fresh "a" in 
  let H' := fresh "H'" in 
  intros a H';
  repeat (first [destruct H' as [H' | H']; subst; [> try (left; easy); repeat (right; try easy; try (left; easy)) | idtac] | inversion H']).

Ltac validateCaptoSep :=
  match goal with 
  | |- {{ Cap _  }} _ {{ Sep _ }} => eapply CONS; [> compute; Rsimpl; apply ID_implies | 
                                                            validateCapImpliesSep | 
                                                            eapply CONS; [> apply ID_implies | idtac | validate] ];
                                   validateCapImpliesCap
  end.





(* Computation for "non-additive" gate application function since T gates don't preserve well-formedness *)
(** ** Calculate Postcondition Function ** **)

Inductive nonadditive_prog : prog -> Prop :=
| H_nonadditive : forall (bit : nat), nonadditive_prog (H bit)
| S_nonadditive : forall (bit : nat), nonadditive_prog (S bit)
| CNOT_nonadditive : forall (ctrl targ : nat), nonadditive_prog (CNOT ctrl targ)
| seq_nonadditive : forall (g1 g2 : prog), nonadditive_prog g1 -> nonadditive_prog g2 ->
                                      nonadditive_prog (g1 ;; g2).

Inductive prog_bound (n : nat) : prog -> Prop :=
| H_bound : forall (bit : nat), bit < n -> prog_bound n (H bit)
| S_bound : forall (bit : nat), bit < n -> prog_bound n (S bit)
| T_bound : forall (bit : nat), bit < n -> prog_bound n (T bit)
| CNOT_bound : forall (ctrl targ : nat), ctrl < n -> targ < n -> ctrl <> targ -> 
                                  prog_bound n (CNOT ctrl targ)
| seq_bound : forall (g1 g2 : prog), prog_bound n g1 -> prog_bound n g2 ->
                                prog_bound n (g1 ;; g2).



Definition gate_on_TType {n : nat} (g : prog) (t : TType n) : TType n :=
  match g with
  | H n => 
      match t with
      | (c, lp) => match nth n lp gI with
                  | gI => t
                  | gX => (c, switch lp gZ n)
                  | gY => ((- C1 * c)%C, lp)
                  | gZ => (c, switch lp gX n)
                  end
      end
  | S n => match t with
          | (c, lp) => match nth n lp gI with
                      | gI => t
                      | gX => (c, switch lp gY n)
                      | gY => ((- C1 * c)%C, switch lp gX n)
                      | gZ => t
                      end
          end 
  | T n => match t with
          | (c, lp) => match nth n lp gI with
                      | gI => t
                      | gX => t (* [((C1/√2 * c)%C, lp); ((C1/√2 * c)%C, switch lp gY n)] *)
                      | gY => t (* [((C1/√2 * c)%C, lp); ((- C1 * C1/√2 * c)%C , switch lp gX n)] *)
                      | gZ => t
                      end
          end
  | CNOT ctrl targ => match t with
                     | (c, lp) =>
                         match nth ctrl lp gI with
                         | gI => match nth targ lp gI with
                                | gI => t
                                | gX => t
                                | gZ => (c, switch (switch lp gZ ctrl) gZ targ)
                                | gY => (c, switch (switch lp gZ ctrl) gY targ)
                                end
                         | gX => match nth targ lp gI with
                                | gI => (c, switch (switch lp gX ctrl) gX targ)
                                | gX => (c, switch (switch lp gX ctrl) gI targ)
                                | gZ => ((- C1 * c)%C, switch (switch lp gY ctrl) gY targ)
                                | gY => (c, switch (switch lp gY ctrl) gZ targ)
                                end
                         | gZ => match nth targ lp gI with
                                | gI => t
                                | gX => t
                                | gZ => (c, switch (switch lp gI ctrl) gZ targ)
                                | gY => (c, switch (switch lp gI ctrl) gY targ)
                                end
                         | gY => match nth targ lp gI with
                                | gI => (c, switch (switch lp gY ctrl) gX targ)
                                | gX => (c, switch (switch lp gY ctrl) gI targ)
                                | gZ => (c, switch (switch lp gX ctrl) gY targ)
                                | gY => ((- C1 * c)%C, switch (switch lp gX ctrl) gZ targ)
                                end
                         end
                     end
  | _ ;; _ => t
  end.

Lemma gate_on_TType_gScaleT_comm : forall {n : nat} (g : prog) (t : TType n) (c : Coef),
    gate_on_TType g (gScaleT c t) = gScaleT c (gate_on_TType g t).
Proof. intros n g t c. 
  unfold gScaleT. destruct t.
  gen c; induction g; intros; simpl; auto;
    try destruct (nth n0 l gI) eqn:E;
    try destruct (nth n1 l gI) eqn:E1;
    try destruct (nth n2 l gI) eqn:E2;
    simpl; auto;
    repeat (f_equal; try lca).
Qed.



Import my_H.



Lemma WF_TType_gate_on_TType : forall {n : nat} (g : prog) (t : TType n),
    prog_bound n g -> WF_TType t -> WF_TType (gate_on_TType g t).
Proof. intros n g t H0 H1.
  induction g; destruct t; simpl;
  try destruct (nth n0 l gI) eqn:E;
  try destruct (nth n1 l gI) eqn:E1;
  try destruct (nth n2 l gI) eqn:E2;
  try constructor;
  try inversion H1; try inversion H2; try inversion H3; try inversion H0;
    simpl in *; subst; try (left; lca); try (right; lca);
    try split; simpl in *; try rewrite ! switch_len; auto;
    try (rewrite switch_inc;
         [> apply trace_zero_syntax_R; apply trace_zero_syntax_L; constructor |
           try rewrite ! switch_len; auto]);
    try (rewrite switch_switch_diff; auto;
         try (rewrite switch_inc;
              [> apply trace_zero_syntax_R; apply trace_zero_syntax_L; constructor |
                try rewrite ! switch_len; auto])).
Qed.

Fixpoint prog_on_TType {n : nat} (g : prog) (t : TType n) : TType n :=
  match g with
  | g1 ;; g2 => prog_on_TType g2 (prog_on_TType g1 t)
  | _ => gate_on_TType g t
  end.

Lemma WF_TType_prog_on_TType : forall {n : nat} (g : prog) (t : TType n),
    prog_bound n g -> WF_TType t -> WF_TType (prog_on_TType g t).
Proof. intros n g t H0 H1.
  gen t; induction g; intros;  try apply WF_TType_gate_on_TType; auto.
  simpl. inversion H0; subst. auto.
Qed.

Lemma compute_postcond : forall {n : nat} (g : prog) (t : TType n),
    nonadditive_prog g -> prog_bound n g -> WF_TType t ->
    {{ AtoPred [t] }} g {{ AtoPred [prog_on_TType g t] }}.
Proof. intros n g t H0 H1 H2.
  gen t; induction g; intros; destruct t; simpl;
    try destruct (nth n0 l gI) eqn:E;
    try destruct (nth n1 l gI) eqn:E1;
    try destruct (nth n2 l gI) eqn:E2;
    inversion H2; inversion H3; inversion H4; inversion H0; inversion H1; simpl in *; subst.
  1-16: try match goal with
          | Hyp : nth ?n0 ?l gI = gI |- {{ ?A }} _ {{ ?A }} => eapply TEN_ID'; WF_auto
          end.
 1-12: try match goal with
         | Hyp : nth ?n0 ?l gI = _ |- _ => 
             eapply TEN1'; try (symmetry; apply E); try easy;
             try match goal with 
               | Hyp: _ |- {{ _ }} _ {{ _ }} => auto with ht_db
               end; WF_auto;
             try (rewrite switch_inc; auto; rewrite <- E; rewrite <- nth_inc; auto)
         end.
 1-32: try match goal with
          | Hyp : nth ?n0 ?l gI = gI |- {{ ?A }} _ {{ ?A }} => 
              try (eapply TEN_ID2'; easy)
          end.
 1-30: eapply TEN2'; try (symmetry; apply E1); try (symmetry; apply E2); try easy; 
 try match goal with 
   | Hyp: _ |- {{ _ }} _ {{ _ }} => auto with ht_db
   end; WF_auto;
 try (rewrite switch_inc with (n := n1); auto; try rewrite <- E1; rewrite <- nth_inc; auto;
      rewrite switch_inc with (n := n2); auto; try rewrite <- E2; rewrite <- nth_inc; auto).
 all: eapply SEQ; try apply IHg1; auto; try apply IHg2; auto;
   apply WF_TType_prog_on_TType; auto.
 Qed.

Lemma compute_postcond_CAP : forall {n : nat} (g : prog) (lt : list (TType n)),
    nonadditive_prog g -> prog_bound n g -> Forall WF_TType lt ->
    {{ Cap (map TtoA lt) }} g {{ Cap (map (fun t => TtoA (prog_on_TType g t)) lt) }}.
Proof. intros n g lt H0 H1 H2.
  apply CAP'. 
  induction lt; auto.
  rewrite Forall_cons_iff in H2. destruct H2. specialize (IHlt H3).
  constructor; auto.
  apply compute_postcond; auto.
Qed.


