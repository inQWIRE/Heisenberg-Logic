Require Export QuantumLib.Eigenvectors.

(* spectral decomposition *)
Definition WF_Spectral {n : nat} (A : Square n) : Prop :=
  WF_Matrix A /\ (exists (U D: Square n), 
    WF_Diagonal D /\ WF_Unitary U /\ D = U † × A × U).

Lemma pad1_adjoint : forall {n : nat} (A : Square n) (c : C),
    (pad1 A c) † = pad1 (A †) (c ^* ).
Proof. intros. 
  prep_matrix_equality. 
  unfold pad1, Mmult, col_wedge, row_wedge, e_i, Matrix.scale, Matrix.adjoint.
  simpl.
  bdestruct_all; simpl; try lia; try lca; try easy.
Qed.

Lemma spectral_pad1 : forall {n} (A : Square n) (c : C),
  WF_Spectral A -> WF_Spectral (pad1 A c).
Proof. intros n A c [H [U [D [[Hwf Hd] [H1 H0]]]]].
       split. apply WF_pad1; auto.
       exists (pad1 U C1), (pad1 D c).
       split. split; try (apply WF_pad1; auto).
  - intros i0 j H2. 
    destruct i0; destruct j; try lia;
      unfold pad1, col_wedge, row_wedge, scale, e_i;
      bdestruct_all; try easy; try lca.
    all : do 2 rewrite Sn_minus_1; apply Hd; lia. 
  - split; try (apply WF_pad1; auto).
    split.
    destruct H1.
    apply WF_pad1; easy.
    rewrite pad1_adjoint.
    replace (C1 ^* ) with C1 by lca.
    destruct H1 as [H1 H2].
    rewrite <- pad1_mult, H2, Cmult_1_r, pad1_I.
    easy.
    rewrite pad1_adjoint.
    replace (C1 ^* ) with C1 by lca.
    do 2 rewrite <- pad1_mult.
    rewrite <- H0, Cmult_1_r, Cmult_1_l.
    easy.
Qed.


Theorem unit_implies_spectral : forall {n} (A : Square n),
  WF_Unitary A -> WF_Spectral A.
Proof. induction n as [| n']. 
       - intros A [H H0]. 
         apply WF0_Zero_l in H. 
         rewrite H.
         unfold WF_Spectral.
         split; auto with wf_db.
         exists (Zero), (Zero).
         split.
         + unfold WF_Diagonal.
           split; auto with wf_db.
         + split.
           * unfold WF_Unitary.
             split; auto with wf_db.
           * lma'.
       - intros A H. 
         assert (H0 := H).
         apply unitary_reduction_step1 in H.
         destruct H as [X [H1 [c H2]]].
         assert (H3 : WF_Unitary ((X) † × A × X)).
         { do 2 try apply Mmult_unitary.
           apply transpose_unitary.
           all : easy. }
         assert (H4 : (forall (i j : nat), (i = 0%nat \/ j = 0%nat) /\ i <> j -> ((X) † × A × X) i j = C0)).
         { apply unitary_reduction_step2; try easy. 
           exists c. easy. }
         apply unitary_reduction_step3 in H3; try easy.
         destruct H3 as [A' [H5 H6]].
         assert (H7 : WF_Spectral ((X) † × A × X)).
         apply IHn' in H5.
         { rewrite <- H6. 
           apply spectral_pad1.
           easy. }
         destruct H7 as [Hwf Hd].
         split. 
         destruct H0; easy.
         destruct Hd as [U [D [H7 [H8 H9]]]].
         exists (X × U).
         exists D.
         destruct H1 as [H1wf H1u].
         destruct H8 as [H8wf H8u].
         split; try easy.
         split; auto with wf_db.
         split; auto with wf_db.
         rewrite Mmult_adjoint.
         rewrite Mmult_assoc.
         rewrite <- Mmult_assoc with (C := U).
         rewrite H1u.
         rewrite Mmult_1_l.
         auto.
         auto with wf_db.
         rewrite Mmult_adjoint.
         repeat rewrite Mmult_assoc.
         repeat rewrite Mmult_assoc in H9.
         easy.
Qed.
