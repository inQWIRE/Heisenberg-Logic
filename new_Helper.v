Require Import Psatz.  
Require Import String. 
Require Import Program.
Require Import List.

 
Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.



(* Some helpers *)


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


