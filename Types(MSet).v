Require Import Psatz.
Require Import Reals.
Require Import Vector.
Require Import MSets Orders BoolOrder.

Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.
Require Export Heisenberg. 
Require Import Setoid.



(************************)
(* Defining coeficients *)
(************************)


Definition Coef := C.

Definition cBigMul (cs : list Coef) : Coef :=
  fold_left Cmult cs C1.

Example test1: cBigMul (cons (RtoC 4) (cons (RtoC 7) nil)) = (RtoC 28).
Proof. lca. Qed.




(**********************)
(* Defining the types *)
(**********************)




(*
Module PauliModule <: OrderedType.

(* this is the lowest level, only Pauli gates are defined *)
Inductive Pauli :=
| gI
| gX
| gY
| gZ.

Definition t := Pauli.
Definition eq := @eq Pauli.
Definition eq_equiv := @eq_equivalence Pauli.
Definition lt (a b : Pauli) : Prop :=
  match a, b with
  | gI, gI => False
  | gZ, gI => True
  | gY, gI => True
  | gX, gI => True
  | gI, gZ => False
  | gZ, gZ => False
  | gY, gZ => True
  | gX, gZ => True
  | gI, gY => False
  | gZ, gY => False
  | gY, gY => False
  | gX, gY => True
  | gI, gX => False
  | gZ, gX => False
  | gY, gX => False
  | gX, gX => False
  end.

Lemma lt_irrefl : forall (a : Pauli), ~ lt a a.
Proof. intros a. induction a; easy. Qed.

Lemma lt_trans : forall a1 a2 a3 : Pauli, lt a1 a2 -> lt a2 a3 -> lt a1 a3.
Proof. intros a1 a2 a3 H H0. induction a1, a2, a3; easy. Qed.


Definition lt_strorder := Build_StrictOrder lt (fun a : Pauli => lt_irrefl a) (fun a1 a2 a3 : Pauli => lt_trans a1 a2 a3).

Definition lt_compat := reflexive_proper lt : Proper (eq ==> eq ==> iff) lt.

Definition compare (a b : Pauli) : comparison :=
  match a, b with
  | gI, gI => Eq
  | gZ, gI => Lt
  | gY, gI => Lt
  | gX, gI => Lt
  | gI, gZ => Gt
  | gZ, gZ => Eq
  | gY, gZ => Lt
  | gX, gZ => Lt
  | gI, gY => Gt
  | gZ, gY => Gt
  | gY, gY => Eq
  | gX, gY => Lt
  | gI, gX => Gt
  | gZ, gX => Gt
  | gY, gX => Gt
  | gX, gX => Eq
  end.

Definition compare_spec :
     forall x y : Pauli, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof. intros x y. induction x, y; constructor; easy. Qed. 

Definition eq_dec : forall x y : Pauli, {eq x y} + {~ eq x y}.
Proof. intros x y. induction x, y; try (left; easy); try (right; easy). Qed.

End PauliModule.

Import PauliModule.

Locate Make.
Module S := MSetList.Make PauliModule. (* Set of Paulis *)
*)








(* this is the lowest level, only Pauli gates are defined *)
Inductive Pauli :=
| gI
| gX
| gY
| gZ.





(*

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

Lemma beq_Pauli_eq : forall (x y : Pauli), beq_Pauli x y = true <-> x = y.
Proof. split.
  - intros H. induction x, y; try easy; inversion H.
  - intros H. induction x, y; easy.
Qed.

*)



Definition translate_P (g : Pauli) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gY => σy
  | gZ => σz
  end.


Lemma WF_Matrix_Pauli : forall (g : Pauli), WF_Matrix (translate_P g).
Proof. intros. 
       destruct g; simpl; auto with wf_db.
Qed.

Hint Resolve WF_Matrix_Pauli : wf_db.

(* Here we define a gMul to give Coef followed by a gMul to give the actual type *)
(* this allows for an easy zip in gMulT *)
Locate "-".
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




Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "< >" := (Vector.nil _) : vector_scope.
Notation "h <:: t " := (Vector.cons _ h _ t) (at level 60, right associativity)
    : vector_scope.
Notation "< x >" := (Vector.cons _ x _ (Vector.nil _ ) ) : vector_scope.
Notation "< x , y , .. , z >" := (Vector.cons _ x _ (Vector.cons _ y _ .. (Vector.cons _ z _ (Vector.nil _)) ..)) : vector_scope. 
Notation "v <@ p >" := (Vector.nth v p) (at level 1, format "v <@ p >") : vector_scope.
Infix "+++" := append (right associativity, at level 60) : vector_scope.
Open Scope vector_scope.
Arguments Vector.nil {A}.
Arguments Vector.cons {A}.







Definition Pauli_eq_dec : forall x y : Pauli, {x = y} + {~ x = y}.
Proof. intros x y. induction x, y; try (left; easy); try (right; easy). Qed.

Definition pair_eq_dec : forall [A B : Type],
    (forall x y : A, {x = y} + {x <> y}) -> (forall x y : B, {x = y} + {x <> y}) -> forall p p' : A * B, {p = p'} + {p <> p'}.
Proof. intros A B X Y p p'. destruct p, p'.
  destruct (X a a0), (Y b b0).
  - left. apply pair_equal_spec. split; easy.
  - right. rewrite pair_equal_spec. intros H. destruct H. contradiction.
  - right. rewrite pair_equal_spec. intros H. destruct H. contradiction.
  - right. rewrite pair_equal_spec. intros H. destruct H. contradiction.
Qed.





(*
Module TTypeModule <: DecidableType.

(* scaling, multiplication, and tensoring done at this level *)
(* using vectors instead of lists *)
Definition TType (len : nat) := (Coef * (t Pauli len))%type.


Definition t := forall len : nat, TType len.
Definition eq := @eq t.
Definition eq_equiv := @eq_equivalence t.
Definition eq_dec : forall (x y : forall len : nat, TType len), {x = y} + {~ x = y}.
Proof. intros x y. unfold TType in *.
  apply pair_eq_dec.
  - apply Ceq_dec.
  - apply list_eq_dec.
    apply Pauli_eq_dec.
Qed.

End TTypeModule.
*)






(*
Module TTypeModule <: DecidableType.

(* scaling, multiplication, and tensoring done at this level *)
(* using vectors instead of lists *)
Definition TType (len : nat) := (Coef * (list Pauli))%type.


Definition t := forall len : nat, TType len.
Definition eq := @eq t.
Definition eq_equiv := @eq_equivalence t.
Definition eq_dec : forall (x y : forall len : nat, TType len), {x = y} + {~ x = y}.
Proof. intros x y. unfold TType in *.
  apply pair_eq_dec.
  - apply Ceq_dec.
  - apply list_eq_dec.
    apply Pauli_eq_dec.
Qed.

End TTypeModule.
*)





Module TTypeModule <: DecidableType.

(* scaling, multiplication, and tensoring done at this level *)
(* using vectors instead of lists *)
Definition TType := (Coef * (list Pauli))%type.

Definition t := TType.
Definition eq := @eq t.
Definition eq_equiv := @eq_equivalence t.
Definition eq_dec : forall (x y : t), {x = y} + {~ x = y}.
Proof. intros x y.
  apply pair_eq_dec.
  - apply Ceq_dec.
  - apply list_eq_dec.
    apply Pauli_eq_dec.
Qed.

End TTypeModule.


(* set of TTypes, each element represents additive terms *)
Module AddSet := MSetWeakList.Make TTypeModule.

Definition TType := TTypeModule.TType.

Definition ErrT : TType := (C1, []).


Definition gMulT (A B : TType) : TType :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if length g1 =? length g2 
                 then (c1 * c2 * (cBigMul (zipWith gMul_Coef g1 g2)), 
                       zipWith gMul_base g1 g2)
                 else ErrT
    end
  end.

Definition gTensorT (A : TType) (B : TType) : TType  :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => (c1 * c2, g1 ++ g2)
    end
  end.

Definition gScaleT (c : Coef) (A : TType) : TType :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.


Definition translate (A : TType) : Square (2 ^ length (map translate_P (snd A))) := 
  (fst A) .* ⨂ (map translate_P (snd A)).









(* Additive Type: set elements are added to each other *)
Definition ArithPauli := AddSet.t.





(*
Inductive ArithPauli : nat -> Type :=
| P : Coef * Pauli -> ArithPauli 1 (* Base *)
| A {n : nat} : ArithPauli n -> ArithPauli n -> ArithPauli n (* Add *)
| M {n : nat} : ArithPauli n -> ArithPauli n -> ArithPauli n (* Mult *)
| T {n m : nat} : ArithPauli n -> ArithPauli m -> ArithPauli (n + m). (* Tensor *)
 *)




Locate "::".

Definition gTensorA (a : ArithPauli) (b : ArithPauli): ArithPauli :=
  
  
  match a with
  | [] => []
  | h1 :: t1 => map (uncurry gTensorT) (list_prod a b)
  end.
(*
Definition gScaleA *)


Inductive vType (n : nat) : Type :=
  | G : ArithPauli n -> vType n
  | Cap : vType n -> vType n -> vType n
  | Arrow : vType n -> vType n -> vType n
  | Err : vType n.

Arguments G {n}.
Arguments Cap {n}.
Arguments Arrow {n}.
Arguments Err {n}.


(* you cannot multiply intersection or arrow types (for now) 
   so any of these options returns Err *)
Definition mul {n} (A B : vType n) : vType n :=
  match A with
  | G a =>
    match B with
    | G b => G (Mul a b)
    | _ => Err
    end
  | _ => Err
  end.
                                       
Definition tensor {n m} (A : vType n) (B : vType m) : vType (n + m) :=
  match A with
  | G a =>
    match B with
    | G b => G (gTensorA a b)
    | _ => Err 
    end
  | _ => Err
  end.

(* since scaling intersections makes sense, we allow this *)
Fixpoint scale {n} (c : Coef) (A : vType n) : vType n :=
  match A with
  | G a => G (gScaleT c a)
  | Cap g1 g2 => Cap (scale c g1) (scale c g2)
  | _ => Err
  end.


Definition i {n} (A : vType n) := scale p_i A.
Notation "- A" := (scale n_1 A).
Infix ".*" := mul (at level 40, left associativity).
Infix ".⊗" := tensor (at level 51, right associativity).



Notation "A → B" := (Arrow A B) (at level 60, no associativity).
Notation "A ∩ B" := (Cap A B) (at level 60, no associativity).


