Require Import Psatz.  
Require Import String. 
Require Import Program.
Require Import List.

 
Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.

Require Export new_Helper.


Inductive Pauli : Type :=
| gI
| gX
| gY
| gZ.



Inductive G : Square 2 -> Type :=
| I : G (Matrix.I 2)
| X : G σx
| Y : G σy
| Z : G σz.

Check G.
Check Z.

Inductive T {n} : Square n -> Type :=
| TG : forall (U : Square 2), G U -> T U
| Tscale : forall {n} (c : C) (U : S

Inductive T : (forall n : nat, Square n) -> Type :=
| TG : forall {U : Square 2}, G U -> T (fun (_ : nat) => U)
| Tscale : forall {n : nat} (c : C) {U : Square n},
    T (fun (_ : nat) => U) -> T (fun (_ : nat) => c .* U )
| Ttensor : forall {n m : nat} {U1 : Square n} {U2 : Square m},
    T (fun (_ : nat) => U1) -> T (fun (_ : nat) => U2) -> T  (fun (_ : nat) => (U1 ⊗ U2))
| Tadd : forall {n : nat} {U1 U2 : Square n},
    T (fun (_ : nat) => U1) -> T (fun (_ : nat) => U2) -> T (fun (_ : nat) => (U1 .+ U2)).

Check TG.
Check (TG Z).
Check (Tadd (TG Z) (Tscale C2 (Ttensor (TG X) (TG I)) )).

Coercion TG : G >-> T.

Infix "+'" := Tadd (at level 50, left associativity).
(* Infix "*'" := mult (at level 43, left associativity). *)
Infix "⊗'" := Ttensor (at level 40, left associativity).
Infix "⋅'" := Tscale (at level 39, left associativity).

Check (X ⊗' C2 ⋅' (Z +' I)).

Check (X ⊗' C2 ⋅' (Z +' (Y ⊗' I))).
Check σx ⊗ (C2 .* (σz .+ (σy ⊗ Matrix.I 2))).

Definition translateT {n : nat} {U : Square n} (t : T (fun _:nat => U)) := U.

Check translateT (X ⊗' C2 ⋅' (Z +' I)).


Inductive P : Type :=
| PT : forall {n : nat} {U : Square n}, T (fun (_ : nat) => U) -> P
| Pcap : P -> P -> P
| Pcup : P -> P -> P
| Psub : P -> list nat -> P.

Infix "⊍" := Pcup (at level 54, left associativity).
Infix "∩" := Pcap (at level 53, left associativity).
Infix "_s" := Psub (at level 52, left associativity).

Check PT (X ⊗' C2 ⋅' (Z +' I)) ∩ PT (X ⊗' C2 ⋅' (Z +' I)).

(* doesn't work *)
Coercion PT : T >-> P.

Fail Check (X ⊗' C2 ⋅' (Z +' I)) ∩ (X ⊗' C2 ⋅' (Z +' I)).


Definition vecEigenT {n : nat} {U : Square n} (v : Vector n) (t : T (fun _:nat => U)) : Prop :=
  WF_Matrix v /\ exists c, Eigenpair U (v, c).




(* this is wrong *)
Fixpoint Tsub {n : nat} {U : Square n} (t : T (fun _:nat => U)) (lst : list nat) :=
  match lst with
  | nil => match t with
           | Ttensor X A => translateT X
           | Ttensor Y A => translateT Y
           | Ttensor Z A => translateT Z
           | Ttensor I A => translateT I
           | _ => Zero
           end
  | x :: xs => match t with
               | Ttensor X A => Tsub A xs
               | Ttensor Y A => Tsub A xs
               | Ttensor Z A => Tsub A xs
               | Ttensor I A => Tsub A xs
               | _ => Zero
               end
  end.

Check Tsub (X ⊗' C2 ⋅' (Z +' I)) [1;2;3]%nat.


Fixpoint vecSatisfiesP {n : nat} (v : Vector n) (p : P) : Prop :=
  match p with
  | PT t => vecEigenT v t
  | Pcap p1 p2 => vecSatisfiesP v p1 /\ vecSatisfiesP v p2
  | Pcup p1 p2 => vecSatisfiesP v p1 /\ vecSatisfiesP v p2
  | Psub p0 lst => match 
