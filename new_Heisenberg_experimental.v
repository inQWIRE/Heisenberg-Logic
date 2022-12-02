Require Import Psatz.  
Require Import String. 
Require Import Program.
Require Import List.

 
Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.

Require Export new_Helper.

Inductive G : Square 2 -> Type :=
| I : G (Matrix.I 2)
| X : G σx
| Y : G σy
| Z : G σz.

Check G.
Check Z.


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





