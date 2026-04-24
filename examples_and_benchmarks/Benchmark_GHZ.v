Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(******************* Benchmark 2: GHZ diagonal sweep *******************)
(***************************************************)


(** ** Benchmark by n-qubit GHZ state ** **)

Fixpoint CNOTchain (n i : nat) : prog :=
  match i with
  | 0 => CNOT (n-1)%nat n
  | s i' => (CNOT (n - i - 1)%nat (n - i)%nat ;; CNOTchain n i')%pg
  end.

(** Works for n >= 2 **)
Definition GHZ (n : nat) : prog := (H 0 ;; CNOTchain (n - 1)%nat (n - 2)%nat)%pg.

Compute GHZ 3.


Definition nat_to_Z_i (size i : nat) := (C1, switch (repeat gI size) gZ i).

Definition GHZ_init (size : nat) : Predicate size :=
  @Cap size (map (fun i => TtoA (nat_to_Z_i size i)) (List.seq 0%nat size)).

Ltac unfoldGHZ :=
  unfold GHZ, GHZ_init, nat_to_Z_i,TtoA; simpl.




Lemma Benchmark_GHZ5 :
exists Placeholder,
{{
GHZ_init 5
}}
GHZ 5
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.01 secs (0.01u,0.s) (success) *)
assumption.
Qed.

Lemma Benchmark_GHZ10 :
exists Placeholder,
{{
GHZ_init 10
}}
GHZ 10
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.029 secs (0.028u,0.s) (success) *)
assumption.
Qed.

Lemma Benchmark_GHZ15 :
exists Placeholder,
{{
GHZ_init 15
}}
GHZ 15
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.066 secs (0.063u,0.s) (success) *)
assumption.
Qed.

Lemma Benchmark_GHZ20 :
exists Placeholder,
{{
GHZ_init 20
}}
GHZ 20
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.134 secs (0.126u,0.004s) (success) *)
assumption.
Qed.

Lemma Benchmark_GHZ25 :
exists Placeholder,
{{
GHZ_init 25
}}
GHZ 25
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.222 secs (0.21u,0.007s) (success) *)
assumption.
Qed.

Lemma Benchmark_GHZ30 :
exists Placeholder,
{{
GHZ_init 30
}}
GHZ 30
{{ Placeholder }} .
Proof. unfoldGHZ.
 time solvePlaceholder_refl.
 (* Tactic call ran for 0.312 secs (0.291u,0.012s) (success) *)
assumption.
Qed.

