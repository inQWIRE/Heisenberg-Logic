Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(******************* Benchmark 3: T gates on a single qubit *******************)
(***************************************************)


(** ** Benchmark by T Gates ** **)

Fixpoint Trepeat (n : nat) : prog :=
  match n with
  | 0 => T 0
  | s n' => (T 0 ;; Trepeat n')%pg
  end.

Definition Ts (n : nat) : prog := Trepeat (n - 1)%nat.

Compute Trepeat 3.
Compute Ts 3.





Lemma Benchmark_T50 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 50
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 0.347 secs (0.313u,0.024s) (success) *)
assumption.
Qed.

Lemma Benchmark_T100 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 100
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 0.768 secs (0.714u,0.03s) (success) *)
assumption.
Qed.

Lemma Benchmark_T150 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 150
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 1.004 secs (0.928u,0.047s) (success) *)
assumption.
Qed.

Lemma Benchmark_T200 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 200
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 1.377 secs (1.293u,0.041s) (success) *)
assumption.
Qed.

Lemma Benchmark_T250 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 250
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 1.764 secs (1.674u,0.049s) (success) *)
assumption.
Qed.

Lemma Benchmark_T300 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 300
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 2.004 secs (1.923u,0.037s) (success) *)
assumption.
Qed.

Lemma Benchmark_T350 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 350
{{ Placeholder }} .
Proof. unfold Ts; simpl.
  time solvePlaceholder_refl.
(* Tactic call ran for 2.236 secs (2.156u,0.03s) (success) *)
assumption.
Qed.
