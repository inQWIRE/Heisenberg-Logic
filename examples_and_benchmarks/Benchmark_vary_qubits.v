Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(******************* Benchmark 1: Graph state qubit sweep *******************)
(***************************************************)

Definition CZ q0 q1 : prog := (H q1 ;; CNOT q0 q1 ;; H q1)%pg.

Fixpoint edges_to_CZ_loop (progs : list prog) (last_prog : prog) : prog :=
  match progs with 
  | h :: t => (h ;; (edges_to_CZ_loop t last_prog))%pg
  | [] => last_prog
  end.

Definition edges_to_CZ (edges : list (nat * nat)) := 
  let progs := (map (fun e => CZ (fst e) (snd e)) edges) in
  edges_to_CZ_loop (removelast progs) (last progs (H 0%nat)).

Compute edges_to_CZ [ (0, 1); (1, 2) ]%nat.


Fixpoint vertex_edges_to_stabilizer_loop (size : nat) (edges : list (nat * nat)) (v : nat) (acc : list Pauli) :=
  match edges with
  | [] => acc
  | (e1, e2) :: t => if Nat.eqb v e1 then
                     vertex_edges_to_stabilizer_loop size t v (switch acc gZ e2)
                   else if Nat.eqb v e2 then
                          vertex_edges_to_stabilizer_loop size t v (switch acc gZ e1)
                        else vertex_edges_to_stabilizer_loop size t v acc
  end.

Definition vertex_edges_to_stabilizer (size : nat) (edges : list (nat * nat)) (v : nat) : TType size :=
  (C1, vertex_edges_to_stabilizer_loop size edges v (switch (repeat gI size) gX v)).

Definition graph_to_stabilizers (size : nat) (edges : list (nat * nat)) : list (TType size) :=
  map (vertex_edges_to_stabilizer size edges) (List.seq 0%nat size).

Definition graph_to_Predicate (size : nat) (edges : list (nat * nat)) : Predicate size :=
  Cap (map TtoA (graph_to_stabilizers size edges)).

Compute graph_to_Predicate 3 [ (0, 1); (1, 2) ]%nat.


Definition nat_to_X_i (size i : nat) := (C1, switch (repeat gI size) gX i).

Definition graph_init (size : nat) : Predicate size :=
  @Cap size (map (fun i => TtoA (nat_to_X_i size i)) (List.seq 0%nat size)).

Definition complete_graph_edges (size : nat) : list (nat * nat) :=
  flat_map (fun left : nat => 
              map (fun right : nat => 
                     (left,right)
                ) (List.seq (left + 1)%nat (size - left - 1)%nat)
    ) (List.seq 0%nat (size - 1)%nat).

Ltac unfoldGraphState :=
  unfold complete_graph_edges, graph_init, nat_to_X_i, graph_to_Predicate, graph_to_stabilizers, vertex_edges_to_stabilizer, edges_to_CZ, TtoA; simpl.


(** ** Benchmark by Graph States ** **)
(** ** Simple benchmark by varying the number of qubits ** **)

Lemma Benchmark_varyQubits_K5_q5 :  (* complete graph K5 in 5 qubits *)
{{ graph_init 5
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 5
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.02 secs (0.02u,0.s) (success) *)
Qed.

Lemma Benchmark_varyQubits_K5_q10 :  (* complete graph K5 in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 10
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.07 secs (0.068u,0.s) (success) *)
Qed.

Lemma Benchmark_varyQubits_K5_q15 :  (* complete graph K5 in 15 qubits *)
{{ graph_init 15
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 15
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.165 secs (0.152u,0.007s) (success) *)
Qed.

Lemma Benchmark_varyQubits_K5_q20 :  (* complete graph K5 in 20 qubits *)
{{ graph_init 20
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 20
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.291 secs (0.273u,0.008s) (success) *)
Qed.

Lemma Benchmark_varyQubits_K5_q25 :  (* complete graph K5 in 25 qubits *)
{{ graph_init 25
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 25
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.502 secs (0.447u,0.037s) (success) *)
Qed.

Lemma Benchmark_varyQubits_K5_q30 :  (* complete graph K5 in 30 qubits *)
{{ graph_init 30
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 30
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.769 secs (0.698u,0.051s) (success) *)
Qed.

(** time complexity seems to be quadratic in the number of qubits (~ n^2) **)

