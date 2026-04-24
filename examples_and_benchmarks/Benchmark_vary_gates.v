Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(******************* Benchmark 1: Graph state gate sweep *******************)
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
(** ** Simple benchmark by varying the number of gates ** **)

Lemma Benchmark_varyGates_K5_q10 :  
(* complete graph K5 (= 3*10 = 30 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 10
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.065 secs (0.064u,0.s) (success) *)
Qed.

Lemma Benchmark_varyGates_K6_q10 :  
(* complete graph K6 (= 3*15 = 45 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 6
) {{ graph_to_Predicate 10
( complete_graph_edges 6
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.069 secs (0.068u,0.s) (success) *)
Qed.

Lemma Benchmark_varyGates_K7_q10 :  
(* complete graph K7 (= 3*21 = 63 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 7
) {{ graph_to_Predicate 10
( complete_graph_edges 7
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.091 secs (0.088u,0.001s) (success) *)
Qed.

Lemma Benchmark_varyGates_K8_q10 :  
(* complete graph K8 (= 3*28 = 84 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 8
) {{ graph_to_Predicate 10
( complete_graph_edges 8
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.11 secs (0.107u,0.002s) (success) *)
Qed.

Lemma Benchmark_varyGates_K9_q10 :  
(* complete graph K9 (= 3*36 = 108 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 9
) {{ graph_to_Predicate 10
( complete_graph_edges 9
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.146 secs (0.138u,0.002s) (success) *)
Qed.

Lemma Benchmark_varyGates_K10_q10 :  
(* complete graph K10 (= 3*45 = 135 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 10
) {{ graph_to_Predicate 10
( complete_graph_edges 10
) }}.
Proof. unfoldGraphState.
  time validate_refl.
(* Tactic call ran for 0.181 secs (0.172u,0.004s) (success) *)
Qed.

(** time complexity seems to be linear in the number of gates **)

