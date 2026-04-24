Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(******************* Graph States *******************)
(***************************************************)

Definition CZ q0 q1 : prog := (H q1 ;; CNOT q0 q1 ;; H q1)%pg.

(* TODO: I-only condition in validate_refl*)
Lemma IICZII : {{ pII }} CZ 0 1 {{ pII }}.
Proof. validate. Qed.

Lemma XICZXZ : {{ pXI }} CZ 0 1 {{ pXZ }}.
Proof. validate_refl. Qed.

Lemma IXCZZX : {{ pIX }} CZ 0 1 {{ pZX }}.
Proof. validate_refl. Qed.

Lemma XXCZYY : {{ pXX }} CZ 0 1 {{ pYY }}.
Proof. validate_refl. Qed.

Lemma YICZYZ : {{ pYI }} CZ 0 1 {{ pYZ }}.
Proof. validate_refl. Qed.

Lemma IYCZZY : {{ pIY }} CZ 0 1 {{ pZY }}.
Proof. validate_refl. Qed.

Lemma YYCZXX : {{ pYY }} CZ 0 1 {{ pXX }}.
Proof. validate_refl. Qed.

Lemma YXCZmXY : {{ pYX }} CZ 0 1 {{ mpXY }}.
Proof. validate_refl. Qed.

Lemma XYCZmYX : {{ pXY }} CZ 0 1 {{ mpYX }}.
Proof. validate_refl. Qed.

Lemma ZYCZIY : {{ pZY }} CZ 0 1 {{ pIY }}.
Proof. validate_refl. Qed.

Lemma YZCZYI : {{ pYZ }} CZ 0 1 {{ pYI }}.
Proof. validate_refl. Qed.

Lemma XZCZXI : {{ pXZ }} CZ 0 1 {{ pXI }}.
Proof. validate_refl. Qed.

Lemma ZXCZIX : {{ pZX }} CZ 0 1 {{ pIX }}.
Proof. validate_refl. Qed.

Lemma ZICZZI : {{ pZI }} CZ 0 1 {{ pZI }}.
Proof. validate_refl. Qed.

Lemma IZCZIZ : {{ pIZ }} CZ 0 1 {{ pIZ }}.
Proof. validate_refl. Qed.

Lemma ZZCZZZ : {{ pZZ }} CZ 0 1 {{ pZZ }}.
Proof. validate_refl. Qed.

#[export] Hint Resolve IICZII XICZXZ IXCZZX XXCZYY YICZYZ IYCZZY YYCZXX YXCZmXY XYCZmYX ZYCZIY YZCZYI XZCZXI ZXCZIX ZICZZI IZCZIZ ZZCZZZ : ht_db. 




(*
n = 3
edges = [ (0, 1); (1, 2) ]
*) 

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



Lemma TestGraphState :
exists Placeholder,
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ Placeholder }}.
Proof. unfoldGraphState.
  solvePlaceholder_refl.
  assumption.
Qed.


Compute @normalize 0%nat 3 [(C1, [gZ; gX; gZ]); (C1, [gI; gZ; gX]); (C1, [gX; gZ; gI])].


Lemma TestGraphState' : 
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ graph_to_Predicate 3 [ (0, 1); (1, 2) ]%nat }}.
Proof. unfoldGraphState.
  validate_refl.
Qed.

Lemma TestGraphState'' : (* complete graph K3 in 10 qubits *)
{{ graph_init 10 }} 
edges_to_CZ [ (0, 1); (0, 2); (1, 2)]%nat
{{ graph_to_Predicate 10 [ (0, 1); (0, 2); (1, 2)]%nat }}.
Proof. unfoldGraphState.
  validate_refl.
Qed.
