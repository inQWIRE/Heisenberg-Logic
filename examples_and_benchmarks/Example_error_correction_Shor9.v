Require Import HeisenbergFoundations.ReflexiveAutomation.



(***************************************************)
(************* Shor code on 9 qubits *************)
(***************************************************)

(* 
g1' ZZIIIIIII
g2' IZZIIIIII 
g3' IIIZZIIII 
g4' IIIIZZIII
g5' IIIIIIZZI
g6' IIIIIIIZZ
g7' XXXXXXIII
g8' IIIXXXXXX
Zbar' XXXXXXXXX
Xbar' ZZZZZZZZZ

ZL' := g1 ∩ ... ∩ g8 ∩ Zbar'
XL' := g1 ∩ ... ∩ g8 ∩ Xbar'
Sh9 := g1 ∩ ... ∩ g8

ZL' = Sh9 ∩ Zbar'
XL' = Sh9 ∩ Xbar'
*)

Definition g1' : TType 9 := (C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI]).
Definition g2' : TType 9 := (C1, [gI; gZ; gZ; gI; gI; gI; gI; gI; gI]).
Definition g3' : TType 9 := (C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI]).
Definition g4' : TType 9 := (C1, [gI; gI; gI; gI; gZ; gZ; gI; gI; gI]).
Definition g5' : TType 9 := (C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI]).
Definition g6' : TType 9 := (C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gZ]).
Definition g7' : TType 9 := (C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI]).
Definition g8' : TType 9 := (C1, [gI; gI; gI; gX; gX; gX; gX; gX; gX]).
Definition Xbar' : TType 9 := (C1, [gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ; gZ]).
Definition Zbar' : TType 9 := (C1, [gX; gX; gX; gX; gX; gX; gX; gX; gX]).
Definition ZL' : list (TType 9) := [g1'; g2'; g3'; g4'; g5'; g6'; g7'; g8'; Zbar'].
Definition XL' : list (TType 9) := [g1'; g2'; g3'; g4'; g5'; g6'; g7'; g8'; Xbar'].


Definition Shor9 q0 q1 q2 q3 q4 q5 q6 q7 q8 : prog := 
(CNOT q0 q3 ;; CNOT q0 q6 ;;
H q0 ;; H q3 ;; H q6 ;;
CNOT q0 q1 ;; CNOT q0 q2 ;;
CNOT q3 q4 ;; CNOT q3 q5 ;;
CNOT q6 q7 ;; CNOT q6 q8)%pg.


Example Shor9Z_solve : 
exists Placeholder,
@triple 9 (Cap ([
[(C1, [gZ; gI; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gI; gZ])]
])) (Shor9 0 1 2 3 4 5 6 7 8) (Placeholder).
Proof. solvePlaceholder_refl.
assumption.
Qed.


Example Shor9Z : 
@triple 9 (Cap ([
[(C1, [gZ; gI; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gI; gZ])]
])) (Shor9 0 1 2 3 4 5 6 7 8) (Cap ([
[(C1, [gX; gX; gX; gI; gI; gI; gI; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI])];
[(C1, [gX; gX; gX; gI; gI; gI; gX; gX; gX])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])]
])).
Proof. validate_refl.
Qed.


Example Shor9X_solve : 
exists Placeholder,
@triple 9 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gI; gZ])]
])) (Shor9 0 1 2 3 4 5 6 7 8) (Placeholder).
Proof. solvePlaceholder_refl.
assumption.
Qed.


Example Shor9X : 
@triple 9 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gI; gZ])]
])) (Shor9 0 1 2 3 4 5 6 7 8) (Cap ([
[(C1, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI])];
[(C1, [gX; gX; gX; gI; gI; gI; gX; gX; gX])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])]
])).
Proof. validate_refl.
Qed.


(** We can check if the normalization are equal. **)
Example equal_normalization_Shor9X :
(@normalize 0%nat 9
(map AtoT [
[(C1, [gZ; gI; gI; gZ; gI; gI; gZ; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gZ; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gX; gX; gX; gX; gX; gX; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gZ; gI; gI; gI])];
[(C1, [gX; gX; gX; gI; gI; gI; gX; gX; gX])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gZ])]
]) = normalize 0%nat XL').
Proof. solveNormalize.
reflexivity.
Qed.


Example Shor9X_normalization : 
@triple 9 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gI; gI; gZ])]
])) (Shor9 0 1 2 3 4 5 6 7 8) (Cap (
map TtoA (normalize 0%nat XL')
)).
Proof. validate_refl'_normalized 0%nat.
Qed.
