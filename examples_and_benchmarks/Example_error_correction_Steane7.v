Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(************* Steane code on 7 qubits *************)
(***************************************************)
(* 
g1 = IIIXXXX
g2 = IXXIIXX
g3 = XIXIXIX
g4 = IIIZZZZ
g5 = IZZIIZZ
g6 = ZIZIZIZ
Xb = XXXXXXX
Zb = ZZZZZZZ
Yb = -YYYYYYY

ZL := g1 ∩ ... ∩ g6 ∩ Zb
XL := g1 ∩ ... ∩ g6 ∩ Xb
YL := g1 ∩ ... ∩ g6 ∩ Yb
St7 := g1 ∩ ... ∩ g6

ZL = St7 ∩ Zb
XL = St7 ∩ Xb
YL = St7 ∩ Yb
*)

Definition g1 : TType 7 := (C1, [gI; gI; gI; gX; gX; gX; gX]).
Definition g2 : TType 7 := (C1, [gI; gX; gX; gI; gI; gX; gX]).
Definition g3 : TType 7 := (C1, [gX; gI; gX; gI; gX; gI; gX]).
Definition g4 : TType 7 := (C1, [gI; gI; gI; gZ; gZ; gZ; gZ]).
Definition g5 : TType 7 := (C1, [gI; gZ; gZ; gI; gI; gZ; gZ]).
Definition g6 : TType 7 := (C1, [gZ; gI; gZ; gI; gZ; gI; gZ]).
Definition Xbar : TType 7 := (C1, [gX; gX; gX; gX; gX; gX; gX]).
Definition Zbar : TType 7 := (C1, [gZ; gZ; gZ; gZ; gZ; gZ; gZ]).
Definition ZL : list (TType 7) := [g1; g2; g3; g4; g5; g6; Zbar].
Definition XL : list (TType 7) := [g1; g2; g3; g4; g5; g6; Xbar].


Definition Steane7 q0 q1 q2 q3 q4 q5 q6 : prog := 
(H q4 ;; H q5 ;; H q6 ;; 
CNOT q0 q1 ;; CNOT q0 q2 ;; 
CNOT q6 q0 ;; CNOT q6 q1 ;; CNOT q6 q3 ;; 
CNOT q5 q0 ;; CNOT q5 q2 ;; CNOT q5 q3 ;; 
CNOT q4 q1 ;; CNOT q4 q2 ;; CNOT q4 q3)%pg. 


Example Steane7Z_solve : 
exists Placeholder,
@triple 7 (Cap ([
[(C1, [gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ])]
])) (Steane7 0 1 2 3 4 5 6) (Placeholder).
Proof. solvePlaceholder_refl.
assumption.
Qed.


Example Steane7Z : 
@triple 7 (Cap ([
[(C1, [gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ])]
])) (Steane7 0 1 2 3 4 5 6) (Cap ([
[(C1, [gZ; gI; gI; gI; gI; gZ; gZ])];
[(C1, [gZ; gZ; gI; gI; gZ; gZ; gI])];
[(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])];
[(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])];
[(C1, [gI; gX; gX; gX; gX; gI; gI])];
[(C1, [gX; gI; gX; gX; gI; gX; gI])];
[(C1, [gX; gX; gI; gX; gI; gI; gX])]
])).
Proof. validate_refl.
Qed.

Example Steane7X_solve : 
exists Placeholder,
@triple 7 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ])]
])) (Steane7 0 1 2 3 4 5 6) (Placeholder).
Proof. solvePlaceholder_refl.
assumption.
Qed.


Example Steane7X : 
@triple 7 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ])]
])) (Steane7 0 1 2 3 4 5 6) (Cap ([
[(C1, [gX; gX; gX; gI; gI; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gZ; gZ; gI])];
[(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])];
[(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])];
[(C1, [gI; gX; gX; gX; gX; gI; gI])];
[(C1, [gX; gI; gX; gX; gI; gX; gI])];
[(C1, [gX; gX; gI; gX; gI; gI; gX])]
])).
Proof. validate_refl.
Qed.

(** We can check if the normalization are equal. **)
Example equal_normalization_Steane7X :
(@normalize 0%nat 7
(map AtoT [
[(C1, [gX; gX; gX; gI; gI; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gZ; gZ; gI])];
[(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])];
[(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])];
[(C1, [gI; gX; gX; gX; gX; gI; gI])];
[(C1, [gX; gI; gX; gX; gI; gX; gI])];
[(C1, [gX; gX; gI; gX; gI; gI; gX])]
]) = normalize 0%nat XL).
Proof. solveNormalize. 
reflexivity.
Qed.

Example Steane7X_normalization : 
@triple 7 (Cap ([
[(C1, [gX; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gZ])]
])) (Steane7 0 1 2 3 4 5 6) (Cap (
map TtoA (normalize 0%nat XL)
)).
Proof. validate_refl'_normalized 0%nat.
Qed.

