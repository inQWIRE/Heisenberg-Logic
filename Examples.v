Require Import HeisenbergFoundations.ReflexiveAutomation.


(***************************************************)
(********************* Toffoli *********************)
(***************************************************)

(** Here for reference:
Definition Td (n : nat) := Z n ;; S n ;; T n. **)

Definition TOFFOLI (a b c : nat) :=
  H c ;; CNOT b c ;; Td c ;; CNOT a c ;; T c ;; CNOT b c ;; Td c ;; CNOT a c ;; T b ;; T c ;; H c ;; CNOT a b ;; T a ;; Td b ;; CNOT a b.


Example ZIITOFFOLI :
  {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }}.
Proof. time validate_refl'. Qed.

Example IZITOFFOLI :
  {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }}.
Proof. time validate_refl'. Qed.

Example IIXTOFFOLI :
  {{ @AtoPred 3 [(C1, [gI; gI; gX])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gI; gI; gX])] }}.
Proof. time validate_refl'. Qed.

Example IIZTOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gI; gI; gZ])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof.
time solvePlaceholder_refl.
assumption.
Qed.


Example IIZTOFFOLI : 
{{ @AtoPred 3 [(C1, [gI; gI; gZ])] }} TOFFOLI 0 1 2 {{ @AtoPred 3  
           [((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gZ; gZ]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gZ; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gZ; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gZ; gZ]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gI; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gI; gZ]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gI; gZ]);
            ((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gI; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gI; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gI; gZ]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gI; gZ]);
            ((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gI; gY]);
            ((C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gZ; gZ]);
            ((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gI; gZ; gY]);
            ((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gZ; gY]);
            ((- C1 / (√ 2 * √ 2 * √ 2 * √ 2))%C, [gZ; gZ; gZ])]
 }}.
Proof. time validate_refl'. Qed.


Example XIITOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gX; gI; gI])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof.
time solvePlaceholder_refl.
assumption.
Qed.

Local Open Scope C_scope.

Example XIITOFFOLI : 
{{ @AtoPred 3 [(C1, [gX; gI; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3  
        [(- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gZ; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gI; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gZ; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gI; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gZ; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gI; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gZ; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gI; gI]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gI; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gZ; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gI; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gZ; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gI; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gZ; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gY; gI; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gX; gZ; gX])]
 }}.
Proof. validate_refl'. Qed.


Example IXITOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gI; gX; gI])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof.
time solvePlaceholder_refl.
assumption.
Qed.

Example IXITOFFOLI :
{{ @AtoPred 3 [(C1, [gI; gX; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3  
      [(- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gX; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gY; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gY; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gX; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gY; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gX; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gX; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gY; gI]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gY; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gX; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gX; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gY; gI]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gX; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gY; gX]);
         (C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gI; gY; gX]);
         (- C1 / (√ 2 * √ 2 * √ 2 * √ 2), [gZ; gX; gX])]
}}.
Proof. time validate_refl'. Qed.



(***************************************************)
(** ** Normalization example on 7 qubit Steane code ** **)
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
ZL := g1 ∩ ... ∩ g6 ∩ Zb
XL := g1 ∩ ... ∩ g6 ∩ Xb 
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

Definition X1' : TType 7 := (C1, [gX; gX; gX; gI; gI; gI; gI]).
Definition Z1' : TType 7 := (C1, [gZ; gI; gI; gI; gI; gZ; gZ]).
Definition Z2' : TType 7 := (C1, [gZ; gZ; gI; gI; gZ; gZ; gI]).
Definition Z3' : TType 7 := (C1, [gZ; gI; gZ; gI; gZ; gI; gZ]).
Definition Z4' : TType 7 := (C1, [gI; gI; gI; gZ; gZ; gZ; gZ]).
Definition Z5' : TType 7 := (C1, [gI; gX; gX; gX; gX; gI; gI]).
Definition Z6' : TType 7 := (C1, [gX; gI; gX; gX; gI; gX; gI]).
Definition Z7' : TType 7 := (C1, [gX; gX; gI; gX; gI; gI; gX]).
Definition LZ : list (TType 7) := [Z1'; Z2'; Z3'; Z4'; Z5'; Z6'; Z7'].
Definition LX : list (TType 7) := [X1'; Z2'; Z3'; Z4'; Z5'; Z6'; Z7'].



(** Some normalization tests **)

Compute map snd (normalize 0%nat ZL). (*
[[gX; gI; gX; gI; gX; gI; gX];
 [gI; gX; gX; gI; gI; gX; gX];
 [gZ; gZ; gZ; gI; gI; gI; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gZ; gI; gI; gZ; gZ; gI; gI];
 [gI; gZ; gI; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)
Compute map snd (normalize 0%nat LZ). (*
[[gX; gI; gX; gI; gX; gI; gX];
 [gI; gX; gX; gI; gI; gX; gX];
 [gZ; gZ; gZ; gI; gI; gI; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gZ; gI; gI; gZ; gZ; gI; gI];
 [gI; gZ; gI; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)

Compute map snd (normalize 0%nat XL). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)
Compute map snd (normalize 0%nat LX). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)

Compute map snd (normalize 0%nat (XL ++ [(C1,  [gI; gI; gX; gI; gX; gX; gI])])). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ];
 [gI; gI; gI; gI; gI; gI; gI]] *)

Compute map snd (normalize 0%nat (removelast XL)). (*
[[gX; gI; gX; gI; gX; gI; gX];
 [gI; gX; gX; gI; gI; gX; gX];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gZ; gZ; gI; gI; gZ; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)



Definition t1' : TType 7 := (C1, [gI; gI; gI; gI; gI; gY; gZ]).
Definition t2' : TType 7 := (C1, [gI; gI; gI; gI; gI; gZ; gX]).
Definition t3' : TType 7 := (C1, [gI; gI; gZ; gX; gZ; gI; gI]).
Definition t4' : TType 7 := (C1, [gI; gI; gZ; gZ; gY; gI; gI]).
Definition t5' : TType 7 := (C1, [gI; gI; gX; gX; gY; gI; gI]).
Definition t6' : TType 7 := (C1, [gX; gY; gI; gI; gI; gI; gI]).
Definition t7' : TType 7 := (C1, [gZ; gX; gI; gI; gI; gI; gI]).
Definition Test' : list (TType 7) := [t1'; t2'; t3'; t4'; t5'; t6'; t7'].

(* Test
[[gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX];
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI];
 [gI; gI; gX; gX; gY; gI; gI];
 [gX; gY; gI; gI; gI; gI; gI];
 [gZ; gX; gI; gI; gI; gI; gI] *)
Compute map snd (normalize 0%nat Test'). (*
[[gY; gZ; gI; gI; gI; gI; gI];
 [gZ; gX; gI; gI; gI; gI; gI];
 [gI; gI; gX; gZ; gZ; gI; gI];
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI];
 [gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX]] *)

Definition t1'' : TType 3 := (C1, [gI; gZ; gX]).
Definition t2'' : TType 3 := (C1, [gI; gY; gZ]).
Definition t3'' : TType 3 := (C1, [gZ; gI; gI]).
Definition Test'' : list (TType 3) := [t1''; t2''; t3''].

(* Test'
[[gI; gZ; gX];
 [gI; gY; gZ];
 [gZ; gI; gI]] *)
Compute map snd (normalize 0%nat Test''). (*
[[gZ; gI; gI];
 [gI; gY; gZ];
 [gI; gZ; gX]] *)

Definition t1''' : TType 4 := (C1, [gI; gI; gX; gX]).
Definition t2''' : TType 4 := (C1, [gI; gI; gZ; gY]).
Definition t3''' : TType 4 := (C1, [gY; gZ; gI; gI]).
Definition t4''' : TType 4 := (C1, [gZ; gX; gI; gI]).
Definition Test''' : list (TType 4) := [t1'''; t2'''; t3'''; t4'''].

(* Test''
[[gI; gZ; gX; gX];
 [gI; gI; gZ; gY];
 [gY; gZ; gI; gZ];
 [gZ; gX; gI; gI]] *)
Compute map snd (normalize 0%nat Test'''). (*
[[gY; gZ; gI; gI];
 [gZ; gX; gI; gI];
 [gI; gI; gY; gZ];
 [gI; gI; gZ; gY]] *)








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
*)

Definition Steane7 (q0 q1 q2 q3 q4 q5 q6 : nat) := 
H q4 ;; H q5 ;; H q6 ;; 
CNOT q0 q1 ;; CNOT q0 q2 ;; 
CNOT q6 q0 ;; CNOT q6 q1 ;; CNOT q6 q3 ;; 
CNOT q5 q0 ;; CNOT q5 q2 ;; CNOT q5 q3 ;; 
CNOT q4 q1 ;; CNOT q4 q2 ;; CNOT q4 q3 . 


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
Proof.
solvePlaceholder_refl.
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
Proof. time validate_refl'. Qed.


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
Proof. time solvePlaceholder_refl.
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
])) (Steane7 0 1 2 3 4 5 6) (Cap (normalizeA 0%nat
[
[(C1, [gX; gX; gX; gI; gI; gI; gI])];
[(C1, [gZ; gZ; gI; gI; gZ; gZ; gI])];
[(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])];
[(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])];
[(C1, [gI; gX; gX; gX; gX; gI; gI])];
[(C1, [gX; gI; gX; gX; gI; gX; gI])];
[(C1, [gX; gX; gI; gX; gI; gI; gX])]
])).
Proof. time validate_refl'_normalized. Qed.




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


Definition Shor9 q0 q1 q2 q3 q4 q5 q6 q7 q8 := 
CNOT q0 q3 ;; CNOT q0 q6 ;;
H q0 ;; H q3 ;; H q6 ;;
CNOT q0 q1 ;; CNOT q0 q2 ;;
CNOT q3 q4 ;; CNOT q3 q5 ;;
CNOT q6 q7 ;; CNOT q6 q8.


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
Proof. time solvePlaceholder_refl.
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
Proof. time validate_refl'. Qed.


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
Proof. 
time solvePlaceholder_refl.
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
Proof. time validate_refl'. Qed.



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
Proof. time solveNormalize. reflexivity. Qed.

Example Shor9X_normalization : 
@triple 9 (Cap (@normalizeA 0%nat 9%nat [
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
Proof. time validate_refl'_normalized.
 
(* rewrite <- equal_normalization_Shor9X.
  apply normalization_admissible;
    [repeat constructor; WF_auto | validate]. *)
Qed.


(***************************************************)
(*********** Separability Function Tests ***********)
(***************************************************)


(** To specify a valid eigenspace, we need independent commuting terms **)
(** Since we are mapping valid terms to valid terms, the checks need not be necessary **)
(* normalize Test'
[[gY; gZ; gI; gI; gI; gI; gI];
 [gZ; gX; gI; gI; gI; gI; gI];
 [gI; gI; gX; gZ; gZ; gI; gI];
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI];
 [gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX]] *)
Compute separable (normalize 0%nat Test') [0; 1; 3]%nat. (* false *)

(* normalize Test''
[[gZ; gI; gI];
 [gI; gY; gZ];
 [gI; gZ; gX]] *)
Compute separable (normalize 0%nat Test'') [1; 2]%nat. (* true *)
Compute separable (normalize 0%nat Test'') [0; 2]%nat. (* false *)

(* normalize Test'''
[[gY; gZ; gI; gI];
 [gZ; gX; gI; gI];
 [gI; gI; gY; gZ];
 [gI; gI; gZ; gY]] *)
Compute separable (normalize 0%nat Test''') [0; 1]%nat. (* true *)
Compute separable (normalize 0%nat Test''') [0; 2]%nat. (* false *)
Compute separable (normalize 0%nat Test''') [1; 2]%nat. (* false *)
Compute separable (normalize 0%nat Test''') [0; 3]%nat. (* false *)
Compute separable (normalize 0%nat Test''') [0; 2; 3]%nat. (* false *)







(***************************************************)
(************** Separability Examples **************)
(***************************************************)

Example separation_test :
{{ @Cap 4 (map TtoA ( normalize 0%nat 
[(C1, [gY; gI; gZ; gI]); 
(C1, [gI; gY; gI; gZ]);
(C1, [gZ; gI; gX; gI]);
(C1, [gI; gZ; gI; gY])] )) }}
H 0 ;; H 0
{{ @Sep 4 (@separate 4 ( normalize 0%nat 
[(C1, [gY; gI; gZ; gI]); 
(C1, [gI; gY; gI; gZ]);
(C1, [gZ; gI; gX; gI]);
(C1, [gI; gZ; gI; gY])]
) [[0; 2]; [1; 3]]%nat) }}.
Proof.
time validate_refl'_normalized.
Qed.


(* map snd (normalize Test')
[[gY; gZ; gI; gI; gI; gI; gI]; 
 [gZ; gX; gI; gI; gI; gI; gI];
 [gI; gI; gX; gZ; gZ; gI; gI]; 
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI]; 
 [gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX]] *)
Compute map snd (normalize 0%nat Test').
Compute separable (normalize 0%nat Test') [2; 3; 4]%nat.
Compute separable (normalize 0%nat Test') [0; 1]%nat.
Compute separable (normalize 0%nat Test') [5; 6]%nat.
Compute separable_all (normalize 0%nat Test') [[2; 3; 4]; [0;1]; [5;6]]%nat.


Example separation_test2 :
{{ Cap (map TtoA (normalize 0%nat Test')) }}
H 0 ;; H 0
{{ Sep (separate (normalize 0%nat Test') [[2; 3; 4]; [0;1]; [5;6]]%nat) }}.
Proof. 
time validate_refl'_normalized.
Qed.


Example separation_test2' :
{{ Cap (map TtoA (Test')) }}
H 0 ;; H 0
{{ Sep (separate (Test') [[2; 3; 4]; [0;1]; [5;6]]%nat) }}.
Proof. 
time validate_refl'.
Qed.

Compute @separate 7 [(C1,[gI; gI; gI; gI; gI; gZ; gI])] [[5%nat]; [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 6%nat]].


Example separation_test3 :
exists Placeholder,
{{ @AtoPred 7 [(C1,[gI; gI; gI; gI; gI; gZ; gI])]
(*@Cap 7 [
 [(C1, [gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gX])]
] *) }}
X 0 ;; X 1 ;; X 3 ;; X 4 ;; TOFFOLI 0 1 2 ;; TOFFOLI 3 4 5 ;; X 0 ;; X 1 ;; X 2 ;; X 3 ;; X 4 ;; X 5 ;; TOFFOLI 2 5 6 ;; X 5 ;; X 4 ;; X 3 ;; X 2 ;; X 1 ;; X 0 ;; TOFFOLI 3 4 5 ;; TOFFOLI 0 1 2 ;; X 4 ;; X 3 ;; X 1 ;; X 0
{{ Placeholder }}.
Proof. time solvePlaceholder_refl.
assumption.
Qed.


Example separation_test3' :
{{ @AtoPred 7 [(C1,[gI; gI; gI; gI; gI; gZ; gI])]
(*@Cap 7 [
 [(C1, [gZ; gI; gI; gI; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI; gI; gI; gI])];
[(C1, [gI; gI; gZ; gI; gI; gI; gI])];
[(C1, [gI; gI; gI; gZ; gI; gI; gI])];
[(C1, [gI; gI; gI; gI; gZ; gI; gI])];
[(C1, [gI; gI; gI; gI; gI; gZ; gI])];
[(C1, [gI; gI; gI; gI; gI; gI; gX])]
] *) }}
X 0 ;; X 1 ;; X 3 ;; X 4 ;; TOFFOLI 0 1 2 ;; TOFFOLI 3 4 5 ;; X 0 ;; X 1 ;; X 2 ;; X 3 ;; X 4 ;; X 5 ;; TOFFOLI 2 5 6 ;; X 5 ;; X 4 ;; X 3 ;; X 2 ;; X 1 ;; X 0 ;; TOFFOLI 3 4 5 ;; TOFFOLI 0 1 2 ;; X 4 ;; X 3 ;; X 1 ;; X 0
{{ Sep (@separate 7 [(C1,[gI; gI; gI; gI; gI; gZ; gI])] [[5%nat]; [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 6%nat]]) }}.
Proof. time validate_refl'.
Qed.




Example separation_test4 :
exists Placeholder,
{{ @Cap 4 [
[(- C1, [gZ; gI; gI; gI])];
[(- C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gZ])]
] }}
TOFFOLI 0 1 3 ;; CNOT 3 2 ;; TOFFOLI 0 1 3 ;; CNOT 0 1
{{ Placeholder }}.
Proof. time solvePlaceholder_refl_normalized.
assumption.
Qed.

Example separation_test4' :
{{ @Cap 4 [
[(C1, [gZ; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gX])]
] }}
TOFFOLI 0 1 3 ;; CNOT 3 2 ;; TOFFOLI 0 1 3 ;; CNOT 0 1
{{ Sep (@separate 4 (map AtoT [
[(C1, [gZ; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gX])]
]) [[0]; [1]; [2]; [3]]%nat) }}.
Proof. (* simpl; cbv [separate]; simpl; cbv [ForgetT unpad_Sep_TType]; simpl. *)
time validate_refl'_normalized. Qed.

Example separation_test4'' :
exists Placeholder,
{{ @Cap 4 [
[(- C1, [gZ; gI; gI; gI])];
[(- C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gX])]
] }}
TOFFOLI 0 1 3 ;; CNOT 3 2 ;; TOFFOLI 0 1 3 ;; CNOT 0 1
{{ Placeholder }}.
Proof. time solvePlaceholder_refl_normalized.
assumption.
Qed.

Example separation_test4''' :
{{ @Cap 4 [
[(C1, [gZ; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gZ])]
] }}
TOFFOLI 0 1 3 ;; CNOT 3 2 ;; TOFFOLI 0 1 3 ;; CNOT 0 1
{{ Sep (@separate 4 (map AtoT [
[(C1, [gZ; gI; gI; gI])];
[(C1, [gI; gZ; gI; gI])];
[(C1, [gI; gI; gX; gI])];
[(C1, [gI; gI; gI; gZ])]
]) [[0]; [1]; [2]; [3]]%nat) }}.
Proof. (* simpl; cbv [separate]; simpl; cbv [ForgetT unpad_Sep_TType]; simpl. *)
time validate_refl'_normalized.
Qed.


(***************************************************)
(******************* Graph States *******************)
(***************************************************)

Definition CZ q0 q1 := H q1 ;; CNOT q0 q1 ;; H q1.

(* TODO: I-only condition in validate_refl*)
Lemma IICZII : {{ pII }} CZ 0 1 {{ pII }}.
Proof. validate. Qed.

Lemma XICZXZ : {{ pXI }} CZ 0 1 {{ pXZ }}.
Proof. validate_refl'. Qed.

Lemma IXCZZX : {{ pIX }} CZ 0 1 {{ pZX }}.
Proof. validate_refl'. Qed.

Lemma XXCZYY : {{ pXX }} CZ 0 1 {{ pYY }}.
Proof. validate_refl'. Qed.

Lemma YICZYZ : {{ pYI }} CZ 0 1 {{ pYZ }}.
Proof. validate_refl'. Qed.

Lemma IYCZZY : {{ pIY }} CZ 0 1 {{ pZY }}.
Proof. validate_refl'. Qed.

Lemma YYCZXX : {{ pYY }} CZ 0 1 {{ pXX }}.
Proof. validate_refl'. Qed.

Lemma YXCZmXY : {{ pYX }} CZ 0 1 {{ mpXY }}.
Proof. validate_refl'. Qed.

Lemma XYCZmYX : {{ pXY }} CZ 0 1 {{ mpYX }}.
Proof. validate_refl'. Qed.

Lemma ZYCZIY : {{ pZY }} CZ 0 1 {{ pIY }}.
Proof. validate_refl'. Qed.

Lemma YZCZYI : {{ pYZ }} CZ 0 1 {{ pYI }}.
Proof. validate_refl'. Qed.

Lemma XZCZXI : {{ pXZ }} CZ 0 1 {{ pXI }}.
Proof. validate_refl'. Qed.

Lemma ZXCZIX : {{ pZX }} CZ 0 1 {{ pIX }}.
Proof. validate_refl'. Qed.

Lemma ZICZZI : {{ pZI }} CZ 0 1 {{ pZI }}.
Proof. validate_refl'. Qed.

Lemma IZCZIZ : {{ pIZ }} CZ 0 1 {{ pIZ }}.
Proof. validate_refl'. Qed.

Lemma ZZCZZZ : {{ pZZ }} CZ 0 1 {{ pZZ }}.
Proof. validate_refl'. Qed.

#[export] Hint Resolve IICZII XICZXZ IXCZZX XXCZYY YICZYZ IYCZZY YYCZXX YXCZmXY XYCZmYX ZYCZIY YZCZYI XZCZXI ZXCZIX ZICZZI IZCZIZ ZZCZZZ : ht_db. 




(*
n = 3
edges = [ (0, 1); (1, 2) ]
*) 

Fixpoint edges_to_CZ_loop (progs : list prog) (last_prog : prog) : prog :=
  match progs with 
  | h :: t => h ;; (edges_to_CZ_loop t last_prog)
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

(*
Lemma GraphState_compute_postcond : 
Lemma compute_postcond_CAP : forall {n : nat} (g : prog) (lt : list (TType n)),
    nonadditive_prog g -> prog_bound n g -> Forall WF_TType lt ->
    {{ Cap (map TtoA lt) }} g {{ Cap (map (fun t => TtoA (prog_on_TType g t)) lt) }}.
Proof. intros n g lt H0 H1 H2.
  apply CAP'. 
  induction lt; auto.
  rewrite Forall_cons_iff in H2. destruct H2. specialize (IHlt H3).
  constructor; auto.
  apply compute_postcond; auto.
Qed.
*)




Lemma TestGraphState :
exists Placeholder,
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ Placeholder }}.
Proof. unfoldGraphState.
time solvePlaceholder_refl.
assumption.
Qed.


Eval lazy -[Cplus Cminus Cmult Cdiv Cinv RtoC sqrt Q2R IZR QC2C Cexp PI sin cos atype_eq Copp triple pred_eq] in @normalize 0%nat 3 [(C1, [gZ; gX; gZ]); (C1, [gI; gZ; gX]); (C1, [gX; gZ; gI])].


Lemma TestGraphState' : 
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ graph_to_Predicate 3 [ (0, 1); (1, 2) ]%nat }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma TestGraphState'' : (* complete graph K3 in 10 qubits *)
{{ graph_init 10 }} 
edges_to_CZ [ (0, 1); (0, 2); (1, 2)]%nat
{{ graph_to_Predicate 10 [ (0, 1); (0, 2); (1, 2)]%nat }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.




(** ** Simple benchmark by varying the number of qubits ** **)

Lemma Benchmark_varyGates_K5_q10 :  
(* complete graph K5 (= 3*10 = 30 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 5
) {{ graph_to_Predicate 10 
( complete_graph_edges 5
) }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyGates_K6_q10 :  
(* complete graph K6 (= 3*15 = 45 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 6
) {{ graph_to_Predicate 10 
( complete_graph_edges 6
) }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyGates_K7_q10 :  
(* complete graph K7 (= 3*21 = 63 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 7
) {{ graph_to_Predicate 10 
( complete_graph_edges 7
) }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyGates_K8_q10 :  
(* complete graph K8 (= 3*28 = 84 Gates) in 10 qubits *)
{{ graph_init 10
}} edges_to_CZ ( complete_graph_edges 8
) {{ graph_to_Predicate 10 
( complete_graph_edges 8
) }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyGates_K9_q10 :  
(* complete graph K9 (= 3*36 = 108 Gates) in 10 qubits *)
{{ graph_init 10 }}
edges_to_CZ
[(0,1); (0,2); (0,3); (0,4); (0,5); (0,6); (0,7); (0,8);
 (1,2); (1,3); (1,4); (1,5); (1,6); (1,7); (1,8);
 (2,3); (2,4); (2,5); (2,6); (2,7); (2,8);
 (3,4); (3,5); (3,6); (3,7); (3,8);
 (4,5); (4,6); (4,7); (4,8);
 (5,6); (5,7); (5,8);
 (6,7); (6,8);
 (7,8)]%nat
{{ graph_to_Predicate 10
[(0,1); (0,2); (0,3); (0,4); (0,5); (0,6); (0,7); (0,8);
 (1,2); (1,3); (1,4); (1,5); (1,6); (1,7); (1,8);
 (2,3); (2,4); (2,5); (2,6); (2,7); (2,8);
 (3,4); (3,5); (3,6); (3,7); (3,8);
 (4,5); (4,6); (4,7); (4,8);
 (5,6); (5,7); (5,8);
 (6,7); (6,8);
 (7,8)]%nat
 }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyGates_K10_q10 :  
(* complete graph K10 (= 3*45 = 135 Gates) in 10 qubits *)
{{ graph_init 10 }}
edges_to_CZ
[(0,1); (0,2); (0,3); (0,4); (0,5); (0,6); (0,7); (0,8); (0,9);
 (1,2); (1,3); (1,4); (1,5); (1,6); (1,7); (1,8); (1,9);
 (2,3); (2,4); (2,5); (2,6); (2,7); (2,8); (2,9);
 (3,4); (3,5); (3,6); (3,7); (3,8); (3,9);
 (4,5); (4,6); (4,7); (4,8); (4,9);
 (5,6); (5,7); (5,8); (5,9);
 (6,7); (6,8); (6,9);
 (7,8); (7,9);
 (8,9)]%nat
{{ graph_to_Predicate 10
[(0,1); (0,2); (0,3); (0,4); (0,5); (0,6); (0,7); (0,8); (0,9);
 (1,2); (1,3); (1,4); (1,5); (1,6); (1,7); (1,8); (1,9);
 (2,3); (2,4); (2,5); (2,6); (2,7); (2,8); (2,9);
 (3,4); (3,5); (3,6); (3,7); (3,8); (3,9);
 (4,5); (4,6); (4,7); (4,8); (4,9);
 (5,6); (5,7); (5,8); (5,9);
 (6,7); (6,8); (6,9);
 (7,8); (7,9);
 (8,9)]%nat
 }}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.




(** ** Benchmark by Graph States ** **)

Lemma Benchmark_varyQubits_K5_q5 :  (* complete graph K5 in 5 qubits *)
{{ graph_init 5 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 5 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyQubits_K5_q10 :  (* complete graph K5 in 10 qubits *)
{{ graph_init 10 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 10
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyQubits_K5_q15 :  (* complete graph K5 in 15 qubits *)
{{ graph_init 15 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 15
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyQubits_K5_q20 :  (* complete graph K5 in 20 qubits *)
{{ graph_init 20 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 20
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyQubits_K5_q25 :  (* complete graph K5 in 25 qubits *)
{{ graph_init 25 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 25
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.

Lemma Benchmark_varyQubits_K5_q30 :  (* complete graph K5 in 30 qubits *)
{{ graph_init 30 }}
edges_to_CZ 
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat
{{ graph_to_Predicate 30
[(0,1); (0,2); (0,3); (0,4); 
(1,2); (1,3); (1,4); 
(2,3); (2,4); 
(3,4)]%nat 
}}.
Proof. unfoldGraphState.
time validate_refl'.
Qed.




(** time complexity seems to be larger than the number of qubits squared (~ n^2 log n)
time complexity seems to be linear in the number of gates **)




(** ** Benchmark by n-qubit GHZ state ** **)

Fixpoint CNOTchain (n i : nat) : prog :=
  match i with
  | 0 => CNOT (n-1)%nat n
  | s i' => CNOT (n - i - 1)%nat (n - i)%nat ;; CNOTchain n i'
  end.

(** Works for n >= 2 **)
Definition GHZ (n : nat) : prog := H 0 ;; CNOTchain (n - 1)%nat (n - 2)%nat.

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
assumption.
Qed.




(** ** Benchmark by T Gates ** **)

Fixpoint Trepeat (n : nat) : prog :=
  match n with
  | 0 => T 0
  | s n' => T 0 ;; Trepeat n'
  end.

Definition Ts (n : nat) : prog := Trepeat (n - 1)%nat.

Compute Trepeat 3.
Compute Ts 3.





Lemma Benchmark_T1 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 1
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T2 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 2
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T3 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 3
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T4 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 4
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T5 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 5
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T6 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 6
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.

Lemma Benchmark_T7 :
exists Placeholder,
{{ @AtoPred 1 ([
(C1, [gX])
])}}
Ts 7
{{ Placeholder }} .
Proof. unfold Ts; simpl.
time solvePlaceholder_refl.
assumption.
Qed.


