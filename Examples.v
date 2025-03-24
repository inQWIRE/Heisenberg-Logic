
Require Import HeisenbergFoundations.Automation.


(***************************************************)
(********************* Toffoli *********************)
(***************************************************)

Definition TOFFOLI (a b c : nat) :=
  H c ;; CNOT b c ;; Td c ;; CNOT a c ;; T c ;; CNOT b c ;; Td c ;; CNOT a c ;; T b ;; T c ;; H c ;; CNOT a b ;; T a ;; Td b ;; CNOT a b.


Example ZIITOFFOLI :
  {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }}.
Proof. time validate. Qed.

Example IZITOFFOLI :
  {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }}.
Proof. time validate. Qed.


Example IIZTOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gI; gI; gZ])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof. time solvePlaceholder.
(* time solvePlaceholder.
Tactic call ran for 60.051 secs (56.539u,1.708s) (success) *)
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
Proof. time validate. Qed.
(* time validate
Tactic call ran for 47.226 secs (44.475u,1.429s) (success) *)


Example XIITOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gX; gI; gI])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof. time solvePlaceholder.
(* time solvePlaceholder.
Tactic call ran for 32.674 secs (32.509u,0.09s) (success) *)
assumption.
Qed.


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
Proof. time validate. Qed.
(* time validate
Tactic call ran for 17.345 secs (17.035u,0.054s) (success) *)



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
XL := g1 ∩ ... ∩ g6 ∩ Xb *)
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

Compute map snd (normalize ZL). (*
[[gX; gI; gX; gI; gX; gI; gX];
 [gI; gX; gX; gI; gI; gX; gX];
 [gZ; gZ; gZ; gI; gI; gI; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gZ; gI; gI; gZ; gZ; gI; gI];
 [gI; gZ; gI; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)
Compute map snd (normalize LZ). (*
[[gX; gI; gX; gI; gX; gI; gX];
 [gI; gX; gX; gI; gI; gX; gX];
 [gZ; gZ; gZ; gI; gI; gI; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gZ; gI; gI; gZ; gZ; gI; gI];
 [gI; gZ; gI; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)

Compute map snd (normalize XL). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)
Compute map snd (normalize LX). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ]] *)

Compute map snd (normalize (XL ++ [(C1,  [gI; gI; gX; gI; gX; gX; gI])])). (*
[[gX; gI; gI; gI; gI; gX; gX];
 [gI; gX; gI; gI; gX; gI; gX];
 [gI; gI; gX; gI; gX; gX; gI];
 [gI; gI; gI; gX; gX; gX; gX];
 [gI; gZ; gZ; gZ; gZ; gI; gI];
 [gZ; gI; gZ; gZ; gI; gZ; gI];
 [gZ; gZ; gI; gZ; gI; gI; gZ];
 [gI; gI; gI; gI; gI; gI; gI]] *)

Compute map snd (normalize (removelast XL)). (*
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
Compute map snd (normalize Test'). (*
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
Compute map snd (normalize Test''). (*
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
Compute map snd (normalize Test'''). (*
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
Yb = YYYYYYY

ZL := g1 ∩ ... ∩ g6 ∩ Zb
XL := g1 ∩ ... ∩ g6 ∩ Xb
YL := g1 ∩ ... ∩ g6 ∩ Yb
St7 := g1 ∩ ... ∩ g6

ZL = St7 ∩ Zb
XL = St7 ∩ Xb
YL = St7 ∩ Yb

Definition g1 := @G 7 (F [(C1, [gI; gI; gI; gX; gX; gX; gX])]).
Definition g2 := @G 7 (F [(C1, [gI; gX; gX; gI; gI; gX; gX])]).
Definition g3 := @G 7 (F [(C1, [gX; gI; gX; gI; gX; gI; gX])]).
Definition g4 := @G 7 (F [(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])]).
Definition g5 := @G 7 (F [(C1, [gI; gZ; gZ; gI; gI; gZ; gZ])]).
Definition g6 := @G 7 (F [(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])]).
Definition Xbar := @G 7 (F [(C1, [gX; gX; gX; gX; gX; gX; gX])]).
Definition Zbar := @G 7 (F [(C1, [gZ; gZ; gZ; gZ; gZ; gZ; gZ])]).
*)

Definition Steane7 q0 q1 q2 q3 q4 q5 q6 := 
H q4 ;; H q5 ;; H q6 ;; 
CNOT q0 q1 ;; CNOT q0 q2 ;; 
CNOT q6 q0 ;; CNOT q6 q1 ;; CNOT q6 q3 ;; 
CNOT q5 q0 ;; CNOT q5 q2 ;; CNOT q5 q3 ;; 
CNOT q4 q1 ;; CNOT q4 q2 ;; CNOT q4 q3. 

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


(* [(C1, [gZ; gI; gI; gI; gI; gZ; gZ])];
[(C1, [gZ; gZ; gI; gI; gZ; gZ; gI])];
[(C1, [gZ; gI; gZ; gI; gZ; gI; gZ])];
[(C1, [gI; gI; gI; gZ; gZ; gZ; gZ])];
[(C1, [gI; gX; gX; gX; gX; gI; gI])];
[(C1, [gX; gI; gX; gX; gI; gX; gI])];
[(C1, [gX; gX; gI; gX; gI; gI; gX])] *)
])).
Proof. time validate. Qed.
(* time validate
Tactic call ran for 18.646 secs (17.973u,0.353s) (success) *)


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
Proof. time solvePlaceholder.
(* time solvePlaceholder.
Tactic call ran for 17.471 secs (16.808u,0.27s) (success) *)
assumption.
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
Compute separable (normalize Test') [0; 1; 3]%nat. (* false *)

(* normalize Test''
[[gZ; gI; gI];
 [gI; gY; gZ];
 [gI; gZ; gX]] *)
Compute separable (normalize Test'') [1; 2]%nat. (* true *)
Compute separable (normalize Test'') [0; 2]%nat. (* false *)

(* normalize Test'''
[[gY; gZ; gI; gI];
 [gZ; gX; gI; gI];
 [gI; gI; gY; gZ];
 [gI; gI; gZ; gY]] *)
Compute separable (normalize Test''') [0; 1]%nat. (* true *)
Compute separable (normalize Test''') [0; 2]%nat. (* false *)
Compute separable (normalize Test''') [1; 2]%nat. (* false *)
Compute separable (normalize Test''') [0; 3]%nat. (* false *)
Compute separable (normalize Test''') [0; 2; 3]%nat. (* false *)







(***************************************************)
(************** Separability Examples **************)
(***************************************************)

Example separation_test :
{{ @Cap 4 (map TtoA ( normalize
[(C1, [gY; gI; gZ; gI]); 
(C1, [gI; gY; gI; gZ]);
(C1, [gZ; gI; gX; gI]);
(C1, [gI; gZ; gI; gY])] )) }}
H 0 ;; H 0
{{ @Sep 4 (@separate 4 ( normalize
[(C1, [gY; gI; gZ; gI]); 
(C1, [gI; gY; gI; gZ]);
(C1, [gZ; gI; gX; gI]);
(C1, [gI; gZ; gI; gY])]
) [[0; 2]; [1; 3]]%nat) }}.
Proof. time validateCaptoSep. 
(* time validateCaptoSep
Tactic call ran for 0.522 secs (0.497u,0.013s) (success) *)
Qed.


(* map snd (normalize Test')
[[gY; gZ; gI; gI; gI; gI; gI]; 
 [gZ; gX; gI; gI; gI; gI; gI];
 [gI; gI; gX; gZ; gZ; gI; gI]; 
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI]; 
 [gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX]] *)
Compute map snd (normalize Test').
Compute separable (normalize Test') [2; 3; 4]%nat.
Compute separable (normalize Test') [0; 1]%nat.
Compute separable (normalize Test') [5; 6]%nat.
Compute separable_all (normalize Test') [[2; 3; 4]; [0;1]; [5;6]]%nat.





Example separation_test2 :
{{ Cap (map TtoA (normalize Test')) }}
H 0 ;; H 0
{{ Sep (separate (normalize Test') [[2; 3; 4]; [0;1]; [5;6]]%nat) }}.
Proof. time validateCaptoSep.
(* time validateCaptoSep.
Tactic call ran for 7.411 secs (6.551u,0.452s) (success) *)
Qed.





(***************************************************)
(******************* Graph States *******************)
(***************************************************)


Definition CZ q0 q1 := H q1 ;; CNOT q0 q1 ;; H q1.

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


Ltac unfoldGraphState :=
  unfold  graph_init, nat_to_X_i, graph_to_Predicate, graph_to_stabilizers, vertex_edges_to_stabilizer, edges_to_CZ, TtoA; simpl.

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


Lemma TestGraphState0 : 
exists Placeholder,
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ Placeholder }}.
Proof. unfoldGraphState.
  time solvePlaceholder.
  assumption.
Qed.

Compute @normalize 3 [(C1, [gZ; gX; gZ]); (C1, [gI; gZ; gX]); (C1, [gX; gZ; gI])].


Lemma TestGraphState1 : 
{{ graph_init 3 }} 
edges_to_CZ [ (0, 1); (1, 2) ]%nat
{{ graph_to_Predicate 3 [ (0, 1); (1, 2) ]%nat }}.
Proof. unfoldGraphState.
  time validate.
Qed.

Lemma TestGraphState2 : (* complete graph K3 in 10 qubits *)
{{ graph_init 10 }} 
edges_to_CZ [ (0, 1); (0, 2); (1, 2)]%nat
{{ graph_to_Predicate 10 [ (0, 1); (0, 2); (1, 2)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 9.833 secs (7.683u,0.791s) (success) *)
Qed.

Lemma TestGraphState3 :  (* complete graph K5 in 5 qubits *)
{{ graph_init 5 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 5 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 10.225 secs (9.296u,0.365s) (success) *)
Qed.

Lemma TestGraphState4 :  (* complete graph K5 in 10 qubits *)
{{ graph_init 10 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 10 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 26.271 secs (24.517u,0.744s) (success) *)
Qed.

Lemma TestGraphState5 :  (* complete graph K10 in 10 qubits *)
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
  time validate.
(* Tactic call ran for 128.407 secs (118.935u,4.08s) (success) *)
Qed.

Lemma TestGraphState6 :  (* complete graph K5 in 15 qubits *)
{{ graph_init 15 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 15 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 60.459 secs (56.59u,1.244s) (success) *)
Qed.

Lemma TestGraphState7 :  (* complete graph K5 in 20 qubits *)
{{ graph_init 20 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 20 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 118.262 secs (108.817u,3.359s) (success) *)
Qed.

Lemma TestGraphState8 :  (* complete graph K5 in 25 qubits *)
{{ graph_init 25 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 25 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 194.406 secs (180.787u,5.28s) (success) *)
Qed.

Lemma TestGraphState9 :  (* complete graph K5 in 30 qubits *)
{{ graph_init 30 }}
edges_to_CZ [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat
{{ graph_to_Predicate 30 [(0,1); (0,2); (0,3); (0,4); (1,2); (1,3); (1,4); (2,3); (2,4); (3,4)]%nat }}.
Proof. unfoldGraphState.
  time validate.
(* Tactic call ran for 337.781 secs (305.632u,10.749s) (success) *)
Qed.




(** time complexity seems to be larger than the number of qubits squared (~ n^2 log n)
time complexity seems to be linear in the number of edges **)



