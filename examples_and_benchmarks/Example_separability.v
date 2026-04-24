Require Import HeisenbergFoundations.ReflexiveAutomation.


Definition t1' : TType 7 := (C1, [gI; gI; gI; gI; gI; gY; gZ]).
Definition t2' : TType 7 := (C1, [gI; gI; gI; gI; gI; gZ; gX]).
Definition t3' : TType 7 := (C1, [gI; gI; gZ; gX; gZ; gI; gI]).
Definition t4' : TType 7 := (C1, [gI; gI; gZ; gZ; gY; gI; gI]).
Definition t5' : TType 7 := (C1, [gI; gI; gX; gX; gY; gI; gI]).
Definition t6' : TType 7 := (C1, [gX; gY; gI; gI; gI; gI; gI]).
Definition t7' : TType 7 := (C1, [gZ; gX; gI; gI; gI; gI; gI]).
Definition Test' : list (TType 7) := [t1'; t2'; t3'; t4'; t5'; t6'; t7'].


Definition t1'' : TType 3 := (C1, [gI; gZ; gX]).
Definition t2'' : TType 3 := (C1, [gI; gY; gZ]).
Definition t3'' : TType 3 := (C1, [gZ; gI; gI]).
Definition Test'' : list (TType 3) := [t1''; t2''; t3''].


Definition t1''' : TType 4 := (C1, [gI; gI; gX; gX]).
Definition t2''' : TType 4 := (C1, [gI; gI; gZ; gY]).
Definition t3''' : TType 4 := (C1, [gY; gZ; gI; gI]).
Definition t4''' : TType 4 := (C1, [gZ; gX; gI; gI]).
Definition Test''' : list (TType 4) := [t1'''; t2'''; t3'''; t4'''].


(***************************************************)
(*********** Separability Function Tests ***********)
(***************************************************)


(* Test'
[[gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX];
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI];
 [gI; gI; gX; gX; gY; gI; gI];
 [gX; gY; gI; gI; gI; gI; gI];
 [gZ; gX; gI; gI; gI; gI; gI] *)
Compute separable Test' [0; 1; 3]%nat. (* false *)
Compute separable Test' [0; 1]%nat. (* true *)

(* Test''
[[gI; gZ; gX];
 [gI; gY; gZ];
 [gZ; gI; gI]] *)
Compute separable Test'' [1; 2]%nat. (* true *)
Compute separable Test'' [0; 2]%nat. (* false *)

(* Test'''
[[gI; gI; gX; gX];
 [gI; gI; gZ; gY];
 [gY; gZ; gI; gZ];
 [gZ; gX; gI; gI]] *)
Compute separable Test''' [0; 1]%nat. (* true *)
Compute separable Test''' [0; 2]%nat. (* false *)
Compute separable Test''' [1; 2]%nat. (* false *)
Compute separable Test''' [0; 3]%nat. (* false *)
Compute separable Test''' [0; 2; 3]%nat. (* false *)



(***************************************************)
(************** Separability Examples **************)
(***************************************************)

(** Test 1 **)

Example separation_solve :
exists Placeholder,
{{ @Cap 4 
[[(C1, [gY; gI; gZ; gI])];
 [(C1, [gI; gY; gI; gZ])];
 [(C1, [gZ; gI; gX; gI])];
 [(C1, [gI; gZ; gI; gY])]]
}}
(H 0 ;; S 0 ;; H 0)%pg
{{ Placeholder }}.
Proof. solvePlaceholder_refl.
assumption.
Qed.

Example separation_validate :
{{ @Cap 4
[[(C1, [gY; gI; gZ; gI])];
 [(C1, [gI; gY; gI; gZ])];
 [(C1, [gZ; gI; gX; gI])];
 [(C1, [gI; gZ; gI; gY])]]
}}
(H 0 ;; S 0 ;; H 0)%pg
{{ @Cap 4
[[(C1, [gZ; gI; gZ; gI])]; 
 [(C1, [gI; gY; gI; gZ])];
 [((- C1)%C, [gY; gI; gX; gI])]; 
 [(C1, [gI; gZ; gI; gY])]]
}}.
Proof. validate_refl.
Qed.


Compute 
@separable_all 4 
[(C1, [gZ; gI; gZ; gI]);
 (C1, [gI; gY; gI; gZ]);
 ((- C1)%C, [gY; gI; gX; gI]); 
 (C1, [gI; gZ; gI; gY])]
  [[0; 2]; [1; 3]]%nat. (* true *)

Compute 
@separate 4 
[(C1, [gZ; gI; gZ; gI]);
 (C1, [gI; gY; gI; gZ]);
 ((- C1)%C, [gY; gI; gX; gI]); 
 (C1, [gI; gZ; gI; gY])]
  [[0; 2]; [1; 3]]%nat. (* 
([2%nat; 2%nat],
 [[(R1, R0, [gZ; gZ]); 
   ((- R1)%R, (- R0)%R, [gY; gX])];
  [(R1, R0, [gY; gZ]); 
   (R1, R0, [gZ; gY])]], 
[0%nat; 2%nat; 1%nat; 3%nat]) *)


Example separation_test :
{{ @Cap 4 
[[(C1, [gY; gI; gZ; gI])]; 
 [(C1, [gI; gY; gI; gZ])];
 [(C1, [gZ; gI; gX; gI])];
 [(C1, [gI; gZ; gI; gY])]] 
}}
(H 0 ;; S 0 ;; H 0)%pg
{{ @Sep 4 (@separate 4
  [(C1, [gZ; gI; gZ; gI]); 
   (C1, [gI; gY; gI; gZ]);
   ((- C1)%C, [gY; gI; gX; gI]); 
   (C1, [gI; gZ; gI; gY])]
  [[0; 2]; [1; 3]]%nat) }}.
Proof. validate_refl'.
Qed.


(** Test 2 **)

(* Test'
[[gI; gI; gI; gI; gI; gY; gZ];
 [gI; gI; gI; gI; gI; gZ; gX];
 [gI; gI; gZ; gX; gZ; gI; gI];
 [gI; gI; gZ; gZ; gY; gI; gI];
 [gI; gI; gX; gX; gY; gI; gI];
 [gX; gY; gI; gI; gI; gI; gI];
 [gZ; gX; gI; gI; gI; gI; gI] *)
Compute map snd Test'.
Compute separable Test' [0; 1]%nat. (* true *)
Compute separable Test' [2; 3; 4]%nat. (* true *)
Compute separable Test' [5; 6]%nat. (* true *)
Compute separable_all Test' [[0;1]; [2; 3; 4]; [5;6]]%nat. (* true *)



Example separation_solve2 :
exists Placeholder,
{{ Cap (map TtoA Test') }}
(H 0 ;; S 0 ;; H 0)%pg
{{ Placeholder }}.
Proof. simpl. 
solvePlaceholder_refl.
assumption.
Qed.

Compute @separable_all 7
[(C1, [gI; gI; gI; gI; gI; gY; gZ]);
 (C1, [gI; gI; gI; gI; gI; gZ; gX]);
 (C1, [gI; gI; gZ; gX; gZ; gI; gI]);
 (C1, [gI; gI; gZ; gZ; gY; gI; gI]);
 (C1, [gI; gI; gX; gX; gY; gI; gI]);
 (C1, [gX; gY; gI; gI; gI; gI; gI]);
 ((- C1)%C, [gY; gX; gI; gI; gI; gI; gI])]
[[0;1]; [2; 3; 4]; [5;6]]%nat. (* true *)


Example separation_test2 :
{{ Cap (map TtoA Test') }}
(H 0 ;; S 0 ;; H 0)%pg
{{ Sep (@separate 7
[(C1, [gI; gI; gI; gI; gI; gY; gZ]);
 (C1, [gI; gI; gI; gI; gI; gZ; gX]);
 (C1, [gI; gI; gZ; gX; gZ; gI; gI]);
 (C1, [gI; gI; gZ; gZ; gY; gI; gI]);
 (C1, [gI; gI; gX; gX; gY; gI; gI]);
 (C1, [gX; gY; gI; gI; gI; gI; gI]);
 ((- C1)%C, [gY; gX; gI; gI; gI; gI; gI])]
[[0;1]; [2; 3; 4]; [5;6]]%nat) }}.
Proof. validate_refl'.
Qed.
