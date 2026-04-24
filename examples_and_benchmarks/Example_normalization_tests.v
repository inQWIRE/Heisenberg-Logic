Require Import HeisenbergFoundations.ReflexiveAutomation.

(***************************************************)
(** ** Normalization Examples ** **)
(***************************************************)

(** Normalization example on 7 qubit Steane code ** **)

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




(** Some other normalization tests **)


Definition t1' : TType 7 := (C1, [gI; gI; gI; gI; gI; gY; gZ]).
Definition t2' : TType 7 := (C1, [gI; gI; gI; gI; gI; gZ; gX]).
Definition t3' : TType 7 := (C1, [gI; gI; gZ; gX; gZ; gI; gI]).
Definition t4' : TType 7 := (C1, [gI; gI; gZ; gZ; gY; gI; gI]).
Definition t5' : TType 7 := (C1, [gI; gI; gX; gX; gY; gI; gI]).
Definition t6' : TType 7 := (C1, [gX; gY; gI; gI; gI; gI; gI]).
Definition t7' : TType 7 := (C1, [gZ; gX; gI; gI; gI; gI; gI]).
Definition Test' : list (TType 7) := [t1'; t2'; t3'; t4'; t5'; t6'; t7'].

(* Test'
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

(* Test''
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

(* Test'''
[[gI; gI; gX; gX];
 [gI; gI; gZ; gY];
 [gY; gZ; gI; gZ];
 [gZ; gX; gI; gI]] *)
Compute map snd (normalize 0%nat Test'''). (*
[[gY; gZ; gI; gI];
 [gZ; gX; gI; gI];
 [gI; gI; gY; gZ];
 [gI; gI; gZ; gY]] *)
