Require Import HeisenbergFoundations.ReflexiveAutomation.

(***************************************************)
(********************* Toffoli *********************)
(***************************************************)

(** Here for reference:
Definition Td (n : nat) := Z n ;; S n ;; T n. **)


Definition TOFFOLI (a b c : nat) :=
  (H c ;; CNOT b c ;; Td c ;; CNOT a c ;; T c ;; CNOT b c ;; Td c ;; CNOT a c ;; T b ;; T c ;; H c ;; CNOT a b ;; T a ;; Td b ;; CNOT a b)%pg.


Example ZIITOFFOLI :
  {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gZ; gI; gI])] }}.
Proof. validate_refl.
Qed.

Example IZITOFFOLI :
  {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gI; gZ; gI])] }}.
Proof. validate_refl.
Qed.

Example IIXTOFFOLI :
  {{ @AtoPred 3 [(C1, [gI; gI; gX])] }} TOFFOLI 0 1 2 {{ @AtoPred 3 [(C1, [gI; gI; gX])] }}.
Proof. validate_refl. 
Qed.

Example IIZTOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gI; gI; gZ])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof. solvePlaceholder_refl.
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
Proof. validate_refl.
Qed.


Example XIITOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gX; gI; gI])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof. solvePlaceholder_refl.
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
Proof. validate_refl.
Qed.


Example IXITOFFOLI_solve : 
exists Placeholder,
{{ @AtoPred 3 [(C1, [gI; gX; gI])] }} TOFFOLI 0 1 2 {{ Placeholder }}.
Proof. solvePlaceholder_refl.
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
Proof. validate_refl.
Qed.
