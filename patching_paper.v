(** * Step 82, stage 5, part 5: patching a pending query, and the lambda form. *)
From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries poly updates_paper.
Set Default Proof Using "Type".
Local Notation PO := paper_ontology.
Ltac by_run5 := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** Both routes from [paid_over 57 @ department_example] reach [L58]:
    patch the pending query, then evaluate; or evaluate, then update the result. *)
Theorem patch_commutes_with_evaluation :
  (salary_update @ (paid_over 57 @ department_example) ==> (paid_over 58 @ incremented_department) /\
   paid_over 58 @ incremented_department ==> L58) /\
  (paid_over 57 @ department_example ==> L57 /\
   salary_update @ L57 ==> L58).
Proof. split; split; by_run5. Qed.




