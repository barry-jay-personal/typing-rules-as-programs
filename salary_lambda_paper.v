(** * Step 82, stage 5, part 5: the salary update reaches the threshold of a lambda program. *)
From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries poly updates_paper.
Set Default Proof Using "Type".
Local Notation PO := paper_ontology.
Ltac by_run5 := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

Theorem salary_update_paid_at_least_57 : salary_update @ paid_at_least 57 ==> paid_at_least 58. Proof. by_run5. Qed.
