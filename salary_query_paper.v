(** * Step 82, stage 5, part 5: the salary update reaches the thresholds of queries and lambda programs. *)
From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries poly updates_paper.
Set Default Proof Using "Type".
Local Notation PO := paper_ontology.
Ltac by_run5 := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

Theorem salary_update_polymorphic : infer PO @ salary_update ==> Sm Update /\
  tp PO @ Update @r Department ==> Sm Department /\ salary_update @ paid_over 57 ==> paid_over 58.
Proof. split; [by_run5|split; [apply type_app_Update|by_run5]]. Qed.
Theorem paid_over_58_typed : infer PO @ paid_over 58 ==> Sm (Query (List Employee)). Proof. exact (paid_over_typed 58). Qed.
