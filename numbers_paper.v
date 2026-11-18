(** * Step 82, stage 5, part 4: addition as a lambda program. *)
From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology fun_ontology self_typing size_queries poly.
Set Default Proof Using "Type".
Local Notation FO := fun_ontology.
Ltac by_run4 := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** [add_lam = lam[add, Nat*Nat, Nat]]. *)
Definition add_lam : Combination := lam add (Nat '* Nat) Nat.

Theorem infer_add_lam : infer FO @ add_lam ==> Sm (Fun (Nat '* Nat) Nat). Proof. by_run4. Qed.
Theorem add_lam_eval : add_lam @ (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_run4. Qed.
Theorem add_lam_application : infer_expression FO @ (add_lam @ (numeral 2 '* numeral 3)) ==> Sm Nat. Proof. by_run4. Qed.

(** The function type refuses every other argument type, for instance [Bool * Bool]. *)
Theorem add_lam_refuses : tp FO @ Fun (Nat '* Nat) Nat @r (Bool '* Bool) ==> Lf. Proof. by_run4. Qed.
Theorem add_lam_refuses_application : infer_expression FO @ (add_lam @ (tt '* ff)) ==> Lf. Proof. by_run4. Qed.
