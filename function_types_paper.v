(** * Step 82, stage 5, part 5: minimisation with a function-typed predicate.

    [minimisation_lam = lam[\p. mk_fun[Nat,Nat] @ (minimisation @ p), Nat -> Bool, Nat -> Nat]].
    The inner function type is built at run time by the constructor
    [mk_fun[Nat,Nat]], whose guard checks [Update # Nat ==> Sm Nat]. *)
From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology fun_ontology self_typing size_queries poly.
Set Default Proof Using "Type".
Local Notation FO := fun_ontology.
Ltac by_runF := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

Definition minimisation_body : Combination := Eval cbn -[mk_fun minimisation] in to_tree
  (star "p" (op (mk_fun Nat Nat) @@ (op minimisation @@ Ref "p"))).
Definition minimisation_lam : Combination := lam minimisation_body (Fun Nat Bool) (Fun Nat Nat).
Definition typed_is_odd : Combination := lam is_odd Nat Bool.

Theorem infer_minimisation_fn : infer FO @ minimisation_lam ==> Sm (Fun (Fun Nat Bool) (Fun Nat Nat)).
Proof. by_runF. Qed.
Theorem infer_typed_is_odd : infer FO @ typed_is_odd ==> Sm (Fun Nat Bool). Proof. by_runF. Qed.
Theorem minimise_is_odd_fn_eval : minimisation_lam @ typed_is_odd @r zero ==> succ zero. Proof. by_runF. Qed.
Theorem infer_minimise_is_odd_fn : infer_expression FO @ (minimisation_lam @ typed_is_odd @r zero) ==> Sm Nat.
Proof. by_runF. Qed.
