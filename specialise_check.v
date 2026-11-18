(** * Step 82, stage 5, part 5: the equality-specialising walk on the new design.

    The walk of src_type36 ([specialise_fn]) replaces each tester
    [wait[equal,c]] by [equal1 c], except when [c] is a stem.  Here it is
    restated as a function and run on the programs of the new design, to
    see whether it meets a code [code T] (a fork) inside a type test. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries.
Set Default Proof Using "Type".
Local Notation PO := paper_ontology.

(** [tester_agrees]: a tester and its specialisation behave alike. *)
Theorem tester_agrees : forall c x v, 'wait[equal, c] @ x ==> v <-> equal1 c @ x ==> v.
Proof.
  intros c x v; split; intro H.
  - apply wait_eval_inv in H. destruct (app2_inv _ _ _ _ H) as [a [Ha Hv]].
    pose proof (eval_deterministic _ _ Ha _ (equal_eval c)) as ->; exact Hv.
  - apply wait_eval; eapply app2; [apply equal_eval|exact H].
Qed.

Definition site (t : Combination) : option Combination :=
  match t with
  | Fk (Sm (Fk (Sm (Fk Lf m)) (Fk Lf c))) i =>
      if andb (if combination_eq_dec m equal then true else false)
              (if combination_eq_dec i ('I) then true else false) then Some c else None
  | _ => None
  end.

Fixpoint specialise_fn (t : Combination) : Combination :=
  match site t with
  | Some (Sm _) => t
  | Some c => equal1 c
  | None => match t with Lf => Lf | Sm u => Sm (specialise_fn u) | Fk u v => Fk (specialise_fn u) (specialise_fn v) end
  end.

(** The number of sites the walk rewrites, and the number of stem sites it skips. *)
Fixpoint sites (t : Combination) : nat * nat :=
  match site t with
  | Some (Sm _) => (0, 1)
  | Some _ => (1, 0)
  | None => match t with
            | Lf => (0, 0)
            | Sm u => sites u
            | Fk u v => let (a, b) := sites u in let (c, d) := sites v in (a + c, b + d)
            end
  end.

Example sites_salary_update : sites salary_update = (0, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_special_query : sites employee_count = (0, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_size : sites size = (0, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_appendR : sites appendR = (0, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_minimisation : sites minimisation = (0, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_tp : sites (tp PO) = (11, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_infer : sites (infer PO) = (33, 0). Proof. vm_compute; reflexivity. Qed.
Example sites_paper_ontology : sites PO = (11, 0). Proof. vm_compute; reflexivity. Qed.

(** The 11 sites of [paper_ontology] are the constructor and identity guards
    [guard1 c = wait[equal, c]], whose [c] are forks (stage 8: 8 before the
    arrays, and the guards of gen_prepend and gen_empty; step 84: and the
    guard of gen_none).  No program holds a
    tester of a code: the type test [wait3[sp_body, code T, f, d]] passes the
    code to [sp_body] as an argument.  So the walk leaves [salary_update]
    unchanged, and its typing in the specialised ontology is unchanged. *)
Theorem specialise_salary_update_unchanged : specialise_fn salary_update = salary_update.
Proof. vm_compute; reflexivity. Qed.
Theorem specialise_salary_update_typed : infer (specialise_fn PO) @ salary_update ==> Sm Update.
Proof. apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end. Qed.
