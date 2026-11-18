(** * Step 84: gen_none at paper_ontology, and the lambda program increment_salary.

    [gen_none @ code[A] :: Option[A]] at [paper_ontology] whenever the names
    of [A] are concrete.  [increment_salary = lam[salary_increment, Salary,
    Salary]] has type [Salary -> Salary] at [fun_ontology] and takes
    [salary[k]] to [salary[succ[k]]]. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt paper_ontology fun_ontology gen_none.
Set Default Proof Using "Type".
Local Notation PO := paper_ontology.
Local Notation FO := fun_ontology.
Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Ltac by_run84 := apply (runp_sound 40); vm_done.

(** ** gen_none *)

Lemma type_app_gen_none : forall A, names_concrete A -> tp PO @ 'label[gen_none_nm] @r code A ==> Sm (Option A).
Proof. intros A HA; eapply tp_abs; [apply PO_gnone|apply elim_of_fwd, gnoe_fwd, HA]. Qed.

Lemma infer_gen_none : infer PO @ gen_none ==> Sm ('label[gen_none_nm]).
Proof. by_run84. Qed.

Lemma gen_none_typed : forall A, names_concrete A -> infer_expression PO @ (gen_none @ code A) ==> Sm (Option A).
Proof.
  intros A HA; eapply ie_fork; [apply ie_stem, infer_gen_none| |apply type_app_gen_none, HA].
  apply ie_stem, concrete_is_self_typed, code_concrete, HA.
Qed.

Example gen_none_Nat_typed : infer_expression PO @ (gen_none @ code Nat) ==> Sm (Option Nat). Proof. by_run84. Qed.
Example gen_none_Nat_eval : gen_none @ code Nat ==> none Nat. Proof. by_run84. Qed.

(** ** increment_salary *)

Definition increment_salary : Combination := lam salary_increment Salary Salary.

Lemma increment_salary_eval : forall k, increment_salary @ salary k ==> salary (succ k).
Proof. intros k; unfold increment_salary, lam, salary_increment, salary_succ, salary, succ, mk_salary, mk_nat, swap; apply tagged_eval; evaluate. Qed.

Lemma increment_salary_typed : infer FO @ increment_salary ==> Sm (Fun Salary Salary).
Proof. by_run84. Qed.
