(** * Step 82, stage 4: results under the paper's Theorem names.
    Several are restated for the new design; the report says which. *)
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology.
Set Default Proof Using "Type".

Theorem paper_evaluation_preserves_typing : typing_sound paper_ontology.
Proof. exact paper_ontology_typing_sound. Qed.

Theorem infer_application : forall O f u F U R, infer O @ f ==> Sm F -> infer O @ u ==> Sm U ->
  tp O @ F @r U ==> Sm R -> infer_expression O @ (f @ u) ==> Sm R.
Proof. intros; eapply ie_fork; [apply ie_stem; eassumption|apply ie_stem; eassumption|eassumption]. Qed.

Theorem function_declaration_sound : forall O r, decl_sound_by_typing O (Fk fun_nm r) (fun_D r (tp O)).
Proof. exact fun_decl_sound_by_typing. Qed.

Theorem infer_lam_fun : forall f F A B, infer O_fun @ f ==> Sm F -> tp O_fun @ F @r A ==> Sm B ->
  names_concrete A -> names_concrete B -> infer O_fun @ lam f A B ==> Sm (Fun A B).
Proof. exact lam_typed. Qed.

Theorem salary_bill_department_2025 : salary_bill @ department_example ==> numeral 171.
Proof. exact salary_bill_department. Qed.

Theorem count_employees_department_example : employee_count @ department_example ==> numeral 3.
Proof. exact employee_count_department. Qed.

(** append_polymorphic, infer_append_application and map_polymorphic are now
    proved for every type parameter in poly.v (stage 5). *)
