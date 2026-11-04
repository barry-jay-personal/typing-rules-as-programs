(** * The ontology of the paper (paper: A Sound Ontology).

    The declarations [paper_ontology], built from its table
    of declarations, and its soundness ([paper_ontology_sound]).

    Build order: It declares every family, so this file follows all
    the families (through updates.v).  The self-typing theorems follow in self_typing.v. *)


(** Combined introduction for data types and generic traversals.
    The generic closure construction ([generic_ontology]) is in updates.v. Here it is populated
    with the ordinary data families, Salary, Employee and Department.
    Capability lemmas, soundness and infer self-typing are established before
    the worked examples in customisation.v. This file imports no examples. *)
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions queries updates booleans data_types arrays conditionals.

From Stdlib Require Import List.
Import ListNotations.
Set Default Proof Using "Type".
Definition company_base_ontology :=
  extend is_named_case (extend employee_case (extend department_case (extend salary_case
    (extend seek_case (extend array_case (extend list_case ordinary_ontology)))))).
Lemma company_base_ontology_row : company_base_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold company_base_ontology.
  apply extend_none_value; [apply is_named_case_none; unfold is_named_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply record_case_none; unfold employee_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply record_case_none; unfold department_nm, employee_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply salary_case_none; unfold salary_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply seek_case_none; unfold seek_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply array_case_none; unfold array_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply list_case_none; unfold list_nm, fun_nm; discriminate|].
  exact (functions_declared ordinary_decl).
Qed.
Definition company_ontology := generic_ontology company_base_ontology.
Canonical Structure company_decl :=
  mkDecl company_ontology (generic_ontology_row _ company_base_ontology_row).

Local Ltac company_lookup :=
  unfold supports_employee, supports_department, supports_list,
    supports_booleans, supports_salary, supports_seek, supports_arrays,
    supports_number, company_ontology;
  repeat first [exact I | lazymatch goal with |- _ /\ _ => split end |
    apply generic_ontology_ordinary; [discriminate |discriminate |] |
    progress unfold company_base_ontology, salary_base_ontology, employee_case, department_case |
    apply extend_some; first [apply is_named_case_some |apply record_case_some |apply list_case_some |
      apply salary_case_some |apply seek_case_some |apply array_case_some] |
    apply extend_none_value;
      [first [apply is_named_case_none |apply record_case_none |apply list_case_none |
        apply salary_case_none |apply seek_case_none |apply array_case_none]; discriminate |] |
    apply ordinary_ontology_supports_number |apply ordinary_ontology_supports_booleans].
Lemma company_employee : supports_employee company_ontology.
Proof. company_lookup. Qed.
Lemma company_department : supports_department company_ontology.
Proof. company_lookup. Qed.
Lemma company_list : supports_list company_ontology.
Proof. company_lookup. Qed.
Lemma company_booleans : supports_booleans company_ontology.
Proof. company_lookup. Qed.
Lemma company_salary : supports_salary company_ontology.
Proof. company_lookup. Qed.
Lemma company_seek : supports_seek company_ontology.
Proof. company_lookup. Qed.
Lemma company_updates : supports_updates company_ontology.
Proof. apply generic_ontology_updates. Qed.
Lemma company_number : supports_number company_ontology.
Proof. company_lookup. Qed.
Lemma company_employee_declared : declared_wrapper company_ontology employee_nm employee_fields.
Proof. apply employee_declared; exact company_employee. Qed.
Lemma company_queries : supports_queries company_ontology.
Proof. apply generic_ontology_queries. Qed.
Lemma company_is_named : supports_is_named company_ontology.
Proof. unfold supports_is_named; company_lookup. Qed.


(** The names of the development are pairwise distinct. *)
Lemma nametags_distinct :
  List.NoDup [fun_nm; query_nm; update_nm; concrete_wrapper_nm; bool_nm; nat_nm;
    opt_nm; sum_nm; list_nm; employee_nm; department_nm; array_nm; salary_nm; seek_nm; is_named_nm].
Proof.
  unfold fun_nm, query_nm, update_nm, concrete_wrapper_nm, bool_nm, nat_nm,
    opt_nm, sum_nm, list_nm, employee_nm, department_nm, array_nm, salary_nm, seek_nm, is_named_nm.
  repeat constructor; cbn; intuition discriminate.
Qed.

(** The company examples and the combined examples share this declarations;
    it includes Salary, Employee and Department as well as the data families. *)
Definition paper_ontology := company_ontology.
Canonical Structure paper_decl :=
  mkDecl paper_ontology (functions_declared company_decl).

(** * The declarations of [paper_ontology], as a table

    Each row [(N, D)] gives a nametag and its abstractor, a program from
    carrier types to eliminators.  The declarations built from a list of
    rows answers, at the nametag of a row, its abstractor, and refuses
    every other nametag.  The rows for queries and updates have abstractors
    that consult the declarations itself; they are added by the reified fixed
    point [generic_ontology] (updates.v). *)
Definition declaration_row := (Combination * Combination)%type.
Definition row_nm (r : declaration_row) : Combination := fst r.
Definition row_abstractor (r : declaration_row) : Combination := snd r.
Definition row_case (r : declaration_row) : Combination :=
  to_tree (tcase (Val (row_nm r)) (Val (row_abstractor r))).

Fixpoint table_ontology (rows : list declaration_row) : Combination :=
  match rows with
  | nil => empty_ontology
  | cons r rs => extend (row_case r) (table_ontology rs)
  end.

(** The rows of the base declarations, in the order of its clauses. *)
Definition base_rows : list declaration_row := [
  (is_named_nm, 'K1 is_named_abstractor);
  (employee_nm, 'K1 (computed_wrap_abstractor employee_payload_program));
  (department_nm, 'K1 (computed_wrap_abstractor department_payload_program));
  (salary_nm, 'K1 (computed_wrap_abstractor salary_payload_program));
  (seek_nm, 'K1 (computed_wrap_abstractor salary_payload_program));
  (array_nm, 'K1 array_abstractor);
  (list_nm, 'K1 list_abstractor);
  (sum_nm, 'K1 sum_abstractor);
  (opt_nm, 'K1 option_abstractor);
  (nat_nm, 'K1 nat_abstractor);
  (bool_nm, 'K1 bool_abstractor);
  (fun_nm, function_abstractor)].

(** The rows added by [generic_ontology], for declarations [AI]. *)
Definition generic_rows (AI : Combination) : list declaration_row := [
  (query_nm, query_abstractor AI);
  (update_nm, update_abstractor AI)].

Definition paper_ontology_rows : list declaration_row :=
  generic_rows paper_ontology ++ base_rows.

(** [paper_ontology] is built from the table. *)
Lemma paper_ontology_from_table :
  paper_ontology = generic_ontology (table_ontology base_rows).
Proof. reflexivity. Qed.

Lemma row_case_hit : forall r,
  row_case r @ row_nm r ==> Sm (row_abstractor r).
Proof. intros; apply tcase_eq. Qed.

Lemma row_case_miss : forall r M, M <> row_nm r -> row_case r @ M ==> Lf.
Proof. intros r M H; apply tcase_neq; intro HE; apply H; symmetry; exact HE. Qed.

Lemma table_ontology_hit : forall rows r,
  NoDup (map row_nm rows) -> In r rows ->
  table_ontology rows @ row_nm r ==> (row_abstractor r).
Proof.
  induction rows as [|r0 rs IH]; intros r Hnd Hin; [contradiction|].
  cbn [table_ontology]; inversion Hnd as [|? ? Hnot Hnd']; subst.
  destruct Hin as [->|Hin].
  - apply extend_some; apply row_case_hit.
  - apply extend_none_value; [apply row_case_miss|apply IH; assumption].
    intro HE; apply Hnot; rewrite <- HE; apply in_map; exact Hin.
Qed.

Lemma table_ontology_refuses : forall rows N,
  ~ In N (map row_nm rows) -> table_ontology rows @ N ==> refusal.
Proof.
  induction rows as [|r0 rs IH]; intros N Hnot.
  - cbn; unfold empty_ontology, refusal; evaluate.
  - cbn [table_ontology]; apply extend_none_value.
    + apply row_case_miss; intro HE; apply Hnot; left; symmetry; exact HE.
    + apply IH; intro HI; apply Hnot; right; exact HI.
Qed.


Lemma base_rows_distinct : NoDup (map row_nm base_rows).
Proof.
  unfold base_rows; cbn [map row_nm].
  unfold is_named_nm, employee_nm, department_nm, salary_nm, seek_nm, array_nm,
    list_nm, sum_nm, opt_nm, nat_nm, bool_nm, fun_nm.
  repeat constructor; cbn; intuition discriminate.
Qed.

Lemma base_rows_ordinary : forall N D,
  In (N, D) base_rows -> N <> query_nm /\ N <> update_nm.
Proof.
  intros N D Hin; unfold base_rows in Hin; cbn [In] in Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; inversion Hin; subst;
    unfold query_nm, update_nm, is_named_nm, employee_nm, department_nm, salary_nm, seek_nm, array_nm,
      list_nm, sum_nm, opt_nm, nat_nm, bool_nm, fun_nm; split; discriminate.
Qed.

(** the paper's ontology figure compiles exactly: [paper_ontology] answers each row's
    abstractor at the nametag, and refuses every other nametag. *)
Lemma paper_ontology_table : forall N D,
  In (N, D) paper_ontology_rows ->
  paper_ontology @ N ==> D.
Proof.
  intros N D Hin.
  unfold paper_ontology_rows in Hin; apply in_app_or in Hin.
  destruct Hin as [[HQ|[HU|[]]]|Hin].
  - inversion HQ; subst; apply generic_ontology_queries.
  - inversion HU; subst; apply generic_ontology_updates.
  - rewrite paper_ontology_from_table.
    destruct (base_rows_ordinary _ _ Hin) as [HQ HU].
    apply generic_ontology_ordinary; [exact HQ|exact HU|].
    exact (table_ontology_hit base_rows (N, D) base_rows_distinct Hin).
Qed.

Lemma paper_ontology_refuses : forall N,
  ~ In N (map row_nm paper_ontology_rows) -> paper_ontology @ N ==> refusal.
Proof.
  intros N Hnot; rewrite paper_ontology_from_table.
  unfold paper_ontology_rows in Hnot; rewrite map_app in Hnot.
  apply generic_ontology_ordinary.
  - intro HE; apply Hnot; apply in_or_app; left; left; rewrite HE; reflexivity.
  - intro HE; apply Hnot; apply in_or_app; left; right; left; rewrite HE; reflexivity.
  - apply table_ontology_refuses; intro HI; apply Hnot; apply in_or_app; right; exact HI.
Qed.


(** The wrapper constructors store concrete payload-building programs and
    reconstruct their abstract types at execution time. The complete declarations
    is therefore tag-free. *)
Lemma paper_ontology_tag_free : tag_free paper_ontology = true.
Proof.
 unfold paper_ontology, company_ontology, company_base_ontology,
   employee_case, department_case, record_case, generic_ontology,
   generic_ontology_body, query_case_builder, update_case_builder.
 cbn [query_case_builder_package update_case_builder_package].
 vm_compute; reflexivity.
Qed.

Local Ltac all_lookup :=
  unfold supports_booleans, supports_number, supports_option, supports_sum,
    supports_list, supports_arrays, paper_ontology, company_ontology;
  apply generic_ontology_ordinary; try discriminate;
  unfold company_base_ontology, employee_case, department_case;
  repeat first [
    apply extend_some; first [apply is_named_case_some |apply record_case_some |apply salary_case_some |
      apply seek_case_some |apply array_case_some |apply list_case_some] |
    apply extend_none_value;
      [first [apply is_named_case_none |apply record_case_none |apply salary_case_none |
        apply seek_case_none |apply array_case_none |apply list_case_none]; discriminate |] |
    apply ordinary_ontology_supports_booleans |
    apply ordinary_ontology_supports_number |
    apply ordinary_ontology_supports_option |
    apply ordinary_ontology_supports_sum ].
Lemma paper_ontology_supports_booleans : supports_booleans paper_ontology.
Proof. all_lookup. Qed.
Lemma paper_ontology_supports_number : supports_number paper_ontology.
Proof. all_lookup. Qed.
Lemma paper_ontology_supports_queries : supports_queries paper_ontology.
Proof. apply generic_ontology_queries. Qed.
Lemma paper_ontology_supports_updates : supports_updates paper_ontology.
Proof. apply generic_ontology_updates. Qed.
Lemma paper_ontology_supports_is_named : supports_is_named paper_ontology.
Proof. unfold supports_is_named; all_lookup. Qed.
Lemma paper_ontology_supports_seek : supports_seek paper_ontology.
Proof. unfold supports_seek; all_lookup. Qed.


(** At every nametag, [paper_ontology] answers a row's declaration or the refusal. *)
Lemma paper_ontology_answers : forall N,
  (exists D, In (N, D) paper_ontology_rows /\ paper_ontology @ N ==> D) \/
  paper_ontology @ N ==> refusal.
Proof.
  intros N.
  destruct (in_dec combination_eq_dec N (map row_nm paper_ontology_rows)) as [Hin|Hnot].
  - apply in_map_iff in Hin; destruct Hin as [[N' D] [HN Hin]].
    cbn [row_nm fst] in HN; subst N'.
    left; exists D; split; [exact Hin|exact (paper_ontology_table _ _ Hin)].
  - right; exact (paper_ontology_refuses N Hnot).
Qed.


(** Agreement on every argument, family by family: every declaration of
    the paper's ontology figure is sound in the one-round sense. *)


(** Built declarations, clause by clause. *)


(** Every row of the paper's ontology figure declares an abstractor sound for values; every
    row but Query, Update and IsNamed is sound by typing. *)
Lemma K1_row_sound : forall (P : Combination -> Prop) a X D,
  ('K1 X) @ a ==> D -> P X -> P D.
Proof. intros P a X D H HX; pose proof (eval_deterministic _ _ H _ (eval_k _ _)) as ->; exact HX. Qed.

Lemma paper_ontology_rows_declaration_sound : forall N R D,
  In (N, R) paper_ontology_rows -> R @ type_app paper_ontology ==> D ->
  sound_abstractor paper_ontology D.
Proof.
  intros N R D Hin HD.
  unfold paper_ontology_rows, generic_rows, base_rows in Hin; cbn [In List.app] in Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; inversion Hin; subst;
    [pose proof (eval_deterministic _ _ HD _ (query_abstractor_partial paper_ontology)) as ->;
       apply plain_query_cond2; exact paper_ontology_supports_queries
    |pose proof (eval_deterministic _ _ HD _ (update_abstractor_partial paper_ontology)) as ->;
       apply plain_update_cond2; exact paper_ontology_supports_updates
    |..];
    try (eapply (K1_row_sound (sound_abstractor paper_ontology)); [exact HD|]);
    [apply is_named_abstractor_value_sound|..]; apply sound_by_typing_implies_sound.
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_array_cond2.
  - apply plain_list_cond2.
  - apply plain_sum_cond2.
  - apply plain_option_cond2.
  - apply plain_nat_cond2.
  - apply plain_bool_cond2.
  - exact (function_abstractor_row_sound paper_decl D HD).
Qed.

(** Every row but Query, Update and IsNamed is sound by typing. *)
Lemma paper_ontology_rows_sound_by_typing : forall N R D,
  In (N, R) paper_ontology_rows -> N <> query_nm -> N <> update_nm -> N <> is_named_nm ->
  R @ type_app paper_ontology ==> D ->
  abstractor_sound_by_typing paper_ontology D.
Proof.
  intros N R D Hin HQ HN HT HD.
  unfold paper_ontology_rows, generic_rows, base_rows in Hin; cbn [In List.app] in Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; inversion Hin; subst;
    [congruence|congruence|congruence|..];
    try (eapply (K1_row_sound (abstractor_sound_by_typing paper_ontology)); [exact HD|]).
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_wrap_cond2.
  - apply plain_array_cond2.
  - apply plain_list_cond2.
  - apply plain_sum_cond2.
  - apply plain_option_cond2.
  - apply plain_nat_cond2.
  - apply plain_bool_cond2.
  - exact (function_abstractor_row_sound paper_decl D HD).
Qed.

(** Hence abstract type introduction is sound by typing at every carrier
    but the one-level and choice carriers of Query and Update and the
    name tests of IsNamed. *)
Lemma paper_plain_intro_sound_but : forall C N E U V,
  (N = query_nm \/ N = update_nm ->
     (forall B, C <> query_one_level B) /\ C <> update_one_level ('Update) /\ choice_free C) ->
  (N = is_named_nm -> forall M, C <> name_test M) ->
  paper_ontology @ N @r type_app paper_ontology @r C ==> Sm E ->
  E @ type_app paper_ontology @r U ==> Sm V ->
  type_app paper_ontology @ C @r U ==> Sm V.
Proof.
  intros C N E U V HB HTn HD HE.
  destruct (combination_eq_dec N query_nm) as [->|HQ].
  - pose proof (query_abstractor_applied _ _ _ paper_ontology_supports_queries HD) as HDC.
    destruct (HB (or_introl eq_refl)) as [Hq [_ Hc]].
    exact (query_abstractor_sound _ C E U V paper_ontology_supports_queries Hq (or_introl Hc) HDC HE).
  - destruct (combination_eq_dec N update_nm) as [->|HU].
    + pose proof (update_abstractor_applied _ _ _ paper_ontology_supports_updates HD) as HDC.
      destruct (HB (or_intror eq_refl)) as [_ [Hu Hc]].
      exact (update_abstractor_sound _ C E U V paper_ontology_supports_updates Hu (or_introl Hc) HDC HE).
    + destruct (combination_eq_dec N is_named_nm) as [->|HT].
      * pose proof (declaration_K1_inv _ _ _ _ _ _ paper_ontology_supports_is_named HD) as HDC.
        destruct (is_named_abstractor_inv _ _ HDC) as [X [-> _]].
        exfalso; exact (HTn eq_refl X eq_refl).
      * destruct (declaration_apply_inv _ _ _ _ _ HD) as [R [D [HR [HRD HDC]]]].
        destruct (paper_ontology_answers N) as [[D' [Hin HR']]|Href].
        -- pose proof (eval_deterministic _ _ HR _ HR') as ->.
           exact (paper_ontology_rows_sound_by_typing _ _ _ Hin HQ HU HT HRD C E U V HDC HE).
        -- pose proof (declaration_K1_inv _ _ _ _ _ _ Href HD) as HC.
           exact (refusal_sound _ C E U V HC HE).
Qed.

(** The declarations of the paper's ontology figure is sound. *)
Lemma paper_ontology_sound : ontology_sound paper_ontology.
Proof.
  intros N R D HR HD.
  destruct (paper_ontology_answers N) as [[R' [Hin HR']]|Href].
  - pose proof (eval_deterministic _ _ HR _ HR') as ->.
    exact (paper_ontology_rows_declaration_sound _ _ _ Hin HD).
  - pose proof (eval_deterministic _ _ HR _ Href) as ->.
    pose proof (eval_deterministic _ _ HD _ (eval_k _ _)) as ->.
    apply refusal_value_sound.
Qed.

Theorem paper_evaluation_preserves_typing :
  forall e v T, e ==> v -> infer_expression paper_ontology @ e ==> Sm T ->
    infer paper_ontology @ v ==> Sm T.
Proof.
  intros e v T HE HI; exact (evaluation_preserves_typing _ e v T paper_ontology_sound HE HI).
Qed.

(** The bare name test cannot be typed at a salary (computed). *)
Lemma name_test_salary_untyped :
  infer paper_ontology @ salary zero ==> Sm ('Salary) /\
  ~ (exists T, infer_expression paper_ontology @ (name_test salary_nm @ salary zero) ==> Sm T).
Proof.
  split.
  - apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity.
  - intros [T H].
    assert (HL : infer_expression paper_ontology @ (name_test salary_nm @ salary zero) ==> Lf)
      by (apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity).
    pose proof (eval_deterministic _ _ H _ HL); discriminate.
Qed.
