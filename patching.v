(** * Patching programs and expressions (paper: "Patching a query program", "Patching expressions").

    Patching query programs: the lambda program
    [paid_at_least_57] and its update to [paid_at_least_58], the update of
    [paid_over_57] to [paid_over_58]
    ([salary_update_paid_over_57],
    [salary_update_paid_at_least_57]) and their typing; and
    patching expressions
    ([update_preserves_expression_typing]). *)


From Stdlib Require Import String Bool Lia.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import arrays booleans functions data_types recursion paper_ontology updates conditionals queries.
From TreeTyping Require Import customisation.
Open Scope string_scope.
Unset Default Proof Using.
Section TraversalExamples.
Local Ltac salary_traverse := repeat first
  [ eassumption | apply salary_update_tag_free; reflexivity |
    apply update_leaf | apply update_stem |
    apply update_miss; [solve [let payload := fresh "payload" in let Hbad := fresh "Hbad" in intros payload Hbad; discriminate Hbad] | |] ].
Local Ltac company_app :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
    first [is_evar T; fail 1 | idtac];
    first [eassumption |
      lazymatch T with
      | ?A --> ?B => apply type_app_abstract; apply funty_eliminator_eval
      | employee_fields => unfold employee_fields; company_app
      | department_fields => unfold department_fields; company_app
      | 'Salary => first [apply type_app_record; cbv; discriminate
          | apply type_app_abstract; apply payload_eliminator_some]
      | 'Employee => first [apply type_app_record; cbv; discriminate
          | apply type_app_abstract; apply payload_eliminator_some]
      | 'Department => first [apply type_app_record; cbv; discriminate
          | apply type_app_abstract; apply payload_eliminator_some]
      | nat_split => unfold nat_split
      | cons_step => unfold cons_step
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | 'Nat => apply type_app_Nat
      | 'tagged[?E,?N] => apply type_app_abstract; ty_elim
      | Lf => apply type_app_leaf_ev
      | Fk Lf _ => apply type_app_K_ev
      | 'I => apply type_app_I
      | Sm _ => apply type_app_stem_ev
      | Fk (Sm _) _ => new_S; [solve [intros; discriminate] | | |]
      end]
  | |- type_app_stem _ @ type_app _ @r _ @r _ ==> _ =>
    first [apply type_app_stem_function |
      apply type_app_stem_structural; solve [intros; discriminate]]
  end.
Local Ltac company_infer := first
  [ eassumption
  | apply infer_nat_ge
  | apply infer_zero; apply company_number
  | apply employee_at_typed
  | apply infer_salary; [apply company_salary | apply numeral_typed; apply company_number]
  | eapply infer_nil_value; [apply company_list |]
  | eapply infer_lam; [ | |]
  | eapply infer_fork | apply infer_stem | apply infer_leaf ].
Definition department_query threshold g witness domain :=
  lam ((filter_value (salary_predicate threshold g witness)) 'C department_employees witness) domain.
Lemma department_query_typed : forall bound m witness domain,
  infer company_ontology @ witness ==> Sm ('Employee) ->
  infer company_ontology @ domain ==> Sm ('Department) ->
  infer company_ontology @ department_query (salary (numeral bound)) (salary (numeral m)) witness domain ==>
    Sm ('Department --> 'List['Employee]).
Proof.
  intros bound m witness domain Hd HD.
  destruct (salary_predicate_typed bound m witness Hd) as [P [HP HPa]].
  unfold department_query; eapply infer_lam.

  - pose proof (infer_filter_value company_ontology _ _ HP) as HF.
    pose proof (department_employees_infer witness Hd); infer_tac.
  - exact HD.
  - eapply type_app_compose; [solve [reject_name]| | |]; [discriminate | apply department_employees_type_app |].
    apply type_app_filter_value; [exact company_list|exact HPa].
Qed.

Definition paid_at_least_57 := department_query (salary (numeral 57)) (salary (numeral 50)) (employee_witness 50) department_example.


Lemma salary_update_lam : forall f f' d d',
  salary_update_example @ f ==> f' -> salary_update_example @ d ==> d' ->
  salary_update_example @ lam f d ==> lam f' d'.
Proof.
  intros; unfold lam; apply salary_update_tagged; try discriminate; try reflexivity.
  salary_traverse.
Qed.
Lemma salary_update_decorate : forall f f' d d',
  salary_update_example @ f ==> f' -> salary_update_example @ d ==> d' ->
  salary_update_example @ 'decorate[f,d] ==> 'decorate[f',d'].
Proof. intros; salary_traverse. Qed.
Lemma salary_update_nat_ge : salary_update_example @ nat_ge ==> nat_ge.
Proof. apply salary_update_tag_free; vm_compute; reflexivity. Qed.
Lemma salary_update_salary_test : forall n m,
  salary_update_example @ salary_test (salary (numeral n)) (salary (numeral m)) ==>
    salary_test (salary (numeral (S n))) (salary (numeral (S m))).
Proof.
  intros n m; pose proof salary_update_nat_ge.
  assert (salary_update_example @ salary (numeral n) ==> salary (numeral (S n)))
    by (apply update_hit; apply salary_raise_eval).
  assert (salary_update_example @ salary (numeral m) ==> salary (numeral (S m)))
    by (apply update_hit; apply salary_raise_eval).
  unfold salary_test; salary_traverse.
Qed.
Lemma salary_update_department_employees : forall d d',
  salary_update_example @ d ==> d' ->
  salary_update_example @ department_employees d ==> department_employees d'.
Proof.
  intros d d' Hd.
  assert (Hnil : salary_update_example @ nil_value d ==> nil_value d')
    by (apply salary_update_nil; exact Hd).
  unfold department_employees, lam, swap, wrap, department.
  salary_traverse.
Qed.
Lemma salary_update_filter_from : forall p p' d d',
  salary_update_example @ p ==> p' -> salary_update_example @ d ==> d' ->
  salary_update_example @ filter_from p d ==> filter_from p' d'.
Proof.
  intros p p' d d' Hp Hd.
  assert (HC : salary_update_example @ cons_step ==> cons_step)
    by (apply salary_update_tag_free; vm_compute; reflexivity).
  assert (HN : salary_update_example @ nil_value d ==> nil_value d')
    by (apply salary_update_nil; exact Hd).
  unfold filter_from, foldright_value, filter_step, swap.
  salary_traverse.
Qed.
Lemma salary_update_filter : forall p p',
  salary_update_example @ p ==> p' ->
  salary_update_example @ filter_value p ==> filter_value p'.
Proof.
  intros p p' Hp.
  assert (HC : salary_update_example @ emptied ==> emptied)
    by (apply salary_update_tag_free; vm_compute; reflexivity).
  assert (HD : salary_update_example @ cons_step ==> cons_step)
    by (apply salary_update_tag_free; vm_compute; reflexivity).
  unfold filter_value, filter_step.
  salary_traverse.
Qed.
Lemma paid_at_least_57_typed : infer company_ontology @ paid_at_least_57 ==> Sm ('Department --> 'List['Employee]).
Proof. apply department_query_typed; [apply employee_at_typed | apply department_example_typed]. Qed.

Local Ltac company_query_app := first
  [ lazymatch goal with
    | |- type_app _ @ ('Query[?B]) @r _ ==> _ =>
      apply type_app_abstract; apply query_eliminator_eval
    | |- type_app_stem _ @ type_app _ @r _ @r _ ==> _ =>
      apply type_app_stem_tagged; apply query_abstractor_supported;
      [apply company_queries | first [apply query_abstractor_K | eapply query_abstractor_S | apply query_abstractor_triage | apply query_abstractor_diagonal]]
    end
  | company_app ].
Local Ltac company_query_infer := first
  [ eassumption
  | eapply infer_Kq; [apply company_queries|]
  | eapply infer_diagonal_query; [apply company_queries|]
  | eapply infer_S_q; [apply company_queries| | |]
  | eapply infer_tq; [apply company_queries|]
  | apply infer_append
  | company_infer ].
Local Opaque type_app infer equal equal1 get_tagname.
Local Hint Resolve company_number company_booleans company_salary company_employee company_department company_list company_queries : core.
Local Ltac choice_app := first
 [ solve [apply type_app_stem_tagged; eapply query_abstractor_supported; [exact company_queries|]; eapply queries.constructor_choice;
      [apply concreteb_sound; vm_compute; reflexivity|exact company_employee_declared]]
 | company_query_app ].
Local Ltac is_list_go := repeat first [apply is_list_cons | apply is_list_nil].
Local Ltac append_go := first
  [ apply append_nil
  | apply append_cons; [is_list_go|is_list_go|append_go] ].
Local Ltac collect_nodes := first
  [ apply collect_employees_employee
  | apply collect_employees_nil
  | apply collect_employees_cell; collect_nodes
  | apply collect_employees_decoration; collect_nodes
  | apply collect_employees_leaf
  | apply collect_employees_stem; collect_nodes
  | eapply collect_employees_fork_miss;
    [ reflexivity | first [apply get_tagname_some | apply get_tagname_none; intros; discriminate]
    | intros; discriminate | discriminate | collect_nodes | collect_nodes
    | append_go ] ].
Lemma salary_update_append : salary_update_example @ append ==> append.
Proof. apply salary_update_tag_free; tag_free_tac. Qed.
Lemma salary_update_singleton : salary_update_example @ singleton ==> singleton.
Proof. apply salary_update_tag_free; tag_free_tac. Qed.
(** The decoration test inspects a fixed shape. Salary traversal leaves its
    Boolean and Query coefficients unchanged. *)
Lemma pc_tagged : forall p f s, exists e, pc p f s = 'tagged[e, query_nm].
Proof. intros [| |p|a c] f s; cbn [pc]; eexists; reflexivity. Qed.
Lemma salary_update_Kq : forall x, salary_update_example @ x ==> x ->
  salary_update_example @ ('Kq x) ==> ('Kq x).
Proof.
  intros; apply salary_update_tagged; try discriminate; try reflexivity; salary_traverse.
Qed.
Lemma salary_update_tq : forall a e c,
  salary_update_example @ a ==> a ->
  salary_update_example @ 'tagged[e, query_nm] ==> 'tagged[e, query_nm] ->
  salary_update_example @ c ==> c ->
  salary_update_example @ ('tq[a,'tagged[e, query_nm],c]) ==> ('tq[a,'tagged[e, query_nm],c]).
Proof.
  intros; apply salary_update_tagged; try discriminate; try reflexivity; salary_traverse.
Qed.
Lemma salary_update_pc : forall p f s,
  salary_update_example @ f ==> f -> salary_update_example @ s ==> s ->
  salary_update_example @ pc p f s ==> pc p f s.
Proof.
  induction p as [| |p IH|a IHa c IHc]; intros f s Hf Hs; cbn [pc].
  - apply salary_update_Kq; assumption.
  - apply salary_update_tq; repeat (assumption || apply salary_update_Kq).
  - pose proof (IH f s Hf Hs) as H; destruct (pc_tagged p f s) as [e He]; rewrite He in *.
    apply salary_update_tq; repeat (assumption || apply salary_update_Kq).
  - assert (Hk : salary_update_example @ ('Kq f) ==> ('Kq f)) by (apply salary_update_Kq; assumption).
    apply salary_update_tq; [assumption|assumption|apply IHa; [assumption|apply IHc; assumption]].
Qed.
Lemma salary_update_pattern_query : forall p,
  salary_update_example @ pattern_query p ==> pattern_query p.
Proof.
  intros; apply salary_update_pc; apply salary_update_tagged; try discriminate;
    try reflexivity; apply salary_update_tag_free; reflexivity.
Qed.
Lemma salary_update_is_decoration_query :
  salary_update_example @ is_decoration_query ==> is_decoration_query.
Proof. apply salary_update_pattern_query. Qed.

Lemma salary_update_is_list_q : salary_update_example @ is_list_q ==> is_list_q.
Proof. apply salary_update_pattern_query. Qed.

Lemma salary_update_typed_K_q : salary_update_example @ typed_K_q ==> typed_K_q.
Proof. apply salary_update_tag_free; vm_compute; reflexivity. Qed.

Lemma salary_update_collect_employees : forall d d',
  salary_update_example @ d ==> d' ->
  salary_update_example @ collect_employees d ==> collect_employees d'.
Proof.
  intros d d' Hd.
  assert (Hnil : salary_update_example @ nil_value d ==> nil_value d') by (apply salary_update_nil; exact Hd).
  pose proof salary_update_append as HA.
  pose proof salary_update_singleton as HS.
  pose proof salary_update_department_employees as HD.
  pose proof salary_update_is_decoration_query as HW.
  pose proof salary_update_is_list_q as HDQ.
  pose proof salary_update_typed_K_q as Hconstant.
  unfold collect_employees, fix_query, collect_function, collect_function_body, cons_case_term,
    cond_t, payload_t, path_to_cell, flag_pat,
    choice_term, ghost_case_term, query_decorated_program_term, employee_fork_query_term, sum_fork_term, Z; cbn -[is_list_q].
  salary_traverse.
Qed.
Lemma salary_update_paid_over : forall bound m d d',
  salary_update_example @ d ==> d' ->
  salary_update_example @ paid_over (salary (numeral bound)) (salary (numeral m)) d ==>
    paid_over (salary (numeral (S bound))) (salary (numeral (S m))) d'.
Proof.
  intros bound m d d' Hd.
  pose proof (salary_update_collect_employees d d' Hd) as HC.
  assert (HF : salary_update_example @ filter_from (salary_predicate (salary (numeral bound)) (salary (numeral m)) d) d ==>
    filter_from (salary_predicate (salary (numeral (S bound))) (salary (numeral (S m))) d') d').
  { apply salary_update_filter_from; [|exact Hd].
    apply salary_update_decorate; [apply salary_update_salary_test|exact Hd]. }
  assert (Hnil : salary_update_example @ nil_value d ==> nil_value d') by (apply salary_update_nil; exact Hd).
  assert (HL : salary_update_example @ filter_function (salary_predicate (salary (numeral bound)) (salary (numeral m)) d) d ==>
    filter_function (salary_predicate (salary (numeral (S bound))) (salary (numeral (S m))) d') d').
  { unfold filter_function; apply salary_update_decorate; assumption. }
  unfold paid_over; salary_traverse.
Qed.
Lemma paid_over_update_preserves_type : forall bound m d d',
  infer company_ontology @ d ==> Sm ('Employee) ->
  salary_update_example @ d ==> d' ->
  infer company_ontology @ paid_over (salary (numeral (S bound))) (salary (numeral (S m))) d' ==>
    Sm ('Query['List['Employee]]).
Proof.
  intros bound m d d' Hd Hupdate.
  eapply abstract_update_preserves_typing with (x := paid_over (salary (numeral bound)) (salary (numeral m)) d).
  - exact paper_ontology_sound.
  - apply company_update_typed.
  - apply paid_over_typed; assumption.
  - apply salary_update_paid_over; exact Hupdate.
Qed.


Local Ltac add_counts := first
  [ apply (addition_zero company_ontology company_booleans company_number )
  | apply (addition_succ company_ontology company_booleans company_number ); add_counts ].
Local Ltac count_nodes := first
  [ apply count_employees_employee
  | apply count_employees_nil
  | apply count_employees_cell; count_nodes
  | apply count_employees_decoration; count_nodes
  | apply count_employees_leaf
  | apply count_employees_stem; count_nodes
  | eapply count_employees_fork_miss;
    [ reflexivity | first [apply get_tagname_some | apply get_tagname_none; intros; discriminate]
    | intros; discriminate | discriminate | count_nodes | count_nodes | add_counts ] ].
Local Ltac sum_nodes := first
  [ apply salary_sum_salary
  | apply salary_sum_leaf
  | apply salary_sum_stem; bill_nodes
  | eapply salary_sum_fork;
    [ first [apply get_tagname_some | apply get_tagname_none; intros; discriminate]
    | discriminate | bill_nodes | bill_nodes ] ]
with bill_nodes := first
  [ apply naive_salary_bill_step; sum_nodes
  | apply salary_bill_nil
  | apply salary_bill_cell; bill_nodes
  | apply salary_bill_decoration; bill_nodes
  | apply salary_bill_other; [reflexivity|intros; discriminate|sum_nodes] ].

Local Ltac su_traverse := repeat first
  [ eassumption | apply su_tag_free; reflexivity |
    apply su_hit |
    apply ghost_guarded_leaf | apply ghost_guarded_stem |
    apply ghost_guarded_decoration |
    apply ghost_guarded_miss;
      [reflexivity
      |solve [let g := fresh in let w := fresh in let Hbad := fresh in intros g w Hbad; discriminate Hbad]
      |solve [let p := fresh in let Hbad := fresh in intros p Hbad; discriminate Hbad]| |] ].
Local Ltac su_go := repeat first
  [ eassumption | apply su_tag_free; reflexivity |
    apply su_hit | apply su_nil |
    apply ghost_guarded_leaf | apply ghost_guarded_stem |
    apply ghost_guarded_decoration |
    apply ghost_guarded_miss;
      [reflexivity
      |solve [let g := fresh in let w := fresh in let Hbad := fresh in intros g w Hbad; discriminate Hbad]
      |solve [let p := fresh in let Hbad := fresh in intros p Hbad; discriminate Hbad]| |] ].
(** ** The salary update on the query programs *)
Lemma su_nat_ge : salary_update @ nat_ge ==> nat_ge.
Proof. apply su_tag_free; vm_compute; reflexivity. Qed.
(** The update raises the threshold and leaves the getter's ghost alone. *)
Lemma su_salary_test : forall n g,
  salary_update @ salary_test (salary (numeral n)) g ==>
    salary_test (salary (numeral (S n))) g.
Proof.
  intros n g; pose proof su_nat_ge; pose proof (su_hit n).
  assert (salary_update @ 'decorate['snd, zero '* g] ==> 'decorate['snd, zero '* g])
    by (apply ghost_guarded_decoration; apply su_tag_free; reflexivity).
  assert (salary_update @ 'decorate['I, zero] ==> 'decorate['I, zero])
    by (apply ghost_guarded_decoration; apply su_tag_free; reflexivity).
  unfold salary_test; su_go.
Qed.
Lemma su_salary_predicate : forall n g d,
  salary_update @ salary_predicate (salary (numeral n)) g d ==>
    salary_predicate (salary (numeral (S n))) g d.
Proof. intros; apply ghost_guarded_decoration; apply su_salary_test. Qed.
(** Filtering and concatenation keep their ghosts: every lambda in them
    whose ghost mentions the witness is a closed lambda program. *)
Lemma su_filter : forall p p',
  salary_update @ p ==> p' ->
  salary_update @ filter_value p ==> filter_value p'.
Proof.
  intros p p' Hp.
  assert (HC : salary_update @ emptied ==> emptied)
    by (apply su_tag_free; tag_free_tac).
  assert (HD : salary_update @ cons_step ==> cons_step)
    by (apply su_tag_free; vm_compute; reflexivity).
  unfold filter_value, filter_step.
  su_go.
Qed.
Lemma su_filter_from : forall p p' d,
  salary_update @ p ==> p' ->
  salary_update @ filter_from p d ==> filter_from p' d.
Proof.
  intros p p' d Hp.
  assert (HD : salary_update @ cons_step ==> cons_step)
    by (apply su_tag_free; vm_compute; reflexivity).
  assert (HN : salary_update @ nil_value d ==> nil_value d) by apply ghost_guarded_nil.
  unfold filter_from, foldright_value, filter_step, swap.
  su_go.
Qed.
Lemma su_append : salary_update @ append ==> append.
Proof. apply su_tag_free; tag_free_tac. Qed.
Lemma su_singleton : salary_update @ singleton ==> singleton.
Proof. apply su_tag_free; tag_free_tac. Qed.
Lemma su_Kq : forall x, salary_update @ x ==> x -> salary_update @ ('Kq x) ==> ('Kq x).
Proof. intros; apply su_tagged; try discriminate; try reflexivity; su_go. Qed.
Lemma su_tq : forall a e c, salary_update @ a ==> a ->
  salary_update @ 'tagged[e, query_nm] ==> 'tagged[e, query_nm] ->
  salary_update @ c ==> c ->
  salary_update @ ('tq[a,'tagged[e, query_nm],c]) ==> ('tq[a,'tagged[e, query_nm],c]).
Proof.
  intros a e c Ha He Hc; apply su_tagged; try discriminate; try reflexivity.
  apply ghost_guarded_miss.
  - unfold off_list, list_pat; cbn [pattern_matches]; destruct a; reflexivity.
  - intros g w Hbad; discriminate Hbad.
  - intros p Hbad; discriminate Hbad.
  - apply ghost_guarded_miss.
    + unfold off_list, list_pat; cbn [pattern_matches];
        rewrite Bool.andb_false_r; reflexivity.
    + intros g w Hbad; discriminate Hbad.
    + intros p Hbad; discriminate Hbad.
    + exact Ha.
    + exact He.
  - exact Hc.
Qed.
Lemma su_pc : forall p f s,
  salary_update @ f ==> f -> salary_update @ s ==> s -> salary_update @ pc p f s ==> pc p f s.
Proof.
  induction p as [| |p IH|a IHa c IHc]; intros f s Hf Hs; cbn [pc].
  - apply su_Kq; assumption.
  - apply su_tq; repeat (assumption || apply su_Kq).
  - pose proof (IH f s Hf Hs) as H; destruct (pc_tagged p f s) as [e He]; rewrite He in *.
    apply su_tq; repeat (assumption || apply su_Kq).
  - assert (Hk : salary_update @ ('Kq f) ==> ('Kq f)) by (apply su_Kq; assumption).
    apply su_tq; [assumption|assumption|apply IHa; [assumption|apply IHc; assumption]].
Qed.
Lemma su_pattern_query : forall p, salary_update @ pattern_query p ==> pattern_query p.
Proof.
  intros; apply su_pc; apply su_tagged; try discriminate; try reflexivity;
    apply su_tag_free; reflexivity.
Qed.
Lemma su_is_list_q : salary_update @ is_list_q ==> is_list_q.
Proof. apply su_pattern_query. Qed.
Lemma su_collect : forall d,
  salary_update @ collect_employees d ==> collect_employees d.
Proof.
  intros d.
  pose proof su_append as HA.
  pose proof su_singleton as HS.
  pose proof su_is_list_q as HDQ.
  pose proof (su_pattern_query decoration_pattern) as HW; fold is_decoration_query in HW.
  assert (Hc : salary_update @ typed_K_q ==> typed_K_q)
    by (apply su_tag_free; vm_compute; reflexivity).
  unfold collect_employees, fix_query, collect_function, collect_function_body, cons_case_term,
    cond_t, payload_t, path_to_cell, flag_pat,
    choice_term, ghost_case_term, query_decorated_program_term, Z; cbn -[is_list_q].
  su_go.
Qed.
Lemma su_paid_over : forall bound g d,
  salary_update @ paid_over (salary (numeral bound)) g d ==>
    paid_over (salary (numeral (S bound))) g d.
Proof.
  intros bound g d.
  pose proof (su_collect d) as HC.
  pose proof (su_filter_from _ _ d (su_salary_predicate bound g d)) as HF.
  assert (HL : salary_update @ filter_function (salary_predicate (salary (numeral bound)) g d) d ==>
    filter_function (salary_predicate (salary (numeral (S bound))) g d) d)
    by (unfold filter_function; apply ghost_guarded_decoration; exact HF).
  unfold paid_over; su_go.
Qed.
Lemma su_department_employees : forall d,
  salary_update @ department_employees d ==> department_employees d.
Proof.
  intros; unfold department_employees; apply su_lam.
  unfold swap; su_go; apply su_lam; apply su_tag_free; reflexivity.
Qed.
Lemma su_department_query : forall bound g d dom,
  salary_update @ department_query (salary (numeral bound)) g d dom ==>
    department_query (salary (numeral (S bound))) g d dom.
Proof.
  intros bound g d dom.
  pose proof (su_department_employees d) as HD.
  pose proof (su_filter_from _ _ d (su_salary_predicate bound g d)) as HF.
  unfold department_query; apply su_lam; su_go.
Qed.

(** ** The extended example with the ghost-aware update

    The update raises the threshold and nothing else: every ghost in the
    query, its lists and its functions stays at E(0,0), and the getter's
    ghost salary stays at 0. *)
Definition paid_over_58 :=
  paid_over (salary (numeral 58)) (salary (numeral 0)) (employee_witness 0).
Definition paid_at_least_58 :=
  department_query (salary (numeral 58)) (salary (numeral 50)) (employee_witness 50) department_example.
Lemma salary_update_paid_over_57 :
  salary_update @ paid_over_57 ==> paid_over_58.
Proof. apply su_paid_over. Qed.

(** The salary update, its type application at
    departments, and its action on a query program. *)
Theorem salary_update_polymorphic :
  infer paper_ontology @ salary_update ==> Sm ('Update) /\
  type_app paper_ontology @ ('Update) @r ('Department) ==> Sm ('Department) /\
  salary_update @ paid_over_57 ==> paid_over_58.
Proof.
  split; [exact salary_update_typed|split; [apply type_app_Update|exact salary_update_paid_over_57]].
Qed.

Theorem salary_update_paid_at_least_57 :
  salary_update @ paid_at_least_57 ==> paid_at_least_58.
Proof. apply su_department_query. Qed.
Lemma paid_over_58_typed :
  infer company_ontology @ paid_over_58 ==> Sm ('Query['List['Employee]]).
Proof.
  eapply abstract_update_preserves_typing.
  - exact paper_ontology_sound.
  - apply salary_update_typed.
  - apply paid_over_57_typed.
  - apply salary_update_paid_over_57.
Qed.
Lemma paid_at_least_58_typed :
  infer company_ontology @ paid_at_least_58 ==> Sm ('Department --> 'List['Employee]).
Proof.
  eapply abstract_update_preserves_typing.
  - exact paper_ontology_sound.
  - apply salary_update_typed.
  - apply paid_at_least_57_typed.
  - apply salary_update_paid_at_least_57.
Qed.
Lemma table_58_2026 : paid_over_58 @ department_2026 ==> paid_58_in_2026.
Proof.
  apply paid_over_department_eval.
  apply filter_keep_first_last; apply salary_predicate_eval.
Qed.
(** Updating the result r of the 2025 query gives r+, the result of the
    updated query on the 2026 department; the ghost stays at E(0,50). *)
Lemma salary_update_result : salary_update @ paid_57_in_2025 ==> paid_58_in_2026.
Proof.
  unfold paid_57_in_2025, original_at57, paid_58_in_2026.
  apply su_cell; [apply su_employee|].
  apply su_cell; [apply su_employee|].
  apply ghost_guarded_nil.
Qed.
(** The pending application [q57 @ d2025] is patched to [q58 @ d2026]. *)
Lemma salary_update_pending_query :
  salary_update @ (paid_over_57 @ department_example) ==>
    paid_over_58 @ department_2026.
Proof.
  apply ghost_guarded_miss.
  - reflexivity.
  - intros g w Hbad; discriminate Hbad.
  - intros p Hbad; discriminate Hbad.
  - apply ghost_guarded_stem; exact salary_update_paid_over_57.
  - apply ghost_guarded_stem; exact salary_update_department_2025.
Qed.

End TraversalExamples.

(** Paper names for the company examples (specialisation.tex, updates.tex,
    witness-protection.tex). The ghost employee is E(0,50) throughout. *)


(** These are the actual company programs, under the combined declarations. *)
Example all_department_typed :
  infer paper_ontology @ department_example ==> Sm (wrap_type department_fields department_nm).
Proof. apply department_example_typed. Qed.
Example all_salary_update_typed : 
  infer paper_ontology @ salary_update_example ==> Sm ('Update).
Proof. apply company_update_typed; reflexivity. Qed.
Example all_paid_over_typed : 
  infer paper_ontology @ paid_over_57 ==> Sm ('Query['List[wrap_type employee_fields employee_nm]]).
Proof. apply paid_over_57_typed; reflexivity. Qed.
Example all_ghost_salary_update_typed :
  infer paper_ontology @ salary_update ==> Sm ('Update).
Proof. apply salary_update_typed; reflexivity. Qed.

(** Under the combined declarations, the pending query
    [paid_over_57 @ department_2025] has type
    [List[Employee]]. *)
Definition employee_list :=
  'tagged[list_eliminator (wrap_type employee_fields employee_nm), list_nm].

Lemma pending_query_typed :
  infer_expression paper_ontology @ (paid_over_57 @ department_example) ==>
    Sm employee_list.
Proof.
  eapply query_expression_application_typing;
    apply infer_expression_stem;
    [exact all_paid_over_typed | exact all_department_typed].
Qed.

(** Read as a value, the pending query has the type
    [Query[List[Employee]] @ Department] of its parts, and the update
    [salary_update] applied to it preserves that type. *)
Theorem salary_update_pending_query_typed :
  infer_expression paper_ontology
    @ (salary_update @ (paid_over_57 @ department_2025)) ==>
    Sm (Fk (Sm ('Query['List['Employee]])) (Sm ('Department))).
Proof.
  eapply infer_expression_fork;
    [apply infer_expression_stem; exact all_ghost_salary_update_typed
    |apply infer_expression_stem|apply type_app_Update].
  eapply infer_fork;
    [apply infer_stem; exact all_paid_over_typed
    |apply infer_stem; exact all_department_typed|].
  apply app_stem, type_app_stem_structural; intros C N; discriminate.
Qed.


Unset Default Proof Using.

(**********************************************************************)
(* Updating pending computations.                                     *)
(**********************************************************************)

(** An expression is also a tree, so a generic update can traverse it
    before it is evaluated.  This file shows that such a patch preserves
    expression typing, and that in the salary example patching a pending
    query gives the same result as patching the query's result.

    The argument rests on one observation.  The value type of a typable
    expression tree mirrors its structure: a quoted value [Sm v] has type
    [Sm V], and an application [Fk e1 e2] has type [Fk E1 E2].  Such a tree
    of types is never tag-shaped, since a tag would need a leaf where every
    typable expression has a stem or fork.  Expression typing is computed
    from these value types alone, so any tree with the same value type has
    the same expression type.  Value-level preservation for updates then
    gives expression-level preservation. *)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions queries booleans updates paper_ontology conditionals data_types customisation.

Set Default Proof Using "Type".

(** * Value types of expression trees *)

(** The shape of the value type of a typable expression: quoted values
    give stems, applications give forks, and no leaf occurs. *)
Fixpoint expression_type_shape (E : Combination) : Prop :=
  match E with
  | Lf => False
  | Sm _ => True
  | Fk E1 E2 => expression_type_shape E1 /\ expression_type_shape E2
  end.

(** A tag [S2[K1 C, S2[K, K1 N]]] has a leaf at the head of [K1 N], so an
    application of such types is never tag-shaped. *)
Lemma expression_type_untagged : forall E1 E2,
  expression_type_shape E2 -> forall C N, Fk E1 E2 <> 'tagged[C,N].
Proof.
  intros E1 E2 H2 C N Heq; inversion Heq; subst; cbn in H2; tauto.
Qed.

(** The value type of a typable expression mirrors it, and determines its
    expression type: any tree with the same value type has the same
    expression type. *)
Lemma expression_type_factors : forall AI e T,
  infer_expression AI @ e ==> Sm T ->
  exists E, expression_type_shape E /\ infer AI @ e ==> Sm E /\
    forall e', infer AI @ e' ==> Sm E -> infer_expression AI @ e' ==> Sm T.
Proof.
  intros AI e; induction e as [|u _|e1 IH1 e2 IH2]; intros T H.
  - pose proof (eval_deterministic _ _ H _ (infer_expression_leaf AI));
      discriminate.
  - apply infer_expression_stem_inv in H.
    exists (Sm T); repeat split.
    + apply infer_stem; exact H.
    + intros e' He'.
      destruct (infer_stem_result_inv AI e' T He') as [t [-> Ht]].
      apply infer_expression_stem; exact Ht.
  - destruct (infer_expression_fork_inv AI e1 e2 T H)
      as [T1 [T2 [H1 [H2 Happ]]]].
    destruct (IH1 T1 H1) as [E1 [S1 [V1 D1]]].
    destruct (IH2 T2 H2) as [E2 [S2 [V2 D2]]].
    exists (Fk E1 E2); repeat split; try assumption.
    + eapply infer_fork; [exact V1|exact V2|].
      apply app_stem; apply type_app_stem_structural.
      apply expression_type_untagged; exact S2.
    + intros e' He'; destruct e' as [|u|u1 u2].
      * pose proof (eval_deterministic _ _ He' _ (infer_leaf AI));
          discriminate.
      * destruct (infer_stem_inv AI u _ He') as [U [HU _]]; discriminate.
      * destruct (infer_fork_inv AI u1 u2 _ He') as [U1 [U2 [Hu1 [Hu2 Ha]]]].
        apply app_stem_inv in Ha.
        destruct (tagged_decide (Fk U1 U2)) as [[C [N Heq]]|Hplain].
        -- inversion Heq; subst U1 U2.
           destruct (type_app_stem_tagged_success_inv AI _ _ _ _ Ha)
             as [E [_ HE]].
           exfalso; eapply expression_type_untagged; [exact S2|exact HE].
        -- pose proof (type_app_stem_structural_inv AI _ _ _ _ Hplain Ha)
             as HR; inversion HR; subst U1 U2.
           eapply infer_expression_fork; [apply D1|apply D2|]; eassumption.
Qed.

(** * Updates preserve expression typing *)

Theorem update_preserves_expression_typing : forall (AI : Decl) u e e' T,
  ontology_sound AI -> infer AI @ u ==> Sm ('Update) ->
  infer_expression AI @ e ==> Sm T -> u @ e ==> e' ->
  infer_expression AI @ e' ==> Sm T.
Proof.
  intros AI u e e' T Hsound Hu He Hupd.
  destruct (expression_type_factors AI e T He) as [E [_ [HE Hdet]]].
  apply Hdet; eapply abstract_update_preserves_typing; eassumption.
Qed.

(** * Patching a pending query *)


(** * Patching with the ghost-aware salary update

    [salary_update] patches the pending query [q57 @ d2025] into
    [q58 @ d2026], where the department's ghost employee stays on the
    minimum wage. Patching then running agrees with running then patching:
    r = [E(1,58),E(3,57)] and r+ = [E(1,59),E(3,58)]. *)
Lemma ghost_pending_query_updated :
  salary_update @ (paid_over_57 @ department_2025) ==>
    paid_over_58 @ department_2026.
Proof. exact salary_update_pending_query. Qed.

Theorem patch_commutes_with_evaluation :
  (salary_update @ (paid_over_57 @ department_2025) ==>
     paid_over_58 @ department_2026 /\
   paid_over_58 @ department_2026 ==> paid_58_in_2026) /\
  (paid_over_57 @ department_2025 ==> paid_57_in_2025 /\
   salary_update @ paid_57_in_2025 ==> paid_58_in_2026).
Proof.
  repeat split.
  - exact ghost_pending_query_updated.
  - exact table_58_2026.
  - exact table_57_2025.
  - exact salary_update_result.
Qed.

Lemma patched_query_typed :
  infer_expression paper_ontology @
    (paid_over_58 @ department_2026) ==> Sm employee_list.
Proof.
  eapply update_preserves_expression_typing.
  - exact paper_ontology_sound.
  - exact all_ghost_salary_update_typed.
  - exact pending_query_typed.
  - exact ghost_pending_query_updated.
Qed.
