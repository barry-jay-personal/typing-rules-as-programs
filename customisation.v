(** * Querying a department and raising salaries (paper: "Querying a department", "Raising salaries").

    The running company example: salary updates on data, employees
    and departments, ghost-aware employee collection and counting
    ([count_employees]), the threshold query [paid_over_57], the salary bills ([naive_salary_bill], [salary_bill]),
    the naive and ghost-aware salary updates and [department_2026].

    The patching of query programs and expressions
    is in patching.v, which reopens a Rocq section of the same name and repeats
    the local tactics and declarations it needs. *)


From Stdlib Require Import String Bool Lia.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import arrays booleans functions data_types recursion paper_ontology updates conditionals queries.
Open Scope string_scope.
Unset Default Proof Using.
Section TraversalExamples.

Lemma salary_base_ontology_row : salary_base_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold salary_base_ontology.
  apply extend_none_value; [apply is_named_case_none; unfold is_named_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply salary_case_none; unfold salary_nm, fun_nm; discriminate|].
  exact (functions_declared nat_decl).
Qed.
Definition salary_ontology := generic_ontology salary_base_ontology.
Canonical Structure salary_decl :=
  mkDecl salary_ontology (generic_ontology_row _ salary_base_ontology_row).
Lemma salary_ontology_supports_salary : supports_salary salary_ontology.
Proof.
  unfold supports_salary, salary_ontology; apply generic_ontology_ordinary; try discriminate.
  unfold salary_base_ontology; apply extend_none_value; [apply is_named_case_none; discriminate|].
  apply extend_some; apply salary_case_some.
Qed.
Lemma salary_ontology_supports_is_named : supports_is_named salary_ontology.
Proof.
  unfold supports_is_named, salary_ontology; apply generic_ontology_ordinary; try discriminate.
  unfold salary_base_ontology; apply extend_some; apply is_named_case_some.
Qed.
Lemma salary_ontology_supports_updates : supports_updates salary_ontology.
Proof. apply generic_ontology_updates. Qed.
Lemma salary_ontology_supports_number : supports_number salary_ontology.
Proof.
  unfold supports_number, salary_ontology; apply generic_ontology_ordinary; try discriminate.
  unfold salary_base_ontology; apply extend_none_value; [apply is_named_case_none; discriminate|].
  apply extend_none_value; [apply salary_case_none; discriminate|].
  apply nat_ontology_supports_number.
Qed.


Definition update_salary f := update salary_nm f.
Theorem infer_update_salary : forall (AI : Decl) f F,
  supports_salary AI -> supports_updates AI -> supports_is_named AI ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r 'Salary ==> Sm ('Salary) ->
  infer AI @ update_salary f ==> Sm ('Update).
Proof.
  intros AI f F HS HU HT Hf HF; unfold update_salary.
  eapply infer_update with (T := 'Nat); try (apply concreteb_sound; vm_compute; reflexivity); eauto using salary_payload_lookup; discriminate.
Qed.

Definition salary_update_example := update_salary salary_raise.
Lemma salary_zero_typed : infer salary_ontology @ salary zero ==> Sm ('Salary).
Proof.
  apply infer_salary; [apply salary_ontology_supports_salary|].
  apply infer_zero; apply salary_ontology_supports_number.
Qed.
Lemma salary_one_typed : infer salary_ontology @ salary one ==> Sm ('Salary).
Proof.
  apply infer_salary; [apply salary_ontology_supports_salary|].
  apply infer_one; apply salary_ontology_supports_number.
Qed.
Lemma salary_update_example_typed :
  infer salary_ontology @ salary_update_example ==> Sm ('Update).
Proof.
  unfold salary_update_example; eapply infer_update_salary.

  - apply salary_ontology_supports_salary.
  - apply salary_ontology_supports_updates.
  - apply salary_ontology_supports_is_named.
  - apply infer_tag_free; exact salary_raise_tag_free.
  - apply type_app_salary_raise; auto using salary_ontology_supports_salary, salary_ontology_supports_number.
Qed.
Lemma salary_update_example_changes_amount :
  salary_update_example @ salary zero ==> salary one.
Proof. apply update_hit; apply salary_raise_eval. Qed.
Lemma salary_amounts_differ : salary zero <> salary one.
Proof. unfold salary, wrap, one, succ, zero; discriminate. Qed.
Lemma salary_update_below_stem :
  salary_update_example @ Sm (salary zero) ==> Sm (salary one).
Proof. apply update_stem; apply salary_update_example_changes_amount. Qed.
Lemma salary_update_example_leaf : salary_update_example @ Lf ==> Lf.
Proof. apply update_leaf. Qed.

(** An unrelated Nat contains no Salary node and is left unchanged.
    In general, a different wrapper name is a miss, so traversal continues
    through that wrapper rather than skipping its children. *)
Lemma salary_update_example_preserves_nat : salary_update_example @ zero ==> zero.
Proof.
  unfold salary_update_example, update_salary, zero, nat_nm.
  repeat first [apply update_leaf | apply update_stem |
    apply update_miss; [intros p Hbad; discriminate Hbad | |]].
Qed.

Definition salary_pair := Fk (salary zero) (salary one).
Definition updated_salary_pair := Fk (salary one) (salary two).
Lemma salary_pair_updated : salary_update_example @ salary_pair ==> updated_salary_pair.
Proof.
  apply update_miss.
  - intros p Hbad; discriminate Hbad.
  - apply update_hit; apply salary_raise_eval.
  - apply update_hit; apply salary_raise_eval.
Qed.
Lemma salary_pair_typed :
  infer salary_ontology @ salary_pair ==> Sm (Fk ('Salary) ('Salary)).
Proof.
  unfold salary_pair; eapply infer_fork.
  - apply salary_zero_typed.
  - apply salary_one_typed.
  - apply type_app_stem_ev; apply type_app_stem_structural; discriminate.
Qed.


(** * Employees and departments

    Both records use the existing nominal-wrapper protocol. Employee stores
    [number * salary]; Department stores [manager * workers]. The manager
    and every worker have the same Employee type. *)
(** Standard structural pieces are traversed without changing their shape. *)
Lemma salary_update_tag_free : forall t,
  tag_free t = true -> salary_update_example @ t ==> t.
Proof.
  induction t as [|t IH|l IHl r IHr]; intro H.
  - apply update_leaf.
  - apply update_stem; apply IH; exact H.
  - cbn [tag_free] in H; apply andb_true_iff in H; destruct H as [H Hr].
    apply andb_true_iff in H; destruct H as [Htag Hl].
    apply update_miss.
    + intros p HE; assert (Hres : reserved_tagb (Fk l r) = true) by (rewrite HE; reflexivity).
      rewrite Hres in Htag; discriminate.
    + apply IHl; exact Hl.
    + apply IHr; exact Hr.
Qed.
Local Ltac salary_traverse := repeat first
  [ eassumption | apply salary_update_tag_free; reflexivity |
    apply update_leaf | apply update_stem |
    apply update_miss; [solve [let payload := fresh "payload" in let Hbad := fresh "Hbad" in intros payload Hbad; discriminate Hbad] | |] ].
Lemma salary_update_product : forall a b a' b',
  salary_update_example @ a ==> a' -> salary_update_example @ b ==> b' ->
  salary_update_example @ (a '* b) ==> (a' '* b').
Proof. intros; salary_traverse. Qed.
Lemma salary_update_tagged : forall C C' N,
  N <> salary_nm -> tag_free N = true ->
  salary_update_example @ C ==> C' ->
  salary_update_example @ ('tagged[C,N]) ==> 'tagged[C',N].
Proof.
  intros C C' N HN Hcon HC; apply update_miss.
  - intros p H; inversion H; contradiction.
  - salary_traverse.
  - assert (salary_update_example @ N ==> N) by (apply salary_update_tag_free; exact Hcon).
    salary_traverse.
Qed.
Lemma salary_update_numeral : forall n, salary_update_example @ numeral n ==> numeral n.
Proof.
  induction n; cbn [numeral].
  - unfold zero; apply salary_update_tagged; try discriminate; try reflexivity; salary_traverse.
  - unfold succ; apply salary_update_tagged; try discriminate; try reflexivity; salary_traverse.
Qed.
Lemma salary_update_employee : forall id n,
  salary_update_example @ employee (numeral id) (salary (numeral n)) ==>
    employee (numeral id) (salary (numeral (S n))).
Proof.
  intros; unfold employee, wrap; apply salary_update_tagged; try discriminate; try reflexivity.
  assert (salary_update_example @ numeral id ==> numeral id) by apply salary_update_numeral.
  assert (salary_update_example @ salary (numeral n) ==> salary (numeral (S n)))
    by (apply update_hit; apply salary_raise_eval).
  salary_traverse; apply salary_update_product; assumption.
Qed.
Lemma salary_update_swap : forall p p', salary_update_example @ p ==> p' ->
  salary_update_example @ swap p ==> swap p'.
Proof.
  intros; unfold swap; apply update_miss;
    [intros p0 Hbad; discriminate Hbad|apply salary_update_tag_free; reflexivity|].
  apply update_miss; [intros p0 Hbad; discriminate Hbad|apply update_leaf|assumption].
Qed.
Lemma salary_update_K1 : forall n n', salary_update_example @ n ==> n' ->
  salary_update_example @ ('K1 n) ==> ('K1 n').
Proof.
  intros; apply update_miss; [intros p0 Hbad; discriminate Hbad|apply update_leaf|assumption].
Qed.
Lemma salary_update_wait : forall M n n', tag_free M = true ->
  salary_update_example @ n ==> n' ->
  salary_update_example @ 'wait[M,n] ==> 'wait[M,n'].
Proof.
  intros M n n' HM Hn.
  apply update_miss; [intros p0 Hbad; discriminate Hbad| |apply salary_update_tag_free; reflexivity].
  apply update_stem.
  apply update_miss; [intros p0 Hbad; discriminate Hbad| |apply salary_update_K1; exact Hn].
  apply update_stem; apply salary_update_K1; apply salary_update_tag_free; exact HM.
Qed.
Lemma salary_update_nil : forall d d',
  salary_update_example @ d ==> d' ->
  salary_update_example @ nil_value d ==> nil_value d'.
Proof.
  intros; unfold nil_value; apply salary_update_tagged; try discriminate; try reflexivity.
  apply salary_update_wait; [reflexivity|assumption].
Qed.
(** The naive update reaches the ghost at the bottom of a list. *)
Lemma salary_update_cell : forall x s x' s',
  salary_update_example @ x ==> x' -> salary_update_example @ s ==> s' ->
  salary_update_example @ cell x s ==> cell x' s'.
Proof.
  intros; unfold cell, cell_carrier; apply salary_update_tagged; try discriminate; try reflexivity.
  apply salary_update_wait; [vm_compute; reflexivity|].
  apply salary_update_product; assumption.
Qed.
Lemma salary_update_department : forall m ws m' ws',
  salary_update_example @ m ==> m' -> salary_update_example @ ws ==> ws' ->
  salary_update_example @ department m ws ==> department m' ws'.
Proof.
  intros; unfold department, wrap; apply salary_update_tagged; try discriminate; try reflexivity.
  salary_traverse; apply salary_update_product; assumption.
Qed.

(** Employee 1 is the manager. Workers 2 and 3 earn 56 and 57;
    the manager earns 58, strictly more than either worker. The worker
    list is written from the empty list with ghost E(0,50), which stays at
    the bottom of the list. *)
Definition employee_at id amount := employee (numeral id) (salary (numeral amount)).
Definition employee_witness amount := employee_at 0 amount.
Definition department_example := department (employee_at 1 58)
  (cons_value (employee_at 2 56) (cons_value (employee_at 3 57) (nil_value (employee_witness 50)))).
Definition incremented_department := department (employee_at 1 59)
  (cons_value (employee_at 2 57) (cons_value (employee_at 3 58) (nil_value (employee_witness 51)))).
Lemma department_example_updated :
  salary_update_example @ department_example ==> incremented_department.
Proof.
  apply salary_update_department.
  - apply salary_update_employee.
  - apply salary_update_cell; [apply salary_update_employee|].
    apply salary_update_cell; [apply salary_update_employee|].
    apply salary_update_nil; apply salary_update_employee.
Qed.
Lemma employee_at_typed : forall id amount,
  infer company_ontology @ employee_at id amount ==> Sm ('Employee).
Proof.
  intros; apply infer_employee.
  - apply company_employee.
  - apply numeral_typed; apply company_number.
  - apply infer_salary; [apply company_salary | apply numeral_typed; apply company_number].
Qed.
Lemma department_example_typed :
  infer company_ontology @ department_example ==> Sm ('Department).
Proof.
  apply infer_department; [apply company_department | apply employee_at_typed |].
  repeat first [apply infer_cons_value; [apply company_list | |] |
    apply infer_nil_value; [apply company_list |] | apply employee_at_typed].
Qed.
Lemma company_update_typed : 
  infer company_ontology @ salary_update_example ==> Sm ('Update).
Proof.
  eapply infer_update_salary; auto using company_salary, company_number, company_updates, company_is_named.
  - apply infer_tag_free; exact salary_raise_tag_free.
  - apply type_app_salary_raise; auto using company_salary, company_number.
Qed.
Lemma department_update_preserves_type :
  infer company_ontology @ incremented_department ==> Sm ('Department).
Proof.
  eapply abstract_update_preserves_typing.
  - exact paper_ontology_sound.
  - apply company_update_typed.
  - apply department_example_typed.
  - apply department_example_updated.
Qed.

(** The salary predicate retains a Salary value as its threshold. This is
    the value an update will change inside the predicate. The salary
    getter [decorate[snd, (0, g)]] has its own ghost Salary g, which does
    not mention the threshold. *)
Definition salary_test threshold g := Eval cbn in to_tree
  (star "e" (Val nat_ge @@
    (((Ref "e" @@ Val ('decorate['snd, zero '* g])) @@ Val ('decorate['I, zero])) ''*
      ((Val ('K1 threshold) @@ Ref "e") @@ Val ('decorate['I, zero]))))).
Definition salary_predicate threshold g witness := 'decorate[salary_test threshold g, witness].
Lemma salary_predicate_eval : forall bound g witness id amount,
  salary_predicate (salary (numeral bound)) g witness @ employee_at id amount ==>
    (if Nat.leb bound amount then 'tt else 'ff).
Proof.
  intros; unfold salary_predicate; apply wait_eval.
  pose proof (nat_ge_numerals amount bound) as HG.
  unfold salary_test, employee_at, employee, salary, wrap; evaluate.
Qed.

Lemma type_app_record : forall AI nm fields R, nm <> fun_nm ->
  type_app AI @ wrap_type fields nm @r (fields --> R) ==> Sm R.
Proof.
  intros AI nm fields R H; apply type_app_abstract.
  apply payload_eliminator_some; apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** The continuation consumes the Department's payload product. Its
    witness uses the supplied employee, so updating that employee also
    updates all annotations in the getter. *)
Definition department_cons_fields := Eval cbn in to_tree
  (star "fields" (cons2 (Val 'fst @@ Ref "fields") (Val 'snd @@ Ref "fields"))).
Definition department_employees d :=
  lam (swap (lam department_cons_fields (d '* nil_value d)))
    (department d (nil_value d)).

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
      apply type_app_stem_structural; solve [intros; discriminate] |
      apply type_app_stem_tagged; eapply list_abstractor_supported;
        [apply company_list|first [apply list_abstractor_nil|apply list_abstractor_cons]]]
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
Local Definition salary_IsNamed_package bound m :
  {F : Combination | infer company_ontology @ salary_test (salary (numeral bound)) (salary (numeral m)) ==> Sm F /\
    type_app company_ontology @ F @r ('Employee) ==> Sm ('Bool)}.
Proof.
  pose proof (type_app_nat_ge company_ontology company_number company_booleans) as HG.
  eexists; split; unfold salary_test; cbn.
  all: repeat first [company_infer | company_app].
Defined.
Lemma salary_predicate_typed : forall bound m witness,
  infer company_ontology @ witness ==> Sm ('Employee) ->
  exists P, infer company_ontology @ salary_predicate (salary (numeral bound)) (salary (numeral m)) witness ==>
    Sm P /\ type_app company_ontology @ P @r 'Employee ==> Sm ('Bool).
Proof.
  intros bound m witness Hd; unfold salary_predicate; eexists; split.
  - apply infer_decorate; [exact (proj1 (proj2_sig (salary_IsNamed_package bound m)))|exact Hd].
  - eapply type_app_wait; [apply type_app_K_ev|].
    exact (proj2 (proj2_sig (salary_IsNamed_package bound m))).
Qed.
Lemma department_employees_infer : forall d,
  infer company_ontology @ d ==> Sm ('Employee) ->
  infer company_ontology @ department_employees d ==> Sm ('Department --> 'List['Employee]).
Proof.
  intros d Hd.
  assert (Hnil : infer company_ontology @ nil_value d ==> Sm ('List['Employee]))
    by (apply infer_nil_value; [apply company_list |exact Hd]).
  assert (Hfields : infer company_ontology @ lam department_cons_fields (d '* nil_value d)
      ==> Sm (department_fields --> 'List['Employee])).
  { eapply infer_lam; [apply infer_tag_free; reflexivity |infer_tac |].
    unfold department_cons_fields; repeat company_app. }
  unfold department_employees; eapply infer_lam; [ | |].
  - unfold swap; infer_tac.
  - apply infer_department; [apply company_department |exact Hd |exact Hnil].
  - unfold swap; type_app_tac; apply payload_eliminator_some;
      apply type_app_abstract; apply funty_eliminator_eval.
Qed.
Lemma department_employees_type_app :
  type_app company_ontology @ ('Department --> 'List['Employee]) @r ('Department) ==> Sm ('List['Employee]).
Proof. apply type_app_abstract; apply funty_eliminator_eval. Qed.

(** The four results contain whole Employees, in manager-first order.
    Witnesses in nil_value and lam are typing annotations; they are not records
    returned by this collector. Their salaries are also traversed by update. *)
Definition original_at57 := cons_value (employee_at 1 58)
  (cons_value (employee_at 3 57) (nil_value (employee_witness 0))).

(** * Annotations: employee collection and counting

    The salary updates above require no annotation handling. Here the query
    chooses to ignore evidence: [ghost_case b r g] sends a decoration's
    executable component to the recursive query r, and sends other values to
    g. This policy is defined using existing Query constructors in
    updates.v; it adds no hardwired typing rule.

    Employee collection and counting share this policy. Selection connects
    runtime names to action domains; ordinary Query constructors supply
    recursion, list combination and addition. Counting an Employee stops at
    that record, and counting empty-list evidence contributes nothing. *)
(** At a fork, first collect xs from the left child, then collect ys from
    the right child and append them. The two Query levels consume one child
    each; the captured xs has the ordinary list type. *)
Definition employee_fork_query_term r :=
  sum_fork_term (fun xs ys => Val append @@ (xs ''* ys)) r.
Definition employee_fork_query r := Eval cbn in
  to_tree (employee_fork_query_term (Val r)).

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
Definition count_employees_fork_term r :=
  sum_fork_term (fun n m => Val add @@ (n ''* m)) r.
Definition count_employees_fork r := Eval cbn in
  to_tree (count_employees_fork_term (Val r)).

Local Opaque type_app infer equal equal1 get_tagname.
Local Hint Resolve company_number company_booleans company_salary company_employee company_department company_list company_queries : core.
Definition employee_choice fallback := specialised_query employee_nm singleton fallback.
(** Like the headcount, the collector has no Department case: traversal
    reaches the manager and then the workers through the enclosing
    structure. *)
Definition collect_body d r := cons_case (nil_value d) r (ghost_case (nil_value d) r
 (employee_choice ('tq[nil_value d,r,employee_fork_query r]))).
Definition employee_one := 'K1 one.
Definition count_body r := cons_case zero r (ghost_case zero r
 (specialised_query employee_nm employee_one
   ('tq[zero,r,count_employees_fork r]))).
(** The same two bodies, abstracted over their recursive query. *)
Definition choice_term N f d :=
 ''tagged[''S2[''S2[''S2[Val (is_named N), ''K1 (Val f)], ''K1 d],Val 'I],Val query_nm].
Definition collect_function_body d := Eval cbn -[is_list_q] in to_tree
 (star "r" (cons_case_term (nil_value d) (Ref "r") (ghost_case_term (nil_value d) (Ref "r")
   (choice_term employee_nm singleton
     (''tq[Val (nil_value d),Ref "r",employee_fork_query_term (Ref "r")]))))).
Definition count_function_body := Eval cbn -[is_list_q] in to_tree
 (star "r" (cons_case_term zero (Ref "r") (ghost_case_term zero (Ref "r")
  (choice_term employee_nm employee_one
   (''tq[Val zero,Ref "r",count_employees_fork_term (Ref "r")]))))).
Definition collect_function d := 'decorate[collect_function_body d, 'Kq (nil_value d)].
Definition count_function := 'decorate[count_function_body, 'Kq zero].
Definition collect_employees d := fix_query (collect_function d).
Definition count_employees := fix_query count_function.

Local Ltac choice_app := first
 [ apply type_app_typed_K_q; exact company_queries
 | apply type_app_stem_tagged; eapply query_abstractor_supported; [exact company_queries|]; eapply queries.constructor_choice;
      [apply concreteb_sound; vm_compute; reflexivity|first [exact company_employee_declared|apply salary_declared; exact company_salary]|]
 | company_query_app ].
Local Definition collect_function_type d
 (Hd : inf company_ontology @ d ==> Sm ('Employee)) :
 {F : Combination | inf company_ontology @ collect_function_body d ==> Sm F /\
  app company_ontology @ F @r ('Query['List['Employee]]) ==> Sm ('Query['List['Employee]])}.
Proof.
 pose proof (infer_nil_value company_ontology d ('Employee) company_list Hd) as Hnil.
 pose proof (infer_append company_ontology) as HA.
 pose proof (type_app_append company_ontology ('Employee) company_list) as HT.
 pose proof (infer_singleton company_ontology) as HSing.
 pose proof (type_app_singleton company_ontology company_list ('Employee)) as HSingE.
 assert (HPE : inf company_ontology @ is_named employee_nm ==> Sm (IsNamed employee_nm))
   by (apply inf_is_named; [apply concreteb_sound; vm_compute; reflexivity|exact company_is_named]).
 assert (Hp : inf company_ontology @ is_decoration_query ==> Sm ('Query['Bool]))
   by (apply is_decoration_query_typed; eauto).
 assert (Ht : inf company_ontology @ ('tt) ==> Sm ('Bool)) by (apply tt_infer; exact company_booleans).
 assert (Hdq : inf company_ontology @ is_list_q ==> Sm ('Query['Bool]))
   by (apply is_list_q_typed; [exact company_queries|exact company_booleans]).
 pose proof (infer_typed_K_q_any company_ontology) as Hc.
 pose proof (type_app_typed_K_q company_ontology ('List['Employee]) company_queries) as HcE.
 pose proof (type_app_choose company_ontology ('List['Employee]) company_booleans) as Hch.
 eexists; split; unfold collect_function_body, cons_case_term, cond_t, payload_t, path_to_cell, flag_pat,
   choice_term, ghost_case_term,
   query_decorated_program_term, employee_fork_query_term, sum_fork_term; cbn -[is_list_q].
 all: repeat first [company_query_infer | choice_app].
 Unshelve. all: repeat first [company_query_infer | choice_app].
Defined.
Lemma collect_employees_typed : forall d,
 inf company_ontology @ d ==> Sm ('Employee) ->
 inf company_ontology @ collect_employees d ==> Sm ('Query['List['Employee]]).
Proof.
 intros d Hd; unfold collect_employees, collect_function; eapply infer_fix_query; [exact company_queries| | |].
 - exact (proj1 (proj2_sig (collect_function_type d Hd))).
 - apply infer_Kq; [exact company_queries|apply infer_nil_value; auto].
 - exact (proj2 (proj2_sig (collect_function_type d Hd))).
Qed.
Local Definition count_function_type :
 {F : Combination | inf company_ontology @ count_function_body ==> Sm F /\
  app company_ontology @ F @r ('Query['Nat]) ==> Sm ('Query['Nat])}.
Proof.
 assert (Hz : inf company_ontology @ zero ==> Sm ('Nat)) by (apply infer_zero; exact company_number).
 pose proof (infer_add company_ontology) as HA.
 assert (Ho : inf company_ontology @ one ==> Sm ('Nat)) by
  (unfold one; apply infer_succ; [exact company_number|apply infer_zero; exact company_number]).
 pose proof (type_app_add company_ontology company_number) as HAa.
 assert (HP : inf company_ontology @ is_named employee_nm ==> Sm (IsNamed employee_nm))
   by (apply inf_is_named; [apply concreteb_sound; vm_compute; reflexivity|exact company_is_named]).
 assert (Hp : inf company_ontology @ is_decoration_query ==> Sm ('Query['Bool]))
   by (apply is_decoration_query_typed; eauto).
 assert (Ht : inf company_ontology @ ('tt) ==> Sm ('Bool)) by (apply tt_infer; exact company_booleans).
 assert (Hdq : inf company_ontology @ is_list_q ==> Sm ('Query['Bool]))
   by (apply is_list_q_typed; [exact company_queries|exact company_booleans]).
 pose proof (infer_typed_K_q_any company_ontology) as Hc.
 pose proof (type_app_typed_K_q company_ontology ('Nat) company_queries) as HcN.
 pose proof (type_app_choose company_ontology ('Nat) company_booleans) as Hch.
 eexists; split; unfold count_function_body, employee_one, cons_case_term, cond_t, payload_t, path_to_cell, flag_pat,
   choice_term, ghost_case_term,
   query_decorated_program_term, count_employees_fork_term, sum_fork_term; cbn -[is_list_q].
 all: repeat first [company_query_infer | choice_app].
 Unshelve. all: repeat first [company_query_infer | choice_app].
Defined.
Lemma count_employees_typed : inf company_ontology @ count_employees ==> Sm ('Query['Nat]).
Proof.
 unfold count_employees, count_function; eapply infer_fix_query; [exact company_queries| | |].
 - exact (proj1 (proj2_sig count_function_type)).
 - apply infer_Kq; [exact company_queries|apply infer_zero; exact company_number].
 - exact (proj2 (proj2_sig count_function_type)).
Qed.

Local Lemma fix_query_eval_step : forall f u v,
  f @ fix_query f @r u ==> v -> fix_query f @ u ==> v.
Proof.
  intros f u v H; inv_out H.
  unfold fix_query at 1; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|eassumption].
  eapply eval_c; eapply eval_appr.
  - unfold tagged_query; evaluate.
  - eassumption.
Qed.
Lemma employee_fork_query_eval : forall r x y xs ys zs,
  r @ x ==> xs -> r @ y ==> ys ->
  append @ (xs '* ys) ==> zs ->
  employee_fork_query r @ x @r y ==> zs.
Proof.
  intros r x y xs ys zs Hx Hy Ha.
  destruct (eval_pair_inv _ _ _ Ha) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  eapply eval_appl.
  - unfold employee_fork_query, employee_fork_query_term, sum_fork_term; cbn.
    eapply S_q_eval; [apply K_q_eval|exact Hx|]. evaluate.
  - eapply S_q_eval; [apply K_q_eval|exact Hy|]. evaluate.
Qed.
Lemma count_employees_fork_eval : forall r x y a b n,
  r @ x ==> a -> r @ y ==> b -> add @ (a '* b) ==> n ->
  count_employees_fork r @ x @r y ==> n.
Proof.
  intros r x y a b n Hx Hy Hsum.
  destruct (eval_pair_inv _ _ _ Hsum) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  eapply eval_appl.
  - unfold count_employees_fork, count_employees_fork_term, sum_fork_term; cbn.
    eapply S_q_eval; [apply K_q_eval|exact Hx|]. evaluate.
  - eapply S_q_eval; [apply K_q_eval|exact Hy|]. evaluate.
Qed.

Lemma specialised_query_hit : forall N f d u v,
 get_tagname @ u ==> Sm N -> f @ u ==> v ->
 specialised_query N f d @ u ==> v.
Proof.
 intros; unfold specialised_query; apply tagged_eval.
 eapply if_named_hit; eauto.
Qed.
Lemma specialised_query_miss : forall N f d u found v,
 get_tagname @ u ==> found -> found <> Sm N -> d @ u ==> v ->
 specialised_query N f d @ u ==> v.
Proof.
 intros; unfold specialised_query; apply tagged_eval.
 eapply if_named_miss; eassumption.
Qed.
Lemma collect_function_eval : forall d r,
 collect_function d @ r ==> collect_body d r.
Proof.
 intros; unfold collect_function; apply wait_eval.
 unfold collect_function_body, collect_body, employee_choice, cons_case, cons_case_term, cond, cond_t, path_query, path_query_t, inner_q, payload_q, payload_t, pc, pc_t,
 flag_pat, path_to_cell,
 choice_term, specialised_query, if_named, ghost_case_term,
 query_decorated_program_term, ghost_case, query_decorated_program,
 query_left, query_right, query_stem, diagonal_query, choose_queries,
 employee_fork_query, employee_fork_query_term, sum_fork_term; cbn; evaluate.
Qed.
Lemma collect_employees_step : forall d u v,
 collect_body d (collect_employees d) @ u ==> v -> collect_employees d @ u ==> v.
Proof.
 intros; unfold collect_employees at 1; apply fix_query_eval_step.
 eapply eval_appl; [apply collect_function_eval|exact H].
Qed.
Lemma collect_employees_employee : forall d id pay,
 collect_employees d @ employee id pay ==>
   cons_value (employee id pay) (nil_value (employee id pay)).
Proof.
 intros; apply collect_employees_step; unfold collect_body.
 apply cons_case_miss; [reflexivity|]; apply ghost_case_miss; [intros; discriminate|].
 unfold employee_choice; eapply specialised_query_hit; [apply get_tagname_some|].
 apply singleton_eval.
Qed.
Lemma collect_employees_nil : forall d a, collect_employees d @ nil_value a ==> nil_value d.
Proof. intros; apply collect_employees_step; apply cons_case_nil. Qed.
Lemma collect_employees_cell : forall d x s v,
 collect_employees d @ (x '* s) ==> v -> collect_employees d @ cell x s ==> v.
Proof. intros; apply collect_employees_step; apply cons_case_cell; assumption. Qed.
Lemma collect_employees_decoration : forall d f a xs,
 collect_employees d @ f ==> xs -> collect_employees d @ 'decorate[f,a] ==> xs.
Proof.
 intros; apply collect_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_hit; eauto.
Qed.
Lemma collect_employees_leaf : forall d, collect_employees d @ Lf ==> nil_value d.
Proof.
 intros; apply collect_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_miss; [intros; discriminate|].
 eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_leaf.
Qed.
Lemma collect_employees_stem : forall d x xs,
 collect_employees d @ x ==> xs -> collect_employees d @ Sm x ==> xs.
Proof.
 intros; apply collect_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_miss; [intros; discriminate|].
 eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_stem; eauto.
Qed.
Lemma collect_employees_fork_miss : forall d x y found xs ys zs,
 off_list (Fk x y) ->
 get_tagname @ Fk x y ==> found -> (forall f a, Fk x y <> 'decorate[f,a]) ->
 found <> Sm employee_nm ->
 collect_employees d @ x ==> xs -> collect_employees d @ y ==> ys ->
 append @ (xs '* ys) ==> zs -> collect_employees d @ Fk x y ==> zs.
Proof.
 intros; apply collect_employees_step; apply cons_case_miss; [assumption|];
   apply ghost_case_miss; [assumption|].
 eapply specialised_query_miss; [eassumption|assumption|].
 apply tagged_eval; eapply eval_fork; eapply employee_fork_query_eval; eauto.
Qed.
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
(** Collection from a department with two workers lists the manager, then
    the workers in order. The result ends in the collector's ghost d; the
    department's own ghost w is passed over. *)
Lemma collect_employees_department : forall d i1 a1 i2 a2 i3 a3 w,
 collect_employees d @ department (employee_at i1 a1)
   (cons_value (employee_at i2 a2) (cons_value (employee_at i3 a3) (nil_value w))) ==>
 cons_value (employee_at i1 a1) (cons_value (employee_at i2 a2)
   (cons_value (employee_at i3 a3) (nil_value d))).
Proof.
 intros; eassert (H : collect_employees d @ department (employee_at i1 a1)
   (cons_value (employee_at i2 a2) (cons_value (employee_at i3 a3) (nil_value w))) ==> _).
 { unfold department, wrap; collect_nodes. }
 exact H.
Qed.
Definition filter_function p d := 'decorate[filter_from p d, nil_value d].
Definition paid_over threshold g d :=
 'S_q['Kq (filter_function (salary_predicate threshold g d) d),collect_employees d].
Theorem paid_over_typed : forall bound m d,
  infer company_ontology @ d ==> Sm ('Employee) ->
  infer company_ontology @ paid_over (salary (numeral bound)) (salary (numeral m)) d ==>
    Sm ('Query['List['Employee]]).
Proof.
  intros bound m d Hd; unfold paid_over.
  destruct (salary_predicate_typed bound m d Hd) as [P [HP HPa]].
  eapply infer_S_q; [apply company_queries| |apply collect_employees_typed; auto|].
  - apply infer_Kq; [apply company_queries|].
    unfold filter_function; apply infer_decorate.
    + unfold filter_from; apply infer_foldright_value;
        [apply infer_filter_step; exact HP
        |apply infer_nil_value; [apply company_list|exact Hd]].
    + apply infer_nil_value; [apply company_list|exact Hd].
  - eapply type_app_wait; [apply type_app_K_ev|].
    apply type_app_foldright_value; apply type_app_filter_step; [exact company_list|exact HPa].
Qed.
Lemma paid_over_eval : forall threshold g d u xs result,
 collect_employees d @ u ==> xs ->
 filter_from (salary_predicate threshold g d) d @ xs ==> result ->
 paid_over threshold g d @ u ==> result.
Proof.
  intros; unfold paid_over; eapply S_q_eval; [apply K_q_eval|eassumption|].
  unfold filter_function; apply wait_eval; eapply eval_appl; [evaluate|assumption].
Qed.
Lemma paid_over_department_eval : forall threshold g d i1 a1 i2 a2 i3 a3 w result,
 filter_from (salary_predicate threshold g d) d @
   cons_value (employee_at i1 a1) (cons_value (employee_at i2 a2)
     (cons_value (employee_at i3 a3) (nil_value d))) ==> result ->
 paid_over threshold g d @ department (employee_at i1 a1)
   (cons_value (employee_at i2 a2) (cons_value (employee_at i3 a3) (nil_value w))) ==> result.
Proof. intros; eapply paid_over_eval; [apply collect_employees_department|exact H]. Qed.
Definition paid_over_57 := paid_over (salary (numeral 57)) (salary (numeral 0)) (employee_witness 0).
(** Three employees, first and last kept: the shape of both paper tables. *)
Lemma filter_keep_first_last : forall p a b c d e,
  p @ a ==> 'tt -> p @ b ==> 'ff -> p @ c ==> 'tt ->
  filter_from p e @ cons_value a (cons_value b (cons_value c (nil_value d))) ==>
    cons_value a (cons_value c (nil_value e)).
Proof.
  intros p a b c d e Ha Hb Hc.
  apply foldright_value_eval.
  eapply cell_apply; [|apply filter_step_true; exact Ha].
  eapply cell_apply; [|apply filter_step_false; exact Hb].
  eapply cell_apply; [apply nil_apply|apply filter_step_true; exact Hc].
Qed.
Theorem paid_over_57_original : paid_over_57 @ department_example ==> original_at57.
Proof.
  apply paid_over_department_eval.
  apply filter_keep_first_last; apply salary_predicate_eval.
Qed.

Local Opaque typed_conjunction typed_K_q typed_query_conjunction.
(** The generic queries use the same thresholds and result lists as the
    Department-specific baseline above. They need no Department witness. *)

Lemma paid_over_57_typed :
 infer company_ontology @ paid_over_57 ==> Sm ('Query['List['Employee]]).
Proof. apply paid_over_typed; apply employee_at_typed. Qed.

Lemma count_function_eval : forall r, count_function @ r ==> count_body r.
Proof.
 intros; unfold count_function; apply wait_eval.
 unfold count_function_body, count_body, employee_one, cons_case, cons_case_term, cond, cond_t, path_query, path_query_t, inner_q, payload_q, payload_t, pc, pc_t,
 flag_pat, path_to_cell, choice_term,
 specialised_query, if_named, ghost_case_term, query_decorated_program_term,
 ghost_case, query_decorated_program, query_left, query_right, query_stem,
 diagonal_query, choose_queries, count_employees_fork, count_employees_fork_term,
 sum_fork_term; cbn; evaluate.
Qed.
Lemma count_employees_step : forall u v,
 count_body count_employees @ u ==> v -> count_employees @ u ==> v.
Proof.
 intros; unfold count_employees at 1; apply fix_query_eval_step.
 eapply eval_appl; [apply count_function_eval|exact H].
Qed.
Lemma count_employees_decoration : forall f a n,
 count_employees @ f ==> n -> count_employees @ 'decorate[f,a] ==> n.
Proof.
 intros; apply count_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_hit; eauto.
Qed.
Lemma count_employees_nil : forall a, count_employees @ nil_value a ==> zero.
Proof. intros; apply count_employees_step; apply cons_case_nil. Qed.
Lemma count_employees_cell : forall x s v,
 count_employees @ (x '* s) ==> v -> count_employees @ cell x s ==> v.
Proof. intros; apply count_employees_step; apply cons_case_cell; assumption. Qed.
Lemma count_employees_employee : forall id pay, count_employees @ employee id pay ==> one.
Proof.
 intros; apply count_employees_step; unfold count_body.
 apply cons_case_miss; [reflexivity|]; apply ghost_case_miss; [intros; discriminate|].
 eapply specialised_query_hit; [apply get_tagname_some|].
 unfold employee_one; evaluate.
Qed.
Lemma count_employees_leaf : count_employees @ Lf ==> zero.
Proof.
 apply count_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_miss; [intros; discriminate|].
 eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_leaf.
Qed.
Lemma count_employees_stem : forall x n, count_employees @ x ==> n -> count_employees @ Sm x ==> n.
Proof.
 intros; apply count_employees_step; apply cons_case_miss; [reflexivity|];
   apply ghost_case_miss; [intros; discriminate|].
 eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_stem; eauto.
Qed.
Lemma count_employees_fork_miss : forall x y found a b n,
 off_list (Fk x y) ->
 get_tagname @ Fk x y ==> found -> (forall f a, Fk x y <> 'decorate[f,a]) ->
 found <> Sm employee_nm -> count_employees @ x ==> a -> count_employees @ y ==> b ->
 add @ (a '* b) ==> n -> count_employees @ Fk x y ==> n.
Proof.
 intros; apply count_employees_step; apply cons_case_miss; [assumption|];
   apply ghost_case_miss; [exact H1|].
 eapply specialised_query_miss; [exact H0|exact H2|].
 apply tagged_eval; eapply eval_fork; eapply count_employees_fork_eval; eauto.
Qed.

Local Ltac fold_counts := first
  [ apply zero_apply
  | eapply succ_apply; [fold_counts|apply succ_step_eval] ].
Local Ltac add_counts := apply add_eval; unfold one; fold_counts.
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
Theorem count_employees_department_example : count_employees @ department_example ==> numeral 3.
Proof.
  unfold department_example; unfold department, wrap.
  count_nodes.
Qed.
Lemma count_employees_incremented_department : count_employees @ incremented_department ==> numeral 3.
Proof.
  unfold incremented_department; unfold department, wrap.
  count_nodes.
Qed.

Lemma count_employees_nested_department :
  count_employees @ Sm department_example ==> numeral 3.
Proof. apply count_employees_stem; apply count_employees_department_example. Qed.


(** The paper's example uses an Employee witness [a]: [nil[a]] contributes
    no employees, while [a] supplied directly counts as one. *)
Lemma count_employees_nil_employee_evidence :
  count_employees @ nil_value (employee_witness 50) ==> zero.
Proof. apply count_employees_nil. Qed.

Lemma count_employees_employee_witness :
  count_employees @ employee_witness 50 ==> one.
Proof. apply count_employees_employee. Qed.

(** Function evidence is ignored, while Employees in executable code remain
    visible. This distinguishes annotation skipping from skipping the whole
    decorated program. *)
Lemma count_employees_in_function_body :
  count_employees @ lam ('K1 (employee_at 1 58)) (employee_at 2 56) ==> one.
Proof. unfold lam; count_nodes. Qed.

(** * Salary bills

    A salary bill sums salary amounts as count_employees sums employees.
    A Salary contributes its amount and stops descent; otherwise a leaf
    contributes zero, a stem its child's bill, and a fork the sum of its
    children's bills. [naive_salary_bill] is not ghost-aware: at an empty
    list it includes the wage of the ghost employee in [nil[E(0,50)]].
    [salary_bill] wraps the same body in [cons_case] and [ghost_case], so
    no ghost contributes. *)
Definition salary_amount_body := Eval cbn in to_tree
  (star "s" (Ref "s" @@ Val ('decorate['I, zero]))).
Definition salary_amount := 'decorate[salary_amount_body, salary zero].
Lemma salary_amount_eval : forall n, salary_amount @ salary n ==> n.
Proof.
  intros; unfold salary_amount; apply wait_eval.
  unfold salary_amount_body, salary, wrap; evaluate.
Qed.

Definition salary_sum_body r := specialised_query salary_nm salary_amount
  ('tq[zero,r,count_employees_fork r]).
Definition salary_bill_body r := cons_case zero r (ghost_case zero r (salary_sum_body r)).
Definition naive_salary_bill_function_body := Eval cbn in to_tree
 (star "r" (choice_term salary_nm salary_amount
   (''tq[Val zero,Ref "r",count_employees_fork_term (Ref "r")]))).
Definition salary_bill_function_body := Eval cbn -[is_list_q] in to_tree
 (star "r" (cons_case_term zero (Ref "r") (ghost_case_term zero (Ref "r")
  (choice_term salary_nm salary_amount
   (''tq[Val zero,Ref "r",count_employees_fork_term (Ref "r")]))))).
Definition naive_salary_bill_function := 'decorate[naive_salary_bill_function_body, 'Kq zero].
Definition salary_bill_function := 'decorate[salary_bill_function_body, 'Kq zero].
Definition naive_salary_bill := fix_query naive_salary_bill_function.
Definition salary_bill := fix_query salary_bill_function.


Lemma naive_salary_bill_function_eval : forall r,
 naive_salary_bill_function @ r ==> salary_sum_body r.
Proof.
 intros; unfold naive_salary_bill_function; apply wait_eval.
 unfold naive_salary_bill_function_body, salary_sum_body, choice_term,
 specialised_query, if_named, count_employees_fork, count_employees_fork_term,
 sum_fork_term; cbn; evaluate.
Qed.
Lemma salary_bill_function_eval : forall r,
 salary_bill_function @ r ==> salary_bill_body r.
Proof.
 intros; unfold salary_bill_function; apply wait_eval.
 unfold salary_bill_function_body, salary_bill_body, salary_sum_body, cons_case, cons_case_term, cond, cond_t, path_query, path_query_t, inner_q, payload_q, payload_t, pc, pc_t,
 flag_pat, path_to_cell, choice_term,
 specialised_query, if_named, ghost_case_term, query_decorated_program_term,
 ghost_case, query_decorated_program, query_left, query_right, query_stem,
 diagonal_query, choose_queries, count_employees_fork, count_employees_fork_term,
 sum_fork_term; cbn; evaluate.
Qed.

(** The salary-sum body, for any recursive query r whose results are numerals. *)
Lemma salary_sum_salary : forall r n,
 salary_sum_body r @ salary (numeral n) ==> numeral n.
Proof.
 intros; unfold salary_sum_body; eapply specialised_query_hit;
 [apply get_tagname_some|apply salary_amount_eval].
Qed.
Lemma salary_sum_leaf : forall r, salary_sum_body r @ Lf ==> numeral 0.
Proof.
 intros; eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_leaf.
Qed.
Lemma salary_sum_stem : forall r x n, r @ x ==> n -> salary_sum_body r @ Sm x ==> n.
Proof.
 intros; eapply specialised_query_miss; [apply get_tagname_none; intros; discriminate|discriminate|].
 apply tagged_eval; apply eval_stem; eauto.
Qed.
Lemma salary_sum_fork : forall r x y found a b,
 get_tagname @ Fk x y ==> found -> found <> Sm salary_nm ->
 r @ x ==> numeral a -> r @ y ==> numeral b ->
 salary_sum_body r @ Fk x y ==> numeral (a + b).
Proof.
 intros; eapply specialised_query_miss; [eassumption|eassumption|].
 apply tagged_eval; eapply eval_fork; eapply count_employees_fork_eval; eauto.
 apply add_numerals.
Qed.

Lemma naive_salary_bill_step : forall u v,
 salary_sum_body naive_salary_bill @ u ==> v -> naive_salary_bill @ u ==> v.
Proof.
 intros; unfold naive_salary_bill at 1; apply fix_query_eval_step.
 eapply eval_appl; [apply naive_salary_bill_function_eval|exact H].
Qed.
Lemma salary_bill_step : forall u v,
 salary_bill_body salary_bill @ u ==> v -> salary_bill @ u ==> v.
Proof.
 intros; unfold salary_bill at 1; apply fix_query_eval_step.
 eapply eval_appl; [apply salary_bill_function_eval|exact H].
Qed.
Lemma salary_bill_decoration : forall f a n,
 salary_bill @ f ==> n -> salary_bill @ 'decorate[f,a] ==> n.
Proof.
 intros; apply salary_bill_step; apply cons_case_miss; [reflexivity|]; apply ghost_case_hit; eauto.
Qed.
Lemma salary_bill_other : forall u n, off_list u ->
 (forall f a, u <> 'decorate[f,a]) -> salary_sum_body salary_bill @ u ==> n ->
 salary_bill @ u ==> n.
Proof.
 intros; apply salary_bill_step; apply cons_case_miss; [assumption|];
   apply ghost_case_miss; eauto.
Qed.
Lemma salary_bill_nil : forall a, salary_bill @ nil_value a ==> numeral 0.
Proof. intros; apply salary_bill_step; apply cons_case_nil. Qed.
Lemma salary_bill_cell : forall x s n,
 salary_bill @ (x '* s) ==> n -> salary_bill @ cell x s ==> n.
Proof. intros; apply salary_bill_step; apply cons_case_cell; assumption. Qed.

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

(** A list keeps the ghost of its nil, so the naive bill reads it, on a
    non-empty list as on an empty one: 171 and the 50 of the ghost. *)
Lemma naive_salary_bill_department_2025 :
  naive_salary_bill @ department_example ==> numeral 221.
Proof.
  eassert (H : naive_salary_bill @ department_example ==> numeral _).
  { unfold department_example; 
      unfold employee_at, employee, department, cons_value, cell, cell_carrier, nil_value,
        employee_witness, employee_at, employee, wrap.
    bill_nodes. }
  exact H.
Qed.
(** On an empty list it reads the ghost. *)
Lemma naive_salary_bill_empty :
  naive_salary_bill @ department (employee_at 1 58) (nil_value (employee_witness 50)) ==> numeral 108.
Proof.
  eassert (H : naive_salary_bill @ department (employee_at 1 58)
      (nil_value (employee_witness 50)) ==> numeral _).
  { unfold employee_witness, employee_at, employee, department, nil_value, wrap.
    bill_nodes. }
  exact H.
Qed.
Theorem salary_bill_department_2025 :
  salary_bill @ department_example ==> numeral 171.
Proof.
  eassert (H : salary_bill @ department_example ==> numeral _).
  { unfold department_example; 
      unfold employee_at, employee, department, wrap.
    bill_nodes. }
  exact H.
Qed.

(** * The paper's naive update and the 2026 department

    A non-empty list has no ghost, so the naive update
    [update[salary_nm,increment_salary]] and the ghost-aware [salary_update]
    below agree on departments with workers.  On an empty list the naive
    update raises the ghost ([salary_update_nil]) and [salary_update] does
    not ([su_nil]). *)

Definition department_2026 := department (employee_at 1 59)
  (cons_value (employee_at 2 57) (cons_value (employee_at 3 58) (nil_value (employee_witness 50)))).
Lemma count_employees_department_2026 : count_employees @ department_2026 ==> numeral 3.
Proof.
  unfold department_2026; unfold department, wrap.
  count_nodes.
Qed.


(** The results in the paper's table. The threshold-58 entries are proved below. *)
Definition paid_57_in_2025 := original_at57.
Definition paid_58_in_2026 := cons_value (employee_at 1 59)
  (cons_value (employee_at 3 58) (nil_value (employee_witness 0))).
Lemma table_57_2025 : paid_over_57 @ department_example ==> paid_57_in_2025.
Proof. exact paid_over_57_original. Qed.

(** * The ghost-aware salary update

    [salary_update] is the naive update with its recursion guarded by
    [ghost_update]: at a haunted program [decorate[f,w]] it updates f and
    leaves the ghost w alone. *)
Definition salary_update := ghost_guarded_update salary_nm salary_raise.
Lemma salary_update_typed : infer company_ontology @ salary_update ==> Sm ('Update).
Proof.
  unfold salary_update; eapply ghost_guarded_update_typed;
    [exact company_updates | exact company_queries | exact company_booleans | exact company_is_named |
     apply concreteb_sound; vm_compute; reflexivity | apply salary_declared; exact company_salary | |].
  - apply infer_tag_free; exact salary_raise_tag_free.
  - apply type_app_salary_raise; auto using company_salary, company_number.
Qed.
Lemma su_hit : forall n, salary_update @ salary (numeral n) ==> salary (numeral (S n)).
Proof.
  intros; unfold salary_update, salary, wrap; apply ghost_guarded_hit;
    [apply off_tagged; discriminate|apply salary_raise_eval].
Qed.
Lemma off_tag_free : forall l r, tag_free (Fk l r) = true -> off_list (Fk l r).
Proof.
  intros l r H; unfold off_list.
  destruct (pattern_matches list_pat (Fk l r)) eqn:E; [|reflexivity].
  apply list_pat_inv in E; destruct E as [C HE]; rewrite HE in H; cbn in H; discriminate.
Qed.
Lemma su_tag_free_size : forall n t,
  tree_size t <= n -> tag_free t = true -> salary_update @ t ==> t.
Proof.
  induction n; intros t Hs Hc; [destruct t; cbn in Hs; lia|].
  destruct t as [|t|l r].
  - apply ghost_guarded_leaf.
  - apply ghost_guarded_stem; apply IHn; [cbn in Hs; lia|exact Hc].
  - destruct (pattern_matches decoration_pattern (Fk l r)) eqn:E.
    + apply decoration_pattern_inv in E; destruct E as [g [w Eq]]; rewrite Eq in *.
      apply ghost_guarded_decoration; apply IHn.
      * cbn in Hs; lia.
      * cbn [tag_free] in Hc; repeat (apply andb_true_iff in Hc; destruct Hc as [Hc ?]).
        cbn [tag_free] in *; repeat match goal with H : _ && _ = true |- _ =>
          apply andb_true_iff in H; destruct H end; assumption.
    + pose proof (off_tag_free l r Hc) as Hoff.
      cbn [tag_free] in Hc; apply andb_true_iff in Hc; destruct Hc as [H Hr].
      apply andb_true_iff in H; destruct H as [Htag Hl].
      apply ghost_guarded_miss; [exact Hoff| | | |].
      * intros g w HE; rewrite HE in E; rewrite decoration_pattern_hit in E; discriminate.
      * intros p HE; assert (Hres : reserved_tagb (Fk l r) = true) by (rewrite HE; reflexivity).
        rewrite Hres in Htag; discriminate.
      * apply IHn; [cbn in Hs; lia|exact Hl].
      * apply IHn; [cbn in Hs; lia|exact Hr].
Qed.
Lemma su_tag_free : forall t, tag_free t = true -> salary_update @ t ==> t.
Proof. intros; eapply su_tag_free_size; [apply le_n|assumption]. Qed.
Local Ltac su_traverse := repeat first
  [ eassumption | apply su_tag_free; reflexivity |
    apply su_hit |
    apply ghost_guarded_leaf | apply ghost_guarded_stem |
    apply ghost_guarded_decoration |
    apply ghost_guarded_miss;
      [reflexivity
      |solve [let g := fresh in let w := fresh in let Hbad := fresh in intros g w Hbad; discriminate Hbad]
      |solve [let p := fresh in let Hbad := fresh in intros p Hbad; discriminate Hbad]| |] ].
Lemma su_tagged : forall C C' N,
  N <> salary_nm -> N <> list_nm -> tag_free N = true ->
  salary_update @ C ==> C' -> salary_update @ ('tagged[C,N]) ==> 'tagged[C',N].
Proof.
  intros C C' N HN HL Hcon HC; apply ghost_guarded_miss.
  - apply off_tagged; exact HL.
  - intros g w Hbad; discriminate Hbad.
  - intros p H; inversion H; contradiction.
  - su_traverse.
  - assert (salary_update @ N ==> N) by (apply su_tag_free; exact Hcon).
    su_traverse.
Qed.
Lemma su_product : forall a b a' b',
  salary_update @ a ==> a' -> salary_update @ b ==> b' ->
  salary_update @ (a '* b) ==> (a' '* b').
Proof. intros; su_traverse. Qed.
Lemma su_numeral : forall n, salary_update @ numeral n ==> numeral n.
Proof.
  induction n; cbn [numeral].
  - unfold zero; apply su_tagged; try discriminate; try reflexivity; su_traverse.
  - unfold succ; apply su_tagged; try discriminate; try reflexivity; su_traverse.
Qed.
Lemma su_employee : forall id n,
  salary_update @ employee_at id n ==> employee_at id (S n).
Proof.
  intros; unfold employee_at, employee, wrap; apply su_tagged; try discriminate; try reflexivity.
  pose proof (su_numeral id); pose proof (su_hit n).
  su_traverse; apply su_product; assumption.
Qed.
(** The ghost of an empty list is left alone, whatever it is. *)
Lemma su_nil : forall d, salary_update @ nil_value d ==> nil_value d.
Proof. intros; apply ghost_guarded_nil. Qed.
Local Ltac su_go := repeat first
  [ eassumption | apply su_tag_free; reflexivity |
    apply su_hit | apply su_nil |
    apply ghost_guarded_leaf | apply ghost_guarded_stem |
    apply ghost_guarded_decoration |
    apply ghost_guarded_miss;
      [reflexivity
      |solve [let g := fresh in let w := fresh in let Hbad := fresh in intros g w Hbad; discriminate Hbad]
      |solve [let p := fresh in let Hbad := fresh in intros p Hbad; discriminate Hbad]| |] ].
Lemma su_cell : forall x s x' s',
  salary_update @ x ==> x' -> salary_update @ s ==> s' ->
  salary_update @ cell x s ==> cell x' s'.
Proof. intros; apply ghost_guarded_cell; apply su_product; assumption. Qed.
Lemma su_department : forall m ws m' ws',
  salary_update @ m ==> m' -> salary_update @ ws ==> ws' ->
  salary_update @ department m ws ==> department m' ws'.
Proof.
  intros; unfold department, wrap; apply su_tagged; try discriminate; try reflexivity.
  su_go; apply su_product; assumption.
Qed.
(** The ghost of a function is left alone, whatever it is. *)
Lemma su_lam : forall f f' d,
  salary_update @ f ==> f' -> salary_update @ lam f d ==> lam f' d.
Proof.
  intros; unfold lam; apply su_tagged; try discriminate; try reflexivity.
  apply ghost_guarded_decoration; assumption.
Qed.

(** Every employee gets a rise, while the ghost employee stays on the
    minimum wage. *)
Theorem salary_update_department_2025 :
  salary_update @ department_example ==> department_2026.
Proof.
  apply su_department; [apply su_employee|].
  apply su_cell; [apply su_employee|].
  apply su_cell; [apply su_employee|].
  apply ghost_guarded_nil.
Qed.

End TraversalExamples.

(** Paper names. *)
Abbreviation department_2025 := department_example (only parsing).
Abbreviation naive_salary_update := salary_update_example (only parsing).
