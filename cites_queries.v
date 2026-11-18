(** * Step 83 (stage 10), group B: cited results on updates, queries, patching and infer.

    - [bool_pair_flipped_n]: update[Bool,neg] takes tt*ff to ff*tt.
    - [updates_not_sound_by_typing]: the update declaration of paper_ontology
      is not sound by typing (the children carrier type refuses Bool).
    - [queries_not_sound_by_typing]: the query declaration at Query[Nat] is not
      sound by typing (the triage carrier type refuses Bool).
    - [installed_traversal]: the triage carrier type gives B at argument types
      that are not abstract (instances at five shapes).
    - [query_triage_reduct_typing], [query_one_level_value_typing]: the fork
      case of the triage carrier, typed by the premise AS(k).
    - [infer_special_query_n]: special_query[Nat,is_odd,Kq[ff]] : Query[Bool],
      taking 1 to tt and tt to ff.
    - [count_employees_typed]: the headcount has type Query[Nat] at paper_ontology.
    - [patched_query_typed], [salary_update_pending_query_typed]: the salary
      update patches the pending query and keeps its expression type.
    - [type_app_infer_Bool]: infer is its own type, and its type application
      refuses Bool. *)

From Stdlib Require Import String List Bool Lia Arith.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries_core queries_entries queries scott_arithmetic department_queries paper_ontology self_typing size_queries poly updates_paper patching_paper.
Set Default Proof Using "Type".

Local Notation PO := paper_ontology.
Ltac by_runB := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** Updates *)

(** [update[Bool,neg]] takes the fork of [tt] and [ff] to the fork of [ff] and [tt]. *)
Theorem bool_pair_flipped_n : update_at Bool neg @ (tt '* ff) ==> (ff '* tt).
Proof. by_runB. Qed.

(** The carrier type of the children update, [wait[ch_body, Update]], is
    admitted by the update guard, but type application refuses to apply it
    to the abstract type [Bool]. *)
Theorem updates_not_sound_by_typing :
  PO @ update_nm @r tp PO ==> Sm (D_upd update_nm (tp PO)) /\
  ~ decl_sound_by_typing PO update_nm (D_upd update_nm (tp PO)).
Proof.
  split; [exact PO_update|intros H].
  assert (HC : guard_of @ D_upd update_nm (tp PO) @r 'wait[ch_body, Update] ==> 'K) by by_runB.
  assert (HE : elim_of @ D_upd update_nm (tp PO) @r update_nm @r tp PO @r Bool ==> Sm Bool) by by_runB.
  assert (HL : tp PO @ 'wait[ch_body, Update] @r Bool ==> Lf) by by_runB.
  pose proof (eval_deterministic _ _ (H _ _ _ HC HE) _ HL); discriminate.
Qed.

(** ** Queries *)

(** The carrier type of the triage query at [Query[B]]. *)
Definition triage_carrier_type (B : Combination) : Combination :=
  'wait3[tq_body, B, Query B, Fk (Query (Query B)) (Query (Query B))].

(** The triage carrier type is admitted by the query guard, but type
    application refuses to apply it to the abstract type [Bool]. *)
Theorem queries_not_sound_by_typing :
  PO @ query_tag (code Nat) @r tp PO ==> Sm (D_query (code Nat) (tp PO)) /\
  ~ decl_sound_by_typing PO (query_tag (code Nat)) (D_query (code Nat) (tp PO)).
Proof.
  split; [apply PO_query; reflexivity|intros H].
  assert (HC : guard_of @ D_query (code Nat) (tp PO) @r triage_carrier_type Nat ==> 'K) by by_runB.
  assert (HE : elim_of @ D_query (code Nat) (tp PO) @r query_tag (code Nat) @r tp PO @r Bool ==> Sm Nat) by by_runB.
  assert (HL : tp PO @ triage_carrier_type Nat @r Bool ==> Lf) by by_runB.
  pose proof (eval_deterministic _ _ (H _ _ _ HC HE) _ HL); discriminate.
Qed.

(** The carrier type gives [B] at argument types that are not abstract:
    a leaf, stems and forks, including forks of abstract types. *)
Theorem installed_traversal :
  tp PO @ triage_carrier_type Nat @r Lf ==> Sm Nat /\
  tp PO @ triage_carrier_type Nat @r Sm Lf ==> Sm Nat /\
  tp PO @ triage_carrier_type Nat @r Sm Bool ==> Sm Nat /\
  tp PO @ triage_carrier_type Nat @r Fk Lf Lf ==> Sm Nat /\
  tp PO @ triage_carrier_type Nat @r (Bool '* Bool) ==> Sm Nat.
Proof. repeat split; by_runB. Qed.

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Opaque qK_prog qS_prog qsp_prog qe_prog gdq_prog or_prog gtq_prog.

Section QueryTriage.
Variable O : Combination.
Hypothesis HQ : forall r, concreteb r = true -> O @ query_tag r @r tp O ==> Sm (D_query r (tp O)).

Lemma QQ_app : forall B X, names_concrete B -> tp O @ Query (Query B) @r X ==> Sm (Query B).
Proof using HQ.
  intros B X HB; change (Query (Query B)) with (QQl (code B)); unfold QQl.
  apply (Query_app_r_g O HQ); [cbn; rewrite (code_concrete B HB); reflexivity|cbn; reflexivity].
Qed.

(** On a fork with children [y] and [z] the triage carrier applies
    [g : Query[Query[B]]] to [y]: within the height [k], [AS(k)] gives the
    value of this application the type [Query[B]]. *)
Theorem query_triage_reduct_typing : forall k j B g y Y h, names_concrete B ->
  app_sound_upto O k -> j <= k ->
  infer O @ g ==> Sm (Query (Query B)) -> infer O @ y ==> Sm Y -> evaln j (g @ y) h ->
  infer O @ h ==> Sm (Query B).
Proof using HQ.
  intros k j B g y Y h HB Hk Hj Hg Hy Hh.
  exact (Hk j g y h _ Y _ Hj Hh Hg Hy (QQ_app B Y HB)).
Qed.

(** ... and then applies that value to [z]: the result has type [B]. *)
Theorem query_one_level_value_typing : forall k B b s g t y z U w, names_concrete B ->
  app_sound_upto O k ->
  infer O @ g ==> Sm (Query (Query B)) -> infer O @ Fk y z ==> Sm U -> tag_of (Fk y z) = None ->
  evaln k ('wait3[tq_body, b, s, Fk g t] @ Fk y z) w ->
  infer O @ w ==> Sm B.
Proof using HQ.
  intros k B b s g t y z U w HB Hk Hg Hv Hn Hw.
  destruct (tq_inv_h _ _ _ _ _ _ _ Hw) as
    [[c' [n' [h [j1 [j2 [E _]]]]]]|[[E _]|[[y' [j [E _]]]|[y' [z' [h [j1 [j2 [E [_ [Hj1 [Hj2 [Hk1 Hk2]]]]]]]]]]]]];
    [rewrite E in Hn; cbn in Hn; discriminate|discriminate|discriminate|].
  inversion E; subst y' z'.
  apply infer_inv in Hv; inversion Hv as [| | |u1 u2 Y Z _ Hy Hz _]; subst;
    [match goal with H : tag_of _ = None |- _ => cbn in H; discriminate H end|].
  assert (Hh : infer O @ h ==> Sm (Query B))
    by (eapply query_triage_reduct_typing; [exact HB|exact Hk| |exact Hg|exact Hy|exact Hj1]; lia).
  eapply Hk; [|exact Hj2|exact Hh|exact Hz|].
  - lia.
  - apply (Query_app_r_g O HQ); [apply code_concrete, HB|apply decode_code].
Qed.
End QueryTriage.

(** [special_query[Nat, is_odd, Kq[ff]] : Query[Bool]] takes 1 to [tt] and [tt] to [ff]. *)
Theorem infer_special_query_n :
  infer PO @ special_query Bool Nat is_odd (Kq Bool ff) ==> Sm (Query Bool) /\
  special_query Bool Nat is_odd (Kq Bool ff) @ numeral 1 ==> tt /\
  special_query Bool Nat is_odd (Kq Bool ff) @ tt ==> ff.
Proof. repeat split; by_runB. Qed.

(** The headcount has type [Query[Nat]] at [paper_ontology]. *)
Theorem count_employees_typed : infer PO @ employee_count ==> Sm (Query Nat).
Proof. by_runB. Qed.

(** ** Patching a pending query *)

(** The pending query [paid_over[57] @ department_2025] and its patch
    [paid_over[58] @ department_2026] both have expression type [List[Emp]]. *)
Theorem patched_query_typed :
  infer_expression PO @ (paid_over 57 @ department_example) ==> Sm (List Employee) /\
  infer_expression PO @ (paid_over 58 @ incremented_department) ==> Sm (List Employee).
Proof. split; by_runB. Qed.

(** The salary update patches both the query and the data of the pending
    application and preserves its expression type. *)
Theorem salary_update_pending_query_typed :
  infer_expression PO @ (paid_over 57 @ department_example) ==> Sm (List Employee) /\
  salary_update @ (paid_over 57 @ department_example) ==> (paid_over 58 @ incremented_department) /\
  infer_expression PO @ (paid_over 58 @ incremented_department) ==> Sm (List Employee).
Proof.
  destruct patched_query_typed as [H1 H2].
  split; [exact H1|split; [exact (proj1 (proj1 patch_commutes_with_evaluation))|exact H2]].
Qed.

(** ** infer refuses abstract argument types *)

(** [infer] is its own type, and its type application refuses [Bool]. *)
Theorem type_app_infer_Bool :
  infer PO @ infer PO ==> Sm (infer PO) /\ tp PO @ infer PO @r Bool ==> Lf.
Proof. split; [exact paper_infer_self_typed|by_runB]. Qed.

