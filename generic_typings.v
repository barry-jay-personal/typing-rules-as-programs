(** * Step 86 (stage 13), part 2: general typings of four constructors.

    The Specification lines of the paper's figures for update types and
    query types, proved at every ontology that declares updates (resp.
    queries):

    - [children_typed_g]: [children r : Update] if [r : Update];
    - [fix_typed_g]: [fix_update b : Update] if [b : F] and [F # Update ==> Sm Update];
    - [Sq_typed_g]: [Sq B g f : Query B] if [g : Query F], [f : Query V],
      [F # V ==> Sm B] and the names of [B] are concrete;
    - [special_query_typed_g]: [special_query B T f d : Query B] if
      [d : Query B], [f : F], [F # T ==> Sm B] and the names of [T] are concrete
      (those of [B] are concrete since [d] has type [Query B]).

    In each case inference of the carrier is structural, so the carrier type
    is the carrier with the types of its parameters in their places, and the
    guard admits that carrier type by one of its arms. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries_core queries_entries queries scott_arithmetic department_queries paper_ontology size_queries.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.

(** ** Updates *)

Section GenericUpdates.
Variable O : Combination.
Hypothesis HO : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).

Lemma children_typed_g : forall r, infer O @ r ==> Sm Update -> infer O @ children r ==> Sm Update.
Proof using HO.
  intros r Hr.
  assert (Hc : infer O @ 'wait[ch_body, r] ==> Sm ('wait[ch_body, 'label[update_nm]]))
    by (unfold Update in Hr; build O).
  eapply infer_tag; [reflexivity|exact Hc|exact HO|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard.
  eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
  apply or_g_l, gch_hit.
Qed.

Lemma fix_typed_g : forall b F, infer O @ b ==> Sm F -> tp O @ F @r Update ==> Sm Update ->
  infer O @ fix_update b ==> Sm Update.
Proof using HO.
  intros b F Hb HF.
  assert (Hc : infer O @ Z (b 'C 'tagger[update_nm]) ==> Sm (Z (F 'C 'tagger[update_nm])))
    by (unfold Z, self_apply, wait1; build O).
  eapply infer_tag; [reflexivity|exact Hc|exact HO|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard.
  eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gch_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit; exact HF].
Qed.
End GenericUpdates.

(** ** Queries

    [qS_hit], [qsp_hit], [qS_miss_sp], [Sq_typed_g] and
    [special_query_typed_g] are in size_queries.v since step 89, where the
    recursive queries use them. *)

(** ** At paper_ontology *)

Local Notation PO := paper_ontology.

Lemma children_typed_PO : forall r, infer PO @ r ==> Sm Update -> infer PO @ children r ==> Sm Update.
Proof. apply children_typed_g, PO_update. Qed.
Lemma fix_typed_PO : forall b F, infer PO @ b ==> Sm F -> tp PO @ F @r Update ==> Sm Update ->
  infer PO @ fix_update b ==> Sm Update.
Proof. apply fix_typed_g, PO_update. Qed.
Lemma Sq_typed_PO : forall B g f F V, names_concrete B ->
  infer PO @ g ==> Sm (Query F) -> infer PO @ f ==> Sm (Query V) -> tp PO @ F @r V ==> Sm B ->
  infer PO @ Sq B g f ==> Sm (Query B).
Proof. apply Sq_typed_g, PO_query. Qed.
Lemma special_query_typed_PO : forall B T f d F, names_concrete T ->
  infer PO @ d ==> Sm (Query B) -> infer PO @ f ==> Sm F -> tp PO @ F @r T ==> Sm B ->
  infer PO @ special_query B T f d ==> Sm (Query B).
Proof. apply special_query_typed_g, PO_query. Qed.
