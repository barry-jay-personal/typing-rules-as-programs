(** * Step 82, stage 5, part 1: the triage query, size, recursive queries.

    The triage query [triageq[B,b,s,g] = tagged[wait3[tq_body,b,s,g], query_tag[code B]]]:

      tq_body b s g tagged[c,n] = s @ c        (the carrier only, never the label)
      tq_body b s g Lf          = b
      tq_body b s g (Sm y)      = s @ y
      tq_body b s g (Fk y z)    = g @ y @ z    (Fk y z not a tag)

    admitted by the query guard at carrier type
    [wait3[tq_body, B, Query[B], Query[Query[B]]]].  The declaration stays
    sound by values ([query_decl_sound_g], queries.v).

    Queries built at run time are tagged by the query constructor
    [mk_query[B]] (family at [Fk mkq_nm r]), since [tagger] is untyped.

    Step 89: a recursive query is built from a recursive update with a seed
    [s : Query[B]] (queries_core.v): [rec_query[B,f,s] = D[fix_update[c], s]],
    and [rec_query[B,f,s] @ x] evaluates [f @ rec_query[B,f,s] @r x]
    ([rec_query_unfold]).  The query guard has no recursive clause.

    [size = rec_query[Nat, size_body, Kq[Nat, 1]]], where [size_body @ r] is a triage
    query whose leaf case is 1, whose stem case is [Sq[Kq[succ], r]] and
    whose fork case is [Sq[Kq[h_of r], ...]] (sum of the two recursive
    results, plus one). *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries sums array_family paper_ontology.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

(** ** Paper names for the elimination rules *)

Theorem type_app_Query : forall B U, names_concrete B -> tp PO @ Query B @r U ==> Sm B.
Proof.
  intros B U HB; eapply tp_abs; [apply PO_query, code_concrete, HB|apply elim_of_fwd, qe_fwd, decode_code].
Qed.

Theorem type_app_Update : forall U, tp PO @ Update @r U ==> Sm U.
Proof. apply Update_app_g, PO_update. Qed.

(** A concrete code has concrete names. *)
Lemma code_concrete_inv : forall A, concreteb (code A) = true -> names_concrete A.
Proof.
  induction A as [|u IH|u IHu v IHv]; intro H; cbn [names_concrete]; [exact I|exact (IH H)|].
  cbn [code] in H; destruct (label_of (Fk u v)) as [n|] eqn:E.
  - cbn in H. exact H.
  - change (negb (label_pair (Sm (code u)) (code v)) && concreteb (code u) && concreteb (code v) = true) in H.
    apply andb_prop in H as [H Hv]; apply andb_prop in H as [_ Hu]; split; [apply IHu|apply IHv]; assumption.
Qed.

(** The type parameter of a typed query has concrete names. *)
Lemma query_type_names : forall O q B, infer O @ q ==> Sm (Query B) -> names_concrete B.
Proof.
  intros O q B H; apply code_concrete_inv. unfold Query in H.
  destruct (no_junk O q _ H) as [f [F [D [_ [Hn _]]]]].
  unfold query_tag in Hn; cbn in Hn; exact Hn.
Qed.

(** ** Guard hits and misses *)

Lemma qK_miss : forall r C, (forall B, C <> 'K1 B) -> exists v, 'wait[qK_prog, r] @ C ==> v /\ is_Kb v = false.
Proof.
  intros r C HC; pose proof (decode_p_eval r) as Hd; destruct (decode r) as [B|]; cbn [opt] in Hd.
  - exists ('KI); split; [|reflexivity]. apply wait_eval; unfold qK_prog.
    pose proof (equal_neq _ _ (HC B)) as He; ev2.
  - eexists; split; [apply wait_eval; unfold qK_prog; ev2; apply equal_eval|reflexivity].
Qed.

Ltac miss_run := split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | apply decode_p_eval | (apply equal1_neq; cbn [left_of right_of stem_of]; discriminate)
    | progress cbn [left_of right_of stem_of] | progress evaluate2].


Lemma qS_miss_tq : forall r a b s g, 'wait2[qS_prog, r, a] @ 'wait3[tq_body, b, s, g] ==> 'KI.
Proof. intros; apply wait2_eval; unfold qS_prog; miss_run. Qed.
Lemma tq_sp_neq : tq_body <> sp_body. Proof. vm_compute; discriminate. Qed.
Lemma qsp_miss_tq : forall r a b s g, 'wait2[qsp_prog, r, a] @ 'wait3[tq_body, b, s, g] ==> 'KI.
Proof.
  intros; apply wait2_eval; unfold qsp_prog.
  split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | apply decode_p_eval
    | (apply equal1_neq; cbn [left_of right_of stem_of]; intro E; inversion E as [E1];
       exact (tq_sp_neq E1))
    | progress cbn [left_of right_of stem_of] | progress evaluate2].
Qed.

Lemma gtq_hit : forall B, 'wait[gtq_prog, code B] @ 'wait3[tq_body, B, 'label[Fk query_nm (code B)], Fk (QQl (code B)) (QQl (code B))] ==> 'K.
Proof.
  intros B; apply wait_eval; unfold gtq_prog, QQl.
  pose proof (decode_p_code B) as Hd.
  pose proof (equal_eq ('wait3[tq_body, B, 'label[Fk query_nm (code B)],
     Fk ('label[Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm (code B)))]) ('label[Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm (code B)))])])) as He.
  ev2.
Qed.

Lemma gdq_hit : forall r, 'wait[gdq_prog, r] @ 'S2[QQl r, 'I] ==> 'K.
Proof.
  intros r; apply wait_eval; unfold gdq_prog, QQl.
  pose proof (equal_eq ('S2['label[Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm r))], 'I])) as He. ev2.
Qed.
Lemma gdq_miss : forall r C, C <> 'S2[QQl r, 'I] -> 'wait[gdq_prog, r] @ C ==> 'KI.
Proof.
  intros r C H; apply wait_eval; unfold gdq_prog.
  pose proof (equal_neq _ _ H) as He; unfold QQl in He; ev2.
Qed.
Lemma gdq_miss_tq : forall r b s g, 'wait[gdq_prog, r] @ 'wait3[tq_body, b, s, g] ==> 'KI.
Proof. intros; apply gdq_miss; discriminate. Qed.
Lemma qS_miss_dq : forall r a G, 'wait2[qS_prog, r, a] @ 'S2[G, 'I] ==> 'KI.
Proof. intros; apply wait2_eval; unfold qS_prog; miss_run. Qed.
Lemma qsp_miss_dq : forall r a r', 'wait2[qsp_prog, r, a] @ 'S2[QQl r', 'I] ==> 'KI.
Proof. intros; apply wait2_eval; unfold qsp_prog, QQl; miss_run. Qed.

Lemma qK_miss_code : forall X C, (forall B, C <> 'K1 B) -> 'wait[qK_prog, code X] @ C ==> 'KI.
Proof.
  intros X C HC; pose proof (decode_p_code X) as Hd. apply wait_eval; unfold qK_prog.
  pose proof (equal_neq _ _ (HC X)) as He; ev2.
Qed.

Lemma gsp_hit_code : forall m a cT T F, decode cT = Some T -> a @ F @r T ==> Sm T ->
  'wait2[gsp_prog, m, a] @ 'wait3[sp_body, cT, F, 'label[m]] ==> 'K.
Proof. intros m a cT T F HT H; rewrite <- (code_decode _ _ HT); apply gsp_hit; exact H. Qed.

Lemma names_concrete_Query : forall B, names_concrete B -> names_concrete (Query B).
Proof. intros B HB; cbn. rewrite (code_concrete B HB). reflexivity. Qed.

Lemma qS_hit : forall B F V a, a @ F @r V ==> Sm B ->
  'wait2[qS_prog, code B, a] @ 'S2[Query F, Query V] ==> 'K.
Proof.
  intros B F V a H; apply wait2_eval. Local Transparent qS_prog. unfold qS_prog. Local Opaque qS_prog.
  pose proof (decode_p_code B) as HdB; pose proof (decode_p_code F) as HdF; pose proof (decode_p_code V) as HdV.
  pose proof (equal_eq B) as He1; pose proof (equal_eq ('S2[Query F, Query V])) as He2.
  unfold Query, query_tag in *; ev_many.
Qed.


Lemma qsp_hit : forall B T F a, a @ F @r T ==> Sm B ->
  'wait2[qsp_prog, code B, a] @ 'wait3[sp_body, code T, F, Query B] ==> 'K.
Proof.
  intros B T F a H; apply wait2_eval. Local Transparent qsp_prog. unfold qsp_prog. Local Opaque qsp_prog.
  pose proof (decode_p_code B) as HdB; pose proof (decode_p_code T) as HdT.
  pose proof (equal_eq B) as He1; pose proof (equal_eq (Query B)) as He2.
  pose proof (equal_eq ('wait3[sp_body, code T, F, Query B])) as He3.
  unfold Query, query_tag in *; ev_many.
Qed.

Lemma qS_miss_sp : forall r a cT F D, 'wait2[qS_prog, r, a] @ 'wait3[sp_body, cT, F, D] ==> 'KI.
Proof.
  intros; apply wait2_eval. Local Transparent qS_prog. unfold qS_prog. Local Opaque qS_prog. miss_run.
Qed.



(** ** Generic typings of the triage query and of recursive queries *)

Section Generic.
Variable O : Combination.
Hypothesis HQ : forall r, concreteb r = true -> O @ query_tag r @r tp O ==> Sm (D_query r (tp O)).

Lemma query_tag_concrete : forall B, names_concrete B -> concreteb (query_tag (code B)) = true.
Proof.
  intros B HB; unfold query_tag; cbn [concreteb]; rewrite (code_concrete B HB).
  assert (E : label_pair query_nm (code B) = false) by reflexivity; rewrite E; reflexivity.
Qed.

Theorem infer_triageq : forall B b s g t,
  infer O @ b ==> Sm B -> infer O @ s ==> Sm (Query B) -> infer O @ g ==> Sm (Query (Query B)) ->
  infer O @ t ==> Sm (Query (Query B)) ->
  infer O @ triageq B b s g t ==> Sm (Query B).
Proof using HQ.
  intros B b s g t Hb Hs Hg Ht. pose proof (type_names_concrete O b B Hb) as HB.
  change (Query (Query B)) with (QQl (code B)) in Hg, Ht.
  destruct (no_junk O g _ Hg) as [fg [? [? [-> _]]]].
  assert (Hgt : infer O @ Fk ('tagged[fg, Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm (code B)))]) t ==>
     Sm (Fk (QQl (code B)) (QQl (code B)))) by (apply infer_fork; [reflexivity|exact Hg|exact Ht|reflexivity]).
  assert (Hc : infer O @ 'wait3[tq_body, b, s, Fk ('tagged[fg, Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm (code B)))]) t] ==>
     Sm ('wait3[tq_body, B, 'label[Fk query_nm (code B)], Fk (QQl (code B)) (QQl (code B))])).
  { unfold Query, query_tag in Hs; build O. }
  eapply infer_tag; [apply query_tag_concrete, HB|exact Hc|apply HQ, code_concrete, HB|].
  eapply app2; [apply guard_of_pair|]. unfold query_guard.
  destruct (qK_miss (code B) ('wait3[tq_body, B, 'label[Fk query_nm (code B)], Fk (QQl (code B)) (QQl (code B))])) as [v [Hv Hk]];
    [intros X; discriminate|].
  eapply or_g_r; [exact Hv|exact Hk|].
  eapply or_g_r; [apply qS_miss_tq|reflexivity|].
  eapply or_g_r; [apply qsp_miss_tq|reflexivity|].
  eapply or_g_r; [apply gdq_miss_tq|reflexivity|].
  apply gtq_hit.
Qed.

Lemma Kq_typed_g : forall B b, infer O @ b ==> Sm B -> infer O @ Kq B b ==> Sm (Query B).
Proof using HQ.
  intros B b Hb; pose proof (type_names_concrete O b B Hb) as HB. eapply infer_tag.
  - unfold query_tag; cbn [concreteb]; rewrite (code_concrete B HB).
    assert (E : label_pair query_nm (code B) = false) by reflexivity; rewrite E; reflexivity.
  - apply infer_fork; [reflexivity|apply infer_leaf|exact Hb|reflexivity].
  - apply HQ, code_concrete, HB.
  - eapply app2; [apply guard_of_pair|]. unfold query_guard. apply or_g_l, qK_hit.
Qed.

Lemma Sq_typed_g : forall B g f F V, names_concrete B ->
  infer O @ g ==> Sm (Query F) -> infer O @ f ==> Sm (Query V) -> tp O @ F @r V ==> Sm B ->
  infer O @ Sq B g f ==> Sm (Query B).
Proof using HQ.
  intros B g f F V HB Hg Hf HF.
  destruct (no_junk O g _ Hg) as [fg [? [? [-> _]]]].
  assert (Hc : infer O @ 'S2['tagged[fg, query_tag (code F)], f] ==> Sm ('S2[Query F, Query V]))
    by (apply infer_fork; [reflexivity|apply infer_stem; exact Hg|exact Hf|reflexivity]).
  eapply infer_tag; [apply query_tag_concrete, HB|exact Hc|apply HQ, code_concrete, HB|].
  eapply app2; [apply guard_of_pair|]. unfold query_guard.
  destruct (qK_miss (code B) ('S2[Query F, Query V])) as [v [Hv Hk]]; [intros X; discriminate|].
  eapply or_g_r; [exact Hv|exact Hk|].
  apply or_g_l, qS_hit; exact HF.
Qed.

Lemma special_query_typed_g : forall B T f d F, names_concrete T ->
  infer O @ d ==> Sm (Query B) -> infer O @ f ==> Sm F -> tp O @ F @r T ==> Sm B ->
  infer O @ special_query B T f d ==> Sm (Query B).
Proof using HQ.
  intros B T f d F HT Hd Hf HF.
  pose proof (query_type_names O d B Hd) as HB.
  pose proof (code_self_typed O T HT) as HiT.
  assert (Hc : infer O @ 'wait3[sp_body, code T, f, d] ==> Sm ('wait3[sp_body, code T, F, Query B]))
    by (unfold Query, query_tag in Hd; build O).
  eapply infer_tag; [apply query_tag_concrete, HB|exact Hc|apply HQ, code_concrete, HB|].
  eapply app2; [apply guard_of_pair|]. unfold query_guard.
  destruct (qK_miss (code B) ('wait3[sp_body, code T, F, Query B])) as [v [Hv Hk]]; [intros X; discriminate|].
  eapply or_g_r; [exact Hv|exact Hk|].
  eapply or_g_r; [apply qS_miss_sp|reflexivity|].
  apply or_g_l, qsp_hit; exact HF.
Qed.
Lemma diag_typed_g : forall B g, infer O @ g ==> Sm (Query (Query B)) -> infer O @ Sq B g 'I ==> Sm (Query B).
Proof using HQ.
  intros B g Hg. pose proof (query_type_names O g _ Hg) as HQB.
  assert (HB : names_concrete B) by (apply code_concrete_inv; exact HQB).
  change (Query (Query B)) with (QQl (code B)) in Hg.
  destruct (no_junk O g _ Hg) as [fg [? [? [-> _]]]].
  assert (Hc : infer O @ 'S2['tagged[fg, Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm (code B)))], 'I] ==> Sm ('S2[QQl (code B), 'I]))
    by (apply infer_fork; [reflexivity|apply infer_stem; exact Hg|apply concrete_is_self_typed; reflexivity|reflexivity]).
  eapply infer_tag; [apply query_tag_concrete, HB|exact Hc|apply HQ, code_concrete, HB|].
  eapply app2; [apply guard_of_pair|]. unfold query_guard.
  destruct (qK_miss (code B) ('S2[QQl (code B), 'I])) as [v [Hv Hk]]; [intros X; discriminate|].
  eapply or_g_r; [exact Hv|exact Hk|].
  eapply or_g_r; [apply qS_miss_dq|reflexivity|].
  eapply or_g_r; [apply qsp_miss_dq|reflexivity|].
  apply or_g_l, gdq_hit.
Qed.


Theorem generic_query_application : forall q B x U,
  infer O @ q ==> Sm (Query B) -> infer O @ x ==> Sm U -> infer_expression O @ (q @ x) ==> Sm B.
Proof using HQ.
  intros q B x U Hq Hx; pose proof (query_type_names O q B Hq) as HB; eapply ie_fork; [apply ie_stem, Hq|apply ie_stem, Hx|].
  eapply tp_abs; [apply HQ, code_concrete, HB|apply elim_of_fwd, qe_fwd, decode_code].
Qed.

(** A query applies to any typed expression. *)
Theorem query_on_expressions : forall q B e T,
  infer O @ q ==> Sm (Query B) -> infer_expression O @ e ==> Sm T -> infer_expression O @ (Fk (Sm q) e) ==> Sm B.
Proof using HQ.
  intros q B e T Hq He; pose proof (query_type_names O q B Hq) as HB; eapply ie_fork; [apply ie_stem, Hq|exact He|].
  eapply tp_abs; [apply HQ, code_concrete, HB|apply elim_of_fwd, qe_fwd, decode_code].
Qed.
End Generic.


(** ** Recursive queries by recursive updates (Step 89) *)

Ltac lp_false := match goal with |- label_pair ?a ?b = false =>
  let EL := fresh "EL" in destruct (label_pair a b) eqn:EL; [exfalso; let m := fresh "m" in let Em := fresh "Em" in
  destruct (label_pair_K1 _ _ EL) as [m Em]; discriminate Em|reflexivity] end.
Ltac lo_none := match goal with |- label_of ?t = None =>
  let EL := fresh "EL" in destruct (label_of t) eqn:EL; [exfalso; apply label_of_some in EL; discriminate EL|reflexivity] end.

Section RecQueries.
Variable O : Combination.
Hypothesis HQ : forall r, concreteb r = true -> O @ query_tag r @r tp O ==> Sm (D_query r (tp O)).
Hypothesis HMQ : forall r, concreteb r = true -> O @ Fk mkq_nm r @r tp O ==> Sm (D_mkq r (tp O)).
Hypothesis HU : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).
Hypothesis HMU : O @ mku_nm @r tp O ==> Sm (D_mku (tp O)).

Lemma mkq_typed_g : forall X, names_concrete X -> infer O @ mk_query X ==> Sm ('label[Fk mkq_nm (code X)]).
Proof using HMQ.
  intros X HX. pose proof (code_concrete X HX) as Hc.
  assert (Hn : concreteb (Fk mkq_nm (code X)) = true) by (cbn; rewrite Hc; reflexivity).
  eapply infer_tag; [exact Hn|apply concrete_is_self_typed|apply HMQ, Hc|].
  - unfold query_tag; cbn [concreteb]. rewrite Hc. reflexivity.
  - eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec ('tagger[query_tag (code X)]) ('tagger[query_tag (code X)])) as E.
    destruct combination_eq_dec as [_|n]; [exact E|contradiction].
Qed.

Lemma mkq_app : forall X C, names_concrete X -> query_guard (code X) (tp O) @ C ==> 'K ->
  tp O @ 'label[Fk mkq_nm (code X)] @r C ==> Sm (Query X).
Proof using HMQ.
  intros X C HX H; eapply tp_abs; [apply HMQ, code_concrete, HX|]. apply elim_of_fwd, ctor_elim_fwd; exact H.
Qed.

Lemma identity_update_typed_g : infer O @ identity_update ==> Sm Update.
Proof using HU.
  eapply infer_tag; [reflexivity|apply concrete_is_self_typed; reflexivity|exact HU|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard. apply or_g_l.
  pose proof (guard1_spec 'I 'I) as G; destruct combination_eq_dec; [exact G|contradiction].
Qed.

Section RecQuery.
Variables B f F : Combination.
Hypothesis HB : names_concrete B.
Hypothesis Hf : infer O @ f ==> Sm F.
Hypothesis HF : tp O @ F @r Query B ==> Sm (Query B).

Ltac buildR := first
  [ eassumption
  | apply infer_leaf
  | (apply infer_stem; buildR)
  | (apply concrete_is_self_typed; vm_compute; reflexivity)
  | (eapply infer_fork; [first [reflexivity|idtac]|buildR|buildR|first [reflexivity|lp_false]]) ].

Lemma infer_rq_fix : infer O @ rq_fix B f ==> Sm Update.
Proof using HQ HMQ HU HMU HB Hf HF.
  pose proof (names_concrete_Query B HB) as HQB.
  assert (HUc : names_concrete Update) by (cbn; reflexivity).
  pose proof (mkq_typed_g B HB) as M1. pose proof (mkq_typed_g (Query B) HQB) as M2. pose proof (mkq_typed_g Update HUc) as M3.
  pose proof (mk_update_typed_g O HMU) as M4. pose proof identity_update_typed_g as M5.
  pose proof (code_self_typed O (Query B) HQB) as M6.
  evar (Bc : Combination).
  assert (Hb : infer O @ rq_body B f ==> Sm Bc) by (unfold rq_body, Bc; buildR).
  assert (H1 : query_guard (code Update) (tp O) @ ('K1 Update) ==> 'K) by (unfold query_guard; apply or_g_l, qK_hit).
  assert (H2 : query_guard (code (Query B)) (tp O) @ ('K1 (Query B)) ==> 'K) by (unfold query_guard; apply or_g_l, qK_hit).
  assert (H3 : query_guard (code (Query B)) (tp O) @ 'S2[Query Update, Query (Query B)] ==> 'K).
  { unfold query_guard. eapply or_g_r; [apply qK_miss_code; intros ? ?; discriminate|reflexivity|].
    apply or_g_l, qS_hit, (Update_app_g O HU). }
  assert (H4 : query_guard (code B) (tp O) @ 'S2[Query (Query B), 'I] ==> 'K).
  { unfold query_guard. eapply or_g_r; [apply qK_miss_code; intros ? ?; discriminate|reflexivity|].
    eapply or_g_r; [apply qS_miss_dq|reflexivity|].
    eapply or_g_r; [apply qsp_miss_dq|reflexivity|]. apply or_g_l. exact (gdq_hit (code B)). }
  assert (HBc : tp O @ Bc @r Update ==> Sm Update).
  { unfold Bc. repeat first
    [ eassumption
    | (apply mkq_app; [assumption|eassumption])
    | apply (Update_app_g O HU)
    | (apply (mku_app O HMU); unfold upd_guard;
       eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
       eapply or_g_r; [apply gch_miss; discriminate|reflexivity|]; apply or_g_l;
       eapply gsp_hit_code; [apply decode_code|])
    | apply tp_K1_fwd
    | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
    | (apply tp_stem; first [reflexivity|lp_false])
    | apply tp_leaf_fwd ]. }
  unfold rq_fix, fix_update.
  assert (Hc : infer O @ Z (rq_body B f 'C 'tagger[update_nm]) ==> Sm (Z (Bc 'C 'tagger[update_nm])))
    by (unfold Z, self_apply, wait1; build O).
  eapply infer_tag; [reflexivity|exact Hc|exact HU|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard.
  eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gch_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit; exact HBc].
Qed.
End RecQuery.

(** A recursive query, from a seed [s : Query[B]] and a functional [f : F]
    with [F # Query[B] ==> Sm Query[B]], has type [Query[B]], and its update
    [rq_fix[B,f] = fix_update[c]] has type [Update].  The names of [B] are
    concrete since [s : Query[B]]. *)
Theorem rec_query_generic : forall B f F s,
  infer O @ f ==> Sm F -> tp O @ F @r Query B ==> Sm (Query B) -> infer O @ s ==> Sm (Query B) ->
  infer O @ rec_query B f s ==> Sm (Query B) /\ infer O @ rq_fix B f ==> Sm Update.
Proof using HQ HMQ HU HMU.
  intros B f F s Hf HF Hs. pose proof (query_type_names O s B Hs) as HB.
  pose proof (infer_rq_fix B f F HB Hf HF) as Hu. split; [|exact Hu].
  unfold rec_query, Dq. apply (diag_typed_g O HQ).
  eapply (Sq_typed_g O HQ); [apply names_concrete_Query, HB|apply (Kq_typed_g O HQ), Hu|apply (Kq_typed_g O HQ), Hs|apply (Update_app_g O HU)].
Qed.
End RecQueries.

(** ** Evaluation *)
Lemma mku_fwd : forall c, mk_update @ c ==> 'tagged[c, update_nm].
Proof. intros; apply tagged_eval, tagger_eval. Qed.
Lemma mkq_fwd : forall B c, mk_query B @ c ==> 'tagged[c, query_tag (code B)].
Proof. intros; apply tagged_eval, tagger_eval. Qed.

Section RQEval.
Local Opaque mk_query mk_update identity_update code Query Update.
Lemma rq_body_eval : forall B f r, exists st, rq_body B f @ r ==> special_type (Query B) st identity_update /\
  forall q v, f @ Dq B r q ==> v -> st @ q ==> v.
Proof.
  intros B f r; eexists; split.
  - unfold rq_body, special_type. split2; evaluate2; repeat first [apply mku_fwd | apply mkq_fwd | progress evaluate2].
  - intros q v H; unfold Dq, Sq, Kq in H.
    split2; evaluate2; repeat first [eassumption | apply mkq_fwd | progress evaluate2].
Qed.
End RQEval.

Lemma S2_fwd : forall g f x a b v, g @ x ==> a -> f @ x ==> b -> a @ b ==> v -> 'S2[g,f] @ x ==> v.
Proof. intros; evaluate; eassumption. Qed.
Lemma K1_fwd : forall a x, ('K1 a) @ x ==> a. Proof. intros; evaluate. Qed.
Lemma Kq_fwd : forall B b x, Kq B b @ x ==> b. Proof. intros; apply tagged_eval, K1_fwd. Qed.

Lemma type_of_tagged : forall c n, type_of ('tagged[c,n]) = 'label[n].
Proof. intros c n; cbn [type_of]; rewrite tag_of_tagged; reflexivity. Qed.

(** At a seed tagged as a query of type [B], the update [rq_fix[B,f]] is [f @ rec_query[B,f,s]]. *)
Lemma rq_fix_at_seed : forall B f cs q, let s := 'tagged[cs, query_tag (code B)] in
  f @ rec_query B f s ==> q -> rq_fix B f @ s ==> q.
Proof.
  intros B f cs q s H.
  destruct (rq_body_eval B f (rq_fix B f)) as [st [Hb Hst]].
  pose proof (tagger_eval update_nm (Z (rq_body B f 'C 'tagger[update_nm]))) as Ht.
  unfold rq_fix at 1, fix_update at 1. apply tagged_eval, Z_unfold.
  eapply eval_appl; [|apply special_type_hit; [apply type_of_tagged|apply Hst; exact H]].
  unfold rq_fix, fix_update in Hb. ev2.
Qed.

(** The unfolding: [rec_query[B,f,s] @ x] is [f @ rec_query[B,f,s] @r x]. *)
Lemma rec_query_unfold : forall B f cs x q v, let s := 'tagged[cs, query_tag (code B)] in
  f @ rec_query B f s ==> q -> q @ x ==> v -> rec_query B f s @ x ==> v.
Proof.
  intros B f cs x q v s H1 H2. pose proof (rq_fix_at_seed B f cs q H1) as Hus.
  unfold rec_query at 1, Dq at 1, Sq at 1. apply tagged_eval.
  eapply S2_fwd; [|apply I_eval|exact H2].
  unfold Sq; apply tagged_eval. eapply S2_fwd; [apply Kq_fwd|apply Kq_fwd|exact Hus].
Qed.

(** ** The value type of a typed expression (moved from updates_paper.v, step 87) *)

Section ExpressionValue.
Variable O : Combination.

Lemma ie_Lf_none : forall T, ~ (infer_expression O @ Lf ==> Sm T).
Proof.
  intros T H; destruct (ie_inv O _ _ H) as [[u [E _]]|[e1 [e2 [T1 [T2 [E _]]]]]]; discriminate.
Qed.

Lemma ie_K1_none : forall x T, ~ (infer_expression O @ Fk Lf x ==> Sm T).
Proof.
  intros x T H; destruct (ie_inv O _ _ H) as [[u [E _]]|[e1 [e2 [T1 [T2 [E [H1 _]]]]]]]; [discriminate|].
  inversion E; subst; exact (ie_Lf_none _ H1).
Qed.

(** The value type of a typed expression determines its expression type. *)
Lemma expression_value_type : forall e T, infer_expression O @ e ==> Sm T ->
  exists V, infer O @ e ==> Sm V /\ forall e', infer O @ e' ==> Sm V -> infer_expression O @ e' ==> Sm T.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intros T H.
  - exfalso; exact (ie_Lf_none _ H).
  - destruct (ie_inv O _ _ H) as [[u' [E Hu]]|[e1 [e2 [T1 [T2 [E _]]]]]]; [|discriminate].
    inversion E; subst u'. exists (Sm T); split; [apply infer_stem, Hu|].
    intros e' He'; destruct (type_Sm_inv O _ _ He') as [u'' [-> Hu'']]; apply ie_stem, Hu''.
  - destruct (ie_inv O _ _ H) as [[u' [E _]]|[a [b [T1 [T2 [E [H1 [H2 H3]]]]]]]]; [discriminate|].
    inversion E; subst a b.
    destruct (IH1 _ H1) as [V1 [Hv1 Hk1]]; destruct (IH2 _ H2) as [V2 [Hv2 Hk2]].
    assert (HL : label_pair V1 V2 = false).
    { destruct (label_pair V1 V2) eqn:EL; [|reflexivity]. exfalso.
      destruct (label_pair_K1 _ _ EL) as [m ->].
      destruct (type_Fk_inv O _ _ _ Hv2) as [[n En]|[x1 [x2 [-> [_ [Hx1 _]]]]]]; [discriminate|].
      pose proof (type_Lf_inv O _ Hx1) as ->. exact (ie_K1_none _ _ H2). }
    exists (Fk V1 V2); split.
    + apply infer_fork; [|exact Hv1|exact Hv2|exact HL].
      destruct (tag_of (Fk e1 e2)) as [[f n]|] eqn:Et; [|reflexivity]. exfalso.
      apply tag_of_some in Et; inversion Et; subst.
      destruct (ie_inv O _ _ H2) as [[u' [E' _]]|[a [b [U1 [U2 [E' [_ [Hb _]]]]]]]]; [discriminate|].
      inversion E'; subst; exact (ie_K1_none _ _ Hb).
    + intros e' He'.
      destruct (type_Fk_inv O _ _ _ He') as [[n En]|[x1 [x2 [-> [_ [Hx1 [Hx2 _]]]]]]].
      * exfalso; rewrite label_pair_of in HL; rewrite En in HL; discriminate.
      * eapply ie_fork; [apply Hk1, Hx1|apply Hk2, Hx2|exact H3].
Qed.
End ExpressionValue.

(** ** The generators of updates and queries at paper_ontology *)

Lemma PO_mku : PO @ mku_nm @r tp PO ==> Sm (D_mku (tp PO)).
Proof.
  unfold PO; apply rows_f_miss; [reflexivity|]. unfold PO_fam; apply alt_some; [|apply arr_fam_partial].
  unfold P_fam; apply alt_some; [|apply tail_partial].
  unfold L_fam; apply alt_some; [apply upd_fam_mku|]. apply alt_partial, list_entry_partial.
Qed.

Lemma PO_mkq : forall r, concreteb r = true -> PO @ Fk mkq_nm r @r tp PO ==> Sm (D_mkq r (tp PO)).
Proof.
  intros r Hr; unfold PO; apply rows_f_miss; [reflexivity|]. unfold PO_fam; apply alt_some; [|apply arr_fam_partial].
  unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_some; [apply mkq_entry_hit; exact Hr|apply sum_fam_partial].
Qed.

(** ** Size *)

Ltac by_runS := apply (runp_sound 40); vm_done.

Definition ty_of (t : Combination) : Combination :=
  match runp 40 (infer PO @ t) with Some (Sm A) => A | _ => Lf end.
Definition ap_ty (F U : Combination) : Combination :=
  match runp 40 (tp PO @ F @r U) with Some (Sm R) => R | _ => Lf end.

Definition S2t (x y : Term) : Term := Val Lf @@ (Val Lf @@ x) @@ y.

(** [asc @ m @ n = succ (add (m * n))]. *)
Definition asc : Combination := Eval cbn -[succ_fn add] in to_tree
  (star "m" (star "n" (op succ_fn @@ (op add @@ (Ref "m" ''* Ref "n"))))).

Definition SuccT : Combination := Eval vm_compute in ty_of succ_fn.
Definition ASC : Combination := Eval vm_compute in ty_of asc.
Definition F1 : Combination := Eval vm_compute in ap_ty ASC Nat.
Definition kq_succ : Combination := Kq SuccT succ_fn.
Definition kq_asc : Combination := Kq ASC asc.

(** [h_of @ r @ m] is the query [z => succ (m + r @ z)]. *)
Definition h_of : Combination := Eval cbn -[mk_query kq_asc] in to_tree
  (star "r" (star "m" (op (mk_query Nat) @@
     S2t (op (mk_query F1) @@ S2t (Val kq_asc) (op (mk_query Nat) @@ (Val 'K @@ Ref "m"))) (Ref "r")))).
Definition HOF : Combination := Eval vm_compute in ty_of h_of.
Definition HT : Combination := Eval vm_compute in ap_ty HOF (Query Nat).
Definition kq_hof : Combination := Kq HOF h_of.

Definition size_body : Combination := Eval cbn -[mk_query kq_succ kq_hof tq_body one] in to_tree
  (star "r" (op (mk_query Nat) @@
     W3 (Val tq_body) (Val one)
        (op (mk_query Nat) @@ S2t (Val kq_succ) (Ref "r"))
        (Val Lf @@
          (op (mk_query (Query Nat)) @@
           S2t (op (mk_query HT) @@ S2t (Val kq_hof) (op (mk_query (Query Nat)) @@ (Val 'K @@ Ref "r")))
               (Ref "r"))
        @@
          (op (mk_query (Query Nat)) @@
           S2t (op (mk_query HT) @@ S2t (Val kq_hof) (op (mk_query (Query Nat)) @@ (Val 'K @@ Ref "r")))
               (Ref "r"))))).

(** The seed is the constant query [Kq[Nat, 0]]; it is never applied. *)
Definition size_seed : Combination := Kq Nat zero.
Definition size : Combination := rec_query Nat size_body size_seed.

Definition SizeBodyT : Combination := Eval vm_compute in ty_of size_body.

Lemma infer_size_body : infer PO @ size_body ==> Sm SizeBodyT. Proof. by_runS. Qed.
Lemma size_body_type_app : tp PO @ SizeBodyT @r Query Nat ==> Sm (Query Nat). Proof. by_runS. Qed.

Lemma infer_size_seed : infer PO @ size_seed ==> Sm (Query Nat). Proof. by_runS. Qed.

Theorem infer_size : infer PO @ size ==> Sm (Query Nat).
Proof.
  eapply rec_query_generic; [exact PO_query|exact PO_mkq|exact PO_update|exact PO_mku
    |exact infer_size_body|exact size_body_type_app|exact infer_size_seed].
Qed.

(** Step 87: [size] measures the snapshot tree [e] itself: [size @ e] is
    the application of [size] to the value [e]. *)
Theorem size_on_paper_expressions : forall e T, infer_expression PO @ e ==> Sm T ->
  infer_expression PO @ (size @ e) ==> Sm Nat.
Proof.
  intros e T He; destruct (expression_value_type PO e T He) as [V [Hv _]].
  eapply generic_query_application; [exact PO_query|exact infer_size|exact Hv].
Qed.

(** Examples: a leaf has size 1, a stem one more than its child, a fork one
    more than the sum of its children, and a tagged value [tagged[c,n]] one
    more than the sum of the sizes of its carrier [c] and its name [n]: the
    tag is counted as a fork over carrier and name, and the label is not
    counted. *)
Example size_leaf : size @ Lf ==> numeral 1. Proof. by_runS. Qed.
Example size_K : size @ 'K ==> numeral 2. Proof. by_runS. Qed.
Example size_K1 : size @ ('K1 Lf) ==> numeral 3. Proof. by_runS. Qed.
Example size_fork : size @ Fk 'K Lf ==> numeral 4. Proof. by_runS. Qed.
Example size_fst : size @ 'fst ==> numeral 12. Proof. by_runS. Qed.
(** [tt = tagged[fst, bool_nm]]: size counts the tag node, the carrier
    [fst] (12) and the name [bool_nm] (5), not the label. *)
Example size_tt : size @ tt ==> numeral 18. Proof. by_runS. Qed.
(** [zero = tagged[fst, nat_nm]], and [nat_nm] has size 6. *)
Example size_zero : size @ zero ==> numeral 19. Proof. by_runS. Qed.
Example size_tt_typed : infer_expression PO @ (size @ tt) ==> Sm Nat. Proof. by_runS. Qed.
