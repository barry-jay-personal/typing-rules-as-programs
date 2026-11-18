(** * Step 82: queries, part 3 of 3 (split for build time): the triage carrier, soundness, constructor typings, examples. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Export queries_core queries_entries.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries_core queries_entries.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Opaque qK_prog qS_prog qsp_prog qe_prog gdq_prog or_prog gtq_prog.

(** Height-aware inversion of the triage carrier. *)
Lemma tq_inv_h : forall k b s g t v w, evaln k ('wait3[tq_body, b, s, Fk g t] @ v) w ->
  (exists c n h j1 j2, v = 'tagged[c,n] /\ evaln j1 (t @ c) h /\ evaln j2 (h @ n) w /\ j1 < k /\ j2 < k) \/
  (v = Lf /\ w = b) \/
  (exists y j, v = Sm y /\ evaln j (s @ y) w /\ j < k) \/
  (exists y z h j1 j2, v = Fk y z /\ tag_of v = None /\ evaln j1 (g @ y) h /\ evaln j2 (h @ z) w /\
     j1 < k /\ j2 < k).
Proof.
  intros k b s g t v w H.
  pose proof (get_tagged_spec v) as HG.
  pose proof (get_l_fk g t) as Hgl; pose proof (get_r_fk g t) as Hgr.
  destruct (tag_of v) as [[f n]|] eqn:E.
  - apply tag_of_some in E; subst v. left.
    pose proof (get_l_fk f n) as Hl; pose proof (get_r_fk f n) as Hr.
    unfold tq_body in H; do 3 crunchn; finl.
  - right. destruct v as [|y|y z].
    + left. unfold tq_body in H; do 3 crunchn; split; reflexivity.
    + right; left. unfold tq_body in H; do 3 crunchn; finl.
    + right; right. unfold tq_body in H; do 3 crunchn; finl.
Qed.

Section QueryGeneric.
Variable O : Combination.
Hypothesis HQ : forall r, concreteb r = true -> O @ query_tag r @r tp O ==> Sm (D_query r (tp O)).

Lemma Query_app_r_g : forall r B U, concreteb r = true -> decode r = Some B ->
  tp O @ 'label[query_tag r] @r U ==> Sm B.
Proof using HQ. intros r B U Hr H; eapply tp_abs; [apply HQ; exact Hr|apply elim_of_fwd, qe_fwd; exact H]. Qed.

(** The query declaration is sound by values. *)
Theorem query_decl_sound_g : forall r, concreteb r = true -> decl_sound O (query_tag r) (D_query r (tp O)).
Proof using HQ.
  intros r Hr k C U V c v w HC HE Hc Hv Hk Hw.
  apply elim_of_inv, qe_inv in HE.
  destruct (query_guard_inv _ _ _ HC) as [[B [HB ->]]|[[cF [cV [F [W [B [-> [HF [HW [HB HFW]]]]]]]]]|
     [[cT [F [T [B [-> [HT [HB HFT]]]]]]]|[->|[B [HB ->]]]]]];
    try (rewrite HB in HE; inversion HE; subst B).
  - (* constant *)
    destruct (type_Fk_inv O c _ _ Hc) as [[m E]|[x [b [-> [_ [Hx [Hb _]]]]]]]; [discriminate|].
    pose proof (type_Lf_inv O _ Hx) as ->.
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (eval_k b v)) as ->; exact Hb.
  - (* applicative *)
    destruct (type_Fk_inv O c _ _ Hc) as [[m E]|[x [f [-> [_ [Hx [Hf _]]]]]]]; [discriminate|].
    destruct (type_Sm_inv O _ _ Hx) as [g [-> Hg]].
    pose proof (Fk_name_concrete _ _ _ _ Hg) as HcF; pose proof (Fk_name_concrete _ _ _ _ Hf) as HcV.
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    assert (Hp1 : infer O @ p1 ==> Sm F) by (eapply Hk; [|exact H1|exact Hg|exact Hv|apply Query_app_r_g; [exact HcF|exact HF]]; lia).
    assert (Hp2 : infer O @ p2 ==> Sm W) by (eapply Hk; [|exact H2|exact Hf|exact Hv|apply Query_app_r_g; [exact HcV|exact HW]]; lia).
    eapply Hk; [|exact H3|exact Hp1|exact Hp2|exact HFW]; lia.
  - (* specialised *)
    force O.
    match goal with Hw : evaln k ('wait3[sp_body, ?cv, ?f, ?d] @ v) w,
                    Hcv : infer O @ ?cv ==> Sm cT, Hf : infer O @ ?f ==> Sm F,
                    Hd : infer O @ ?d ==> Sm _ |- _ =>
      destruct (sp_inv_h _ _ _ _ _ _ Hw) as [j [[[E Hj]|[E Hj]] Hjk]];
      [ rewrite (type_of_agrees O v U Hv) in E; subst;
        pose proof (concrete_is_self_typed O _ (code_concrete U (type_names_concrete O v U Hv))) as Hs;
        pose proof (eval_deterministic _ _ Hs _ Hcv) as E1; inversion E1; subst;
        rewrite decode_code in HT; inversion HT; subst;
        eapply Hk; [|exact Hj|exact Hf|exact Hv|exact HFT]; lia
      | eapply Hk; [|exact Hj|exact Hd|exact Hv|apply Query_app_r_g; [exact Hr|exact HB]]; lia ]
    end.
  - (* diagonal *)
    assert (HQQ : forall X, tp O @ QQl r @r X ==> Sm ('label[Fk query_nm r])).
    { intros X; unfold QQl; apply Query_app_r_g; [cbn; rewrite Hr; reflexivity|cbn; reflexivity]. }
    destruct (type_Fk_inv O c _ _ Hc) as [[m E]|[x [i [-> [_ [Hx [Hi _]]]]]]]; [discriminate|].
    destruct (type_Sm_inv O _ _ Hx) as [g [-> Hg]].
    apply (concrete_type_forces O) in Hi; [subst i|reflexivity].
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ (I_eval v)) as ->.
    assert (Hp1 : infer O @ p1 ==> Sm ('label[Fk query_nm r])) by (eapply Hk; [|exact H1|exact Hg|exact Hv|apply HQQ]; lia).
    eapply Hk; [|exact H3|exact Hp1|exact Hv|apply Query_app_r_g; [exact Hr|exact HE]]; lia.
  - (* triage *)
    assert (HQQ : forall X, tp O @ QQl r @r X ==> Sm ('label[Fk query_nm r])).
    { intros X; unfold QQl; apply Query_app_r_g; [cbn; rewrite Hr; reflexivity|cbn; reflexivity]. }
    assert (HQ1 : forall X, tp O @ 'label[Fk query_nm r] @r X ==> Sm V) by (intros X; apply Query_app_r_g; assumption).
    force O.
    match goal with Hw : evaln k ('wait3[tq_body, ?b, ?s, Fk ?g ?t] @ v) w |- _ =>
      assert (Hb : infer O @ b ==> Sm V) by assumption;
      assert (Hs : infer O @ s ==> Sm ('label[Fk query_nm r])) by assumption;
      assert (Hg : infer O @ g ==> Sm (QQl r)) by assumption;
      assert (Ht : infer O @ t ==> Sm (QQl r)) by assumption;
      destruct (tq_inv_h _ _ _ _ _ _ _ Hw) as [[c' [n' [h [j1 [j2 [-> [Hj1 [Hj2 [Hk1 Hk2]]]]]]]]]|[[-> ->]|[[y [j [-> [Hj Hjk]]]]|
        [y [z [h [j1 [j2 [-> [Hn [Hj1 [Hj2 [Hk1 Hk2]]]]]]]]]]]]]
    end.
    + apply infer_inv in Hv; inversion Hv; subst;
        try (match goal with H : tag_of _ = None |- _ => cbn in H; discriminate H end).
      match goal with Hc' : concreteb n' = true, Hf : infer O @ c' ==> Sm ?F |- _ =>
        assert (Hh : infer O @ h ==> Sm ('label[Fk query_nm r]))
          by (eapply Hk; [|exact Hj1|exact Ht|exact Hf|apply HQQ]; lia);
        eapply Hk; [|exact Hj2|exact Hh|apply concrete_is_self_typed, Hc'|apply HQ1]; lia
      end.
    + exact Hb.
    + apply infer_inv in Hv; inversion Hv; subst.
      eapply Hk; [|exact Hj|exact Hs|eassumption|apply HQ1]; lia.
    + apply infer_inv in Hv; inversion Hv; subst;
        [match goal with H : tag_of _ = None |- _ => discriminate H end|].
      assert (Hh : infer O @ h ==> Sm ('label[Fk query_nm r]))
        by (eapply Hk; [|exact Hj1|exact Hg|eassumption|apply HQQ]; lia).
      eapply Hk; [|exact Hj2|exact Hh|eassumption|apply HQ1]; lia.
Qed.

End QueryGeneric.

(** The query declaration is sound by values. *)
Theorem query_decl_sound : forall r, concreteb r = true -> decl_sound O_q (query_tag r) (D_query r (tp O_q)).
Proof. intros r Hr; apply query_decl_sound_g; [exact O_q_query|exact Hr]. Qed.

Theorem O_q_sound : ontology_sound O_q.
Proof.
  intros n D H.
  destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst.
    unfold G_rows, D_rows, L_rows, O_rows in HL; cbn [lookup List.app] in HL.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_q_static; reflexivity|apply guard_of_pair].
    + eapply ctor_decl_sound; [reflexivity|apply O_q_static; reflexivity|apply guard_of_pair].
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_q_static; reflexivity|apply guard_of_pair].
    + apply gcons_decl_sound, O_q_list.
    + apply gnil_decl_sound, O_q_list.
  - destruct (Q_fam_inv _ _ _ HF) as [HL|[[r [-> [Hr ->]]]|[r [-> [Hr ->]]]]];
      [|apply query_decl_sound; exact Hr|eapply ctor_decl_sound; [|apply O_q_query; exact Hr|apply guard_of_pair];
        unfold query_tag; cbn [concreteb]; rewrite Hr; reflexivity].
    destruct (L_fam_inv _ _ _ HL) as [[-> ->]|[[-> ->]|[[r [-> ->]]|[r [-> [Hc ->]]]]]].
    + apply upd_decl_sound_g, O_q_update.
    + apply mku_decl_sound_g, O_q_update.
    + apply list_decl_sound.
    + eapply ctor_decl_sound; [cbn; exact Hc|apply O_q_list|apply guard_of_pair].
Qed.

Corollary O_q_typing_sound : typing_sound O_q.
Proof. apply evaluation_preserves_typing, O_q_sound. Qed.

(** ** Constructor typings *)

Lemma qK_hit : forall B, 'wait[qK_prog, code B] @ ('K1 B) ==> 'K.
Proof.
  intros B; apply wait_eval. Local Transparent qK_prog. unfold qK_prog. Local Opaque qK_prog.
  pose proof (decode_p_code B) as Hd; pose proof (equal_eq ('K1 B)) as He; ev2.
Qed.

Theorem Kq_typed : forall B b, names_concrete B -> infer O_q @ b ==> Sm B -> infer O_q @ Kq B b ==> Sm (Query B).
Proof.
  intros B b HB Hb; eapply infer_tag.
  - unfold query_tag; cbn [concreteb]; rewrite (code_concrete B HB).
    assert (E : label_pair query_nm (code B) = false) by reflexivity; rewrite E; reflexivity.
  - apply infer_fork; [reflexivity|apply infer_leaf|exact Hb|reflexivity].
  - apply O_q_query, code_concrete, HB.
  - eapply app2; [apply guard_of_pair|]. unfold query_guard. apply or_g_l, qK_hit.
Qed.

(** Every query applies at every argument. *)
Theorem generic_query_application_q : forall q B x U, names_concrete B ->
  infer O_q @ q ==> Sm (Query B) -> infer O_q @ x ==> Sm U -> infer_expression O_q @ (q @ x) ==> Sm B.
Proof. intros q B x U HB Hq Hx; eapply ie_fork; [apply ie_stem, Hq|apply ie_stem, Hx|apply Query_app, HB]. Qed.

(** ** Examples, by computation *)

Ltac by_runq := apply (runp_sound 40); vm_done.

Example Kq_eval : Kq Nat zero @ tt ==> zero. Proof. by_runq. Qed.
Example Sq_typed : infer O_q @ Sq Nat (Kq ('K1 Nat) ('K1 zero)) (Kq Bool tt) ==> Sm (Query Nat). Proof. by_runq. Qed.
Example Sq_eval : Sq Nat (Kq ('K1 Nat) ('K1 zero)) (Kq Bool tt) @ ff ==> zero. Proof. by_runq. Qed.
Example rec_query_typed : infer O_q @ rec_query Nat ('K1 (Kq Nat zero)) (Kq Nat zero) ==> Sm (Query Nat). Proof. by_runq. Qed.
Example rec_query_eval : rec_query Nat ('K1 (Kq Nat zero)) (Kq Nat zero) @ tt ==> zero. Proof. by_runq. Qed.
Example employee_count_typed : infer O_q @ employee_count ==> Sm (Query Nat). Proof. by_runq. Qed.
Theorem employee_count_department : employee_count @ department_example ==> numeral 3. Proof. by_runq. Qed.
Theorem employee_count_department_typed : infer_expression O_q @ (employee_count @ department_example) ==> Sm Nat.
Proof. by_runq. Qed.
Example employee_count_other : employee_count @ tt ==> zero. Proof. by_runq. Qed.
