(** * Divergence: gaps in evaluation and typing (support for the paper's "Concrete recursion" and "Functions").

    [omega] is the concrete self-applying program [S I I].  Its
    self-application has no value, and neither does the typing of that
    application: type application on concrete operators mirrors
    evaluation, so [omega # omega] unfolds to [omega # omega] again.
    The same happens inside function type introduction for [lam omega omega].
    At the end, the truth-teller [Z I]: like the liar [dither_fn]
    (functions.v) its application has no value, and unlike it, its typing
    has none either.

    All proofs compare a recursive evaluation with the original through the
    height-indexed copy [evaln] of [eval] (soundness.v), as in
    [dither_fn_tt_no_value] (functions.v). *)

From Stdlib Require Import Arith Lia.
From TreeTyping Require Import tree typing soundness booleans functions self_typing.
Set Default Proof Using "Type".

Definition omega : Combination := 'S2['I,'I].

(** ** omega is concrete and is its own type *)

Lemma omega_concrete : concrete omega.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma omega_self_typed : forall AI, infer AI @ omega ==> Sm omega.
Proof. intros; apply concrete_is_self_typed, omega_concrete. Qed.

(** ** omega @ omega has no value *)

Lemma I_omega : 'I @ omega ==> omega.
Proof. unfold omega; evaluate. Qed.

Lemma omega_omega_evaln_smaller : forall n v,
  evaln n (omega @ omega) v -> exists m, m < n /\ evaln m (omega @ omega) v.
Proof.
  intros n v H; unfold omega at 1 in H.
  inv_out H.
  match goal with H : evaln _ (Fk (Fk _ _) _) _ |- _ => inv_out H end.
  match goal with H : evaln _ (Fk (Sm _) (Fk _ _)) _ |- _ => inv_out H end.
  repeat match goal with
  | H : evaln _ ('I @ _) ?x |- _ =>
      apply evaln_eval in H;
      pose proof (eval_deterministic _ _ H _ I_omega); subst x; clear H
  end.
  eexists; split; [|eassumption]; lia.
Qed.

Lemma omega_omega_no_value : forall v, ~ (omega @ omega ==> v).
Proof.
  intros v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  destruct (omega_omega_evaln_smaller _ _ Hn) as [m [Hm Hm']].
  exact (IH m Hm v Hm').
Qed.

(** ** omega # omega has no value *)

Local Opaque type_app infer equal equal1 get_tagname.
Local Opaque abstract_case default_body type_app_stem type_app_S
  triage_case get_name_test.

(** Height-indexed inversion of the S clause for an arbitrary result [R],
    given that both component applications succeed. *)
Lemma default_S_evaln_any : forall (AI : Decl) rec G F U w m VG VF R,
  evaln m (default_body AI @ rec @r ('S2[G,F])) w -> evaln m (w @ U) R ->
  rec @ G @r U ==> Sm VG -> rec @ F @r U ==> Sm VF ->
  evaln m (rec @ VG @r VF) R.
Proof.
  intros AI rec G F U w m VG VF R Hw H HG HF.
  assert (HT : evaln m (type_app_S @ rec @r G @r F) w).
  { pose proof (default_S_head_inv _ _ _ _ _ (evaln_eval _ _ _ Hw)) as HS.
    clear H.
    Local Transparent default_body.
    unfold default_body in Hw; invert_evaln.
    Local Opaque default_body.
    all: try (exfalso; match goal with
    | H : evaln _ (get_tagged @ Sm _) (Sm _) |- _ =>
      apply evaln_eval in H; destruct (get_tagged_success_inv _ _ H) as [? [? [HT _]]];
      discriminate HT end).
    all: match goal with
    | HS0 : type_app_S @ ?r @r ?g @r ?f ==> ?w0,
      H1 : evaln _ (type_app_S @ ?r) ?t, H2 : evaln _ (?t @ ?g) ?t1,
      H3 : evaln _ (?t1 @ ?f) ?v |- _ =>
      let E := fresh "E" in
      assert (E : w0 = v) by (eapply eval_deterministic; [exact HS0|
        eapply eval_appl; [eapply eval_appl; [exact (evaln_eval _ _ _ H1)|
          exact (evaln_eval _ _ _ H2)]|exact (evaln_eval _ _ _ H3)]]);
      try rewrite E; evaln_close
    end. }
  clear Hw.
  Local Transparent type_app_S.
  unfold type_app_S in HT; cbn in HT.
  invert_evaln.
  all: repeat match goal with
    | Hc : ?r @ ?g @r ?u ==> Sm ?vg,
      H1 : evaln _ (?r @ ?g) ?x, H2 : evaln _ (?x @ ?u) ?a |- _ =>
        let E := fresh "E" in
        assert (E : a = Sm vg) by (eapply eval_deterministic;
          [eapply eval_appl; [exact (evaln_eval _ _ _ H1)|exact (evaln_eval _ _ _ H2)]
          |exact Hc]);
        clear H2; first [discriminate E | injection E; intros; subst]
    end.
  all: evaln_close.
  Local Opaque type_app_S.
Qed.

Lemma omega_untagged : forall E N, omega <> 'tagged[E,N].
Proof. intros E N H; unfold omega in H; discriminate H. Qed.

(** Type application of [omega] to [omega] unfolds, through the clause for
    [S2[G,F]] with [I # omega ==> Sm omega], to itself at smaller height. *)
Lemma type_app_omega_evaln_smaller : forall (AI : Decl) n R,
  evaln n (type_app AI @ omega @r omega) R ->
  exists m, m < n /\ evaln m (type_app AI @ omega @r omega) R.
Proof.
  intros AI n R H.
  destruct (app_evaln_head AI n omega omega R omega_untagged H)
    as [m [w [Hm [Hw HR]]]].
  exists m; split; [exact Hm|].
  exact (default_S_evaln_any AI (type_app AI) 'I 'I omega w m omega omega R
      Hw HR (app_I AI omega) (app_I AI omega)).
Qed.

Lemma type_app_omega_no_value : forall (AI : Decl) R,
  ~ (type_app AI @ omega @r omega ==> R).
Proof.
  intros AI R H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert R Hn.
  induction n as [n IH] using lt_wf_ind; intros R Hn.
  destruct (type_app_omega_evaln_smaller _ _ _ Hn) as [m [Hm Hm']].
  exact (IH m Hm R Hm').
Qed.

(** ** The typing of the expression omega @ omega has no value

    As an expression, [omega @ omega] is [Fk (Sm omega) (Sm omega)]: the
    application of the quoted value [omega] to itself. *)

Lemma expression_success2_type_app_any_inv : forall AI T1 T2 R,
  expression_success2_type_app AI @ Sm T1 @r Sm T2 ==> R ->
  type_app AI @ T1 @r T2 ==> R.
Proof.
  intros AI T1 T2 R H.
  unfold expression_success2_type_app in H; cbn in H; invert_eval.
  eauto using eval_appl.
Qed.

Lemma infer_expression_omega_omega_no_value : forall (AI : Decl) R,
  ~ (infer_expression AI @ (omega @ omega) ==> R).
Proof.
  intros AI R H.
  destruct (infer_expression_fork_gen_inv AI _ _ _ H) as [a [b [Ha [Hb HR]]]].
  apply infer_expression_stem_inv in Ha; apply infer_expression_stem_inv in Hb.
  pose proof (eval_deterministic _ _ Ha _ (omega_self_typed AI)); subst a.
  pose proof (eval_deterministic _ _ Hb _ (omega_self_typed AI)); subst b.
  apply expression_success2_type_app_any_inv in HR.
  exact (type_app_omega_no_value AI R HR).
Qed.

(** ** The lambda program lam[omega, omega]

    [lam omega omega] is the tagged value [tagged[decorate[omega,omega],
    fun_nm]].  Its carrier [decorate[omega,omega]] is concrete, so it is its
    own type, and function type introduction computes [omega # omega] to
    find the codomain.  Every evaluation of its inference therefore
    contains an evaluation of [omega # omega]. *)

Local Transparent type_app_stem extend_program.
Lemma type_app_stem_fun_any_inv : forall (AI : Decl) app C R,
  type_app_stem AI @ app @r (Sm ('K1 C)) @r ('S2['K,'K1 fun_nm]) ==> R ->
  exists r, function_abstractor_core @ C @r app ==> r.
Proof.
  intros AI app C R H.
  pose proof (functions_declared AI) as HF.
  revert H HF; generalize (dtree AI) as D; intros D H HF.
  unfold type_app_stem in H; cbn in H; unfold extend_program in H.
  repeat first
    [ match goal with
      | HH : get_tagged @ ('tagged[C,fun_nm]) ==> ?v |- _ =>
          is_var v;
          pose proof (eval_deterministic _ _ HH _ (get_tagged_some C fun_nm)) as HE;
          subst v; clear HH
      end
    | progress invert_eval1 ].
  all: match goal with
  | H1 : ?ai @ ?n ==> ?f, H2 : ?f @ ?a ==> ?g, H3 : ?g @ ?c ==> ?r |- _ =>
      assert (HS : ai @ n @r a @r c ==> r)
        by (eapply eval_appl; [eapply eval_appl; eassumption|eassumption]);
      clear H1 H2 H3
  end.
  all: eexists; eapply function_row_inv; eassumption.
Qed.
Local Opaque type_app_stem extend_program.


Lemma check_function_direct_decorate : forall F U,
  exists continuation,
    check_function_direct @ 'decorate[F,U] ==> Sm continuation.
Proof.
  intros F U; eexists; unfold check_function_direct; cbn.
  repeat first [apply get_decorate_some | progress evaluate].
Qed.

Lemma check_function_direct_any_inv : forall type_app0 F U continuation E,
  check_function_direct @ 'decorate[F,U] ==> Sm continuation ->
  continuation @ type_app0 ==> E ->
  exists V, type_app0 @ F @r U ==> V.
Proof.
  intros type_app0 F U continuation E H Happly.
  unfold check_function_direct in H; cbn in H.
  invert_eval.
  all: match goal with
       | Hd : get_decorate @ _ ==> Sm (Fk _ _) |- _ =>
           apply get_decorate_inv in Hd; inversion Hd; subst
       end.
  all: eexists; eapply eval_appl; eauto.
Qed.

Local Transparent function_abstractor_core.
Lemma function_abstractor_decorate_any_inv : forall F U type_app0 r,
  function_abstractor_core @ 'decorate[F,U] @r type_app0 ==> r ->
  exists V, type_app0 @ F @r U ==> V.
Proof.
  intros F U type_app0 r H.
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hr]]; clear H.
  unfold function_abstractor_core in Hw.
  destruct (check_function_direct_decorate F U) as [c Hc].
  destruct (extend_inv _ _ _ _ Hw)
    as [[c' [Hc' ->]]|[[Hnone _]|[l [q [Hfork _]]]]].
  - exact (check_function_direct_any_inv _ _ _ _ _ Hc' Hr).
  - pose proof (eval_deterministic _ _ Hc _ Hnone); discriminate.
  - pose proof (eval_deterministic _ _ Hc _ Hfork); discriminate.
Qed.
Local Opaque function_abstractor_core.

Lemma infer_label_fun_nm : forall AI,
  infer AI @ ('S2['K,'K1 fun_nm]) ==> Sm ('S2['K,'K1 fun_nm]).
Proof.
  intros AI.
  eapply infer_fork.
  - eapply infer_stem; eapply infer_tag_free; tag_free_tac.
  - eapply infer_K1; first [eapply infer_leaf | unfold fun_nm; eapply infer_K1; eapply infer_leaf].
  - eapply type_app_stem_ev; eapply type_app_stem_structural;
      intros; discriminate.
Qed.

Lemma infer_lam_omega_needs_type_app : forall (AI : Decl) R,
  infer AI @ lam omega omega ==> R ->
  exists V, type_app AI @ omega @r omega ==> V.
Proof.
  intros AI R H; unfold lam in H.
  destruct (infer_fork_gen_inv AI _ _ _ H) as [a [b [Ha [Hb HR]]]]; clear H.
  pose proof (eval_deterministic _ _ Ha _
    (infer_tag_free AI (Sm ('K1 ('decorate[omega,omega]))) ltac:(tag_free_tac)));
    subst a.
  pose proof (eval_deterministic _ _ Hb _ (infer_label_fun_nm AI)); subst b.
  apply (proj1 (infer_fork_results_spec AI _ _ R)) in HR.
  apply app_stem_inv in HR.
  destruct (type_app_stem_fun_any_inv _ _ _ _ HR) as [r' Hr'].
  exact (function_abstractor_decorate_any_inv _ _ _ _ Hr').
Qed.

Lemma infer_lam_omega_no_value : forall (AI : Decl) R,
  ~ (infer AI @ lam omega omega ==> R).
Proof.
  intros AI R H.
  destruct (infer_lam_omega_needs_type_app AI R H) as [V HV].
  exact (type_app_omega_no_value AI V HV).
Qed.

(** * The truth-teller Z I

    "This sentence is true" says that its value is its own value.  The
    fixfunction [Z I] does the same: [Z I @ x] unfolds to [I @ Z I @ x],
    that is, to [Z I @ x] again.  So the application has no value, and,
    since [Z I] is concrete, its typing mirrors the unfolding and has no
    value either.  Compare the liar [dither_fn] (functions.v), which is typed
    but has no value. *)

Definition truth_teller : Combination := Z 'I.

(** ** Z I @ x has no value *)

Lemma truth_teller_evaln_smaller : forall n x v,
  evaln n (truth_teller @ x) v ->
  exists m, m < n /\ evaln m (truth_teller @ x) v.
Proof.
  intros n x v H; unfold truth_teller in H.
  destruct (Z_evaln_unfold_inv _ _ _ _ H) as [m [w [Hm [Hw H2]]]].
  assert (Hw' : w = Z 'I) by
    (eapply eval_deterministic; [exact Hw|unfold Z; evaluate]).
  subst w; exists m; split; [exact Hm|exact H2].
Qed.

Lemma truth_teller_no_value : forall x v, ~ (truth_teller @ x ==> v).
Proof.
  intros x v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  destruct (truth_teller_evaln_smaller _ _ _ Hn) as [m [Hm Hm']].
  exact (IH m Hm v Hm').
Qed.

(** ** Z I is concrete, so it is its own type *)

Lemma truth_teller_concrete : concrete truth_teller.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma truth_teller_self_typed : forall AI, infer AI @ truth_teller ==> Sm truth_teller.
Proof. intros; apply concrete_is_self_typed, truth_teller_concrete. Qed.

(** ** Z I # U has no value *)

Local Transparent extend_program.

(** The head of [Z I], applied as a type, gives [Z I] back, as in
    evaluation. *)
Lemma app_truth_teller_head : forall AI U,
  app AI @ ('S2['K1 dup_z,'K1 ('I 'C bz)]) @r U ==> Sm truth_teller.
Proof.
  Local Transparent get_name_test.
  intros AI U; unfold truth_teller.
  Ltac step := first
    [ match goal with
      | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
        apply type_app_stem_structural; intros; discriminate
      | |- app _ @ ?T @r _ ==> _ =>
        tryif is_evar T then fail 1 else first
        [ eapply app_S; [intros; discriminate|
            solve [name_failure]| | |]
        | apply app_K | apply app_I | apply app_stem | apply app_leaf ]
      end ].
  repeat step.
  Unshelve.
  all: repeat step.
  all: try (fold (Z ('I)); apply app_I).
  Local Opaque get_name_test.
Qed.

Lemma truth_teller_untagged : forall E N, truth_teller <> 'tagged[E,N].
Proof. intros E N H; unfold truth_teller, Z in H; discriminate H. Qed.

(** Type application of [Z I] unfolds, through the clause for [S2[G,F]],
    to itself at smaller height, just as its evaluation does. *)
Lemma type_app_truth_teller_evaln_smaller : forall (AI : Decl) n U R,
  evaln n (type_app AI @ truth_teller @r U) R ->
  exists m, m < n /\ evaln m (type_app AI @ truth_teller @r U) R.
Proof.
  intros AI n U R H.
  destruct (app_evaln_head AI n truth_teller U R truth_teller_untagged H)
    as [m [w [Hm [Hw HR]]]].
  exists m; split; [exact Hm|].
  unfold truth_teller, Z in Hw.
  exact (default_S_evaln_any AI (type_app AI)
      ('S2['K1 dup_z,'K1 ('I 'C bz)]) 'I U w m truth_teller U R
      Hw HR (app_truth_teller_head AI U) (app_I AI U)).
Qed.

Lemma type_app_truth_teller_no_value : forall (AI : Decl) U R,
  ~ (type_app AI @ truth_teller @r U ==> R).
Proof.
  intros AI U R H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert R Hn.
  induction n as [n IH] using lt_wf_ind; intros R Hn.
  destruct (type_app_truth_teller_evaln_smaller _ _ _ _ Hn) as [m [Hm Hm']].
  exact (IH m Hm R Hm').
Qed.

(** ** The typing of Z I @ x has no value, whenever x is typed *)

Lemma infer_expression_truth_teller_no_value : forall (AI : Decl) x X R,
  infer AI @ x ==> Sm X ->
  ~ (infer_expression AI @ (truth_teller @ x) ==> R).
Proof.
  intros AI x X R Hx H.
  destruct (infer_expression_fork_gen_inv AI _ _ _ H) as [a [b [Ha [Hb HR]]]].
  apply infer_expression_stem_inv in Ha; apply infer_expression_stem_inv in Hb.
  pose proof (eval_deterministic _ _ Ha _ (truth_teller_self_typed AI)); subst a.
  pose proof (eval_deterministic _ _ Hb _ Hx); subst b.
  apply expression_success2_type_app_any_inv in HR.
  exact (type_app_truth_teller_no_value AI X R HR).
Qed.

(** ** Concrete dither: its typing has no value either

    [cdither] (self_typing.v) negates its own result.  Its type application
    unfolds through the clause for [S2[G,F]] to [cneg 'C cdither], and the
    component [cdither # U] runs again at smaller height. *)

Lemma default_S_evaln_right : forall (AI : Decl) rec G F U w m VG R,
  evaln m (default_body AI @ rec @r ('S2[G,F])) w -> evaln m (w @ U) R ->
  rec @ G @r U ==> Sm VG ->
  exists k R', k <= m /\ evaln k (rec @ F @r U) R'.
Proof.
  intros AI rec G F U w m VG R Hw H HG.
  assert (HT : evaln m (type_app_S @ rec @r G @r F) w).
  { pose proof (default_S_head_inv _ _ _ _ _ (evaln_eval _ _ _ Hw)) as HS.
    clear H.
    Local Transparent default_body.
    unfold default_body in Hw; invert_evaln.
    Local Opaque default_body.
    all: try (exfalso; match goal with
    | H : evaln _ (get_tagged @ Sm _) (Sm _) |- _ =>
      apply evaln_eval in H; destruct (get_tagged_success_inv _ _ H) as [? [? [HT _]]];
      discriminate HT end).
    all: match goal with
    | HS0 : type_app_S @ ?r @r ?g @r ?f ==> ?w0,
      H1 : evaln _ (type_app_S @ ?r) ?t, H2 : evaln _ (?t @ ?g) ?t1,
      H3 : evaln _ (?t1 @ ?f) ?v |- _ =>
      let E := fresh "E" in
      assert (E : w0 = v) by (eapply eval_deterministic; [exact HS0|
        eapply eval_appl; [eapply eval_appl; [exact (evaln_eval _ _ _ H1)|
          exact (evaln_eval _ _ _ H2)]|exact (evaln_eval _ _ _ H3)]]);
      try rewrite E; evaln_close
    end. }
  clear Hw.
  Local Transparent type_app_S.
  unfold type_app_S in HT; cbn in HT.
  invert_evaln.
  all: repeat match goal with
    | Hc : ?r @ ?g @r ?u ==> Sm ?vg,
      H1 : evaln _ (?r @ ?g) ?x, H2 : evaln _ (?x @ ?u) ?a |- _ =>
        let E := fresh "E" in
        assert (E : a = Sm vg) by (eapply eval_deterministic;
          [eapply eval_appl; [exact (evaln_eval _ _ _ H1)|exact (evaln_eval _ _ _ H2)]
          |exact Hc]);
        clear H2; first [discriminate E | injection E; intros; subst]
    end.
  all: match goal with
    | |- exists _ _, _ /\ evaln _ (Fk ?e (Sm ?u0)) _ =>
      match goal with
      | H1 : evaln ?a e ?x, H2 : evaln ?b (Fk (Sm ?x) (Sm u0)) ?r |- _ =>
        exists (S (Nat.max a b)), r; split;
        [ lia | apply (evaln_appl_pred (S (Nat.max a b)) _ _ _ x r);
          [ lia | apply (evaln_lt a _ _ _ H1); cbn; lia | apply (evaln_lt b _ _ _ H2); cbn; lia ] ]
      end
    end.
  Local Opaque type_app_S.
Qed.

Lemma app_cdither_head : forall AI U,
  app AI @ ('S2['K1 dup_z,'K1 (cdither_body 'C bz)]) @r U ==> Sm (cneg 'C cdither).
Proof.
  Local Transparent get_name_test.
  intros AI U; unfold cdither.
  Ltac step2 := first
    [ match goal with
      | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
        apply type_app_stem_structural; intros; discriminate
      | |- app _ @ ?T @r _ ==> _ =>
        tryif is_evar T then fail 1 else first
        [ eapply app_S; [intros; discriminate|
            solve [name_failure]| | |]
        | apply app_K | apply app_I | apply app_stem | apply app_leaf ]
      end ].
  repeat step2.
  Unshelve.
  all: repeat step2.
  Local Opaque get_name_test.
Qed.
Lemma cdither_untagged : forall E N, cdither <> 'tagged[E,N].
Proof. intros E N H; unfold cdither, Z in H; discriminate H. Qed.
Lemma cneg_compose_untagged : forall E N, (cneg 'C cdither) <> 'tagged[E,N].
Proof. intros E N H; cbv [cneg] in H; inversion H. Qed.
Lemma type_app_cdither_evaln_smaller : forall (AI : Decl) n U R,
  evaln n (type_app AI @ cdither @r U) R ->
  exists m R', m < n /\ evaln m (type_app AI @ cdither @r U) R'.
Proof.
  intros AI n U R H.
  destruct (app_evaln_head AI n cdither U R cdither_untagged H) as [m [w [Hm [Hw HR]]]].
  unfold cdither, Z in Hw.
  pose proof (default_S_evaln_any AI (type_app AI)
      ('S2['K1 dup_z,'K1 (cdither_body 'C bz)]) 'I U w m (cneg 'C cdither) U R
      Hw HR (app_cdither_head AI U) (app_I AI U)) as H1.
  destruct (app_evaln_head AI m (cneg 'C cdither) U R cneg_compose_untagged H1) as [m2 [w2 [Hm2 [Hw2 HR2]]]].
  destruct (default_S_evaln_right AI (type_app AI) ('K1 cneg) cdither U w2 m2 cneg R Hw2 HR2
      ltac:(apply app_K)) as [k [R' [Hk H3]]].
  exists k, R'; split; [lia|exact H3].
Qed.
Lemma type_app_cdither_no_value : forall (AI : Decl) U R,
  ~ (type_app AI @ cdither @r U ==> R).
Proof.
  intros AI U R H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert R Hn.
  induction n as [n IH] using lt_wf_ind; intros R Hn.
  destruct (type_app_cdither_evaln_smaller _ _ _ _ Hn) as [m [R' [Hm Hm']]].
  exact (IH m Hm R' Hm').
Qed.
Lemma cdither_self_typed : forall AI, infer AI @ cdither ==> Sm cdither.
Proof. intros; apply concrete_is_self_typed, cdither_concrete. Qed.
Theorem infer_expression_cdither_no_value : forall (AI : Decl) x X R,
  infer AI @ x ==> Sm X ->
  ~ (infer_expression AI @ (cdither @ x) ==> R).
Proof.
  intros AI x X R Hx H.
  destruct (infer_expression_fork_gen_inv AI _ _ _ H) as [a [b [Ha [Hb HR]]]].
  apply infer_expression_stem_inv in Ha; apply infer_expression_stem_inv in Hb.
  pose proof (eval_deterministic _ _ Ha _ (cdither_self_typed AI)); subst a.
  pose proof (eval_deterministic _ _ Hb _ Hx); subst b.
  apply expression_success2_type_app_any_inv in HR.
  exact (type_app_cdither_no_value AI X R HR).
Qed.

(** ** Plain [Z] dither on [Bool]

    Forgetting alone does not help: with the abstract booleans, the program
    [zdither] has a type, but that type is as recursive as the program, so
    type application at any argument has no result. *)

From Stdlib Require Import String.
From TreeTyping Require Import data_types.
Local Open Scope string_scope.
Definition zdither_body := Eval cbn in to_tree (star "r" (Val neg ''C Ref "r")).
Definition zdither := Z zdither_body.
Definition zdither_type_body := Eval cbn in to_tree (star "r" (Val Neg ''C Ref "r")).
Definition zdither_type := Z zdither_type_body.
Lemma neg_step : zdither_body @ zdither ==> neg 'C zdither.
Proof. unfold zdither_body; cbn; d_eval. Qed.
Lemma zdither_no_value : forall x v, ~ (zdither @ x ==> v).
Proof.
  intros x v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  unfold zdither at 1 in Hn.
  destruct (Z_evaln_unfold_inv _ _ _ _ Hn) as [m2 [w [Hm2 [Hw H2]]]].
  pose proof (eval_deterministic _ _ Hw _ neg_step) as Heq; subst w.
  destruct (compose_evaln_inv _ _ _ _ _ H2) as [m3 [w [Hm3 H3]]].
  exact (IH m3 ltac:(lia) w H3).
Qed.

Lemma app_zdither_type_head : forall AI U,
  app AI @ ('S2['K1 dup_z,'K1 (zdither_type_body 'C bz)]) @r U ==> Sm (Neg 'C zdither_type).
Proof.
  Local Transparent get_name_test.
  intros AI U; unfold zdither_type.
  repeat step2.
  Unshelve.
  all: repeat step2.
  Local Opaque get_name_test.
Qed.
Lemma zdither_type_untagged : forall E N, zdither_type <> 'tagged[E,N].
Proof. intros E N H; unfold zdither_type, Z in H; discriminate H. Qed.
Lemma Neg_compose_untagged : forall E N, (Neg 'C zdither_type) <> 'tagged[E,N].
Proof. intros E N H; cbv [Neg] in H; inversion H. Qed.
Lemma type_app_zdither_evaln_smaller : forall (AI : Decl) n U R,
  evaln n (type_app AI @ zdither_type @r U) R ->
  exists m R', m < n /\ evaln m (type_app AI @ zdither_type @r U) R'.
Proof.
  intros AI n U R H.
  destruct (app_evaln_head AI n zdither_type U R zdither_type_untagged H) as [m [w [Hm [Hw HR]]]].
  unfold zdither_type, Z in Hw.
  pose proof (default_S_evaln_any AI (type_app AI)
      ('S2['K1 dup_z,'K1 (zdither_type_body 'C bz)]) 'I U w m (Neg 'C zdither_type) U R
      Hw HR (app_zdither_type_head AI U) (app_I AI U)) as H1.
  destruct (app_evaln_head AI m (Neg 'C zdither_type) U R Neg_compose_untagged H1) as [m2 [w2 [Hm2 [Hw2 HR2]]]].
  destruct (default_S_evaln_right AI (type_app AI) ('K1 Neg) zdither_type U w2 m2 Neg R Hw2 HR2
      ltac:(apply app_K)) as [k [R' [Hk H3]]].
  exists k, R'; split; [lia|exact H3].
Qed.
Theorem type_app_zdither_no_value : forall (AI : Decl) U R,
  ~ (type_app AI @ zdither_type @r U ==> R).
Proof.
  intros AI U R H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert R Hn.
  induction n as [n IH] using lt_wf_ind; intros R Hn.
  destruct (type_app_zdither_evaln_smaller _ _ _ _ Hn) as [m [R' [Hm Hm']]].
  exact (IH m Hm R' Hm').
Qed.

(** [zdither] has the type whose application has no result, for every
    ontology that supports booleans. *)
Lemma zdither_typed : forall AI : Combination,
  supports_booleans AI -> infer AI @ zdither ==> Sm zdither_type.
Proof.
  intros AI HB; pose proof (neg_infer AI HB) as Hn.
  unfold zdither, zdither_type; apply infer_Z.
  unfold zdither_body, zdither_type_body; infer_tac.
Qed.

From TreeTyping Require Import paper_ontology.

(** ** Type application of [infer] at an abstract type

    [infer] inspects its argument by triage, which type application refuses
    at an abstract type. *)
Lemma type_app_infer_Bool :
  type_app paper_ontology @ infer paper_ontology @r 'Bool ==> Lf.
Proof. apply (eval_bounded_sound 300000); vm_compute; reflexivity. Qed.

