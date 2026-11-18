(** * Step 82, stage 5, part 1: dither, zdither, equality.

    [dither = rec_query[Bool, dither_body, Kq[Bool, tt]]] with
    [dither_body @ r = Sq[Bool, Kq[neg], r]] (built through [mk_query]):
    it negates its own result.  [dither : Query[Bool]], so
    [dither @ tt :: Bool], yet [dither @ tt] has no value.

    [zdither = Z[\r. neg o r]] has the type [zdither_type = Z[\r. Neg o r]]
    and [zdither_type # U] has no value, for every ontology and every U.

    [typed_equal = rec_query[Query[Bool], eq_body]] compares two trees
    one level at a time by triage queries. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing divergence size_queries.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

Ltac by_runD := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** dither *)

Definition NegT : Combination := Eval vm_compute in ty_of neg.
Definition kq_neg : Combination := Kq NegT neg.
Definition dither_body : Combination := Eval cbn -[mk_query kq_neg] in to_tree
  (star "r" (op (mk_query Bool) @@ S2t (Val kq_neg) (Ref "r"))).
(** The seed is the constant query [Kq[Bool, tt]]; it is never applied. *)
Definition dither_seed : Combination := Kq Bool tt.
Definition dither : Combination := rec_query Bool dither_body dither_seed.
Definition DitherBodyT : Combination := Eval vm_compute in ty_of dither_body.

Lemma infer_dither_body : infer PO @ dither_body ==> Sm DitherBodyT. Proof. by_runD. Qed.
Lemma dither_body_type_app : tp PO @ DitherBodyT @r Query Bool ==> Sm (Query Bool). Proof. by_runD. Qed.

Theorem infer_dither : infer PO @ dither ==> Sm (Query Bool).
Proof.
  eapply rec_query_generic; [exact PO_query|exact PO_mkq|exact PO_update|exact PO_mku
    |exact infer_dither_body|exact dither_body_type_app|by_runD].
Qed.

Theorem dither_tt_infer_expression : infer_expression PO @ (dither @ tt) ==> Sm Bool.
Proof.
  eapply generic_query_application; [exact PO_query|exact infer_dither|].
  by_runD.
Qed.

Definition dither_step : Combination := Eval vm_compute in
  match runp 40 (dither_body @ dither) with Some v => v | None => Lf end.
Lemma dither_body_eval : dither_body @ dither ==> dither_step. Proof. by_runD. Qed.
Lemma dither_step_shape : dither_step = 'tagged['S2[kq_neg, dither], query_tag (code Bool)].
Proof. vm_compute; reflexivity. Qed.

(** The recursive call: the inner query of [dither] gives [dither_step] at every argument. *)
Lemma dither_inner : forall x,
  Sq (Query Bool) (Kq Update (rq_fix Bool dither_body)) (Kq (Query Bool) dither_seed) @ x ==> dither_step.
Proof.
  intros x; unfold Sq at 1; apply tagged_eval. eapply S2_fwd; [apply Kq_fwd|apply Kq_fwd|].
  apply (rq_fix_at_seed Bool dither_body ('K1 tt)), dither_body_eval.
Qed.

Theorem dither_no_value : forall x v, ~ (dither @ x ==> v).
Proof.
  intros x v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  unfold dither at 1, rec_query, Dq in Hn. unfold Sq at 1 in Hn.
  destruct (evaln_tagged_inv _ _ _ _ _ Hn) as [j0 [Hj0 H0]].
  destruct (evaln_S2_inv _ _ _ _ _ H0) as [j1 [p1 [p2 [Hj1 [H1a [H1b H1c]]]]]].
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1a) _ (dither_inner x)) as Ep1.
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1b) _ (I_eval x)) as Ep2.
  rewrite dither_step_shape in Ep1; subst p1 p2.
  destruct (evaln_tagged_inv _ _ _ _ _ H1c) as [j3 [Hj3 H3]].
  destruct (evaln_S2_inv _ _ _ _ _ H3) as [j4 [p1 [p2 [Hj4 [H4a [H4b H4c]]]]]].
  exact (IH j4 ltac:(lia) p2 H4b).
Qed.

Theorem dither_typed_no_value : infer_expression PO @ (dither @ tt) ==> Sm Bool /\ forall v, ~ (dither @ tt ==> v).
Proof. split; [exact dither_tt_infer_expression|intros v; apply dither_no_value]. Qed.

(** ** zdither *)

Definition zd_body : Combination := Eval cbn -[neg] in to_tree (star "r" (op neg ''C Ref "r")).
Definition zdither : Combination := Z zd_body.
Definition zdt_body : Combination := Eval cbn -[NegT] in to_tree (star "r" (op NegT ''C Ref "r")).
Definition zdither_type : Combination := Z zdt_body.

Theorem zdither_typed : infer PO @ zdither ==> Sm zdither_type. Proof. by_runD. Qed.

Definition zd_w : Combination := zdt_body 'C bz.
Lemma zdither_S2 : zdither_type = 'S2['S2['K1 self_apply, 'K1 zd_w], 'I].
Proof. reflexivity. Qed.

Section ZditherTyping.
Variable O : Combination.
Ltac tpf := repeat first
  [ eassumption
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [reflexivity| | |])
  | (apply tp_stem; reflexivity)
  | apply tp_leaf_fwd ].

Lemma zd_G_fwd : forall X, tp O @ 'S2['K1 self_apply, 'K1 zd_w] @r X ==> Sm (('I 'C NegT) 'C zdither_type).
Proof. intros X; unfold zd_w, zdither_type, Z, zdt_body, self_apply, wait1; cbn -[NegT]; tpf. Qed.

Theorem type_app_zdither_no_value : forall X v, ~ (tp O @ zdither_type @r X ==> v).
Proof.
  intros X v H. destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (eval_evaln _ _ Hq) as [k Hk]; clear Hq.
  revert v Hk. induction k as [k IH] using lt_wf_ind. intros v Hk.
  pose proof Hp as Hp0. rewrite zdither_S2 in Hp.
  destruct (tp_S2_h_any O ('S2['K1 self_apply, 'K1 zd_w]) 'I p X v k eq_refl Hp Hk)
    as [pG [pH [a [b [j1 [j2 [HpG [Ha [HpH [Hb [Hj1 [Hj2 Hcont]]]]]]]]]]]].
  assert (Ea : a = Sm (('I 'C NegT) 'C zdither_type)).
  { pose proof (eval_appl _ _ _ _ _ HpG (evaln_eval _ _ _ Ha)) as E.
    exact (eval_deterministic _ _ E _ (zd_G_fwd X)). }
  assert (Eb : b = Sm X).
  { pose proof (eval_appl _ _ _ _ _ HpH (evaln_eval _ _ _ Hb)) as E.
    exact (eval_deterministic _ _ E _ (app_I O X)). }
  destruct (Hcont _ _ Ea Eb) as [q [j3 [Hq3 [Hq3e Hj3]]]].
  destruct (tp_S2_h_any O ('K1 ('I 'C NegT)) zdither_type q X v j3 eq_refl Hq3 Hq3e)
    as [pG' [pH' [a' [b' [j1' [j2' [_ [_ [HpH' [Hb' [_ [Hj2' _]]]]]]]]]]]].
  pose proof (eval_deterministic _ _ HpH' _ Hp0) as ->.
  exact (IH j2' ltac:(lia) b' Hb').
Qed.
End ZditherTyping.
