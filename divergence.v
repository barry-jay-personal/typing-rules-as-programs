(** * Step 82, stage 3: concrete recursion need not terminate in typing.

    [cdither = Z[\r. cneg o r]] is concrete, so [cdither : cdither], but
    [cdither @ x] has no value ([cdither_no_value]), and when [x] has a
    type, the typing of [cdither @ x] has no value either
    ([infer_expression_cdither_no_value]).  The proof is by induction on
    the height of the type application: [cdither # X] needs
    [cdither # X] again at a smaller height. *)

From Stdlib Require Import String Arith Lia.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates self_typing.
Open Scope string_scope.
Set Default Proof Using "Type".

Definition cneg := Eval cbn in to_tree (star "b" (Ref "b" @@ Val 'KI @@ Val 'K)).
Definition cdither_body := Eval cbn in to_tree (star "r" (Val cneg ''C Ref "r")).
Definition cdither := Z cdither_body.

Lemma cdither_concrete : concrete cdither.
Proof. apply Z_preserves_concrete; apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma cdither_self_typed : forall O, infer O @ cdither ==> Sm cdither.
Proof. intros; apply concrete_is_self_typed, concreteb_spec, cdither_concrete. Qed.

Lemma Z_evaln_unfold_inv : forall n f x v, evaln n (Z f @ x) v ->
  exists m w, m < n /\ f @ Z f ==> w /\ evaln m (w @ x) v.
Proof.
  intros n f x v H; unfold Z, self_apply, wait1 in H; crunchn.
  match goal with H : evaln ?m (?w @ _) v, H' : _ ==> ?w |- _ =>
    exists m, w; split; [lia|split; [exact H'|exact H]] end.
Qed.

Lemma compose_evaln_inv : forall n g f x v,
  evaln n ((g 'C f) @ x) v -> exists m w, m < n /\ evaln m (f @ x) w.
Proof.
  intros n g f x v H; crunchn.
  match goal with H : evaln ?m (f @ x) ?w |- _ => exists m, w; split; [lia|exact H] end.
Qed.

Lemma cdither_step : cdither_body @ cdither ==> cneg 'C cdither.
Proof. unfold cdither_body; cbn; evaluate. Qed.

Theorem cdither_no_value : forall x v, ~ (cdither @ x ==> v).
Proof.
  intros x v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  unfold cdither at 1 in Hn.
  destruct (Z_evaln_unfold_inv _ _ _ _ Hn) as [m2 [w [Hm2 [Hw H2]]]].
  pose proof (eval_deterministic _ _ Hw _ cdither_step) as Heq; subst w.
  destruct (compose_evaln_inv _ _ _ _ _ H2) as [m3 [w [Hm3 H3]]].
  exact (IH m3 ltac:(lia) w H3).
Qed.

(** ** Height-aware inversion of the S2 clause *)

Section S2Height.
Variable O : Combination.
Local Opaque get_label resv label_tst elim_of guard_of isK is_concrete get_tagged
  leaf_cl stem_cl tri_cl abs_cl tp.

Lemma s_cl_h : forall rec G H p U R k, s_cl @ rec @r G @r H ==> p -> evaln k (p @ U) (Sm R) ->
  exists pG pH V W q j1 j2 j3, rec @ G ==> pG /\ evaln j1 (pG @ U) (Sm V) /\
    rec @ H ==> pH /\ evaln j2 (pH @ U) (Sm W) /\ rec @ V ==> q /\ evaln j3 (q @ W) (Sm R) /\
    j1 < k /\ j2 < k /\ j3 < k.
Proof.
  intros rec G H p U R k H1 H2; unfold s_cl in H1; crunch; crunchn; finl.
Qed.

Ltac finl2 := match goal with
 | |- _ \/ _ => first [left; finl2 | right; finl2]
 | |- exists _, _ => eexists; finl2
 | |- _ /\ _ => split; finl2
 | |- forall _, _ => let EV := fresh in let EW := fresh in intros ? ? EV EW;
                     inversion EV; inversion EW; subst; finl2
 | |- _ => solve [reflexivity | eassumption | lia | auto ]
end.

Lemma s_cl_h_any : forall rec G H p U v k, s_cl @ rec @r G @r H ==> p -> evaln k (p @ U) v ->
  exists pG pH a b j1 j2, rec @ G ==> pG /\ evaln j1 (pG @ U) a /\
    rec @ H ==> pH /\ evaln j2 (pH @ U) b /\ j1 < k /\ j2 < k /\
    (forall V W, a = Sm V -> b = Sm W -> exists q j3, rec @ V ==> q /\ evaln j3 (q @ W) v /\ j3 < k).
Proof.
  intros rec G H p U v k H1 H2; unfold s_cl in H1; crunch; crunchn; finl2.
Qed.

Local Transparent tp.
Lemma tp_partial_S2 : forall G H p, label_of ('S2[G,H]) = None ->
  tp O @ 'S2[G,H] ==> p -> s_cl @ tp O @r G @r H ==> p.
Proof.
  intros G H p HL Hp; unfold tp in Hp; apply Z_unfold_inv in Hp; fold (tp O) in Hp.
  destruct (tp_body_inv O _ _ _ Hp) as [[_ Ho]|[n [E _]]]; [|rewrite E in HL; discriminate].
  Local Transparent ord_cl fk_cl. unfold ord_cl in Ho.
  destruct (resv_spec (Sm G)) as [r [Hr [_ Hiff]]]; specialize (Hiff eq_refl); subst r.
  crunch. unfold fk_cl in *. crunch. fin.
Qed.
Local Opaque tp ord_cl fk_cl.

(** [tp] at an S2 type, by the height of the application of its partial value. *)
Lemma tp_S2_h : forall G H p U R k, label_of ('S2[G,H]) = None ->
  tp O @ 'S2[G,H] ==> p -> evaln k (p @ U) (Sm R) ->
  exists pG pH V W q j1 j2 j3, tp O @ G ==> pG /\ evaln j1 (pG @ U) (Sm V) /\
    tp O @ H ==> pH /\ evaln j2 (pH @ U) (Sm W) /\ tp O @ V ==> q /\ evaln j3 (q @ W) (Sm R) /\
    j1 < k /\ j2 < k /\ j3 < k.
Proof. intros G H p U R k HL Hp Hk; apply (s_cl_h (tp O) G H p); [apply tp_partial_S2|]; assumption. Qed.

Lemma tp_S2_h_any : forall G H p U v k, label_of ('S2[G,H]) = None ->
  tp O @ 'S2[G,H] ==> p -> evaln k (p @ U) v ->
  exists pG pH a b j1 j2, tp O @ G ==> pG /\ evaln j1 (pG @ U) a /\
    tp O @ H ==> pH /\ evaln j2 (pH @ U) b /\ j1 < k /\ j2 < k /\
    (forall V W, a = Sm V -> b = Sm W -> exists q j3, tp O @ V ==> q /\ evaln j3 (q @ W) v /\ j3 < k).
Proof. intros G H p U v k HL Hp Hk; apply (s_cl_h_any (tp O) G H p); [apply tp_partial_S2|]; assumption. Qed.
End S2Height.

(** ** The typing of cdither does not terminate *)

Definition cd_w : Combination := cdither_body 'C bz.
Lemma cdither_S2 : cdither = 'S2['S2['K1 self_apply, 'K1 cd_w], 'I].
Proof. reflexivity. Qed.

Section CditherTyping.
Variable O : Combination.

Ltac tpf := repeat first
  [ eassumption
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [reflexivity| | |])
  | (apply tp_stem; reflexivity)
  | apply tp_leaf_fwd ].

Lemma cd_G_fwd : forall X, tp O @ 'S2['K1 self_apply, 'K1 cd_w] @r X ==> Sm (cneg 'C cdither).
Proof. intros X; unfold cd_w, cdither, Z, cdither_body, cneg, self_apply, wait1; cbn; tpf. Qed.

Theorem tp_cdither_no_value : forall X v, ~ (tp O @ cdither @r X ==> v).
Proof.
  intros X v H. destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (eval_evaln _ _ Hq) as [k Hk]; clear Hq.
  revert v Hk. induction k as [k IH] using lt_wf_ind. intros v Hk.
  pose proof Hp as Hp0. rewrite cdither_S2 in Hp.
  destruct (tp_S2_h_any O ('S2['K1 self_apply, 'K1 cd_w]) 'I p X v k eq_refl Hp Hk)
    as [pG [pH [a [b [j1 [j2 [HpG [Ha [HpH [Hb [Hj1 [Hj2 Hcont]]]]]]]]]]]].
  assert (Ea : a = Sm (cneg 'C cdither)).
  { pose proof (eval_appl _ _ _ _ _ HpG (evaln_eval _ _ _ Ha)) as E.
    exact (eval_deterministic _ _ E _ (cd_G_fwd X)). }
  assert (Eb : b = Sm X).
  { pose proof (eval_appl _ _ _ _ _ HpH (evaln_eval _ _ _ Hb)) as E.
    exact (eval_deterministic _ _ E _ (app_I O X)). }
  destruct (Hcont _ _ Ea Eb) as [q [j3 [Hq3 [Hq3e Hj3]]]].
  destruct (tp_S2_h_any O ('K1 cneg) cdither q X v j3 eq_refl Hq3 Hq3e)
    as [pG' [pH' [a' [b' [j1' [j2' [_ [_ [HpH' [Hb' [_ [Hj2' _]]]]]]]]]]]].
  pose proof (eval_deterministic _ _ HpH' _ Hp0) as ->.
  exact (IH j2' ltac:(lia) b' Hb').
Qed.
End CditherTyping.

(** If [x] has a type then the typing of [cdither @ x] has no value. *)
Theorem infer_expression_cdither_no_value : forall O x X v, infer O @ x ==> Sm X ->
  ~ (infer_expression O @ (cdither @ x) ==> v).
Proof.
  intros O x X v Hx H.
  Local Transparent infer_expression.
  unfold infer_expression in H; apply Z_unfold_inv in H; fold (infer_expression O) in H.
  unfold ie_body in H.
  pose proof (ie_stem O _ _ (cdither_self_typed O)) as H1.
  pose proof (ie_stem O _ _ Hx) as H2.
  unfold infer_expression in H1, H2.
  crunch.
  match goal with H7 : tp O @ cdither ==> ?p, H9 : ?p @ ?X ==> ?w |- _ =>
    exact (tp_cdither_no_value O X w (eval_appl _ _ _ _ _ H7 H9)) end.
Qed.



