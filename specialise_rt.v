(** * Step 82, stage 7, part 3: specialising equality.

    The walk [specialise_equal] (ported unchanged from src_type36's
    specialise_equal.v) replaces each tester [wait[equal,c]] by the value
    [equal1 c] of [equal @ c], except when [c] is a stem.  On the new design:
    - it is concrete, so self-typed;
    - at the type level [equal # c ==> Sm (equal1 c)] for concrete [c]
      ([app_equal]), so a tester and its specialisation apply alike at
      every argument type ([app_tester]);
    - so typing is preserved when the walk replaces only heads of [e]. *)

From Stdlib Require Import String List Bool Lia PeanoNat.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology poly optimisation_rt specialise_check.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Notation PO := paper_ontology.
Definition ceqb (p q : Combination) : bool := if combination_eq_dec p q then true else false.
Lemma ceqb_refl : forall p, ceqb p p = true.
Proof. intros p; unfold ceqb; destruct (combination_eq_dec p p); [reflexivity|contradiction]. Qed.
Lemma ceqb_true : forall p q, ceqb p q = true -> p = q.
Proof. intros p q; unfold ceqb; destruct (combination_eq_dec p q); [auto|discriminate]. Qed.

(** ** The walk *)

(** [site] and [specialise_fn] are those of specialise_check.v. *)

Definition is_stem : Combination := 'triage['KI, 'K1 'K, 'K1 ('K1 'KI)].

Definition specialise_body : Combination := Eval cbn in to_tree
    (\"rec" (\"t"
       ((\"e"
         ((''triage [
            ''triage [
              Val Lf,
              \"u" (Val Lf @@ (Ref "rec" @@ Ref "u")),
              \"a" (\"b" (Val Lf @@ (Ref "rec" @@ Ref "a") @@ (Ref "rec" @@ Ref "b")))],
            \"c" (\"x" (Val is_stem @@ Ref "c" @@ Ref "x" @@ (Ref "e" @@ Ref "c"))),
            Val Lf ]
           @@ ((''triage [
                 Val Lf,
                 ''triage [
                   Val Lf,
                   Val Lf,
                   \"M" (\"c" (Ref "e" @@ Ref "M" @@ Ref "e" @@ (Val Lf @@ Ref "c") @@ Val Lf))],
                 Val Lf ])
               @@ (Val get_wait @@ Ref "t")))
          @@ Ref "t"))
        @@ Val equal))).
Definition specialise_equal : Combination := Z specialise_body.

Lemma site_wait : forall c, site ('wait[equal,c]) = Some c.
Proof.
  intro c; cbn [site].
  destruct (combination_eq_dec equal equal); [|contradiction].
  destruct (combination_eq_dec 'I 'I); [|contradiction]; reflexivity.
Qed.

Lemma site_some : forall t c, site t = Some c -> t = 'wait[equal,c].
Proof.
  intros t c H; unfold site in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => is_var x; destruct x
         end; try discriminate.
  destruct (combination_eq_dec _ equal) as [E1|]; [|cbn in H; discriminate].
  destruct (combination_eq_dec _ ('I)) as [E2|]; [|cbn in H; discriminate].
  subst; cbn in H; inversion H; reflexivity.
Qed.

Lemma site_none : forall t, (forall c, t <> 'wait[equal,c]) -> site t = None.
Proof.
  intros t H; destruct (site t) as [c|] eqn:E; [|reflexivity].
  exfalso; eapply H; apply site_some; exact E.
Qed.

Lemma specialise_fn_site_none : forall t, site t = None ->
  specialise_fn t = match t with Lf => Lf | Sm u => Sm (specialise_fn u) | Fk u v => Fk (specialise_fn u) (specialise_fn v) end.
Proof. intros t H; destruct t; cbn [specialise_fn]; rewrite ?H; reflexivity. Qed.

Lemma specialise_fn_wait : forall c,
  specialise_fn ('wait[equal,c]) = match c with Sm _ => 'wait[equal,c] | _ => equal1 c end.
Proof.
  intro c; unfold specialise_fn; cbn beta iota zeta delta -[site]; fold specialise_fn.
  rewrite site_wait; destruct c; reflexivity.
Qed.

Local Opaque get_wait equal equal1.

Local Ltac body_run :=
  unfold specialise_equal; eapply Z_unfold;
  cbv -[get_wait equal equal1 Z specialise_body]; unfold specialise_body at 1;
  cbv -[get_wait equal equal1 Z specialise_body]; evaluate.

Lemma specialise_equal_eval : forall t, specialise_equal @ t ==> specialise_fn t.
Proof.
  induction t as [|u IH|u IHu v IHv].
  - pose proof (get_wait_none Lf ltac:(intros M N H; discriminate)) as Hg. body_run.
  - pose proof (get_wait_none (Sm u) ltac:(intros M N H; discriminate)) as Hg. body_run.
  - destruct (wait_decide (Fk u v)) as [[M [N HE]]|Hno].
    + pose proof (get_wait_some M N) as Hg; rewrite <- HE in Hg.
      pose proof (equal_eval M) as He.
      destruct (combination_eq_dec M equal) as [->|Hne].
      * pose proof (equal1_eq equal) as Hk.
        pose proof (equal_eval N) as HN.
        rewrite HE, specialise_fn_wait; rewrite <- HE.
        destruct N as [|n|a b]; body_run.
      * pose proof (equal1_neq M equal Hne) as Hk.
        rewrite specialise_fn_site_none.
        -- body_run.
        -- destruct (site (Fk u v)) as [c|] eqn:Es; [|reflexivity].
           apply site_some in Es; rewrite HE in Es; inversion Es; congruence.
    + pose proof (get_wait_none _ Hno) as Hg.
      rewrite specialise_fn_site_none by (apply site_none; intro; apply Hno).
      body_run.
Qed.

Lemma specialise_equal_concrete : concreteb specialise_equal = true.
Proof. Local Transparent equal get_wait. vm_compute; reflexivity. Qed.
Local Opaque equal get_wait.

(** ** The tester: [tester_agrees] is in specialise_check.v. *)

Local Transparent equal1.
Lemma equal1_shape : forall c, exists a b d, equal1 c = Fk (Fk a b) d.
Proof. intros [|c|a b]; cbn; eauto. Qed.

Lemma equal1_concrete : forall c, concreteb (equal1 c) = true.
Proof.
  induction c as [|c IH|a IHa b IHb]; [reflexivity|..].
  - cbn [equal1]; destruct (equal1_shape c) as [p [q [r E]]]; cbn; rewrite ?E in *;
    cbn in *; rewrite ?IH; reflexivity.
  - cbn [equal1]; destruct (equal1_shape a) as [p [q [r E]]]; cbn; rewrite ?E in *;
    cbn in *; rewrite ?IHa, ?IHb; cbn; try reflexivity.
Qed.
Local Opaque equal1.

(** ** Type application on concrete programs *)

Section TpConcrete.
Variable O : Combination.
Local Opaque get_label resv label_tst elim_of.

Lemma reserved_concrete : forall X, concreteb X = true -> reservedb X = false.
Proof.
  intros X H; unfold reservedb.
  destruct (tag_of X) as [[f n]|] eqn:Et.
  - apply tag_of_some in Et; subst X; cbn in H; rewrite Bool.andb_false_r in H; discriminate.
  - destruct (label_of X) as [n|] eqn:El; [|reflexivity].
    apply label_of_some in El; subst X; discriminate.
Qed.

Lemma label_of_concrete : forall X, concreteb X = true -> label_of X = None.
Proof.
  intros X H; destruct (label_of X) as [n|] eqn:El; [|reflexivity].
  apply label_of_some in El; subst X; discriminate.
Qed.

Lemma fk_tri : forall rec F0 F1 Y q, reservedb (Fk F0 F1) = false ->
  tri_cl @ rec @r F0 @r F1 @r Y ==> q -> fk_cl @ rec @r Fk F0 F1 @r Y ==> q.
Proof.
  intros rec F0 F1 Y q HR H; destruct (s_partial rec) as [a Ha]; destruct (tri_partial rec) as [b Hb].
  destruct (resv_spec (Fk F0 F1)) as [r [Hr [_ Hiff]]]; specialize (Hiff HR); subst r.
  unfold fk_cl; ev3.
Qed.

Lemma tri_cl_partial : forall rec F0 F1 F2 p1 p2, rec @ F1 ==> p1 -> rec @ F2 ==> p2 ->
  exists q, tri_cl @ rec @r F0 @r F1 @r F2 ==> q.
Proof. intros; unfold tri_cl; eexists; ev2. Qed.

Lemma tri_fwd_leaf : forall rec F0 F1 F2 p1 p2, rec @ F1 ==> p1 -> rec @ F2 ==> p2 ->
  tri_cl @ rec @r F0 @r F1 @r F2 @r Lf ==> Sm F0.
Proof.
  intros; pose proof (get_label_spec Lf) as Hg; cbn in Hg. unfold tri_cl; ev2.
Qed.

Lemma tri_fwd_stem : forall rec F0 F1 F2 X v p2, rec @ F1 @r X ==> v -> rec @ F2 ==> p2 ->
  tri_cl @ rec @r F0 @r F1 @r F2 @r Sm X ==> v.
Proof.
  intros rec F0 F1 F2 X v p2 H1 H2; destruct (app2_inv _ _ _ _ H1) as [p1 [Hp1 Hq1]].
  pose proof (get_label_spec (Sm X)) as Hg; cbn in Hg. unfold tri_cl; ev2.
Qed.

Lemma tri_fwd_fork : forall rec F0 F1 F2 X Y G v p1, label_of (Fk X Y) = None ->
  rec @ F1 ==> p1 -> rec @ F2 @r X ==> Sm G -> rec @ G @r Y ==> v ->
  tri_cl @ rec @r F0 @r F1 @r F2 @r Fk X Y ==> v.
Proof.
  intros rec F0 F1 F2 X Y G v p1 HL H1 H2 H3.
  destruct (app2_inv _ _ _ _ H2) as [p2 [Hp2 Hq2]].
  pose proof (get_label_spec (Fk X Y)) as Hg; rewrite HL in Hg; cbn in Hg. unfold tri_cl; ev2.
Qed.

Lemma ord_leaf : ord_cl @ tp O @r Lf ==> leaf_cl.
Proof. unfold ord_cl. destruct (fk_partial (tp O)) as [p Hp]. ev2. Qed.

Lemma stem_cl_partial : forall G, exists p, stem_cl @ G ==> p.
Proof.
  intros G; destruct (app2_inv _ _ _ _ (label_tst_spec G Lf)) as [a [Ha _]].
  unfold stem_cl; eexists; ev2.
Qed.

Lemma s_cl_partial3 : forall rec G H p1 p2, rec @ G ==> p1 -> rec @ H ==> p2 -> exists q, s_cl @ rec @r G @r H ==> q.
Proof. intros; unfold s_cl; eexists; ev2. Qed.

Lemma tp_partial_concrete : forall F, concreteb F = true -> exists p, tp O @ F ==> p.
Proof.
  assert (H : forall k F, tree_size F < k -> concreteb F = true -> exists p, tp O @ F ==> p).
  { induction k as [|k IH]; intros F Hk Hc; [lia|].
    destruct F as [|G|X Y].
    - eexists; apply tp_head_ord; [reflexivity|apply ord_leaf].
    - destruct (stem_cl_partial G) as [p Hp]; exists p; apply tp_stem_head, Hp.
    - destruct (concrete_Fk _ _ Hc) as [_ [HX HY]].
      destruct (IH Y ltac:(cbn in Hk; lia) HY) as [pY HpY].
      destruct X as [|G|F0 F1].
      + eexists; apply tp_head_ord; [reflexivity|apply ord_fork, fk_K1].
      + destruct (IH G ltac:(cbn in Hk; lia) HX) as [pG HpG].
        destruct (s_cl_partial3 (tp O) G Y pG pY HpG HpY) as [q Hq].
        exists q; apply tp_head_ord; [apply label_of_concrete, Hc|apply ord_fork, fk_S2, Hq].
      + destruct (concrete_Fk _ _ HX) as [_ [_ H1]].
        destruct (IH F1 ltac:(cbn in Hk; lia) H1) as [p1 Hp1].
        destruct (tri_cl_partial (tp O) F0 F1 Y p1 pY Hp1 HpY) as [q Hq].
        exists q; apply tp_head_ord; [apply label_of_concrete, Hc|].
        apply ord_fork, fk_tri; [apply reserved_concrete, HX|exact Hq]. }
  intros F; apply (H (S (tree_size F))); lia.
Qed.

Theorem tp_tri_leaf : forall F0 F1 F2, concreteb (Fk F0 F1) = true -> concreteb F2 = true ->
  tp O @ 'triage[F0,F1,F2] @r Lf ==> Sm F0.
Proof.
  intros F0 F1 F2 H01 H2.
  destruct (concrete_Fk _ _ H01) as [_ [_ H1]].
  destruct (tp_partial_concrete F1 H1) as [p1 Hp1]; destruct (tp_partial_concrete F2 H2) as [p2 Hp2].
  destruct (appl_inv _ _ _ _ (tri_fwd_leaf (tp O) F0 F1 F2 p1 p2 Hp1 Hp2)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [reflexivity|apply ord_fork, fk_tri; [apply reserved_concrete, H01|exact Hq]]|exact Hq'].
Qed.

Theorem tp_tri_stem : forall F0 F1 F2 X v, concreteb (Fk F0 F1) = true -> concreteb F2 = true ->
  tp O @ F1 @r X ==> v -> tp O @ 'triage[F0,F1,F2] @r Sm X ==> v.
Proof.
  intros F0 F1 F2 X v H01 H2 H.
  destruct (tp_partial_concrete F2 H2) as [p2 Hp2].
  destruct (appl_inv _ _ _ _ (tri_fwd_stem (tp O) F0 F1 F2 X v p2 H Hp2)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [reflexivity|apply ord_fork, fk_tri; [apply reserved_concrete, H01|exact Hq]]|exact Hq'].
Qed.

Theorem tp_tri_fork : forall F0 F1 F2 X Y G v, concreteb (Fk F0 F1) = true -> label_of (Fk X Y) = None ->
  tp O @ F2 @r X ==> Sm G -> tp O @ G @r Y ==> v -> tp O @ 'triage[F0,F1,F2] @r Fk X Y ==> v.
Proof.
  intros F0 F1 F2 X Y G v H01 HL H2 H3.
  destruct (concrete_Fk _ _ H01) as [_ [_ H1]].
  destruct (tp_partial_concrete F1 H1) as [p1 Hp1].
  destruct (appl_inv _ _ _ _ (tri_fwd_fork (tp O) F0 F1 F2 X Y G v p1 HL Hp1 H2 H3)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [reflexivity|apply ord_fork, fk_tri; [apply reserved_concrete, H01|exact Hq]]|exact Hq'].
Qed.
End TpConcrete.

Lemma label_pair_equal1_l : forall c X, label_pair (equal1 c) X = false.
Proof. intros c X; destruct (equal1_shape c) as [a [b [d ->]]]; reflexivity. Qed.
Lemma label_pair_equal1_r : forall u c, label_pair u (equal1 c) = false.
Proof.
  intros u c; destruct (label_pair u (equal1 c)) eqn:E; [|reflexivity].
  destruct (label_pair_K1 _ _ E) as [m Em]; destruct (equal1_shape c) as [a [b [d Ed]]]; congruence.
Qed.

Lemma label_pair_equal1_s : forall c X, label_pair (Sm (equal1 c)) X = false.
Proof.
  intros c X; destruct (label_pair (Sm (equal1 c)) X) eqn:E; [|reflexivity].
  rewrite label_pair_of in E. destruct (label_of (Fk (Sm (equal1 c)) X)) as [n|] eqn:El; [|discriminate].
  apply label_of_some in El; inversion El as [E1].
  destruct (equal1_shape c) as [a [b [d Ed]]]; congruence.
Qed.

Ltac conc := first [ reflexivity | (vm_compute; reflexivity)
  | (cbn [concreteb label_pair label_of]; repeat (rewrite ?equal1_concrete, ?label_pair_equal1_l, ?label_pair_equal1_r; cbn [andb]); reflexivity) ].

Ltac mirror := repeat first
  [ eassumption
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [reflexivity| | |])
  | (apply tp_stem; first [reflexivity|apply label_pair_equal1_l|apply label_pair_equal1_r|apply label_pair_equal1_s])
  | apply tp_leaf_fwd
  | (apply tp_tri_leaf; conc)
  | (eapply tp_tri_stem; [conc|conc|])
  | (eapply tp_tri_fork; [conc|first [reflexivity|apply label_of_concrete; assumption]| |]) ].

Local Transparent equal Z equal1.
Lemma app_equal : forall O c, concreteb c = true -> tp O @ equal @r c ==> Sm (equal1 c).
Proof.
  intros O c; induction c as [|c IH|a IHa b IHb]; intro Hc.
  - unfold equal, Z; cbv [equal_body star_triage star_fork]; mirror.
  - cbn [concreteb] in Hc; specialize (IH Hc).
    unfold equal at 1, Z; cbv [equal_body star_triage star_fork]; mirror.
  - destruct (concrete_Fk _ _ Hc) as [_ [Ha Hb]]; specialize (IHa Ha); specialize (IHb Hb).
    unfold equal at 1, Z; cbv [equal_body star_triage star_fork equal_fork]; mirror.
Qed.
Local Opaque equal Z equal1.

(** At the type level the tester runs as the program: both forms apply
    alike at every argument type. *)
Lemma app_tester : forall O c U V, concreteb c = true ->
  tp O @ 'wait[equal,c] @r U ==> Sm V <-> tp O @ equal1 c @r U ==> Sm V.
Proof.
  intros O c U V Hc; split; intro H.
  - apply tp_inv in H; inversion H as [| | | |G H0 U0 A W R0 HL HA HW HAW| | |]; subst.
    unfold app in *.
    pose proof (eval_deterministic _ _ HW _ (app_I O U)) as E; inversion E; subst W; clear E HW.
    apply tp_inv in HA; inversion HA as [| | | |G1 H1 U1 A1 B1 R1 HL1 HA1 HB1 HAB1| | |]; subst.
    unfold app in *.
    pose proof (eval_deterministic _ _ HA1 _ (tp_K1_fwd O equal U)) as E1.
    pose proof (eval_deterministic _ _ HB1 _ (tp_K1_fwd O c U)) as E2.
    inversion E1; inversion E2; subst A1 B1.
    pose proof (eval_deterministic _ _ HAB1 _ (app_equal O c Hc)) as E3.
    inversion E3; subst A; exact HAW.
  - eapply tp_S2_fwd; [reflexivity| |apply app_I|exact H].
    eapply tp_S2_fwd; [reflexivity|apply tp_K1_fwd|apply tp_K1_fwd|apply app_equal, Hc].
Qed.

(** ** Expressions whose testers are only applied *)

Definition fixedb (v : Combination) : bool := ceqb (specialise_fn v) v.
Definition redex_head (v : Combination) : bool :=
  match site v with Some c => concreteb c | None => false end.
Fixpoint heads_only (e : Combination) : bool :=
  match e with
  | Lf => true
  | Sm v => fixedb v
  | Fk e1 e2 =>
      match site (Fk e1 e2) with
      | Some _ => false
      | None =>
          (match e1 with
           | Sm v => fixedb v || redex_head v
           | _ => heads_only e1
           end) && heads_only e2
      end
  end%bool.

Lemma wait_equal_concrete : forall c, concreteb c = true -> concreteb ('wait[equal,c]) = true.
Proof.
  intros c H. Local Transparent equal Z.
  change ('wait[equal,c]) with ('S2['S2['K1 equal, 'K1 c], 'I]).
  cbn [concreteb label_pair label_of]. rewrite H.
  assert (He : concreteb equal = true) by (vm_compute; reflexivity). rewrite He.
  destruct (label_pair equal c) eqn:E; [|reflexivity].
  destruct (label_pair_K1 _ _ E) as [m ->]; discriminate.
  Local Opaque equal Z.
Qed.

Lemma specialise_preserves_expression_typing : forall O e T,
  heads_only e = true -> infer_expression O @ e ==> Sm T -> infer_expression O @ specialise_fn e ==> Sm T.
Proof.
  intros O; induction e as [|u _|e1 IH1 e2 IH2]; intros T Ho H.
  - exact H.
  - rewrite specialise_fn_site_none by reflexivity.
    cbn [heads_only] in Ho; apply ceqb_true in Ho; rewrite Ho; exact H.
  - cbn [heads_only] in Ho; destruct (site (Fk e1 e2)) as [c|] eqn:Es; [discriminate|].
    rewrite specialise_fn_site_none by exact Es.
    apply andb_prop in Ho as [Ho1 Ho2].
    destruct (ie_inv O _ _ H) as [[u [E _]]|[e1' [e2' [T1 [T2 [E [H1 [H2 Happ]]]]]]]]; [discriminate|].
    inversion E; subst e1' e2'; clear E.
    destruct e1 as [|v|a b].
    + destruct (ie_inv O _ _ H1) as [[u [E _]]|[x [y [_ [_ [E _]]]]]]; discriminate.
    + destruct (ie_inv O _ _ H1) as [[u' [E Hv]]|[x [y [_ [_ [E _]]]]]]; [|discriminate].
      inversion E; subst u'; clear E.
      apply Bool.orb_true_iff in Ho1 as [Hf|Hr].
      * rewrite specialise_fn_site_none by reflexivity.
        apply ceqb_true in Hf; rewrite Hf.
        eapply ie_fork; [apply ie_stem; exact Hv|exact (IH2 T2 Ho2 H2)|exact Happ].
      * unfold redex_head in Hr; destruct (site v) as [c|] eqn:Ev; [|discriminate].
        apply site_some in Ev; subst v.
        pose proof (eval_deterministic _ _ Hv _ (concrete_is_self_typed O _ (wait_equal_concrete c Hr))) as E;
          inversion E; subst T1; clear E.
        rewrite specialise_fn_site_none by reflexivity.
        rewrite specialise_fn_wait.
        assert (Hw : infer O @ (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end)
                       ==> Sm (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end) /\
                     tp O @ (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end) @r T2 ==> Sm T).
        { destruct c as [|n|p q]; split;
            first [ exact Happ
                  | exact Hv
                  | apply concrete_is_self_typed, equal1_concrete
                  | apply (app_tester O _ T2 T Hr); exact Happ ]. }
        eapply ie_fork; [apply ie_stem; exact (proj1 Hw)|exact (IH2 T2 Ho2 H2)|exact (proj2 Hw)].
    + eapply ie_fork; [exact (IH1 T1 Ho1 H1)|exact (IH2 T2 Ho2 H2)|exact Happ].
Qed.

(** ** The theorem *)

Theorem specialise_typed : forall O,
  infer O @ specialise_equal ==> Sm specialise_equal /\
  (forall c, specialise_equal @ 'wait[equal,'K1 c] ==> equal1 ('K1 c)) /\
  (forall e e' T, heads_only e = true -> infer_expression O @ e ==> Sm T ->
     specialise_equal @ e ==> e' -> infer_expression O @ e' ==> Sm T).
Proof.
  intro O; split; [apply concrete_is_self_typed, specialise_equal_concrete|split].
  - intro c; pose proof (specialise_equal_eval ('wait[equal,'K1 c])) as H.
    rewrite specialise_fn_wait in H; exact H.
  - intros e e' T Ho H He.
    rewrite (eval_deterministic _ _ He _ (specialise_equal_eval e)).
    exact (specialise_preserves_expression_typing O e T Ho H).
Qed.

(** ** What needs the condition *)

(** A tester that is not applied changes type: a concrete value is its own type. *)
Definition K1_tester := 'wait[equal,'K1 Lf].
Theorem specialise_changes_type : forall O,
  infer_expression O @ Sm K1_tester ==> Sm K1_tester /\
  infer_expression O @ specialise_fn (Sm K1_tester) ==> Sm (equal1 ('K1 Lf)) /\
  K1_tester <> equal1 ('K1 Lf).
Proof.
  intro O; split; [|split].
  - apply ie_stem, concrete_is_self_typed, wait_equal_concrete; reflexivity.
  - assert (E : specialise_fn (Sm K1_tester) = Sm (equal1 ('K1 Lf))).
    { rewrite specialise_fn_site_none by reflexivity; unfold K1_tester.
      rewrite specialise_fn_wait; reflexivity. }
    rewrite E; apply ie_stem, concrete_is_self_typed, equal1_concrete.
  - Local Transparent equal1 equal Z. unfold K1_tester; cbn; discriminate.
Qed.
