(** * Specialising equality.

    The optimisation [specialise_equal] walks a tree and replaces each tester
    [wait[equal,c]] by the value of [equal @ c], which is [equal1 c] by
    [equal_eval].  It holds [equal] and no copy of [equal1].  The tester of a
    stem [c = Sm n] is left alone, since [name_test n] holds that tester and
    the IsNamed row reads it.

    On the redex, behaviour is unchanged ([tester_agrees]).  Optimisation does
    not promise that results never change: a program that reads the tree, such
    as [size], sees the difference.  What is proved:

    - concrete programs stay concrete, so each is still its own type
      ([specialise_concrete], [specialise_self_typed]); a tester holds no
      label for any [c] ([equal1_concrete]);
    - type and value of an expression are preserved when every replaced tester
      is the function part of an application ([heads_only],
      [specialise_typed], [specialise_preserves_evaluation]); without that
      the type changes ([specialise_changes_type]), and the excluded name
      tests would lose theirs ([specialised_name_test_untyped]);
    - results of [infer] on the optimised declarations agree with
      [paper_ontology] on whatever is proved from the ordinary rows
      ([unchanged_from_support]), and on computed examples
      ([infer_unchanged_examples]);
    - the table of sizes ([size_table]) and exact step counts ([takes]). *)

From Stdlib Require Import String Lia PeanoNat List NArith.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions queries updates paper_ontology conditionals data_types arrays customisation self_typing optimisation steps.
Import ListNotations.

Open Scope string_scope.

(** * The program *)

(** [site t] reads the tester [wait[equal,c]]. *)
Definition site (t : Combination) : option Combination :=
  match t with
  | Fk (Sm (Fk (Sm (Fk Lf m)) (Fk Lf c))) i =>
      if andb (ceqb m equal) (ceqb i ('I)) then Some c else None
  | _ => None
  end.

Fixpoint specialise_fn (t : Combination) : Combination :=
  match site t with
  | Some (Sm _) => t
  | Some c => equal1 c
  | None =>
      match t with
      | Lf => Lf
      | Sm u => Sm (specialise_fn u)
      | Fk u v => Fk (specialise_fn u) (specialise_fn v)
      end
  end.

Definition is_stem : Combination := 'triage['KI, 'K1 'K, 'K1 ('K1 'KI)].

Definition specialise_body_package :
  { t | to_tree
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
        @@ Val equal))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition specialise_body := Eval cbn in proj1_sig specialise_body_package.
Definition specialise_equal := Z specialise_body.



Lemma site_wait : forall c, site ('wait[equal,c]) = Some c.
Proof.
  intro c; cbn [site].
  rewrite !ceqb_refl; reflexivity.
Qed.

Lemma site_some : forall t c, site t = Some c -> t = 'wait[equal,c].
Proof.
  intros t c H; unfold site in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => is_var x; destruct x
         end; try discriminate.
  match type of H with
  | context [ceqb ?m equal] => destruct (ceqb m equal) eqn:E1
  end; [|discriminate].
  match type of H with
  | context [ceqb ?i ('I)] => destruct (ceqb i ('I)) eqn:E2
  end; [|discriminate].
  apply ceqb_true in E1; apply ceqb_true in E2; subst.
  cbn in H; inversion H; reflexivity.
Qed.

Lemma site_none : forall t, (forall c, t <> 'wait[equal,c]) -> site t = None.
Proof.
  intros t H; destruct (site t) as [c|] eqn:E; [|reflexivity].
  exfalso; eapply H; apply site_some; exact E.
Qed.

Lemma specialise_fn_site_none : forall t, site t = None ->
  specialise_fn t =
    match t with
    | Lf => Lf
    | Sm u => Sm (specialise_fn u)
    | Fk u v => Fk (specialise_fn u) (specialise_fn v)
    end.
Proof. intros t H; destruct t; cbn [specialise_fn]; rewrite ?H; reflexivity. Qed.

Lemma specialise_fn_wait : forall c,
  specialise_fn ('wait[equal,c]) =
    match c with Sm _ => 'wait[equal,c] | _ => equal1 c end.
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
  - pose proof (get_wait_none Lf ltac:(intros M N H; discriminate)) as Hg.
    body_run.
  - pose proof (get_wait_none (Sm u) ltac:(intros M N H; discriminate)) as Hg.
    body_run.
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


(** * The redex *)

Theorem tester_agrees : forall c x v,
  'wait[equal,c] @ x ==> v <-> equal1 c @ x ==> v.
Proof.
  intros c x v; split; intro H.
  - apply wait_eval_inv in H.
    destruct (eval_pair_inv _ _ _ H) as [a [b [Ha [Hb Hv]]]].
    inv_out Hb.
    rewrite (eval_deterministic _ _ Ha _ (equal_eval c)) in Hv; exact Hv.
  - apply wait_eval; eapply eval_appl; [apply equal_eval|exact H].
Qed.

Lemma specialise_fn_agrees : forall c x v,
  'wait[equal,c] @ x ==> v <-> specialise_fn ('wait[equal,c]) @ x ==> v.
Proof.
  intros c x v; rewrite specialise_fn_wait; destruct c; try reflexivity;
  apply tester_agrees.
Qed.

(** * Testers hold no labels *)

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

Lemma sp_leaf : forall t, specialise_fn t = Lf -> t = Lf.
Proof.
  intros t H; destruct (site t) as [c|] eqn:E.
  - apply site_some in E; subst t; rewrite specialise_fn_wait in H.
    destruct c as [|c|a b]; cbn in H; discriminate.
  - rewrite specialise_fn_site_none in H by exact E.
    destruct t; congruence.
Qed.

Lemma sp_stem : forall t x, specialise_fn t = Sm x ->
  exists y, t = Sm y /\ specialise_fn y = x.
Proof.
  intros t x H; destruct (site t) as [c|] eqn:E.
  - apply site_some in E; subst t; rewrite specialise_fn_wait in H.
    destruct c as [|c|a b]; cbn in H; discriminate.
  - rewrite specialise_fn_site_none in H by exact E.
    destruct t; inversion H; eauto.
Qed.

Lemma sp_K1 : forall t n, specialise_fn t = Fk Lf n -> exists m, t = Fk Lf m.
Proof.
  intros t n H; destruct (site t) as [c|] eqn:E.
  - apply site_some in E; subst t; rewrite specialise_fn_wait in H.
    destruct c as [|c|a b]; cbn in H; discriminate.
  - rewrite specialise_fn_site_none in H by exact E.
    destruct t; inversion H; subst.
    apply sp_leaf in H1; subst; eauto.
Qed.

Lemma label_pair_specialise : forall u v,
  label_pair (specialise_fn u) (specialise_fn v) = true -> label_pair u v = true.
Proof.
  intros u v H; unfold label_pair in H.
  destruct (specialise_fn u) as [|[|[|a|a b]|a b]|a b] eqn:Eu; try discriminate.
  destruct (specialise_fn v) as [|a|[|a|a b] n] eqn:Ev; try discriminate.
  destruct (sp_stem _ _ Eu) as [y [-> Ey]].
  destruct (sp_stem _ _ Ey) as [z [-> Ez]].
  apply sp_leaf in Ez; subst z.
  destruct (sp_K1 _ _ Ev) as [m ->]; reflexivity.
Qed.

Theorem specialise_concrete : forall t,
  concreteb t = true -> concreteb (specialise_fn t) = true.
Proof.
  induction t as [|u IH|u IHu v IHv]; intro H; [reflexivity|..].
  - rewrite specialise_fn_site_none by reflexivity; cbn in *; apply IH; exact H.
  - destruct (site (Fk u v)) as [c|] eqn:E.
    + apply site_some in E; rewrite E, specialise_fn_wait.
      destruct c; try apply equal1_concrete; rewrite <- E; exact H.
    + rewrite specialise_fn_site_none by exact E.
      cbn [concreteb] in *.
      apply andb_prop in H as [H Hv]; apply andb_prop in H as [Hp Hu].
      rewrite IHu, IHv by assumption.
      destruct (label_pair (specialise_fn u) (specialise_fn v)) eqn:El; [|reflexivity].
      apply label_pair_specialise in El; rewrite El in Hp; discriminate.
Qed.

Corollary specialise_self_typed : forall AI p, concrete p ->
  infer AI @ specialise_fn p ==> Sm (specialise_fn p).
Proof.
  intros AI p Hp; apply infer_tag_free, concrete_tag_free, concreteb_sound.
  apply specialise_concrete, concreteb_spec, Hp.
Qed.

Lemma specialise_equal_concrete : concrete specialise_equal.
Proof. Local Transparent equal get_wait. apply concreteb_sound; vm_compute; reflexivity. Qed.
Local Opaque equal get_wait.

(** [heads_only e]: every tester that [specialise_fn] replaces in the
    expression [e] is the function part of an application, at a tag-free
    [c]. *)
Definition fixedb (v : Combination) : bool := ceqb (specialise_fn v) v.
Definition redex_head (v : Combination) : bool :=
  match site v with Some c => tag_free c | None => false end.
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

Section Mirror.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).

Local Opaque structural_fork.
Lemma app_triage_leaf : forall F0 F1 F2,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  tapp @ 'triage[F0,F1,F2] @r Lf ==> Sm F0.
Proof.
  intros F0 F1 F2 HP; apply app_triage_structural.
  apply (proj2 (structural_triage_plain _ _ _ _ _ _ HP)).
  unfold plain_triage; evaluate.
Qed.

Lemma app_triage_stem : forall F0 F1 F2 N V,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  tapp @ F1 @r N ==> Sm V ->
  tapp @ 'triage[F0,F1,F2] @r Sm N ==> Sm V.
Proof.
  intros F0 F1 F2 N V HP H; apply app_triage_structural.
  apply (proj2 (structural_triage_plain _ _ _ _ _ _ HP)).
  unfold plain_triage; apply eval_stem; apply wait_eval; exact H.
Qed.

Local Transparent structural_fork.
Lemma app_triage_fork : forall F0 F1 F2 X Y G V,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  (forall E N, Fk X Y <> 'tagged[E,N]) ->
  tapp @ F2 @r X ==> Sm G -> tapp @ G @r Y ==> Sm V ->
  tapp @ 'triage[F0,F1,F2] @r Fk X Y ==> Sm V.
Proof.
  intros F0 F1 F2 X Y G V HP HX H1 H2; apply app_triage_structural.
  apply (proj2 (structural_triage_plain _ _ _ _ _ _ HP)).
  unfold plain_triage, structural_fork.
  pose proof (get_tagged_none _ HX).
  destruct (eval_app_r_inv _ _ _ H1) as [w [Hw HR]].
  destruct (eval_app_r_inv _ _ _ H2) as [w2 [Hw2 HR2]].
  cbn; repeat first [eassumption | progress evaluate].
Qed.

Local Ltac mirror := repeat first
  [ eassumption
  | apply app_K | apply app_I | apply app_true | apply app_leaf
  | apply app_stem; apply type_app_stem_structural; solve [intros; discriminate]
  | new_S; [solve [intros; discriminate]| | |] ].

Local Transparent equal Z.
Lemma app_equal : forall c, tag_free c = true -> tapp @ equal @r c ==> Sm (equal1 c).
Proof.
  induction c as [|c IH|a IHa b IHb]; intro Hc.
  - unfold equal at 1; eapply app_Z.
    + cbv [equal_body star_triage star_fork]; mirror.
    + cbv [equal_body star_triage star_fork]; apply app_triage_leaf; intros; discriminate.
  - unfold equal at 1; eapply app_Z.
    + cbv [equal_body star_triage star_fork]; mirror.
    + cbv [equal_body star_triage star_fork]; apply app_triage_stem; [intros; discriminate|].
      cbn in Hc; specialize (IH Hc). mirror.
  - cbn [tag_free] in Hc.
    apply andb_prop in Hc as [Hc Hb]; apply andb_prop in Hc as [Hn Ha].
    specialize (IHa Ha); specialize (IHb Hb).
    assert (HP : forall E N, Fk a b <> 'tagged[E,N]).
    { intros E N HE; rewrite HE in Hn; cbn in Hn; discriminate. }
    unfold equal at 1; eapply app_Z.
    + cbv [equal_body star_triage star_fork]; mirror.
    + cbv [equal_body star_triage star_fork].
      eapply app_triage_fork; [intros; discriminate|exact HP|..].
      * unfold equal_fork. mirror.
      * cbn [equal1]; mirror.
Qed.
Local Opaque equal Z.

Lemma wait_equal_tag_free : forall c, tag_free c = true ->
  tag_free ('wait[equal,c]) = true.
Proof.
  intros c H; cbn [tag_free reserved_tagb andb negb].
  rewrite equal_tag_free, H; reflexivity.
Qed.

(** At the type level the tester runs as the program: both forms apply
    alike at every argument type. *)
Lemma app_tester : forall c U V, tag_free c = true ->
  tapp @ 'wait[equal,c] @r U ==> Sm V <-> tapp @ equal1 c @r U ==> Sm V.
Proof.
  intros c U V Hc; split; intro H.
  - destruct (S_success_inv' AI ('S2['K1 equal,'K1 c]) 'I U V
      ltac:(intros; discriminate) ltac:(reject_name) H) as [A [B [HA [HB HAB]]]].
    pose proof (eval_deterministic _ _ HB _ (app_I AI U)) as E; inversion E; subst B; clear E HB.
    destruct (S_success_inv' AI ('K1 equal) ('K1 c) U A
      ltac:(intros; discriminate) ltac:(reject_name) HA) as [A1 [B1 [HA1 [HB1 HAB1]]]].
    pose proof (eval_deterministic _ _ HA1 _ (app_K AI equal U)) as E1.
    pose proof (eval_deterministic _ _ HB1 _ (app_K AI c U)) as E2.
    inversion E1; inversion E2; subst A1 B1.
    pose proof (eval_deterministic _ _ HAB1 _ (app_equal c Hc)) as E3.
    inversion E3; subst A; exact HAB.
  - eapply type_app_wait; [apply app_equal; exact Hc|exact H].
Qed.

(** ** Expressions whose testers are only applied *)

Lemma specialise_preserves_expression_typing : forall e T,
  heads_only e = true ->
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ specialise_fn e ==> Sm T.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intros T Ho H.
  - exact H.
  - rewrite specialise_fn_site_none by reflexivity.
    cbn [heads_only] in Ho; apply ceqb_true in Ho; rewrite Ho; exact H.
  - cbn [heads_only] in Ho; destruct (site (Fk e1 e2)) as [c|] eqn:Es; [discriminate|].
    rewrite specialise_fn_site_none by exact Es.
    apply andb_prop in Ho as [Ho1 Ho2].
    destruct (infer_expression_fork_inv AI e1 e2 T H) as [T1 [T2 [H1 [H2 Happ]]]].
    destruct e1 as [|v|a b].
    + pose proof (eval_deterministic _ _ H1 _ (infer_expression_leaf AI)); discriminate.
    + apply infer_expression_stem_inv in H1.
      apply Bool.orb_true_iff in Ho1 as [Hf|Hr].
      * rewrite specialise_fn_site_none by reflexivity.
        apply ceqb_true in Hf; rewrite Hf.
        eapply infer_expression_fork;
          [apply infer_expression_stem; exact H1|exact (IH2 T2 Ho2 H2)|exact Happ].
      * unfold redex_head in Hr; destruct (site v) as [c|] eqn:Ev; [|discriminate].
        apply site_some in Ev; subst v.
        pose proof (eval_deterministic _ _ H1 _
          (infer_tag_free AI _ (wait_equal_tag_free c Hr))) as E; inversion E; subst T1; clear E.
        rewrite specialise_fn_site_none by reflexivity.
        rewrite specialise_fn_wait.
        assert (Hv : infer AI @ (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end)
                       ==> Sm (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end) /\
                     tapp @ (match c with Sm _ => 'wait[equal,c] | _ => equal1 c end) @r T2 ==> Sm T).
        { destruct c as [|n|p q]; split;
            first [ exact Happ
                  | exact H1
                  | apply infer_tag_free, concrete_tag_free, concreteb_sound, equal1_concrete
                  | apply app_tester; [exact Hr|exact Happ] ]. }
        eapply infer_expression_fork;
          [apply infer_expression_stem; exact (proj1 Hv)|exact (IH2 T2 Ho2 H2)|exact (proj2 Hv)].
    + eapply infer_expression_fork; [exact (IH1 T1 Ho1 H1)|exact (IH2 T2 Ho2 H2)|exact Happ].
Qed.
End Mirror.


Lemma specialise_value_head : forall v u w, redex_head v = true ->
  v @ u ==> w <-> specialise_fn v @ u ==> w.
Proof.
  intros v u w Hr; unfold redex_head in Hr; destruct (site v) as [c|] eqn:Ev; [|discriminate].
  apply site_some in Ev; subst v; apply specialise_fn_agrees.
Qed.

Lemma specialise_preserves_evaluation : forall e v,
  heads_only e = true -> (e ==> v <-> specialise_fn e ==> v).
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intros v Ho.
  - reflexivity.
  - cbn [heads_only] in Ho; apply ceqb_true in Ho.
    rewrite specialise_fn_site_none by reflexivity; rewrite Ho; reflexivity.
  - cbn [heads_only] in Ho; destruct (site (Fk e1 e2)) as [c|] eqn:Es; [discriminate|].
    rewrite specialise_fn_site_none by exact Es.
    apply andb_prop in Ho as [Ho1 Ho2].
    destruct e1 as [|w|a b].
    + split; intro H; inversion H.
    + rewrite specialise_fn_site_none by reflexivity.
      rewrite !value_app_eval_iff.
      apply Bool.orb_true_iff in Ho1 as [Hf|Hr].
      * apply ceqb_true in Hf; rewrite Hf; split; intros [v2 [H2 H]];
          exists v2; split; [apply IH2; assumption|exact H|apply IH2; assumption|exact H].
      * split; intros [v2 [H2 H]]; exists v2; split.
        -- apply IH2; assumption.
        -- apply (proj1 (specialise_value_head _ _ _ Hr)); exact H.
        -- apply IH2; assumption.
        -- apply (proj2 (specialise_value_head _ _ _ Hr)); exact H.
    + rewrite !app_eval_iff; split; intros [v1 [v2 [H1 [H2 H]]]];
        exists v1, v2; repeat split;
        [apply IH1; assumption|apply IH2; assumption|exact H|
         apply IH1; assumption|apply IH2; assumption|exact H].
Qed.

Theorem specialise_typed : forall (AI : Decl),
  infer AI @ specialise_equal ==> Sm specialise_equal /\
  (forall c, specialise_equal @ 'wait[equal,'K1 c] ==> equal1 ('K1 c)) /\
  (forall e e' T, heads_only e = true ->
     infer_expression AI @ e ==> Sm T ->
     specialise_equal @ e ==> e' -> infer_expression AI @ e' ==> Sm T).
Proof.
  intro AI; split; [apply infer_tag_free, concrete_tag_free, specialise_equal_concrete|split].
  - intro c; pose proof (specialise_equal_eval ('wait[equal,'K1 c])) as H.
    rewrite specialise_fn_wait in H; exact H.
  - intros e e' T Ho H He.
    rewrite (eval_deterministic _ _ He _ (specialise_equal_eval e)).
    exact (specialise_preserves_expression_typing AI e T Ho H).
Qed.

(** ** What needs the exclusions *)

Definition K1_tester := 'wait[equal,'K1 Lf].

(** A tester that is not only applied changes type: a concrete value is
    its own type. *)
Lemma specialise_changes_type : forall (AI : Decl),
  infer_expression AI @ Sm K1_tester ==> Sm K1_tester /\
  infer_expression AI @ specialise_fn (Sm K1_tester) ==> Sm (equal1 ('K1 Lf)) /\
  K1_tester <> equal1 ('K1 Lf).
Proof.
  intro AI; split; [|split].
  - apply infer_expression_stem, infer_tag_free, wait_equal_tag_free; reflexivity.
  - assert (E : specialise_fn (Sm K1_tester) = Sm (equal1 ('K1 Lf))).
    { rewrite specialise_fn_site_none by reflexivity; unfold K1_tester.
      rewrite specialise_fn_wait; reflexivity. }
    rewrite E; apply infer_expression_stem, infer_tag_free, concrete_tag_free,
      concreteb_sound, equal1_concrete.
  - unfold K1_tester; cbn; discriminate.
Qed.

Lemma specialise_get_tagname : specialise_fn get_tagname = get_tagname.
Proof. apply ceqb_true; vm_compute; reflexivity. Qed.

Lemma specialise_name_test : forall n, specialise_fn (name_test n) = name_test n.
Proof.
  intro n; unfold name_test.
  rewrite specialise_fn_site_none by reflexivity.
  rewrite specialise_get_tagname.
  rewrite (specialise_fn_site_none (Sm _)) by reflexivity.
  rewrite (specialise_fn_site_none ('K1 _)) by reflexivity.
  rewrite specialise_fn_wait; reflexivity.
Qed.

Lemma specialise_is_named : forall n,
  specialise_fn (is_named n) = is_named n.
Proof.
  intro n; unfold is_named.
  rewrite specialise_fn_site_none by reflexivity.
  rewrite (specialise_fn_site_none (Sm _)) by reflexivity.
  rewrite (specialise_fn_site_none ('K1 _)) by reflexivity.
  rewrite specialise_name_test.
  assert (E : specialise_fn ('label[is_named_nm]) = 'label[is_named_nm])
    by (apply ceqb_true; vm_compute; reflexivity).
  rewrite E; reflexivity.
Qed.

(** Replacing the tester of a name test would lose its type: the IsNamed row
    reads [name_test N] from the carrier. *)
Lemma specialised_name_test_untyped : forall AI N,
  supports_is_named AI ->
  ~ exists T, infer AI @ 'tagged[equal1 (Sm N) 'C get_tagname, is_named_nm] ==> Sm T.
Proof.
  intros AI N HT [T H].
  destruct (infer_tagged_source_inv AI _ _ _ H) as [C [M [E [_ [HC [Hn HI]]]]]].
  assert (Htn : infer AI @ is_named_nm ==> Sm is_named_nm) by (apply infer_tag_free; reflexivity).
  pose proof (eval_deterministic _ _ Hn _ Htn) as EM; inversion EM; subst M; clear EM Hn.
  assert (Hc : tag_free (equal1 (Sm N) 'C get_tagname) = true).
  { apply concrete_tag_free, concreteb_sound.
    assert (Hg : concreteb get_tagname = true) by (vm_compute; reflexivity).
    assert (Gen : forall e, concreteb e = true -> concreteb (e 'C get_tagname) = true).
    { intros e He; cbn [concreteb label_pair negb andb]; rewrite He; exact Hg. }
    apply Gen, equal1_concrete. }
  pose proof (eval_deterministic _ _ HC _ (infer_tag_free AI _ Hc)) as EC.
  inversion EC; subst C; clear EC HC.
  pose proof (declaration_K1_inv _ _ _ _ _ _ HT HI) as Hrun.
  destruct (is_named_abstractor_inv _ _ Hrun) as [X [Ee _]].
  unfold name_test in Ee; inversion Ee.
Qed.

(** * The optimised declarations *)

Definition specialised_ontology := specialise_fn paper_ontology.

Lemma specialise_infer :
  specialise_fn (infer paper_ontology) = infer specialised_ontology.
Proof. apply ceqb_true; vm_compute; reflexivity. Qed.

Lemma specialise_equal_infer :
  specialise_equal @ infer paper_ontology ==> infer specialised_ontology.
Proof. rewrite <- specialise_infer; apply specialise_equal_eval. Qed.

Lemma specialised_ontology_concrete : concrete specialised_ontology.
Proof.
  apply concreteb_sound, specialise_concrete, concreteb_spec, paper_ontology_concrete.
Qed.

Lemma specialised_ontology_tag_free : tag_free specialised_ontology = true.
Proof. apply concrete_tag_free, specialised_ontology_concrete. Qed.

Theorem specialised_infer_self_typed :
  infer specialised_ontology @ infer specialised_ontology
    ==> Sm (infer specialised_ontology).
Proof.
  apply infer_self_typed, specialised_ontology_concrete.
Qed.

Lemma specialised_infer_typed_by_paper :
  infer paper_ontology @ infer specialised_ontology
    ==> Sm (infer specialised_ontology).
Proof.
  rewrite <- specialise_infer; apply specialise_self_typed, infer_all_concrete.
Qed.

(** * Results of [infer] on the optimised declarations *)

Definition supports_base AI : Prop :=
  supports_booleans AI /\ supports_number AI /\ supports_option AI /\
  supports_sum AI /\ supports_list AI /\ supports_arrays AI /\
  supports_salary AI /\ supports_employee AI /\ supports_department AI /\
  supports_is_named AI /\ supports_seek AI.

Local Ltac lookup := eapply run_sound with (fuel := 1000); vm_compute; reflexivity.

Lemma specialised_row : specialised_ontology @ fun_nm ==> function_abstractor.
Proof. lookup. Qed.
Canonical Structure specialised_decl := mkDecl specialised_ontology specialised_row.

Lemma specialised_supports_base : supports_base specialised_ontology.
Proof. repeat split; unfold supports_booleans, supports_number, supports_option,
  supports_sum, supports_list, supports_arrays, supports_salary, supports_employee,
  supports_department, supports_is_named, supports_seek; lookup. Qed.

Lemma paper_supports_base : supports_base paper_ontology.
Proof. repeat split; unfold supports_booleans, supports_number, supports_option,
  supports_sum, supports_list, supports_arrays, supports_salary, supports_employee,
  supports_department, supports_is_named, supports_seek; lookup. Qed.

(** What is proved from the support of the ordinary rows, for every
    declarations, holds alike before and after. *)
Theorem unchanged_from_support : forall P : Combination -> Prop,
  (forall (AI : Decl), supports_base AI -> P AI) ->
  P paper_ontology /\ P specialised_ontology.
Proof.
  intros P H; split; apply H; [exact paper_supports_base|exact specialised_supports_base].
Qed.

Corollary infer_unchanged_tag_free : forall x, tag_free x = true ->
  infer paper_ontology @ x ==> Sm x /\ infer specialised_ontology @ x ==> Sm x.
Proof. intros x H; split; apply infer_tag_free; exact H. Qed.

Corollary infer_unchanged_numeral : forall n,
  infer paper_ontology @ numeral n ==> Sm ('Nat) /\
  infer specialised_ontology @ numeral n ==> Sm ('Nat).
Proof.
  intro n; apply (unchanged_from_support (fun AI => infer AI @ numeral n ==> Sm ('Nat))).
  intros AI [_ [HN _]]; apply numeral_typed; exact HN.
Qed.

Corollary infer_unchanged_employee : forall id amount,
  infer paper_ontology @ employee_at id amount ==> Sm ('Employee) /\
  infer specialised_ontology @ employee_at id amount ==> Sm ('Employee).
Proof.
  intros id amount;
  apply (unchanged_from_support (fun AI => infer AI @ employee_at id amount ==> Sm ('Employee))).
  intros AI [_ [HN [_ [_ [_ [_ [HS [HE _]]]]]]]]; apply infer_employee.
  - exact HE.
  - apply numeral_typed; exact HN.
  - apply infer_salary; [exact HS|apply numeral_typed; exact HN].
Qed.

(** Worked instances that reach the replaced tester, computed. *)
Definition run_fuel := 1000 * 1000.

Definition same_result (fuel : nat) (A B x : Combination) : bool :=
  match run fuel (infer A) x, run fuel (infer B) x with
  | Some (Sm T), Some (Sm T') => ceqb T T'
  | _, _ => false
  end.

Lemma same_result_sound : forall fuel A B x, same_result fuel A B x = true ->
  exists T, infer A @ x ==> Sm T /\ infer B @ x ==> Sm T.
Proof.
  intros fuel A B x H; unfold same_result in H.
  destruct (run fuel (infer A) x) as [[|T|]|] eqn:E1; try discriminate.
  destruct (run fuel (infer B) x) as [[|T'|]|] eqn:E2; try discriminate.
  apply ceqb_true in H; subst T'.
  exists T; split; eapply run_sound; eassumption.
Qed.

Lemma infer_unchanged_examples :
  forallb (same_result run_fuel paper_ontology specialised_ontology)
    [salary_bill; salary_update; count_employees; paid_over_57;
     department_example; is_named salary_nm] = true.
Proof. vm_compute; reflexivity. Qed.

(** * Step counts *)

(** [crun] evaluates and counts, in the steps of [steps]: name tests count one. *)
Fixpoint teq (a b : Combination) : bool :=
  match a, b with
  | Lf, Lf => true
  | Sm x, Sm y => teq x y
  | Fk x y, Fk u v => teq x u && teq y v
  | _, _ => false
  end%bool.

Lemma teq_spec : forall a b, teq a b = true <-> a = b.
Proof.
  induction a as [|x IH|x IHx y IHy]; intros [|u|u v]; cbn; split; intro H;
    try discriminate; try reflexivity.
  - rewrite (proj1 (IH u) H); reflexivity.
  - inversion H; subst; apply IH; reflexivity.
  - apply andb_prop in H as [H1 H2].
    rewrite (proj1 (IHx u) H1), (proj1 (IHy v) H2); reflexivity.
  - inversion H; subst; rewrite (proj2 (IHx u) eq_refl), (proj2 (IHy v) eq_refl); reflexivity.
Qed.

Definition quick_test (f : Combination) : option Combination :=
  match f with
  | Fk (Sm (Fk _ (Fk (Sm (Fk _ (Fk _ (Sm n)))) _))) _ =>
      if teq f (name_test n) then Some n else None
  | _ => None
  end.

Lemma quick_test_eq : forall f, quick_test f = as_name_test f.
Proof.
  intro f; unfold quick_test;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => is_var x; destruct x
         end;
  try reflexivity;
  unfold as_name_test; cbn [name_of_test];
  try (destruct combination_eq_dec as [E|E]; try reflexivity;
       unfold name_test in E; discriminate E).
  match goal with
  | |- (if teq ?f ?g then _ else _) = _ =>
      destruct (teq f g) eqn:Et;
      [apply teq_spec in Et; destruct combination_eq_dec as [E|E]; [reflexivity|contradiction]
      |destruct combination_eq_dec as [E|E]; [apply teq_spec in E; congruence|reflexivity]]
  end.
Qed.

Fixpoint crun (fuel : nat) (f u : Combination) : option (Combination * N) :=
  match fuel with
  | O => None
  | S k =>
    match quick_test f with
    | Some n => Some (test_answer n u, 1%N)
    | None =>
    match f with
    | Lf => Some (Sm u, 1%N)
    | Sm x => Some (Fk x u, 1%N)
    | Fk Lf x => Some (x, 1%N)
    | Fk (Sm g) h =>
      match crun k g u, crun k h u with
      | Some (a, i), Some (b, j) =>
        match crun k a b with
        | Some (r, l) => Some (r, (i + j + l + 1)%N)
        | None => None
        end
      | _, _ => None
      end
    | Fk (Fk a b) c =>
      match u with
      | Lf => Some (a, 1%N)
      | Sm x =>
        match crun k b x with
        | Some (r, i) => Some (r, (i + 1)%N)
        | None => None
        end
      | Fk x y =>
        match crun k c x with
        | Some (d, i) =>
          match crun k d y with
          | Some (r, j) => Some (r, (i + j + 1)%N)
          | None => None
          end
        | None => None
        end
      end
    end
    end
  end.

Local Abbreviation adv := (advances_n atomic_rewrite).

Lemma crun_sound : forall fuel f u v n,
  crun fuel f u = Some (v, n) -> adv (N.to_nat n) (f @ u) (Sm v).
Proof.
  induction fuel as [|fuel IH]; intros f u v n H; [discriminate|].
  cbn [crun] in H.
  destruct (quick_test f) as [m|] eqn:Eq.
  - inversion H; subst.
    rewrite quick_test_eq in Eq.
    change (N.to_nat 1) with 1.
    econstructor; [apply adv_ready|].
    unfold atomic_rewrite; rewrite Eq; constructor.
  - rewrite quick_test_eq in Eq.
    assert (Er : atomic_rewrite f u = rule_rewrite f u)
      by (unfold atomic_rewrite; rewrite Eq; reflexivity).
    assert (Hstep : forall k, adv k (rule_rewrite f u) (Sm v) -> adv (S k) (f @ u) (Sm v)).
    { intros k Hk; econstructor; [apply adv_ready|rewrite Er; exact Hk]. }
    destruct f as [|x|[|g|a b] h].
    + inversion H; subst; apply Hstep; constructor.
    + inversion H; subst; apply Hstep; constructor.
    + inversion H; subst; apply Hstep; constructor.
    + destruct (crun fuel g u) as [[a i]|] eqn:E1; [|discriminate].
      destruct (crun fuel h u) as [[b j]|] eqn:E2; [|discriminate].
      destruct (crun fuel a b) as [[r l]|] eqn:E3; [|discriminate].
      injection H; intros; subst.
      replace (N.to_nat (i + j + l + 1)) with (S (N.to_nat i + (N.to_nat j + N.to_nat l))) by lia.
      apply Hstep; cbn [rule_rewrite].
      eapply advances_n_trans; [apply advances_n_op; apply IH; exact E1|].
      eapply advances_n_trans; [apply advances_n_arg; apply IH; exact E2|].
      apply IH; exact E3.
    + destruct u as [|x|x y].
      * inversion H; subst; apply Hstep; constructor.
      * destruct (crun fuel b x) as [[r i]|] eqn:E1; [|discriminate].
        injection H; intros; subst.
        replace (N.to_nat (i + 1)) with (S (N.to_nat i)) by lia.
        apply Hstep; apply IH; exact E1.
      * destruct (crun fuel h x) as [[d i]|] eqn:E1; [|discriminate].
        destruct (crun fuel d y) as [[r j]|] eqn:E2; [|discriminate].
        injection H; intros; subst.
        replace (N.to_nat (i + j + 1)) with (S (N.to_nat i + N.to_nat j)) by lia.
        apply Hstep; cbn [rule_rewrite].
        eapply advances_n_trans; [apply advances_n_op; apply IH; exact E1|].
        apply IH; exact E2.
Qed.

(** [takes n e v]: [e] reaches the value [v] in exactly [n] steps. *)
Definition takes (n : N) (e v : Combination) : Prop :=
  steps (N.to_nat n) e = Sm v /\
  forall j w, j < N.to_nat n -> steps j e <> Sm w.

Lemma adv_first : forall k e v, adv k e (Sm v) ->
  forall j w, j < k -> steps j e <> Sm w.
Proof.
  intros k e v H; remember (Sm v) as t; induction H; intros j w Hj; [lia|].
  destruct (advances_fork _ _ _ H) as [a [b ->]].
  destruct j as [|j]; [cbn; discriminate|].
  rewrite <- (advances_step _ _ _ H) in *.
  cbn; apply IHadvances_n; [assumption|lia].
Qed.

Lemma crun_takes : forall fuel f u v n,
  crun fuel f u = Some (v, n) -> takes n (f @ u) v.
Proof.
  intros fuel f u v n H; pose proof (crun_sound _ _ _ _ _ H) as A; split.
  - exact (advances_n_steps _ _ _ _ A).
  - apply (adv_first _ _ _ A).
Qed.

Definition counts (fuel : nat) (n : N) (f u : Combination) : bool :=
  match crun fuel f u with
  | Some (_, m) => N.eqb m n
  | None => false
  end.

Lemma counts_takes : forall fuel n f u, counts fuel n f u = true ->
  exists v, takes n (f @ u) v.
Proof.
  intros fuel n f u H; unfold counts in H.
  destruct (crun fuel f u) as [[v m]|] eqn:E; [|discriminate].
  apply N.eqb_eq in H; subst m.
  exists v; eapply crun_takes; exact E.
Qed.

Definition specialised_infer := infer specialised_ontology.

Local Ltac counted := eapply counts_takes with (fuel := run_fuel); vm_compute; reflexivity.

(** Steps, before and after; the first three programs are unchanged in
    length, and [salary_bill] is unchanged as a tree. *)
Lemma specialise_leaves_examples :
  specialise_fn salary_bill = salary_bill /\
  specialise_fn nat_abstractor = nat_abstractor.
Proof. split; apply ceqb_true; vm_compute; reflexivity. Qed.

Lemma steps_infer_one :
  (exists v, takes 132996 (infer paper_ontology @ one) v) /\
  (exists v, takes 132996 (specialised_infer @ one) v).
Proof. split; counted. Qed.

Lemma steps_infer_employee :
  (exists v, takes 755366 (infer paper_ontology @ employee_at 1 2) v) /\
  (exists v, takes 755366 (specialised_infer @ employee_at 1 2) v).
Proof. split; counted. Qed.

Lemma steps_nat_abstractor :
  exists v, takes 114179 (nat_abstractor @ 'S2['snd,'Nat]) v.
Proof. counted. Qed.

Lemma steps_bill :
  exists v, takes 545335 (salary_bill @ department_example) v.
Proof. counted. Qed.

(** A tester that is reached: typing the bill and the update. *)
Lemma steps_infer_bill :
  (exists v, takes 23680101 (infer paper_ontology @ salary_bill) v) /\
  (exists v, takes 23620501 (specialised_infer @ salary_bill) v).
Proof. split; counted. Qed.

Lemma steps_infer_update :
  (exists v, takes 15297806 (infer paper_ontology @ salary_update) v) /\
  (exists v, takes 15238206 (specialised_infer @ salary_update) v).
Proof. split; counted. Qed.

(** * Sizes, as computed by [size] *)

(** [(p, n, n')]: [p] has size [n] and its specialisation size [n']. *)
Definition size_row_ok (r : Combination * nat * nat) : bool :=
  match r with
  | (p, n, n') =>
      Nat.eqb (tree_size p) n && Nat.eqb (tree_size (specialise_fn p)) n'
  end.

Definition size_row (r : Combination * nat * nat) : Prop :=
  match r with
  | (p, n, n') =>
      size @ p ==> numeral n /\
      specialise_equal @ p ==> specialise_fn p /\
      size @ specialise_fn p ==> numeral n'
  end.

Lemma size_row_sound : forall r, size_row_ok r = true -> size_row r.
Proof.
  intros [[p n] n'] H; cbn [size_row_ok] in H; cbn [size_row].
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst n n'.
  split; [apply size_eval|split; [apply specialise_equal_eval|apply size_eval]].
Qed.

#[warnings="-abstract-large-number"]
Definition size_rows : list (Combination * nat * nat) := [
  (infer paper_ontology, 70069, 97721);
  (paper_ontology, 66858, 94510);
  (get_IfNamed, 3424, 17250);
  (query_abstractor Lf, 15963, 29789);
  (update_abstractor Lf, 9872, 23698);
  (is_named_abstractor, 1857, 1857);
  (computed_wrap_abstractor employee_payload_program, 1605, 1605);
  (computed_wrap_abstractor department_payload_program, 2931, 2931);
  (computed_wrap_abstractor salary_payload_program, 1459, 1459);
  (array_abstractor, 8815, 8815);
  (list_abstractor, 4388, 4388);
  (sum_abstractor, 3888, 3888);
  (option_abstractor, 3753, 3753);
  (nat_abstractor, 1424, 1424);
  (bool_abstractor, 2455, 2455);
  (specialise_equal, 1224, 1224)].

Theorem size_table : Forall size_row size_rows.
Proof.
  apply Forall_forall; intros r Hr; apply size_row_sound.
  assert (H : forallb size_row_ok size_rows = true) by (vm_compute; reflexivity).
  exact (proj1 (forallb_forall _ _) H r Hr).
Qed.

(** * The sites of the walk

    [sites t] lists, in the order of the walk, the values [c] of the
    testers [wait[equal,c]] that [specialise_fn] replaces in [t]. *)
Fixpoint sites (t : Combination) : list Combination :=
  match site t with
  | Some (Sm _) => []
  | Some c => [c]
  | None =>
      match t with
      | Lf => []
      | Sm u => sites u
      | Fk u v => sites u ++ sites v
      end
  end.

(** The sizes of each site's value [c] and of its tester [equal1 c]. *)
Definition site_sizes (t : Combination) : list (nat * nat) :=
  List.map (fun c => (tree_size c, tree_size (equal1 c))) (sites t).

(** The walk finds four sites in [infer paper_ontology], two in each of the
    query and update abstractors: values of 324 and 190 nodes, whose
    testers have 9272 and 5744 nodes.  Computed. *)
#[warnings="-abstract-large-number"]
Lemma specialise_sites :
  site_sizes (infer paper_ontology) = [(324, 9272); (190, 5744); (324, 9272); (190, 5744)] /\
  site_sizes (query_abstractor Lf) = [(324, 9272); (190, 5744)] /\
  site_sizes (update_abstractor Lf) = [(324, 9272); (190, 5744)].
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** ** The sites are exactly the replacements

    [subtree s t]: [s] occurs in [t]. *)
Inductive subtree (s : Combination) : Combination -> Prop :=
| subtree_refl : subtree s s
| subtree_stem : forall u, subtree s u -> subtree s (Sm u)
| subtree_left : forall u v, subtree s u -> subtree s (Fk u v)
| subtree_right : forall u v, subtree s v -> subtree s (Fk u v).

Lemma sites_eq : forall t, sites t =
  match site t with
  | Some (Sm _) => []
  | Some c => [c]
  | None =>
      match t with
      | Lf => []
      | Sm u => sites u
      | Fk u v => (sites u ++ sites v)%list
      end
  end.
Proof. destruct t; reflexivity. Qed.

Lemma specialise_fn_eq : forall t, specialise_fn t =
  match site t with
  | Some (Sm _) => t
  | Some c => equal1 c
  | None =>
      match t with
      | Lf => Lf
      | Sm u => Sm (specialise_fn u)
      | Fk u v => Fk (specialise_fn u) (specialise_fn v)
      end
  end.
Proof. destruct t; reflexivity. Qed.

(** A replaced tester changes: [equal1 c] is a triage, the tester a wait. *)
Lemma equal1_not_wait : forall c, equal1 c <> 'wait[equal,c].
Proof. intro c; destruct c; unfold equal1; discriminate. Qed.

(** [specialise_fn t] leaves [t] unchanged exactly when [sites t] is
    empty, and each value [c] in [sites t] is not a stem, its tester
    [wait[equal,c]] occurs in [t], and [equal1 c] occurs in
    [specialise_fn t]. *)
Lemma sites_specialise_fn : forall t,
  (sites t = [] <-> specialise_fn t = t) /\
  (forall c, In c (sites t) ->
     (forall n, c <> Sm n) /\ subtree ('wait[equal,c]) t /\
     subtree (equal1 c) (specialise_fn t)).
Proof.
  induction t as [|u IHu|u IHu v IHv]; rewrite sites_eq, specialise_fn_eq.
  - cbn; split; [tauto|intros c []].
  - destruct (site (Sm u)) as [c|] eqn:E.
    { pose proof (site_some _ _ E) as Ht; discriminate Ht. }
    destruct IHu as [Iu Su]; split.
    + split; intro H; [rewrite (proj1 Iu H); reflexivity|].
      injection H as H; exact (proj2 Iu H).
    + intros c Hc; destruct (Su c Hc) as [Hn [H1 H2]].
      split; [exact Hn|split; apply subtree_stem; assumption].
  - destruct (site (Fk u v)) as [c|] eqn:E.
    + pose proof (site_some _ _ E) as Ht; rewrite Ht; clear IHu IHv E Ht.
      destruct c as [|n|a b].
      * split; [split; intro H; [discriminate|exact (False_ind _ (equal1_not_wait _ H))]|].
        intros c [<-|[]]; split; [discriminate|split; apply subtree_refl].
      * split; [tauto|intros c []].
      * split; [split; intro H; [discriminate|exact (False_ind _ (equal1_not_wait _ H))]|].
        intros c [<-|[]]; split; [discriminate|split; apply subtree_refl].
    + destruct IHu as [Iu Su]; destruct IHv as [Iv Sv]; split.
      * split; intro H.
        -- apply app_eq_nil in H as [H1 H2].
           rewrite (proj1 Iu H1), (proj1 Iv H2); reflexivity.
        -- injection H as H1 H2.
           rewrite (proj2 Iu H1), (proj2 Iv H2); reflexivity.
      * intros c Hc; apply in_app_or in Hc as [Hc|Hc].
        -- destruct (Su c Hc) as [Hn [H1 H2]].
           split; [exact Hn|split; apply subtree_left; assumption].
        -- destruct (Sv c Hc) as [Hn [H1 H2]].
           split; [exact Hn|split; apply subtree_right; assumption].
Qed.

Lemma sites_nil_specialise_fn : forall t,
  sites t = [] -> specialise_fn t = t.
Proof. intros t H; exact (proj1 (proj1 (sites_specialise_fn t)) H). Qed.

(** The sites lie in [get_IfNamed]: its own walk finds the same two. *)
Lemma specialise_sites_get_IfNamed : site_sizes get_IfNamed = [(324, 9272); (190, 5744)].
Proof. vm_compute; reflexivity. Qed.
