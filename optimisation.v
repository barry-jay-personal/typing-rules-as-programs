(** * Typed optimisation (paper: Towards Typed Tooling, "Typed optimisation").

    Typing-preserving optimisation: untagging and the optimiser [optimise],
    projections and unghosting, and the erasure of fixfunction tags at the
    root and along the spine of a function body. *)


(**********************************************************************)
(* Optimisation: dropping tags from applied abstract programs.        *)
(**********************************************************************)

(** An abstract program is a tagged value [tagged[t,n] = t o label[n]],
    and [tagged[t,n] @ v] evaluates exactly as [t @ v].  So in an
    expression, an application whose function part is the quoted value
    [Sm (tagged[t,n])] may use [Sm t] instead (repeatedly, while [t] is
    itself tagged).  Likewise [decorate[f,w] @ v] evaluates exactly as
    [f @ v], so a decorated function part, once untagged, may use [Sm f].
    The optimisation recurses through application nodes and never looks
    inside a value.

    It preserves evaluation (in both directions) and, relative to a sound
    declarations, expression typing: if [tagged[t,n]] has type
    [F] and [F # U ==> Sm V], then the carrier [t] has a type [C] with
    [C # U ==> Sm V].  This is the content of
    [infer_tagged_source_inv], [app_abstract_inv] and
    [plain_intro_sound], which also covers function introduction.
    A decoration [decorate[f,w]] of type [decorate[F,W]] applies exactly
    as [f] of type [F] ([undecorate_typing]). *)

From Stdlib Require Import String Lia PeanoNat.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions queries booleans updates paper_ontology conditionals data_types customisation patching.

Set Default Proof Using "Type".

(** * The optimisation *)

(** [untag v] removes all outer tags of the value [v]. *)
Fixpoint untag (v : Combination) : Combination :=
  match v with
  | Fk (Sm (Fk Lf t)) (Fk (Sm (Sm Lf)) (Fk Lf _)) => untag t
  | _ => v
  end.

(** [undecorate v] removes one outer decoration [decorate[f,w]] of [v]. *)
Definition undecorate (v : Combination) : Combination :=
  match v with
  | Fk (Sm (Fk (Sm (Fk Lf (Fk Lf f))) (Fk Lf _))) (Fk (Sm (Sm Lf)) (Sm Lf)) => f
  | _ => v
  end.

(** [optimise_fn e] untags and then undecorates the function part of
    every application node of the expression [e] whose function part is a
    value. *)
Fixpoint optimise_fn (e : Combination) : Combination :=
  match e with
  | Fk e1 e2 =>
      Fk (match e1 with
          | Sm v => Sm (undecorate (untag v))
          | _ => optimise_fn e1
          end) (optimise_fn e2)
  | _ => e
  end.

Lemma untag_tagged : forall t n, untag ('tagged[t,n]) = untag t.
Proof. reflexivity. Qed.

Lemma untag_plain : forall v,
  (forall t n, v <> 'tagged[t,n]) -> untag v = v.
Proof.
  intros v H.
  destruct v as [|a|a b]; cbn [untag]; try reflexivity;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => is_var x; destruct x
         end;
  try reflexivity; exfalso; eapply H; reflexivity.
Qed.

(** [untag] follows the chain of tags down to its innermost carrier. *)
Lemma untag_ind : forall (P : Combination -> Combination -> Prop),
  (forall v, (forall t n, v <> 'tagged[t,n]) -> P v v) ->
  (forall t n w, P t w -> P ('tagged[t,n]) w) ->
  forall v, P v (untag v).
Proof.
  intros P Hplain Htag.
  assert (H : forall k v, tree_size v < k -> P v (untag v)).
  { induction k as [|k IH]; intros v Hk; [lia|].
    destruct (tagged_decide v) as [[t [n ->]]|Hp].
    - rewrite untag_tagged; apply Htag; apply IH; cbn in Hk; lia.
    - rewrite (untag_plain _ Hp); apply Hplain; exact Hp. }
  intro v; apply (H (S (tree_size v))); lia.
Qed.

Lemma undecorate_cases : forall v,
  (exists f w, v = 'decorate[f,w] /\ undecorate v = f) \/ undecorate v = v.
Proof.
  intro v; unfold undecorate;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x
         end; try (right; reflexivity); left; eauto.
Qed.

(** * Evaluation of applications *)

Lemma value_app_eval_iff : forall v1 e2 v,
  Fk (Sm v1) e2 ==> v <-> exists v2, e2 ==> v2 /\ v1 @ v2 ==> v.
Proof.
  intros v1 e2 v; split.
  - intro H; destruct e2 as [|u|a b].
    + inversion H.
    + exists u; split; [apply eval_val|exact H].
    + inversion H; subst; eauto.
  - intros [v2 [H2 H]]; destruct e2 as [|u|a b].
    + inversion H2.
    + inversion H2; subst; exact H.
    + eapply eval_appr; eassumption.
Qed.

Lemma app_eval_iff : forall e1 e2 v,
  Fk e1 e2 ==> v <->
  exists v1 v2, e1 ==> v1 /\ e2 ==> v2 /\ v1 @ v2 ==> v.
Proof.
  intros e1 e2 v; split; [apply eval_pair_inv|].
  intros [v1 [v2 [H1 [H2 H]]]]; eapply eval_pair; eassumption.
Qed.

(** [tagged[t,n] @ u] evaluates exactly as [t @ u]. *)
Lemma tagged_app_eval_iff : forall t n u v,
  'tagged[t,n] @ u ==> v <-> t @ u ==> v.
Proof.
  intros t n u v; split; intro H.
  - inversion H; subst.
    apply app_eval_iff in H4.
    destruct H4 as [v1 [v2 [H1 [H2 H3]]]].
    inversion H1; subst.
    assert (v2 = u) by (eapply eval_deterministic; [exact H2|evaluate]).
    subst; exact H3.
  - apply eval_s; apply app_eval_iff.
    exists t, u; repeat split; [evaluate|evaluate|exact H].
Qed.

(** Untagging the function value does not change any application. *)
Lemma untag_app_eval_iff : forall v u w,
  v @ u ==> w <-> untag v @ u ==> w.
Proof.
  intro v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v _ u w; reflexivity.
  - intros t n x IH u w; rewrite tagged_app_eval_iff; apply IH.
Qed.

(** [decorate[f,w] @ x] evaluates exactly as [f @ x]. *)
Lemma decorate_app_eval_iff : forall f w x r,
  'decorate[f,w] @ x ==> r <-> f @ x ==> r.
Proof.
  intros f w x r; split; intro H.
  - apply wait_eval_inv in H.
    apply app_eval_iff in H; destruct H as [v1 [v2 [H1 [H2 H3]]]].
    pose proof (eval_deterministic _ _ H1 _ (eval_k f w)) as ->.
    inversion H2; subst; exact H3.
  - apply decorate_apply; exact H.
Qed.

Lemma undecorate_app_eval_iff : forall v u r,
  v @ u ==> r <-> undecorate v @ u ==> r.
Proof.
  intros v u r.
  destruct (undecorate_cases v) as [[f [w [-> ->]]]| ->].
  - apply decorate_app_eval_iff.
  - reflexivity.
Qed.

Lemma optimise_value_app_eval_iff : forall v u w,
  v @ u ==> w <-> undecorate (untag v) @ u ==> w.
Proof.
  intros v u w; rewrite untag_app_eval_iff; apply undecorate_app_eval_iff.
Qed.

(** * Optimisation preserves evaluation *)

Theorem optimise_preserves_evaluation : forall e v,
  e ==> v <-> optimise_fn e ==> v.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intro v; cbn [optimise_fn];
    try reflexivity.
  destruct e1 as [|u|a b].
  - split; intro H; inversion H.
  - rewrite !value_app_eval_iff; split; intros [v2 [H2 H]];
      exists v2; split;
      [apply IH2; exact H2|apply (proj1 (optimise_value_app_eval_iff _ _ _)); exact H|
       apply IH2; exact H2|apply (proj2 (optimise_value_app_eval_iff _ _ _)); exact H].
  - rewrite !app_eval_iff; split; intros [v1 [v2 [H1 [H2 H]]]];
      exists v1, v2; repeat split;
      [apply IH1; exact H1|apply IH2; exact H2|exact H|
       apply IH1; exact H1|apply IH2; exact H2|exact H].
Qed.

(** * Optimisation preserves expression typing *)

Section OptimiseTyping.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Notation "F # U" := (tapp @ F @r U) (at level 45, left associativity).

(** The function nametag [fun_nm] = [Lf] is concrete, so it is its own type. *)
Lemma infer_fun_nm : inf AI @ fun_nm ==> Sm fun_nm.
Proof. unfold fun_nm; exact (infer_leaf AI). Qed.


(** With one-round soundness the carrier agrees at every argument type. *)
Lemma tagged_carrier_typing_plain : forall t n F U V,
  plain_intro_sound AI ->
  infer AI @ 'tagged[t,n] ==> Sm F -> F # U ==> Sm V ->
  exists C, infer AI @ t ==> Sm C /\ C # U ==> Sm V.
Proof.
  intros t n F U V Hp HF Happ.
  destruct (infer_tagged_source_inv AI t n F HF)
    as [C [N [E [-> [HC [Hn HI]]]]]].
  exists C; split; [exact HC|].
  assert (HE : E @ tapp @r U ==> Sm V) by (eapply app_abstract_inv; exact Happ).
  eapply Hp; eassumption.
Qed.

Lemma untag_typing_plain : forall v F U V,
  plain_intro_sound AI ->
  infer AI @ v ==> Sm F -> F # U ==> Sm V ->
  exists F', infer AI @ untag v ==> Sm F' /\ F' # U ==> Sm V.
Proof.
  intros v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v _ F U V _ HF Happ; exists F; split; assumption.
  - intros t n x IH F U V Hp HF Happ.
    destruct (tagged_carrier_typing_plain t n F U V Hp HF Happ) as [C [HC HCapp]].
    exact (IH C U V Hp HC HCapp).
Qed.

(** Inversion of the S rule at a plain, unnamed [S2[G,F]]. *)
Local Lemma S_success_inv : forall G F U V,
 (forall E N, 'S2[G,F] <> 'tagged[E,N]) ->
 get_name_test @ ('S2[G,F]) ==> Lf ->
 tapp @ ('S2[G,F]) @r U ==> Sm V ->
 exists A B, tapp @ G @r U ==> Sm A /\
 tapp @ F @r U ==> Sm B /\ tapp @ A @r B ==> Sm V.
Proof.
 intros G F U V HP HN H.
 assert (HA : abstract_case @ ('S2[G,F]) ==> Lf)
   by (unfold abstract_case; apply type_app_abstract_case_S_none; exact HP).
 eapply default_S_inv; exact (app_plain_inv _ _ _ _ HA H).
Qed.

(** The type [decorate[F,W]] applies exactly as [F]: the annotation type
    [W] is consulted only as the discarded argument of [K1 F]. *)
Lemma decorate_type_app_inv : forall F W U V,
  tapp @ 'decorate[F,W] @r U ==> Sm V -> tapp @ F @r U ==> Sm V.
Proof.
  intros F W U V H.
  destruct (S_success_inv ('S2['K1 ('K1 F),'K1 W]) 'I U V
    ltac:(intros; discriminate) ltac:(reject_name) H) as [A [B [HA [HB HAB]]]].
  pose proof (eval_deterministic _ _ HB _ (app_I AI U)) as HBeq.
  inversion HBeq; subst B; clear HB HBeq.
  destruct (S_success_inv ('K1 ('K1 F)) ('K1 W) U A
    ltac:(intros; discriminate) ltac:(reject_name) HA) as [A1 [B1 [HA1 [HB1 HAB1]]]].
  pose proof (eval_deterministic _ _ HA1 _ (app_K AI ('K1 F) U)) as E1.
  pose proof (eval_deterministic _ _ HB1 _ (app_K AI W U)) as E2.
  inversion E1; inversion E2; subst A1 B1.
  pose proof (eval_deterministic _ _ HAB1 _ (app_K AI F W)) as E3.
  inversion E3; subst A; exact HAB.
Qed.

Lemma undecorate_typing : forall v D U V,
  inf AI @ v ==> Sm D -> tapp @ D @r U ==> Sm V ->
  exists F, inf AI @ undecorate v ==> Sm F /\ tapp @ F @r U ==> Sm V.
Proof.
  intros v D U V Hv Happ.
  destruct (undecorate_cases v) as [[f [w [-> ->]]]| ->].
  - destruct (infer_decorate_result_inv AI f w D Hv) as [F [W [-> [Hf _]]]].
    exists F; split; [exact Hf|eapply decorate_type_app_inv; exact Happ].
  - exists D; split; assumption.
Qed.

(** Untagging the function part of an application is sound: under a sound
    declarations every carrier agrees with its eliminator at every argument
    type, so no condition on the expression is needed. *)
Lemma optimise_preserves_expression_typing : forall e T,
  ontology_sound_by_typing AI ->
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ (optimise_fn e) ==> Sm T.
Proof.
  intros e; induction e as [|u _|e1 IH1 e2 IH2]; intros T Hsound H;
    cbn [optimise_fn]; try exact H.
  pose proof (ontology_sound_by_typing_plain AI Hsound) as Hp.
  destruct (infer_expression_fork_inv AI e1 e2 T H)
    as [T1 [T2 [H1 [H2 Happ]]]].
  destruct e1 as [|u|a b].
  - pose proof (eval_deterministic _ _ H1 _ (infer_expression_leaf AI));
      discriminate.
  - apply infer_expression_stem_inv in H1.
    destruct (untag_typing_plain u T1 T2 T Hp H1 Happ) as [F' [HF' HF'app]].
    destruct (undecorate_typing _ _ _ _ HF' HF'app) as [F [HF HFapp]].
    eapply infer_expression_fork;
      [apply infer_expression_stem; exact HF|exact (IH2 T2 Hsound H2)|exact HFapp].
  - eapply infer_expression_fork;
      [exact (IH1 T1 Hsound H1)|exact (IH2 T2 Hsound H2)|exact Happ].
Qed.

(** ** Untagging with some carriers excluded

    A declarations sound for values need not be sound by typing: the
    one-level carriers of Query and Update, their choice carriers, and
    the name tests of IsNamed are not.  Untagging remains sound at every tag
    whose name is not in the list [Bs], and at every tag whose carrier is
    not of one of these shapes ([bad_carrier]). *)
Definition is_triage (t : Combination) : bool :=
  match t with Fk (Fk _ _) _ => true | _ => false end.
Definition is_choice (t : Combination) : bool :=
  match t with Fk (Sm (Fk (Sm (Fk (Sm _) (Fk Lf _))) (Fk Lf _))) i => ceqb i ('I) | _ => false end.
Definition is_name_test_shape (t : Combination) : bool :=
  match t with Fk (Sm (Fk Lf _)) g => ceqb g get_tagname | _ => false end.
Definition bad_carrier (t : Combination) : bool :=
  is_triage t || is_choice t || is_name_test_shape t.

Definition plain_intro_sound_but (Bs : list Combination) : Prop :=
  forall C N E U V,
    (List.In N Bs -> exists t, infer AI @ t ==> Sm C /\ bad_carrier t = false) ->
    AI @ N @r tapp @r C ==> Sm E -> E @ tapp @r U ==> Sm V -> C # U ==> Sm V.

(** [tags_avoid Bs v]: every tag removed by [untag v] whose name is in
    [Bs] has a carrier that is not bad. *)
Fixpoint tags_avoid (Bs : list Combination) (v : Combination) : bool :=
  match v with
  | Fk (Sm (Fk Lf t)) (Fk (Sm (Sm Lf)) (Fk Lf n)) =>
      (negb (List.existsb (ceqb n) Bs) || negb (bad_carrier t)) && tags_avoid Bs t
  | _ => true
  end.

(** [heads_avoid Bs e]: the same for every function part that
    [optimise_fn] untags. *)
Fixpoint heads_avoid (Bs : list Combination) (e : Combination) : bool :=
  match e with
  | Fk e1 e2 =>
      (match e1 with Sm v => tags_avoid Bs v | _ => heads_avoid Bs e1 end)
        && heads_avoid Bs e2
  | _ => true
  end.

Lemma untag_typing_but : forall Bs v F U V,
  plain_intro_sound_but Bs -> List.forallb tag_free Bs = true -> tags_avoid Bs v = true ->
  infer AI @ v ==> Sm F -> F # U ==> Sm V ->
  exists F', infer AI @ untag v ==> Sm F' /\ F' # U ==> Sm V.
Proof.
  intros Bs v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v _ F U V _ _ _ HF Happ; exists F; split; assumption.
  - intros t n x IH F U V Hp HB Ha HF Happ.
    cbn [tags_avoid] in Ha; apply andb_prop in Ha; destruct Ha as [Hn Ht].
    destruct (infer_tagged_source_inv AI t n F HF)
      as [C [N [E [-> [HC [HnN HI]]]]]].
    assert (HE : E @ tapp @r U ==> Sm V) by (eapply app_abstract_inv; exact Happ).
    assert (HCapp : C # U ==> Sm V).
    { eapply Hp; [ |exact HI|exact HE].
        intros HIn; exists t; split; [exact HC|].
        pose proof (proj1 (List.forallb_forall _ _) HB N HIn) as HtN.
        pose proof (infer_tag_free_inv AI n N HnN HtN) as ->.
        assert (Hex : List.existsb (ceqb N) Bs = true)
          by (apply List.existsb_exists; exists N; split; [exact HIn|apply ceqb_refl]).
        rewrite Hex in Hn; cbn in Hn; destruct (bad_carrier t); [discriminate|reflexivity]. }
    exact (IH C U V Hp HB Ht HC HCapp).
Qed.

Lemma optimise_preserves_expression_typing_but : forall B e T,
  plain_intro_sound_but B -> List.forallb tag_free B = true ->
  infer_expression AI @ e ==> Sm T -> heads_avoid B e = true ->
  infer_expression AI @ (optimise_fn e) ==> Sm T.
Proof.
  intros B e; induction e as [|u _|e1 IH1 e2 IH2]; intros T Hp HB H Ha;
    cbn [optimise_fn]; try exact H.
  cbn [heads_avoid] in Ha; apply andb_prop in Ha; destruct Ha as [Ha1 Ha2].
  destruct (infer_expression_fork_inv AI e1 e2 T H)
    as [T1 [T2 [H1 [H2 Happ]]]].
  destruct e1 as [|u|a b].
  - pose proof (eval_deterministic _ _ H1 _ (infer_expression_leaf AI));
      discriminate.
  - apply infer_expression_stem_inv in H1.
    destruct (untag_typing_but B u T1 T2 T Hp HB Ha1 H1 Happ) as [F' [HF' HF'app]].
    destruct (undecorate_typing _ _ _ _ HF' HF'app) as [F [HF HFapp]].
    eapply infer_expression_fork;
      [apply infer_expression_stem; exact HF|exact (IH2 T2 Hp HB H2 Ha2)|exact HFapp].
  - eapply infer_expression_fork;
      [exact (IH1 T1 Hp HB H1 Ha1)|exact (IH2 T2 Hp HB H2 Ha2)|exact Happ].
Qed.

End OptimiseTyping.

(** The paper declarations are sound by typing at every name but those
    of Query, Update and IsNamed ([paper_plain_intro_sound_but]). *)
Definition paper_excluded : list Combination :=
  List.cons query_nm (List.cons update_nm (List.cons is_named_nm List.nil)).

Lemma paper_excluded_tag_free : List.forallb tag_free paper_excluded = true.
Proof. vm_compute; reflexivity. Qed.

(** A value of an IfNamed type is an if_named conditional. *)
Lemma choice_carrier_shape : forall (AI : Decl) t N F D,
  inf AI @ t ==> Sm (IfNamed N F D) -> is_choice t = true.
Proof.
  intros AI t N F D Ht; unfold IfNamed, IsNamed in Ht.
  Local Ltac plain_fork H :=
    let X := fresh "X" in
    pose proof (fun Hn => infer_plain_fork_inv _ _ _ _ Hn H) as X;
    specialize (X ltac:(intros ? ? ?; discriminate)).
  plain_fork Ht; destruct X as [l [r [-> [Hl Hr]]]].
  pose proof (infer_tag_free_inv AI r ('I) Hr eq_refl) as ->.
  destruct (infer_stem_result_inv AI l _ Hl) as [g [-> Hg]].
  plain_fork Hg; destruct X as [g1 [g2 [-> [Hg1 Hg2]]]].
  destruct (infer_stem_result_inv AI g1 _ Hg1) as [k [-> Hk]].
  destruct (infer_K1_inv AI g2 _ Hg2) as [d' [-> _]].
  plain_fork Hk; destruct X as [k1 [k2 [-> [Hk1 Hk2]]]].
  destruct (infer_stem_result_inv AI k1 _ Hk1) as [w [-> _]].
  destruct (infer_K1_inv AI k2 _ Hk2) as [f' [-> _]].
  reflexivity.
Qed.

Lemma paper_plain_intro_sound_excl :
  plain_intro_sound_but paper_ontology paper_excluded.
Proof.
  intros C N E U V HIn HD HE.
  apply (paper_plain_intro_sound_but C N E U V); [ | |exact HD|exact HE].
  - intros HN; destruct HIn as [t [Ht Hnt]];
      [destruct HN as [->| ->]; [left|right; left]; reflexivity|].
    unfold bad_carrier in Hnt; apply Bool.orb_false_iff in Hnt as [Hnt Hnn];
      apply Bool.orb_false_iff in Hnt as [Htr Hch].
    split; [|split].
    + intros B ->.
      pose proof Ht as Ht'; unfold query_one_level in Ht'.
      destruct (infer_plain_fork_inv paper_ontology _ (Fk B ('Query[B]))
        ('Query['Query[B]]) ltac:(intros;discriminate) Ht') as [l [r [-> [Hl _]]]].
      destruct (infer_plain_fork_inv paper_ontology _ B ('Query[B])
        ltac:(intros;discriminate) Hl) as [a [b [-> _]]].
      discriminate.
    + intros ->.
      pose proof Ht as Ht'; unfold update_one_level in Ht'.
      destruct (infer_plain_fork_inv paper_ontology _ (Fk Lf (Lf 'C ('Update)))
        (update_fork ('Update)) ltac:(intros;discriminate) Ht') as [l [r [-> [Hl _]]]].
      destruct (infer_plain_fork_inv paper_ontology _ Lf (Lf 'C ('Update))
        ltac:(intros;discriminate) Hl) as [a [b [-> _]]].
      discriminate.
    + intros N' F D ->.
      rewrite (choice_carrier_shape _ _ _ _ _ Ht) in Hch; discriminate.
  - intros ->; destruct HIn as [t [Ht Hnt]]; [right; right; left; reflexivity|].
    intros M ->.
    destruct (infer_name_test_inv paper_ontology t M Ht) as [m [-> _]].
    unfold bad_carrier in Hnt; apply Bool.orb_false_iff in Hnt as [_ Hnn].
    change (ceqb get_tagname get_tagname = false) in Hnn; rewrite ceqb_refl in Hnn; discriminate.
Qed.

(** * The optimisation as a program *)

Open Scope string_scope.

(** [untag_program @ v]: if [get_tagged] finds [tagged[C,N]], recurse on
    [C], else return [v]. *)
Definition untag_body_package :
  { t | to_tree
    (\"rec" (\"v"
       (''triage [
          Ref "v",
          ''triage [Val Lf, Val Lf, \"C" (\"N" (Ref "rec" @@ Ref "C"))],
          Val Lf ]
        @@ (Val get_tagged @@ Ref "v")))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition untag_body := Eval cbn in proj1_sig untag_body_package.
Definition untag_program := Z untag_body.

Lemma untag_program_eval : forall v, untag_program @ v ==> untag v.
Proof.
  intro v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v Hp.
    pose proof (get_tagged_none v Hp) as Hg.
    unfold untag_program; eapply Z_unfold; cbv -[get_tagged Z]; evaluate.
  - intros t n w IH.
    pose proof (get_tagged_some t n) as Hg.
    unfold untag_program; eapply Z_unfold; cbv -[get_tagged Z]; evaluate.
Qed.

(** [undecorate_program @ v]: if [get_decorate] finds [decorate[F,W]],
    return [F], else return [v]. *)
Definition undecorate_program_package :
  { t | to_tree
    (\"v"
       (''triage [
          Ref "v",
          ''triage [Val Lf, Val Lf, \"F" (\"W" (Ref "F"))],
          Val Lf ]
        @@ (Val get_decorate @@ Ref "v"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition undecorate_program := Eval cbn in proj1_sig undecorate_program_package.

Lemma undecorate_program_eval : forall v,
  undecorate_program @ v ==> undecorate v.
Proof.
  intro v; destruct (undecorate_cases v) as [[f [w [-> ->]]]|Hv].
  - pose proof (get_decorate_some f w) as Hg.
    unfold undecorate_program; cbv -[get_decorate]; evaluate.
  - assert (Hn : forall E D, v <> 'decorate[E,D]).
    { intros E D ->; cbn in Hv.
      apply (f_equal tree_size) in Hv; cbn in Hv; lia. }
    pose proof (get_decorate_none v Hn) as Hg; rewrite Hv.
    unfold undecorate_program; cbv -[get_decorate]; evaluate.
Qed.

(** [optimise @ e]: a leaf or a stem is returned unchanged; a fork
    [Fk e1 e2] becomes [Fk e1' (optimise @ e2)], where [e1'] is [e1] for a
    leaf, [Sm (undecorate (untag v))] for a stem [Sm v], and
    [optimise @ e1] for a fork. *)
Definition optimise_body_package :
  { t | to_tree
    (\"rec"
       (''triage [
          Val Lf,
          Val Lf,
          \"e1" (\"e2"
            (Val Lf
               @@ (''triage [
                     Val Lf,
                     \"u" (Val Lf @@ (Val undecorate_program
                                        @@ (Val untag_program @@ Ref "u"))),
                     \"a" (\"b" (Ref "rec" @@ (Val Lf @@ Ref "a" @@ Ref "b")))]
                   @@ Ref "e1")
               @@ (Ref "rec" @@ Ref "e2"))) ])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition optimise_body := Eval cbn in proj1_sig optimise_body_package.
Definition optimise := Z optimise_body.

Lemma optimise_eval : forall e, optimise @ e ==> optimise_fn e.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2].
  - unfold optimise; eapply Z_unfold; cbv -[untag_program undecorate_program Z]; evaluate.
  - unfold optimise; eapply Z_unfold; cbv -[untag_program undecorate_program Z]; evaluate.
  - destruct e1 as [|u|a b]; cbn [optimise_fn].
    + unfold optimise; eapply Z_unfold; cbv -[untag_program undecorate_program Z]; evaluate.
    + pose proof (untag_program_eval u) as Hu.
      pose proof (undecorate_program_eval (untag u)) as Hd.
      unfold optimise; eapply Z_unfold; cbv -[untag_program undecorate_program Z]; evaluate.
    + unfold optimise; eapply Z_unfold; cbv -[untag_program undecorate_program Z]; evaluate.
Qed.

Lemma untag_program_concrete : concrete untag_program.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma undecorate_program_concrete : concrete undecorate_program.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma optimise_concrete : concrete optimise.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

(** * The running example

    The pending query [paid_over_57 @ department_2025]
    applies a tagged abstract program.  Optimisation drops its tag, and
    the optimised expression has the same type [List[Employee]] and the
    same value [paid_57_in_2025]. *)


(** * The Boolean example

    [tt = tagged[fst, bool_nm]], so optimisation turns [tt @ (u*v)] into
    [fst @ (u*v)].  At the typed instance [u = ff] and [v = tt] (both of
    type [Bool]), both expressions have type [Bool] and value [ff]. *)

Lemma optimised_boolean_example :
  optimise_fn ('tt @ ('ff '* 'tt)) = 'fst @ ('ff '* 'tt) /\
  infer_expression paper_ontology @ ('tt @ ('ff '* 'tt)) ==> Sm ('Bool) /\
  infer_expression paper_ontology @ ('fst @ ('ff '* 'tt)) ==> Sm ('Bool) /\
  'tt @ ('ff '* 'tt) ==> 'ff /\
  'fst @ ('ff '* 'tt) ==> 'ff.
Proof.
  assert (Htyped :
    infer_expression paper_ontology @ ('tt @ ('ff '* 'tt)) ==> Sm ('Bool)).
  { eapply infer_expression_fork.
    - apply infer_expression_stem; apply tt_infer;
        exact paper_ontology_supports_booleans.
    - apply infer_expression_stem; apply infer_product_value;
        [apply ff_infer|apply tt_infer];
        exact paper_ontology_supports_booleans.
    - apply type_app_abstract; apply bool_eliminator_some. }
  assert (Hfst : 'fst @ ('ff '* 'tt) ==> 'ff) by apply fst_pair.
  assert (Hopt : optimise_fn ('tt @ ('ff '* 'tt)) = 'fst @ ('ff '* 'tt))
    by reflexivity.
  split; [exact Hopt|split; [exact Htyped|split; [|split]]].
  - rewrite <- Hopt; apply (optimise_preserves_expression_typing_but paper_ontology paper_excluded _ _
      paper_plain_intro_sound_excl paper_excluded_tag_free Htyped);
      vm_compute; reflexivity.
  - apply (proj2 (optimise_preserves_evaluation _ _)); rewrite Hopt;
      exact Hfst.
  - exact Hfst.
Qed.

(** * The function example

    [typed_neg = lam[neg,tt] = tagged[decorate[neg,tt], fun_nm]], so
    optimisation turns [typed_neg @ tt] into [neg @ tt].
    Both have type [Bool] and value [ff]. *)


Unset Default Proof Using.

(**********************************************************************)
(* Further optimisations: projections on actual pairs, ghost erasure, *)
(* and their composition with tag erasure.                            *)
(**********************************************************************)

(** Each transformation follows the discipline of [optimise_fn]: it
    recurses through application nodes of an expression and never looks
    inside a value.

    - [project_fn] replaces [fst @ (u*v)] by the value [u] and
      [snd @ (u*v)] by the value [v].
    - [unghost_fn] replaces the function part [decorate[f,w]] of an
      application by [f].
    - [optimise_all_fn] optimises, then unghosts, then projects; since
      [optimise_fn] already undecorates once, [unghost_fn] removes only
      a second decoration.

    Evaluation is preserved in both directions, with no hypotheses.
    Expression typing is preserved by [project_fn] and [unghost_fn] with
    no hypotheses (pairs and decorations are typed by the concrete
    rules); [optimise_all_fn] inherits the soundness hypothesis
    [ontology_sound] from [optimise_fn]. *)

From Stdlib Require Import String Lia PeanoNat.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans paper_ontology.

Set Default Proof Using "Type".

(** * E4: projections on actual pairs *)

(** [project_redex e1 e2] recognises the application of [fst] or [snd]
    to an actual pair value. *)
Definition project_redex (e1 e2 : Combination) : option Combination :=
  match e1, e2 with
  | Sm 'fst, Sm (u '* v) => Some u
  | Sm 'snd, Sm (u '* v) => Some v
  | _, _ => None
  end.

Fixpoint project_fn (e : Combination) : Combination :=
  match e with
  | Fk e1 e2 =>
      match project_redex e1 e2 with
      | Some w => Sm w
      | None => Fk (project_fn e1) (project_fn e2)
      end
  | _ => e
  end.

Lemma project_redex_some : forall e1 e2 w,
  project_redex e1 e2 = Some w ->
  (exists v, e1 = Sm 'fst /\ e2 = Sm (w '* v)) \/
  (exists u, e1 = Sm 'snd /\ e2 = Sm (u '* w)).
Proof.
  intros e1 e2 w H; unfold project_redex in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x
         end; try discriminate; inversion H; subst; eauto.
Qed.

Lemma project_redex_eval : forall e1 e2 w v,
  project_redex e1 e2 = Some w -> (Fk e1 e2 ==> v <-> v = w).
Proof.
  intros e1 e2 w v H.
  destruct (project_redex_some _ _ _ H) as [[y [-> ->]]|[x [-> ->]]];
    split; intro Hv.
  - eapply eval_deterministic; [exact Hv|apply fst_pair].
  - subst; apply fst_pair.
  - eapply eval_deterministic; [exact Hv|apply snd_pair].
  - subst; apply snd_pair.
Qed.

Lemma project_preserves_evaluation : forall e v,
  e ==> v <-> project_fn e ==> v.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intro v; cbn [project_fn];
    try reflexivity.
  destruct (project_redex e1 e2) as [w|] eqn:Hr.
  - rewrite (project_redex_eval _ _ _ _ Hr); split; intro H.
    + subst; apply eval_val.
    + inversion H; reflexivity.
  - rewrite !app_eval_iff; split; intros [v1 [v2 [H1 [H2 H]]]];
      exists v1, v2; repeat split;
      [apply IH1; exact H1|apply IH2; exact H2|exact H|
       apply IH1; exact H1|apply IH2; exact H2|exact H].
Qed.

Section ProjectTyping.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Abbreviation inf := (infer AI).

(** Pairs are typed by the concrete rules: [u*v : U*V]. *)
Lemma infer_pair : forall u v U V,
  inf @ u ==> Sm U -> inf @ v ==> Sm V -> inf @ (u '* v) ==> Sm (U '* V).
Proof.
  intros u v U V Hu Hv.
  eapply infer_fork.
  - eapply infer_stem. eapply infer_fork.
    + apply infer_tag_free; reflexivity.
    + apply infer_K1; exact Hu.
    + apply app_stem; apply type_app_stem_structural; intros; discriminate.
  - apply infer_K1; exact Hv.
  - apply app_stem; apply type_app_stem_structural; intros; discriminate.
Qed.

Lemma infer_pair_inv : forall u v P,
  inf @ (u '* v) ==> Sm P ->
  exists U V, inf @ u ==> Sm U /\ inf @ v ==> Sm V /\ P = U '* V.
Proof.
  intros u v P H.
  destruct (infer_fork_inv _ _ _ _ H) as [A [B [Ha [Hb _]]]].
  destruct (infer_stem_inv _ _ _ Ha) as [A' [-> Ha']].
  destruct (infer_fork_inv _ _ _ _ Ha') as [C [D [_ [Hd _]]]].
  destruct (infer_fork_inv _ _ _ _ Hd) as [L [U [_ [Hu _]]]].
  destruct (infer_fork_inv _ _ _ _ Hb) as [L' [V [_ [Hv _]]]].
  exists U, V; repeat split; try assumption.
  pose proof (eval_deterministic _ _ H _ (infer_pair u v U V Hu Hv)) as Heq.
  inversion Heq; reflexivity.
Qed.

(** Projections at the type level mirror evaluation. *)
Lemma fst_pair_type : forall U V, tapp @ 'fst @r (U '* V) ==> Sm U.
Proof.
  intros U V.
  eapply app_S; [intros; discriminate|reject_name|apply app_I|apply app_K|].
  eapply app_S; [intros; discriminate|reject_name| |apply app_K|apply app_K].
  eapply app_S; [intros; discriminate|reject_name|apply app_I|apply app_K|].
  apply app_true.
Qed.

Lemma snd_pair_type : forall U V, tapp @ 'snd @r (U '* V) ==> Sm V.
Proof.
  intros U V.
  eapply app_S; [intros; discriminate|reject_name|apply app_I|apply app_K|].
  eapply app_S; [intros; discriminate|reject_name| |apply app_K|apply app_I].
  eapply app_S; [intros; discriminate|reject_name|apply app_I|apply app_K|].
  apply app_K.
Qed.

(** The key step: a typed projection redex has the type of its result. *)
Lemma project_redex_typing : forall e1 e2 w T,
  project_redex e1 e2 = Some w ->
  infer_expression AI @ Fk e1 e2 ==> Sm T ->
  inf @ w ==> Sm T.
Proof.
  intros e1 e2 w T Hr H.
  destruct (infer_expression_fork_inv AI e1 e2 T H)
    as [T1 [T2 [H1 [H2 Happ]]]].
  destruct (project_redex_some _ _ _ Hr) as [[y [-> ->]]|[x [-> ->]]];
    apply infer_expression_stem_inv in H1;
    apply infer_expression_stem_inv in H2;
    destruct (infer_pair_inv _ _ _ H2) as [U [V [Hu [Hv ->]]]].
  - pose proof (eval_deterministic _ _ H1 _
      (infer_tag_free AI 'fst ltac:(reflexivity))) as HT1;
    inversion HT1; subst T1.
    pose proof (eval_deterministic _ _ Happ _ (fst_pair_type U V)) as HT.
    inversion HT; subst; exact Hu.
  - pose proof (eval_deterministic _ _ H1 _
      (infer_tag_free AI 'snd ltac:(reflexivity))) as HT1;
    inversion HT1; subst T1.
    pose proof (eval_deterministic _ _ Happ _ (snd_pair_type U V)) as HT.
    inversion HT; subst; exact Hv.
Qed.

Lemma project_preserves_expression_typing : forall e T,
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ (project_fn e) ==> Sm T.
Proof.
  intros e; induction e as [|u _|e1 IH1 e2 IH2]; intros T H;
    cbn [project_fn]; try exact H.
  destruct (project_redex e1 e2) as [w|] eqn:Hr.
  - apply infer_expression_stem; eapply project_redex_typing; eassumption.
  - destruct (infer_expression_fork_inv AI e1 e2 T H)
      as [T1 [T2 [H1 [H2 Happ]]]].
    eapply infer_expression_fork;
      [exact (IH1 T1 H1)|exact (IH2 T2 H2)|exact Happ].
Qed.

End ProjectTyping.

(** * E5: ghost erasure *)

(** [unghost_fn e] undecorates the function part of every application
    node of [e] whose function part is a value. *)
Fixpoint unghost_fn (e : Combination) : Combination :=
  match e with
  | Fk e1 e2 =>
      Fk (match e1 with
          | Sm v => Sm (undecorate v)
          | _ => unghost_fn e1
          end) (unghost_fn e2)
  | _ => e
  end.

Lemma unghost_preserves_evaluation : forall e v,
  e ==> v <-> unghost_fn e ==> v.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intro v; cbn [unghost_fn];
    try reflexivity.
  destruct e1 as [|u|a b].
  - split; intro H; inversion H.
  - rewrite !value_app_eval_iff; split; intros [v2 [H2 H]];
      exists v2; split;
      [apply IH2; exact H2|apply (proj1 (undecorate_app_eval_iff _ _ _)); exact H|
       apply IH2; exact H2|apply (proj2 (undecorate_app_eval_iff _ _ _)); exact H].
  - rewrite !app_eval_iff; split; intros [v1 [v2 [H1 [H2 H]]]];
      exists v1, v2; repeat split;
      [apply IH1; exact H1|apply IH2; exact H2|exact H|
       apply IH1; exact H1|apply IH2; exact H2|exact H].
Qed.

Section UnghostTyping.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Abbreviation inf := (infer AI).

Lemma unghost_preserves_expression_typing : forall e T,
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ (unghost_fn e) ==> Sm T.
Proof.
  intros e; induction e as [|u _|e1 IH1 e2 IH2]; intros T H;
    cbn [unghost_fn]; try exact H.
  destruct (infer_expression_fork_inv AI e1 e2 T H)
    as [T1 [T2 [H1 [H2 Happ]]]].
  destruct e1 as [|u|a b].
  - pose proof (eval_deterministic _ _ H1 _ (infer_expression_leaf AI));
      discriminate.
  - apply infer_expression_stem_inv in H1.
    destruct (undecorate_typing AI u T1 T2 T H1 Happ) as [F [HF HFapp]].
    eapply infer_expression_fork;
      [apply infer_expression_stem; exact HF|exact (IH2 T2 H2)|exact HFapp].
  - eapply infer_expression_fork;
      [exact (IH1 T1 H1)|exact (IH2 T2 H2)|exact Happ].
Qed.

End UnghostTyping.

(** * E8: composition *)

Definition optimise_all_fn (e : Combination) : Combination :=
  project_fn (unghost_fn (optimise_fn e)).

Lemma optimise_all_preserves_evaluation : forall e v,
  e ==> v <-> optimise_all_fn e ==> v.
Proof.
  intros e v; unfold optimise_all_fn.
  rewrite optimise_preserves_evaluation, unghost_preserves_evaluation,
    project_preserves_evaluation; reflexivity.
Qed.

Lemma optimise_all_preserves_expression_typing : forall (AI : Decl) e T,
  ontology_sound_by_typing AI ->
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ (optimise_all_fn e) ==> Sm T.
Proof.
  intros AI e T Hsound H; unfold optimise_all_fn.
  apply project_preserves_expression_typing,
    unghost_preserves_expression_typing,
    optimise_preserves_expression_typing; assumption.
Qed.

Lemma optimise_all_preserves_expression_typing_but : forall (AI : Decl) B e T,
  plain_intro_sound_but AI B -> List.forallb tag_free B = true ->
  infer_expression AI @ e ==> Sm T -> heads_avoid B e = true ->
  infer_expression AI @ (optimise_all_fn e) ==> Sm T.
Proof.
  intros AI B e T Hp HB H Ha; unfold optimise_all_fn.
  apply project_preserves_expression_typing,
    unghost_preserves_expression_typing.
  eapply optimise_preserves_expression_typing_but; eassumption.
Qed.

(** ** Examples *)

Local Transparent typed_neg.

(** [tt @ (u*v)] becomes [fst @ (u*v)] by untagging, and then [u]. *)
Lemma optimise_all_tt_pair : forall u v,
  optimise_fn ('tt @ (u '* v)) = 'fst @ (u '* v) /\
  optimise_all_fn ('tt @ (u '* v)) = Sm u.
Proof. intros; split; reflexivity. Qed.

Lemma typed_neg_tt_typed :
  infer_expression paper_ontology @ (typed_neg @ 'tt) ==> Sm ('Bool).
Proof.
  eapply infer_expression_fork.
  - apply infer_expression_stem;
      apply typed_neg_infer; exact paper_ontology_supports_booleans.
  - apply infer_expression_stem;
      apply tt_infer; exact paper_ontology_supports_booleans.
  - apply app_abstract; apply funty_eliminator_eval.
Qed.

(** The paper's example: [typed_neg @ tt] becomes [neg @ tt], with the
    same type [Bool] and the same value [ff]. *)
Lemma optimised_neg_example :
  optimise_fn (typed_neg @ 'tt) = neg @ 'tt /\
  optimise_all_fn (typed_neg @ 'tt) = neg @ 'tt /\
  infer_expression paper_ontology @ optimise_all_fn (typed_neg @ 'tt) ==>
    Sm ('Bool) /\
  typed_neg @ 'tt ==> 'ff /\
  optimise_all_fn (typed_neg @ 'tt) ==> 'ff.
Proof.
  assert (Heq : optimise_all_fn (typed_neg @ 'tt) = neg @ 'tt)
    by reflexivity.
  split; [reflexivity|split; [exact Heq|split; [|split]]].
  - apply (optimise_all_preserves_expression_typing_but paper_ontology paper_excluded _ _
      paper_plain_intro_sound_excl paper_excluded_tag_free typed_neg_tt_typed);
      vm_compute; reflexivity.
  - apply (proj2 (optimise_all_preserves_evaluation _ _)).
    rewrite Heq; exact neg_tt.
  - rewrite Heq; exact neg_tt.
Qed.

(** [optimise] is its own type, it erases the tag
    and ghost of [typed_neg], and it preserves the types of expressions
    whose heads avoid the carriers that are not sound by typing
    ([heads_avoid paper_excluded]). *)
Theorem optimise_typed :
  infer paper_ontology @ optimise ==> Sm optimise /\
  optimise @ (('Kq zero) @ 'tt) ==> ('K1 zero) @ 'tt /\
  (forall e e' T, heads_avoid paper_excluded e = true ->
     infer_expression paper_ontology @ e ==> Sm T ->
     optimise @ e ==> e' -> infer_expression paper_ontology @ e' ==> Sm T).
Proof.
  split; [apply infer_tag_free, concrete_tag_free, optimise_concrete|split].
  - assert (HQ : optimise_fn (('Kq zero) @ 'tt) = ('K1 zero) @ 'tt) by (vm_compute; reflexivity).
    rewrite <- HQ; apply optimise_eval.
  - intros e e' T Ha H He.
    rewrite (eval_deterministic _ _ He _ (optimise_eval e)).
    exact (optimise_preserves_expression_typing_but paper_ontology paper_excluded e T
      paper_plain_intro_sound_excl paper_excluded_tag_free H Ha).
Qed.


Unset Default Proof Using.

(**********************************************************************)
(* E7: head erasure inside fixfunctions (typing first).               *)
(**********************************************************************)

(** Principle: an optimisation must preserve typing; preserving behaviour is a bonus.

    [head_erase] rewrites inside a value.  At every head-of-composition
    position, [S2[K1 c, g]] (that is [c 'C g]) and [S1 (K1 c)], the head
    program [c] is replaced by [erase c = undecorate (untag c)]; elsewhere
    it recurses into the children.  Two choices:

    - It recurses into the head program before erasing it
      ([erase (head_erase c)]), so that heads nested inside the head program
      are erased too.  On a tagged or decorated head, [head_erase] keeps
      the outer tag or decoration, so [erase] still removes it afterwards
      (e.g. [erase (head_erase typed_neg) = neg]).

    - A tag [tagged[t,n] = S2[K1 t, label[n]]] has the shape of a
      composition, but it is not optimised: its carrier [t] is only
      recursed into, and its label is kept.  Without this exception every
      [lam[f,u] = tagged[decorate[f,u],fun_nm]] would lose its ghost, and
      direct function introduction would fail.

    Results.

    - Stage 1 (dither).  Applied literally to the whole carrier of
      [dither_fn = fix[dither_function]], [head_erase] also erases the
      functional [dither_function], which sits at the head of the
      composition [dither_function 'C tagged_fun] in the Z-body.  The fix
      rule reads the functional's type syntactically, so the result has no
      type under any declarations ([dither_whole_erase_untypable]).  The right
      optimisation keeps the functional's tag and ghost and erases inside
      its body: [fix_erase].  The result [erased_dither] has type [Bool -> Bool],
      and [erased_dither @ tt] has type [Bool].
    - Stage 2 (addition, recursion.v).  [head_erase] replaces the typed
      successor (a [lam]) at its head position by its body.  The optimised
      addition has the same type [Nat -> Nat -> Nat] and the same values
      on small arguments.
    - Stage 3 (general).  The general statement is false: the structural
      type of a partial composition [S1 (K1 c)] records the type of [c],
      and a function may return such a value
      ([head_erase_changes_lam_type]).  What holds is preservation when
      the composition's type is only applied: at the root of a function
      body ([lam_root_erase_typing], [fix_root_erase_typing]), along the
      right spine of a chain of compositions ([lam_spine_erase_typing],
      [fix_spine_erase_typing], applied to the run-time chains of E7a in
      [chain_head_erase_typing]), and for the typed composition functional
      [typed_compose_with] ([compose_with_erase_typing]), all for every
      sound declarations. *)

From Stdlib Require Import String Lia PeanoNat.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans data_types recursion paper_ontology.

Set Default Proof Using "Type".
Open Scope string_scope.

(** * The rewrite *)

Definition erase (c : Combination) : Combination := undecorate (untag c).

Fixpoint head_erase (t : Combination) : Combination :=
  match t with
  | Fk (Sm (Fk Lf c)) (Fk (Sm (Sm Lf)) (Fk Lf n)) =>
      (* a tag [tagged[c,n]]: keep it, recurse into the carrier *)
      Fk (Sm (Fk Lf (head_erase c))) (Fk (Sm (Sm Lf)) (Fk Lf n))
  | Fk (Sm (Fk Lf c)) g =>
      (* a composition [c 'C g] *)
      Fk (Sm (Fk Lf (erase (head_erase c)))) (head_erase g)
  | Sm (Sm (Fk Lf c)) =>
      (* a partial composition [S1 (K1 c)] *)
      Sm (Sm (Fk Lf (erase (head_erase c))))
  | Lf => Lf
  | Sm a => Sm (head_erase a)
  | Fk a b => Fk (head_erase a) (head_erase b)
  end.

(** The optimisation of a typed function value keeps the function tag and
    the ghost of its own [lam], and erases inside the body. *)
Definition fix_erase (b w : Combination) : Combination :=
  fix_function (lam (head_erase b) w).

(** * Behaviour of erasure at a head *)

Lemma erase_app_eval_iff : forall c u r, c @ u ==> r <-> erase c @ u ==> r.
Proof.
  intros c u r; unfold erase.
  rewrite (untag_app_eval_iff c u r).
  apply undecorate_app_eval_iff.
Qed.

(** * Inversion lemmas for function introduction *)

Section Inversions.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Abbreviation inf := (infer AI).

Lemma stem_plain : forall F U R,
  (forall C N, Fk F U <> 'tagged[C,N]) ->
  tapp @ Sm F @r U ==> Sm R -> R = Fk F U.
Proof.
  intros F U R Hp H.
  exact (type_app_stem_structural_inv AI _ _ _ _ Hp
    (typing.type_app_stem_inv _ _ _ _ H)).
Qed.

Lemma infer_Z_inv : forall X C,
  inf @ Z X ==> Sm C -> exists X', C = Z X' /\ inf @ X ==> Sm X'.
Proof.
  intros X C H; unfold Z in H.
  destruct (infer_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 H12]]]].
  destruct (infer_stem_inv AI _ _ H1) as [A' [-> HA]].
  pose proof (eval_deterministic _ _ H2 _ (infer_I AI)) as E2.
  inversion E2; subst T2; clear E2 H2.
  destruct (infer_fork_inv AI _ _ _ HA) as [P [Q [HP [HQ HPQ]]]].
  pose proof (eval_deterministic _ _ HP _
    (infer_tag_free AI (Sm ('K1 dup_z)) ltac:(tag_free_tac))) as EP.
  inversion EP; subst P; clear EP HP.
  destruct (infer_K1_result_inv AI _ _ HQ) as [G [-> HG]].
  apply stem_plain in HPQ; [subst A'|intros; discriminate].
  apply stem_plain in H12; [subst C|intros; discriminate].
  destruct (infer_fork_inv AI _ _ _ HG) as [P2 [Q2 [HP2 [HQ2 HPQ2]]]].
  destruct (infer_stem_inv AI _ _ HP2) as [A2 [-> HA']].
  pose proof (eval_deterministic _ _ HQ2 _ (infer_tag_free AI bz ltac:(tag_free_tac))) as EQ.
  inversion EQ; subst Q2; clear EQ HQ2.
  destruct (infer_K1_result_inv AI _ _ HA') as [X' [-> HX]].
  apply stem_plain in HPQ2; [subst G|intros; discriminate].
  exists X'; split; [reflexivity|exact HX].
Qed.

Lemma tagged_fun_not_label : forall n, tagged_fun <> 'label[n].
Proof. intros n H; unfold tagged_fun in H; discriminate. Qed.

(** Inference of a composition whose right part is not a label. *)
Lemma infer_compose_inv : forall g f C,
  (forall n, f <> 'label[n]) ->
  inf @ (g 'C f) ==> Sm C ->
  exists G F, C = G 'C F /\ inf @ g ==> Sm G /\ inf @ f ==> Sm F.
Proof.
  intros g f C Hf H.
  destruct (infer_fork_inv AI _ _ _ H) as [T1 [F [H1 [H2 H12]]]].
  destruct (infer_stem_inv AI _ _ H1) as [K [-> HK]].
  destruct (infer_K1_result_inv AI _ _ HK) as [G [-> HG]].
  assert (Hplain : forall E N, Fk (Sm ('K1 G)) F <> 'tagged[E,N]).
  { intros E N HE; inversion HE; subst.
    destruct (infer_tag_right_inv AI _ _ H2) as [n [-> _]].
    exact (Hf n eq_refl). }
  pose proof (type_app_stem_structural_inv AI _ _ _ _ Hplain
    (typing.type_app_stem_inv _ _ _ _ H12)) as ->.
  exists G, F; repeat split; assumption.
Qed.

Lemma infer_compose : forall g f G F,
  (forall n, f <> 'label[n]) ->
  inf @ g ==> Sm G -> inf @ f ==> Sm F ->
  inf @ (g 'C f) ==> Sm (G 'C F).
Proof.
  intros g f G F Hf HG HF.
  eapply infer_fork; [eapply infer_stem; eapply infer_K1; exact HG|exact HF|].
  apply type_app_stem_ev; apply type_app_stem_structural.
  intros E N HE; inversion HE; subst.
  destruct (infer_tag_right_inv AI _ _ HF) as [n [-> _]].
  exact (Hf n eq_refl).
Qed.

(** Converse of [infer_lam]: a typed [lam[f,u]] has a body type that maps
    the witness type to the result type.  No soundness hypothesis is
    needed, since introduction at [fun_nm] is the core rule. *)
Lemma lam_typing_inv : forall f u T,
  inf @ lam f u ==> Sm T ->
  exists F U V, T = U --> V /\ inf @ f ==> Sm F /\ inf @ u ==> Sm U /\
    tapp @ F @r U ==> Sm V.
Proof.
  intros f u T H; unfold lam in H.
  destruct (infer_tagged_source_inv AI _ _ _ H)
    as [C [N [E [-> [HC [HN HI]]]]]].
  pose proof (eval_deterministic _ _ HN _ (infer_fun_nm AI)) as EN.
  inversion EN; subst N; clear EN HN.
  apply (function_declared_inv AI) in HI.
  destruct (function_abstractor_success_inv _ _ _ HI)
    as [[F [U [V [-> [HF ->]]]]] | [U [V [-> ->]]]].
  - destruct (infer_decorate_result_inv AI _ _ _ HC)
      as [F' [U' [Heq [Hf Hu]]]].
    inversion Heq; subst F' U'.
    exists F, U, V; repeat split; assumption.
  - exfalso.
    destruct (infer_decorate_result_inv AI _ _ _ HC)
      as [F' [U' [Heq _]]].
    unfold Z in Heq; discriminate Heq.
Qed.

(** Converse of [infer_fix_function]. *)
Lemma fix_function_typing_inv : forall f T,
  inf @ fix_function f ==> Sm T ->
  exists U V, T = U --> V /\ inf @ f ==> Sm ((U --> V) --> (U --> V)).
Proof.
  intros f T H; unfold fix_function in H.
  destruct (infer_tagged_source_inv AI _ _ _ H)
    as [C [N [E [-> [HC [HN HI]]]]]].
  pose proof (eval_deterministic _ _ HN _ (infer_fun_nm AI)) as EN.
  inversion EN; subst N; clear EN HN.
  apply (function_declared_inv AI) in HI.
  destruct (infer_Z_inv _ _ HC) as [X' [-> HX]].
  destruct (function_abstractor_success_inv _ _ _ HI)
    as [[F [U [V [Heq _]]]] | [U [V [Heq ->]]]].
  - exfalso; unfold Z in Heq; discriminate Heq.
  - unfold Z in Heq; inversion Heq; subst X'.
    destruct (infer_compose_inv _ _ _ tagged_fun_not_label HX)
      as [G [F [Heq' [HG _]]]].
    inversion Heq'; subst G.
    exists U, V; split; [reflexivity|exact HG].
Qed.

(** The type of [fix[lam[b,w]]] depends only on the applicative behaviour
    of the type of [b] at the type of [w]. *)
Lemma fix_lam_typing_iff : forall b w U V,
  inf @ fix_function (lam b w) ==> Sm (U --> V) <->
  inf @ w ==> Sm (U --> V) /\
  exists B, inf @ b ==> Sm B /\ tapp @ B @r (U --> V) ==> Sm (U --> V).
Proof.
  intros b w U V; split.
  - intro H.
    destruct (fix_function_typing_inv _ _ H) as [U' [V' [HT Hf]]].
    destruct (lam_typing_inv _ _ _ Hf) as [B [W [R [HT' [Hb [Hw HB]]]]]].
    unfold funty in HT, HT'; inversion HT; subst U' V'.
    inversion HT'; subst W R.
    split; [exact Hw|exists B; split; assumption].
  - intros [Hw [B [Hb HB]]].
    apply infer_fix_function; eapply infer_lam; eassumption.
Qed.

End Inversions.

(** * Stage 1: dither *)

Local Transparent typed_neg.

Definition dither_body_neg : Combination := typed_compose_with_body neg 'tt.

(** [head_erase] commutes with the body of [typed_compose_with]: the head
    [g] is erased, the witness is only recursed into. *)
Lemma head_erase_compose_with_body : forall g d,
  head_erase (typed_compose_with_body g d) =
  typed_compose_with_body (erase (head_erase g)) (head_erase d).
Proof. intros; reflexivity. Qed.

Lemma head_erase_typed_neg : head_erase typed_neg = typed_neg.
Proof. vm_compute; reflexivity. Qed.

Lemma head_erase_tt : head_erase 'tt = 'tt.
Proof. vm_compute; reflexivity. Qed.


(** Literal application to the whole carrier: the functional itself is
    erased, leaving the raw body (with [neg]) at the head of the Z-body. *)
Lemma dither_head_erase_whole :
  head_erase dither_fn = 'tagged[Z (dither_body_neg 'C tagged_fun), fun_nm].
Proof. vm_compute; reflexivity. Qed.

(** ... and the result has no type at all, under any declarations: the fix
    rule needs the functional's type to be an endofunction type, but the
    type of the raw body is a structural fork ending in [K1 label[fun_nm]]. *)
Lemma dither_whole_erase_untypable : forall (AI : Decl) T,
  ~ infer AI @ head_erase dither_fn ==> Sm T.
Proof.
  intros AI T H; rewrite dither_head_erase_whole in H.
  change (infer AI @ fix_function dither_body_neg ==> Sm T) in H.
  destruct (fix_function_typing_inv AI _ _ H) as [U [V [_ HB]]].
  unfold dither_body_neg, typed_compose_with_body in HB; cbn in HB.
  destruct (infer_fork_inv AI _ _ _ HB) as [X [Y [_ [HY HXY]]]].
  pose proof (eval_deterministic _ _ HY _
    (infer_tag_free AI ('K1 ('label[fun_nm])) ltac:(unfold fun_nm; tag_free_tac))) as EY.
  inversion EY; subst Y; clear EY HY.
  apply stem_plain in HXY; [|intros; discriminate].
  unfold funty in HXY; discriminate HXY.
Qed.

(** The optimisation that keeps the functional's tag and ghost. *)
Definition erased_dither : Combination := fix_erase (typed_compose_with_body typed_neg 'tt) typed_neg.

Lemma erased_dither_shape : erased_dither = fix_function (lam dither_body_neg typed_neg).
Proof.
  unfold erased_dither, fix_erase, dither_body_neg.
  rewrite head_erase_compose_with_body, head_erase_typed_neg, head_erase_tt.
  reflexivity.
Qed.

(** ** The typed composition functional with an untyped-as-function head

    [infer_typed_compose_with] (functions.v) needs the head [g] to have a
    function type.  Only the applicative behaviour of its type is used:
    the body builds [lam[g 'C f, d]] at run time, and the introduction of
    that [lam] checks [(G 'C F) # U], i.e. [G # V]. *)

Local Ltac known_concrete_type_app_step :=
  lazymatch goal with
  | |- app ?AI @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | ?A --> ?B =>
          eapply type_app_abstract; apply funty_eliminator_eval
      | Lf => eapply type_app_leaf_ev
      | Fk Lf ?x => eapply type_app_K_ev
      | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
      | Sm ?x =>
          eapply type_app_stem_ev; eapply type_app_stem_structural;
          intros E N Heq; inversion Heq
      | Fk (Sm (Fk Lf ?g)) ?f =>
          eapply type_app_compose; [solve [reject_name]| | |];
          [intros E N Heq; inversion Heq | |]
      | Fk (Sm ?g) ?f =>
          new_S;
          [intros E N Heq; inversion Heq | | |]
      end
  end.

Lemma compose_with_body_typing : forall (AI : Decl) g G fw d U V W,
  infer AI @ g ==> Sm G ->
  type_app AI @ G @r V ==> Sm W ->
  infer AI @ fw ==> Sm (U --> V) ->
  infer AI @ d ==> Sm U ->
  infer AI @ lam (typed_compose_with_body g d) fw ==>
    Sm ((U --> V) --> (U --> W)).
Proof.
  intros AI g G fw d U V W Hg HG Hfw Hd.
  eapply infer_lam.
  - unfold typed_compose_with_body; cbn.
    repeat first [eassumption | progress infer_tac].
    all: repeat known_concrete_type_app_step.
  - exact Hfw.
  - unfold typed_compose_with_body; cbn.
    repeat first [eassumption | progress infer_tac].
    all: repeat known_concrete_type_app_step.
    eapply type_app_stem_ev.
    eapply type_app_stem_function.
    eapply type_app_compose; [solve [reject_name]| | |].
    + unfold funty; intros E N Heq; discriminate Heq.
    + eapply type_app_abstract; apply funty_eliminator_eval.
    + exact HG.
Qed.

(** Typing of erasure at a head, for any sound declarations. *)
Lemma erase_typing_but : forall (AI : Decl) B c C X Y,
  plain_intro_sound_but AI B -> List.forallb tag_free B = true -> tags_avoid B c = true ->
  infer AI @ c ==> Sm C -> type_app AI @ C @r X ==> Sm Y ->
  exists C', infer AI @ erase c ==> Sm C' /\ type_app AI @ C' @r X ==> Sm Y.
Proof.
  intros AI B c C X Y Hs HB Ha Hc HC.
  destruct (untag_typing_but AI B c C X Y Hs HB Ha Hc HC) as [C1 [H1 HC1]].
  exact (undecorate_typing AI _ _ _ _ H1 HC1).
Qed.

Lemma erase_typing : forall (AI : Decl) c C X Y,
  plain_intro_sound AI ->
  infer AI @ c ==> Sm C -> type_app AI @ C @r X ==> Sm Y ->
  exists C', infer AI @ erase c ==> Sm C' /\ type_app AI @ C' @r X ==> Sm Y.
Proof.
  intros AI c C X Y Hs Hc HC.
  destruct (untag_typing_plain AI c C X Y Hs Hc HC) as [C1 [H1 HC1]].
  exact (undecorate_typing AI _ _ _ _ H1 HC1).
Qed.

(** Stage 3, special case: erasing the head of the typed composition
    functional preserves its type, for every head [g] of function type. *)
Lemma compose_with_erase_typing : forall (AI : Decl) g fw d U V W,
  plain_intro_sound AI ->
  infer AI @ g ==> Sm (V --> W) ->
  infer AI @ fw ==> Sm (U --> V) ->
  infer AI @ d ==> Sm U ->
  infer AI @ lam (typed_compose_with_body (erase g) d) fw ==>
    Sm ((U --> V) --> (U --> W)).
Proof.
  intros AI g fw d U V W Hs Hg Hfw Hd.
  destruct (erase_typing AI g (V --> W) V W Hs Hg
    ltac:(eapply type_app_abstract; apply funty_eliminator_eval))
    as [G' [HG' HG'app]].
  eapply compose_with_body_typing; eassumption.
Qed.

(** ** Stage 1 theorems *)

Lemma erased_dither_functional_infer : forall (AI : Decl),
  supports_booleans AI ->
  infer AI @ lam dither_body_neg typed_neg ==>
    Sm (('Bool --> 'Bool) --> ('Bool --> 'Bool)).
Proof.
  intros AI Hb; unfold dither_body_neg.
  eapply compose_with_body_typing.
  - apply neg_infer; exact Hb.
  - apply neg_type_app.
  - apply typed_neg_infer; exact Hb.
  - apply tt_infer; exact Hb.
Qed.

(** (a) [erased_dither] has the type of [dither_fn], with no soundness hypothesis
    (the erased head [neg] is typed directly). *)
Lemma erased_dither_infer : forall (AI : Decl),
  supports_booleans AI ->
  infer AI @ erased_dither ==> Sm ('Bool --> 'Bool).
Proof.
  intros AI Hb; rewrite erased_dither_shape.
  apply infer_fix_function; apply erased_dither_functional_infer; exact Hb.
Qed.


(** (b) [erased_dither @ tt] has expression type [Bool]. *)
Lemma erased_dither_tt_infer_expression : forall (AI : Decl),
  supports_booleans AI ->
  infer_expression AI @ (erased_dither @ 'tt) ==> Sm ('Bool).
Proof.
  intros AI Hb.
  eapply infer_expression_fork.
  - apply infer_expression_stem; apply erased_dither_infer; exact Hb.
  - apply infer_expression_stem; apply tt_infer; exact Hb.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.


(** [fix_erase] is [head_erase] inside the functional's body: the only
    difference from the literal rewrite is that the functional at the head
    of the Z-body is kept. *)
Lemma dither_is_fix : dither_fn =
  fix_function (lam (typed_compose_with_body typed_neg 'tt) typed_neg).
Proof. reflexivity. Qed.

(** * Stage 2: addition (recursion.v)

    [addition = fix[lam[addition_functional_body, typed_zero_binary]]].
    Inside its body, the typed successor [successor_function] (a [lam])
    occurs once, at a head position [S1 (K1 successor_function)]: the step
    is [lam[successor_function 'C wait[recursive,a], zero]].  [head_erase]
    replaces it by its raw body [successor_function_body]. *)

Local Transparent successor_function.

(** The body of addition, parameterised by the successor program [s]
    (a copy of the local terms of recursion.v). *)
Definition addition_step_term_with (s : Combination) (recursive a : Term) : Term :=
  lam2 (Val s ''C ''wait[recursive,a]) (Val zero).

Definition addition_inner_term_with (s : Combination) (recursive a : Term) : Term :=
  lam2 (star "n" (Val nat_split @@ Ref "n" @@ (a ''* addition_step_term_with s recursive a)))
    (Val zero).

Definition addition_value_term_with (s : Combination) (recursive : Term) : Term :=
  lam2 (star "a" (addition_inner_term_with s recursive (Ref "a"))) (Val zero).

Definition addition_body_with_package (s : Combination) :
  { t : Combination |
    to_tree (star "recursive" (addition_value_term_with s (Ref "recursive"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition addition_body_with (s : Combination) : Combination :=
  Eval cbn in proj1_sig (addition_body_with_package s).

Definition addition_with (s : Combination) : Combination :=
  fix_function (lam (addition_body_with s) typed_zero_binary).

(** The optimised addition. *)
Definition erased_addition : Combination :=
  fix_erase addition_functional_body typed_zero_binary.

Lemma head_erase_addition_body :
  head_erase addition_functional_body =
  addition_body_with successor_function_body.
Proof. vm_compute; reflexivity. Qed.

Lemma erased_addition_is_with :
  erased_addition = addition_with successor_function_body.
Proof.
  unfold erased_addition, fix_erase, addition_with.
  rewrite head_erase_addition_body; reflexivity.
Qed.

(** ** Typing, for any successor program of the right applicative type *)

Section AdditionTyping.
Set Default Proof Using "All".
Variable AI : Decl.
Hypothesis AI_supports_booleans : supports_booleans AI.
Hypothesis AI_supports_number : supports_number AI.
Variables s S : Combination.
Hypothesis Hs : infer AI @ s ==> Sm S.
Hypothesis HS : type_app AI @ S @r ('Nat) ==> Sm ('Nat).

Local Ltac addition_infer :=
  repeat first
    [ match goal with H : infer _ @ ?x ==> Sm ?X |- _ => exact H end
    | solve [eapply infer_zero; eauto]
    | apply infer_nat_split
    | eapply infer_lam
    | eapply infer_fork
    | eapply infer_stem
    | eapply infer_leaf
    | eapply infer_I
    | eapply infer_K1
    ].

Local Ltac known_addition_type_app := first [exact HS | ty].

Lemma addition_body_with_type :
  { F : Combination |
      infer AI @ addition_body_with s ==> Sm F /\
      type_app AI @ F @r ('Nat --> ('Nat --> 'Nat)) ==>
        Sm ('Nat --> ('Nat --> 'Nat)) }.
Proof.
  pose proof (infer_addition_seed AI AI_supports_booleans AI_supports_number)
    as Hrecursive.
  eexists; split.
  - unfold addition_body_with; cbn.
    all: repeat first
      [ exact Hrecursive
      | progress addition_infer
      | known_addition_type_app ].
  - unfold addition_body_with; cbn.
    all: repeat first
      [ exact Hrecursive
      | progress addition_infer
      | known_addition_type_app ].
Defined.

Lemma addition_with_infer :
  infer AI @ addition_with s ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  unfold addition_with; apply infer_fix_function; eapply infer_lam.
  - exact (proj1 (proj2_sig addition_body_with_type)).
  - apply infer_addition_seed; assumption.
  - exact (proj2 (proj2_sig addition_body_with_type)).
Qed.

End AdditionTyping.

Lemma successor_body_typing : forall (AI : Decl),
  supports_booleans AI -> supports_number AI ->
  exists S, infer AI @ successor_function_body ==> Sm S /\
    type_app AI @ S @r ('Nat) ==> Sm ('Nat).
Proof.
  intros AI Hb Hn.
  destruct (lam_typing_inv AI _ _ _ (infer_successor_function AI Hb Hn))
    as [F [U [V [HT [HF [_ HFapp]]]]]].
  unfold funty in HT; inversion HT; subst U V.
  exists F; split; assumption.
Qed.

(** Stage 2 typing: the optimised addition has the type of addition. *)
Lemma erased_addition_infer : forall (AI : Decl),
  supports_booleans AI -> supports_number AI ->
  infer AI @ erased_addition ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  intros AI Hb Hn; rewrite erased_addition_is_with.
  destruct (successor_body_typing AI Hb Hn) as [S [Hs HS]].
  exact (addition_with_infer AI Hb Hn _ _ Hs HS).
Qed.

Lemma erased_addition_infer_all :
  infer paper_ontology @ erased_addition ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  apply erased_addition_infer;
    [exact paper_ontology_supports_booleans|exact paper_ontology_supports_number].
Qed.

(** The same holds for the erasure of any typed successor program. *)
Lemma addition_with_erase_typing : forall (AI : Decl) s,
  plain_intro_sound AI -> supports_booleans AI -> supports_number AI ->
  infer AI @ s ==> Sm ('Nat --> 'Nat) ->
  infer AI @ addition_with (erase s) ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  intros AI s Hsound Hb Hn Hs.
  destruct (erase_typing AI s _ ('Nat) ('Nat) Hsound Hs
    ltac:(eapply type_app_abstract; apply funty_eliminator_eval))
    as [S [HS HSapp]].
  exact (addition_with_infer AI Hb Hn _ _ HS HSapp).
Qed.

(** ** Behaviour on small arguments (bonus)

    A certified fuel evaluator.  Fuel exhaustion proves nothing; successful runs become evaluation
    derivations by [run_sound]. *)

Fixpoint run (fuel : nat) (f u : Combination) : option Combination :=
  match fuel with
  | O => None
  | S k =>
    match f with
    | Lf => Some (Sm u)
    | Sm x => Some (Fk x u)
    | Fk Lf x => Some x
    | Fk (Sm g) h =>
      match run k g u, run k h u with
      | Some a, Some b => run k a b
      | _, _ => None
      end
    | Fk (Fk a b) c =>
      match u with
      | Lf => Some a
      | Sm x => run k b x
      | Fk x y => match run k c x with Some d => run k d y | None => None end
      end
    end
  end.

Lemma run_sound : forall fuel f u v,
  run fuel f u = Some v -> f @ u ==> v.
Proof.
  induction fuel as [|fuel IH]; intros f u v H; [discriminate|].
  destruct f as [|a|a b]; cbn in H.
  - inversion H; constructor.
  - inversion H; constructor.
  - destruct a as [|a|a c].
    + inversion H; constructor.
    + destruct (run fuel a u) eqn:HA; [|discriminate].
      destruct (run fuel b u) eqn:HB; [|discriminate].
      apply eval_s; eapply eval_appl; [eapply IH; exact HA|].
      eapply eval_appr; eapply IH; eassumption.
    + destruct u as [|x|x y].
      * inversion H; constructor.
      * apply eval_stem; eapply IH; exact H.
      * destruct (run fuel b x) eqn:HB; [|discriminate].
        apply eval_fork; eapply eval_appl; eapply IH; eassumption.
Qed.

Definition run2 fuel f x y :=
  match run fuel f x with Some g => run fuel g y | None => None end.

Lemma run2_sound : forall fuel f x y v,
  run2 fuel f x y = Some v -> f @ x @r y ==> v.
Proof.
  intros fuel f x y v H; unfold run2 in H.
  destruct (run fuel f x) eqn:HG; [|discriminate].
  eapply eval_appl; eapply run_sound; eassumption.
Qed.

Definition one := succ zero.
Definition two := succ one.
Definition three := succ two.
Definition five := succ (succ three).

Lemma erased_addition_values :
  (erased_addition @ zero @r zero ==> zero /\ addition @ zero @r zero ==> zero) /\
  (erased_addition @ two @r zero ==> two /\ addition @ two @r zero ==> two) /\
  (erased_addition @ zero @r two ==> two /\ addition @ zero @r two ==> two) /\
  (erased_addition @ two @r three ==> five /\ addition @ two @r three ==> five) /\
  (erased_addition @ three @r two ==> five /\ addition @ three @r two ==> five).
Proof.
  repeat split; apply (run2_sound 200); vm_compute; reflexivity.
Qed.

(** * Stage 3: the general question *)

(** ** The exact condition

    By [fix_lam_typing_iff], [fix_erase b w] keeps the type [U -> V] of
    [fix[lam[b,w]]] exactly when the type of [head_erase b] maps [U -> V]
    to [U -> V].  So the general statement is equivalent to: head erasure
    preserves the type application of the body at the witness type. *)
Lemma fix_erase_typing_iff : forall (AI : Decl) b w U V,
  infer AI @ fix_function (lam b w) ==> Sm (U --> V) ->
  (infer AI @ fix_erase b w ==> Sm (U --> V) <->
   exists B', infer AI @ head_erase b ==> Sm B' /\
     type_app AI @ B' @r (U --> V) ==> Sm (U --> V)).
Proof.
  intros AI b w U V H; unfold fix_erase.
  rewrite fix_lam_typing_iff in H |- *; destruct H as [Hw _].
  split; [intros [_ HB]; exact HB|intro HB; split; assumption].
Qed.

(** ** The general statement fails

    Types are structural on programs that are not tagged: the type of a
    partial composition [S1 (K1 c)] is [S1 (K1 C)], which records the type
    [C] of its head.  A function that returns such a value exposes [C] in
    its result type, and erasure changes [C]. *)

Definition b_bad : Combination := 'K1 ('S1 ('K1 typed_neg)).

Lemma head_erase_b_bad : head_erase b_bad = 'K1 ('S1 ('K1 neg)).
Proof. vm_compute; reflexivity. Qed.

Lemma funty_neq_Neg : ('Bool --> 'Bool) <> Neg.
Proof. unfold funty, Neg; discriminate. Qed.

Lemma head_erase_changes_lam_type : forall (AI : Decl),
  supports_booleans AI ->
  infer AI @ lam b_bad 'tt ==> Sm ('Bool --> 'S1 ('K1 ('Bool --> 'Bool))) /\
  infer AI @ lam (head_erase b_bad) 'tt ==> Sm ('Bool --> 'S1 ('K1 Neg)) /\
  ~ infer AI @ lam (head_erase b_bad) 'tt ==>
      Sm ('Bool --> 'S1 ('K1 ('Bool --> 'Bool))).
Proof.
  intros AI Hb.
  assert (H2 : infer AI @ lam (head_erase b_bad) 'tt ==>
                 Sm ('Bool --> 'S1 ('K1 Neg))).
  { rewrite head_erase_b_bad; eapply infer_lam;
      [|apply tt_infer; exact Hb|apply type_app_K_ev].
    apply infer_K1; apply infer_stem; apply infer_stem; apply infer_K1.
    apply neg_infer; exact Hb. }
  split; [|split; [exact H2|]].
  - unfold b_bad; eapply infer_lam;
      [|apply tt_infer; exact Hb|apply type_app_K_ev].
    apply infer_K1; apply infer_stem; apply infer_stem; apply infer_K1.
    apply typed_neg_infer; exact Hb.
  - intro H1; pose proof (eval_deterministic _ _ H1 _ H2) as E.
    unfold funty, Neg in E; inversion E.
Qed.

(** The failure persists inside a fixfunction, even though [fix_erase]
    keeps the functional's tag, ghost and witness: here the functional
    returns a [lam] whose result type exposes the head. *)
Definition w_bad : Combination := lam b_bad 'tt.
Definition fb_bad : Combination := 'K1 w_bad.
Definition T_bad : Combination := 'Bool --> 'S1 ('K1 ('Bool --> 'Bool)).

Lemma head_erase_fb_bad : head_erase fb_bad = 'K1 (lam ('K1 ('S1 ('K1 neg))) 'tt).
Proof. vm_compute; reflexivity. Qed.

Lemma fix_erase_counterexample : forall (AI : Decl),
  supports_booleans AI ->
  infer AI @ fix_function (lam fb_bad w_bad) ==> Sm T_bad /\
  forall T, ~ infer AI @ fix_erase fb_bad w_bad ==> Sm T.
Proof.
  intros AI Hb.
  destruct (head_erase_changes_lam_type AI Hb) as [Hw [Hw' Hne]].
  split.
  - unfold T_bad; apply infer_fix_function; eapply infer_lam;
      [apply infer_K1; exact Hw|exact Hw|apply type_app_K_ev].
  - intros T H.
    destruct (fix_function_typing_inv AI _ _ H) as [U [V [-> HF]]].
    destruct (lam_typing_inv AI _ _ _ HF) as [B [U' [V' [HT [HB [Hwt HBapp]]]]]].
    unfold funty in HT; inversion HT; subst U' V'; clear HT.
    pose proof (eval_deterministic _ _ Hwt _ Hw) as EW.
    unfold funty in EW; inversion EW; subst U V; clear EW.
    rewrite head_erase_fb_bad in HB.
    destruct (infer_K1_result_inv AI _ _ HB) as [L [-> HL]].
    pose proof (eval_deterministic _ _ HL _ Hw') as EL.
    inversion EL; subst L; clear EL.
    pose proof (eval_deterministic _ _ HBapp _
      (type_app_K_ev AI _ ('Bool --> 'S1 ('K1 ('Bool --> 'Bool))))) as EV.
    unfold funty, Neg in EV; inversion EV.
Qed.

(** ** What holds: erasure at a head whose composition is only applied

    At the root of a function body, the composition [c 'C g] has the
    structural type [C 'C G], and introduction only applies it to the
    witness type.  Its type application factors as [C # (G # U)], and
    erasure preserves every type application of the head
    ([erase_typing]).  Two side conditions keep the composition an
    ordinary one: [g] is not a label (else [c 'C g] is a tag) and [g] is
    not [get_tagname] (else it may be a name test). *)

Section RootErasure.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Abbreviation inf := (infer AI).

(** Copy of the local [S_success_inv] above. *)
Lemma S_success_inv' : forall G F U V,
 (forall E N, 'S2[G,F] <> 'tagged[E,N]) ->
 get_name_test @ ('S2[G,F]) ==> Lf ->
 tapp @ ('S2[G,F]) @r U ==> Sm V ->
 exists A B, tapp @ G @r U ==> Sm A /\
 tapp @ F @r U ==> Sm B /\ tapp @ A @r B ==> Sm V.
Proof.
 intros G F U V HP HN H.
 assert (HA : abstract_case @ ('S2[G,F]) ==> Lf)
   by (unfold abstract_case; apply type_app_abstract_case_S_none; exact HP).
 eapply default_S_inv; exact (app_plain_inv _ _ _ _ HA H).
Qed.

Lemma get_tagname_tag_free : tag_free get_tagname = true.
Proof. tag_free_tac. Qed.

(** Typing of a root composition, both directions packaged as one step. *)
Lemma root_erase_app : forall c g G C U V,
  plain_intro_sound AI ->
  g <> get_tagname -> (forall n, g <> 'label[n]) ->
  inf @ c ==> Sm C -> inf @ g ==> Sm G ->
  tapp @ (C 'C G) @r U ==> Sm V ->
  exists C', inf @ erase c ==> Sm C' /\ tapp @ (C' 'C G) @r U ==> Sm V.
Proof.
  intros c g G C U V Hs Hgt Hgl Hc Hg H.
  assert (HG1 : G <> get_tagname).
  { intro E; subst G; apply Hgt.
    exact (infer_tag_free_inv AI _ _ Hg get_tagname_tag_free). }
  assert (HG2 : forall C0 E N, C0 'C G <> 'tagged[E,N]).
  { intros C0 E N HE; inversion HE; subst.
    destruct (infer_tag_right_inv AI _ _ Hg) as [n [-> _]].
    exact (Hgl n eq_refl). }
  destruct (S_success_inv' _ _ _ _ (HG2 C)
    (get_name_test_S_right _ _ HG1) H) as [A [B [HA [HB HAB]]]].
  pose proof (eval_deterministic _ _ HA _ (app_K AI C U)) as EA.
  inversion EA; subst A; clear EA HA.
  destruct (erase_typing AI c C B V Hs Hc HAB) as [C' [HC' HC'app]].
  exists C'; split; [exact HC'|].
  eapply type_app_compose;
    [apply get_name_test_S_right; exact HG1|apply HG2|exact HB|exact HC'app].
Qed.

Lemma lam_root_erase_typing : forall c g u T,
  plain_intro_sound AI ->
  g <> get_tagname -> (forall n, g <> 'label[n]) ->
  inf @ lam (c 'C g) u ==> Sm T ->
  inf @ lam (erase c 'C g) u ==> Sm T.
Proof.
  intros c g u T Hs Hgt Hgl H.
  destruct (lam_typing_inv AI _ _ _ H) as [F [U [V [-> [HF [Hu HFapp]]]]]].
  destruct (infer_compose_inv AI _ _ _ Hgl HF) as [C [G [-> [Hc Hg]]]].
  destruct (root_erase_app c g G C U V Hs
    Hgt Hgl Hc Hg HFapp)
    as [C' [HC' HC'app]].
  eapply infer_lam; [eapply infer_compose; eassumption|exact Hu|exact HC'app].
Qed.

Lemma fix_root_erase_typing : forall c g w T,
  plain_intro_sound AI ->
  g <> get_tagname -> (forall n, g <> 'label[n]) ->
  inf @ fix_function (lam (c 'C g) w) ==> Sm T ->
  inf @ fix_function (lam (erase c 'C g) w) ==> Sm T.
Proof.
  intros c g w T Hs Hgt Hgl H.
  destruct (fix_function_typing_inv AI _ _ H) as [U [V [-> HF]]].
  apply infer_fix_function.
  exact (lam_root_erase_typing c g w _ Hs Hgt Hgl HF).
Qed.

End RootErasure.

(** ** Erasure along the right spine of a chain of compositions

    The run-time values found in E7a, [typed_neg 'C (typed_neg 'C ... I)],
    are chains of compositions.  Erasing every head along the right spine
    preserves the type of a function whose body is such a chain. *)

Fixpoint spine_erase (t : Combination) : Combination :=
  match t with
  | Fk (Sm (Fk Lf _)) (Fk (Sm (Sm Lf)) (Fk Lf _)) => t
  | Fk (Sm (Fk Lf c)) g => Fk (Sm (Fk Lf (erase c))) (spine_erase g)
  | _ => t
  end.

Fixpoint spine_ok (t : Combination) : Prop :=
  match t with
  | Fk (Sm (Fk Lf _)) (Fk (Sm (Sm Lf)) (Fk Lf _)) => True
  | Fk (Sm (Fk Lf _)) g =>
      g <> get_tagname /\ spine_erase g <> get_tagname /\ spine_ok g
  | _ => True
  end.

Lemma spine_erase_label : forall t n,
  spine_erase t = 'label[n] -> t = 'label[n].
Proof.
  intros t n H.
  destruct t as [|a|a b]; try exact H.
  cbn in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x
         end; first [discriminate H | exact H].
Qed.

Section SpineErasure.
Variable AI : Decl.
Local Abbreviation tapp := (typing.type_app AI).
Local Abbreviation inf := (infer AI).

Lemma spine_erase_app : forall t T U V,
  plain_intro_sound AI -> spine_ok t ->
  inf @ t ==> Sm T -> tapp @ T @r U ==> Sm V ->
  exists T', inf @ spine_erase t ==> Sm T' /\ tapp @ T' @r U ==> Sm V.
Proof.
  intros t; induction t as [|a _|a _ g IHg]; intros T U V Hs Hok Ht HT;
    try (exists T; split; assumption).
  (* the fork case: only compositions [c 'C g] with [g] not a label change *)
  destruct (combination_eq_dec (spine_erase (Fk a g)) (Fk a g)) as [E|Hne].
  { rewrite E; exists T; split; assumption. }
  destruct a as [|a|a1 a2]; [exfalso; apply Hne; reflexivity| |
    exfalso; apply Hne; reflexivity].
  destruct a as [|a|a1 c]; try (exfalso; apply Hne; reflexivity).
  destruct a1; try (exfalso; apply Hne; reflexivity).
  assert (Hgl : forall n, g <> 'label[n]).
  { intros n ->; apply Hne; reflexivity. }
  assert (Hshape : spine_erase (c 'C g) = erase c 'C spine_erase g /\
                   spine_ok (c 'C g) =
                   (g <> get_tagname /\
                    spine_erase g <> get_tagname /\ spine_ok g)).
  { destruct g as [|g|g1 g2]; [split; reflexivity|split; reflexivity|].
    destruct g1 as [|g1|g11 g12]; try (split; reflexivity).
    destruct g1 as [|g1|g11 g12]; try (split; reflexivity).
    destruct g1; try (split; reflexivity).
    destruct g2 as [|g2|g21 g22]; try (split; reflexivity).
    destruct g21; try (split; reflexivity).
    exfalso; exact (Hgl g22 eq_refl). }
  destruct Hshape as [Hse Hsok].
  change (spine_ok (c 'C g)) in Hok; rewrite Hsok in Hok.
  destruct Hok as [Hgt [Hg't Hokg]].
  rewrite Hse.
  destruct (infer_compose_inv AI _ _ _ Hgl Ht) as [C [G [-> [Hc Hg]]]].
  assert (HG1 : G <> get_tagname).
  { intro E; subst G; apply Hgt.
    exact (infer_tag_free_inv AI _ _ Hg (get_tagname_tag_free AI)). }
  assert (HG2 : forall C0 E N, C0 'C G <> 'tagged[E,N]).
  { intros C0 E N HE; inversion HE; subst.
    destruct (infer_tag_right_inv AI _ _ Hg) as [n [-> _]].
    exact (Hgl n eq_refl). }
  destruct (S_success_inv' AI _ _ _ _ (HG2 C)
    (get_name_test_S_right _ _ HG1) HT) as [A [B [HA [HB HAB]]]].
  pose proof (eval_deterministic _ _ HA _ (app_K AI C U)) as EA.
  inversion EA; subst A; clear EA HA.
  destruct (IHg G U B Hs Hokg Hg HB) as [G' [HG' HG'app]].
  destruct (erase_typing AI c C B V Hs Hc HAB) as [C' [HC' HC'app]].
  assert (Hg'l : forall n, spine_erase g <> 'label[n]).
  { intros n E; exact (Hgl n (spine_erase_label _ _ E)). }
  assert (HG'1 : G' <> get_tagname).
  { intro E; subst G'; apply Hg't.
    exact (infer_tag_free_inv AI _ _ HG' (get_tagname_tag_free AI)). }
  exists (C' 'C G'); split.
  - apply infer_compose; assumption.
  - eapply type_app_compose; [apply get_name_test_S_right; exact HG'1| |
      exact HG'app|exact HC'app].
    intros E N HE; inversion HE; subst.
    destruct (infer_tag_right_inv AI _ _ HG') as [n [Hn _]].
    exact (Hg'l n Hn).
Qed.

Lemma lam_spine_erase_typing : forall t u T,
  plain_intro_sound AI -> spine_ok t ->
  inf @ lam t u ==> Sm T -> inf @ lam (spine_erase t) u ==> Sm T.
Proof.
  intros t u T Hs Hok H.
  destruct (lam_typing_inv AI _ _ _ H) as [F [U [V [-> [HF [Hu HFapp]]]]]].
  destruct (spine_erase_app t F U V Hs
    Hok HF HFapp) as [F' [HF' HF'app]].
  eapply infer_lam; eassumption.
Qed.

Lemma fix_spine_erase_typing : forall t w T,
  plain_intro_sound AI -> spine_ok t ->
  inf @ fix_function (lam t w) ==> Sm T ->
  inf @ fix_function (lam (spine_erase t) w) ==> Sm T.
Proof.
  intros t w T Hs Hok H.
  destruct (fix_function_typing_inv AI _ _ H) as [U [V [-> HF]]].
  apply infer_fix_function; exact (lam_spine_erase_typing t w _ Hs Hok HF).
Qed.

End SpineErasure.

(** *** Application: the run-time chains of neg_times (E7a) *)

Lemma head_erase_compose : forall c g, (forall n, g <> 'label[n]) ->
  head_erase (c 'C g) = erase (head_erase c) 'C head_erase g.
Proof.
  intros c g Hgl.
  destruct g as [|g|g1 g2]; try reflexivity.
  destruct g1 as [|g1|g11 g12]; try reflexivity.
  destruct g1 as [|g1|g11 g12]; try reflexivity.
  destruct g1; try reflexivity.
  destruct g2 as [|g2|g21 g22]; try reflexivity.
  destruct g21; try reflexivity.
  exfalso; exact (Hgl g22 eq_refl).
Qed.

Lemma spine_compose : forall c g, (forall n, g <> 'label[n]) ->
  spine_erase (c 'C g) = erase c 'C spine_erase g /\
  spine_ok (c 'C g) =
    (g <> get_tagname /\ spine_erase g <> get_tagname /\ spine_ok g).
Proof.
  intros c g Hgl.
  destruct g as [|g|g1 g2]; try (split; reflexivity).
  destruct g1 as [|g1|g11 g12]; try (split; reflexivity).
  destruct g1 as [|g1|g11 g12]; try (split; reflexivity).
  destruct g1; try (split; reflexivity).
  destruct g2 as [|g2|g21 g22]; try (split; reflexivity).
  destruct g21; try (split; reflexivity).
  exfalso; exact (Hgl g22 eq_refl).
Qed.

(** [chain h n = h 'C (h 'C ... 'C I)], with [n] copies of [h]. *)
Fixpoint chain (h : Combination) (n : nat) : Combination :=
  match n with
  | O => 'I
  | S k => h 'C chain h k
  end.

Lemma chain_not_label : forall h n m, chain h n <> 'label[m].
Proof. intros h [|n] m; discriminate. Qed.

Lemma tag_free_compose : forall c g,
  tag_free c = false -> tag_free (c 'C g) = false.
Proof.
  intros c g H; cbn [tag_free].
  rewrite H, !Bool.andb_false_r; cbn; reflexivity.
Qed.

Lemma chain_not_get_tagname : forall h n,
  tag_free h = false -> chain h n <> get_tagname.
Proof.
  intros h [|n] Hh E.
  - vm_compute in E; discriminate E.
  - pose proof (tag_free_compose h (chain h n) Hh) as Hf.
    cbn [chain] in E; rewrite E in Hf.
    rewrite (get_tagname_tag_free function_decl) in Hf; discriminate.
Qed.

Lemma tag_free_typed_neg : tag_free typed_neg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma tag_free_neg : tag_free neg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma head_erase_chain : forall n,
  head_erase (chain typed_neg n) = chain neg n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [chain]; rewrite head_erase_compose by apply chain_not_label.
  rewrite IH, head_erase_typed_neg; reflexivity.
Qed.

Lemma spine_chain : forall n,
  spine_erase (chain typed_neg n) = chain neg n /\ spine_ok (chain typed_neg n).
Proof.
  induction n as [|n [IH1 IH2]]; [split; [reflexivity|exact I]|].
  cbn [chain]; destruct (spine_compose typed_neg (chain typed_neg n)
    (chain_not_label _ _)) as [E1 E2].
  rewrite E1, E2, IH1; split; [reflexivity|].
  repeat split; try exact IH2;
    apply chain_not_get_tagname;
    first [exact tag_free_typed_neg|exact tag_free_neg].
Qed.

Lemma chain_typing : forall (AI : Decl) h Hty n,
  tag_free h = false ->
  infer AI @ h ==> Sm Hty -> type_app AI @ Hty @r ('Bool) ==> Sm ('Bool) ->
  exists R, infer AI @ chain h n ==> Sm R /\
    type_app AI @ R @r ('Bool) ==> Sm ('Bool).
Proof.
  intros AI h Hty n Hf Hh HH.
  induction n as [|n [R [HR HRapp]]].
  - exists 'I; split; [apply infer_I|apply type_app_I].
  - exists (Hty 'C R); split.
    + apply infer_compose; [apply chain_not_label|exact Hh|exact HR].
    + assert (HR1 : R <> get_tagname).
      { intro E; subst R; apply (chain_not_get_tagname h n Hf).
        exact (infer_tag_free_inv AI _ _ HR (get_tagname_tag_free AI)). }
      eapply type_app_compose;
        [apply get_name_test_S_right; exact HR1| |exact HRapp|exact HH].
      intros E N HE; inversion HE; subst.
      destruct (infer_tag_right_inv AI _ _ HR) as [m [Hm _]].
      exact (chain_not_label h n m Hm).
Qed.

(** The typed chain [lam[typed_neg 'C ... 'C I, tt]] has type
    [Bool -> Bool]; so does its head erasure, obtained from
    [lam_spine_erase_typing] (not by retyping the erased chain). *)
Lemma chain_head_erase_typing : forall (AI : Decl) n,
  plain_intro_sound AI -> supports_booleans AI ->
  infer AI @ lam (chain typed_neg n) 'tt ==> Sm ('Bool --> 'Bool) /\
  infer AI @ lam (head_erase (chain typed_neg n)) 'tt ==>
    Sm ('Bool --> 'Bool).
Proof.
  intros AI n Hs Hb.
  destruct (chain_typing AI typed_neg _ n tag_free_typed_neg
    (typed_neg_infer AI Hb)
    ltac:(eapply type_app_abstract; apply funty_eliminator_eval))
    as [R [HR HRapp]].
  assert (H : infer AI @ lam (chain typed_neg n) 'tt ==>
                Sm ('Bool --> 'Bool))
    by (eapply infer_lam; [exact HR|apply tt_infer; exact Hb|exact HRapp]).
  split; [exact H|].
  rewrite head_erase_chain.
  destruct (spine_chain n) as [E Hok].
  rewrite <- E; exact (lam_spine_erase_typing AI _ _ _ Hs Hok H).
Qed.

Lemma chain_head_erase_values :
  lam (chain typed_neg 2) 'tt @ 'tt ==> 'tt /\
  lam (head_erase (chain typed_neg 2)) 'tt @ 'tt ==> 'tt /\
  lam (chain typed_neg 3) 'tt @ 'tt ==> 'ff /\
  lam (head_erase (chain typed_neg 3)) 'tt @ 'tt ==> 'ff.
Proof. repeat split; apply (run_sound 200); vm_compute; reflexivity. Qed.

(** * Assumptions *)

(* ===================================================================== *)
(** * Erasing inside a salary fixfunction.
    raise_emp : Emp -> Emp raises one salary; raise_all is the right fold
    over List[Emp] applying it; erased_raise_all erases the tags and ghosts
    inside the body.  Paper Theorems erased_raise_all_typed and
    raise_all_workers. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types conditionals paper_ontology customisation.
Open Scope string_scope.
Set Default Proof Using "Type".

(** ** Raising one employee, parameterised by the salary raiser [g] *)

Definition raise_fields_with_package (g : Combination) :
  {t : Combination | to_tree
    (star "p" (''tagged[''S2[Val ('I), ''K1 ((Val 'fst @@ Ref "p") ''*
       (Val g @@ (Val 'snd @@ Ref "p")))], Val employee_nm])) = t}.
Proof. eexists; cbn; reflexivity. Defined.
Definition raise_fields_with (g : Combination) : Combination :=
  Eval cbn in proj1_sig (raise_fields_with_package g).

Definition raise_emp_with (g : Combination) : Combination :=
  lam (swap (lam (raise_fields_with g) (zero '* salary zero))) (employee_witness 50).

Definition raise_emp : Combination := raise_emp_with increment_salary.

Lemma raise_emp_with_eval : forall g, (forall n, g @ salary n ==> salary (succ n)) ->
  forall i n, raise_emp_with g @ employee_at i n ==> employee_at i (S n).
Proof.
  intros g Hg i n; pose proof (Hg (numeral n)) as HI.
  unfold raise_emp_with, lam; apply tagged_eval; apply wait_eval.
  eapply eval_appl; [evaluate |].
  unfold swap; evaluate.
  unfold employee_at, employee, wrap; apply tagged_eval; evaluate.
  unfold raise_fields_with; cbn [numeral]; evaluate.
Qed.

Lemma raise_emp_eval : forall i n,
  raise_emp @ employee_at i n ==> employee_at i (S n).
Proof. apply raise_emp_with_eval; apply increment_salary_eval. Qed.

(** ** Typing of [raise_emp_with g] for any [g] whose type maps Salary to Salary *)

Local Abbreviation AI := company_ontology.

Local Ltac emp_app :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
    first [is_evar T; fail 1 | idtac];
    first [eassumption |
      lazymatch T with
      | ?A --> ?B => apply type_app_abstract; apply funty_eliminator_eval
      | employee_fields => unfold employee_fields; emp_app
      | 'Salary => apply type_app_record; cbv; discriminate
      | 'Employee => apply type_app_record; cbv; discriminate
      | nat_split => unfold nat_split
      | cons_step => unfold cons_step
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | 'Nat => apply type_app_Nat
      | 'tagged[?E,?M] => apply type_app_abstract; ty_elim
      | Lf => apply type_app_leaf_ev
      | Fk Lf _ => apply type_app_K_ev
      | 'I => apply type_app_I
      | Sm _ => apply type_app_stem_ev
      | Fk (Sm _) _ => new_S; [solve [intros; discriminate] | | |]
      end]
  | |- type_app_stem _ @ type_app _ @r _ @r _ ==> _ =>
    first [apply type_app_stem_function |
      apply type_app_stem_tagged; eapply declaration_apply; [exact company_employee|
          apply computed_wrap_abstractor_some; apply employee_payload_program_eval] |
      apply type_app_stem_structural; solve [intros; discriminate]]
  end.

Local Ltac emp_infer := first
  [ eassumption
  | apply infer_zero; apply company_number
  | apply infer_salary; [apply company_salary | apply infer_zero; apply company_number]
  | eapply infer_fork | apply infer_stem | apply infer_leaf ].

Section RaiseTyping.
Variables g G : Combination.
Hypothesis Hg : infer AI @ g ==> Sm G.
Hypothesis HG : type_app AI @ G @r ('Salary) ==> Sm ('Salary).

Definition raise_fields_type :
  {F : Combination | infer AI @ raise_fields_with g ==> Sm F /\
    type_app AI @ F @r employee_fields ==> Sm ('Employee)}.
Proof using Hg HG.
  eexists; split; unfold raise_fields_with; cbn.
  all: repeat first [emp_infer | emp_app].
Defined.

Lemma raise_emp_with_typed :
  infer AI @ raise_emp_with g ==> Sm ('Employee --> 'Employee).
Proof using Hg HG.
  assert (Hfields : infer AI @ lam (raise_fields_with g) (zero '* salary zero)
      ==> Sm (employee_fields --> 'Employee)).
  { eapply infer_lam;
      [exact (proj1 (proj2_sig raise_fields_type)) | |
       exact (proj2 (proj2_sig raise_fields_type))].
    unfold employee_fields; apply infer_product_value;
      [apply infer_zero; apply company_number|].
    apply infer_salary; [apply company_salary|apply infer_zero; apply company_number]. }
  unfold raise_emp_with; eapply infer_lam; [ | |].
  - unfold swap; infer_tac.
  - apply employee_at_typed.
  - unfold swap; type_app_tac; apply payload_eliminator_some;
      apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End RaiseTyping.

Lemma raise_emp_typed : infer AI @ raise_emp ==> Sm ('Employee --> 'Employee).
Proof.
  eapply raise_emp_with_typed;
    [apply infer_increment_salary; [exact company_salary|exact company_number]|].
  apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** ** Raising every employee of a list: a fixfunction around a fold *)

Definition raise_all_seed : Combination :=
  lam ('K1 (nil_value (employee_witness 50))) (nil_value (employee_witness 50)).
Definition raise_all_fold (s : Combination) : Combination :=
  lam (foldright_value (map_step_value s) (nil_value (employee_witness 50)))
    (nil_value (employee_witness 50)).
Definition raise_all_with (s : Combination) : Combination :=
  fix_function (lam ('K1 (raise_all_fold s)) raise_all_seed).

Definition raise_all : Combination := raise_all_with raise_emp.

(** [raise_all] is [fix[lam[raise_all_body, raise_all_seed]]]. *)
Definition raise_all_body : Combination := 'K1 (raise_all_fold raise_emp).

Lemma raise_all_is_fix :
  raise_all = fix_function (lam raise_all_body raise_all_seed).
Proof. reflexivity. Qed.

(** The optimisation: erase inside the body. *)
Definition erased_raise_all : Combination := fix_erase raise_all_body raise_all_seed.

(** Erasure inside the body removes the tag and ghost of [raise_emp] and
    of the [increment_salary] nested in it; nothing else changes. *)
Lemma erased_raise_all_shape :
  erased_raise_all = raise_all_with (erase (raise_emp_with (erase increment_salary))).
Proof. vm_compute; reflexivity. Qed.

Lemma raise_all_with_typed : forall s S,
  infer AI @ s ==> Sm S -> type_app AI @ S @r ('Employee) ==> Sm ('Employee) ->
  infer AI @ raise_all_with s ==> Sm ('List['Employee] --> 'List['Employee]).
Proof.
  intros s S Hs HS; unfold raise_all_with.
  assert (Hn : infer AI @ nil_value (employee_witness 50) ==> Sm ('List['Employee]))
    by (apply infer_nil_value; [exact company_list|apply employee_at_typed]).
  assert (Hm : infer AI @ map_step_value s ==> Sm (map_step_value S)).
  { unfold map_step_value.
    repeat first [apply infer_cons_step | exact Hs | eapply infer_I
      | eapply infer_fork | eapply infer_stem | eapply infer_leaf | eapply type_app_I
      | eapply type_app_K_ev
      | eapply type_app_stem_ev; eapply type_app_stem_structural; intros; discriminate
      | new_S; [intros; discriminate |] ]. }
  assert (Hl : infer AI @ raise_all_fold s ==> Sm ('List['Employee] --> 'List['Employee])).
  { unfold raise_all_fold; eapply infer_lam;
      [apply infer_foldright_value; [exact Hm|exact Hn]|exact Hn|].
    apply type_app_foldright_value; apply type_app_map_step; [exact company_list|exact HS]. }
  apply infer_fix_function; eapply infer_lam.
  - apply infer_K1; exact Hl.
  - unfold raise_all_seed; eapply infer_lam;
      [apply infer_K1; exact Hn|exact Hn|apply type_app_K_ev].
  - apply type_app_K_ev.
Qed.

Lemma raise_all_typed :
  infer AI @ raise_all ==> Sm ('List['Employee] --> 'List['Employee]).
Proof.
  eapply raise_all_with_typed; [exact raise_emp_typed|].
  apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** Typing of the erased fixfunction: twice [erase_typing] (optimisation.v),
    once for the nested [increment_salary] and once for [raise_emp]. *)
Lemma erased_raise_all_typed :
  infer AI @ erased_raise_all ==> Sm ('List['Employee] --> 'List['Employee]).
Proof.
  rewrite erased_raise_all_shape.
  pose proof (infer_increment_salary AI company_salary company_number) as Hinc.
  destruct (erase_typing_but AI paper_excluded increment_salary _ ('Salary) ('Salary)
    paper_plain_intro_sound_excl paper_excluded_tag_free ltac:(vm_compute; reflexivity) Hinc
    ltac:(apply type_app_abstract; apply funty_eliminator_eval))
    as [G [HG HGapp]].
  pose proof (raise_emp_with_typed _ _ HG HGapp) as Hr.
  destruct (erase_typing_but AI paper_excluded (raise_emp_with (erase increment_salary)) _
    ('Employee) ('Employee)
    paper_plain_intro_sound_excl paper_excluded_tag_free ltac:(vm_compute; reflexivity) Hr
    ltac:(apply type_app_abstract; apply funty_eliminator_eval))
    as [S [HS HSapp]].
  exact (raise_all_with_typed _ _ HS HSapp).
Qed.

(** The same, as an instance of the general fixfunction statement
    [fix_erase_typing_iff]: the erased body keeps the endofunction type. *)
Lemma erased_raise_all_body_typed :
  exists B', infer AI @ head_erase raise_all_body ==> Sm B' /\
    type_app AI @ B' @r ('List['Employee] --> 'List['Employee]) ==>
      Sm ('List['Employee] --> 'List['Employee]).
Proof.
  apply (fix_erase_typing_iff AI raise_all_body raise_all_seed).
  - rewrite <- raise_all_is_fix; exact raise_all_typed.
  - exact erased_raise_all_typed.
Qed.

(** ** Evaluation on the workers of department_2025 *)

Definition workers_2025 :=
  cons_value (employee_at 2 56)
    (cons_value (employee_at 3 57) (nil_value (employee_witness 50))).
Definition workers_2026 :=
  cons_value (employee_at 2 57)
    (cons_value (employee_at 3 58) (nil_value (employee_witness 50))).

Lemma raise_all_workers :
  raise_all @ workers_2025 ==> workers_2026 /\
  erased_raise_all @ workers_2025 ==> workers_2026.
Proof.
  assert (H : forall c, (forall i n, c @ employee_at i n ==> employee_at i (S n)) ->
    raise_all_with c @ workers_2025 ==> workers_2026).
  { intros c Hc; unfold raise_all_with, workers_2025, workers_2026.
    apply fix_function_eval_step.
    eapply eval_appl; [apply lam_eval; evaluate|].
    unfold raise_all_fold; apply lam_eval; apply foldright_value_eval.
    eapply cell_apply; [|exact (map_step_eval c _ _ _ (Hc 2 56))].
    eapply cell_apply; [apply nil_apply|exact (map_step_eval c _ _ _ (Hc 3 57))]. }
  split; [apply H; exact raise_emp_eval|].
  rewrite erased_raise_all_shape; apply H; intros i n.
  apply (proj1 (erase_app_eval_iff _ _ _)).
  apply raise_emp_with_eval; intro m.
  apply (proj1 (erase_app_eval_iff _ _ _)); apply increment_salary_eval.
Qed.

(** Erasing an unsafe head can leave an untyped expression: the triage
    query [tq[tt, Kq tt, Kq (Kq tt)]] applied to [tt] is typed, its head is
    not safe, and the optimised expression has no type (computed). *)
Lemma optimise_unsafe_head_untyped :
  heads_avoid paper_excluded ('tq['tt, 'Kq 'tt, 'Kq ('Kq 'tt)] @ 'tt) = false /\
  (exists T, infer_expression paper_ontology @ ('tq['tt, 'Kq 'tt, 'Kq ('Kq 'tt)] @ 'tt) ==> Sm T) /\
  ~ (exists T, infer_expression paper_ontology @ optimise_fn ('tq['tt, 'Kq 'tt, 'Kq ('Kq 'tt)] @ 'tt) ==> Sm T).
Proof.
  split; [vm_compute; reflexivity|split].
  - eexists; apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity.
  - intros [T H].
    assert (HL : infer_expression paper_ontology @ optimise_fn ('tq['tt, 'Kq 'tt, 'Kq ('Kq 'tt)] @ 'tt) ==> Lf)
      by (apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity).
    pose proof (eval_deterministic _ _ H _ HL); discriminate.
Qed.
