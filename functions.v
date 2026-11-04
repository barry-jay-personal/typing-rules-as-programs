(** * Functions (paper: Functions).

    Lambda programs, function type introduction and recursive functions,
    and dither_fn, which is typed but has no value. *)


(** Typed function programs using the reserved core arrow constructors.

    Unary arrow representation and constructor checking live below type
    application. This file proves inference rules and supplies executable
    examples. Direct abstractions store evidence directly in a decoration, so the declarations
    needs no entry for evidence or functions. *)
From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.

From TreeTyping Require Import booleans.
Set Default Proof Using "Type".
Local Opaque type_app infer equal equal1.
Open Scope string_scope.
Definition lam (f u : Combination) : Combination :=
  'tagged['decorate[f,u],fun_nm].

(** Term-level form of [lam], for programs compiled by a surrounding
    package. *)
Definition lam2 (f u : Term) : Term :=
  ''tagged[''decorate[f,u],Val fun_nm].


(** Recursive functions use a distinct hardwired constructor.  Retagging the
    recursive occurrence prevents its concrete self-type from being confused
    with a function type. *)
Definition fix_function (f : Combination) : Combination :=
  'tagged[Z (f 'C tagged_fun), fun_nm].

Notation "'fix [ f ]" := (fix_function f) (at level 0).


Definition funty2 (U V : Term) : Term :=
  ''tagged[funty_eliminator2 U V,Val fun_nm].

Notation "U -->> V" := (funty2 U V) (at level 65).


(** [function_abstractor_direct_eval] is in soundness.v. *)


Section DirectFunctionApplication.
Variable AI : Decl.
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation type_app := (typing.type_app AI).
Lemma type_app_stem_function : forall app F U V,
  app @ F @r U ==> Sm V ->
  type_app_stem @ app @r (Sm ('K1 ('decorate[F,U])))
    @r ('S2['K,'K1 fun_nm]) ==> Sm (U --> V).
Proof using AI.
  intros; apply type_app_stem_tagged; apply function_declared.
  apply function_abstractor_direct_eval; assumption.
Qed.

End DirectFunctionApplication.

Lemma tagged_fun_eval : forall x,
  tagged_fun @ x ==> 'tagged[x,fun_nm].
Proof. intros x; unfold tagged_fun; evaluate. Qed.

(** [lam[f,u] @ x ~~> f @ x] (function-types.tex). *)
Lemma lam_eval : forall f d u v, f @ u ==> v -> lam f d @ u ==> v.
Proof. intros; unfold lam; apply tagged_eval; apply wait_eval; evaluate. Qed.

(** [fix[f] @ x ~~> f @ fix[f] @r x] (function-types.tex). *)
Lemma fix_function_eval_step : forall f u v,
  f @ fix_function f @r u ==> v -> fix_function f @ u ==> v.
Proof.
  intros f u v H; inv_out H.
  unfold fix_function at 1; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|eassumption].
  eapply eval_c; eapply eval_appr; [apply tagged_fun_eval|eassumption].
Qed.


Lemma tagged_fun_tag_free : tag_free tagged_fun = true.
Proof. unfold tagged_fun; tag_free_tac. Qed.
Section FunctionTypeFacts.
Variable AI : Decl.
Notation "F # U" := (type_app AI @ F @r U)
  (at level 45, left associativity).

Lemma infer_fun_tagged : forall f F u U V,
  infer AI @ f ==> Sm F ->
  infer AI @ u ==> Sm U ->
  type_app AI @ F @r U ==> Sm V ->
  infer AI @ ('tagged['decorate[f,u],fun_nm]) ==> Sm (U --> V).
Proof.
  intros f F u U V Hf Hu Hfun.
  eapply infer_fork.
  - eapply infer_stem; eapply infer_K1.
    repeat first
      [ exact Hf | exact Hu
      | eapply infer_fork | eapply infer_stem | eapply infer_leaf
      | eapply type_app_I | eapply type_app_K_ev
      | eapply type_app_stem_ev; eapply type_app_stem_structural;
        intros; discriminate
      | new_S; [intros; discriminate |]
      ].
  - eapply infer_fork.
    + eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    + eapply infer_K1; unfold fun_nm; first [eapply infer_leaf | eapply infer_K1; eapply infer_leaf].
    + eapply type_app_stem_ev; eapply type_app_stem_structural;
        intros; discriminate.
  - eapply type_app_stem_ev; eapply type_app_stem_function; eauto.
Qed.

Theorem infer_lam : forall f F u U V,
  infer AI @ f ==> Sm F ->
  infer AI @ u ==> Sm U ->
  type_app AI @ F @r U ==> Sm V ->
  infer AI @ lam f u ==> Sm (U --> V).
Proof.
  intros f F u U V Hf Hu Happ.
  unfold lam; eapply infer_fun_tagged; eauto.
Qed.

Theorem infer_fix_function : forall f U V,
  infer AI @ f ==> Sm ((U --> V) --> (U --> V)) ->
  infer AI @ fix_function f ==> Sm (U --> V).
Proof.
  intros f U V Hf.
  assert (Htagged_fun : infer AI @ tagged_fun ==> Sm tagged_fun).
  { eapply infer_tag_free; apply tagged_fun_tag_free. }
  assert (Hcomposition :
    infer AI @ (f 'C tagged_fun) ==>
      Sm (((U --> V) --> (U --> V)) 'C tagged_fun)).
  { infer_tac. }
  unfold fix_function.
  eapply infer_fork.
  - eapply infer_stem; eapply infer_K1.
    eapply infer_Z; exact Hcomposition.
  - eapply infer_fork.
    + eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    + eapply infer_K1; first [eapply infer_leaf | unfold fun_nm; eapply infer_K1; eapply infer_leaf].
    + eapply type_app_stem_ev; eapply type_app_stem_structural;
        intros; discriminate.
  - eapply type_app_stem_ev; eapply type_app_stem_recursive_function.
Qed.

(** The application rule. *)
Theorem infer_application : forall f F u U V,
  infer AI @ f ==> Sm F ->
  infer AI @ u ==> Sm U ->
  type_app AI @ F @r U ==> Sm V ->
  infer_expression AI @ (f @ u) ==> Sm V.
Proof.
  intros f F u U V Hf Hu Happ; eapply infer_expression_fork;
    [apply infer_expression_stem; exact Hf|apply infer_expression_stem; exact Hu|exact Happ].
Qed.


End FunctionTypeFacts.

(** Inference is structural on a raw composition.  When [g] and [f] are
    functions, [type_app_compose] subsequently shows that this inferred
    composite type maps [U] to [W]. *)

Lemma infer_composition : forall AI g f U V W,
  infer AI @ g ==> Sm (V --> W) ->
  infer AI @ f ==> Sm (U --> V) ->
  infer AI @ (g 'C f) ==> Sm ((V --> W) 'C (U --> V)).
Proof.
  intros AI g f U V W Hg Hf.
  infer_tac.
Qed.

(** Familiar function values obtained from concrete combinators. *)
Definition typed_identity (domain_witness : Combination) : Combination :=
  lam 'I domain_witness.

Lemma infer_typed_identity : forall (AI : Decl) domain_witness U,
  infer AI @ domain_witness ==> Sm U ->
  infer AI @ typed_identity domain_witness ==> Sm (U --> U).
Proof.
  intros AI domain_witness U Hd; unfold typed_identity.
  eapply infer_lam; [ apply infer_I | exact Hd | apply type_app_I].
Qed.

Lemma typed_identity_operation : forall domain_witness x,
  typed_identity domain_witness @ x ==> x.
Proof.
  intros domain_witness x; unfold typed_identity, lam.
  eapply tagged_eval; eapply wait_eval; evaluate.
Qed.

Definition typed_compose
    (g f domain_witness : Combination) : Combination :=
  lam (g 'C f) domain_witness.

Lemma infer_typed_compose : forall (AI : Decl) g f domain_witness U V W,
  infer AI @ g ==> Sm (V --> W) ->
  infer AI @ f ==> Sm (U --> V) ->
  infer AI @ domain_witness ==> Sm U ->
  infer AI @ typed_compose g f domain_witness ==> Sm (U --> W).
Proof.
  intros AI g f domain_witness U V W Hg Hf Hd.
  unfold typed_compose; eapply infer_lam.

  - eapply infer_composition; eauto.
  - exact Hd.
  - eapply type_app_compose; [solve [reject_name]| | |].
    + unfold funty; intros E N Heq; discriminate Heq.
    + eapply type_app_abstract; apply funty_eliminator_eval.
    + eapply type_app_abstract; apply funty_eliminator_eval.
Qed.

Lemma typed_compose_operation : forall g f domain_witness x result,
  (g 'C f) @ x ==> result ->
  typed_compose g f domain_witness @ x ==> result.
Proof.
  intros g f domain_witness x result H.
  unfold typed_compose, lam.
  eapply tagged_eval; eapply wait_eval; evaluate.
Qed.

(** Fixing the outer function of typed composition yields a functional on
    function values.  The body constructs the canonical tagged result rather
    than merely returning the raw composite type expression. *)
Local Definition typed_compose_with_body_package
    (g domain_witness : Combination) :
  { t : Combination |
    to_tree
      (\ "f"
        (''tagged[
          ''decorate[Val g ''C Ref "f", Val domain_witness],
          Val fun_nm])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition typed_compose_with_body g domain_witness :=
  Eval cbn in proj1_sig
    (typed_compose_with_body_package g domain_witness).

Definition typed_compose_with
    (g function_witness domain_witness : Combination) : Combination :=
  lam (typed_compose_with_body g domain_witness) function_witness.

Lemma typed_compose_with_operation : forall g function_witness
    domain_witness f,
  typed_compose_with g function_witness domain_witness @ f ==>
    typed_compose g f domain_witness.
Proof.
  intros g function_witness domain_witness f.
  unfold typed_compose_with, typed_compose_with_body, typed_compose, lam.
  eapply tagged_eval; eapply wait_eval.
  unfold typed_compose_with_body_package; cbn; evaluate.
Qed.

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

Lemma infer_typed_compose_with : forall (AI : Decl) g function_witness domain_witness
    U V W,
  infer AI @ g ==> Sm (V --> W) ->
  infer AI @ function_witness ==> Sm (U --> V) ->
  infer AI @ domain_witness ==> Sm U ->
  infer AI @ typed_compose_with g function_witness domain_witness ==>
    Sm ((U --> V) --> (U --> W)).
Proof.
  intros AI g function_witness domain_witness U V W
    Hg Hfunction Hu.
  unfold typed_compose_with; eapply infer_lam.

  - unfold typed_compose_with_body; cbn.
    repeat first [eassumption | progress infer_tac].
    all: repeat known_concrete_type_app_step.
  - exact Hfunction.
  - unfold typed_compose_with_body; cbn.
    repeat first [eassumption | progress infer_tac].
    all: repeat known_concrete_type_app_step.
    eapply type_app_stem_ev.
    eapply type_app_stem_function.
    eapply type_app_compose; [solve [reject_name]| | |].
    + unfold funty; intros E N Heq; discriminate Heq.
    + eapply type_app_abstract; apply funty_eliminator_eval.
    + eapply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** The public negation value carries both function annotations explicitly. *)
Definition typed_neg := lam neg 'tt.

Lemma typed_neg_infer : forall declarations : Decl,
  supports_booleans declarations ->
  infer declarations @ typed_neg ==> Sm ('Bool --> 'Bool).
Proof.
  intros declarations Hsupports.
  unfold typed_neg.
  eapply infer_lam.

  - eapply neg_infer; exact Hsupports.
  - eapply tt_infer; exact Hsupports.
  - apply neg_type_app.
Qed.

Opaque typed_neg.

(** [d r] is the explicitly typed composition of [typed_neg] after
    the recursive function [r]. *)
Definition dither_function :=
  typed_compose_with typed_neg typed_neg 'tt.

Lemma dither_function_infer : forall declarations : Decl,
  supports_booleans declarations ->
  infer declarations @ dither_function ==>
    Sm (('Bool --> 'Bool) --> ('Bool --> 'Bool)).
Proof.
  intros declarations Hsupports.
  unfold dither_function.
  eapply infer_typed_compose_with.

  - eapply typed_neg_infer; eauto.
  - eapply typed_neg_infer; eauto.
  - eapply tt_infer; exact Hsupports.
Qed.

(** Both annotations are Boolean witnesses.  Their inferred types, rather
    than their syntax, determine the resulting function name. *)
Definition dither_fn := 'fix[dither_function].

Lemma dither_fn_infer : forall declarations : Decl,
  supports_booleans declarations ->
  infer declarations @ dither_fn ==> Sm ('Bool --> 'Bool).
Proof.
  intros declarations Hsupports.
  unfold dither_fn.
  eapply infer_fix_function.

  - eapply dither_function_infer; eauto.
Qed.

Lemma inf_lam : forall (AI : Decl) f F d U V,
 inf AI @ f ==> Sm F -> inf AI @ d ==> Sm U ->
 app AI @ F @r U ==> Sm V -> inf AI @ lam f d ==> Sm (U --> V).
Proof. intros; eapply infer_lam; eassumption. Qed.


Unset Default Proof Using.
Transparent type_app infer equal equal1 typed_neg.

(** * Dither has no value

    The paper (Functions) observes that [dither_fn], the fixpoint of the
    typed composition of negation after the recursive call, satisfies
    [dither_fn @ tt :: Bool] while the application has no value.

    Evaluation of [dither_fn @ 'tt] unfolds the fixpoint and reduces to
    negation applied to a fresh evaluation of [dither_fn @ 'tt].  Since the
    big-step relation [eval] lives in [Prop], the recursive occurrence is
    compared with the original by the height-indexed copy [evaln] of [eval]
    (soundness.v):
    every derivation has some height, and the recursive evaluation occurs
    at strictly smaller height.  Strong induction on the height then rules
    out every derivation. *)
From Stdlib Require Import Arith Lia.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import booleans.
Set Default Proof Using "Type".

(** ** Height-indexed evaluation

    [evaln n e v], its monotonicity, its agreement with [eval] and the
    tactic [invert_evaln] are in soundness.v. *)

(** ** Height-decreasing inversions along the unfolding of [dither_fn] *)

Lemma tagged_evaln_inv : forall n f t u v,
  evaln n ('tagged[f,t] @ u) v -> exists m, m < n /\ evaln m (f @ u) v.
Proof.
  intros n f t u v H; invert_evaln.
  eexists; split; [|eassumption]; lia.
Qed.

Lemma Z_evaln_unfold_inv : forall n f x v,
  evaln n (Z f @ x) v ->
  exists m w, m < n /\ f @ Z f ==> w /\ evaln m (w @ x) v.
Proof.
  intros n f x v H; unfold Z in H; invert_evaln.
  match goal with
  | H : evaln _ (Fk (Sm dup_z) (Sm _)) _ |- _ =>
      unfold dup_z at 1 in H
  end; invert_evaln.
  match goal with
  | H : evaln _ (Fk (Sm bz) (Sm _)) _ |- _ =>
      unfold bz in H
  end; invert_evaln.
  match goal with
  | H : evaln _ (?f @ _) ?w, H' : evaln ?m (Fk (Sm ?w) (Sm _)) _ |- _ =>
      exists m, w; split; [lia|split; [|exact H']];
      apply evaln_eval in H; exact H
  end.
Qed.

Lemma typed_compose_evaln_inv : forall n g f d x v,
  evaln n (typed_compose g f d @ x) v ->
  exists m w, m < n /\ evaln m (f @ x) w.
Proof.
  intros n g f d x v H; unfold typed_compose, lam in H; invert_evaln.
  match goal with
  | H : evaln ?m (?f @ _) ?w |- exists _ _, _ /\ evaln _ (?f @ _) _ =>
      exists m, w; split; [lia|exact H]
  end.
Qed.

(** The recursive functional of [dither_fn], applied to [dither_fn] itself. *)
Lemma dither_fn_functional_eval :
  (dither_function 'C tagged_fun) @ Z (dither_function 'C tagged_fun) ==>
    typed_compose typed_neg dither_fn 'tt.
Proof.
  apply eval_c; eapply eval_appr; [apply tagged_fun_eval|].
  apply typed_compose_with_operation.
Qed.

Lemma dither_fn_tt_evaln_smaller : forall n v,
  evaln n (dither_fn @ 'tt) v ->
  exists m w, m < n /\ evaln m (dither_fn @ 'tt) w.
Proof.
  intros n v H.
  unfold dither_fn at 1, fix_function in H.
  destruct (tagged_evaln_inv _ _ _ _ _ H) as [m1 [Hm1 H1]]; clear H.
  destruct (Z_evaln_unfold_inv _ _ _ _ H1) as [m2 [w [Hm2 [Hw H2]]]]; clear H1.
  pose proof (eval_deterministic _ _ Hw _ dither_fn_functional_eval) as Heq;
    subst w; clear Hw.
  destruct (typed_compose_evaln_inv _ _ _ _ _ _ H2) as [m3 [w [Hm3 H3]]];
    clear H2.
  exists m3, w; split; [lia|exact H3].
Qed.

(** ** The theorem *)

Lemma dither_fn_tt_no_value : forall v, ~ (dither_fn @ 'tt ==> v).
Proof.
  intros v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  destruct (dither_fn_tt_evaln_smaller _ _ Hn) as [m [w [Hm Hw]]].
  exact (IH m Hm w Hw).
Qed.

(** ** The typing [dither_fn @ tt :: Bool]

    As an expression, [dither_fn @ 'tt] is the application of the quoted
    value [dither_fn] to the quoted value ['tt]. *)
Lemma dither_fn_tt_infer_expression : forall declarations : Decl,
  supports_booleans declarations ->
  infer_expression declarations @ (dither_fn @ 'tt) ==> Sm ('Bool).
Proof.
  intros declarations Hsupports.
  eapply infer_expression_fork.
  - apply infer_expression_stem; apply dither_fn_infer; exact Hsupports.
  - apply infer_expression_stem; apply tt_infer; exact Hsupports.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** Paper Theorem: dither_fn @ tt is typed, yet has no value. *)
Theorem dither_fn_typed_no_value : forall declarations : Decl,
  supports_booleans declarations ->
  infer_expression declarations @ (dither_fn @ 'tt) ==> Sm ('Bool) /\
  forall v, ~ (dither_fn @ 'tt ==> v).
Proof.
  intros declarations H; split;
  [exact (dither_fn_tt_infer_expression declarations H) | exact dither_fn_tt_no_value].
Qed.
