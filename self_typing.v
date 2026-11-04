(** * Self-typing (paper: Concrete Types).
    Concrete programs are self-typed (each is the only value of its type);
    closed normal combinators, fixfunctions and the mu-recursive programs
    are concrete, so the concrete programs form a Turing-complete class;
    the typing programs are concrete whenever the declarations is; and so
    [infer] has type [infer] under the paper's declarations.
    Build order: this file follows paper_ontology.v, since the headline
    theorem [paper_infer_self_typed] concerns that declarations.  The recursion
    machinery used by the size query is in recursion.v. *)

From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions queries updates data_types arrays conditionals paper_ontology.
From Stdlib Require Import List Lia Arith.
Import ListNotations.
Set Default Proof Using "Type".

(** ** Concrete programs are self-typed *)

Theorem concrete_is_self_typed :
  forall AI c, concrete c -> infer AI @ c ==> Sm c.
Proof. intros AI c Hc; apply infer_tag_free, concrete_tag_free; exact Hc. Qed.

(** A concrete type has exactly one value: itself. *)
Theorem concrete_type_unique_value : forall AI v T,
  infer AI @ v ==> Sm T ->
  concrete T ->
  v = T.
Proof.
  intros AI v T Hv HT.
  eapply infer_tag_free_inv; [exact Hv | apply concrete_tag_free; exact HT].
Qed.

(** The identity is implicitly polymorphic: it applies at every type. *)
Theorem identity_polymorphic : forall AI u U,
  infer AI @ u ==> Sm U ->
  infer_expression AI @ ('I @ u) ==> Sm U.
Proof.
  intros AI u U Hu; eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_I.
  - apply infer_expression_stem; exact Hu.
  - apply type_app_I.
Qed.

(** ** Which programs are concrete *)

(** Paper-facing: closed pure normal combinators compile to concrete
    (label-free) trees. *)
Theorem normal_combinators_are_concrete : forall t,
  pure_nf t -> no_ref t = true -> concrete (to_tree t).
Proof.
  intros t Hp Hc; destruct (pure_invariants t Hp) as [Hi Hn].
  apply closed_lf; auto.
Qed.

Lemma bz_concrete : concrete bz.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma dup_z_concrete : concrete dup_z.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Theorem Z_preserves_concrete : forall f, concrete f -> concrete (Z f).
Proof. intros f Hf; pose proof bz_concrete; pose proof dup_z_concrete; unfold Z; lf_tac. Qed.

Lemma konst_concrete : forall m c, concrete c -> concrete (konst m c).
Proof. induction m; intros c Hc; cbn [konst]; auto; lf_tac; auto. Qed.

Lemma sel_concrete : forall j, concrete (sel j).
Proof. induction j; cbn [sel]; lf_tac. Qed.

Lemma proj_concrete : forall i j, concrete (proj i j).
Proof. intros; apply konst_concrete, sel_concrete. Qed.

Lemma projs_concrete : forall n p, Forall concrete (projs p n).
Proof. induction n; intros p; cbn [projs]; constructor; auto using proj_concrete. Qed.

Lemma phi_concrete : forall m, concrete (phi m).
Proof. induction m; cbn [phi]; lf_tac. Qed.

Lemma sapp_concrete :
  forall m A B, concrete A -> concrete B -> concrete (sapp m A B).
Proof. intros m A B HA HB; pose proof (phi_concrete m); unfold sapp; lf_tac. Qed.

Lemma appn_concrete :
  forall m As F, concrete F -> Forall concrete As ->
  concrete (appn m F As).
Proof.
  intros m As; induction As as [|A As IH]; intros F HF HAs; cbn [appn fold_left]; auto.
  inversion HAs; subst; apply IH; auto; apply sapp_concrete; auto.
Qed.

Lemma rec_prog_concrete :
  forall k G H, concrete G -> concrete H -> concrete (rec_prog k G H).
Proof.
  intros k G H HG HH; unfold rec_prog; apply Z_preserves_concrete.
  unfold rec_body; apply appn_concrete; [|repeat (apply Forall_cons || apply Forall_nil); auto using proj_concrete].
  apply konst_concrete; unfold rec_D.
  assert (HT : concrete (rec_T k H)).
  { unfold rec_T; apply appn_concrete; [auto using konst_concrete|].
    repeat (apply Forall_cons || apply Forall_nil); auto using proj_concrete, projs_concrete.
    apply appn_concrete; [apply proj_concrete|].
    constructor; auto using proj_concrete, projs_concrete. }
  lf_tac.
Qed.

Lemma min_prog_concrete :
  forall k F, concrete F -> concrete (min_prog k F).
Proof.
  intros k F HF.
  assert (Hret : concrete (min_ret k)) by apply proj_concrete.
  assert (Hrec : concrete (min_rec k)).
  { unfold min_rec; apply appn_concrete; [apply proj_concrete|].
    constructor; auto using projs_concrete.
    apply appn_concrete; [apply konst_concrete; exact lf_leaf|].
    repeat (apply Forall_cons || apply Forall_nil); apply proj_concrete. }
  assert (HE : concrete (min_E k)).
  { unfold min_E, min_ret in *; cbn [proj konst] in *; lf_tac. }
  unfold min_prog; apply appn_concrete.
  - apply konst_concrete; unfold min_search_prog; apply Z_preserves_concrete.
    unfold min_body; apply appn_concrete.
    + unfold min_test; apply appn_concrete; [apply konst_concrete; exact HE|].
      repeat (apply Forall_cons || apply Forall_nil).
      apply appn_concrete; [apply konst_concrete; exact HF|].
      constructor; auto using proj_concrete, projs_concrete.
    + repeat (apply Forall_cons || apply Forall_nil); auto using proj_concrete, projs_concrete.
  - constructor; auto using projs_concrete.
    apply konst_concrete; exact lf_leaf.
Qed.

Scheme mu_fun_ind2 := Induction for mu_fun Sort Prop
  with mu_funs_ind2 := Induction for mu_funs Sort Prop.
Combined Scheme mu_fun_mutind from mu_fun_ind2, mu_funs_ind2.

Lemma compile_concrete_all :
  (forall n (f : mu_fun n), concrete (compile f)) /\
  (forall n m (gs : mu_funs n m), Forall concrete (compiles gs)).
Proof.
  apply (mu_fun_mutind
    (fun n f => concrete (compile f))
    (fun n m gs => Forall concrete (compiles gs)));
    cbn [compile compiles]; intros.
  - apply konst_concrete; exact lf_leaf.
  - lf_tac.
  - apply proj_concrete.
  - apply appn_concrete; auto using konst_concrete.
  - apply rec_prog_concrete; auto.
  - apply min_prog_concrete; auto.
  - constructor.
  - constructor; auto.
Qed.

Lemma compile_concrete : forall n (f : mu_fun n), concrete (compile f).
Proof. exact (proj1 compile_concrete_all). Qed.

Lemma compile_tag_free : forall n (f : mu_fun n), tag_free (compile f) = true.
Proof. intros; apply concrete_tag_free, compile_concrete. Qed.

(** * The conjecture, for mu-recursive functions

    Every partial mu-recursive function of positive arity is represented
    by a tag-free program: on the numerals of any arguments at which it
    is defined, the program computes the numeral of its value. *)

Lemma mu_recursive_tag_free :
  forall n (f : mu_fun n),
    { P : Combination |
      tag_free P = true /\
      forall xs y, mu_eval n f xs y -> apps P (map num xs) ==> num y }.
Proof.
  intros n f; exists (compile f); split;
    [apply compile_tag_free | intros; apply compile_sound; auto].
Qed.

(** Paper-facing: every partial mu-recursive function of positive arity
    is represented by a concrete (label-free) program. *)
Theorem concrete_is_Turing_complete :
  forall n (f : mu_fun n),
    { P : Combination |
      concrete P /\
      forall xs y, mu_eval n f xs y -> apps P (map num xs) ==> num y }.
Proof.
  intros n f; exists (compile f); split;
    [apply compile_concrete | intros; apply compile_sound; auto].
Qed.

(** ** The typing programs are concrete *)


Lemma paper_ontology_self_typed :
 infer paper_ontology @ paper_ontology ==> Sm paper_ontology.
Proof. apply infer_tag_free; apply paper_ontology_tag_free. Qed.

(** A concrete type has exactly one value under the combined declarations. *)
Lemma paper_ontology_concrete_type_unique_value : forall v T,
 infer paper_ontology @ v ==> Sm T ->
 concrete T ->
 v = T.
Proof. exact (concrete_type_unique_value paper_ontology). Qed.

(** * Concreteness of the typing programs

    A label is the identity [S2[K, K1 n]] carrying the name
    [n]; concreteness ([concrete], tree.v)
    implies tag-freeness ([concrete_tag_free]).  No typing program contains a
    label: wherever a type is tagged at run time, as in [\x. tagged[x,n]],
    the label is built by [make_label] (through [tagger[n]]) instead of
    being stored as a constant, and literal type patterns compile to
    concrete testers. *)
Section Concreteness.
Local Transparent equal Z.

(** Array append is concrete, hence self-typed. *)
Lemma array_append_concrete : concrete array_append.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma paper_ontology_concrete : concrete paper_ontology.
Proof.
  apply concreteb_sound.
  unfold paper_ontology, company_ontology, company_base_ontology,
    employee_case, department_case, record_case, generic_ontology,
    generic_ontology_body, query_case_builder, update_case_builder.
  cbn [query_case_builder_package update_case_builder_package].
  vm_compute; reflexivity.
Qed.

(** For any concrete declarations, the typing programs are concrete:
    their code is fixed apart from the declarations, which never occurs in
    the [K] position of a label. *)
Local Ltac lf_ai AI H :=
  repeat match goal with
  | |- concrete AI => exact H
  | |- concrete Lf => exact I
  | |- concrete 'I => apply lf_I
  | |- concrete (Sm _) => apply lf_stem
  | |- concrete (Fk _ _) => apply lf_fork; [ | | discriminate ]
  | |- concrete ?t =>
      first [ apply concreteb_sound; vm_compute; reflexivity
            | let t' := eval hnf in t in progress change (concrete t') ]
  end.

Lemma type_app_concrete : forall AI,
  concrete AI -> concrete (type_app AI).
Proof.
  intros AI H; unfold type_app; apply Z_preserves_concrete; lf_ai AI H.
Qed.
Theorem infer_self_typed : forall AI, concrete AI ->
  infer AI @ infer AI ==> Sm (infer AI).
Proof. intros AI H; apply infer_concrete_self_typed, H. Qed.

Lemma infer_concrete : forall AI,
  concrete AI -> concrete (infer AI).
Proof.
  intros AI H; unfold infer; apply Z_preserves_concrete; lf_ai AI H.
Qed.
Lemma infer_expression_concrete : forall AI,
  concrete AI -> concrete (infer_expression AI).
Proof.
  intros AI H; unfold infer_expression; apply Z_preserves_concrete; lf_ai AI H.
Qed.

Lemma type_app_all_concrete : concrete (type_app paper_ontology).
Proof.
  apply type_app_concrete;
    apply paper_ontology_concrete.
Qed.
Lemma infer_all_concrete : concrete (infer paper_ontology).
Proof.
  apply infer_concrete;
    apply paper_ontology_concrete.
Qed.
Lemma infer_expression_all_concrete :
  concrete (infer_expression paper_ontology).
Proof.
  apply infer_expression_concrete;
    apply paper_ontology_concrete.
Qed.

(** The typing programs of the combined declarations are concrete. *)
Lemma all_typing_concrete :
  concrete paper_ontology /\ concrete (type_app paper_ontology) /\
  concrete (infer paper_ontology) /\
  concrete (infer_expression paper_ontology).
Proof.
  (* Not [repeat split]: it would unfold [concrete] on the trees. *)
  exact (conj paper_ontology_concrete (conj type_app_all_concrete
    (conj infer_all_concrete infer_expression_all_concrete))).
Qed.
End Concreteness.

(** Self-typing of inference needs only that the declarations are concrete. *)
Theorem paper_infer_self_typed :
 infer paper_ontology @ infer paper_ontology ==> Sm (infer paper_ontology).
Proof. apply infer_self_typed, paper_ontology_concrete. Qed.

(** * Concrete dither

    With the concrete booleans [K] and [KI], a recursive function that
    negates its own result is concrete, so it is its own type, and it has
    no value at any argument.  Its type is as recursive as the program. *)
From Stdlib Require Import String Arith Lia.
From TreeTyping Require Import functions data_types.
Local Open Scope string_scope.
Definition cneg := Eval cbn in to_tree (star "b" (Ref "b" @@ Val 'KI @@ Val 'K)).
Definition cdither_body := Eval cbn in to_tree (star "r" (Val cneg ''C Ref "r")).
Definition cdither := Z cdither_body.

Lemma cdither_concrete : concrete cdither.
Proof. apply Z_preserves_concrete; apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma compose_evaln_inv : forall n g f x v,
  evaln n ((g 'C f) @ x) v -> exists m w, m < n /\ evaln m (f @ x) w.
Proof.
  intros n g f x v H; invert_evaln.
  match goal with H : evaln ?m (f @ x) ?w |- _ => exists m, w; split; [lia|exact H] end.
Qed.

Lemma cdither_step : cdither_body @ cdither ==> cneg 'C cdither.
Proof. unfold cdither_body; cbn; d_eval. Qed.

Lemma cdither_no_value : forall x v, ~ (cdither @ x ==> v).
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

