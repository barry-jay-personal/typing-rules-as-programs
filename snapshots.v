(** * Step 83 (stage 10): snapshots of evaluation, examples.

    - [rule_step_not_typing]: the step of Figure 4 alone does not preserve
      typing, even for an ontology sound by typing: by the rule for [S2]
      the application of a tag exposes its bare label.  This is why
      [step] applies the carrier of a tag in one step.
    - [name_test_snapshot_untyped]: [flip_here @ tt] is typed at
      [paper_ontology], and its first rule-by-rule snapshot is not.
    - [flip_here_snapshot_untyped]: neither is its first snapshot under
      [step], which exposes the carrier of the update; the update
      declaration is not sound by typing.
    - [size_snapshot_untyped]: [size @ tt] is typed but its first snapshot
      is not, since it exposes the triage carrier of [size] at [Bool].
    - [dither_pending_typed]: every number of negations of [dither @ tt]
      has type [Bool] at [paper_ontology]. *)

From Stdlib Require Import String List Bool Lia Arith.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing divergence size_queries dither_queries optimisation_rt steps.

Import ListNotations.
Local Notation PO := paper_ontology.
Ltac by_runN := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** An expression with no expression type. *)
Definition untyped (O e : Combination) : Prop := ~ exists T, infer_expression O @ e ==> Sm T.

Lemma untyped_by_run : forall O e, infer_expression O @ e ==> Lf -> untyped O e.
Proof. intros O e HL [T H]; pose proof (eval_deterministic _ _ H _ HL); discriminate. Qed.

(** ** The rule for [S2] on a tag exposes its label *)

(** The first rule-by-rule snapshot of the application of a tag is
    untyped, for every ontology. *)
Lemma rule_step_tag_untyped : forall O c n u, untyped O (rule_step ('tagged[c,n] @ u)).
Proof.
  intros O c n u [T H]; cbn in H.
  destruct (ie_inv O _ _ H) as [[u0 [E _]]|[e1 [e2 [T1 [T2 [E [_ [H2 _]]]]]]]]; [discriminate|].
  inversion E; subst e1 e2.
  destruct (ie_inv O _ _ H2) as [[u0 [E2 _]]|[e1 [e2 [T3 [T4 [E2 [H3 _]]]]]]]; [discriminate|].
  inversion E2; subst e1 e2.
  destruct (ie_inv O _ _ H3) as [[l [E3 Hl]]|[e1 [e2 [T5 [T6 [E3 _]]]]]]; [|discriminate].
  inversion E3; subst l.
  exact (bare_label_untyped O n _ Hl).
Qed.

(** An ontology of Booleans alone, sound by typing. *)
Definition O_bool : Combination := rows [(bool_nm, D_bool)].

Lemma O_bool_sound_by_typing : ontology_sound_by_typing O_bool.
Proof.
  intros n D H.
  pose proof (rows_spec [(bool_nm, D_bool)] n (tp O_bool)) as Hs.
  pose proof (eval_deterministic _ _ H _ Hs) as E.
  cbn [lookup] in E; destruct (combination_eq_dec bool_nm n) as [<-|]; [|discriminate].
  inversion E; subst D; apply bool_decl_sound_by_typing.
Qed.

(** The step of Figure 4 alone does not preserve typing: at the sound
    ontology [O_bool], [tt @ (ff * tt)] has type [Bool] but its first
    rule-by-rule snapshot has none. *)
Theorem rule_step_not_typing :
  ontology_sound_by_typing O_bool /\
  infer_expression O_bool @ (tt @ (ff '* tt)) ==> Sm Bool /\
  untyped O_bool (rule_step (tt @ (ff '* tt))).
Proof.
  split; [exact O_bool_sound_by_typing|split; [by_runN|apply rule_step_tag_untyped]].
Qed.

(** ** Snapshots at [paper_ontology] *)

Definition flip_here : Combination := special_type Bool neg identity_update.

(** If a step applied only one rule then the first snapshot of the
    typed expression [flip_here @ tt] would be untyped. *)
Theorem name_test_snapshot_untyped :
  infer_expression PO @ (flip_here @ tt) ==> Sm Bool /\
  untyped PO (rule_steps 1 (flip_here @ tt)).
Proof. split; [by_runN|apply rule_step_tag_untyped]. Qed.

(** Under [step] too: the first snapshot exposes the carrier of the
    update at the abstract type [Bool]. *)
Theorem flip_here_snapshot_untyped : untyped PO (steps 1 (flip_here @ tt)).
Proof. apply untyped_by_run; by_runN. Qed.

(** [size @ tt] has an expression type, but one of its snapshots has
    none.  Since step 89 ([size] is a recursive query by updates) the
    first eight snapshots are typed and the ninth is not. *)
Theorem size_snapshot_untyped :
  infer_expression PO @ (size @ tt) ==> Sm Nat /\
  exists k, untyped PO (steps k (size @ tt)).
Proof. split; [exact size_tt_typed|exists 9; apply untyped_by_run; by_runN]. Qed.

(** ** Pending negations of [dither @ tt] *)

Fixpoint pending (k : nat) : Combination :=
  match k with
  | O => dither @ tt
  | S k => Fk (Sm neg) (pending k)
  end.

Lemma infer_neg_PO : infer PO @ neg ==> Sm NegT. Proof. by_runN. Qed.
Lemma neg_type_app_PO : tp PO @ NegT @r Bool ==> Sm Bool. Proof. by_runN. Qed.

(** The expression that applies [neg] any number of times to [dither @ tt]
    has type [Bool], although [dither @ tt] has no value. *)
Theorem dither_pending_typed : forall k, infer_expression PO @ pending k ==> Sm Bool.
Proof.
  induction k as [|k IH]; cbn [pending].
  - exact dither_tt_infer_expression.
  - eapply ie_fork; [apply ie_stem, infer_neg_PO|exact IH|exact neg_type_app_PO].
Qed.
