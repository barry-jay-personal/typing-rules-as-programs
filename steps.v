(** * Step 83 (stage 10): snapshots of evaluation, the small-step semantics.

    A small-step semantics derived from the big-step semantics (Figure 4
    of the paper), made into programs on expression trees: [step],
    agreement with Figure 4 ([steps_agree]), the program [step_prog]
    ([step_prog_eval]), and each step preserving expression typing when
    the ontology is sound by typing ([step_preserves_expression_typing]).

    Expressions are trees: [Sm v] is the value [v], [Fk e1 e2] is the
    application of [e1] to [e2].  An application [f @ u] of a value to a
    value is _ready_.  One step rewrites the first ready application in
    evaluation order (operator before argument) by the rule of Figure 4
    that applies to it ([rule_rewrite]), except that the application of a
    tagged value [tagged[c,n] @ u] goes in one step to the application
    [c @ u] of its carrier ([atomic_rewrite]).  By the rule for [S2] the
    tagged application would instead expose the bare label [label[n]] as
    a value, and a bare label has no type ([bare_label_untyped]): see
    [rule_step_not_typing] in snapshots.v.

    This replaces the semantics of [src_type36/steps.v], whose atomic
    steps were name tests; in the new design a type test is a carrier like
    any other (the run-time type [type_of_p] of updates.v), and soundness
    by typing is what types the exposed carriers. *)

From Stdlib Require Import Arith Lia String.
From BigStep Require Import tree typing soundness.
Open Scope string_scope.

(** * One rewrite per rule *)

Definition rule_rewrite (f u : Combination) : Combination :=
  match f with
  | Lf => Sm (Sm u)
  | Sm g => Sm (Fk g u)
  | Fk Lf y => Sm y
  | Fk (Sm g) h => Fk (g @ u) (h @ u)
  | Fk (Fk f0 f1) f2 =>
      match u with
      | Lf => Sm f0
      | Sm x => f1 @ x
      | Fk x y => Fk (f2 @ x) (Sm y)
      end
  end.

(** A tagged value is applied by applying its carrier; every other ready
    application is rewritten by its rule. *)
Definition atomic_rewrite (f u : Combination) : Combination :=
  match tag_of f with
  | Some (c, _) => c @ u
  | None => rule_rewrite f u
  end.

(** * Steps, for any rewrite of ready applications *)

Section Steps.

Variable rw : Combination -> Combination -> Combination.

Fixpoint step_with (e : Combination) : Combination :=
  match e with
  | Fk (Sm f) (Sm u) => rw f u
  | Fk (Sm f) (Fk _ _ as e2) => Fk (Sm f) (step_with e2)
  | Fk (Fk _ _ as e1) e2 => Fk (step_with e1) e2
  | _ => e
  end.

Fixpoint steps_with (k : nat) (e : Combination) : Combination :=
  match k with
  | O => e
  | S k => steps_with k (step_with e)
  end.

Lemma steps_with_add : forall j k e,
  steps_with (j + k) e = steps_with k (steps_with j e).
Proof. induction j; intros; cbn; auto. Qed.

Lemma steps_with_S : forall k e,
  steps_with (S k) e = step_with (steps_with k e).
Proof.
  intros k e; replace (S k) with (k + 1) by lia.
  rewrite steps_with_add; reflexivity.
Qed.

Lemma steps_with_finished : forall k v, steps_with k (Sm v) = Sm v.
Proof. induction k; intros; cbn; auto. Qed.

(** The rewrite is the rule, or it applies the carrier of a tag. *)
Hypothesis rw_ok : forall f u,
  rw f u = rule_rewrite f u \/ exists c n, f = 'tagged[c,n] /\ rw f u = c @ u.

(** ** Soundness: a step does not change the value *)

Lemma rule_rewrite_back : forall f u v,
  rule_rewrite f u ==> v -> f @ u ==> v.
Proof.
  intros f u v H; destruct f as [|g|[|g|f0 f1] h]; cbn in H.
  - inv_out H; constructor.
  - inv_out H; constructor.
  - inv_out H; constructor.
  - apply eval_s; exact H.
  - destruct u as [|x|x y].
    + inv_out H; constructor.
    + apply eval_stem; exact H.
    + apply eval_fork; exact H.
Qed.

Lemma rw_back : forall f u v, rw f u ==> v -> f @ u ==> v.
Proof.
  intros f u v H; destruct (rw_ok f u) as [E|[c [n [-> E]]]]; rewrite E in H.
  - apply rule_rewrite_back; exact H.
  - apply tagged_eval; exact H.
Qed.

Lemma step_with_back : forall e v, step_with e ==> v -> e ==> v.
Proof.
  induction e as [|a _|e1 IH1 e2 IH2]; intros v H; try exact H.
  destruct e1 as [|f|a b].
  - exact H.
  - destruct e2 as [|u|c d].
    + exact H.
    + apply rw_back; exact H.
    + cbn [step_with] in H.
      destruct (eval_arg_value_inv _ _ _ H) as [w [Hw Hfw]].
      eapply eval_arg_value; [apply IH2; exact Hw|exact Hfw].
  - cbn [step_with] in H.
    destruct (eval_pair_inv _ _ _ H) as [v1 [v2 [H1 [H2 H3]]]].
    eapply eval_pair; [apply IH1; exact H1|exact H2|exact H3].
Qed.

Lemma steps_with_sound : forall k e v, steps_with k e = Sm v -> e ==> v.
Proof.
  induction k; intros e v H; cbn in H.
  - subst; constructor.
  - apply step_with_back, IHk, H.
Qed.

(** ** Completeness: every evaluation is reached by steps *)

Inductive advances : Combination -> Combination -> Prop :=
| adv_ready : forall f u, advances (f @ u) (rw f u)
| adv_arg : forall f a b e', advances (Fk a b) e' ->
    advances (Fk (Sm f) (Fk a b)) (Fk (Sm f) e')
| adv_op : forall a b e2 e', advances (Fk a b) e' ->
    advances (Fk (Fk a b) e2) (Fk e' e2).

Inductive advances_n : nat -> Combination -> Combination -> Prop :=
| adv_zero : forall e, advances_n 0 e e
| adv_succ : forall k e e' e'', advances e e' -> advances_n k e' e'' ->
    advances_n (S k) e e''.

Lemma advances_step : forall e e', advances e e' -> step_with e = e'.
Proof. intros e e' H; induction H; [reflexivity|rewrite <- IHadvances; reflexivity|rewrite <- IHadvances; reflexivity]. Qed.

Lemma advances_n_steps : forall k e e', advances_n k e e' -> steps_with k e = e'.
Proof.
  intros k e e' H; induction H; cbn; [reflexivity|].
  rewrite (advances_step _ _ H); exact IHadvances_n.
Qed.

Lemma advances_n_trans : forall j k e e' e'',
  advances_n j e e' -> advances_n k e' e'' -> advances_n (j + k) e e''.
Proof.
  intros j k e e' e'' H; revert k e''; induction H; intros; cbn; auto.
  econstructor; eauto.
Qed.

Lemma advances_fork : forall e e', advances e e' -> exists a b, e = Fk a b.
Proof. intros e e' H; destruct H; eauto. Qed.

Lemma advances_n_op : forall k e1 e1' e2,
  advances_n k e1 e1' -> advances_n k (Fk e1 e2) (Fk e1' e2).
Proof.
  intros k e1 e1' e2 H; induction H; [constructor|].
  destruct (advances_fork _ _ H) as [a [b ->]].
  econstructor; [apply adv_op; exact H|exact IHadvances_n].
Qed.

Lemma advances_n_arg : forall k f e2 e2',
  advances_n k e2 e2' -> advances_n k (Fk (Sm f) e2) (Fk (Sm f) e2').
Proof.
  intros k f e2 e2' H; induction H; [constructor|].
  destruct (advances_fork _ _ H) as [a [b ->]].
  econstructor; [apply adv_arg; exact H|exact IHadvances_n].
Qed.

(** The rule of a ready application leads to its value, at a smaller height. *)
Lemma rule_rewrite_evaln : forall k f u v, evaln k (f @ u) v ->
  rule_rewrite f u = Sm v \/ exists j, j < k /\ evaln j (rule_rewrite f u) v.
Proof.
  intros k f u v H; inversion H; subst; cbn [rule_rewrite];
    first [left; reflexivity | right; eexists; split; [|eassumption]; lia].
Qed.

Lemma evaln_advances : forall k e v, evaln k e v -> exists j, advances_n j e (Sm v).
Proof.
  intros k; induction k as [k IH] using lt_wf_ind; intros e v H.
  assert (ready : forall f u, evaln k (f @ u) v -> exists j, advances_n j (f @ u) (Sm v)).
  { intros f u Hk.
    destruct (rw_ok f u) as [E|[c [n [-> E]]]].
    - destruct (rule_rewrite_evaln _ _ _ _ Hk) as [E2|[j [Hj Hjv]]].
      + exists 1; econstructor; [apply adv_ready|rewrite E, E2; constructor].
      + destruct (IH j Hj _ _ Hjv) as [i Hi].
        exists (S i); econstructor; [apply adv_ready|rewrite E; exact Hi].
    - destruct (evaln_tagged_inv _ _ _ _ _ Hk) as [j [Hj Hjv]].
      destruct (IH j Hj _ _ Hjv) as [i Hi].
      exists (S i); econstructor; [apply adv_ready|rewrite E; exact Hi]. }
  destruct H.
  - exists 0; constructor.
  - destruct (IH n (Nat.lt_succ_diag_r n) _ _ H) as [j Hj].
    destruct (IH n (Nat.lt_succ_diag_r n) _ _ H0) as [i Hi].
    exists (j + i); eapply advances_n_trans; [apply advances_n_op; exact Hj|exact Hi].
  - destruct (IH n (Nat.lt_succ_diag_r n) _ _ H) as [j Hj].
    destruct (IH n (Nat.lt_succ_diag_r n) _ _ H0) as [i Hi].
    exists (j + i); eapply advances_n_trans; [apply advances_n_arg; exact Hj|exact Hi].
  - apply ready; constructor.
  - apply ready; constructor.
  - apply ready; constructor.
  - apply ready; constructor; exact H.
  - apply ready; constructor.
  - apply ready; constructor; exact H.
  - apply ready; constructor; exact H.
Qed.

Lemma steps_with_complete : forall e v, e ==> v -> exists k, steps_with k e = Sm v.
Proof.
  intros e v H; destruct (eval_evaln e v H) as [n Hn].
  destruct (evaln_advances n e v Hn) as [k Hk].
  exists k; apply advances_n_steps; exact Hk.
Qed.

Lemma steps_with_agree : forall e v, e ==> v <-> exists k, steps_with k e = Sm v.
Proof.
  intros e v; split; [apply steps_with_complete|].
  intros [k Hk]; eapply steps_with_sound; exact Hk.
Qed.

End Steps.

(** * The two instances *)

Lemma atomic_rewrite_ok : forall f u,
  atomic_rewrite f u = rule_rewrite f u \/
  exists c n, f = 'tagged[c,n] /\ atomic_rewrite f u = c @ u.
Proof.
  intros f u; unfold atomic_rewrite.
  destruct (tag_of f) as [[c n]|] eqn:E; [right|left; reflexivity].
  apply tag_of_some in E; exists c, n; split; [exact E|reflexivity].
Qed.

Lemma rule_rewrite_ok : forall f u,
  rule_rewrite f u = rule_rewrite f u \/
  exists c n, f = 'tagged[c,n] /\ rule_rewrite f u = c @ u.
Proof. left; reflexivity. Qed.

(** The rule-by-rule semantics, which exposes labels. *)
Definition rule_step := step_with rule_rewrite.
Definition rule_steps := steps_with rule_rewrite.

(** The semantics used from here on. *)
Definition step := step_with atomic_rewrite.
Definition steps := steps_with atomic_rewrite.

(** Some number of steps takes [e] to [Sm v] exactly when [e ==> v]. *)
Theorem steps_agree : forall e v,
  e ==> v <-> exists k, steps k e = Sm v.
Proof. exact (steps_with_agree atomic_rewrite atomic_rewrite_ok). Qed.

Lemma rule_steps_agree : forall e v,
  e ==> v <-> exists k, rule_steps k e = Sm v.
Proof. exact (steps_with_agree rule_rewrite rule_rewrite_ok). Qed.

(** * Progress

    An expression with an expression type has no leaf in an expression
    position, and neither has any of its steps.  So each snapshot of a
    typed expression is a value or takes a step. *)

Lemma rule_rewrite_leaf_free : forall f u, leaf_free_expression (rule_rewrite f u).
Proof.
  intros f u; destruct f as [|g|[|g|f0 f1] h]; try destruct u; cbn [rule_rewrite];
    repeat constructor.
Qed.

Lemma atomic_rewrite_leaf_free : forall f u, leaf_free_expression (atomic_rewrite f u).
Proof.
  intros f u; unfold atomic_rewrite; destruct (tag_of f) as [[c n]|];
    [repeat constructor|apply rule_rewrite_leaf_free].
Qed.

Lemma step_leaf_free : forall e, leaf_free_expression e -> leaf_free_expression (step e).
Proof.
  unfold step; intros e H; induction H as [v|e1 e2 H1 IH1 H2 IH2]; [constructor|].
  destruct H1 as [f|a b Ha Hb].
  - destruct H2 as [u|c d Hc Hd].
    + apply atomic_rewrite_leaf_free.
    + cbn [step_with]; constructor; [constructor|exact IH2].
  - cbn [step_with]; constructor; [exact IH1|exact H2].
Qed.

Lemma step_progress : forall e, leaf_free_expression e ->
  (exists v, e = Sm v) \/ advances atomic_rewrite e (step e).
Proof.
  unfold step; intros e H; induction H as [v|e1 e2 H1 IH1 H2 IH2]; [left; eauto|right].
  destruct H1 as [f|a b Ha Hb].
  - destruct H2 as [u|c d Hc Hd].
    + apply adv_ready.
    + destruct IH2 as [[v Hv]|IH2]; [discriminate|].
      cbn [step_with]; apply adv_arg; exact IH2.
  - destruct IH1 as [[v Hv]|IH1]; [discriminate|].
    cbn [step_with]; apply adv_op; exact IH1.
Qed.

Lemma typed_progress : forall O e T,
  infer_expression O @ e ==> Sm T -> forall k,
  (exists v, steps k e = Sm v) \/ advances atomic_rewrite (steps k e) (steps (S k) e).
Proof.
  intros O e T H k.
  assert (Hk : leaf_free_expression (steps k e)).
  { pose proof (expression_typed_leaf_free O e T H) as H0; clear H.
    unfold steps; induction k as [|k IH]; [exact H0|].
    rewrite steps_with_S; apply step_leaf_free; exact IH. }
  replace (steps (S k) e) with (step (steps k e))
    by (unfold steps, step; symmetry; apply steps_with_S).
  apply step_progress; exact Hk.
Qed.

(* ===================================================================== *)
(** * The small-step semantics as a program of the calculus.

    [step_prog @ e ==> step e]: the program takes the expression [e] apart
    as a tree and rebuilds it with its first ready application rewritten;
    it never evaluates [e]. *)

Definition stemT (x : Term) : Term := Val Lf @@ x.
Definition forkT (x y : Term) : Term := Val Lf @@ x @@ y.

Lemma app2_split : forall F x y r,
  F @ x @r y ==> r -> exists v, F @ x ==> v /\ v @ y ==> r.
Proof.
  intros F x y r H; destruct (eval_pair_inv _ _ _ H) as [v1 [v2 [H1 [H2 H3]]]].
  inv_out H2; eauto.
Qed.

Definition rule_prog_package :
  { t | to_tree
    (\"f" (\"u"
      ((''triage [
          \"u" (stemT (stemT (Ref "u"))),
          \"g" (\"u" (stemT (forkT (Ref "g") (Ref "u")))),
          \"A" (\"h" (\"u"
            ((''triage [
                \"h" (\"u" (stemT (Ref "h"))),
                \"g" (\"h" (\"u"
                  (forkT (forkT (stemT (Ref "g")) (stemT (Ref "u")))
                          (forkT (stemT (Ref "h")) (stemT (Ref "u")))))),
                \"f0" (\"f1" (\"h" (\"u"
                  ((''triage [
                      stemT (Ref "f0"),
                      \"x" (forkT (stemT (Ref "f1")) (stemT (Ref "x"))),
                      \"x" (\"y" (forkT (forkT (stemT (Ref "h")) (stemT (Ref "x")))
                                          (stemT (Ref "y"))))])
                   @@ Ref "u"))))])
             @@ Ref "A" @@ Ref "h" @@ Ref "u")))])
       @@ Ref "f" @@ Ref "u"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition rule_prog := Eval cbn in proj1_sig rule_prog_package.

Lemma rule_prog_eval : forall f u, rule_prog @ f @r u ==> rule_rewrite f u.
Proof.
  intros f u.
  destruct f as [|g|[|g|f0 f1] h]; [| | | |destruct u as [|x|x y]];
    cbv; evaluate.
Qed.

(** [tag_prog @ f @r u] is [Sm (c @ u)] when [f = tagged[c,n]] and a leaf
    otherwise. *)
Definition tag_prog_package :
  { t | to_tree
    (\"f" (\"u"
      ((''triage [
          Val Lf,
          \"p" ((''triage [Val Lf, Val ('K1 Lf),
                   \"c" (\"n" (stemT (forkT (stemT (Ref "c")) (stemT (Ref "u")))))])
                @@ Ref "p"),
          Val ('K1 ('K1 Lf)) ])
       @@ (Val get_tagged @@ Ref "f")))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition tag_prog := Eval cbn -[get_tagged] in proj1_sig tag_prog_package.

Lemma tag_prog_eval : forall f u,
  tag_prog @ f @r u ==>
    match tag_of f with Some (c, _) => Sm (c @ u) | None => Lf end.
Proof.
  intros f u.
  destruct (tag_of f) as [[c n]|] eqn:E.
  - apply tag_of_some in E; subst f.
    pose proof (get_tagged_some c n) as Hg.
    unfold tag_prog; cbv -[get_tagged]; evaluate2; try eassumption; evaluate.
  - pose proof (get_tagged_none f (tag_of_none f E)) as Hg.
    unfold tag_prog; cbv -[get_tagged]; evaluate2; try eassumption; evaluate.
Qed.

Definition atomic_prog_package :
  { t | to_tree
    (\"f" (\"u"
      ((''triage [ Val rule_prog @@ Ref "f" @@ Ref "u", Val 'I, Val ('K1 ('K1 Lf)) ])
       @@ (Val tag_prog @@ Ref "f" @@ Ref "u")))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition atomic_prog := Eval cbn in proj1_sig atomic_prog_package.

Lemma atomic_prog_eval : forall f u, atomic_prog @ f @r u ==> atomic_rewrite f u.
Proof.
  intros f u.
  destruct (app2_split _ _ _ _ (rule_prog_eval f u)) as [vr [Hr1 Hr2]].
  destruct (app2_split _ _ _ _ (tag_prog_eval f u)) as [vn [Hn1 Hn2]].
  unfold atomic_rewrite.
  destruct (tag_of f) as [[c n]|];
    unfold atomic_prog; cbv -[rule_prog tag_prog rule_rewrite];
    evaluate.
Qed.

Definition step_body (r : Combination) : Combination :=
  to_tree
    (\"rec"
      (''triage [
         Val Lf,
         \"v" (stemT (Ref "v")),
         \"e1" (\"e2"
           ((''triage [
               \"e2" (forkT (Val Lf) (Ref "e2")),
               \"f" (\"e2"
                 ((''triage [
                     forkT (stemT (Ref "f")) (Val Lf),
                     ''wait [Val r, Ref "f"],
                     \"a" (\"b" (forkT (stemT (Ref "f"))
                                         (Ref "rec" @@ forkT (Ref "a") (Ref "b"))))])
                  @@ Ref "e2")),
               \"a" (\"b" (\"e2"
                 (forkT (Ref "rec" @@ forkT (Ref "a") (Ref "b")) (Ref "e2"))))])
            @@ Ref "e1" @@ Ref "e2"))])).

Definition step_prog_with (r : Combination) := Z (step_body r).

Lemma step_prog_with_eval : forall r rw,
  (forall f u, r @ f @r u ==> rw f u) ->
  forall e, step_prog_with r @ e ==> step_with rw e.
Proof.
  intros r rw Hr e.
  induction e as [|v _|e1 IH1 e2 IH2].
  - unfold step_prog_with; eapply Z_unfold; cbv -[Z]; evaluate.
  - unfold step_prog_with; eapply Z_unfold; cbv -[Z]; evaluate.
  - destruct e1 as [|f|a b].
    + unfold step_prog_with; eapply Z_unfold; cbv -[Z]; evaluate.
    + destruct e2 as [|u|c d].
      * unfold step_prog_with; eapply Z_unfold; cbv -[Z]; evaluate.
      * destruct (app2_split _ _ _ _ (Hr f u)) as [vr [Hr1 Hr2]].
        unfold step_prog_with; eapply Z_unfold; cbv -[Z step_with]; evaluate.
      * unfold step_prog_with in *; eapply Z_unfold; cbv -[Z step_with]; evaluate.
    + unfold step_prog_with in *; eapply Z_unfold; cbv -[Z step_with]; evaluate.
Qed.

Definition step_prog := step_prog_with atomic_prog.

(** [step_prog] performs one step. *)
Theorem step_prog_eval : forall e, step_prog @ e ==> step e.
Proof. apply step_prog_with_eval; exact atomic_prog_eval. Qed.

(* ===================================================================== *)
(** * Each step preserves expression typing, when the ontology is sound by typing.

    A step to a value is typed by evaluation preserving typing.  The rule
    for [S2] and the triage rules produce applications whose parts are
    typed by the clause of type application that typed the redex.  The
    application of a tag goes to the application of its carrier, whose
    type is given by soundness by typing of the declaration. *)

Section StepTyping.
Variable O : Combination.
Hypothesis Hsound : ontology_sound_by_typing O.

Lemma value_step_typing : forall f u w T,
  f @ u ==> w -> infer_expression O @ (f @ u) ==> Sm T ->
  infer_expression O @ Sm w ==> Sm T.
Proof using Hsound.
  intros f u w T Hw H; apply ie_stem.
  eapply preservation; [apply ontology_sound_by_typing_values; exact Hsound|exact Hw|exact H].
Qed.

Ltac kill Hf Etag := first
  [ let KE := fresh "KE" in pose proof (type_Lf_inv _ _ Hf) as KE; discriminate KE
  | let KE := fresh "KE" in destruct (type_Sm_inv _ _ _ Hf) as [? [KE _]]; discriminate KE
  | let KE := fresh "KE" in destruct (no_junk _ _ _ Hf) as [? [? [? [KE _]]]];
      first [discriminate KE | rewrite KE in Etag; cbn in Etag; discriminate Etag]
  | let KE := fresh "KE" in let Ha := fresh "Ha" in let Hi := fresh "Hi" in
      destruct (type_Fk_inv _ _ _ _ Hf) as [[? KE]|[? [? [KE [_ [Ha _]]]]]];
      [first [discriminate KE | inversion KE; subst; match goal with HL : label_of _ = None |- _ => cbn in HL; discriminate HL end]
       |inversion KE; subst; pose proof (infer_inv _ _ _ Ha) as Hi; solve [inversion Hi]] ].

Lemma ready_step_typing : forall f u T,
  infer_expression O @ (f @ u) ==> Sm T ->
  infer_expression O @ atomic_rewrite f u ==> Sm T.
Proof using Hsound.
  intros f u T H.
  destruct (ie_inv O _ _ H) as [[u0 [E _]]|[e1 [e2 [F [U [E [H1 [H2 HR]]]]]]]]; [discriminate|].
  inversion E; subst e1 e2; clear E.
  destruct (ie_inv O _ _ H1) as [[f' [E1 Hf]]|[? [? [? [? [E1 _]]]]]]; inversion E1; subst f'; clear E1.
  destruct (ie_inv O _ _ H2) as [[u' [E2 Hu]]|[? [? [? [? [E2 _]]]]]]; inversion E2; subst u'; clear E2.
  unfold atomic_rewrite.
  destruct (tag_of f) as [[c n]|] eqn:Etag.
  - (* the application of a tag: its carrier *)
    apply tag_of_some in Etag; subst f.
    pose proof (infer_inv O _ _ Hf) as Hinf;
      inversion Hinf as [| |c' n' C D Hc HC HD HG|u1 u2 U1 U2 Ht _ _ _]; subst.
    + apply tp_inv in HR; inversion HR as [n0 U0 D0 R0 HD0 HE| | | | G H0 U0 V W R0 HL| | |]; subst.
      * pose proof (eval_deterministic _ _ HD _ HD0) as ED; inversion ED; subst D0; clear ED.
        eapply ie_fork; [apply ie_stem; exact HC|apply ie_stem; exact Hu|].
        exact (Hsound n D HD C U T HG HE).
      * cbn in HL; discriminate.
    + cbn in Ht; discriminate.
  - destruct f as [|g|[|g|f0 f1] h]; cbn [rule_rewrite].
    + eapply value_step_typing; [constructor|exact H].
    + eapply value_step_typing; [constructor|exact H].
    + eapply value_step_typing; [constructor|exact H].
    + (* [S2[g,h] @ u] to [Fk (g @ u) (h @ u)] *)
      apply tp_inv in HR; inversion HR; subst; try kill Hf Etag.
      unfold app in *.
      destruct (type_Fk_inv O _ _ _ Hf) as [[m Em]|[a [b [Eab [_ [Ha [Hb _]]]]]]];
        [inversion Em; subst; match goal with HL : label_of _ = None |- _ => cbn in HL; discriminate HL end|].
      inversion Eab; subst a b.
      destruct (type_Sm_inv O _ _ Ha) as [g' [Eg Hg]]; inversion Eg; subst g'.
      eapply ie_fork;
        [eapply ie_fork; [apply ie_stem; exact Hg|apply ie_stem; exact Hu|eassumption]
        |eapply ie_fork; [apply ie_stem; exact Hb|apply ie_stem; exact Hu|eassumption]
        |eassumption].
    + (* triage *)
      apply tp_inv in HR; inversion HR; subst; try kill Hf Etag; unfold app in *;
        (destruct (type_Fk_inv O _ _ _ Hf) as [[m Em]|[a [b [Eab [_ [Ha [Hh _]]]]]]]; [discriminate Em|]);
        inversion Eab; subst a b;
        (destruct (type_Fk_inv O _ _ _ Ha) as [[m Em]|[a0 [a1 [Ea [_ [Hf0 [Hf1 _]]]]]]];
          [match goal with HR0 : reservedb _ = false |- _ => rewrite Em in HR0; cbn in HR0; discriminate HR0 end|]);
        inversion Ea; subst a0 a1.
      * pose proof (type_Lf_inv _ _ Hu) as ->; cbn [rule_rewrite].
        eapply value_step_typing; [constructor|exact H].
      * destruct (type_Sm_inv _ _ _ Hu) as [x [-> Hx]]; cbn [rule_rewrite].
        eapply ie_fork; [apply ie_stem; exact Hf1|apply ie_stem; exact Hx|eassumption].
      * destruct (type_Fk_inv _ _ _ _ Hu) as [[m Em]|[x1 [x2 [-> [_ [Hx1 [Hx2 _]]]]]]];
          [match goal with HL : label_of _ = None |- _ => rewrite Em in HL; cbn in HL; discriminate HL end|].
        cbn [rule_rewrite].
        eapply ie_fork; [|apply ie_stem; exact Hx2|eassumption].
        eapply ie_fork; [apply ie_stem; exact Hh|apply ie_stem; exact Hx1|eassumption].
Qed.

(** Each step preserves expression types. *)
Theorem step_preserves_expression_typing : forall e T,
  infer_expression O @ e ==> Sm T ->
  infer_expression O @ step e ==> Sm T.
Proof using Hsound.
  induction e as [|v _|e1 IH1 e2 IH2]; intros T H; try exact H.
  destruct e1 as [|f|a b]; [exact H| |].
  - destruct e2 as [|u|c d]; [exact H| |].
    + apply ready_step_typing; exact H.
    + destruct (ie_inv O _ _ H) as [[u0 [E _]]|[e1 [e2 [T1 [T2 [E [H1 [H2 Happ]]]]]]]]; [discriminate|].
      inversion E; subst e1 e2.
      change (step (Fk (Sm f) (Fk c d))) with (Fk (Sm f) (step (Fk c d))).
      eapply ie_fork; [exact H1|apply IH2; exact H2|exact Happ].
  - destruct (ie_inv O _ _ H) as [[u0 [E _]]|[e1' [e2' [T1 [T2 [E [H1 [H2 Happ]]]]]]]]; [discriminate|].
    inversion E; subst e1' e2'.
    change (step (Fk (Fk a b) e2)) with (Fk (step (Fk a b)) e2).
    eapply ie_fork; [apply IH1; exact H1|exact H2|exact Happ].
Qed.

Corollary steps_preserve_expression_typing : forall k e T,
  infer_expression O @ e ==> Sm T ->
  infer_expression O @ steps k e ==> Sm T.
Proof using Hsound.
  induction k; intros e T H; [exact H|].
  apply IHk, step_preserves_expression_typing, H.
Qed.
End StepTyping.
