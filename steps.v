(** * Snapshots of evaluation (paper: Towards Typed Tooling, "Snapshots of evaluation").

    A small-step semantics with a step counter, derived from the big-step
    semantics (the paper's evaluation figure), made into programs on expression trees:
    [step], [bound_eval], agreement with the evaluation rules ([steps_agree]), each step
    preserving expression typing ([step_preserves_expression_typing],
    [bound_eval_preserves_expression_typing]), queries observing every
    snapshot ([size_on_snapshots], [size_on_mid_snapshots]), a computed
    rule-by-rule snapshot of a name test without expression type
    ([name_test_snapshot_untyped]), and patching a paused expression
    ([patch_during_evaluation]). *)


(* ===================================================================== *)
(** * A small-step semantics derived from the big-step semantics (meta level).

    Expressions are trees: [Sm v] is the value [v], [Fk e1 e2] is the
    application of [e1] to [e2], and a leaf is not an evaluable expression.
    An application [Fk (Sm f) (Sm u)] of a value to a value is _ready_.
    One step rewrites the first ready application in evaluation order
    (operator before argument, as in the evaluation rules) by the big-step rule that
    applies to it; each evaluation rule that acts on a ready application
    becomes one rewrite:

    - [Lf @ u]                      to the value [Sm u]        (eval_to_stem)
    - [Sm g @ u]                    to the value [Fk g u]      (eval_to_fork)
    - [K1 y @ u]                    to the value [y]           (eval_k)
    - [S2[g,h] @ u]                 to [Fk (g @ u) (h @ u)]    (eval_s)
    - [triage[f0,f1,f2] @ Lf]       to the value [f0]          (eval_leaf)
    - [triage[f0,f1,f2] @ Sm x]     to [f1 @ x]                (eval_stem)
    - [triage[f0,f1,f2] @ Fk x y]   to [Fk (f2 @ x) (Sm y)]    (eval_fork)

    The two congruence rules [eval_appl] and [eval_appr] become the choice
    of position.  A step acts on one node at a time, not in parallel: the
    program below then needs only one traversal, which stops at
    the first ready application, and the agreement proofs follow the evaluation rules
    rule by rule.

    Name tests.  The IsNamed test [is_named n] is typed as a whole, by
    the IsNamed family: at an argument of abstract type the intermediate
    expressions of the name test (which take the argument apart with
    triage) have no type.  The derived semantics [step] treats a name test
    applied to a value as one step, to its Boolean answer.  The
    purely rule-by-rule semantics is [rule_steps].

    Finished expressions [Sm v] are left alone by further steps, and so are
    stuck expressions (those that reach a leaf in an expression position);
    a stuck expression never becomes a value. *)

From TreeTyping Require Import tree typing.
From Stdlib Require Import Arith Lia.


(** * One rewrite per rule *)

(** [rule_rewrite f u] rewrites the ready application [f @ u] by the
    big-step rule for the shape of [f] (and of [u], for triage). *)
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

(** * Name tests as single steps *)

(** The name position of a name test [name_test n], found by following
    one path through the tree; a tree without that path gives a leaf. *)
Definition name_of_test (f : Combination) : Combination :=
  match f with
  | Fk (Sm (Fk _ (Fk (Sm (Fk _ (Fk _ (Sm n)))) _))) _ => n
  | _ => Lf
  end.

Lemma name_of_test_name_test : forall n, name_of_test (name_test n) = n.
Proof. reflexivity. Qed.

(** [as_name_test f] is [Some n] exactly when [f] is the name test [name_test n]. *)
Definition as_name_test (f : Combination) : option Combination :=
  if combination_eq_dec f (name_test (name_of_test f))
  then Some (name_of_test f) else None.

Lemma as_name_test_some : forall f n, as_name_test f = Some n -> f = name_test n.
Proof.
  intros f n; unfold as_name_test.
  destruct (combination_eq_dec f (name_test (name_of_test f))) as [E|E];
    intro H; inversion H; subst; exact E.
Qed.


(** The answer of the name test at [n] on the value [u]. *)
Definition test_answer (n u : Combination) : Combination :=
  match u with
  | Fk (Sm (Fk Lf _)) (Fk (Sm (Sm Lf)) (Fk Lf m)) =>
      if combination_eq_dec m n then 'K else 'KI
  | _ => 'KI
  end.

Lemma test_answer_eval : forall n u, name_test n @ u ==> test_answer n u.
Proof.
  intros n u; destruct (tagged_decide u) as [[C [M ->]]|Hplain].
  - cbn [test_answer]; destruct (combination_eq_dec M n) as [->|HM].
    + apply name_test_tag_hit.
    + apply name_test_tag_miss; intros D HD; inversion HD; congruence.
  - assert (test_answer n u = 'KI) as ->.
    { destruct u as [|a|a b]; cbn [test_answer]; try reflexivity;
      repeat match goal with
             | |- context [match ?x with _ => _ end] => is_var x; destruct x
             end; try reflexivity; exfalso; eapply Hplain; reflexivity. }
    apply name_test_tag_miss; intros C HC; eapply Hplain; exact HC.
Qed.

(** [atomic_rewrite]: a name test applied to a value goes in one step to its
    answer; every other ready application is rewritten by its rule. *)
Definition atomic_rewrite (f u : Combination) : Combination :=
  match as_name_test f with
  | Some n => Sm (test_answer n u)
  | None => rule_rewrite f u
  end.

(** * Steps, for any rewrite of ready applications *)

Section Steps.

Variable rw : Combination -> Combination -> Combination.

(** [step_with rw e] rewrites the first ready application of [e] in
    evaluation order; a finished or stuck expression is returned as is. *)
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

(** The rewrite must agree with evaluation: either it is the rule, or it
    goes straight to the value of the application. *)
Hypothesis rw_ok : forall f u,
  rw f u = rule_rewrite f u \/ exists w, f @ u ==> w /\ rw f u = Sm w.

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
  intros f u v H; destruct (rw_ok f u) as [E|[w [Hw E]]]; rewrite E in H.
  - apply rule_rewrite_back; exact H.
  - inv_out H; exact Hw.
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

(** [advances e e']: [e'] is one step from [e], at a ready application. *)
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

(** A ready application whose rule leads in [k] steps to [Sm v]. *)
Lemma ready_advances : forall f u v k,
  f @ u ==> v -> advances_n k (rule_rewrite f u) (Sm v) ->
  exists j, advances_n j (f @ u) (Sm v).
Proof.
  intros f u v k Hv Hk.
  destruct (rw_ok f u) as [E|[w [Hw E]]].
  - exists (S k); econstructor; [apply adv_ready|rewrite E; exact Hk].
  - pose proof (eval_deterministic _ _ Hv _ Hw) as <-.
    exists 1; econstructor; [apply adv_ready|rewrite E; constructor].
Qed.

Lemma eval_advances : forall e v, e ==> v -> exists k, advances_n k e (Sm v).
Proof.
  intros e v H; induction H.
  - exists 0; constructor.
  - destruct IHeval1 as [j Hj]; destruct IHeval2 as [k Hk].
    exists (j + k); eapply advances_n_trans; [apply advances_n_op; exact Hj|exact Hk].
  - destruct IHeval1 as [j Hj]; destruct IHeval2 as [k Hk].
    exists (j + k); eapply advances_n_trans; [apply advances_n_arg; exact Hj|exact Hk].
  - eapply ready_advances with (k := 0); [constructor|constructor].
  - eapply ready_advances with (k := 0); [constructor|constructor].
  - eapply ready_advances with (k := 0); [constructor|constructor].
  - destruct IHeval as [k Hk]; eapply ready_advances; [apply eval_s; exact H|exact Hk].
  - eapply ready_advances with (k := 0); [constructor|constructor].
  - destruct IHeval as [k Hk]; eapply ready_advances; [apply eval_stem; exact H|exact Hk].
  - destruct IHeval as [k Hk]; eapply ready_advances; [apply eval_fork; exact H|exact Hk].
Qed.

Lemma steps_with_complete : forall e v, e ==> v -> exists k, steps_with k e = Sm v.
Proof.
  intros e v H; destruct (eval_advances e v H) as [k Hk].
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
  exists w, f @ u ==> w /\ atomic_rewrite f u = Sm w.
Proof.
  intros f u; unfold atomic_rewrite.
  destruct (as_name_test f) as [n|] eqn:E; [right|left; reflexivity].
  apply as_name_test_some in E; subst f.
  exists (test_answer n u); split; [apply test_answer_eval|reflexivity].
Qed.

Definition rule_steps := steps_with rule_rewrite.

(** The semantics with atomic name tests, used from here on. *)
Definition step := step_with atomic_rewrite.
Definition steps := steps_with atomic_rewrite.


Lemma steps_agree : forall e v,
  e ==> v <-> exists k, steps k e = Sm v.
Proof. exact (steps_with_agree atomic_rewrite atomic_rewrite_ok). Qed.


(** * Progress

    Every ready application is rewritten by a rule (or, for a name test,
    to its answer), so an expression gets stuck only where a leaf stands
    in an expression position.  An expression with an expression type has
    no such leaf, and neither has any of its steps.  So each snapshot of a
    typed expression is a value or takes a step.  No preservation of
    typing is used. *)

(** No leaf stands in an expression position. *)
Inductive leaf_free_expression : Combination -> Prop :=
| lfe_value : forall v, leaf_free_expression (Sm v)
| lfe_app : forall e1 e2, leaf_free_expression e1 -> leaf_free_expression e2 ->
    leaf_free_expression (Fk e1 e2).

Lemma rule_rewrite_leaf_free : forall f u, leaf_free_expression (rule_rewrite f u).
Proof.
  intros f u; destruct f as [|g|[|g|f0 f1] h]; try destruct u; cbn [rule_rewrite];
    repeat constructor.
Qed.

Lemma atomic_rewrite_leaf_free : forall f u, leaf_free_expression (atomic_rewrite f u).
Proof.
  intros f u; unfold atomic_rewrite; destruct (as_name_test f);
    [constructor|apply rule_rewrite_leaf_free].
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

Lemma expression_typed_leaf_free : forall AI e T,
  infer_expression AI @ e ==> Sm T -> leaf_free_expression e.
Proof.
  intros AI e; induction e as [|u _|e1 IH1 e2 IH2]; intros T H.
  - pose proof (eval_deterministic _ _ H _ (infer_expression_leaf AI)); discriminate.
  - constructor.
  - destruct (infer_expression_fork_inv AI e1 e2 T H) as [T1 [T2 [H1 [H2 _]]]].
    constructor; [eapply IH1; exact H1|eapply IH2; exact H2].
Qed.

(** Progress: each snapshot of a typed expression is a value or is
    rewritten at its first ready application. *)
Lemma typed_progress : forall AI e T,
  infer_expression AI @ e ==> Sm T -> forall k,
  (exists v, steps k e = Sm v) \/ advances atomic_rewrite (steps k e) (steps (S k) e).
Proof.
  intros AI e T H k.
  assert (Hk : leaf_free_expression (steps k e)).
  { pose proof (expression_typed_leaf_free AI e T H) as H0; clear H.
    unfold steps; induction k as [|k IH]; [exact H0|].
    rewrite steps_with_S; apply step_leaf_free; exact IH. }
  replace (steps (S k) e) with (step (steps k e))
    by (unfold steps, step; symmetry; apply steps_with_S).
  apply step_progress; exact Hk.
Qed.


(* ===================================================================== *)
(** * The small-step semantics as programs of the calculus.

    [step_prog @ e ==> step e]: the program takes the expression [e] apart
    as a tree and rebuilds it with its first ready application rewritten;
    it never evaluates [e].  The only application it performs on parts of
    [e] is a name test [name_test n @ u], which is one step of [step] and
    always terminates.

    [bound_eval] acts on the expression [pair @ succ n @ e], that is the
    tree [Fk (Fk (Sm pair) (Sm (succ n))) e]: it returns the expression
    [pair @ n @ e'] where [e'] is [e] after one step.  On every other tree
    (in particular at the count [zero]) it is the identity. *)

From TreeTyping Require Import tree typing data_types.
From Stdlib Require Import String Lia.
Open Scope string_scope.

(** * Building trees inside programs *)

Definition stemT (x : Term) : Term := Val Lf @@ x.
Definition forkT (x y : Term) : Term := Val Lf @@ x @@ y.

(** Split an application to two arguments. *)
Lemma app2_split : forall F x y r,
  F @ x @r y ==> r -> exists v, F @ x ==> v /\ v @ y ==> r.
Proof.
  intros F x y r H; destruct (eval_pair_inv _ _ _ H) as [v1 [v2 [H1 [H2 H3]]]].
  inv_out H2; eauto.
Qed.

(** * One rewrite per rule *)

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

(** * Name tests *)

(** [name_of_test_prog] follows the path to the name of a name test; it
    gives a leaf as soon as the path fails. *)
Definition nt7 := 'triage[Lf, 'I, 'K1 ('K1 Lf)].
Definition nt6 := 'triage[Lf, 'K1 Lf, 'K1 nt7].
Definition nt5 := 'triage[Lf, 'K1 Lf, 'K1 nt6].
Definition nt4 := 'triage[Lf, nt5, 'K1 ('K1 Lf)].
Definition nt3 := 'triage[Lf, 'K1 Lf, 'K 'C nt4].
Definition nt2 := 'triage[Lf, 'K1 Lf, 'K1 nt3].
Definition nt1 := 'triage[Lf, nt2, 'K1 ('K1 Lf)].
Definition name_of_test_prog := 'triage[Lf, 'K1 Lf, 'K 'C nt1].

Ltac destruct_matches :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] => is_var x; destruct x
         end.

Lemma name_of_test_prog_eval : forall f,
  name_of_test_prog @ f ==> name_of_test f.
Proof.
  intro f; destruct f; cbn [name_of_test]; destruct_matches;
    unfold name_of_test_prog, nt1, nt2, nt3, nt4, nt5, nt6, nt7; evaluate.
Qed.

(** [nt_prog @ f @r u] is [Sm (Sm b)] when [f] is a name test with answer
    [b] at [u], and a leaf otherwise.  The answer is computed by applying
    [f] to [u] only after [f] has been recognised. *)
Definition nt_prog_package :
  { t | to_tree
    (\"f" (\"u"
      (((Val equal @@ Ref "f"
           @@ ((''wait [ Val equal, stemT (Val name_of_test_prog @@ Ref "f") ])
                 ''C Val get_tagname))
          @@ (\"x" (stemT (stemT (Ref "f" @@ Ref "x"))))
          @@ Val ('K1 Lf))
       @@ Ref "u"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition nt_prog := Eval cbn in proj1_sig nt_prog_package.

Lemma nt_prog_eval : forall f u,
  nt_prog @ f @r u ==>
    match as_name_test f with
    | Some n => Sm (Sm (test_answer n u))
    | None => Lf
    end.
Proof.
  intros f u.
  pose proof (name_of_test_prog_eval f) as Hn.
  destruct (as_name_test f) as [n|] eqn:E.
  - apply as_name_test_some in E; subst f.
    rewrite name_of_test_name_test in Hn.
    pose proof (equal_eval (name_test n)) as Heq1.
    pose proof (equal1_eq (name_test n)) as Heq2.
    pose proof (test_answer_eval n u) as Ht.
    unfold name_test in *.
    unfold nt_prog; cbv -[equal equal1 name_of_test_prog test_answer get_tagname].
    evaluate2; try eassumption; evaluate.
  - assert (Hne : f <> name_test (name_of_test f)).
    { intro H; unfold as_name_test in E.
      destruct (combination_eq_dec f (name_test (name_of_test f))); congruence. }
    pose proof (equal_eval f) as Heq1.
    pose proof (equal1_neq _ _ Hne) as Heq2.
    unfold name_test in *.
    unfold nt_prog; cbv -[equal equal1 name_of_test_prog name_of_test get_tagname].
    evaluate2; try eassumption; evaluate.
Qed.

(** [atomic_prog]: a name test goes to its answer; otherwise the rule. *)
Definition atomic_prog_package :
  { t | to_tree
    (\"f" (\"u"
      ((''triage [ Val rule_prog @@ Ref "f" @@ Ref "u", Val 'I, Val ('K1 ('K1 Lf)) ])
       @@ (Val nt_prog @@ Ref "f" @@ Ref "u")))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition atomic_prog := Eval cbn in proj1_sig atomic_prog_package.

Lemma atomic_prog_eval : forall f u, atomic_prog @ f @r u ==> atomic_rewrite f u.
Proof.
  intros f u.
  destruct (app2_split _ _ _ _ (rule_prog_eval f u)) as [vr [Hr1 Hr2]].
  destruct (app2_split _ _ _ _ (nt_prog_eval f u)) as [vn [Hn1 Hn2]].
  unfold atomic_rewrite.
  destruct (as_name_test f) as [n|];
    unfold atomic_prog; cbv -[rule_prog nt_prog rule_rewrite test_answer];
    evaluate.
Qed.

(** * One step

    [step_prog_with r] traverses the expression: a leaf or a value is
    returned as is; at an application it looks at the operator, then at the
    argument, and rewrites the first ready application with [r]. *)

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

Lemma step_prog_eval : forall e, step_prog @ e ==> step e.
Proof. apply step_prog_with_eval; exact atomic_prog_eval. Qed.


(** * Bounded evaluation *)

(** The count and the expression of [pair @ succ n @ e]; junk otherwise. *)
Definition count_of (p : Combination) : Combination :=
  match p with
  | Fk (Fk _ (Sm (Fk (Sm (Fk _ (Fk _ n))) _))) _ => n
  | _ => Lf
  end.

Definition expr_of (p : Combination) : Combination :=
  match p with
  | Fk _ e => e
  | _ => Lf
  end.

(** The expression [pair @ c @ e]. *)
Definition pair_expr (c e : Combination) : Combination :=
  Fk (Fk (Sm 'pair) (Sm c)) e.

Definition bound_eval_fn (stepf : Combination -> Combination) (p : Combination) :=
  if combination_eq_dec p (pair_expr (succ (count_of p)) (expr_of p))
  then pair_expr (count_of p) (stepf (expr_of p))
  else p.

Lemma bound_eval_fn_succ : forall stepf n e,
  bound_eval_fn stepf (pair_expr (succ n) e) = pair_expr n (stepf e).
Proof.
  intros; unfold bound_eval_fn.
  cbn [count_of expr_of pair_expr succ].
  destruct (combination_eq_dec _ _) as [_|H]; [reflexivity|].
  exfalso; apply H; reflexivity.
Qed.

Lemma bound_eval_fn_other : forall stepf p,
  (forall n e, p <> pair_expr (succ n) e) -> bound_eval_fn stepf p = p.
Proof.
  intros stepf p H; unfold bound_eval_fn.
  destruct (combination_eq_dec _ _) as [E|_]; [|reflexivity].
  exfalso; eapply H; exact E.
Qed.

Lemma bound_eval_fn_zero : forall stepf e,
  bound_eval_fn stepf (pair_expr zero e) = pair_expr zero e.
Proof.
  intros; apply bound_eval_fn_other; intros n e' H; inversion H.
Qed.

(** Programs for [count_of] and [expr_of]. *)
Definition ct7 := 'triage[Lf, 'K1 Lf, 'K1 'I].
Definition ct5 := 'triage[Lf, 'K1 Lf, 'K1 ct7].
Definition ct4 := 'triage[Lf, ct5, 'K1 ('K1 Lf)].
Definition ct3 := 'triage[Lf, 'K1 Lf, 'K 'C ct4].
Definition ct2 := 'triage[Lf, ct3, 'K1 ('K1 Lf)].
Definition ct1 := 'triage[Lf, 'K1 Lf, 'K1 ct2].
Definition count_prog := 'triage[Lf, 'K1 Lf, 'K 'C ct1].
Definition expr_prog := 'triage[Lf, 'K1 Lf, 'K1 'I].

Lemma count_prog_eval : forall p, count_prog @ p ==> count_of p.
Proof.
  intro p; destruct p; cbn [count_of]; destruct_matches;
    unfold count_prog, ct1, ct2, ct3, ct4, ct5, ct7; evaluate.
Qed.

Lemma expr_prog_eval : forall p, expr_prog @ p ==> expr_of p.
Proof. intro p; destruct p; unfold expr_prog; cbn [expr_of]; evaluate. Qed.

Definition bound_eval_with_package (s : Combination) :
  { t | to_tree
    (\"p"
      (((Val equal @@ Ref "p"
           @@ forkT (forkT (Val (Sm 'pair))
                             (stemT (''tagged[''S2[Val 'snd, Val count_prog @@ Ref "p"],
                                              Val nat_nm])))
                     (Val expr_prog @@ Ref "p"))
          @@ (\"q" (forkT (forkT (Val (Sm 'pair)) (stemT (Val count_prog @@ Ref "q")))
                           (Val s @@ (Val expr_prog @@ Ref "q"))))
          @@ Val 'I)
       @@ Ref "p")) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition bound_eval_with (s : Combination) := proj1_sig (bound_eval_with_package s).

Lemma bound_eval_with_eval : forall s stepf,
  (forall e, s @ e ==> stepf e) ->
  forall p, bound_eval_with s @ p ==> bound_eval_fn stepf p.
Proof.
  intros s stepf Hs p.
  pose proof (count_prog_eval p) as Hc.
  pose proof (expr_prog_eval p) as Hx.
  pose proof (Hs (expr_of p)) as He.
  unfold bound_eval_fn.
  destruct (combination_eq_dec p (pair_expr (succ (count_of p)) (expr_of p))) as [E|E].
  - pose proof (equal_eval p) as Hq1.
    pose proof (equal1_eq p) as Hq2.
    rewrite E in Hq2 at 2.
    unfold pair_expr, succ in Hq2.
    unfold bound_eval_with; cbn -[equal equal1 count_prog expr_prog count_of expr_of].
    unfold pair_expr; evaluate2; try eassumption; evaluate.
  - pose proof (equal_eval p) as Hq1.
    pose proof (equal1_neq _ _ E) as Hq2.
    unfold pair_expr, succ in Hq2.
    unfold bound_eval_with; cbn -[equal equal1 count_prog expr_prog count_of expr_of].
    evaluate2; try eassumption; evaluate.
Qed.

Definition bound_eval := bound_eval_with step_prog.

Lemma bound_eval_eval : forall p, bound_eval @ p ==> bound_eval_fn step p.
Proof. apply bound_eval_with_eval; exact step_prog_eval. Qed.

Lemma bound_eval_succ : forall n e,
  bound_eval @ pair_expr (succ n) e ==> pair_expr n (step e).
Proof. intros; rewrite <- bound_eval_fn_succ; apply bound_eval_eval. Qed.

Lemma bound_eval_zero : forall e,
  bound_eval @ pair_expr zero e ==> pair_expr zero e.
Proof. intros; rewrite <- (bound_eval_fn_zero step) at 2; apply bound_eval_eval. Qed.

Lemma bound_eval_other : forall p,
  (forall n e, p <> pair_expr (succ n) e) -> bound_eval @ p ==> p.
Proof. intros p H; rewrite <- (bound_eval_fn_other step p H) at 2; apply bound_eval_eval. Qed.


(* ===================================================================== *)
(** * Each step preserves expression typing; so does bounded evaluation.

    The proof follows the cases of evaluation_preserves_typing (EPT) in
    soundness.v.  A step to a value is typed by EPT itself.  The steps that
    produce applications ([S2], triage on a stem or a fork) are typed by the
    same local lemmas that EPT uses for the premises of those rules.  The one
    case where EPT uses the whole evaluation, a name test, is a single step
    in [step], and is again covered by EPT. *)

From TreeTyping Require Import tree typing soundness booleans data_types.

Section StepTyping.
Variable AI : Decl.
Hypothesis Hsound : ontology_sound_by_typing AI.

(** A step to a value is typed by evaluation_preserves_typing. *)
Lemma value_step_typing : forall f u w T,
  f @ u ==> w ->
  infer_expression AI @ (f @ u) ==> Sm T ->
  infer_expression AI @ Sm w ==> Sm T.
Proof using Hsound.
  intros f u w T Hw H; apply infer_expression_stem.
  eapply evaluation_preserves_typing;
    [apply ontology_sound_by_typing_value; exact Hsound|eassumption|eassumption].
Qed.

Lemma ready_step_typing : forall f u T,
  infer_expression AI @ (f @ u) ==> Sm T ->
  infer_expression AI @ atomic_rewrite f u ==> Sm T.
Proof using Hsound.
  intros f u T H; unfold atomic_rewrite.
  destruct (as_name_test f) as [n|] eqn:Ename.
  - apply as_name_test_some in Ename; subst f.
    eapply value_step_typing; [apply test_answer_eval|exact H].
  - destruct f as [|g|[|g|f0 f1] h]; cbn [rule_rewrite].
    + eapply value_step_typing; [constructor|exact H].
    + eapply value_step_typing; [constructor|exact H].
    + eapply value_step_typing; [constructor|exact H].
    + (* [S2[g,h] @ u] to [Fk (g @ u) (h @ u)] *)
      destruct (infer_expression_fork_inv AI _ _ _ H)
        as [FT [U [Hfunction [Hargument Happ]]]].
      apply infer_expression_stem_inv in Hfunction.
      apply infer_expression_stem_inv in Hargument.
      destruct (infer_fork_inv AI _ _ _ Hfunction)
        as [GT [F [Hleft [Hf Hconstruction]]]].
      destruct (infer_stem_inv AI _ _ Hleft) as [G [-> Hg]].
      destruct (tagged_decide ('S2[G,F])) as [[C [N Htag]]|Hplain].
      * (* abstract or function introduction *)
        eapply plain_tagged_redex_typing; eauto using ontology_sound_by_typing_plain.
      * apply app_stem_inv in Hconstruction.
        pose proof (type_app_stem_structural_inv AI (type_app AI) _ _ _
          Hplain Hconstruction) as ->.
        assert (HA : abstract_case @ ('S2[G,F]) ==> Lf).
        { unfold abstract_case; apply type_app_abstract_case_S_none; exact Hplain. }
        pose proof (app_plain_inv AI _ _ _ HA Happ) as HD.
        destruct (default_S_inv _ _ _ _ _ _ HD) as [VG [VF [HG [HF HR]]]].
        eapply infer_expression_fork.
        -- eapply infer_expression_fork;
             [apply infer_expression_stem; exact Hg|
              apply infer_expression_stem; exact Hargument|exact HG].
        -- eapply infer_expression_fork;
             [apply infer_expression_stem; exact Hf|
              apply infer_expression_stem; exact Hargument|exact HF].
        -- exact HR.
    + (* triage *)
      destruct u as [|x|x y].
      * eapply value_step_typing; [constructor|exact H].
      * destruct (triage_application_typing AI f0 f1 h (Sm x) T H)
          as [X [Hx [HS|[HQ|[-> HC]]]]].
        -- destruct HS as [F0 [F1 [F2 [HF HC]]]].
           exact (structural_triage_reduct_typing AI f0 f1 h F0 F1 F2 (Sm x) X T HF Hx HC).
        -- exact (query_triage_reduct_typing AI f0 f1 h (Sm x) T X HQ Hx).
        -- exact (children_reduct_typing AI f0 f1 h (Sm x) X HC Hx).
      * destruct (triage_application_typing AI f0 f1 h (Fk x y) T H)
          as [X [Hx [HS|[HQ|[-> HC]]]]].
        -- destruct HS as [F0 [F1 [F2 [HF HC]]]].
           exact (structural_triage_reduct_typing AI f0 f1 h F0 F1 F2 (Fk x y) X T HF Hx HC).
        -- exact (query_triage_reduct_typing AI f0 f1 h (Fk x y) T X HQ Hx).
        -- exact (children_reduct_typing AI f0 f1 h (Fk x y) X HC Hx).
Qed.

Lemma step_preserves_expression_typing : forall e T,
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ step e ==> Sm T.
Proof using Hsound.
  induction e as [|v _|e1 IH1 e2 IH2]; intros T H; try exact H.
  destruct e1 as [|f|a b]; [exact H| |].
  - destruct e2 as [|u|c d]; [exact H| |].
    + apply ready_step_typing; exact H.
    + destruct (infer_expression_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 Happ]]]].
      change (step (Fk (Sm f) (Fk c d))) with (Fk (Sm f) (step (Fk c d))).
      eapply infer_expression_fork; [exact H1|apply IH2; exact H2|exact Happ].
  - destruct (infer_expression_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 Happ]]]].
    change (step (Fk (Fk a b) e2)) with (Fk (step (Fk a b)) e2).
    eapply infer_expression_fork; [apply IH1; exact H1|exact H2|exact Happ].
Qed.

Lemma steps_preserve_expression_typing : forall k e T,
  infer_expression AI @ e ==> Sm T ->
  infer_expression AI @ steps k e ==> Sm T.
Proof using Hsound.
  induction k; intros e T H; [exact H|].
  apply IHk, step_preserves_expression_typing, H.
Qed.

(** * Bounded evaluation preserves expression typing *)

Hypothesis Hnumber : supports_number AI.

(** The count below a successor has the type of the successor. *)
Lemma succ_count_type : forall n K,
  infer AI @ succ n ==> Sm K -> infer AI @ n ==> Sm K.
Proof using Hnumber.
  intros n K H.
  assert (HK : K = 'Nat).
  { destruct (infer_tagged_source_inv AI _ _ _ H) as [C [N [E [-> [HC [HN HI]]]]]].
    pose proof (eval_deterministic _ _ HN _ (infer_nat_nm AI Hnumber)) as HE; inversion HE; subst N.
    pose proof (declaration_K1_inv _ _ _ _ _ _ Hnumber HI) as HS.
    destruct (nat_abstractor_inv _ _ HS) as [-> _].
    reflexivity. }
  subst K.
  destruct (nat_is_data AI (succ n) Hnumber H) as [Hz|[m [Hm Hmt]]].
  - inversion Hz.
  - inversion Hm; subst; exact Hmt.
Qed.

Lemma bound_eval_preserves_expression_typing : forall p p' T,
  infer_expression AI @ p ==> Sm T ->
  bound_eval @ p ==> p' ->
  infer_expression AI @ p' ==> Sm T.
Proof using Hsound Hnumber.
  intros p p' T H Hp.
  pose proof (eval_deterministic _ _ Hp _ (bound_eval_eval p)) as ->.
  unfold bound_eval_fn.
  destruct (combination_eq_dec p (pair_expr (succ (count_of p)) (expr_of p))) as [E|_];
    [|exact H].
  rewrite E in H; unfold pair_expr in *.
  destruct (infer_expression_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 Happ]]]].
  destruct (infer_expression_fork_inv AI _ _ _ H1) as [P [K [Hpair [Hk Happ1]]]].
  apply infer_expression_stem_inv, succ_count_type in Hk.
  eapply infer_expression_fork;
    [eapply infer_expression_fork;
       [exact Hpair|apply infer_expression_stem; exact Hk|exact Happ1]
    |apply step_preserves_expression_typing; exact H2
    |exact Happ].
Qed.

End StepTyping.


(* ===================================================================== *)
(** * Snapshots: quoted expressions, their value types, and their sizes.

    An expression is a tree, so it can be read as a value: this reading is
    quotation, with no encoding.  Its value type is the expression with each
    value replaced by its type ([quoted_type]); for example the expression
    [f @ u] has value type [Fk (Sm F) (Sm U)].  This type expression plays
    the role of a code type: evaluating it, read as an expression, gives
    the expression type.  The step program and bounded evaluation act on
    quoted expressions, and queries such as [size] observe them.

    Results:
    - [quoted_type_infer]: a quoted expression has its quoted type as value
      type; every expression with an expression type has one.
    - [size_on_snapshots]: [size] applied to every snapshot with an
      expression type has expression type [Nat] and computes its node
      count.
    - three examples: a loop that negates and recurses (snapshots cycle,
      size bounded); dither (pending negations, size grows linearly);
      minimisation searching for [n = succ n] (the count grows, and so does
      the size of the snapshot at each call of the predicate). *)

From TreeTyping Require Import tree typing soundness booleans functions
  data_types recursion queries paper_ontology.
From Stdlib Require Import List String Arith Lia.
Import ListNotations.
Open Scope string_scope.

(** * Quoted types *)

Section Quotation.
Variable AI : Decl.

(** [quoted_type e X]: [X] is [e] with each value replaced by its type. *)
Inductive quoted_type : Combination -> Combination -> Prop :=
| quoted_value : forall v V, infer AI @ v ==> Sm V -> quoted_type (Sm v) (Sm V)
| quoted_application : forall a b A B,
    quoted_type a A -> quoted_type b B -> quoted_type (Fk a b) (Fk A B).

Lemma quoted_type_not_leaf : forall e X, quoted_type e X -> X <> Lf.
Proof. intros e X H; destruct H; discriminate. Qed.

Lemma quoted_type_not_K1 : forall e X N, quoted_type e X -> X <> Fk Lf N.
Proof.
  intros e X N H; destruct H as [|a b A B Ha Hb]; [discriminate|].
  intro E; inversion E; subst; exact (quoted_type_not_leaf _ _ Ha eq_refl).
Qed.

(** A quoted application never has the shape of a tagged type. *)
Lemma quoted_type_not_tagged : forall a b A B C N,
  quoted_type a A -> quoted_type b B -> Fk A B <> 'tagged[C,N].
Proof.
  intros a b A B C N Ha Hb E; inversion E; subst.
  inversion Hb; subst.
  match goal with H : quoted_type _ (Fk Lf N) |- _ =>
    exact (quoted_type_not_K1 _ _ _ H eq_refl) end.
Qed.

Lemma quoted_type_infer : forall e X, quoted_type e X -> infer AI @ e ==> Sm X.
Proof.
  intros e X H; induction H.
  - apply infer_stem; assumption.
  - eapply infer_fork; [exact IHquoted_type1|exact IHquoted_type2|].
    apply app_stem, type_app_stem_structural.
    intros C N; eapply quoted_type_not_tagged; eassumption.
Qed.

Lemma expression_quoted_type : forall e T,
  infer_expression AI @ e ==> Sm T -> exists X, quoted_type e X.
Proof.
  induction e as [|v _|a IHa b IHb]; intros T H.
  - pose proof (eval_deterministic _ _ H _ (infer_expression_leaf AI)); discriminate.
  - apply infer_expression_stem_inv in H; eexists; constructor; exact H.
  - destruct (infer_expression_fork_inv AI _ _ _ H) as [A [B [Ha [Hb _]]]].
    destruct (IHa _ Ha) as [X Hx]; destruct (IHb _ Hb) as [Y Hy].
    exists (Fk X Y); constructor; assumption.
Qed.

(** Every expression with an expression type, read as a value, has a value type. *)
Lemma expression_value_type : forall e T,
  infer_expression AI @ e ==> Sm T -> exists X, infer AI @ e ==> Sm X.
Proof.
  intros e T H; destruct (expression_quoted_type e T H) as [X HX].
  exists X; apply quoted_type_infer; exact HX.
Qed.

End Quotation.

(** * Size on snapshots *)

Section SnapshotSizes.
Variable AI : Decl.
Hypothesis Hq : supports_queries AI.
Hypothesis Hn : supports_number AI.

(** [size] applies to every quoted expression that has a value type. *)
Lemma size_on_quoted : forall e X,
  infer AI @ e ==> Sm X ->
  infer_expression AI @ (size @ e) ==> Sm ('Nat) /\ size @ e ==> numeral (tree_size e).
Proof using Hq Hn.
  intros e X H; split; [eapply size_application_typed; eassumption|apply size_eval].
Qed.

Lemma size_on_snapshots : forall e T k,
  infer_expression AI @ steps k e ==> Sm T ->
  infer_expression AI @ (size @ steps k e) ==> Sm ('Nat) /\
  size @ steps k e ==> numeral (tree_size (steps k e)).
Proof using Hq Hn.
  intros e T k H.
  destruct (expression_value_type AI (steps k e) T H) as [X HX].
  eapply size_on_quoted; exact HX.
Qed.

(** ** Rule-by-rule snapshots *)

(** The first ready application of an expression, in evaluation order. *)
Fixpoint ready_of (e : Combination) : option (Combination * Combination) :=
  match e with
  | Fk (Sm f) (Sm u) => Some (f, u)
  | Fk (Sm f) (Fk _ _ as e2) => ready_of e2
  | Fk (Fk _ _ as e1) e2 => ready_of e1
  | _ => None
  end.

(** The only rule that can build a value without a value type: a fork
    [Fk g u] built from [Sm g @ u].  When [Fk G U] is not the shape of a
    tagged type, it is the type of [Fk g u]. *)
Lemma plain_construction_typed : forall g u G U,
  infer AI @ g ==> Sm G -> infer AI @ u ==> Sm U ->
  (forall C N, Fk G U <> 'tagged[C,N]) ->
  infer AI @ Fk g u ==> Sm (Fk G U).
Proof.
  intros g u G U HG HU Hp; eapply infer_fork; [exact HG|exact HU|].
  apply app_stem, type_app_stem_structural; exact Hp.
Qed.


Lemma value_typed_subtrees : forall a b W,
  infer AI @ Fk a b ==> Sm W -> (exists A, infer AI @ a ==> Sm A) /\ (exists B, infer AI @ b ==> Sm B).
Proof.
  intros a b W H; destruct (infer_fork_inv AI _ _ _ H) as [A [B [Ha [Hb' _]]]]; eauto.
Qed.

Lemma value_typed_stem : forall a W,
  infer AI @ Sm a ==> Sm W -> exists A, infer AI @ a ==> Sm A.
Proof. intros a W H; destruct (infer_stem_inv AI _ _ H) as [A [_ Ha]]; eauto. Qed.

Lemma rule_rewrite_quoted : forall f u F U,
  infer AI @ f ==> Sm F -> infer AI @ u ==> Sm U ->
  (forall g, f = Sm g -> exists W, infer AI @ Fk g u ==> Sm W) ->
  exists X, quoted_type AI (rule_rewrite f u) X.
Proof.
  intros f u F U Hf Hu Hc.
  destruct f as [|g|[|g|f0 f1] h]; cbn [rule_rewrite].
  - eexists; constructor; apply infer_stem; exact Hu.
  - destruct (Hc g eq_refl) as [W HW]; eexists; constructor; exact HW.
  - destruct (value_typed_subtrees _ _ _ Hf) as [_ [Y HY]].
    eexists; constructor; exact HY.
  - destruct (value_typed_subtrees _ _ _ Hf) as [[SG HSG] [H' HH]].
    destruct (value_typed_stem _ _ HSG) as [G HG].
    eexists; repeat first [apply quoted_application | apply quoted_value; eassumption].
  - destruct (value_typed_subtrees _ _ _ Hf) as [[L HL] [F2 HF2]].
    destruct (value_typed_subtrees _ _ _ HL) as [[F0 HF0] [F1 HF1]].
    destruct u as [|x|x y].
    + eexists; constructor; exact HF0.
    + destruct (value_typed_stem _ _ Hu) as [X HX].
      eexists; repeat first [apply quoted_application | apply quoted_value; eassumption].
    + destruct (value_typed_subtrees _ _ _ Hu) as [[X HX] [Y HY]].
      eexists; repeat first [apply quoted_application | apply quoted_value; eassumption].
Qed.


End SnapshotSizes.

(** ** A rule-by-rule snapshot of a name test without expression type *)

(** [eval_bounded] and [eval_bounded_sound] are in soundness.v. *)

(** The IsNamed test [is_named bool_nm] applied to ['tt] has an
    expression type, but its first rule-by-rule snapshot has none: the
    snapshot exposes the raw name test, which is typed structurally and
    so cannot be applied at the abstract type ['Bool].  The snapshot of
    [step] is instead the answer.  The declarations add the IsNamed row to
    [bool_ontology]. *)
Definition bool_is_named_ontology :=
  extend (to_tree (tcase (Val is_named_nm) (Val ('K1 is_named_abstractor)))) bool_ontology.
Lemma name_test_snapshot_untyped :
  (exists T, infer_expression bool_is_named_ontology @ (is_named bool_nm @ 'tt) ==> Sm T) /\
  ~ (exists T, infer_expression bool_is_named_ontology @ (rule_steps 1 (is_named bool_nm @ 'tt)) ==> Sm T).
Proof.
  split.
  - eexists; apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity.
  - intros [T H].
    assert (HL : infer_expression bool_is_named_ontology @ (rule_steps 1 (is_named bool_nm @ 'tt)) ==> Lf)
      by (apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity).
    pose proof (eval_deterministic _ _ H _ HL); discriminate.
Qed.

(** * Examples *)

(** ** A loop that negates and recurses

    [loop @ b] calls [loop] on the negation of [b], in tail position: the
    body of its functional is [r o neg], with the Boolean witness [tt]. *)
Definition loop_body := Eval cbn in to_tree
  (\"r" (''tagged[''decorate[Ref "r" ''C Val typed_neg, Val 'tt], Val fun_nm])).
Definition loop_function := lam loop_body typed_neg.
Definition loop := 'fix[loop_function].

Lemma loop_tt_ff : steps 177 (loop @ 'tt) = loop @ 'ff.
Proof. vm_compute; reflexivity. Qed.

Lemma loop_ff_tt : steps 180 (loop @ 'ff) = loop @ 'tt.
Proof. vm_compute; reflexivity. Qed.

Lemma loop_cycle : steps 357 (loop @ 'tt) = loop @ 'tt.
Proof.
  change 357 with (177 + 180); unfold steps; rewrite steps_with_add.
  fold (steps 177 (loop @ 'tt)); rewrite loop_tt_ff; exact loop_ff_tt.
Qed.

Lemma steps_period : forall p e, steps p e = e ->
  forall q r, steps (q * p + r) e = steps r e.
Proof.
  intros p e Hp; induction q; intro r; [reflexivity|].
  replace (S q * p + r) with (p + (q * p + r)) by lia.
  unfold steps in *; rewrite steps_with_add, Hp; apply IHq.
Qed.

Definition loop_bound := 3552.

Lemma loop_window : forallb (fun r => Nat.leb (tree_size (steps r (loop @ 'tt))) loop_bound)
  (seq 0 357) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma loop_size_bounded : forall k, tree_size (steps k (loop @ 'tt)) <= loop_bound.
Proof.
  intro k.
  rewrite (Nat.div_mod k 357) by lia; rewrite Nat.mul_comm.
  rewrite (steps_period 357 _ loop_cycle).
  pose proof loop_window as W; rewrite forallb_forall in W.
  apply Nat.leb_le, W, in_seq; split; [lia|].
  pose proof (Nat.mod_upper_bound k 357); lia.
Qed.

(** ** dither: pending negations

    [dither] is the query of dither_minimisation.v.  Every 92 steps one more
    negation [neg] waits for the value of [dither @ tt], which reappears
    unchanged. *)
From TreeTyping Require Import dither_minimisation.
Fixpoint pending (k : nat) : Combination :=
  match k with
  | O => dither @ 'tt
  | S k => Fk (Sm neg) (pending k)
  end.

Definition forks_upto (p : nat) (e : Combination) : bool :=
  forallb (fun i => match steps i e with Fk _ _ => true | _ => false end) (seq 0 p).

Lemma steps_argument : forall p f e,
  (forall i, i < p -> exists a b, steps i e = Fk a b) ->
  steps p (Fk (Sm f) e) = Fk (Sm f) (steps p e) /\
  (forall i, i < p -> exists a b, steps i (Fk (Sm f) e) = Fk a b).
Proof.
  induction p as [|p IH]; intros f e H; [split; [reflexivity|intros; lia]|].
  assert (H' : forall i, i < p -> exists a b, steps i e = Fk a b) by (intros; apply H; lia).
  destruct (IH f e H') as [Hp Hi].
  destruct (H p ltac:(lia)) as [a [b Hab]].
  split.
  - unfold steps in *; rewrite !steps_with_S, Hp, Hab; reflexivity.
  - intros i Hlt; destruct (Nat.eq_dec i p) as [->|Hne]; [|apply Hi; lia].
    rewrite (proj1 (IH f e H')); eauto.
Qed.

Lemma dither_round : steps 92 (dither @ 'tt) = pending 1.
Proof. vm_compute; reflexivity. Qed.

Lemma dither_round_forks : forks_upto 92 (dither @ 'tt) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma forks_upto_spec : forall p e, forks_upto p e = true ->
  forall i, i < p -> exists a b, steps i e = Fk a b.
Proof.
  intros p e H i Hi; unfold forks_upto in H; rewrite forallb_forall in H.
  specialize (H i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
  destruct (steps i e); try discriminate; eauto.
Qed.

Lemma dither_pending : forall k, steps (k * 92) (dither @ 'tt) = pending k.
Proof.
  assert (Hctx : forall k,
    steps 92 (pending k) = pending (S k) /\
    forall i, i < 92 -> exists a b, steps i (pending k) = Fk a b).
  { induction k as [|k [IH1 IH2]].
    - split; [exact dither_round|apply forks_upto_spec; exact dither_round_forks].
    - destruct (steps_argument 92 neg (pending k) IH2) as [H1 H2].
      split; [cbn [pending]; rewrite H1, IH1; reflexivity|exact H2]. }
  induction k as [|k IH]; [reflexivity|].
  replace (S k * 92) with (k * 92 + 92) by lia.
  unfold steps in *; rewrite steps_with_add, IH; apply Hctx.
Qed.

Lemma tree_size_pending : forall k, tree_size (pending k) = 339 + 86 * k.
Proof.
  induction k as [|k IH]; [vm_compute; reflexivity|].
  cbn [pending tree_size]; rewrite IH.
  assert (tree_size neg = 84) as -> by (vm_compute; reflexivity); lia.
Qed.

Lemma dither_size_grows : forall k,
  tree_size (steps (k * 92) (dither @ 'tt)) = 339 + 86 * k.
Proof. intro k; rewrite dither_pending; apply tree_size_pending. Qed.

(** Every round [pending k] of the query [dither @ tt] has expression type
    [Bool], at declarations that support queries and Booleans. *)
Lemma dither_pending_typed : forall (AI : Decl) k,
  supports_queries AI -> supports_booleans AI ->
  infer_expression AI @ pending k ==> Sm ('Bool).
Proof.
  intros AI k HQ HB; induction k as [|k IH]; cbn [pending].
  - exact (dither_tt_infer_expression AI HQ HB).
  - eapply infer_expression_fork;
      [apply infer_expression_stem; apply neg_infer; exact HB|exact IH|apply neg_type_app].
Qed.

(** Every snapshot of the function-typed [dither_fn @ tt] has expression type [Bool], for
    declarations sound by typing that support the Booleans (for example
    [bool_ontology], [bool_ontology_sound_by_typing]).  A step preserves
    typing only under soundness by typing; declarations that support
    queries or updates are not sound by typing
    ([queries_not_sound_by_typing], [updates_not_sound_by_typing]). *)
Lemma dither_fn_snapshots_typed : forall (AI : Decl) k,
  ontology_sound_by_typing AI -> supports_booleans AI ->
  infer_expression AI @ steps k (dither_fn @ 'tt) ==> Sm ('Bool).
Proof.
  intros AI k Hs Hb.
  apply steps_preserve_expression_typing; [exact Hs|].
  exact (dither_fn_tt_infer_expression AI Hb).
Qed.

(** [size] is a query, it measures the snapshots of
    [dither @ tt], and it applies to every typed expression. *)
Theorem size_on_expressions :
  (forall k, size @ steps (k * 92) (dither @ 'tt) ==> numeral (339 + 86 * k)) /\
  (forall e T, infer_expression paper_ontology @ e ==> Sm T ->
     infer_expression paper_ontology @ (size @ e) ==> Sm ('Nat)).
Proof.
  pose proof paper_ontology_supports_queries as Hq.
  pose proof paper_ontology_supports_number as Hn.
  split.
  - intro k; rewrite <- dither_size_grows; apply size_eval.
  - intros e T H.
    destruct (expression_value_type paper_ontology e T H) as [X HX].
    exact (proj1 (size_on_quoted paper_ontology Hq Hn e X HX)).
Qed.

(** The ontology of the paper is not sound by typing, and a snapshot of a
    typed expression can be untyped: after 165 steps, [size @ tt] exposes
    the triage carrier of [size] at the abstract type [Bool].  Computed. *)
Lemma size_snapshot_untyped :
  infer_expression paper_ontology @ (size @ 'tt) ==> Sm ('Nat) /\
  ~ (exists T, infer_expression paper_ontology @ (steps 165 (size @ 'tt)) ==> Sm T).
Proof.
  split.
  - apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity.
  - intros [T H].
    assert (HL : infer_expression paper_ontology @ (steps 165 (size @ 'tt)) ==> Lf)
      by (apply (eval_bounded_sound (Nat.pow 10 6)); vm_compute; reflexivity).
    pose proof (eval_deterministic _ _ H _ HL); discriminate.
Qed.


(** ** Minimisation searching for [n = succ n]

    The predicate compares [n] with its successor by the typed equality
    query; it is never true, so the search goes on for ever.  At the k-th
    call of the predicate the count is [numeral k] and the snapshot has
    [4426 + 150 k] nodes; the calls are ever further apart. *)
Definition pred_body := Eval cbn in to_tree
  (\"n" (Val typed_equal @@ Ref "n" @@ (Val successor_function @@ Ref "n"))).
Definition pred := lam pred_body zero.
Definition search := minimisation_fn @ pred @r zero.

Definition calls_pred (e : Combination) (k : nat) : bool :=
  match ready_of e with
  | Some (f, u) =>
      if combination_eq_dec f pred then
        if combination_eq_dec u (numeral k) then true else false
      else false
  | None => false
  end.

(* The large nat literals (step counts and sizes) are intentional; Rocq reads them via Nat.of_num_uint. *)
#[warnings="-abstract-large-number"]
Lemma search_call_0 : calls_pred (steps 366 search) 0 = true /\
  tree_size (steps 366 search) = 4426.
Proof. split; vm_compute; reflexivity. Qed.


#[warnings="-abstract-large-number"]
Lemma search_call_3 : calls_pred (steps 55773 search) 3 = true /\
  tree_size (steps 55773 search) = 4426 + 150 * 3.
Proof. split; vm_compute; reflexivity. Qed.


(* ===================================================================== *)
(** * A middle granularity: rule by rule, except that [equal] is atomic.

    [mid_step] rewrites every ready application by its evaluation rule,
    inside name tests too, except the applications of the equality program:
    [equal @ p] goes in one step to its value [equal1 p], and [equal1 p @ q]
    goes in one step to [K] or [KI].  So a name test runs [get_tagname]
    rule by rule and then compares the nametags in one step. *)

From TreeTyping Require Import tree typing.
From Stdlib Require Import Arith Lia Bool.

(** * Boolean equality of trees, deciding left to right *)

Fixpoint cmb_eqb (x y : Combination) : bool :=
  match x, y with
  | Lf, Lf => true
  | Sm a, Sm b => cmb_eqb a b
  | Fk a b, Fk c d => if cmb_eqb a c then cmb_eqb b d else false
  | _, _ => false
  end.

Lemma cmb_eqb_spec : forall x y, cmb_eqb x y = true <-> x = y.
Proof.
  induction x as [|a IHa|a IHa b IHb]; destruct y as [|c|c d]; cbn;
    split; intro H; try discriminate; try congruence.
  - f_equal; apply IHa; exact H.
  - inversion H; subst; apply IHa; reflexivity.
  - destruct (cmb_eqb a c) eqn:E; [|discriminate].
    f_equal; [apply IHa; exact E|apply IHb; exact H].
  - inversion H; subst.
    rewrite (proj2 (IHa c) eq_refl); apply IHb; reflexivity.
Qed.

Lemma cmb_eqb_refl : forall x, cmb_eqb x x = true.
Proof. intro x; apply cmb_eqb_spec; reflexivity. Qed.

Lemma cmb_eqb_false : forall x y, cmb_eqb x y = false -> x <> y.
Proof. intros x y H E; subst; rewrite cmb_eqb_refl in H; discriminate. Qed.

(** * Recognising the testers [equal1 p] *)

Fixpoint decode (f : Combination) : Combination :=
  match f with
  | Fk (Fk _ _) (Fk (Sm (Fk (Sm q1) (Fk _ q2))) _) =>
      Fk (decode q1) (decode q2)
  | Fk (Fk (Fk _ _) q) _ => Sm (decode q)
  | _ => Lf
  end.

Lemma decode_equal1 : forall p, decode (equal1 p) = p.
Proof.
  induction p as [|p IH|p1 IH1 p2 IH2]; [reflexivity| |].
  - change (equal1 (Sm p)) with ('triage [('KI), equal1 p, 'K1 ('K1 ('KI))]).
    cbn [decode]; rewrite IH; reflexivity.
  - change (equal1 (Fk p1 p2)) with
      ('triage ['KI, 'K1 'KI, 'S2 ['S2 [equal1 p1, 'K1 equal1 p2], 'K1 ('K1 'KI)]]).
    cbn [decode]; rewrite IH1, IH2; reflexivity.
Qed.

(** * The middle rewrite *)

Definition mid_rewrite (f u : Combination) : Combination :=
  if cmb_eqb f equal then Sm (equal1 u)
  else if cmb_eqb f (equal1 (decode f)) then
    Sm (if cmb_eqb (decode f) u then 'K else 'KI)
  else rule_rewrite f u.

Lemma mid_rewrite_ok : forall f u,
  mid_rewrite f u = rule_rewrite f u \/
  exists w, f @ u ==> w /\ mid_rewrite f u = Sm w.
Proof.
  intros f u; unfold mid_rewrite.
  destruct (cmb_eqb f equal) eqn:E1.
  - apply cmb_eqb_spec in E1; subst; right; eexists; split; [apply equal_eval|reflexivity].
  - destruct (cmb_eqb f (equal1 (decode f))) eqn:E2; [|left; reflexivity].
    apply cmb_eqb_spec in E2; right.
    destruct (cmb_eqb (decode f) u) eqn:E3.
    + apply cmb_eqb_spec in E3; eexists; split; [|reflexivity].
      rewrite E2, E3; apply equal1_eq.
    + eexists; split; [|reflexivity].
      rewrite E2; apply equal1_neq; apply cmb_eqb_false; exact E3.
Qed.

Definition mid_step := step_with mid_rewrite.
Definition mid_steps := steps_with mid_rewrite.

Lemma mid_steps_agree : forall e v,
  e ==> v <-> exists k, mid_steps k e = Sm v.
Proof. exact (steps_with_agree mid_rewrite mid_rewrite_ok). Qed.


(* ===================================================================== *)
(** * Running a name test with unknown arguments.

    A name test [name_test n @ u] is run by [mid_step] for every [n] and
    [u] at once, on symbolic trees: a symbolic tree has holes standing for
    unknown subtrees, and two abbreviations, [SEq1 p] for the tester
    [equal1 p] and [SBool p q] for the answer of comparing [p] with [q].
    A symbolic step that would need the shape of a hole reports the hole;
    the hole is then split into a leaf, a stem and a fork, and the run is
    repeated on each.  Since [get_tagname] is not recursive, finitely many
    splits suffice.  The result is [name_test_runs_well]: no step of
    a name test builds a fork whose function part is a stem of [K1 c], that
    is, no step builds a value of the shape of a tagged value. *)

From TreeTyping Require Import tree typing.
From Stdlib Require Import Arith Lia Bool.

(** * Concrete notion: a step that could build a tagged value *)

(** The rule [Sm g @ x ==> Fk g x] builds a value of the shape of a tagged
    value exactly when [g = Sm (K1 c)] and [x = S2[K, K1 t]]. *)
Definition bad (e : Combination) : bool :=
  match ready_of e with
  | Some (Sm (Sm (Fk Lf _)), Fk (Sm (Sm Lf)) (Fk Lf _)) => true
  | _ => false
  end.

Lemma bad_finished : forall v, bad (Sm v) = false.
Proof. reflexivity. Qed.

(** * Symbolic trees *)

Inductive Sym : Set :=
| SLf | SSm (a : Sym) | SFk (a b : Sym) | SHole (i : nat)
| SEq1 (p : Sym) | SBool (p q : Sym).

Fixpoint inst (sg : nat -> Combination) (s : Sym) : Combination :=
  match s with
  | SLf => Lf
  | SSm a => Sm (inst sg a)
  | SFk a b => Fk (inst sg a) (inst sg b)
  | SHole i => sg i
  | SEq1 p => equal1 (inst sg p)
  | SBool p q => if cmb_eqb (inst sg p) (inst sg q) then 'K else 'KI
  end.

Fixpoint of_comb (c : Combination) : Sym :=
  match c with
  | Lf => SLf
  | Sm a => SSm (of_comb a)
  | Fk a b => SFk (of_comb a) (of_comb b)
  end.

Lemma inst_of : forall sg c, inst sg (of_comb c) = c.
Proof. induction c; cbn; congruence. Qed.

Fixpoint to_closed (s : Sym) : option Combination :=
  match s with
  | SLf => Some Lf
  | SSm a => option_map Sm (to_closed a)
  | SFk a b => match to_closed a, to_closed b with
               | Some x, Some y => Some (Fk x y)
               | _, _ => None
               end
  | _ => None
  end.

Lemma to_closed_inst : forall sg s c, to_closed s = Some c -> inst sg s = c.
Proof.
  intros sg; induction s; cbn; intros c H; try discriminate.
  - inversion H; reflexivity.
  - destruct (to_closed s) eqn:E; inversion H; subst; cbn; f_equal; auto.
  - destruct (to_closed s1) eqn:E1; destruct (to_closed s2) eqn:E2;
      inversion H; subst; f_equal; auto.
Qed.

Inductive R (A : Type) : Type := Hit (i : nat) | Stuck | Ok (a : A).
Arguments Hit {A} i.
Arguments Stuck {A}.
Arguments Ok {A} a.

Definition bindR {A B} (r : R A) (f : A -> R B) : R B :=
  match r with Hit i => Hit i | Stuck => Stuck | Ok a => f a end.

Lemma bindR_ok : forall A B (r : R A) (f : A -> R B) b,
  bindR r f = Ok b -> exists a, r = Ok a /\ f a = Ok b.
Proof. intros A B r f b H; destruct r; cbn in H; try discriminate; eauto. Qed.

Ltac bok H x Hx :=
  let H' := fresh "H" in
  destruct (bindR_ok _ _ _ _ _ H) as [x [Hx H']]; clear H; rename H' into H.

Ltac bind_ok H :=
  let a := fresh "a" in let Ha := fresh "Ha" in let H' := fresh "H" in
  destruct (bindR_ok _ _ _ _ _ H) as [a [Ha H']]; clear H; rename H' into H.

(** The tester [equal1 (Fk p1 p2)], one level exposed. *)
Definition sK1 x := SFk SLf x.
Definition sS2 u v := SFk (SSm u) v.
Definition sC g f := SFk (SSm (SFk SLf g)) f.

Definition eq1_fork (q1 q2 : Sym) : Sym :=
  SFk (SFk (of_comb ('KI)) (of_comb ('K1 'KI)))
    (sS2 (sS2 (SEq1 q1) (sK1 (SEq1 q2))) (of_comb ('K1 ('K1 'KI)))).

Lemma inst_eq1_fork : forall sg q1 q2,
  inst sg (eq1_fork q1 q2) = equal1 (Fk (inst sg q1) (inst sg q2)).
Proof. intros; unfold eq1_fork, sK1, sS2, sC; cbn [inst]; rewrite !inst_of; reflexivity. Qed.

Definition top (s : Sym) : bool :=
  match s with SLf | SSm _ | SFk _ _ => true | _ => false end.

(** Expose the top constructor; compare. *)
Fixpoint hnf (k : nat) (s : Sym) {struct k} : R Sym :=
  match k with
  | O => Stuck
  | S k =>
      match s with
      | SLf | SSm _ | SFk _ _ => Ok s
      | SHole i => Hit i
      | SEq1 p =>
          bindR (hnf k p) (fun p' =>
            match p' with
            | SLf => Ok (of_comb ('isLeaf))
            | SSm q => Ok (SFk (SFk (of_comb ('KI)) (SEq1 q)) (of_comb ('K1 ('K1 'KI))))
            | SFk q1 q2 => Ok (eq1_fork q1 q2)
            | _ => Stuck
            end)
      | SBool p q => bindR (sceqb k p q) (fun b => Ok (of_comb (if b then 'K else 'KI)))
      end
  end
with sceqb (k : nat) (x y : Sym) {struct k} : R bool :=
  match k with
  | O => Stuck
  | S k =>
      bindR (hnf k x) (fun x' => bindR (hnf k y) (fun y' =>
        match x', y' with
        | SLf, SLf => Ok true
        | SSm a, SSm b => sceqb k a b
        | SFk a b, SFk c d => bindR (sceqb k a c) (fun t => if t then sceqb k b d else Ok false)
        | SLf, (SSm _ | SFk _ _) | SSm _, (SLf | SFk _ _) | SFk _ _, (SLf | SSm _) => Ok false
        | _, _ => Stuck
        end))
  end.

Lemma hnf_sceqb_sound : forall k,
  (forall s s' sg, hnf k s = Ok s' -> inst sg s' = inst sg s /\ top s' = true) /\
  (forall x y b sg, sceqb k x y = Ok b -> cmb_eqb (inst sg x) (inst sg y) = b).
Proof.
  induction k as [|k [IHh IHc]]; split; intros; cbn in H; try discriminate.
  - destruct s; try (inversion H; subst; split; reflexivity); try discriminate.
    + bind_ok H; apply (IHh _ _ sg) in Ha; destruct Ha as [Ha Ht].
      destruct a; try discriminate; inversion H; subst; cbn [inst]; rewrite <- Ha;
        cbn [inst]; split; try reflexivity;
        rewrite ?inst_of, ?inst_eq1_fork; reflexivity.
    + bind_ok H; apply (IHc _ _ _ sg) in Ha; inversion H; subst; cbn [inst].
      rewrite inst_of; split; [reflexivity|destruct (cmb_eqb _ _); reflexivity].
  - bind_ok H; bind_ok H.
    apply (IHh _ _ sg) in Ha; apply (IHh _ _ sg) in Ha0.
    destruct Ha as [Ea Ta]; destruct Ha0 as [Eb Tb].
    rewrite <- Ea, <- Eb.
    destruct a; try discriminate; destruct a0; try discriminate;
      cbn in H; try (inversion H; reflexivity); cbn [inst cmb_eqb].
    + apply IHc; exact H.
    + bind_ok H; apply (IHc _ _ _ sg) in Ha; rewrite Ha.
      destruct a; [apply IHc; exact H|inversion H; reflexivity].
Qed.

Lemma hnf_sound : forall k s s' sg, hnf k s = Ok s' -> inst sg s' = inst sg s.
Proof. intros; apply (proj1 (hnf_sceqb_sound k)); assumption. Qed.

Lemma sceqb_sound : forall k x y b sg, sceqb k x y = Ok b -> cmb_eqb (inst sg x) (inst sg y) = b.
Proof. intros; apply (proj2 (hnf_sceqb_sound k)); assumption. Qed.

(** * Symbolic rewriting *)

Definition mk_bool (k : nat) (p q : Sym) : Sym :=
  match sceqb k p q with
  | Ok b => of_comb (if b then 'K else 'KI)
  | _ => SBool p q
  end.

Lemma inst_mk_bool : forall k p q sg,
  inst sg (mk_bool k p q) = if cmb_eqb (inst sg p) (inst sg q) then 'K else 'KI.
Proof.
  intros; unfold mk_bool; destruct (sceqb k p q) eqn:E; try reflexivity.
  rewrite inst_of, (sceqb_sound _ _ _ _ sg E); reflexivity.
Qed.

Definition srule (k : nat) (f u : Sym) : R Sym :=
  bindR (hnf k f) (fun f' =>
  match f' with
  | SLf => Ok (SSm (SSm u))
  | SSm g => Ok (SSm (SFk g u))
  | SFk a h =>
      bindR (hnf k a) (fun a' =>
      match a' with
      | SLf => Ok (SSm h)
      | SSm g => Ok (SFk (SFk (SSm g) (SSm u)) (SFk (SSm h) (SSm u)))
      | SFk f0 f1 =>
          bindR (hnf k u) (fun u' =>
          match u' with
          | SLf => Ok (SSm f0)
          | SSm x => Ok (SFk (SSm f1) (SSm x))
          | SFk x y => Ok (SFk (SFk (SSm h) (SSm x)) (SSm y))
          | _ => Stuck
          end)
      | _ => Stuck
      end)
  | _ => Stuck
  end).

Lemma srule_sound : forall k f u r sg,
  srule k f u = Ok r -> rule_rewrite (inst sg f) (inst sg u) = inst sg r.
Proof.
  intros k f u r sg H; unfold srule in H; bind_ok H.
  rewrite <- (hnf_sound _ _ _ sg Ha).
  destruct a as [| g | a h | | |]; try discriminate.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - bind_ok H; cbn [inst rule_rewrite].
    rewrite <- (hnf_sound _ _ _ sg Ha0).
    destruct a0 as [| g | f0 f1 | | |]; try discriminate.
    + inversion H; reflexivity.
    + inversion H; reflexivity.
    + bind_ok H; cbn [inst].
      rewrite <- (hnf_sound _ _ _ sg Ha1).
      destruct a0; try discriminate; inversion H; reflexivity.
Qed.

(** Whether the instance has the shape [Fk (Fk _ _) _] of a tester. *)
Definition tri_shape (k : nat) (f : Sym) : R bool :=
  bindR (hnf k f) (fun f' =>
  match f' with
  | SFk a _ => bindR (hnf k a) (fun a' =>
      match a' with SFk _ _ => Ok true | SLf | SSm _ => Ok false | _ => Stuck end)
  | SLf | SSm _ => Ok false
  | _ => Stuck
  end).

Lemma equal1_shape : forall p, exists a b c, equal1 p = Fk (Fk a b) c.
Proof. destruct p; cbn; eauto. Qed.

Lemma tri_shape_false : forall k f sg, tri_shape k f = Ok false ->
  forall p, inst sg f <> equal1 p.
Proof.
  intros k f sg H p E; destruct (equal1_shape p) as [a [b [c Ep]]]; rewrite Ep in E.
  unfold tri_shape in H; bind_ok H.
  rewrite <- (hnf_sound _ _ _ sg Ha) in E.
  destruct a0; try discriminate; cbn in E; try discriminate.
  bind_ok H; inversion E; subst.
  rewrite <- (hnf_sound _ _ _ sg Ha0) in H1.
  destruct a0; try discriminate; cbn in H1; discriminate.
Qed.

Lemma equal1_not_equal : forall p, equal1 p <> equal.
Proof. intros p E; destruct (equal1_shape p) as [a [b [c Ep]]]; rewrite Ep in E; discriminate. Qed.

Definition smid_plain (k : nat) (f u : Sym) : R Sym :=
  bindR (sceqb k f (of_comb equal)) (fun is_eq =>
  if is_eq then Ok (SSm (SEq1 u)) else
  bindR (tri_shape k f) (fun tri =>
  if tri then
    match to_closed f with
    | Some fc =>
        if cmb_eqb fc (equal1 (decode fc))
        then Ok (SSm (mk_bool k (of_comb (decode fc)) u))
        else srule k f u
    | None => Stuck
    end
  else srule k f u)).

Definition smid_rewrite (k : nat) (f u : Sym) : R Sym :=
  match f with
  | SEq1 p => Ok (SSm (mk_bool k p u))
  | _ => smid_plain k f u
  end.

Lemma smid_plain_sound : forall k f u r sg,
  smid_plain k f u = Ok r -> mid_rewrite (inst sg f) (inst sg u) = inst sg r.
Proof.
  intros k f u r sg H; unfold mid_rewrite, smid_plain in *; bind_ok H.
  pose proof (sceqb_sound _ _ _ _ sg Ha) as Eq; rewrite inst_of in Eq; rewrite Eq.
  destruct a.
  - inversion H; reflexivity.
  - bind_ok H; destruct a.
    + destruct (to_closed f) as [fc|] eqn:Ec; [|discriminate].
      rewrite (to_closed_inst sg _ _ Ec).
      destruct (cmb_eqb fc (equal1 (decode fc))) eqn:E2.
      * inversion H; subst; cbn [inst]; rewrite (inst_mk_bool k), inst_of; reflexivity.
      * rewrite <- (to_closed_inst sg _ _ Ec); eapply srule_sound; exact H.
    + destruct (cmb_eqb (inst sg f) (equal1 (decode (inst sg f)))) eqn:E2.
      * apply cmb_eqb_spec in E2; exfalso; eapply tri_shape_false; eassumption.
      * eapply srule_sound; exact H.
Qed.

Lemma smid_rewrite_sound : forall k f u r sg,
  smid_rewrite k f u = Ok r -> mid_rewrite (inst sg f) (inst sg u) = inst sg r.
Proof.
  intros k f u r sg H.
  destruct f as [| | | |p|]; try (eapply smid_plain_sound; exact H).
  cbn [smid_rewrite] in H; inversion H; subst; cbn [inst]; unfold mid_rewrite.
  destruct (cmb_eqb (equal1 (inst sg p)) equal) eqn:E1.
  - apply cmb_eqb_spec, equal1_not_equal in E1; contradiction.
  - rewrite decode_equal1, cmb_eqb_refl, (inst_mk_bool k); reflexivity.
Qed.

(** * Symbolic steps and runs *)

Lemma step_with_arg : forall rw f a b,
  step_with rw (Fk (Sm f) (Fk a b)) = Fk (Sm f) (step_with rw (Fk a b)).
Proof. reflexivity. Qed.

Lemma step_with_op : forall rw a b e2,
  step_with rw (Fk (Fk a b) e2) = Fk (step_with rw (Fk a b)) e2.
Proof. reflexivity. Qed.

Fixpoint sstep (k : nat) (e : Sym) : R Sym :=
  match e with
  | SFk (SSm f) (SSm u) => smid_rewrite k f u
  | SFk (SSm f) (SFk _ _ as e2) => bindR (sstep k e2) (fun e' => Ok (SFk (SSm f) e'))
  | SFk (SFk _ _ as e1) e2 => bindR (sstep k e1) (fun e' => Ok (SFk e' e2))
  | SSm _ => Ok e
  | _ => Stuck
  end.

Lemma sstep_sound : forall k e e' sg,
  sstep k e = Ok e' -> mid_step (inst sg e) = inst sg e'.
Proof.
  intros k e; induction e as [|a _|e1 IH1 e2 IH2| | |]; intros e' sg H;
    cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct e1 as [|f|a b| | |]; try discriminate.
    + destruct e2 as [|u|c d| | |]; try discriminate.
      * eapply smid_rewrite_sound; exact H.
      * bind_ok H; inversion H; subst.
        cbn [inst]; unfold mid_step; rewrite step_with_arg; fold mid_step.
        pose proof (IH2 _ sg Ha) as E; cbn [inst] in E; rewrite E; reflexivity.
    + bind_ok H; inversion H; subst.
      cbn [inst]; unfold mid_step; rewrite step_with_op; fold mid_step.
      pose proof (IH1 _ sg Ha) as E; cbn [inst] in E; rewrite E; reflexivity.
Qed.

Fixpoint sready (e : Sym) : R (option (Sym * Sym)) :=
  match e with
  | SFk (SSm f) (SSm u) => Ok (Some (f, u))
  | SFk (SSm _) (SFk _ _ as e2) => sready e2
  | SFk (SFk _ _ as e1) _ => sready e1
  | SSm _ => Ok None
  | _ => Stuck
  end.

Lemma sready_sound : forall e r sg, sready e = Ok r ->
  ready_of (inst sg e) = option_map (fun p => (inst sg (fst p), inst sg (snd p))) r.
Proof.
  induction e as [|a _|e1 IH1 e2 IH2| | |]; intros r sg H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct e1 as [|f|a b| | |]; try discriminate.
    + destruct e2 as [|u|c d| | |]; try discriminate.
      * inversion H; reflexivity.
      * apply (IH2 _ sg) in H; exact H.
    + apply (IH1 _ sg) in H; exact H.
Qed.

Definition sbad_f (k : nat) (f : Sym) : R bool :=
  bindR (hnf k f) (fun f1 =>
  match f1 with
  | SSm g => bindR (hnf k g) (fun g1 =>
      match g1 with
      | SSm g' => bindR (hnf k g') (fun g2 =>
          match g2 with
          | SFk a _ => bindR (hnf k a) (fun a1 =>
              match a1 with SLf => Ok true | SSm _ | SFk _ _ => Ok false | _ => Stuck end)
          | SLf | SSm _ => Ok false
          | _ => Stuck
          end)
      | SLf | SFk _ _ => Ok false
      | _ => Stuck
      end)
  | SLf | SFk _ _ => Ok false
  | _ => Stuck
  end).

Definition sbad_x (k : nat) (x : Sym) : R bool :=
  bindR (hnf k x) (fun x1 =>
  match x1 with
  | SFk a b => bindR (hnf k a) (fun a1 =>
      match a1 with
      | SSm a2 => bindR (hnf k a2) (fun a3 =>
          match a3 with
          | SSm a4 => bindR (hnf k a4) (fun a5 =>
              match a5 with
              | SLf => bindR (hnf k b) (fun b1 =>
                  match b1 with
                  | SFk c _ => bindR (hnf k c) (fun c1 =>
                      match c1 with SLf => Ok true | SSm _ | SFk _ _ => Ok false | _ => Stuck end)
                  | SLf | SSm _ => Ok false
                  | _ => Stuck
                  end)
              | SSm _ | SFk _ _ => Ok false
              | _ => Stuck
              end)
          | SLf | SFk _ _ => Ok false
          | _ => Stuck
          end)
      | SLf | SFk _ _ => Ok false
      | _ => Stuck
      end)
  | SLf | SSm _ => Ok false
  | _ => Stuck
  end).

Definition sbad (k : nat) (e : Sym) : R bool :=
  bindR (sready e) (fun r => match r with
    | None => Ok false
    | Some (f, x) => bindR (sbad_f k f) (fun b => if b then sbad_x k x else Ok false)
    end).

Ltac destruct_all_matches :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] => is_var x; destruct x
         | H : context [match ?x with _ => _ end] |- _ => is_var x; destruct x
         end.

Lemma sbad_f_sound : forall k f sg, sbad_f k f = Ok false ->
  match inst sg f with Sm (Sm (Fk Lf _)) => False | _ => True end.
Proof.
  intros k f sg H; unfold sbad_f in H; bind_ok H; rewrite <- (hnf_sound _ _ _ sg Ha).
  destruct a; try discriminate; cbn [inst]; try exact I.
  bind_ok H; rewrite <- (hnf_sound _ _ _ sg Ha0).
  destruct a0; try discriminate; cbn [inst]; try exact I.
  bind_ok H; rewrite <- (hnf_sound _ _ _ sg Ha1).
  destruct a1; try discriminate; cbn [inst]; try exact I.
  bind_ok H; rewrite <- (hnf_sound _ _ _ sg Ha2).
  destruct a1; try discriminate; cbn [inst]; exact I.
Qed.

Lemma sbad_x_sound : forall k x sg, sbad_x k x = Ok false ->
  match inst sg x with Fk (Sm (Sm Lf)) (Fk Lf _) => False | _ => True end.
Proof.
  intros k x sg H; unfold sbad_x in H.
  bok H x1 H1; rewrite <- (hnf_sound _ _ _ sg H1).
  destruct x1 as [| |a b| | |]; try discriminate; cbn [inst]; try exact I.
  bok H a1 H2; rewrite <- (hnf_sound _ _ _ sg H2).
  destruct a1 as [|a2|? ?| | |]; try discriminate; cbn [inst]; try exact I.
  bok H a3 H3; rewrite <- (hnf_sound _ _ _ sg H3).
  destruct a3 as [|a4|? ?| | |]; try discriminate; cbn [inst]; try exact I.
  bok H a5 H4; rewrite <- (hnf_sound _ _ _ sg H4).
  destruct a5 as [|?|? ?| | |]; try discriminate; cbn [inst]; try exact I.
  bok H b1 H5; rewrite <- (hnf_sound _ _ _ sg H5).
  destruct b1 as [|?|c ?| | |]; try discriminate; cbn [inst]; try exact I.
  bok H c1 H6; rewrite <- (hnf_sound _ _ _ sg H6).
  destruct c1 as [|?|? ?| | |]; try discriminate; cbn [inst]; exact I.
Qed.

Lemma sbad_sound : forall k e sg, sbad k e = Ok false -> bad (inst sg e) = false.
Proof.
  intros k e sg H; unfold sbad in H; bind_ok H; unfold bad.
  rewrite (sready_sound _ _ sg Ha).
  destruct a as [[f x]|]; [|reflexivity]; cbn [option_map fst snd].
  bind_ok H; destruct a.
  - pose proof (sbad_x_sound _ _ sg H) as Hx.
    generalize dependent (inst sg x); generalize (inst sg f); intros F X Hx.
    destruct_all_matches; try reflexivity; contradiction.
  - pose proof (sbad_f_sound _ _ sg Ha0) as Hf.
    generalize dependent (inst sg f); intros F Hf.
    destruct_all_matches; try reflexivity; contradiction.
Qed.

Fixpoint srun (n k : nat) (e : Sym) : R bool :=
  match e with
  | SSm _ => Ok true
  | _ =>
      match n with
      | O => Stuck
      | S n =>
          bindR (sbad k e) (fun b =>
          if b then Ok false else bindR (sstep k e) (fun e' => srun n k e'))
      end
  end.

(** The property established for every instance. *)
Definition runs_well (x : Combination) : Prop :=
  (forall j, bad (mid_steps j x) = false) /\ exists j v, mid_steps j x = Sm v.

Lemma runs_well_finished : forall v, runs_well (Sm v).
Proof.
  intro v; split; [intro j; unfold mid_steps; rewrite steps_with_finished; reflexivity|].
  exists 0, v; reflexivity.
Qed.

Lemma srun_sound : forall n k e sg, srun n k e = Ok true -> runs_well (inst sg e).
Proof.
  induction n as [|n IH]; intros k e sg H.
  - destruct e; cbn in H; try discriminate; apply runs_well_finished.
  - destruct e as [|a|a b| | |];
      try (cbn in H; discriminate).
    + apply runs_well_finished.
    + cbn [srun] in H; bind_ok H; destruct a0; [discriminate|].
      bind_ok H.
      destruct (IH _ _ sg H) as [Hb [j [v Hv]]].
      pose proof (sbad_sound _ _ sg Ha) as H0.
      pose proof (sstep_sound _ _ _ sg Ha0) as H1.
      split.
      * intros [|j']; [exact H0|].
        unfold mid_steps; cbn [steps_with]; fold mid_step; rewrite H1; apply Hb.
      * exists (S j), v; unfold mid_steps in *; cbn [steps_with]; fold mid_step;
          rewrite H1; exact Hv.
Qed.

(** * Splitting holes *)

Fixpoint repl (i : nat) (r s : Sym) : Sym :=
  match s with
  | SLf => SLf
  | SSm a => SSm (repl i r a)
  | SFk a b => SFk (repl i r a) (repl i r b)
  | SHole j => if Nat.eqb i j then r else SHole j
  | SEq1 p => SEq1 (repl i r p)
  | SBool p q => SBool (repl i r p) (repl i r q)
  end.

Lemma inst_repl : forall sg i r s, inst sg r = sg i -> inst sg (repl i r s) = inst sg s.
Proof.
  intros sg i r s Hr; induction s; cbn;
    try rewrite IHs; try rewrite IHs1, IHs2; try reflexivity.
  destruct (Nat.eqb_spec i i0); subst; [exact Hr|reflexivity].
Qed.

Fixpoint below (m : nat) (s : Sym) : bool :=
  match s with
  | SLf => true
  | SSm a | SEq1 a => below m a
  | SFk a b | SBool a b => below m a && below m b
  | SHole j => Nat.ltb j m
  end.

Definition upd (sg : nat -> Combination) (m : nat) (x : Combination) :=
  fun j => if Nat.eqb j m then x else sg j.

Lemma inst_upd : forall sg m x s, below m s = true -> inst (upd sg m x) s = inst sg s.
Proof.
  intros sg m x s; induction s; cbn; intro H;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end;
    try rewrite IHs by assumption; try rewrite IHs1, IHs2 by assumption; try reflexivity.
  unfold upd; destruct (Nat.eqb_spec i m); [apply Nat.ltb_lt in H; lia|reflexivity].
Qed.

Lemma below_mono : forall m m' s, m <= m' -> below m s = true -> below m' s = true.
Proof.
  intros m m' s Hm; induction s; cbn; intro H;
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end;
    auto; try (rewrite IHs1, IHs2; auto).
  apply Nat.ltb_lt in H; apply Nat.ltb_lt; lia.
Qed.

Inductive tree : Set := TLeaf | TSplit (i m : nat) (t0 t1 t2 : tree).

Fixpoint check (t : tree) (n k : nat) (s : Sym) : bool :=
  match t with
  | TLeaf => match srun n k s with Ok true => true | _ => false end
  | TSplit i m t0 t1 t2 =>
      below m s && Nat.ltb i m &&
      check t0 n k (repl i SLf s) &&
      check t1 n k (repl i (SSm (SHole m)) s) &&
      check t2 n k (repl i (SFk (SHole m) (SHole (S m))) s)
  end.

Lemma check_sound : forall t n k s, check t n k s = true -> forall sg, runs_well (inst sg s).
Proof.
  induction t as [|i m t0 IH0 t1 IH1 t2 IH2]; intros n k s H sg; cbn in H.
  - destruct (srun n k s) as [| |[]] eqn:E; try discriminate; eapply srun_sound; exact E.
  - destruct (andb_prop _ _ H) as [H' C2]; destruct (andb_prop _ _ H') as [H'' C1];
    destruct (andb_prop _ _ H'') as [H3 C0]; destruct (andb_prop _ _ H3) as [Hb Hi].
    apply Nat.ltb_lt in Hi.
    destruct (sg i) as [|x|x y] eqn:Ei.
    + rewrite <- (inst_repl sg i SLf s) by (cbn; congruence); eapply IH0; exact C0.
    + set (sg' := upd sg m x).
      assert (E : inst sg' s = inst sg s) by (apply inst_upd; assumption).
      rewrite <- E, <- (inst_repl sg' i (SSm (SHole m)) s).
      * eapply IH1; exact C1.
      * cbn; unfold sg', upd; rewrite Nat.eqb_refl.
        destruct (Nat.eqb_spec i m); [lia|congruence].
    + set (sg' := upd (upd sg m x) (S m) y).
      assert (E : inst sg' s = inst sg s).
      { unfold sg'; rewrite inst_upd by (eapply below_mono; [|eassumption]; lia).
        apply inst_upd; assumption. }
      rewrite <- E, <- (inst_repl sg' i (SFk (SHole m) (SHole (S m))) s).
      * eapply IH2; exact C2.
      * cbn; unfold sg', upd.
        rewrite Nat.eqb_refl.
        destruct (Nat.eqb_spec m (S m)); [lia|].
        rewrite Nat.eqb_refl.
        destruct (Nat.eqb_spec i (S m)); [lia|].
        destruct (Nat.eqb_spec i m); [lia|congruence].
Qed.

Fixpoint explore (d n k : nat) (s : Sym) (m : nat) : tree :=
  match d with
  | O => TLeaf
  | S d =>
      match srun n k s with
      | Hit i =>
          TSplit i m (explore d n k (repl i SLf s) (S (S m)))
                     (explore d n k (repl i (SSm (SHole m)) s) (S (S m)))
                     (explore d n k (repl i (SFk (SHole m) (SHole (S m))) s) (S (S m)))
      | _ => TLeaf
      end
  end.

(** * The name test *)

(** [name_test h], with the name [h] symbolic. *)
Definition sname_test (h : Sym) : Sym :=
  SFk (SSm (SFk SLf
         (SFk (SSm (SFk (SSm (SFk SLf (of_comb equal))) (SFk SLf (SSm h)))) (of_comb ('I)))))
      (of_comb get_tagname).

Lemma inst_sname_test : forall sg h, inst sg (sname_test h) = name_test (inst sg h).
Proof. intros; unfold sname_test; cbn [inst]; rewrite !inst_of; reflexivity. Qed.

Definition as_name_test_sym : Sym := SFk (SSm (sname_test (SHole 0))) (SSm (SHole 1)).

Definition name_test_tree : tree :=
  Eval vm_compute in explore 40 400 2000 as_name_test_sym 2.

Lemma name_test_tree_check : check name_test_tree 400 2000 as_name_test_sym = true.
Proof. vm_compute; reflexivity. Qed.

(** Every name test runs to its answer at the middle granularity, and no
    step of the run builds a value of the shape of a tagged value. *)
Lemma name_test_runs_well : forall n u, runs_well (name_test n @ u).
Proof.
  intros n u.
  pose (sg := fun i => if Nat.eqb i 0 then n else u).
  assert (E : inst sg as_name_test_sym = name_test n @ u).
  { unfold as_name_test_sym; cbn [inst]; rewrite inst_sname_test; reflexivity. }
  rewrite <- E; exact (check_sound _ _ _ _ name_test_tree_check sg).
Qed.


(* ===================================================================== *)
(** * Queries on the snapshots of the middle granularity.

    Every snapshot of [mid_steps] from a typed expression has a value type,
    even inside a name test, where it has no expression type
    ([mid_snapshots_value_typed], for declarations sound by typing).  [size]
    applies with type [Nat] to every snapshot with a value type
    ([size_on_mid_snapshots]); declarations that support queries are not
    sound by typing ([queries_not_sound_by_typing]), so the two are stated
    separately.

    Outside name tests a snapshot keeps its expression type (each step is a
    evaluation rule, or goes straight to the value of an application).
    Inside a name test it keeps a value type: every value it builds is
    either a fork that is not of the shape of a tagged value
    (name_test_runs_well), which has a value type when its parts do, or the
    tester [equal1 p] or a Boolean, which are tag-free. *)

From TreeTyping Require Import tree typing soundness booleans data_types queries.
From Stdlib Require Import Arith Lia.

(** * Contexts of evaluation *)

Inductive ctx : Set :=
| CHole
| COp (c : ctx) (e2 : Combination)
| CArg (f : Combination) (c : ctx).

Fixpoint plug (c : ctx) (x : Combination) : Combination :=
  match c with
  | CHole => x
  | COp c e2 => Fk (plug c x) e2
  | CArg f c => Fk (Sm f) (plug c x)
  end.

Definition is_fork (x : Combination) : Prop := exists a b, x = Fk a b.

Lemma plug_fork : forall c x, is_fork x -> is_fork (plug c x).
Proof. intros c x H; destruct c; cbn; [exact H|eexists; eexists; reflexivity|eexists; eexists; reflexivity]. Qed.

Lemma plug_step : forall rw c x, is_fork x ->
  step_with rw (plug c x) = plug c (step_with rw x).
Proof.
  intros rw c x Hx; induction c as [|c IH e2|f c IH]; cbn [plug]; [reflexivity| |].
  - destruct (plug_fork c x Hx) as [a [b E]]; rewrite E in *.
    change (step_with rw (Fk (Fk a b) e2)) with (Fk (step_with rw (Fk a b)) e2).
    rewrite IH; reflexivity.
  - destruct (plug_fork c x Hx) as [a [b E]]; rewrite E in *.
    change (step_with rw (Fk (Sm f) (Fk a b))) with (Fk (Sm f) (step_with rw (Fk a b))).
    rewrite IH; reflexivity.
Qed.


Lemma ready_decompose : forall e f u, ready_of e = Some (f, u) ->
  exists c, e = plug c (f @ u).
Proof.
  induction e as [|a _|e1 IH1 e2 IH2]; intros f u H; cbn in H; try discriminate.
  destruct e1 as [|g|a b]; try discriminate.
  - destruct e2 as [|v|c1 d1]; try discriminate.
    + inversion H; subst; exists CHole; reflexivity.
    + destruct (IH2 _ _ H) as [cx E]; exists (CArg g cx); cbn; rewrite <- E; reflexivity.
  - destruct (IH1 _ _ H) as [cx E]; exists (COp cx e2); cbn; rewrite <- E; reflexivity.
Qed.

Lemma ready_none_step : forall rw e, ready_of e = None -> step_with rw e = e.
Proof.
  intro rw; induction e as [|a _|e1 IH1 e2 IH2]; intro H; cbn in H; try reflexivity.
  destruct e1 as [|g|a b]; try reflexivity.
  - destruct e2 as [|v|c d]; try reflexivity; [discriminate|].
    change (step_with rw (Fk (Sm g) (Fk c d))) with (Fk (Sm g) (step_with rw (Fk c d))).
    rewrite IH2; auto.
  - change (step_with rw (Fk (Fk a b) e2)) with (Fk (step_with rw (Fk a b)) e2).
    rewrite IH1; auto.
Qed.


Section MidTyping.
Variable AI : Decl.
Hypothesis Hsound : ontology_sound_by_typing AI.

(** ** Contexts and types *)

Lemma plug_typing : forall c x T,
  infer_expression AI @ plug c x ==> Sm T ->
  exists X, infer_expression AI @ x ==> Sm X /\
    forall y, infer_expression AI @ y ==> Sm X -> infer_expression AI @ plug c y ==> Sm T.
Proof.
  induction c as [|c IH e2|f c IH]; intros x T H; cbn [plug] in *.
  - exists T; split; auto.
  - destruct (infer_expression_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 Happ]]]].
    destruct (IH _ _ H1) as [X [HX Hy]].
    exists X; split; [exact HX|intros y Hy'].
    eapply infer_expression_fork; [apply Hy; exact Hy'|exact H2|exact Happ].
  - destruct (infer_expression_fork_inv AI _ _ _ H) as [T1 [T2 [H1 [H2 Happ]]]].
    destruct (IH _ _ H2) as [X [HX Hy]].
    exists X; split; [exact HX|intros y Hy'].
    eapply infer_expression_fork; [exact H1|apply Hy; exact Hy'|exact Happ].
Qed.

Lemma plug_quoted : forall c x y X Y,
  quoted_type AI (plug c x) X -> quoted_type AI y Y ->
  exists Z, quoted_type AI (plug c y) Z.
Proof.
  induction c as [|c IH e2|f c IH]; intros x y X Y Hx Hy; cbn [plug] in *.
  - eauto.
  - inversion Hx; subst.
    match goal with H : quoted_type _ (plug c x) _ |- _ =>
      destruct (IH _ _ _ _ H Hy) as [Z HZ] end.
    eexists; constructor; eassumption.
  - inversion Hx; subst.
    match goal with H : quoted_type _ (plug c x) _ |- _ =>
      destruct (IH _ _ _ _ H Hy) as [Z HZ] end.
    eexists; constructor; eassumption.
Qed.

(** ** Steps outside name tests keep the expression type *)

Lemma mid_ready_typing : forall f u T,
  as_name_test f = None ->
  infer_expression AI @ (f @ u) ==> Sm T ->
  infer_expression AI @ mid_rewrite f u ==> Sm T.
Proof using Hsound.
  intros f u T Hn H.
  destruct (mid_rewrite_ok f u) as [E|[w [Hw E]]]; rewrite E.
  - pose proof (ready_step_typing AI Hsound f u T H) as HT.
    unfold atomic_rewrite in HT; rewrite Hn in HT; exact HT.
  - eapply value_step_typing; eassumption.
Qed.

Lemma mid_step_typing : forall e T,
  infer_expression AI @ e ==> Sm T ->
  (forall f u, ready_of e = Some (f, u) -> as_name_test f = None) ->
  infer_expression AI @ mid_step e ==> Sm T.
Proof using Hsound.
  intros e T H Hn.
  destruct (ready_of e) as [[f u]|] eqn:Er.
  - destruct (ready_decompose _ _ _ Er) as [c ->].
    unfold mid_step; rewrite plug_step by (eexists; eexists; reflexivity).
    destruct (plug_typing _ _ _ H) as [X [HX Hy]].
    apply Hy, mid_ready_typing; [eapply Hn; reflexivity|exact HX].
  - unfold mid_step; rewrite ready_none_step by exact Er; exact H.
Qed.

(** ** Values built inside name tests *)

Lemma tag_free_equal1 : forall p, tag_free (equal1 p) = true.
Proof.
  induction p as [|p IH|p1 IH1 p2 IH2]; [reflexivity| |].
  - change (equal1 (Sm p)) with ('triage [('KI), equal1 p, 'K1 ('K1 ('KI))]).
    cbn [tag_free]; rewrite IH; reflexivity.
  - change (equal1 (Fk p1 p2)) with
      ('triage ['KI, 'K1 'KI, 'S2 ['S2 [equal1 p1, 'K1 equal1 p2], 'K1 ('K1 'KI)]]).
    destruct (equal1_shape p1) as [a [b [c E]]].
    cbn [tag_free]; rewrite IH1, IH2, E; reflexivity.
Qed.

Definition bad_pair (f u : Combination) : bool :=
  match f, u with
  | Sm (Sm (Fk Lf _)), Fk (Sm (Sm Lf)) (Fk Lf _) => true
  | _, _ => false
  end.

Lemma bad_ready : forall x f u, ready_of x = Some (f, u) -> bad x = bad_pair f u.
Proof. intros x f u H; unfold bad; rewrite H; reflexivity. Qed.

Lemma inv_K1_type : forall x C, infer AI @ x ==> Sm (Fk Lf C) -> exists r, x = Fk Lf r.
Proof.
  intros x C H.
  assert (Hp : forall E N, Fk Lf C <> 'tagged[E,N]) by (intros E N Heq; discriminate Heq).
  destruct (infer_plain_fork_inv AI x Lf C Hp H) as [l [r [-> [Hl _]]]].
  pose proof (infer_tag_free_inv AI _ _ Hl eq_refl) as ->; eauto.
Qed.

Lemma inv_label_type : forall x N,
  infer AI @ x ==> Sm (Fk (Sm (Sm Lf)) (Fk Lf N)) ->
  exists r, x = Fk (Sm (Sm Lf)) (Fk Lf r).
Proof.
  intros x N H.
  assert (Hp : forall E M, Fk (Sm (Sm Lf)) (Fk Lf N) <> 'tagged[E,M])
    by (intros E M Heq; discriminate Heq).
  destruct (infer_plain_fork_inv AI x _ _ Hp H) as [u1 [u2 [-> [Hu1 Hu2]]]].
  destruct (infer_stem_result_inv AI _ _ Hu1) as [u1' [-> Hu1']].
  pose proof (infer_tag_free_inv AI _ _ Hu1' eq_refl) as ->.
  destruct (inv_K1_type _ _ Hu2) as [r ->]; eauto.
Qed.

Lemma construction_typed : forall g u G U,
  infer AI @ g ==> Sm G -> infer AI @ u ==> Sm U ->
  bad_pair (Sm g) u = false ->
  exists W, infer AI @ Fk g u ==> Sm W.
Proof.
  intros g u G U HG HU Hb.
  destruct (tagged_decide (Fk G U)) as [[C [N E]]|Hp].
  - exfalso; inversion E; subst.
    destruct (infer_stem_result_inv AI _ _ HG) as [g' [-> Hg']].
    destruct (inv_K1_type _ _ Hg') as [r ->].
    destruct (inv_label_type _ _ HU) as [t ->].
    discriminate Hb.
  - eexists; apply plain_construction_typed; eassumption.
Qed.

Lemma mid_rewrite_quoted : forall f u F U,
  infer AI @ f ==> Sm F -> infer AI @ u ==> Sm U ->
  bad_pair f u = false ->
  exists X, quoted_type AI (mid_rewrite f u) X.
Proof.
  intros f u F U Hf Hu Hb; unfold mid_rewrite.
  destruct (cmb_eqb f equal).
  - eexists; constructor; apply infer_tag_free, tag_free_equal1.
  - destruct (cmb_eqb f (equal1 (decode f))).
    + eexists; constructor; apply infer_tag_free;
        destruct (cmb_eqb (decode f) u); reflexivity.
    + eapply rule_rewrite_quoted; [exact Hf|exact Hu|].
      intros g ->; destruct (infer_stem_inv AI _ _ Hf) as [G [_ HG]].
      eapply construction_typed; eassumption.
Qed.

Lemma mid_step_quoted : forall e X,
  quoted_type AI e X -> bad e = false ->
  exists X', quoted_type AI (mid_step e) X'.
Proof.
  induction e as [|v _|a IHa b IHb]; intros X H Hb; [inversion H|exists X; exact H|].
  inversion H as [|a' b' A B Ha Hb']; subst.
  destruct a as [|f|a1 a2]; [inversion Ha| |].
  - inversion Ha as [f' F HF|]; subst.
    destruct b as [|u|b1 b2]; [inversion Hb'| |].
    + inversion Hb' as [u' U HU|]; subst.
      apply (mid_rewrite_quoted f u F U HF HU).
      rewrite <- (bad_ready (f @ u) f u); [exact Hb|reflexivity].
    + assert (Hb2 : bad (Fk b1 b2) = false).
      { unfold bad in *; cbn [ready_of] in Hb; exact Hb. }
      destruct (IHb _ Hb' Hb2) as [B' HB'].
      exists (Fk (Sm F) B'); unfold mid_step in *; rewrite step_with_arg.
      constructor; [exact Ha|exact HB'].
  - assert (Ha2 : bad (Fk a1 a2) = false).
    { unfold bad in *; cbn [ready_of] in Hb; exact Hb. }
    destruct (IHa _ Ha Ha2) as [A' HA'].
    exists (Fk A' B); unfold mid_step in *; rewrite step_with_op.
    constructor; [exact HA'|exact Hb'].
Qed.

(** ** The runs of name tests *)

Lemma runs_well_shape : forall x, runs_well x ->
  forall j, (exists v, mid_steps j x = Sm v) \/ is_fork (mid_steps j x).
Proof.
  intros x [_ [k [v Hk]]] j.
  destruct (mid_steps j x) as [|w|a b] eqn:E; eauto.
  - exfalso.
    assert (forall d, mid_steps (j + d) x = Lf).
    { intro d; unfold mid_steps in *; rewrite steps_with_add, E.
      induction d; [reflexivity|cbn; exact IHd]. }
    destruct (Nat.le_gt_cases j k) as [Hjk|Hjk].
    + replace k with (j + (k - j)) in Hk by lia; rewrite H in Hk; discriminate.
    + unfold mid_steps in *.
      replace j with (k + (j - k)) in E by lia.
      rewrite steps_with_add, Hk, steps_with_finished in E; discriminate.
  - right; eexists; eexists; reflexivity.
Qed.


Lemma name_test_quoted : forall n u T j,
  infer_expression AI @ (name_test n @ u) ==> Sm T ->
  exists X, quoted_type AI (mid_steps j (name_test n @ u)) X.
Proof.
  intros n u T j H.
  destruct (expression_quoted_type AI _ _ H) as [X0 H0].
  destruct (name_test_runs_well n u) as [Hbad _].
  induction j as [|j IH]; [exists X0; exact H0|].
  destruct IH as [X HX].
  unfold mid_steps in *; rewrite steps_with_S; fold mid_step.
  eapply mid_step_quoted; [exact HX|apply Hbad].
Qed.

Lemma name_test_answer : forall n u v j T,
  infer_expression AI @ (name_test n @ u) ==> Sm T ->
  mid_steps j (name_test n @ u) = Sm v ->
  infer_expression AI @ Sm v ==> Sm T.
Proof using Hsound.
  intros n u v j T H E.
  assert (Hv : name_test n @ u ==> v)
    by (apply (proj2 (mid_steps_agree _ _)); exists j; exact E).
  eapply value_step_typing; eassumption.
Qed.

(** ** The invariant *)

Definition snapshot_ok (e : Combination) : Prop :=
  (exists T, infer_expression AI @ e ==> Sm T) \/
  (exists c n u j T,
     infer_expression AI @ plug c (name_test n @ u) ==> Sm T /\
     e = plug c (mid_steps j (name_test n @ u)) /\
     is_fork (mid_steps j (name_test n @ u))).

Lemma name_test_continue : forall c n u j T,
  infer_expression AI @ plug c (name_test n @ u) ==> Sm T ->
  is_fork (mid_steps j (name_test n @ u)) ->
  snapshot_ok (plug c (mid_steps (S j) (name_test n @ u))).
Proof using Hsound.
  intros c n u j T H Hj.
  destruct (runs_well_shape _ (name_test_runs_well n u) (S j)) as [[v Ev]|Hf].
  - left; rewrite Ev.
    destruct (plug_typing _ _ _ H) as [X [HX Hy]].
    exists T; apply Hy; eapply name_test_answer; eassumption.
  - right; exists c, n, u, (S j), T; repeat split; assumption.
Qed.

Lemma snapshot_ok_step : forall e, snapshot_ok e -> snapshot_ok (mid_step e).
Proof using Hsound.
  intros e [[T H]|[c [n [u [j [T [H [-> Hj]]]]]]]].
  - destruct (ready_of e) as [[f u]|] eqn:Er.
    + destruct (as_name_test f) as [n|] eqn:En.
      * apply as_name_test_some in En; subst f.
        destruct (ready_decompose _ _ _ Er) as [c ->].
        unfold mid_step; rewrite plug_step by (eexists; eexists; reflexivity).
        change (step_with mid_rewrite (name_test n @ u)) with (mid_steps 1 (name_test n @ u)).
        apply (name_test_continue c n u 0 T H); eexists; eexists; reflexivity.
      * left; exists T; apply mid_step_typing; [exact H|].
        intros f' u' E; rewrite Er in E; inversion E; subst; exact En.
    + left; exists T; unfold mid_step; rewrite ready_none_step by exact Er; exact H.
  - unfold mid_step; rewrite plug_step by exact Hj; fold mid_step.
    replace (mid_step (mid_steps j (name_test n @ u)))
      with (mid_steps (S j) (name_test n @ u))
      by (unfold mid_steps, mid_step; rewrite steps_with_S; reflexivity).
    eapply name_test_continue; eassumption.
Qed.

Lemma snapshot_ok_quoted : forall e, snapshot_ok e -> exists X, quoted_type AI e X.
Proof.
  intros e [[T H]|[c [n [u [j [T [H [-> Hj]]]]]]]].
  - eapply expression_quoted_type; exact H.
  - destruct (expression_quoted_type AI _ _ H) as [X0 H0].
    destruct (plug_typing _ _ _ H) as [X [HX _]].
    destruct (name_test_quoted n u X j HX) as [Y HY].
    eapply plug_quoted; eassumption.
Qed.

Lemma mid_snapshots_value_typed : forall e T k,
  infer_expression AI @ e ==> Sm T ->
  exists X, infer AI @ mid_steps k e ==> Sm X.
Proof using Hsound.
  intros e T k H.
  assert (Hk : snapshot_ok (mid_steps k e)).
  { induction k as [|k IH]; [left; exists T; exact H|].
    unfold mid_steps in *; rewrite steps_with_S; fold mid_step.
    apply snapshot_ok_step, IH. }
  destruct (snapshot_ok_quoted _ Hk) as [X HX].
  exists X; apply quoted_type_infer; exact HX.
Qed.

Hypothesis Hq : supports_queries AI.
Hypothesis Hn : supports_number AI.

(** Queries observe every snapshot of evaluation, even inside a name test. *)
Lemma size_on_mid_snapshots : forall e X k,
  infer AI @ mid_steps k e ==> Sm X ->
  infer_expression AI @ (size @ mid_steps k e) ==> Sm ('Nat) /\
  size @ mid_steps k e ==> numeral (tree_size (mid_steps k e)).
Proof using Hq Hn.
  intros e X k H; eapply size_on_quoted; [exact Hq|exact Hn|exact H].
Qed.

End MidTyping.


(* ===================================================================== *)
(* Part: patching during evaluation *)
(** * Patching an expression paused in evaluation

    An expression may be paused after any number of steps and patched by a
    typed update; the patched snapshot keeps the type of the snapshot,
    since updates preserve expression typing
    ([update_preserves_expression_typing], patching.v).  As for
    [size_on_snapshots], the typing of the snapshot is a premise: for
    declarations sound by typing it follows from the typing of the
    original expression ([steps_preserve_expression_typing]), but the
    paper's declarations support updates and so are not sound by typing
    ([updates_not_sound_by_typing]). *)

From TreeTyping Require Import patching.

Lemma patch_during_evaluation : forall (AI : Decl) k e e' u e'' T,
  ontology_sound AI ->
  infer_expression AI @ steps k e ==> Sm T ->
  e' = steps k e ->
  infer AI @ u ==> Sm ('Update) ->
  u @ e' ==> e'' ->
  infer_expression AI @ e'' ==> Sm T.
Proof.
  intros AI k e e' u e'' T Hsound He -> Hu Hupd.
  eapply update_preserves_expression_typing; eassumption.
Qed.
