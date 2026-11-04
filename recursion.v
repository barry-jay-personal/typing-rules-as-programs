(** * Recursion support.

    Typed recursive number programs and minimisation, and
    structural recursion: totality and result preservation of fixpoints
    whose bodies recurse on immediate children.

    Build order: this file precedes conditionals.v and queries.v, because
    the size query uses its recursion machinery.  The
    self-typing theorems, including the Turing completeness
    of the concrete programs, are in self_typing.v. *)


(**********************************************************************)
(* Primitive recursion and minimisation over Scott natural numbers.   *)
(**********************************************************************)

(** The operators below are higher-order only to expose parameters such as
    the base, step, and predicate.  This is the cost of presenting the usual
    polymorphic recursion schemes inside the object language: every parameter
    needs an abstraction and hence an inferred intermediate type.  Their
    specialized forms [prec2] and [minimisation2] avoid that overhead and are
    generally preferable when fixfunctions are already available.

    Maintenance note: the proofs below currently duplicate their [type_app]
    and stem-construction dispatchers between specialized and higher-order primitive
    recursion and minimisation.  This should eventually become two shared
    tactics: one for ordinary [type_app] structure and one which commits to
    the direct-function, recursive-function, or structural stem case.  The
    duplication is left explicit for now so that this refactoring does not
    disturb the newly stabilized proofs. *)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans data_types.

Set Default Proof Using "Type".
Open Scope string_scope.
Opaque equal.

Section NumberFunctionExamples.
Set Default Proof Using "All".
Variable AI : Decl.
Hypothesis AI_supports_booleans : supports_booleans AI.
Hypothesis AI_supports_number : supports_number AI.
Local Abbreviation ontology_3 := AI.

Definition typed_zero_function := lam ('K1 zero) zero.

Lemma typed_zero_function_infer :
  infer ontology_3 @ typed_zero_function ==> Sm ('Nat --> 'Nat).
Proof.
  unfold typed_zero_function; eapply infer_lam.

  - eapply infer_K1; eapply infer_zero; eauto.
  - eapply infer_zero; eauto.
  - eapply type_app_K_ev.
Qed.

Definition typed_zero_binary := lam ('K1 typed_zero_function) zero.


(**********************************************************************)
(* Typed successor.                                                    *)
(**********************************************************************)

(* reverse order of args to lam !! *)

Definition successor_function_body :=
  Eval cbn in (to_tree (\ "n" (''tagged[''S2[Val 'snd,Ref "n"],Val nat_nm]))).

Definition successor_function := lam successor_function_body zero.

Lemma infer_successor_function : infer ontology_3 @ successor_function ==> Sm ('Nat --> 'Nat). 
Proof.
  eapply infer_lam.

  - unfold successor_function_body; cbn; infer_tac.
  - eapply infer_zero; eauto.
  - unfold successor_function_body; cbn; repeat ty.
Qed.

Lemma successor_function_operation : forall n,
  successor_function @ n ==> succ n.
Proof.
  intro n; unfold successor_function, lam.
  eapply tagged_eval.
  eapply wait_eval.
  unfold successor_function_body; cbn; evaluate.
Qed.

(**********************************************************************)
(* Predecessor, expressed directly through the Scott eliminator.      *)
(**********************************************************************)

Definition query_predecessor : Combination :=
  lam nat_pred zero.

Lemma query_predecessor_zero : query_predecessor @ zero ==> zero.
Proof. apply lam_eval; exact (nat_pred_numeral 0). Qed.

Lemma query_predecessor_succ : forall k,
  query_predecessor @ succ (numeral k) ==> numeral k.
Proof. intro k; apply lam_eval; exact (nat_pred_numeral (S k)). Qed.

Lemma infer_query_predecessor :
  infer AI @ query_predecessor ==> Sm ('Nat --> 'Nat).
Proof.
  unfold query_predecessor; eapply infer_lam.
  - apply infer_tag_free; vm_compute; reflexivity.
  - eapply infer_zero; eauto.
  - unfold nat_pred; repeat ty.
Qed.

(**********************************************************************)
(* First presentation of addition: a directly typed fixfunction.     *)
(**********************************************************************)

(** Addition is a fold: [n @ (a * successor)].  Only the boundaries of
    the function type remain. *)
Definition addition_inner (a : Term) : Term :=
  lam2 (star "n" (Ref "n" @@ (a ''* Val successor_function))) (Val zero).
Definition addition_body : Combination := Eval cbn -[successor_function] in
  to_tree (star "a" (addition_inner (Ref "a"))).
Definition addition : Combination := lam addition_body zero.

Lemma infer_addition :
  infer AI @ addition ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  pose proof infer_successor_function as HS.
  pose proof (infer_zero AI AI_supports_number) as HZ.
  unfold addition; eapply infer_lam; [|exact HZ|].
  - unfold addition_body; cbn -[successor_function].
    repeat first [exact HS | exact HZ | eapply infer_lam | eapply infer_fork
      | eapply infer_stem | eapply infer_leaf | eapply infer_I | eapply infer_K1 | ty].
  - unfold addition_body; cbn -[successor_function].
    repeat first [exact HS | exact HZ | eapply infer_lam | eapply infer_fork
      | eapply infer_stem | eapply infer_leaf | eapply infer_I | eapply infer_K1 | ty].
Qed.

Lemma addition_fold : forall a n r,
  n @ (a '* successor_function) ==> r -> addition @ a @r n ==> r.
Proof.
  intros a n r H; unfold addition.
  eapply eval_appl; [apply lam_eval; unfold addition_body; cbn -[successor_function]; d_eval|].
  apply lam_eval; d_eval.
Qed.

Lemma addition_zero : forall a,
  addition @ a @r zero ==> a.
Proof. intro a; apply addition_fold; apply zero_apply. Qed.

Lemma tagged_unary_inv : forall f t u r, 'tagged[f,t] @ u ==> r -> f @ u ==> r.
Proof. intros f t u r H; cbv in H |- *; invert_eval. Qed.
Lemma lam_eval_inv : forall f d u v, lam f d @ u ==> v -> f @ u ==> v.
Proof.
  intros f d u v H; unfold lam in H; apply tagged_unary_inv, wait_eval_inv in H.
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hr]].
  pose proof (eval_deterministic _ _ Hw _ (eval_k _ _)) as ->; exact Hr.
Qed.
Lemma swap_eval_inv : forall p n r, swap p @ n ==> r -> n @ p ==> r.
Proof. intros p n r H; unfold swap in H; invert_eval. Qed.

Lemma addition_head : forall a,
  addition @ a ==> lam (swap (a '* successor_function)) zero.
Proof.
  intros a; apply lam_eval; unfold addition_body, lam, swap; cbn -[successor_function]; d_eval.
Qed.
Lemma addition_fold_inv : forall a n r,
  addition @ a @r n ==> r -> n @ (a '* successor_function) ==> r.
Proof.
  intros a n r H; destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hr]].
  pose proof (eval_deterministic _ _ Hw _ (addition_head a)) as ->.
  apply lam_eval_inv, swap_eval_inv in Hr; exact Hr.
Qed.

Lemma addition_succ : forall a n r,
  addition @ a @r n ==> r ->
  addition @ a @r succ n ==> succ r.
Proof.
  intros a n r H; apply addition_fold.
  eapply succ_apply; [apply addition_fold_inv; exact H|apply successor_function_operation].
Qed.

(** Addition by general recursion on the predecessor, kept for the
    erasure of optimisation.v. *)
Local Definition addition_step_term (recursive a : Term) : Term :=
  lam2 (Val successor_function ''C ''wait[recursive,a]) (Val zero).
Local Definition addition_inner_term (recursive a : Term) : Term :=
  lam2 (star "n" (Val nat_split @@ Ref "n" @@ (a ''* addition_step_term recursive a))) (Val zero).
Local Definition addition_value_term (recursive : Term) : Term :=
  lam2 (star "a" (addition_inner_term recursive (Ref "a"))) (Val zero).
Definition addition_functional_body_package :
  { t : Combination | to_tree (star "recursive" (addition_value_term (Ref "recursive"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition addition_functional_body : Combination :=
  Eval cbn in proj1_sig addition_functional_body_package.
Lemma infer_addition_seed :
  infer AI @ typed_zero_binary ==> Sm ('Nat --> ('Nat --> 'Nat)).
Proof.
  unfold typed_zero_binary, typed_zero_function.
  eapply infer_lam.
  - eapply infer_K1; eapply infer_lam.
    + eapply infer_K1; eapply infer_zero; eauto.
    + eapply infer_zero; eauto.
    + apply type_app_K_ev.
  - eapply infer_zero; eauto.
  - apply type_app_K_ev.
Qed.

Opaque successor_function.

End NumberFunctionExamples.
Set Default Proof Using "Type".

Section TuringExamples.

Set Default Proof Using "All".
Variable AI : Decl.
Hypothesis AI_supports_booleans : supports_booleans AI.
Hypothesis AI_supports_number : supports_number AI.

(**********************************************************************)
(* Typed primitive recursion on natural numbers.                      *)
(**********************************************************************)

Local Definition prec_lam_term (f d : Term) : Term :=
  lam2 f d.

Local Definition prec_step_term
    (step recursive : Term) : Term :=
  prec_lam_term
    (star "n"
      (step @@ (Ref "n" ''* (recursive @@ Ref "n"))))
    (Val zero).

Local Definition prec_value_term
    (base step recursive : Term) : Term :=
  prec_lam_term
    (star "n"
      (Val nat_split @@ Ref "n" @@
        (base ''* prec_step_term step recursive)))
    (Val zero).

Local Definition prec_functional_term
    (base step : Term) : Term :=
  star "recursive"
    (prec_value_term base step (Ref "recursive")).

Definition prec_functional_body_package (base step : Combination) :
  { t : Combination |
    to_tree (prec_functional_term (Val base) (Val step)) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition prec_functional_body (base step : Combination) : Combination :=
  Eval cbn in proj1_sig (prec_functional_body_package base step).

Definition prec_seed (base : Combination) : Combination :=
  lam ('K1 base) zero.

Definition prec_functional
    (base step : Combination) : Combination :=
  lam (prec_functional_body base step) (prec_seed base).

Definition prec2 (base step : Combination) : Combination :=
  'fix[prec_functional base step].

Definition prec_pair_witness : Combination := zero '* zero.

Definition prec_step_witness : Combination :=
  lam ('K1 zero) prec_pair_witness.

(** Primitive recursion must also exist as a higher-order object-language
    function.  Although the recursion itself is first-order, abstracting over
    [base] and [step] supplies the parametrisation used in the standard
    first-order account of Turing completeness.  [prec2] is the convenient
    Coq-level specialization; [prec] is its object-language abstraction. *)
Local Definition prec_seed_term (base : Term) : Term :=
  prec_lam_term (''K1 base) (Val zero).

Local Definition prec_functional_value_term
    (base step : Term) : Term :=
  prec_lam_term
    (prec_functional_term base step)
    (prec_seed_term base).

Local Definition prec2_term (base step : Term) : Term :=
  ''tagged[
    Z2 (prec_functional_value_term base step ''C Val tagged_fun),
    Val fun_nm].

Lemma prec2_term_alignment : forall base step,
  to_tree (prec2_term (Val base) (Val step)) = prec2 base step.
Proof.
  intros; unfold prec2_term, prec_functional_value_term,
    prec_seed_term, prec_lam_term, prec_functional_term,
    prec_value_term, prec_step_term.
  unfold prec2, fix_function, prec_functional,
    prec_functional_body, prec_seed, lam, lam2; reflexivity.
Qed.

Definition prec_with_body_package (base : Combination) :
  { t : Combination |
    to_tree (star "step" (prec2_term (Val base) (Ref "step"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition prec_with_body (base : Combination) : Combination :=
  Eval cbn in proj1_sig (prec_with_body_package base).

Definition prec_with (base : Combination) : Combination :=
  lam (prec_with_body base) prec_step_witness.

Local Definition prec_with_term (base : Term) : Term :=
  ''tagged[
    ''decorate[
      star "step" (prec2_term base (Ref "step")),
      Val prec_step_witness],
    Val fun_nm].

Lemma prec_with_term_alignment : forall base,
  to_tree (prec_with_term (Val base)) = prec_with base.
Proof. intros; reflexivity. Qed.

Definition prec_package :
  { t : Combination |
    to_tree
      (''tagged[
        ''decorate[
          star "base" (prec_with_term (Ref "base")),
          Val zero],
        Val fun_nm]) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition prec : Combination :=
  Eval cbn in proj1_sig prec_package.

Lemma prec_first : forall base,
  prec @ base ==> prec_with base.
Proof.
  intros base; unfold prec, prec_package; cbn.
  eapply tagged_eval; eapply wait_eval; eapply eval_appl.
  - apply eval_k.
  - rewrite <- prec_with_term_alignment.
    unfold prec_with_term; cbn; evaluate.
Qed.

Lemma prec_with_eval : forall base step,
  prec_with base @ step ==> prec2 base step.
Proof.
  intros base step; unfold prec_with, lam.
  eapply tagged_eval; eapply wait_eval; eapply eval_appl.
  - apply eval_k.
  - rewrite <- prec2_term_alignment.
    unfold prec_with_body, prec2_term; cbn; evaluate.
Qed.

Lemma prec_eval : forall base step,
  prec @ base @r step ==> prec2 base step.
Proof.
  intros; eapply eval_appl.
  - apply prec_first.
  - apply prec_with_eval.
Qed.

Lemma infer_prec_seed : forall base,
  infer AI @ base ==> Sm ('Nat) ->
  infer AI @ prec_seed base ==> Sm ('Nat --> 'Nat).
Proof.
  intros base Hbase; unfold prec_seed; eapply infer_lam.

  - eapply infer_K1; exact Hbase.
  - eapply infer_zero; eauto.
  - apply type_app_K_ev.
Qed.

Local Ltac known_prec_type_app_step := ty.
Local Ltac prec_infer :=
  repeat first
    [ match goal with H : infer _ @ ?x ==> Sm ?X |- _ => exact H end
    | solve [eapply infer_zero; eauto]
    | eapply infer_fix_function
    | apply infer_nat_split
    | eapply infer_lam
    | eapply infer_fork
    | eapply infer_stem
    | eapply infer_leaf
    | eapply infer_I
    | eapply infer_K1
    ].

Local Ltac known_prec_type_app_step0 :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | ?A --> ?B =>
          eapply type_app_abstract; apply funty_eliminator_eval
      | nat_split => unfold nat_split
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | 'Nat => eapply type_app_Nat
      | 'tagged[?C,?N] =>
          eapply type_app_abstract; evaluate
      | Lf => eapply type_app_leaf_ev
      | Fk Lf ?x => eapply type_app_K_ev
      | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
      | Sm ?x => eapply type_app_stem_ev
      | Fk (Sm (Fk Lf ?g)) ?f =>
          eapply type_app_compose; [solve [reject_name]| | |];
          [ solve [intros E N Heq; discriminate Heq] | |]
      | Fk (Sm ?g) ?f =>
          new_S;
          [ solve [intros E N Heq; discriminate Heq] | | |]
      end
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      first
        [ eapply type_app_stem_function
        | eapply type_app_stem_structural; intros E N Heq; inversion Heq ]
  end.

Local Definition prec_functional_type_package
    (base step H : Combination)
    (Hbase : infer AI @ base ==> Sm ('Nat))
    (Hstep : infer AI @ step ==> Sm H)
    (Hstep_app :
      type_app AI @ H @r ('Nat '* 'Nat) ==> Sm ('Nat)) :
  { F : Combination |
      infer AI @ prec_functional_body base step ==> Sm F /\
      type_app AI @ F @r ('Nat --> 'Nat) ==>
        Sm ('Nat --> 'Nat) }.
Proof.
  eexists; split.
  - unfold prec_functional_body, prec_functional_term,
      prec_value_term, prec_step_term,
      prec_lam_term, lam2; cbn.
    all: repeat first
      [ exact Hbase | exact Hstep | exact Hstep_app
      | progress prec_infer | known_prec_type_app_step ].
  - unfold prec_functional_body, prec_functional_term,
      prec_value_term, prec_step_term,
      prec_lam_term, lam2; cbn.
    all: repeat first
      [ exact Hbase | exact Hstep | exact Hstep_app
      | progress prec_infer | known_prec_type_app_step ].
Defined.

Lemma infer_prec_functional : forall base step H
    (Hbase : infer AI @ base ==> Sm ('Nat))
    (Hstep : infer AI @ step ==> Sm H)
    (Hstep_app :
      type_app AI @ H @r ('Nat '* 'Nat) ==> Sm ('Nat)),
  infer AI @ prec_functional base step ==>
    Sm (('Nat --> 'Nat) --> ('Nat --> 'Nat)).
Proof.
  intros base step H Hbase Hstep Hstep_app.
  unfold prec_functional; eapply infer_lam.

  - exact (proj1 (proj2_sig
      (prec_functional_type_package
        base step H Hbase Hstep Hstep_app))).
  - apply infer_prec_seed; exact Hbase.
  - exact (proj2 (proj2_sig
      (prec_functional_type_package
        base step H Hbase Hstep Hstep_app))).
Qed.

Lemma infer_prec2 : forall base step H
    (Hbase : infer AI @ base ==> Sm ('Nat))
    (Hstep : infer AI @ step ==> Sm H)
    (Hstep_app :
      type_app AI @ H @r ('Nat '* 'Nat) ==> Sm ('Nat)),
  infer AI @ prec2 base step ==> Sm ('Nat --> 'Nat).
Proof.
  intros base step H Hbase Hstep Hstep_app.
  unfold prec2.
  eapply infer_fix_function.

  - eapply infer_prec_functional; eauto.
Qed.

(**********************************************************************)
(* Witnesses used by the typing proof for specialized recursion.      *)
(**********************************************************************)

Lemma infer_prec_pair_witness :
  infer AI @ prec_pair_witness ==> Sm ('Nat '* 'Nat).
Proof.
  unfold prec_pair_witness.
  all: repeat first
    [ solve [eapply infer_zero; eauto]
    | progress prec_infer
    | known_prec_type_app_step ].
Qed.

Lemma infer_prec_step_witness :
  infer AI @ prec_step_witness ==>
    Sm (('Nat '* 'Nat) --> 'Nat).
Proof.
  unfold prec_step_witness; eapply infer_lam.

  - eapply infer_K1; eapply infer_zero; eauto.
  - eapply infer_prec_pair_witness; eauto.
  - apply type_app_K_ev.
Qed.

Local Ltac higher_prec_infer :=
  lazymatch goal with
  | |- infer _ @ ?x ==> _ =>
      first
        [ eapply infer_prec_step_witness
        | eapply infer_prec_pair_witness
        | solve [eapply infer_zero; eauto]
        | eapply infer_fix_function
        | apply infer_nat_split
        | eapply infer_lam
        | eapply infer_fork
        | eapply infer_stem
        | eapply infer_leaf
        | eapply infer_I
        | eapply infer_K1 ]
  end.

Local Ltac higher_prec_type_app := ty.
Local Ltac higher_prec_type_app0 :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      first
        [ change (type_app AI @ 'Nat @r _ ==> _); eapply type_app_Nat
        | change (type_app AI @ (?A --> ?B) @r _ ==> _);
          eapply type_app_abstract; apply funty_eliminator_eval
        | lazymatch T with
          | Lf => eapply type_app_leaf_ev
          | Fk Lf ?x => eapply type_app_K_ev
          | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
          | Sm ?x => eapply type_app_stem_ev
          | Fk (Sm (Fk Lf ?g)) ?f =>
              eapply type_app_compose; [solve [reject_name]| | |];
              [ intros E N Heq; discriminate Heq | |]
          | Fk (Sm ?g) ?f =>
              new_S;
              [ intros E N Heq; discriminate Heq | | |]
          end ]
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      first [eapply type_app_stem_structural; intros E N Heq; discriminate Heq]
  end.

Lemma infer_prec :
  infer AI @ prec ==>
    Sm ('Nat --> (('Nat '* 'Nat --> 'Nat) --> ('Nat --> 'Nat))).
Proof.
  eapply infer_lam; [ | |].
  2: eapply infer_zero; eauto.
  all: unfold prec, prec_package; cbn.
  all: repeat first [progress higher_prec_infer | ty].
Qed.

(**********************************************************************)
(* Defining equations.                                                *)
(**********************************************************************)

Local Opaque nat_split.
Lemma prec2_zero : forall base step,
  prec2 base step @ zero ==> base.
Proof.
  intros base step.
  destruct (nat_split_parts zero) as [w [Hw [Hq Hp]]].
  unfold prec2, fix_function.
  eapply tagged_eval.
  eapply Z_unfold.
  eapply eval_appl.
  - eapply eval_c; eapply eval_appr.
    + apply tagged_fun_eval.
    + unfold prec_functional, lam.
      eapply tagged_eval; eapply wait_eval.
      unfold prec_functional_body, prec_functional_term,
        prec_value_term, prec_step_term, prec_lam_term, lam2; cbn -[nat_split]; ge_eval.
  - apply tagged_eval; apply wait_eval; ge_eval.
Qed.

Lemma prec2_succ : forall base step k recursive_result result,
  prec2 base step @ numeral k ==> recursive_result ->
  step @ (numeral k '* recursive_result) ==> result ->
  prec2 base step @ succ (numeral k) ==> result.
Proof.
  intros base step k recursive_result result Hrecursive Hstep.
  destruct (nat_split_parts (succ (numeral k))) as [w [Hw [Hq Hp]]].
  unfold prec2, fix_function.
  eapply tagged_eval.
  eapply Z_unfold.
  eapply eval_appl.
  - eapply eval_c; eapply eval_appr.
    + apply tagged_fun_eval.
    + unfold prec_functional, lam.
      eapply tagged_eval; eapply wait_eval.
      unfold prec_functional_body, prec_functional_term,
        prec_value_term, prec_step_term, prec_lam_term, lam2; cbn -[nat_split]; ge_eval.
  - apply tagged_eval; apply wait_eval; ge_eval.
Qed.

Lemma prec_zero : forall base step,
  prec @ base @r step @r zero ==> base.
Proof.
  intros; eapply eval_appl.
  - apply prec_eval.
  - apply prec2_zero.
Qed.

Lemma prec_succ : forall base step k recursive_result result,
  prec @ base @r step @r numeral k ==> recursive_result ->
  step @ (numeral k '* recursive_result) ==> result ->
  prec @ base @r step @r succ (numeral k) ==> result.
Proof.
  intros base step k recursive_result result Hrecursive Hstep.
  invert_eval.
  assert (Hhead : prec @ base @r step ==> v1)
    by (eapply eval_appl; eauto).
  pose proof (eval_deterministic _ _ Hhead _ (prec_eval base step)) as Heq.
  subst v1.
  eapply eval_appl.
  - apply prec_eval.
  - eapply prec2_succ; eauto.
Qed.

(**********************************************************************)
(* Minimisation.                                                       *)
(**********************************************************************)

(** Delay [program @ argument] until a witness control token is supplied; the
    token is then ignored.  This is waiting, not an environment-bearing
    closure. *)
Local Definition typed_minimisation_wait_package :
  { t : Combination |
    to_tree
      (star "program"
        (star "argument"
          (star "token" (Ref "program" @@ Ref "argument")))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Local Definition typed_minimisation_wait : Combination :=
  Eval cbn in proj1_sig typed_minimisation_wait_package.

Local Lemma typed_minimisation_wait_compilation :
  to_tree
    (star "program"
      (star "argument"
        (star "token" (Ref "program" @@ Ref "argument")))) =
  typed_minimisation_wait.
Proof.
  unfold typed_minimisation_wait.
  exact (proj2_sig typed_minimisation_wait_package).
Qed.

Local Definition typed_minimisation_value_term
    (predicate recursive : Term) : Term :=
  ''tagged[
    ''decorate[
      star "n"
        (((predicate @@ Ref "n") @@
          (''wait2[
             Val typed_minimisation_wait,
             ''tagged[
               ''decorate[''K1 (Ref "n"), Val zero],
               Val fun_nm],
             Val zero]
           ''*
           ''wait2[
             Val typed_minimisation_wait,
             recursive,
             (Val successor_function @@ Ref "n")]))
          @@ Val zero),
      Val zero],
    Val fun_nm].

Local Definition typed_minimisation_functional_term (predicate : Term) : Term :=
  star "recursive"
    (typed_minimisation_value_term predicate (Ref "recursive")).

Definition typed_minimisation_functional_body_package
    (predicate : Combination) :
  { t : Combination |
    to_tree (typed_minimisation_functional_term (Val predicate)) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition typed_minimisation_functional_body
    (predicate : Combination) : Combination :=
  Eval cbn in proj1_sig
    (typed_minimisation_functional_body_package predicate).

Definition typed_minimisation_functional
    (predicate : Combination) : Combination :=
  lam (typed_minimisation_functional_body predicate) typed_zero_function.

Definition minimisation2 (predicate : Combination) : Combination :=
  'fix[typed_minimisation_functional predicate].

(** Minimisation is likewise higher-order: the predicate is a parameter of
    the object-language operator.  This parametrisation, rather than the
    internal use of a fixfunction, is what belongs to the traditional
    first-order presentation of Turing completeness.  [minimisation2] is
    the specialized Coq family and [minimisation_fn] is its abstraction. *)
Local Definition minimisation_functional_value_term
    (predicate : Term) : Term :=
  prec_lam_term
    (typed_minimisation_functional_term predicate)
    (Val typed_zero_function).

Local Definition minimisation2_term (predicate : Term) : Term :=
  ''tagged[
    Z2 (minimisation_functional_value_term predicate ''C Val tagged_fun),
    Val fun_nm].

Lemma minimisation2_term_alignment : forall predicate,
  to_tree (minimisation2_term (Val predicate)) = minimisation2 predicate.
Proof.
  intros; unfold minimisation2_term, minimisation_functional_value_term,
    prec_lam_term, typed_minimisation_functional_term,
    typed_minimisation_value_term.
  unfold minimisation2, fix_function, typed_minimisation_functional,
    typed_minimisation_functional_body, lam, lam2; reflexivity.
Qed.

Definition minimisation_predicate_witness : Combination :=
  lam ('K1 'tt) zero.

Definition minimisation_package :
  { t : Combination |
    to_tree
      (''tagged[
        ''decorate[
          star "predicate" (minimisation2_term (Ref "predicate")),
          Val minimisation_predicate_witness],
        Val fun_nm]) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition minimisation_fn : Combination :=
  Eval cbn in proj1_sig minimisation_package.

Lemma minimisation_fn_eval : forall predicate,
  minimisation_fn @ predicate ==> minimisation2 predicate.
Proof.
  intros predicate; unfold minimisation_fn, minimisation_package; cbn.
  eapply tagged_eval; eapply wait_eval; eapply eval_appl.
  - apply eval_k.
  - rewrite <- minimisation2_term_alignment.
    unfold minimisation2_term; cbn; evaluate.
Qed.

Local Ltac typed_minimisation_infer :=
  repeat first
    [ match goal with H : infer _ @ ?f ==> Sm ?F |- _ =>
        exact H
      end
    | solve [eapply infer_zero; eauto]
    | solve [eapply infer_successor_function; eauto]
    | solve [eapply typed_zero_function_infer; eauto]
    | apply infer_nat_split
    | eapply infer_lam
    | eapply infer_fork
    | eapply infer_stem
    | eapply infer_leaf
    | eapply infer_I
    | eapply infer_K1
    ].

Local Ltac known_typed_minimisation_type_app_step :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | ?A --> ?B =>
          eapply type_app_abstract;
          apply funty_eliminator_eval
      | nat_split => unfold nat_split
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | 'Nat => eapply type_app_Nat
      | 'Bool =>
          eapply type_app_abstract; apply booleans.bool_eliminator_some
      | 'tagged[?C,?N] =>
          eapply type_app_abstract;
          first
            [ apply funty_eliminator_eval
            | eapply nat_eliminator_eval
            | apply booleans.bool_eliminator_some
            | evaluate ]
      | Fk (Sm (Fk Lf ?C)) (Fk (Sm (Sm Lf)) (Fk Lf ?N)) =>
          eapply type_app_abstract;
          first
            [ apply funty_eliminator_eval
            | eapply nat_eliminator_eval
            | apply booleans.bool_eliminator_some
            | evaluate ]
      | Lf => eapply type_app_leaf_ev
      | Fk Lf ?x => eapply type_app_K_ev
      | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
      | Sm ?x => eapply type_app_stem_ev
      | Fk (Sm (Fk Lf ?g)) ?h =>
          eapply type_app_compose; [solve [reject_name]| | |];
          [ intros E N Heq; inversion Heq | |]
      | Fk (Sm ?g) ?h =>
          new_S;
          [ intros E N Heq; inversion Heq | | |]
      end
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      first
        [ eapply type_app_stem_function
        | eapply type_app_stem_structural; intros E N Heq; inversion Heq ]
  end.

Local Definition typed_minimisation_functional_type_package
    (predicate P : Combination)
    (Hpredicate : infer AI @ predicate ==> Sm P)
    (Hpredicate_app :
      type_app AI @ P @r ('Nat) ==> Sm ('Bool)) :
  { F : Combination |
      infer AI @ typed_minimisation_functional_body predicate ==> Sm F /\
      type_app AI @ F @r ('Nat --> 'Nat) ==>
        Sm ('Nat --> 'Nat) }.
Proof.
  eexists; split.
  - unfold typed_minimisation_functional_body,
      typed_minimisation_functional, typed_minimisation_value_term; cbn.
    all: repeat first
      [ exact Hpredicate_app
      | progress typed_minimisation_infer
      | known_typed_minimisation_type_app_step ].
    all: unfold typed_minimisation_wait; cbn.
    all: repeat first
      [ exact Hpredicate_app
      | progress typed_minimisation_infer
      | known_typed_minimisation_type_app_step ].
  - unfold typed_minimisation_functional_body,
      typed_minimisation_functional, typed_minimisation_value_term; cbn.
    all: repeat first
      [ exact Hpredicate_app
      | progress typed_minimisation_infer
      | known_typed_minimisation_type_app_step ].
    all: unfold typed_minimisation_wait; cbn.
    all: repeat first
      [ exact Hpredicate_app
      | progress typed_minimisation_infer
      | known_typed_minimisation_type_app_step ].
Defined.


Lemma infer_typed_minimisation_functional : forall predicate P
    (Hpredicate : infer AI @ predicate ==> Sm P)
    (Hpredicate_app :
      type_app AI @ P @r ('Nat) ==> Sm ('Bool)),
  infer AI @ typed_minimisation_functional predicate ==>
    Sm (('Nat --> 'Nat) --> ('Nat --> 'Nat)).
Proof.
  intros predicate P Hpredicate Hpredicate_app.
  unfold typed_minimisation_functional; eapply infer_lam.

  - exact (proj1 (proj2_sig
      (typed_minimisation_functional_type_package
        predicate P Hpredicate Hpredicate_app))).
  - eapply typed_zero_function_infer; eauto.
  - exact (proj2 (proj2_sig
      (typed_minimisation_functional_type_package
        predicate P Hpredicate Hpredicate_app))).
Qed.


Lemma infer_minimisation2 : forall predicate P
    (Hpredicate : infer AI @ predicate ==> Sm P)
    (Hpredicate_app :
      type_app AI @ P @r ('Nat) ==> Sm ('Bool)),
  infer AI @ minimisation2 predicate ==> Sm ('Nat --> 'Nat).
Proof.
  intros predicate P Hpredicate Hpredicate_app.
  unfold minimisation2; eapply infer_fix_function.

  - eapply infer_typed_minimisation_functional; eauto.
Qed.

Lemma infer_minimisation_predicate_witness :
  infer AI @ minimisation_predicate_witness ==>
    Sm ('Nat --> 'Bool).
Proof.
  unfold minimisation_predicate_witness; eapply infer_lam.

  - eapply infer_K1; eapply tt_infer; exact AI_supports_booleans.
  - eapply infer_zero; eauto.
  - eapply type_app_K_ev.
Qed.

Local Ltac higher_minimisation_infer :=
  lazymatch goal with
  | |- infer _ @ ?x ==> _ =>
      first
        [ solve [eapply infer_minimisation_predicate_witness]
        | solve [eapply typed_zero_function_infer; eauto]
        | solve [eapply infer_successor_function; eauto]
        | solve [eapply infer_zero; eauto]
        | solve [eapply tt_infer; eauto]
        | eapply infer_fix_function
        | apply infer_nat_split
        | eapply infer_lam
        | eapply infer_fork
        | eapply infer_stem
        | eapply infer_leaf
        | eapply infer_I
        | eapply infer_K1 ]
  end.

Local Ltac higher_minimisation_type_app :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      first
        [ change (type_app AI @ 'Nat @r _ ==> _); eapply type_app_Nat
        | change (type_app AI @ 'Bool @r _ ==> _);
          eapply type_app_abstract; apply bool_eliminator_some
        | change (type_app AI @ (?A --> ?B) @r _ ==> _);
          eapply type_app_abstract; apply funty_eliminator_eval
        | lazymatch T with
          | Lf => eapply type_app_leaf_ev
          | Fk Lf ?x => eapply type_app_K_ev
          | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
          | Sm ?x => eapply type_app_stem_ev
          | Fk (Sm (Fk Lf ?g)) ?f =>
              eapply type_app_compose; [solve [reject_name]| | |];
              [ intros E N Heq; discriminate Heq | |]
          | Fk (Sm ?g) ?f =>
              new_S;
              [ intros E N Heq; discriminate Heq | | |]
          end ]
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      first [eapply type_app_stem_structural; intros E N Heq; discriminate Heq]
  end.

Theorem infer_minimisation_fn :
  infer AI @ minimisation_fn ==>
    Sm (('Nat --> 'Bool) --> ('Nat --> 'Nat)).
Proof.
  eapply infer_lam; [ | |].
  2: apply infer_minimisation_predicate_witness.
  unfold minimisation_fn, minimisation_package; cbn.
  all: repeat first
    [ progress higher_minimisation_infer
    | progress higher_minimisation_type_app ].
  - eapply type_app_stem_function.
    all: repeat first
      [ progress higher_minimisation_infer
      | progress higher_minimisation_type_app ].
    eapply type_app_stem_function.
    all: repeat first
      [ progress higher_minimisation_infer
      | progress higher_minimisation_type_app ].
    + eapply type_app_abstract; apply funty_eliminator_eval.
    + eapply type_app_stem_function; eapply type_app_K_ev.
    + eapply type_app_abstract; apply funty_eliminator_eval.
    + eapply type_app_abstract; apply bool_eliminator_some.
    + cbn.
      repeat first
        [ progress higher_minimisation_infer
        | progress higher_minimisation_type_app ].
      eapply type_app_abstract; apply funty_eliminator_eval.
  - apply type_app_stem_recursive_function.
Qed.

Opaque typed_minimisation_wait.

(* Defining equations.                                                *)
(**********************************************************************)

Lemma minimisation2_true : forall predicate n,
  predicate @ n ==> 'tt ->
  minimisation2 predicate @ n ==> n.
Proof.
  intros predicate n Hpredicate.
  unfold minimisation2, fix_function.
  eapply tagged_eval.
  eapply Z_unfold.
  eapply eval_appl.
  - eapply eval_c; eapply eval_appr.
    + apply tagged_fun_eval.
    + unfold typed_minimisation_functional, lam.
      eapply tagged_eval; eapply wait_eval.
      unfold typed_minimisation_functional_body,
        typed_minimisation_functional_term,
        typed_minimisation_value_term.
      rewrite <- typed_minimisation_wait_compilation; cbn; evaluate.
  - evaluate.
    eapply successor_function_operation; eauto.
Qed.

Lemma minimisation2_false :
  forall predicate n recursive_result,
  predicate @ n ==> 'ff ->
  minimisation2 predicate @ succ n ==> recursive_result ->
  minimisation2 predicate @ n ==> recursive_result.
Proof.
  intros predicate n recursive_result Hpredicate Hrecursive.
  unfold minimisation2, fix_function.
  eapply tagged_eval.
  eapply Z_unfold.
  eapply eval_appl.
  - eapply eval_c; eapply eval_appr.
    + apply tagged_fun_eval.
    + unfold typed_minimisation_functional, lam.
      eapply tagged_eval; eapply wait_eval.
      unfold typed_minimisation_functional_body,
        typed_minimisation_functional_term,
        typed_minimisation_value_term.
      rewrite <- typed_minimisation_wait_compilation; cbn; evaluate.
  - evaluate.
    eapply successor_function_operation; eauto.
Qed.

Lemma minimisation_true : forall predicate n,
  predicate @ n ==> 'tt ->
  minimisation_fn @ predicate @r n ==> n.
Proof.
  intros predicate n Hpredicate; eapply eval_appl.
  - apply minimisation_fn_eval.
  - eapply minimisation2_true; exact Hpredicate.
Qed.

Lemma minimisation_false : forall predicate n recursive_result,
  predicate @ n ==> 'ff ->
  minimisation_fn @ predicate @r succ n ==> recursive_result ->
  minimisation_fn @ predicate @r n ==> recursive_result.
Proof.
  intros predicate n recursive_result Hpredicate Hrecursive.
  invert_eval.
  pose proof
    (eval_deterministic _ _ H3 _ (minimisation_fn_eval predicate)) as Heq.
  subst v1.
  eapply eval_appl.
  - apply minimisation_fn_eval.
  - eapply minimisation2_false; eauto.
Qed.

Opaque zero successor_function.

End TuringExamples.
Set Default Proof Using "Type".


Unset Default Proof Using.
Transparent equal.

(** Structural recursion and its termination argument.

    rtriage_body folds the results of recursive calls on immediate children.
    primtriage_body also supplies the children themselves to its branches:
      R Lf       = a
      R (Sm u)   = b u (R u)
      R (Fk u v) = c u (R u) v (R v).
    Calls are eager, left child before right child. Specialisation may select
    a terminating action and stop; otherwise it uses the recursive body.

    primitive_step says a body terminates on x whenever its proposed recursive
    operation terminates on trees smaller than x. primitive_fixfunction_total
    proves that Z of such a body terminates on every value. Tree size occurs
    only in the proof: no runtime rank or exhaustion case is introduced.

    preserving_step additionally preserves a predicate P on returned values.
    This adapts Analytic's indexed theorem without copying its type syntax.
    P is a specification, not a new type checker or abstract-type constructor.
    The branch premises below must be established independently: an ordinary
    arrow type in the current main line does not imply termination.
    This module adds no inference or type-application rule. *)
From Stdlib Require Import Arith Lia String Wf_nat.
From TreeTyping Require Import tree.
Open Scope string_scope.
Set Default Proof Using "Type".


(** Operational equations expose the source-level meaning of the compiled
    primitive body. These are independent of its termination premises. *)
