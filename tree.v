(** * Tree calculus (paper: Tree Calculus).

    Untyped tree calculus: combinations, big-step evaluation, the derived
    combinators and programming foundations, followed by the concrete
    computation results. *)


(**********************************************************************)
(* Copyright 2026 Barry Jay                                           *)
(*                                                                    *)
(* Permission is hereby granted, free of charge, to any person        *)
(* obtaining a copy of this software and associated documentation     *)
(* files (the "Software"), to deal in the Software without            *)
(* restriction, including without limitation the rights to use, copy, *)
(* modify, merge, publish, distribute, sublicense, and/or sell copies *)
(* of the Software, and to permit persons to whom the Software is     *)
(* furnished to do so, subject to the following conditions:           *)
(*                                                                    *)
(* The above copyright notice and this permission notice shall be     *)
(* included in all copies or substantial portions of the Software.    *)
(*                                                                    *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        *)
(* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       *)
(* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, *)
(* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      *)
(* DEALINGS IN THE SOFTWARE.                                          *)
(**********************************************************************)

(**********************************************************************)
(*                     Combinations and Terms                         *)
(*                              with                                  *)
(*                      Big-Step Semantics                            *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

(** Owner: [Terms]. Untyped combinations, evaluation, and programming
    foundations. *)

From Stdlib Require Import Arith Lia Bool List Nat String.


(** * Overview

    This file develops the calculus of _combinations_ -- finite binary trees
    that serve simultaneously as programs and as the data they act on --
    together with the untyped machinery needed to program with them.

    - _Combinations_ are built from leaves, stems and forks.  Evaluation is
      given by a big-step relation rather than a rewriting system, so that
      evaluation is a partial function and divergent subterms cannot be
      rewritten; applications are evaluated eagerly in both positions.

    - Reasoning about a big-step relation is harder than equational
      reasoning, so we prove that evaluation is _deterministic_ and develop
      syntax-directed tactics and inversion principles for constructing and
      analysing evaluation derivations.

    - _Terms_ add variables and application on top of combinations.  They
      exist to support variable-binding constructions -- lambda-abstraction
      [star] and pattern matching [tcase] -- whose closed results are mapped
      back to combinations by [to_tree].  In principle terms are dispensable:
      one could work directly with the combinations that [to_tree] produces.

    - The development follows a deliberate dependency chain: evaluation
      supports compilation from the intended closed construction fragment of
      [Term]; compilation supports guarded recursion through [Z]; recursion
      supports root-level structural equality and tags; and those in turn
      support pattern programs [extend], [extend2], and [tcase].  Stable
      clients should use the operational lemmas for these programs rather
      than depend on the exact trees produced by compilation. *)


(** * General proof infrastructure

    Small general-purpose tactics used throughout the development. *)

(** Expose the body of a fixpoint and re-fold its recursive occurrences. *)
Ltac refold r := unfold r; fold r.

Ltac auto_t := eauto with TreeHintDb.

(** Invert a hypothesis and dispose of it. *)
Ltac inv_out H := inversion H; clear H; subst.

(** Decompose conjunctions, existentials and disjunctions in the
    hypotheses, split conjunctive goals, and close what it can. *)
Ltac split_all :=
  intros;
  match goal with
  | H : _ /\ _ |- _ => inversion_clear H; split_all
  | H : exists _, _ |- _ => inversion H; clear H; split_all
  | H : _ \/ _ |- _ => inversion H; clear H; split_all
  | _ => try (split; split_all); subst; try contradiction; try lia; auto_t
  end; try congruence.

(** Split disjunctive hypotheses, then try arithmetic. *)
Ltac disjunction_tac :=
  match goal with
  | H : _ \/ _ |- _ => inv_out H; disjunction_tac
  | _ => try lia
  end.

(** simplify "F" =? "N" etc *)
Ltac eqb_tac := cbv [String.eqb Ascii.eqb Bool.eqb].


(** * Combinations

    A combination is a finite binary tree: a leaf [Lf], a stem [Sm t], or a
    fork [Fk t u].  There is no application constructor -- application is
    expressed through evaluation, below -- and no variables, so every
    combination is simultaneously a closed program and a piece of data that
    other programs may inspect. *)

Inductive Combination : Set :=
| Lf : Combination
| Sm : Combination -> Combination
| Fk : Combination -> Combination -> Combination.

Create HintDb TreeHintDb.
Global Hint Constructors Combination : TreeHintDb.

Fixpoint combination_eq_dec
    (x y : Combination) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** ** Notation for the traditional combinators

    The familiar combinators appear as particular trees: [K] is a stem,
    [K u], [S u v] and the composition [g 'C f] are forks, and [I] is
    [S K K]. *)

Notation "'K" := (Sm Lf).
Notation "'K1 x" := (Fk Lf x) (at level 60).
Notation "'S1 x" := (Sm (Sm x)) (at level 60).
Notation "'S2 [ u , v ]" := (Fk (Sm u) v) (at level 0).
Notation "g 'C f" := (Fk (Sm (Fk Lf g)) f) (at level 40).
Notation "'I" := (Fk (Sm (Sm Lf)) (Sm Lf)).
Notation "'KI" := ('K1 'I) (at level 0).

(** ** Notation for intensional combinations

    [triage] performs case analysis on the shape of its argument; it is the
    intensional heart of the calculus. *)

Notation "'triage [ f0 , f1 , f2 ]" := (Fk (Fk f0 f1) f2) (at level 0).
Notation "'onStem1 f" := ('triage [ Lf, f, 'K1 ('K1 Lf) ]) (at level 40).


Fixpoint tree_size t :=
  match t with
  | Sm t1 => S (tree_size t1)
  | Fk t1 t2 => S (tree_size t1 + tree_size t2)
  | _ => 1
  end.

(** * Evaluation

    Expressions and values share the syntax of combinations, but an
    expression is _read_ differently: [Sm v] is the quotation of the value
    [v] (a completed computation), while [Fk e1 e2] is the application of
    [e1] to [e2].  Evaluation is eager in both positions.  An application
    first evaluates its operator and its argument, producing a pair of
    quoted values [Fk (Sm v1) (Sm v2)], and only then dispatches on the
    shape of [v1]:

    - [Lf . v2] builds the stem [Sm v2];
    - [(Sm v1) . v2] builds the fork [Fk v1 v2];
    - [(Fk Lf v1) . v2 = v1]: this is [K v1]; its argument has already
      been evaluated, even though the resulting value is discarded;
    - [(Fk (Sm g) f) . v2 = (g . v2) (f . v2)]: this is [S g f], which
      duplicates the value [v2], not its computation;
    - [(Fk (Fk f0 f1) f2) . v2]: this is [triage [f0, f1, f2]]; continue
      with [f0], [f1 . u] or [(f2 . u1) . u2] according as [v2] is a leaf,
      a stem [Sm u], or a fork [Fk u1 u2]. *)

Inductive eval : Combination -> Combination -> Prop :=
| eval_val : forall v,
    eval (Sm v) v
| eval_appl : forall e11 e12 e2 v1 v,
    eval (Fk e11 e12) v1 ->
    eval (Fk (Sm v1) e2) v ->
    eval (Fk (Fk e11 e12) e2) v
| eval_appr : forall v1 e21 e22 v2 v,
    eval (Fk e21 e22) v2 ->
    eval (Fk (Sm v1) (Sm v2)) v ->
    eval (Fk (Sm v1) (Fk e21 e22)) v
| eval_to_stem : forall v2,
    eval (Fk (Sm Lf) (Sm v2)) (Sm v2)
| eval_to_fork : forall v1 v2,
    eval (Fk (Sm (Sm v1)) (Sm v2)) (Fk v1 v2)
| eval_k : forall v1 v2,
    eval (Fk (Sm (Fk Lf v1)) (Sm v2)) v1
| eval_s : forall g f v2 v,
    eval (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2))) v ->
    eval (Fk (Sm (Fk (Sm g) f)) (Sm v2)) v
| eval_leaf : forall f0 f1 f2,
    eval (Fk (Sm ('triage [f0, f1, f2])) (Sm Lf)) f0
| eval_stem : forall f0 f1 f2 v2 v,
    eval (Fk (Sm f1) (Sm v2)) v ->
    eval (Fk (Sm ('triage [f0, f1, f2])) (Sm (Sm v2))) v
| eval_fork : forall f0 f1 f2 v21 v22 v,
    eval (Fk (Fk (Sm f2) (Sm v21)) (Sm v22)) v ->
    eval (Fk (Sm ('triage [f0, f1, f2])) (Sm (Fk v21 v22))) v.

Global Hint Constructors eval : TreeHintDb.

(** [f @ u] applies the value [f] to the value [u]; [d @r u] applies the
    expression [d] to the value [u].  [e ==> v] is evaluation, and [d ~~> e]
    says that [d] computes whatever [e] computes. *)

Notation "f @ u" := (Fk (Sm f) (Sm u)) (at level 45, left associativity).
Notation "f @r u" := (Fk f (Sm u)) (at level 45, left associativity).
Notation "e ==> v" := (eval e v) (at level 50).
Notation "d ~~> e" := (forall v, e ==> v -> d ==> v) (at level 50).

(** ** Determinism

    Evaluation is a partial function: an expression has at most one value.
    The proof is by induction on the first derivation and case analysis on
    the second; each pair of rules for the same expression is reconciled by
    repeatedly instantiating an induction hypothesis with the corresponding
    premise of the second derivation. *)

Theorem eval_deterministic :
  forall e v, e ==> v -> forall v', e ==> v' -> v = v'.
Proof.
  intros e v Hev; induction Hev; intros v' Hev'; inv_out Hev';
    repeat match goal with
      | IH : forall w, ?e ==> w -> _ = w, H : ?e ==> _ |- _ =>
          apply IH in H; inv_out H
      end; auto.
Qed.

(** Given two evaluations of the same expression, identify their results
    (and discard the goal if they are manifestly distinct). *)
Ltac unify_evals :=
  match goal with
  | Hv1 : ?e ==> ?v1, Hv2 : ?e ==> ?v2 |- _ =>
      assert (v1 = v2) by (eapply eval_deterministic; eauto);
      subst; clear Hv1 Hv2; try discriminate
  end.

(** Invert one evaluation hypothesis as far as its expression shape permits.
    This convenience tactic is retained here for use by downstream files. *)

Ltac invert_eval1 :=
  match goal with
  | H : eval (Sm _) _ |- _ => inv_out H
  | H : eval (Fk (Fk _ _) _) _ |- _ => inv_out H
  | H : eval (Fk (Sm _) (Fk _ _)) _ |- _ => inv_out H
  | H : eval (Fk (Sm Lf) (Sm _)) _ |- _ => inv_out H
  | H : eval (Fk (Sm (Sm _)) (Sm _)) _ |- _ => inv_out H
  | H : eval (Fk (Sm (Fk Lf _)) (Sm _)) _ |- _ => inv_out H
  | H : eval (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ |- _ => inv_out H
  | H : eval (Fk (Sm (Fk (Fk _ _) _)) (Sm _)) _ |- _ => inv_out H
  | H : eval (Fk Lf _) _ |- _ => inv_out H
  | _ => eauto
  end.

(** Repeatedly invert evaluation hypotheses as far as their expression shapes
    permit. *)

Ltac invert_eval :=
  match goal with
  | H : eval (Sm _) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Fk _ _) _) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm _) (Fk _ _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm Lf) (Sm _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm (Sm _)) (Sm _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm (Fk Lf _)) (Sm _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk (Sm (Fk (Fk _ _) _)) (Sm _)) _ |- _ => inv_out H; invert_eval
  | H : eval (Fk Lf _) _ |- _ => inv_out H; invert_eval
  | _ => eauto
  end.


(** The operator of an application may be evaluated first. *)
Lemma eval_op :
  forall e1 w, e1 ==> w ->
  forall e2 v, Fk (Sm w) e2 ==> v -> Fk e1 e2 ==> v.
Proof.
  intros e1 w He; induction He; intros e2' v' Happ;
    try (eapply eval_appl; auto_t).
  exact Happ.
Qed.

(** Once the operator is a value, an argument computation may be performed
    before the value-level application rule fires. *)
Lemma eval_arg_value :
  forall v1 e2 v2, e2 ==> v2 ->
  forall v, v1 @ v2 ==> v -> Fk (Sm v1) e2 ==> v.
Proof. intros v1 e2 v2 He2 v Happ; destruct He2; auto_t. Qed.

Lemma eval_arg_value_inv :
  forall v1 e2 v,
    Fk (Sm v1) e2 ==> v ->
    exists v2,
      e2 ==> v2 /\
      v1 @ v2 ==> v.
Proof.
  intros v1 e2 v H.
  remember (Fk (Sm v1) e2) as e eqn:He.
  induction H; inversion He; subst; repeat eexists; auto_t. 
Qed.

(** Evaluating both positions reduces an application to a pair of values. *)
Lemma eval_pair :
  forall e1 e2 v1 v2 v,
    e1 ==> v1 -> e2 ==> v2 -> v1 @ v2 ==> v -> Fk e1 e2 ==> v.
Proof.
  intros e1 e2 v1 v2 v He1 He2 Happ.
  eapply eval_op; [ exact He1 | ].
  eapply eval_arg_value; eauto.
Qed.

Lemma eval_pair_inv :
  forall e1 e2 v,
    Fk e1 e2 ==> v ->
    exists v1 v2,
      e1 ==> v1 /\
      e2 ==> v2 /\
      v1 @ v2 ==> v.
Proof.
  intros e1 e2 v H.
  remember (Fk e1 e2) as e eqn:He.
  induction H; inversion He; subst; try(repeat eexists; auto_t; fail).
  specialize (eval_arg_value_inv _ _ _ H0); intros; split_all; repeat eexists; auto_t. 
 Qed.

(** ** Evaluation tactics

    [evaluate] builds eager evaluation derivations by syntax-directed proof
    search.  It evaluates the operator spine first, then the argument, and
    finally dispatches on the resulting pair of values.  It is deliberately
    permissive: when no rule applies, [idtac] leaves the current goal
    unchanged.  Thus [evaluate] is an incremental proof-building tactic, not
    a guarantee that evaluation has finished; the enclosing proof must still
    account for every remaining goal. *)

Ltac ev_hyp := first [ eassumption | assumption ].

Ltac evaluate_expr_core recurse head :=
  match goal with
  (* A quotation evaluates to its value. *)
  | |- eval (Sm _) _ =>
      eapply eval_val
  (* Evaluate the operator spine first. *)
  | |- eval (Fk (Fk _ _) _) _ =>
      eapply eval_appl; [ recurse | recurse ]
  (* Then evaluate an application in the argument position. *)
  | |- eval (Fk (Sm _) (Fk _ _)) _ =>
      eapply eval_appr; [ recurse | head ]
  (* A pair of quoted values is ready to dispatch. *)
  | |- eval (Fk (Sm _) (Sm _)) _ =>
      head
  end

with evaluate_head_core recurse :=
  match goal with
  | |- eval (Fk (Sm Lf) (Sm _)) _ =>
      eapply eval_to_stem
  | |- eval (Fk (Sm (Sm _)) (Sm _)) _ =>
      eapply eval_to_fork
  | |- eval (Fk (Sm (Fk Lf _)) (Sm _)) _ =>
      eapply eval_k
  | |- eval (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ =>
      eapply eval_s; recurse
  | |- eval (Fk (Sm (Fk (Fk _ _) _)) (Sm Lf)) _ =>
      eapply eval_leaf
  | |- eval (Fk (Sm (Fk (Fk _ _) _)) (Sm (Sm _))) _ =>
      eapply eval_stem; recurse
  | |- eval (Fk (Sm (Fk (Fk _ _) _)) (Sm (Fk _ _))) _ =>
      eapply eval_fork; recurse
  end.

Ltac evaluate_expr :=
  first
    [ ev_hyp
    | evaluate_expr_core evaluate_expr evaluate_head
    | match goal with
      (* Use a known value for an argument whose syntax is still abstract. *)
      | H : ?e2 ==> ?v2 |- eval (Fk (Sm ?v1) ?e2) _ =>
          lazymatch e2 with
          | Sm _ => fail
          | _ => eapply eval_arg_value; [ exact H | evaluate_head ]
          end
      end
    (* Allow partial solutions. *)
    | idtac ]

with evaluate_head :=
  first [ ev_hyp | evaluate_head_core evaluate_expr | idtac ].

Ltac evaluate := evaluate_expr.


(** [evaluate2] is the assumption-free variant.  It exposes the computation
    forced by syntax without allowing a convenient hypothesis to choose an
    unintended intermediate value; callers discharge the residual semantic
    premises explicitly. *)
Ltac evaluate_expr2 :=
  first
    [ evaluate_expr_core evaluate_expr2 evaluate_head2
    (* Allow partial solutions. *)
    | idtac ]

with evaluate_head2 :=
  first [ evaluate_head_core evaluate_expr2 | idtac ].

Ltac evaluate2 := evaluate_expr2.

(** ** Triage inversion

    Inversion principles for triage on values and on argument
    expressions. *)

(** * Basic programs and shape analysis

    The traditional combinators behave as expected, and triage performs
    case analysis on the shape of its argument. *)

Lemma I_eval : forall x, 'I @ x ==> x.
Proof. intros; evaluate. Qed.

Global Hint Resolve I_eval : TreeHintDb.

Lemma eval_c : forall g f u, (g 'C f) @ u ~~> Fk (Sm g) (f @ u).
Proof. intros; invert_eval; evaluate. Qed. 


(** ** Shape dispatchers

    Shared programs that recognize stems and leaves. *)

Notation "'isLeaf" := ('triage ['K, 'K1 'KI, 'K1 ('K1 'KI)]).


(** * Terms and abstraction

    Terms extend combinations with variables and application.  The intended
    compilable fragment is made of closed terms whose applications denote
    tree constructions; [to_tree] deliberately maps variables and malformed
    or non-construction applications to the fallback [Lf].  Consequently a
    bare equation about [to_tree] is rarely a robust public specification:
    the operational evaluation lemmas below are the stable API. *)

Open Scope string_scope.

Inductive Term : Set :=
| Ref : string -> Term
| Val : Combination -> Term
| App : Term -> Term -> Term.

Notation "x @@ y" := (App x y) (at level 65, left associativity).

(** Second-level constructors build [Term] syntax; they do not construct
    executable [Combination] values.  Compilation by [to_tree], [star], or
    [rawstar] is what eventually produces combinations.  The suffix [2]
    means "second-level Term syntax", not arity (unlike the historical names
    [K1] and [S2]). *)

(** Term-level siblings of the combination notations: a [''x] notation
    builds second-level syntax for the construction that ['x] denotes as a
    closed tree value after compilation. *)

Notation "''K" := (Val 'K).
Notation "''K1 x" := (''K @@ x) (at level 60).
Notation "''S2 [ u , v ]" := (Val Lf @@ (Val Lf @@ u) @@ v) (at level 0).
Notation "g ''C f" := (''S2 [ ''K1 g, f]) (at level 40).
Notation "''I" := (Val Lf @@ (Val Lf @@ ''K) @@ ''K) (at level 0)
(* not to be confused with a value,
   as this creates checks on values in star, below *) . 
Notation "''triage [ f0 , f1 , f2 ]" := (Val Lf @@ (Val Lf @@ f0 @@ f1) @@ f2) (at level 0).

Notation "''onStem1 f" := (Val Lf @@ (''K1 f) @@ (''K1 (''K1 (Val Lf)))) (at level 40).
Notation "''onFork1 f" := (Val (Sm ('K1 ('K1 Lf))) @@ f) (at level 10).
Notation "''onFork21 [ f ]" := (''triage [ Val ('KI), ''K1 (Val ('KI)), f]).


(** Read a construction back as a tree: an application whose operator is a
    leaf builds a stem, one whose operator is a stem builds a fork.  On
    variables the result is the meaningless default [Lf], and on
    applications that are not constructions it is likewise junk; [to_tree]
    is only meaningful on closed construction terms, such as those built by
    [star] and [tcase] below.

    Warning: [Lf] is both a genuine tree and the fallback result, so an [Lf]
    result alone does not show that the input was a valid construction. *)

Fixpoint to_tree t :=
  match t with
  | Val c => c
 (* | App (App (Val Lf) (App (Val Lf) (App (Val 'K) t1))) (Val 'I) =>
      to_tree t1 (* composition-with-identity optimisation *)
*) 
  | t1 @@ t2 =>
      match to_tree t1, to_tree t2 with
      | Lf, c2 => Sm c2
      | Sm c1, c2 => Fk c1 c2
      | _, _ => Lf
      end
  | _ => Lf
  end.

(** ** Lambda-abstraction

    [rawstar] is the uniform S/K compiler: it treats quoted combinations
    opaquely and is required when a parameter, module field, or interface
    value crosses an abstraction boundary.  [star] is the optimising compiler
    for deliberately concrete quotations; it propagates known construction
    shapes and may change the exact compiled tree. 
 *)

Fixpoint star x M :=
  match M with
  | Ref y => if String.eqb x y then ''I else ''K1 (Ref y)
  | Val c => ''K1 (Val c)
  | App t1 t2 =>
      match star x t1 with
      | ''K1 t3 =>
          match star x t2 with
          | ''K1 t4 => ''K1 (App t3 t4)
          | ''I  => t3 
          | t4 => ''S2 [ ''K1 t3, t4]
          end
      | N1 => ''S2 [ N1, star x t2]
      end
  end.

Notation "\" := star.

(** Combinations that build a fork (respectively, a triage, a composition)
    from the results of applying their components to a shared argument;
    these are the shapes that [star]-abstraction produces. *)

Definition star_fork f g := 'S2 [ 'S2 ['K1 Lf, f], g].
Definition star_triage f0 f1 f2 := star_fork (star_fork f0 f1) f2.

Lemma star_triage_eval :
  forall f0 f1 f2 x f0x f1x f2x,
    f0 @ x ==> f0x -> f1 @ x ==> f1x -> f2 @ x ==> f2x ->
    star_triage f0 f1 f2 @ x ==> 'triage [ f0x, f1x, f2x].
Proof. intros; cbv; evaluate. Qed.

(** * Strict waiting

    [wait [M, N]] packages the application of [M] to [N] as a _value_ that
    does nothing until one further argument arrives; [wait2 [M, N, x]] and
    [wait3 [M, N, x, y]] likewise fire on a single further argument, having
    stored one or two more arguments for [M] alongside [N].  Waiting stops
    runaway evaluation, so that recursive programs can be values. *)

Notation "'wait [ M , N ]" :=
  ('S2 [ 'S2 [ 'K1 M, 'K1 N], 'I]) (at level 0).
Notation "''wait [ M , N ]" :=
  (''S2 [ ''S2 [ ''K1 M, ''K1 N], ''I]) (at level 0).
Notation "'wait2 [ M , N , x ]" :=
  ('S2 [ 'S2 [ 'S2 [ 'K1 M, 'K1 N], 'K1 x], 'I]) (at level 0).
Notation "''wait2 [ M , N , x ]" :=
  (''S2 [ ''S2 [ ''S2 [ ''K1 M, ''K1 N], ''K1 x], ''I]) (at level 0).
Notation "'wait3 [ M , N , x , y ]" :=
  ('S2 ['S2 [ 'S2 [ 'S2 [ 'K1 M, 'K1 N], 'K1 x], 'K1 y], 'I]) (at level 0).

Lemma wait_eval : forall M N P v, M @ N @r P ==> v -> 'wait [ M, N] @ P ==> v.
Proof. intros M N P v Hv; invert_eval; cbv; evaluate; eapply eval_arg_value; evaluate. Qed.

Lemma wait_eval_inv :
  forall M N P R,
    'wait [M, N] @ P ==> R ->
    M @ N @r P ==> R.
Proof.
  intros M N P R H.
  invert_eval.
  eapply eval_appl; eauto.
Qed.

Lemma wait2_eval : forall M N x y v, M @ N @r x @r y ==> v -> 'wait2 [ M, N, x] @ y ==> v.
Proof. intros M N x y v Hv; invert_eval; cbv; evaluate; eapply eval_arg_value; evaluate. Qed.

Lemma wait2_eval_inv :
  forall M N x y v,
    'wait2 [M, N, x] @ y ==> v ->
    M @ N @r x @r y ==> v.
Proof.
  intros M N x y v H; invert_eval.
  eapply eval_appl; eauto.
  eapply eval_appl; eauto.
Qed.

Lemma wait_decide : forall X,
  (exists M N, X = 'wait[M,N]) \/
  (forall M N, X <> 'wait[M,N]).
Proof.
  intro X.
  destruct X as [| x | l r];
    try (right; intros M N H; discriminate H).
  destruct l as [| a | l1 l2];
    try (right; intros M N H; discriminate H).
  destruct a as [| a | b d];
    try (right; intros M N H; discriminate H).
  destruct b as [| b | b1 b2];
    try (right; intros M N H; discriminate H).
  destruct b as [| b | c M];
    try (right; intros M0 N H; discriminate H).
  destruct c as [| c | c1 c2];
    try (right; intros M0 N H; discriminate H).
  destruct d as [| d | d1 N];
    try (right; intros M0 N0 H; discriminate H).
  destruct d1 as [| d1 | d11 d12];
    try (right; intros M0 N0 H; discriminate H).
  destruct (combination_eq_dec r 'I) as [-> | Hneq].
  - left; exists M, N; reflexivity.
  - right; intros M0 N0 Heq; injection Heq; intros; contradiction.
Qed.


(** * Strict binary success

    [success2] is independent of typing: it evaluates two option-shaped
    inputs strictly, applies [f] to their payloads when both are stems, and
    returns a bare leaf when either input is a leaf. *)

 
(** * Strict fixfunctions

    Recursion is obtained from self-application, guarded by waiting so that
    every stage is a value.  [dup_z] copies the generator [f 'C bz]; [Z f], the
    fixfunction of [f], is a value satisfying the unfolding law
    [Z f x = f (Z f) x] operationally ([Z_unfold], with converse
    [Z_unfold_inv]).  The generator is [f] after [bz], which delays the
    copying again, so [Z] holds one generator and adds a constant to [f]. *)

Definition dup_z := 'S2['I,'I].
Definition bz := Eval cbv in to_tree (\ "w" (''wait [ Val dup_z, Ref "w"])).

Definition Z f := 'wait [ dup_z, f 'C bz].

Lemma dup_z_eval : forall w v, w @ w ==> v -> dup_z @ w ==> v.
Proof.
  intros w v H; cbv [dup_z]; apply eval_s.
  eapply eval_appl; [apply I_eval|].
  eapply eval_appr; [apply I_eval|exact H].
Qed.

Lemma bz_eval : forall w, bz @ w ==> 'wait [dup_z, w].
Proof. intros; cbv [bz dup_z]; evaluate. Qed.

Lemma Z_unfold : forall f x v, f @ (Z f) @r x ==> v -> Z f @ x ==> v.
Proof.
  intros f x v Hv.
  destruct (eval_pair_inv _ _ _ Hv) as [a [c [Ha [Hc Hw]]]]; inv_out Hc.
  apply wait_eval; eapply eval_appl; [|exact Hw].
  apply dup_z_eval; apply eval_s.
  eapply eval_appl; [apply eval_k|].
  eapply eval_appr; [apply bz_eval|exact Ha].
Qed.

Lemma dup_z_inv : forall w v, dup_z @ w ==> v -> w @ w ==> v.
Proof.
  intros w v H; cbv [dup_z] in H; inv_out H.
  match goal with H5 : eval (Fk (Fk _ _) _) _ |- _ =>
    destruct (eval_pair_inv _ _ _ H5) as [a [c [Ha [Hc Hw]]]] end.
  pose proof (eval_deterministic _ _ Ha _ (I_eval w)) as ->.
  pose proof (eval_deterministic _ _ Hc _ (I_eval w)) as ->; exact Hw.
Qed.

Lemma Z_unfold_inv : forall f x v, Z f @ x ==> v -> f @ (Z f) @r x ==> v.
Proof.
  intros f x v Hv; apply wait_eval_inv in Hv.
  destruct (eval_pair_inv _ _ _ Hv) as [a [c [Ha [Hc Hw]]]]; inv_out Hc.
  apply dup_z_inv in Ha; inv_out Ha.
  match goal with H4 : eval (Fk (Fk _ _) _) _ |- _ =>
    destruct (eval_pair_inv _ _ _ H4) as [g [d [Hg [Hd Hb]]]] end.
  assert (Hk : ('K1 f) @ (f 'C bz) ==> f) by apply eval_k.
  pose proof (eval_deterministic _ _ Hg _ Hk) as ->.
  pose proof (eval_deterministic _ _ Hd _ (bz_eval (f 'C bz))) as ->.
  eapply eval_appl; [exact Hb|exact Hw].
Qed.


(** * Booleans

    Conditionals need no new machinery: ['K] serves as true and ['KI] as
    false, so that [b @ x @r y] is "if b then x else y".  [conjunction]
    is conjunction of such booleans; it is used by [equal_fork] below. *)

Definition conjunction :=
  Eval cbv in to_tree (\ "b1" (\ "b2" (Ref "b1" @@ Ref "b2" @@ (Val ('KI))))).


(** * Structural equality

    [equal] decides structural equality of combinations, returning the
    boolean ['K] (true) or ['KI] (false).  It is a fixfunction whose body
    performs triage on the first argument: leaves are compared with
    [isLeaf]; stems are compared componentwise; forks compare both
    components and combine the answers with [conjunction].  Equality lives
    here because tags and pattern compilation require this root-level
    intensional service; family-specific equality belongs downstream. *)

Definition equal_leaf := 'K1 'isLeaf.
Definition equal_stem :=
  'S1 ('K1 ('S2 [ 'S2 [ 'K1 Lf, Sm ('KI)] , 'K1 ('K1 ('K1 ('KI)))])).
Definition equal_fork :=
  Eval cbv in
    to_tree (\ "e" (\ "x1" (\ "y1"
      (''onFork21 [''S2 [ ''S2 [ Ref "e" @@ Ref "x1", ''K1 (Ref "e" @@ Ref "y1")],
                          ''K1 (''K1 (Val ('KI)))]])))).

Definition equal_body := star_triage equal_leaf equal_stem equal_fork.
Definition equal := Z equal_body.

(** Unfolding [equal] one step on each argument shape. *)

Lemma equal_eval_leaf : equal @ Lf ==> 'isLeaf.
Proof. eapply Z_unfold; cbv; evaluate; auto_t. Qed.

Lemma equal_eval_stem :
  forall u vu,
    equal @ u ==> vu ->
    equal @ (Sm u) ==> 'triage [ 'KI, vu, 'K1 ('K1 ('KI)) ].
Proof.
  intros u vu Hu; eapply Z_unfold; eapply eval_appl.
  eapply star_triage_eval. eapply eval_k. apply eval_to_fork; evaluate.
  unfold equal_fork; evaluate. evaluate.
Qed.


(** The value that [equal] computes when applied to a single argument [p]:
    a program that tests its own argument for equality with [p].  The stem
    case nests the tester for the component; the fork case records,
    verbatim, the residual combination that [equal] builds after consuming
    [Fk p1 p2] -- a program that runs the testers for [p1] and [p2] on the
    components of its argument and conjoins the answers.

    [equal1] is a Gallina function used in the metaproof to characterize that
    residual core program.  It is not the equality analyser itself: the
    object-language program [equal] performs the analysis. *)

Fixpoint equal1 p :=
  match p with
  | Lf => 'isLeaf
  | Sm p1 => 'triage [('KI), equal1 p1, 'K1 ('K1 ('KI))]
  | Fk p1 p2 =>
      'triage ['KI, 'K1 'KI,
        'S2 [ 'S2 [ equal1 p1, 'K1 equal1 p2], 'K1 ('K1 'KI)]]
  end.

Lemma equal_eval : forall p, equal @ p ==> equal1 p.
Proof.
  induction p as [ | p IH | p1 IH1 p2 IH2 ]; simpl.
  - apply equal_eval_leaf.
  - apply equal_eval_stem, IH.
  - eapply Z_unfold. unfold equal_body at 1; evaluate.
    eapply star_triage_eval. eapply eval_k. eapply eval_to_fork; evaluate.
    eapply eval_s; evaluate. evaluate.
Qed.

(** [equal] answers ['K] on equal arguments... *)

Lemma equal1_eq : forall p, equal1 p @ p ==> 'K.
Proof.
  induction p as [ | p IH | p1 IH1 p2 IH2 ].
  - cbv; evaluate.
  - unfold equal1; evaluate.
  - refold equal1; eapply eval_fork. evaluate. 
Qed.

Lemma equal_eq : forall p, equal @ p @r p ==> 'K.
Proof. intros; evaluate; [ eapply equal_eval | eapply equal1_eq ]. Qed.

(** ... and ['KI] on distinct arguments. *)

Lemma equal1_neq : forall p q, p <> q -> equal1 p @ q ==> 'KI.
Proof.
  induction p as [ | p IH | p1 IH1 p2 IH2 ]; intros q Hne.
  - cbv; evaluate; destruct q; try (evaluate; fail); congruence.
  - refold equal1; destruct q; evaluate; eapply IH; congruence.
  - refold equal1; destruct q as [ | q | q1 q2 ]; try (evaluate; fail).
    eapply eval_fork.
    destruct (combination_eq_dec p1 q1) as [->|Hn1].
    + assert (Hn2 : p2 <> q2) by congruence.
      pose proof (equal1_eq q1) as H1; pose proof (IH2 q2 Hn2) as H2.
      eapply eval_appl; [apply eval_s; eapply eval_appl; [apply eval_s;
        eapply eval_appl; [exact H1|]|]|]; evaluate.
    + pose proof (IH1 q1 Hn1) as H1.
      eapply eval_appl; [apply eval_s; eapply eval_appl; [apply eval_s;
        eapply eval_appl; [exact H1|]|]|]; evaluate.
Qed.

Lemma equal_neq : forall p q, p <> q -> equal @ p @r q ==> 'KI.
Proof. intros; evaluate; [ eapply equal_eval | eapply equal1_neq; auto ]. Qed.

(** Since evaluation is deterministic and equality of combinations is
    decidable, the two directions above characterise [equal] completely. *)

Lemma equal_spec :
  forall u1 u2 v,
    equal @ u1 @r u2 ==> v ->
    (v = 'K /\ u1 = u2) \/ (v = 'KI /\ u1 <> u2).
Proof.
  intros u1 u2 v Hv.
  assert (D : u1 = u2 \/ u1 <> u2) by (repeat decide equality).
  destruct D as [ -> | D ].
  - assert (HK : equal @ u2 @r u2 ==> 'K) by apply equal_eq.
    unify_evals; auto.
  - assert (HKI : equal @ u1 @r u2 ==> 'KI) by (apply equal_neq; exact D).
    unify_evals; auto.
Qed.


(** * Pattern programs

    [extend ps r] extends a partial match [ps] with a default [r]: cases
    signal success by returning a stem [Sm result] and failure by returning
    a leaf, and the extension either unwraps the result or falls through to
    the default.  [none n] is the always-failing [n]-argument function. *)


Definition none n := Nat.iter n (Fk Lf) Lf.

Local Definition extend_program_package :
  { t : Combination |
    to_tree
      (\ "partial"
         (\ "fallback"
            (''S2 [
               ''triage [Ref "fallback", ''K, Val (none 3)]
                 ''C Ref "partial",
               ''I]))) = t }.
Proof.
  eexists.
  unfold star at 2; eqb_tac.
  unfold star at 1; eqb_tac.
  unfold to_tree.
  reflexivity.
Defined.

Definition extend_program : Combination :=
  Eval cbn in proj1_sig extend_program_package.

(** A partial match extended by a default: [triage[r, K, none 3]] reads the
    outcome of the match, and the input goes to the default on a leaf. *)
Definition extend partial fallback :=
  'S2[('triage[fallback,'K,none 3]) 'C partial, 'I].

Lemma extend_some : forall ps r u v, ps @ u ==> Sm v -> extend ps r @ u ==> v.
Proof. intros; unfold extend; cbv [none Nat.iter]; evaluate. Qed.

Lemma extend_none_value :
  forall partial fallback input result,
    partial @ input ==> Lf ->
    fallback @ input ==> result ->
    extend partial fallback @ input ==> result.
Proof. intros; unfold extend; cbv [none Nat.iter]; evaluate. Qed.

Lemma extend_none :
  forall ps r u v w,
    ps @ u ==> Lf -> r @ u @r v ==> w -> extend ps r @ u @r v ==> w.
Proof.
  intros ps r u v w Hps Hr; invert_eval; eapply eval_appl; [|eauto].
  apply extend_none_value; assumption.
Qed.

Lemma extend_inv :
  forall partial fallback input result,
    extend partial fallback @ input ==> result ->
    (exists value, partial @ input ==> Sm value /\ result = value) \/
    (partial @ input ==> Lf /\ fallback @ input ==> result) \/
    (exists left right,
       partial @ input ==> Fk left right /\ result = Lf).
Proof.
  intros partial fallback input result Hextend.
  unfold extend in Hextend; cbv [none Nat.iter] in Hextend.
  invert_eval; eauto 10.
Qed.

(** [extend_w] is the same choice held as one program, for a default
    known only at run time. *)
Definition extend_w partial fallback :=
  'wait2 [extend_program, partial, fallback].

Lemma extend_w_inv :
  forall partial fallback input result,
    extend_w partial fallback @ input ==> result ->
    (exists value, partial @ input ==> Sm value /\ result = value) \/
    (partial @ input ==> Lf /\ fallback @ input ==> result) \/
    (exists left right,
       partial @ input ==> Fk left right /\ result = Lf).
Proof.
  intros partial fallback input result Hextend.
  unfold extend_w in Hextend.
  eapply wait2_eval_inv in Hextend.
  unfold extend_program in Hextend; cbn in Hextend.
  invert_eval; eauto 10.
Qed.

(** [extend2] is the term-level compiler image used by patterns. *)
Definition extend2 ps r :=
  ''S2 [ ''triage [r, ''K, Val (none 3)] ''C ps, ''I].
Definition extend_w2 ps r :=
  ''wait2 [Val extend_program, ps, r].

(** [tcase p s] compiles the single match case [p => s]: a function that,
    applied to an argument, returns [Sm result] if the argument matches the
    pattern [p] (binding its variables in [s]) and [Lf] otherwise.
    Patterns are variables, values, and constructions [Val Lf @@ p]
    (matching stems) and [Val Lf @@ p1 @@ p2] or [Val (Sm c) @@ p2] (matching
    forks); anything else fails. *)

Definition closed_test (c : Combination) : Combination :=
  if Nat.leb (tree_size c) 16 then equal1 c else 'wait [equal, c].

Lemma closed_test_eq : forall c, closed_test c @ c ==> 'K.
Proof.
  intros c; unfold closed_test; destruct (Nat.leb (tree_size c) 16);
    [apply equal1_eq|apply wait_eval; apply equal_eq].
Qed.
Lemma closed_test_neq : forall c q, c <> q -> closed_test c @ q ==> 'KI.
Proof.
  intros c q H; unfold closed_test; destruct (Nat.leb (tree_size c) 16);
    [apply equal1_neq; exact H|apply wait_eval; apply equal_neq; exact H].
Qed.

Fixpoint tcase_k (k : nat) p s :=
  match p with
  | Ref x => \ x s
  | Val c => ''S2 [ ''S2 [ Val (closed_test c) , ''K1 s ], Val ('K1 (none k)) ]
  | Val Lf @@ p2 => ''triage [ Val (none k), tcase_k k p2 s, Val ('K1 ('K1 (none k))) ]
  | Val (Sm c) @@ p2 =>
      ''triage [ Val (none k), Val ('K1 (none k)),
        ''S2 [ ''S2 [ Val (closed_test c), ''K1 (tcase_k k p2 s)], Val ('K1 (none (S k)))] ]
  | Val Lf @@ p1 @@ p2 =>
      ''triage [ Val (none k), Val ('K1 (none k)), tcase_k (S k) p1 (tcase_k k p2 s) ]
  | _ => Val ('K1 (none k))
  end.
Definition tcase p s := tcase_k 0 p (Val Lf @@ s).


(** Matching a value pattern succeeds exactly on that value... *)

Lemma tcase_eq : forall p s, to_tree (tcase (Val p) s) @ p ==> Sm (to_tree s).
Proof.
  intros p s; pose proof (closed_test_eq p) as H; unfold tcase;
    cbn [tcase_k to_tree none Nat.iter]; evaluate.
Qed.

Lemma tcase_neq :
  forall p q s, p <> q -> to_tree (tcase (Val p) s) @ q ==> Lf.
Proof.
  intros p q s Hne; pose proof (closed_test_neq p q Hne) as H; unfold tcase;
    cbn [tcase_k to_tree none Nat.iter]; evaluate.
Qed.

(** ... and compound patterns match componentwise. *)


Lemma extend2_val : forall ps r,
  to_tree (extend2 ps (Val r)) = extend (to_tree ps) r.
Proof. reflexivity. Qed.

Lemma extend2_some :
  forall ps r u v,
    to_tree ps @ u ==> Sm v ->
    to_tree (extend2 ps (Val r)) @ u ==> v.
Proof. intros; rewrite extend2_val; apply extend_some; assumption. Qed.

Lemma extend2_none :
  forall ps r u v w,
    to_tree ps @ u ==> Lf ->
    r @ u @r v ==> w ->
    to_tree (extend2 ps (Val r)) @ u @r v ==> w.
Proof. intros; rewrite extend2_val; apply extend_none; assumption. Qed.

(** * Generic pairs and projections

    These are value programs and their operational laws.  Their typing
    belongs to the later Types layer. *)

Notation "'fst" := (Fk (Sm 'I) (Fk Lf (Sm Lf))).
Notation "'snd" := (Fk (Sm 'I) (Fk Lf (Fk Lf 'I))).

Local Definition pair_term :=
  Eval cbv in (\"x" (\"y" (\"f" (Ref "f" @@ Ref "x" @@ Ref "y")))).
Definition pair_comb := Eval cbv in (to_tree pair_term).
Notation "'pair" := pair_comb.

(** Canonical Church-pair values at the Combination and Term-syntax levels. *)
Notation "u '* v" :=
  ('S2['S2['I, 'K1 u], 'K1 v]) (at level 55).
Notation "u ''* v" :=
  (''S2[''S2[''I, ''K1 u], ''K1 v]) (at level 55).

(** The same laws for the canonical pair value [u '* v] (tree.tex, Pairs). *)
Lemma pair_apply : forall u v f r,
  f @ u @r v ==> r -> (u '* v) @ f ==> r.
Proof. intros; inv_out H; evaluate; eauto. Qed.

Lemma fst_pair : forall u v, 'fst @ (u '* v) ==> u.
Proof. intros; evaluate. Qed.

Lemma snd_pair : forall u v, 'snd @ (u '* v) ==> v.
Proof. intros; evaluate. Qed.


Notation "u '* v" :=
  ('S2['S2['I, 'K1 u], 'K1 v]) (at level 55).

(* Z in tcase *) 
Opaque dup_z bz.

 Ltac eqtac :=
    unfold extend_program in *; 
    match goal with
    | H : equal @ ?M ==> ?eM |- _ =>
        assert(eM = equal1 M) by
        (eapply eval_deterministic; eauto; eapply equal_eval; eauto);
        subst; clear H; invert_eval
    | H : equal1 ?M @ ?N ==> ?eMN |- _ =>
        assert(M = N \/ M <> N) by decide equality;
        split_all;
        [ assert(eMN = 'K) by
          (eapply eval_deterministic; eauto; eapply equal1_eq; eauto) |
          assert(eMN = 'KI) by
          (eapply eval_deterministic; eauto; eapply equal1_neq; eauto)];
        subst; clear H; invert_eval
    | _ => idtac
    end.


Definition Z2 f := ''wait [Val dup_z, ''S2 [ ''K1 f, Val bz]].


(** [get_Z] reads the functional, rebuilds the fixed point and compares,
    so that [bz] is not compiled into a specialised test. *)
Definition read_Z : Combination :=
  'triage[Lf, 'K1 Lf, 'K1 'I] 'C ('triage[Lf, 'I, 'K1 ('K1 Lf)] 'C
  ('triage[Lf, 'K1 Lf, 'K] 'C
  ('triage[Lf, 'K1 Lf, 'K1 'I] 'C ('triage[Lf, 'K1 Lf, 'K1 'I] 'C
    ('triage[Lf, 'I, 'K1 ('K1 Lf)] 'C 'triage[Lf, 'K1 Lf, 'K]))))) .
Definition read_Z_fn t :=
  match t with
  | Fk (Sm (Fk _ (Fk _ (Fk (Sm (Fk _ f)) _)))) _ => f
  | _ => Lf
  end.
Lemma read_Z_eval : forall t, read_Z @ t ==> read_Z_fn t.
Proof.
  intros [|t|[|a|a b] c]; try (cbv; evaluate; fail).
  destruct a as [|a|a b]; try (cbv; evaluate; fail).
  destruct b as [|b|b c']; try (cbv; evaluate; fail).
  destruct c' as [|d|d e]; try (cbv; evaluate; fail).
  destruct d as [|d|d e']; try (cbv; evaluate; fail).
  destruct d as [|d|d e'']; cbv; evaluate.
Qed.

Definition get_Z := Eval cbn in to_tree (star "u"
  (star "f" (Val equal @@ Ref "u" @@ Z2 (Ref "f") @@ (Val Lf @@ Ref "f") @@ Val Lf)
    @@ (Val read_Z @@ Ref "u"))).

Lemma get_Z_eval : forall u, exists v, get_Z @ u ==> v /\
  ((u = Z (read_Z_fn u) /\ v = Sm (read_Z_fn u)) \/ (u <> Z (read_Z_fn u) /\ v = Lf)).
Proof.
  intros u; pose proof (read_Z_eval u) as Hr; pose proof (equal_eval u) as He.
  destruct (combination_eq_dec u (Z (read_Z_fn u))) as [E|E].
  - assert (Hk2 : forall a b, a = b -> equal1 a @ b ==> 'K)
      by (intros a b ->; apply equal1_eq).
    pose proof (Hk2 _ _ E) as Hk; clear Hk2.
    exists (Sm (read_Z_fn u)); split; [|left; auto].
    unfold Z in Hk; unfold get_Z; evaluate.
  - pose proof (equal1_neq u _ E) as Hk; exists Lf; split; [|right; auto].
    unfold Z in Hk; unfold get_Z; evaluate.
Qed.

Lemma read_Z_Z : forall f, read_Z_fn (Z f) = f.
Proof. reflexivity. Qed.

Lemma get_Z_some: forall f, get_Z @ (Z f) ==> Sm f.
Proof.
  intros f; destruct (get_Z_eval (Z f)) as [v [H [[_ ->]|[E _]]]]; rewrite read_Z_Z in *.
  - exact H.
  - contradiction E; reflexivity.
Qed.

Lemma get_Z_none: forall u, (forall f, u <> Z f) -> get_Z @ u ==> Lf.
Proof.
  intros u H; destruct (get_Z_eval u) as [v [Hv [[E _]|[_ ->]]]].
  - contradiction (H _ E).
  - exact Hv.
Qed.

Lemma get_Z_inv: forall g f, get_Z @ g ==> Sm f -> g = Z f.
Proof.
  intros g f H; destruct (get_Z_eval g) as [v [Hv [[E ->]|[_ ->]]]].
  - pose proof (eval_deterministic _ _ H _ Hv) as HE; inversion HE; subst f; exact E.
  - pose proof (eval_deterministic _ _ H _ Hv); discriminate.
Qed.

(** Expose the two fields of an arbitrary composition. *)
Definition get_composition :=
  Eval cbv -[equal1] in
    to_tree
      (tcase
         (Ref "D" ''C Ref "R")
         (Val Lf @@ Ref "D" @@ Ref "R")).

Lemma get_composition_some : forall D R,
  get_composition @ (D 'C R) ==> Sm (Fk D R).
Proof.
  intros D R; unfold get_composition.
  repeat (eapply equal1_eq || evaluate).
Qed.

Lemma get_composition_inv : forall X D R,
  get_composition @ X ==> Sm (Fk D R) ->
  X = D 'C R.
Proof.
  intros X D R H.
  unfold get_composition in H.
  inv_out H; invert_eval.
Qed.

(** * Tags

    Tagging attaches a label, comment or guidance [t] to a program [f]
    without disturbing its behaviour.  Recognition is kept here beside
    the common composition recognizer on which it depends. *)

Notation "'tagged [ f , t ]" := ('S2 [ 'K1 f, 'S2 [ 'K , 'K1 t]]).
Notation "''tagged [ f , t ]" := (''S2 [ ''K1 f, ''S2 [ ''K , ''K1 t]]).

(** ** Labels built at run time

    The label [label[n] = S2[K, K1 n]] is the identity carrying the name
    [n]; a tag is [tagged[f,n] = f o label[n]].  So that no typing program
    need contain a label literally, labels are built at run time: the
    program [make_label] maps [n] to [label[n]], and [tagger[n]] maps [x]
    to [tagged[x,n]], recomputing the label on each call.  Neither
    contains a label.  They are notations so that [evaluate]
    computes through them. *)
Notation "'label [ n ]" := ('S2 [ 'K , 'K1 n]) (at level 0).
Notation "'make_label" := ('S2 [ 'K1 (Sm (Sm 'K)), 'K]).
Notation "'tag_head" := ('S2 [ 'K1 Lf, 'S2 [ 'K1 Lf, 'K]]).
Notation "'tagger [ n ]" := ('S2 [ 'tag_head, 'S2 [ 'K1 'make_label, 'K1 n]]) (at level 0).

(** The retagger for the function name [Lf] (fun_nm, typing.v). *)
Definition retag := 'tagger[Lf].
Opaque retag.

Lemma tagged_eval : forall f t u v,
  f @ u ==> v -> 'tagged [f,t] @ u ==> v.
Proof. intros f t u v Hv; cbv; evaluate. Qed.

Lemma tagged_decide : forall T,
  (exists C N, T = 'tagged[C,N]) \/
  (forall C N, T <> 'tagged[C,N]).
Proof.
  intro T.
  destruct T as [| t | l r];
    try (right; intros C N H; discriminate H).
  destruct l as [| l | l1 l2];
    try (right; intros C N H; discriminate H).
  destruct l as [| l | l1 C];
    try (right; intros C0 N H; discriminate H).
  destruct l1 as [| l1 | l11 l12];
    try (right; intros C0 N H; discriminate H).
  destruct r as [| r | r1 r2];
    try (right; intros C0 N H; discriminate H).
  destruct r1 as [| r1 | r11 r12];
    try (right; intros C0 N H; discriminate H).
  destruct r1 as [| r1 | r11 r12];
    try (right; intros C0 N H; discriminate H).
  destruct r1 as [| r1 | r11 r12];
    try (right; intros C0 N H; discriminate H).
  destruct r2 as [| r2 | r21 N];
    try (right; intros C0 N0 H; discriminate H).
  destruct r21 as [| r21 | r211 r212];
    try (right; intros C0 N0 H; discriminate H).
  left; exists C, N; reflexivity.
Qed.

Definition get_tagged :=
  Eval cbv -[equal1] in
    to_tree
      (tcase (''tagged[Ref "C", Ref "N"])
        (Val Lf @@ Ref "C" @@ Ref "N")).

Lemma get_tagged_some : forall C N,
  get_tagged @ ('tagged[C,N]) ==> Sm (Fk C N).
Proof.
  intros C N; unfold get_tagged.
  repeat first
    [ apply equal1_eq
    | eapply extend_some; apply tcase_eq
    | unfold extend_program; cbn; evaluate
    | evaluate
    ].
Qed.

(** Recover just the name carried by a tagged program. *)
Definition get_tagname :=
  Eval cbv -[equal1] in
    to_tree
      (tcase (''tagged[Ref "C", Ref "N"])
        (Ref "N")).

Lemma get_tagname_some : forall C N,
  get_tagname @ ('tagged[C,N]) ==> Sm N.
Proof.
  intros C N; unfold get_tagname.
  repeat first
    [ apply equal1_eq
    | eapply extend_some; apply tcase_eq
    | unfold extend_program; cbn; evaluate
    | evaluate
    ].
Qed.

Lemma get_tagged_fork_none : forall F U,
  (forall C N, Fk F U <> 'tagged[C,N]) ->
  get_tagged @ Fk F U ==> Lf.
Proof.
  intros F U Hnot; unfold get_tagged.
  destruct F; try (cbv; evaluate; fail).
  destruct F; try (cbv; evaluate; fail).
  destruct F1; try (cbv; evaluate; fail).
  destruct U; try (cbv; evaluate; fail).
  destruct U1; try (cbv; evaluate; fail).
  destruct U1; try (cbv; evaluate; fail).
  destruct U1; try (cbv; evaluate; fail).
  destruct U2; try (cbv; evaluate; fail).
  destruct U2_1; try (cbv; evaluate; fail).
  exfalso; eapply Hnot; eauto.
Qed.

Lemma get_tagged_none : forall T,
  (forall C N, T <> 'tagged[C,N]) ->
  get_tagged @ T ==> Lf.
Proof.
  intros T Hnot; destruct T as [| T | left right].
  - unfold get_tagged; cbv; evaluate.
  - unfold get_tagged; cbv; evaluate.
  - apply get_tagged_fork_none; exact Hnot.
Qed.

(** Failure and totality for the option-valued tag-name getter. *)
Lemma get_tagname_fork_none : forall F U,
 (forall C N, Fk F U <> 'tagged[C,N]) ->
 get_tagname @ Fk F U ==> Lf.
Proof.
 intros F U Hnot; unfold get_tagname.
 destruct F; try (cbv; evaluate; fail).
 destruct F; try (cbv; evaluate; fail).
 destruct F1; try (cbv; evaluate; fail).
 destruct U; try (cbv; evaluate; fail).
 destruct U1; try (cbv; evaluate; fail).
 destruct U1; try (cbv; evaluate; fail).
 destruct U1; try (cbv; evaluate; fail).
 destruct U2; try (cbv; evaluate; fail).
 destruct U2_1; try (cbv; evaluate; fail).
 exfalso; eapply Hnot; eauto.
Qed.
Lemma get_tagname_none : forall u,
 (forall C N, u <> 'tagged[C,N]) -> get_tagname @ u ==> Lf.
Proof.
 intros [|u|x y] H.
 - unfold get_tagname; cbv; evaluate.
 - unfold get_tagname; cbv; evaluate.
 - apply get_tagname_fork_none; exact H.
Qed.

(** ** The name test

    The name test [name_test n] checks the nametag of a value: it is
    ordinary equality on the optional tag name. *)
Definition name_test nm := ('wait[equal,Sm nm]) 'C get_tagname.

Lemma name_test_miss : forall nm u found,
  get_tagname @ u ==> found -> found <> Sm nm -> name_test nm @ u ==> 'KI.
Proof. intros; unfold name_test; repeat first [apply equal_eval|apply wait_eval|apply equal1_neq;congruence|progress evaluate]. Qed.

Lemma name_test_tag_hit : forall N C,
 name_test N @ ('tagged[C,N]) ==> 'K.
Proof.
 intros; pose proof (get_tagname_some C N).
 unfold name_test; repeat first [eassumption|apply equal_eval|apply wait_eval|apply equal1_eq|progress evaluate].
Qed.

Lemma name_test_tag_miss : forall N u,
 (forall C, u <> 'tagged[C,N]) -> name_test N @ u ==> 'KI.
Proof.
 intros N u H.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - pose proof (get_tagname_some C M).
   assert (Sm N <> Sm M) by (intro HE; inversion HE; subst; eapply H; reflexivity).
   unfold name_test; repeat first [eassumption|apply equal_eval|apply wait_eval|apply equal1_neq; assumption|progress evaluate].
 - pose proof (get_tagname_none u Hplain).
   unfold name_test; repeat first [eassumption|apply equal_eval|apply wait_eval|apply equal1_neq; discriminate|progress evaluate].
Qed.

Lemma name_test_total : forall N U, exists b, name_test N @ U ==> b.
Proof.
 intros N U; destruct (tagged_decide U) as [[C [M ->]]|Hp].
 - destruct (combination_eq_dec N M) as [->|Hne].
   + eexists; apply name_test_tag_hit.
   + eexists; apply name_test_tag_miss; intros C' HE; inversion HE; congruence.
 - eexists; apply name_test_tag_miss; intros C' HE; eapply Hp; exact HE.
Qed.


Lemma get_tagname_total : forall u,
 get_tagname @ u ==> Lf \/ exists C N, u = 'tagged[C,N] /\ get_tagname @ u ==> Sm N.
Proof.
 intro u; destruct (tagged_decide u) as [[C [N ->]]|Hplain].
 - right; exists C,N; split; [reflexivity|apply get_tagname_some].
 - left; apply get_tagname_none; exact Hplain.
Qed.

(** Compare the second component of a fork with [retag].  Equality is
    kept explicit rather than compiled into a larger [tcase]. *)
Opaque equal.

Local Definition get_retag_check_package :
  { t |
    to_tree
      (\"D" (\"R"
        (Val equal @@ Ref "R" @@ Val retag
          @@ (Val Lf @@ Ref "D") @@ Val Lf))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition get_retag_check :=
  Eval cbn in proj1_sig get_retag_check_package.

Definition get_retag := Fk ('K1 ('K1 Lf)) get_retag_check.

Lemma get_retag_some : forall D,
  get_retag @ (Fk D retag) ==> Sm D.
Proof.
  intros D; unfold get_retag, get_retag_check; cbn.
  repeat (eapply equal_eval || eapply equal1_eq || evaluate).
Qed.

Lemma get_retag_inv : forall X D,
  get_retag @ X ==> Sm D ->
  X = Fk D retag.
Proof.
  intros X D H.
  destruct X as [|X|left right];
    unfold get_retag, get_retag_check in H; cbn in H; invert_eval.
  assert (Hequal : equal @ right @r retag ==> v0)
    by (eapply eval_appl; eauto).
  destruct (equal_spec right retag v0 Hequal)
    as [[-> Heq] | [-> Hneq]].
  - subst right; invert_eval.
  - invert_eval.
Qed.

Definition get_retag_composition :=
  ('onStem1 get_retag) 'C get_composition.

Lemma get_retag_composition_some : forall D,
  get_retag_composition @ (D 'C retag) ==> Sm D.
Proof.
  intros D; unfold get_retag_composition.
  evaluate.
  - apply get_composition_some.
  - evaluate; apply get_retag_some.
Qed.

Lemma get_retag_composition_inv : forall X D,
  get_retag_composition @ X ==> Sm D ->
  X = D 'C retag.
Proof.
  intros X D H.
  unfold get_retag_composition in H.
  invert_eval.
  apply get_retag_inv in H5.
  subst v0.
  apply get_composition_inv in H4.
  exact H4.
Qed.

(** * Decorations

    Decorations are behavioural tags built from [wait].  Their recognition
    is kept beside the corresponding tagged recognizers. *)

Notation "'decorate [ f , U ]" := ('wait [ 'K1 f, U]).
Notation "''decorate [ f , U ]" := (''wait [ ''K1 f, U]).

(** A decoration discards its annotation on application. *)
Lemma decorate_apply : forall f u x r,
  f @ x ==> r -> 'decorate[f,u] @ x ==> r.
Proof. intros; apply wait_eval; evaluate; eauto. Qed.


(** Wait recognition resumes here because it depends on the pattern compiler above. *)

(** Strict waiting is recognised once and then reused by the seed and fix
    constructors. *)
Definition get_wait :=
  Eval cbv in
    to_tree
      (tcase
         (''wait [Ref "M", Ref "N"])
         (Val Lf @@ Ref "M" @@ Ref "N")).

Lemma get_wait_some : forall M N,
  get_wait @ ('wait[M,N]) ==> Sm (Fk M N).
Proof.
  intros M N; unfold get_wait.
  repeat (eapply equal1_eq || evaluate).
Qed.

Lemma get_wait_inv : forall X M N,
  get_wait @ X ==> Sm (Fk M N) ->
  X = 'wait[M,N].
Proof.
  intros X M N H.
  unfold get_wait in H.
  inv_out H; invert_eval.
Qed.

Lemma get_wait_none : forall X,
  (forall M N, X <> 'wait[M,N]) ->
  get_wait @ X ==> Lf.
Proof.
  intros X Hnone.
  destruct X as [| x | l r].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct l as [| a | l1 l2].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct a as [| a | b d].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct b as [| b | b1 b2].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct b as [| b | c M].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct c as [| c | c1 c2].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct d as [| d | d1 N].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct d1 as [| d1 | d11 d12].
  all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
  destruct (combination_eq_dec r 'I) as [-> | Hneq].
  - exfalso; eapply Hnone; reflexivity.
  - destruct r as [| r | r1 r2].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    destruct r1 as [| r1 | r11 r12].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    destruct r1 as [| r1 | r11 r12].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    destruct r1 as [| r1 | r11 r12].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    destruct r2 as [| r2 | r21 r22].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    destruct r2 as [| r2 | r21 r22].
    all: try solve [unfold get_wait; cbv -[equal equal1]; evaluate].
    exfalso; apply Hneq; reflexivity.
Qed.

(** * Reusable delay recognition

    All inspection is performed by tree programs: expose a delay, check its head, and recover its arguments.
    The Coq case analyses below prove those programs correct. *)

Ltac recognizer_eqtac :=
  match goal with
  | H : equal1 ?M @ ?N ==> ?v |- _ =>
    destruct (combination_eq_dec M N) as [Heq|Hneq];
    [subst; assert (v = 'K) by
       (eapply eval_deterministic; [exact H|apply equal1_eq])
    |assert (v = 'KI) by
       (eapply eval_deterministic; [exact H|apply equal1_neq; exact Hneq])];
    subst; clear H; invert_eval
  | _ => progress eqtac
  end.

Opaque get_wait equal equal1.

(** Check a delay's head and pair its stored argument with a supplied value. *)

Opaque get_wait equal.

(** Recover the two stored arguments of nested delays with a fixed head. *)


(** Strip the leading [K1] from the pair exposed by [get_wait]. *)
Definition get_decorate_body :=
  Eval cbv -[equal1] in
    to_tree
      (tcase
         (Val Lf @@ (''K1 (Ref "F")) @@ Ref "E")
         (Val Lf @@ Ref "F" @@ Ref "E")).

Lemma get_decorate_body_some : forall F E,
  get_decorate_body @ (Fk ('K1 F) E) ==> Sm (Fk F E).
Proof.
  intros F E; unfold get_decorate_body.
  repeat (eapply equal1_eq || evaluate).
Qed.

Lemma get_decorate_body_inv : forall X F E,
  get_decorate_body @ X ==> Sm (Fk F E) ->
  X = Fk ('K1 F) E.
Proof.
  Local Transparent equal1.
  intros X F E H.
  unfold get_decorate_body in H.
  inv_out H; invert_eval.
Local Opaque equal1.
Qed.

Definition get_decorate :=
  ('onStem1 get_decorate_body) 'C get_wait.

Lemma get_decorate_some : forall F E,
  get_decorate @ 'decorate[F,E] ==> Sm (Fk F E).
Proof.
  intros F E; unfold get_decorate.
  evaluate.
  - apply get_wait_some.
  - evaluate; apply get_decorate_body_some.
Qed.

Lemma get_decorate_inv : forall X F E,
  get_decorate @ X ==> Sm (Fk F E) ->
  X = 'decorate[F,E].
Proof.
  intros X F E H.
  unfold get_decorate in H.
  invert_eval.
  apply get_decorate_body_inv in H5.
  subst v0.
  apply get_wait_inv in H4.
  exact H4.
Qed.

Lemma get_decorate_result_inv : forall X R,
  get_decorate @ X ==> R ->
  R = Lf \/
  exists F E, R = Sm (Fk F E) /\ X = 'decorate[F,E].
Proof.
  Local Transparent equal1.
  intros X R H; destruct R as [| R | R1 R2].
  - left; reflexivity.
  - destruct R as [| R | F E].
    + unfold get_decorate in H; invert_eval.
      unfold get_decorate_body in H5; invert_eval.
    + unfold get_decorate in H; invert_eval.
      unfold get_decorate_body in H5; invert_eval.
    + right; exists F, E; split; [reflexivity |].
      eapply get_decorate_inv; exact H.
  - unfold get_decorate in H; invert_eval.
    unfold get_decorate_body in H5; invert_eval.
Local Opaque equal1.
Qed.

Lemma get_decorate_none : forall X,
  (forall E D, X <> 'decorate[E,D]) ->
  get_decorate @ X ==> Lf.
Proof.
  intros X Hnone; destruct (wait_decide X) as
    [[M [D ->]] | Hnot_wait].
  - destruct M as [| M | left E].
    + unfold get_decorate; evaluate.
      * apply get_wait_some.
      * unfold get_decorate_body; cbv -[equal equal1]; evaluate.
    + unfold get_decorate; evaluate.
      * apply get_wait_some.
      * unfold get_decorate_body; cbv -[equal equal1]; evaluate.
    + destruct left as [| left | left1 left2].
      * exfalso; eapply Hnone; reflexivity.
      * unfold get_decorate; evaluate.
        -- apply get_wait_some.
        -- unfold get_decorate_body; cbv -[equal equal1].
           repeat (first [eapply equal1_neq; discriminate | evaluate]).
      * unfold get_decorate; evaluate.
        -- apply get_wait_some.
        -- unfold get_decorate_body; cbv -[equal equal1].
           repeat (first [eapply equal1_neq; discriminate | evaluate]).
  - unfold get_decorate; evaluate.
    apply get_wait_none; exact Hnot_wait.
    evaluate.
Qed.


(** * Alternative type tags *)
(** A distinct decorator for abstract types; ordinary values retain [tagged]. *)
Open Scope string_scope.


(** * Recognition of nominal wrappers *)
Set Default Proof Using "Type".
Open Scope string_scope.

(** One-field wrappers. No inference or update machinery is imported. *)
Definition wrap (nm f : Combination) : Combination :=
  'tagged['S2['I,'K1 f],nm].

Notation "'wrap [ f , n ]" := (wrap n f)
  (at level 0, f at level 41, n at level 41).


(** Tag-freeness, shared by inference and update validation. *)
Definition reserved_tagb (t : Combination) : bool :=
  match t with
  | Fk (Sm (Fk Lf _)) (Fk (Sm (Sm Lf)) (Fk Lf _)) => true
  | _ => false
  end.

Fixpoint tag_free (t : Combination) : bool :=
  match t with
  | Lf => true
  | Sm u => tag_free u
  | Fk u v => (negb (reserved_tagb t) && tag_free u) && tag_free v
  end.

Lemma reserved_tagb_tagged : forall E N,
  reserved_tagb ('tagged[E,N]) = true.
Proof. reflexivity. Qed.

Ltac tag_free_tac := vm_compute; reflexivity.

(** Concrete trees by rules: those with no label [S2[K, K1 n]].  This is
    a proof device only; [concrete] below is defined by the program
    [is_concrete], and [concrete_iff_rules] relates the two. *)
Fixpoint concrete_rules (c : Combination) : Prop :=
  match c with
  | Lf => True
  | Sm u => concrete_rules u
  | Fk u v => ~ (u = Sm (Sm Lf) /\ exists n, v = Fk Lf n) /\ concrete_rules u /\ concrete_rules v
  end.

(** Executable check of concreteness. *)
Definition label_pair (u v : Combination) : bool :=
  match u, v with
  | Sm (Sm Lf), Fk Lf _ => true
  | _, _ => false
  end.

Fixpoint concreteb (c : Combination) : bool :=
  match c with
  | Lf => true
  | Sm u => concreteb u
  | Fk u v => negb (label_pair u v) && concreteb u && concreteb v
  end.

Lemma concreteb_sound_rules : forall c, concreteb c = true -> concrete_rules c.
Proof.
  induction c as [|u IH|u IHu v IHv]; cbn; auto.
  intros H; apply andb_prop in H as [H Hv]; apply andb_prop in H as [Hp Hu].
  repeat split; auto.
  intros [-> [n ->]]; discriminate.
Qed.

Lemma concreteb_complete_rules : forall c, concrete_rules c -> concreteb c = true.
Proof.
  induction c as [|u IH|u IHu v IHv]; cbn; auto.
  intros [Hp [Hu Hv]]; rewrite IHu, IHv by assumption.
  destruct (label_pair u v) eqn:E; [|reflexivity].
  exfalso; apply Hp; destruct u as [|[|[| |]|]|]; try discriminate;
    destruct v as [| |[| |] n]; try discriminate; eauto.
Qed.

Lemma concreteb_spec_rules : forall c, concreteb c = true <-> concrete_rules c.
Proof. split; [apply concreteb_sound_rules | apply concreteb_complete_rules]. Qed.

(** Recognition of a label [S2[K, K1 n]] by pattern tests alone.
    ['label_test] applied to [u] and then [v] returns [K] exactly when
    [Fk u v] is a label, and [KI] otherwise.  It inspects [u] by three
    nested triages (looking for [Sm (Sm Lf)]) and then [v] by two
    (looking for [Fk Lf _]); it contains no label itself. *)
Notation "'label_test_r" :=
  ('triage['KI, 'K1 'KI, 'triage['K1 'K, 'K1 ('K1 'KI), 'K1 ('K1 ('K1 'KI))]]).
Notation "'label_test" :=
  ('triage['K1 'KI,
     'triage['K1 'KI,
        'triage['label_test_r, 'K1 ('K1 'KI), 'K1 ('K1 ('K1 'KI))],
        'K1 ('K1 ('K1 'KI))],
     'K1 ('K1 ('K1 'KI))]).

Lemma label_test_spec : forall u v,
  'label_test @ u @r v ==> (if label_pair u v then 'K else 'KI).
Proof.
  intros u v.
  destruct u as [|[|[|u|u1 u2]|u1 u2]|u1 u2]; cbn [label_pair];
    try (evaluate; fail).
  destruct v as [|v|[|v1|v11 v12] v2]; cbn [label_pair]; evaluate.
Qed.

Lemma label_test_spec2 : forall u v, exists w,
  'label_test @ u ==> w /\ w @ v ==> (if label_pair u v then 'K else 'KI).
Proof.
  intros u v; pose proof (label_test_spec u v) as H.
  inversion H; subst; eauto.
Qed.

(** Executable recognition of concreteness. This program
    computes the predicate [concreteb], returning K or KI; hence its name
    [is_concrete].  A concrete tree is also tag-free ([concrete_tag_free]). *)
Local Opaque Z get_tagged equal equal1.
Definition is_concrete := Eval cbn -[Z] in Z (to_tree
  (star "rec" (''triage[Val ('K), Ref "rec",
    star "l" (star "r"
      (Val ('label_test) @@ Ref "l" @@ Ref "r" @@ Val ('KI)
        @@ (Ref "rec" @@ Ref "l" @@ (Ref "rec" @@ Ref "r") @@ Val ('KI))))]))).

Lemma is_concrete_spec : forall n,
  is_concrete @ n ==> (if concreteb n then 'K else 'KI).
Proof.
  induction n as [|n IH|l IHl r IHr].
  - apply Z_unfold; evaluate.
  - change (is_concrete @ Sm n ==> (if concreteb n then 'K else 'KI)).
    destruct (concreteb n); apply Z_unfold; evaluate.
  - destruct (label_test_spec2 l r) as [w [Hw Hlab]].
    cbn [concreteb].
    destruct (label_pair l r); destruct (concreteb l); destruct (concreteb r);
      cbn; apply Z_unfold;
      repeat first [exact IHl|exact IHr|exact Hw|exact Hlab|progress evaluate].
Qed.

(** Concrete trees: those on which the program [is_concrete] says yes. *)
Definition concrete (c : Combination) : Prop := is_concrete @ c ==> 'K.

Lemma concreteb_spec : forall c, concreteb c = true <-> concrete c.
Proof.
  intro n; unfold concrete; pose proof (is_concrete_spec n) as H; split.
  - intro E; rewrite E in H; exact H.
  - intro Hrun; pose proof (eval_deterministic _ _ Hrun _ H).
    destruct (concreteb n); congruence.
Qed.

Lemma concreteb_sound : forall c, concreteb c = true -> concrete c.
Proof. intro c; apply concreteb_spec. Qed.


(** The program agrees with the rules. *)
Lemma concrete_iff_rules : forall c, concrete c <-> concrete_rules c.
Proof. intro c; rewrite <- concreteb_spec, concreteb_spec_rules; reflexivity. Qed.

Lemma is_concrete_true : forall n,
  is_concrete @ n ==> 'K <-> concrete n.
Proof. reflexivity. Qed.

(** * Translations of normal lambda terms are tag-free

    A value is tag-free when no subtree has the tag shape
    [S2[K1 f, S2[K, K1 n]]].  The obstacle to producing a tag is the inner
    [S2[K, K1 n]], which is behaviourally an identity:
    [S2[K, K1 n] @ u ==> u].

    A closed term built in normal form from variables, applications and
    [star] compiles to a tag-free value ([normal_combinators_are_concrete],
    self_typing.v).  Terms with beta-redexes can fail: the redex
    [(\y. x) (\y. y)] is a disguised identity, compiled literally, and
    eta-contraction in [star] turns it into a bare [K].

    Proof outline.  [ops_ok] says every operator is neutral (a variable
    applied to arguments) or a construction head; it excludes redexes.
    Under [ops_ok], [star]'s pattern tests are exact ([star_present]), so
    [star] preserves [ops_ok] and the absence of labels ([star_inv],
    [star_nolab]).  In a closed term with both invariants, [to_tree] is
    structural, so the tree has no label ([closed_lf]); every tag
    contains a label ([concrete_tag_free]). *)


(** * Invariants on translated terms *)

(** Neutral terms: a variable applied to arguments. *)
Inductive neutral : Term -> Prop :=
| neut_ref : forall h, neutral (Ref h)
| neut_app : forall n a, neutral n -> neutral (n @@ a).

(** Admissible operators: neutral terms or construction heads. *)
Definition op_ok (f : Term) : Prop :=
  neutral f \/ f = Val Lf \/ f = Val 'K \/ exists u, f = Val Lf @@ u.

Fixpoint ops_ok (t : Term) : Prop :=
  match t with
  | Ref _ => True
  | Val c => c = Lf \/ c = 'K
  | f @@ a => op_ok f /\ ops_ok f /\ ops_ok a
  end.

Fixpoint occurs_free (x : string) (t : Term) : bool :=
  match t with
  | Ref y => String.eqb x y
  | Val _ => false
  | t1 @@ t2 => occurs_free x t1 || occurs_free x t2
  end.

(** If [x] does not occur, [star] returns the constant function. *)
Lemma star_absent : forall x M, occurs_free x M = false -> star x M = ''K1 M.
Proof.
  intros x M; induction M as [y|c|t1 IH1 t2 IH2]; cbn [occurs_free star]; intro H.
  - rewrite H; reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2); reflexivity.
Qed.

(** * How [star] acts on an application *)

Definition k1_view (s : Term) : option Term :=
  match s with ''K1 t => Some t | _ => None end.
Definition is_I (s : Term) : bool :=
  match s with ''I => true | _ => false end.

Lemma star_app_view : forall x t1 t2,
  star x (t1 @@ t2) =
  match k1_view (star x t1) with
  | Some t3 =>
      match k1_view (star x t2) with
      | Some t4 => ''K1 (t3 @@ t4)
      | None => if is_I (star x t2) then t3 else ''S2 [''K1 t3, star x t2]
      end
  | None => ''S2 [star x t1, star x t2]
  end.
Proof.
  intros x t1 t2; cbn [star]; unfold k1_view, is_I.
  generalize (star x t1) as s1; generalize (star x t2) as s2; intros s2 s1.
  repeat (match goal with
          | |- context [match ?t with _ => _ end] => is_var t; destruct t
          end); reflexivity.
Qed.

(** Terms denoting [K] after compilation, and terms denoting some [K1 n]. *)
Definition denotes_K (u : Term) : Prop := u = Val 'K \/ u = Val Lf @@ Val Lf.

Lemma is_I_S2 : forall u v, is_I (''S2 [u, v]) = true -> u = Val 'K.
Proof.
  intros u v H; unfold is_I in H.
  repeat (match goal with
          | H : context [match ?t with _ => _ end] |- _ => is_var t; destruct t
          end); try discriminate; reflexivity.
Qed.

(** Admissible operators are seen correctly by both pattern tests. *)
Lemma op_ok_views : forall f, op_ok f -> k1_view f = None /\ is_I f = false.
Proof.
  intros f [Hn|[->|[->|[u ->]]]]; try (split; reflexivity).
  inversion Hn as [h|n a Hn' E]; subst; [split; reflexivity|].
  split; [destruct n; try reflexivity; inversion Hn'|].
  inversion Hn' as [h|n0 a0 Hn0 E0]; subst; [reflexivity|].
  destruct n0; try reflexivity; inversion Hn0.
Qed.

(** Under [ops_ok], when [x] occurs the result is never a [K1]-pattern, is the
    [I]-pattern only for [x] itself, and from an admissible operator never
    denotes [K]. *)
Lemma star_present : forall x M, ops_ok M -> occurs_free x M = true ->
  k1_view (star x M) = None /\
  (is_I (star x M) = true -> M = Ref x) /\
  (op_ok M -> ~ denotes_K (star x M)).
Proof.
  intros x M; induction M as [y|c|t1 IH1 t2 IH2]; intros Hinv Hocc.
  - cbn [occurs_free] in Hocc; apply String.eqb_eq in Hocc; subst y.
    cbn [star]; rewrite String.eqb_refl.
    split; [reflexivity|split; [intros _; reflexivity|]].
    intros _ [H|H]; discriminate.
  - discriminate.
  - destruct Hinv as [Hop [Hi1 Hi2]].
    rewrite star_app_view.
    destruct (occurs_free x t1) eqn:E1.
    + destruct (IH1 Hi1 eq_refl) as [N1 [_ K1]]; rewrite N1.
      split; [reflexivity|split].
      * intros HI; apply is_I_S2 in HI; exfalso; apply (K1 Hop); left; exact HI.
      * intros _ [H|H]; discriminate.
    + cbn [occurs_free] in Hocc; rewrite E1 in Hocc; cbn in Hocc.
      rewrite (star_absent x t1 E1); cbn [k1_view].
      destruct (IH2 Hi2 Hocc) as [N2 [I2 _]]; rewrite N2.
      destruct (is_I (star x t2)) eqn:EI.
      * specialize (I2 eq_refl); subst t2.
        destruct (op_ok_views t1 Hop) as [V1 W1].
        split; [exact V1|split; [rewrite W1; discriminate|]].
        intros HopM [H|H]; subst t1.
        -- destruct HopM as [Hn|[H|[H|[u H]]]]; try discriminate.
           inversion Hn as [|n a Hn' E]; subst; inversion Hn'.
        -- destruct HopM as [Hn|[H|[H|[u H]]]]; try discriminate.
           inversion Hn as [|n a Hn' E]; subst; inversion Hn' as [|n' a' Hn'' E'];
             subst; inversion Hn''.
      * split; [reflexivity|split].
        -- intros HI; apply is_I_S2 in HI; discriminate.
        -- intros _ [H|H]; discriminate.
Qed.

(** * [star] preserves both invariants *)

Lemma inv_S2 : forall u v, ops_ok u -> ops_ok v -> ops_ok (''S2 [u, v]).
Proof.
  intros u v Hu Hv; cbn [ops_ok].
  repeat split; auto;
    unfold op_ok; eauto 6.
Qed.

Lemma inv_K1 : forall u, ops_ok u -> ops_ok (''K1 u).
Proof. intros u Hu; cbn [ops_ok]; unfold op_ok; repeat split; auto. Qed.

Lemma star_inv : forall x M, ops_ok M -> ops_ok (star x M).
Proof.
  intros x M; induction M as [y|c|t1 IH1 t2 IH2]; intros Hinv.
  - cbn [star]; destruct (String.eqb x y).
    + apply inv_S2; cbn; auto.
    + apply inv_K1; exact I.
  - cbn [star]; apply inv_K1; exact Hinv.
  - pose proof Hinv as HM; destruct Hinv as [Hop [Hi1 Hi2]].
    rewrite star_app_view.
    destruct (occurs_free x t1) eqn:E1.
    + destruct (star_present x t1 Hi1 E1) as [N1 _]; rewrite N1.
      apply inv_S2; auto.
    + rewrite (star_absent x t1 E1); cbn [k1_view].
      destruct (occurs_free x t2) eqn:E2.
      * destruct (star_present x t2 Hi2 E2) as [N2 _]; rewrite N2.
        destruct (is_I (star x t2)); [exact Hi1|].
        apply inv_S2; [apply inv_K1|]; auto.
      * rewrite (star_absent x t2 E2); cbn [k1_view].
        apply inv_K1; exact HM.
Qed.

(** The label: [S2[u,v]] with [u] denoting [K] and [v] denoting some
    [K1 n].  Behaviourally it is an identity. *)
Definition denotes_K1 (v : Term) : Prop :=
  exists n, v = ''K1 n \/ v = (Val Lf @@ Val Lf) @@ n.
Definition label_shape (t : Term) : Prop :=
  exists u v, t = ''S2 [u, v] /\ denotes_K u /\ denotes_K1 v.

Fixpoint no_label (t : Term) : Prop :=
  match t with
  | f @@ a => ~ label_shape (f @@ a) /\ no_label f /\ no_label a
  | _ => True
  end.

Lemma nolab_S2 : forall u v, no_label u -> no_label v -> ~ denotes_K u \/ ~ denotes_K1 v ->
  no_label (''S2 [u, v]).
Proof.
  intros u v Hu Hv Hk; cbn [no_label]; repeat split; auto;
    intros [u' [v' [E [Hk' Hv']]]]; inversion E; subst; tauto.
Qed.

Lemma nolab_K1 : forall u, no_label u -> no_label (''K1 u).
Proof.
  intros u Hu; cbn [no_label]; repeat split; auto;
    intros [u' [v' [E _]]]; discriminate.
Qed.

Lemma star_nolab : forall x M, ops_ok M -> no_label M -> no_label (star x M).
Proof.
  intros x M; induction M as [y|c|t1 IH1 t2 IH2]; intros Hinv Hnb.
  - cbn [star]; destruct (String.eqb x y).
    + apply nolab_S2; cbn; auto.
      right; intros [n [H|H]]; discriminate.
    + apply nolab_K1; exact I.
  - cbn [star]; apply nolab_K1; exact I.
  - pose proof Hnb as HM; destruct Hinv as [Hop [Hi1 Hi2]];
      destruct Hnb as [_ [Hn1 Hn2]].
    rewrite star_app_view.
    destruct (occurs_free x t1) eqn:E1.
    + destruct (star_present x t1 Hi1 E1) as [N1 [_ K1]]; rewrite N1.
      apply nolab_S2; auto.
    + rewrite (star_absent x t1 E1); cbn [k1_view].
      destruct (occurs_free x t2) eqn:E2.
      * destruct (star_present x t2 Hi2 E2) as [N2 _]; rewrite N2.
        destruct (is_I (star x t2)); [exact Hn1|].
        apply nolab_S2; [apply nolab_K1| |]; auto.
        left; intros [H|H]; discriminate.
      * rewrite (star_absent x t2 E2); cbn [k1_view].
        apply nolab_K1; exact HM.
Qed.

(** * Closed terms compile without labels *)

Fixpoint no_ref (t : Term) : bool :=
  match t with
  | Ref _ => false
  | Val _ => true
  | t1 @@ t2 => no_ref t1 && no_ref t2
  end.

Lemma neut_noref : forall t, neutral t -> no_ref t = false.
Proof.
  intros t H; induction H as [h|n a Hn IH]; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

(** In a closed term satisfying [ops_ok], every operator is a construction
    head. *)
Lemma closed_op : forall f, op_ok f -> no_ref f = true ->
  f = Val Lf \/ f = Val 'K \/ exists u, f = Val Lf @@ u.
Proof.
  intros f [Hn|H] Hc; [rewrite (neut_noref f Hn) in Hc; discriminate|tauto].
Qed.

Lemma reserved_shape : forall t, reserved_tagb t = true ->
  exists a n, t = Fk (Sm (Fk Lf a)) (Fk (Sm (Sm Lf)) (Fk Lf n)).
Proof.
  intros t H; unfold reserved_tagb in H;
  repeat (match goal with
          | H : context [match ?x with _ => _ end] |- _ => is_var x; destruct x
          end); try discriminate; eauto.
Qed.

(** Every tag contains a label, so concrete trees are tag-free. *)
Lemma concrete_tag_free : forall c, concrete c -> tag_free c = true.
Proof.
  setoid_rewrite concrete_iff_rules.
  induction c as [|u IH|u IHu v IHv]; cbn [concrete_rules tag_free]; auto.
  intros [Hb [Hu Hv]].
  destruct (reserved_tagb (Fk u v)) eqn:R.
  - destruct (reserved_shape _ R) as [a [n E]]; inversion E; subst.
    cbn in Hv; exfalso; apply (proj1 Hv); split; eauto.
  - cbn; rewrite IHu, IHv; auto.
Qed.

Lemma closed_leaf : forall t, no_ref t = true -> ops_ok t -> to_tree t = Lf -> t = Val Lf.
Proof.
  intros [y|c|f a] Hc Hi H; try discriminate.
  - cbn in H; subst; reflexivity.
  - cbn [no_ref] in Hc; apply Bool.andb_true_iff in Hc as [Hcf _].
    destruct Hi as [Hop _].
    destruct (closed_op f Hop Hcf) as [->|[->|[u ->]]]; cbn in H; discriminate.
Qed.

Lemma closed_K : forall t, no_ref t = true -> ops_ok t -> to_tree t = Sm Lf -> denotes_K t.
Proof.
  intros [y|c|f a] Hc Hi H; try discriminate.
  - cbn in H; subst; left; reflexivity.
  - cbn [no_ref] in Hc; apply Bool.andb_true_iff in Hc as [Hcf Hca].
    destruct Hi as [Hop [_ Hia]].
    destruct (closed_op f Hop Hcf) as [->|[->|[u ->]]]; cbn in H;
      try discriminate.
    inversion H as [Ha]; apply closed_leaf in Ha; auto; subst; right; reflexivity.
Qed.

Lemma closed_K1 : forall t n, no_ref t = true -> ops_ok t -> to_tree t = Fk Lf n -> denotes_K1 t.
Proof.
  intros [y|c|f a] n Hc Hi H; try discriminate.
  - cbn in H; subst c; destruct Hi as [H|H]; discriminate.
  - cbn [no_ref] in Hc; apply Bool.andb_true_iff in Hc as [Hcf Hca].
    destruct Hi as [Hop [Hif Hia]].
    destruct (closed_op f Hop Hcf) as [->|[->|[u ->]]]; cbn in H;
      try discriminate.
    + exists a; left; reflexivity.
    + cbn [no_ref] in Hcf; cbn [ops_ok] in Hif.
      destruct (to_tree u) eqn:Eu; try discriminate.
      apply closed_leaf in Eu; [|exact Hcf|exact (proj2 (proj2 Hif))].
      subst; exists a; right; reflexivity.
Qed.

Lemma closed_lf : forall t, no_ref t = true -> ops_ok t -> no_label t -> concrete (to_tree t).
Proof.
  setoid_rewrite concrete_iff_rules.
  induction t as [y|c|f IHf a IHa]; intros Hc Hi Hn.
  - discriminate.
  - destruct Hi as [->| ->]; cbn; auto.
  - cbn [no_ref] in Hc; apply Bool.andb_true_iff in Hc as [Hcf Hca].
    pose proof Hi as HiM; pose proof Hn as HnM.
    destruct Hi as [Hop [Hif Hia]]; destruct Hn as [Hbar [Hnf Hna]].
    specialize (IHa Hca Hia Hna).
    destruct (closed_op f Hop Hcf) as [->|[->|[u ->]]].
    + cbn; exact IHa.
    + cbn; repeat split; auto; intros [H _]; discriminate.
    + specialize (IHf Hcf Hif Hnf); cbn in IHf |- *.
      repeat split; auto.
      intros [Hu [n Ha]].
      cbn [no_ref] in Hcf; cbn [ops_ok] in Hif.
      destruct Hif as [_ [_ Hiu]].
      destruct u as [y|c|f' u0]; try discriminate.
      * cbn in Hu; subst c; destruct Hiu as [H|H]; discriminate.
      * cbn [no_ref] in Hcf; apply Bool.andb_true_iff in Hcf as [_ Hcu].
        apply Bool.andb_true_iff in Hcu as [Hcf' Hcu0].
        destruct Hiu as [Hop' [Hif' Hiu0]].
        destruct (closed_op f' Hop' Hcf') as [->|[->|[w ->]]]; cbn in Hu;
          try discriminate.
        inversion Hu as [Hu0].
        apply Hbar; exists u0, a; split; [reflexivity|split].
        -- apply closed_K; auto.
        -- apply (closed_K1 a n); auto.
Qed.

(** * Pure lambda terms in normal form *)

(** Built from variables, applications and [star] within [Term]: normal
    terms are neutral terms or abstractions of normal terms; neutral terms
    are variables applied to normal terms. *)
Inductive pure_nf : Term -> Prop :=
| pure_nf_ne : forall n, pure_ne n -> pure_nf n
| pure_nf_star : forall x b, pure_nf b -> pure_nf (star x b)
with pure_ne : Term -> Prop :=
| pure_ne_ref : forall x, pure_ne (Ref x)
| pure_ne_app : forall n m, pure_ne n -> pure_nf m -> pure_ne (n @@ m).

Scheme pure_nf_mut := Induction for pure_nf Sort Prop
  with pure_ne_mut := Induction for pure_ne Sort Prop.

Lemma pure_invariants :
  forall t, pure_nf t -> ops_ok t /\ no_label t.
Proof.
  apply (pure_nf_mut (fun t _ => ops_ok t /\ no_label t)
                     (fun n _ => neutral n /\ ops_ok n /\ no_label n)).
  - intros n _ [_ H]; exact H.
  - intros x b _ [Hi Hn]; split; [apply star_inv|apply star_nolab]; auto.
  - intros x; repeat split; constructor.
  - intros n m _ [Hne [Hin Hnn]] _ [Him Hnm].
    split; [constructor; exact Hne|].
    split; [cbn; repeat split; auto; left; exact Hne|].
    cbn [no_label]; repeat split; auto.
    intros [u [v [E _]]]; inversion E; subst.
    inversion Hne as [|n' a' Hn' E']; subst; inversion Hn'.
Qed.


Local Opaque equal1.


Unset Default Proof Using.
Transparent dup_z bz retag equal get_wait equal1 Z get_tagged.

(**********************************************************************)
(*                Concrete Programs for Computable Functions           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(**********************************************************************)

(** Owner: [Terms].  Mu-recursive functions compiled to concrete
    programs.

    * Intended semantics

    Conjecture (the author's): every Turing-computable function, that is,
    every partial mu-recursive function, is represented by a _tag-free_
    program, one with no subtree of the tag shape [S2[K1 f, S2[K, K1 n]]].
    The semantic rationale is that tags are behaviourally useless: the
    label [S2[K, K1 n]] inside a tag is an identity, so a program never
    needs one.  This file proves the conjecture, in the stronger form
    that the programs are concrete (contain no label at all), for the
    standard mu-recursive basis of positive arity.

    - _Numerals_ are unary: [num n] is [Sm^n Lf].  The successor is the
      program [Lf] itself, since [Lf @ num n ==> num (S n)]; triage gives
      the zero test and the predecessor.

    - A function of arity [n] takes its [n] arguments by curried
      application: [apps P [x1; ...; xn]] is [P @ x1 @r ... @r xn].

    - _Syntax_ ([mu_fun n]) is indexed by the arity [n], which is always
      positive: a curried program is a value, and no value can stand for a
      divergent nullary computation.  The basis is zero (of every positive
      arity), successor, projections, composition, primitive recursion
      and minimisation.  _Semantics_ ([mu_eval f xs y]) is relational and
      partial; minimisation is the usual unbounded search, presented by
      the auxiliary relation [mu_search] (see [mu_search_spec]).

    - _Compilation_ ([compile]) builds trees directly, with no [star] and
      no tags.  Every arity-[S m] program is assembled from three
      combinator families: the constants [konst], the projections [proj],
      and the arity-indexed S-combinator [sapp m A B], which feeds the
      same [S m] arguments to [A] and [B] and applies the first result to
      the second.  Building trees directly, rather than by [star] over
      [Term]s with the compiled subprograms as constants, avoids [star]'s
      eta and [K]-optimisations, whose outputs depend on the shapes of
      those constants; the invariant is then checked on a handful of
      fixed tree contexts.  Recursion, for both primitive recursion and
      minimisation, uses the fixfunction [Z] of [terms]: the body takes
      the recursive program [self] as its first argument and dispatches
      by triage, so that the recursive call is only computed in the
      branch that needs it.

    - Theorem A ([compile_concrete], with corollary [compile_tag_free]):
      every compiled program is concrete, hence tag-free.  Tag-freeness
      does not compose ([K1 f] and the label are tag-free, [S2[K1 f, label]]
      is a tag), but concreteness does, provided no fork is built with
      operator [K] and a [K1]-shaped argument.  The combinators above
      never do so: their parameters occur only under [K1], under stems,
      or as the right component of a fork whose left component is not
      [K].  [Z f] is concrete whenever [f] is ([Z_preserves_concrete]).

    - Theorem B ([compile_sound]): if [mu_eval f xs y] then
      [apps (compile f) (map num xs) ==> num y].  The proof is by mutual
      induction on the evaluation derivation.  Because evaluation is
      eager, a full application evaluates only if all its prefixes do;
      the proof extracts the intermediate partial applications from the
      full derivations ([apps_app_inv]) rather than proving a separate
      termination property of partial applications. *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

Set Default Proof Using "Type".


(** * Numerals and curried application *)

Fixpoint num (n : nat) : Combination :=
  match n with
  | 0 => Lf
  | S n => Sm (num n)
  end.

(** [appe e xs] applies the expression [e] to the values [xs] in turn;
    [apps P xs] applies the value [P]. *)
Fixpoint appe (e : Combination) (xs : list Combination) : Combination :=
  match xs with
  | [] => e
  | x :: xs => appe (Fk e (Sm x)) xs
  end.

Definition apps (P : Combination) (xs : list Combination) := appe (Sm P) xs.

Lemma appe_app : forall xs ys e, appe e (xs ++ ys) = appe (appe e xs) ys.
Proof. induction xs as [|x xs IH]; intros ys e; cbn; auto. Qed.

(** [appe] respects "computes whatever". *)
Lemma appe_cong : forall xs e e', e ~~> e' -> appe e xs ~~> appe e' xs.
Proof.
  induction xs as [|x xs IH]; intros e e' He; cbn; auto.
  apply IH; intros v Hv.
  destruct (eval_pair_inv _ _ _ Hv) as [v1 [v2 [H1 [H2 H3]]]]; clear Hv.
  inv_out H2. eapply eval_pair; eauto with TreeHintDb.
Qed.

Lemma appe_intro :
  forall xs e w v, e ==> w -> appe (Sm w) xs ==> v -> appe e xs ==> v.
Proof.
  intros xs e w v Hw Hv; eapply appe_cong; [|exact Hv].
  intros u Hu; inv_out Hu; exact Hw.
Qed.

Lemma appe_inv :
  forall xs e v, appe e xs ==> v -> exists w, e ==> w /\ appe (Sm w) xs ==> v.
Proof.
  induction xs as [|x xs IH]; intros e v Hv; cbn in *.
  - exists v; split; auto with TreeHintDb.
  - destruct (IH _ _ Hv) as [w' [Hw' Hrest]]; clear Hv.
    destruct (eval_pair_inv _ _ _ Hw') as [v1 [v2 [H1 [H2 H3]]]]; clear Hw'.
    inv_out H2.
    exists v1; split; auto.
    eapply appe_cong; [|exact Hrest].
    intros u Hu; inv_out Hu; exact H3.
Qed.

Lemma apps_cons_intro :
  forall P x xs w v, P @ x ==> w -> apps w xs ==> v -> apps P (x :: xs) ==> v.
Proof. intros; unfold apps; cbn; eapply appe_intro; eauto. Qed.

Lemma apps_cons_inv :
  forall P x xs v, apps P (x :: xs) ==> v ->
  exists w, P @ x ==> w /\ apps w xs ==> v.
Proof. intros P x xs v H; unfold apps in H; cbn in H; apply appe_inv in H; exact H. Qed.

Lemma apps_app_intro :
  forall P xs ys w v, apps P xs ==> w -> apps w ys ==> v -> apps P (xs ++ ys) ==> v.
Proof.
  intros; unfold apps in *; rewrite appe_app; eapply appe_intro; eauto.
Qed.

Lemma apps_app_inv :
  forall P xs ys v, apps P (xs ++ ys) ==> v ->
  exists w, apps P xs ==> w /\ apps w ys ==> v.
Proof.
  intros P xs ys v H; unfold apps in *; rewrite appe_app in H.
  apply appe_inv in H; exact H.
Qed.

Lemma apps_nil_inv : forall P v, apps P [] ==> v -> v = P.
Proof. intros P v H; unfold apps in H; cbn in H; inv_out H; reflexivity. Qed.

Lemma apps_nil : forall P, apps P [] ==> P.
Proof. intros; apply eval_val. Qed.


(** * Combinators of arbitrary arity *)

(** [konst m c] ignores [m] arguments and returns [c]. *)
Fixpoint konst (m : nat) (c : Combination) : Combination :=
  match m with
  | 0 => c
  | S m => 'K1 (konst m c)
  end.

Lemma konst_eval : forall xs c, apps (konst (length xs) c) xs ==> c.
Proof.
  induction xs as [|x xs IH]; intros c; cbn [length konst].
  - apply apps_nil.
  - eapply apps_cons_intro; [apply eval_k | apply IH].
Qed.

Lemma konst_eval_n : forall n xs c, length xs = n -> apps (konst n c) xs ==> c.
Proof. intros n xs c <-; apply konst_eval. Qed.

(** [sel j] takes an argument [x], then ignores [j] arguments, and returns
    [x]: [sel j @ x ==> konst j x]. *)
Fixpoint sel (j : nat) : Combination :=
  match j with
  | 0 => 'I
  | S j => 'K 'C (sel j)
  end.

Lemma sel_step : forall j x, sel j @ x ==> konst j x.
Proof.
  induction j as [|j IH]; intros x; cbn [sel konst].
  - apply I_eval.
  - apply eval_c. eapply eval_arg_value; [apply IH | apply eval_to_fork].
Qed.

(** [proj i j] has arity [i + 1 + j] and returns its argument at position
    [i] (counting from 0). *)
Definition proj (i j : nat) := konst i (sel j).

Lemma proj_eval :
  forall ys x zs, apps (proj (length ys) (length zs)) (ys ++ x :: zs) ==> x.
Proof.
  intros ys x zs; unfold proj.
  eapply apps_app_intro; [apply konst_eval|].
  eapply apps_cons_intro; [apply sel_step | apply konst_eval].
Qed.

Lemma proj_eval_n :
  forall i j ys x zs, length ys = i -> length zs = j ->
  apps (proj i j) (ys ++ x :: zs) ==> x.
Proof. intros i j ys x zs <- <-; apply proj_eval. Qed.

(** [projs p n] lists the projections onto positions [p, ..., p+n-1] of
    an argument list of length [p + n]. *)
Fixpoint projs (p n : nat) : list Combination :=
  match n with
  | 0 => []
  | S n => proj p n :: projs (S p) n
  end.

Lemma projs_eval :
  forall xs pre,
    Forall2 (fun A a => apps A (pre ++ xs) ==> a)
            (projs (length pre) (length xs)) xs.
Proof.
  induction xs as [|x xs IH]; intros pre; cbn [length projs]; constructor.
  - apply proj_eval.
  - specialize (IH (pre ++ [x])).
    rewrite length_app, <- app_assoc in IH; cbn in IH.
    rewrite Nat.add_1_r in IH; exact IH.
Qed.

Lemma projs_eval_n :
  forall p n pre xs, length pre = p -> length xs = n ->
    Forall2 (fun A a => apps A (pre ++ xs) ==> a) (projs p n) xs.
Proof. intros p n pre xs <- <-; apply projs_eval. Qed.

(** The S-combinator of arity [S m].  [phi m] is the program that builds
    [sapp m a b] from [a] and [b]; [sapp m A B] feeds its [S m] arguments
    to both [A] and [B] and applies the first result to the second. *)
Fixpoint phi (m : nat) : Combination :=
  match m with
  | 0 => 'I
  | S m => Lf 'C (Lf 'C ('S1 ('K1 (phi m))))
  end.

Definition sapp (m : nat) (A B : Combination) := 'S2 ['S2 ['K1 (phi m), A], B].

Lemma phi_eval : forall m a, phi (S m) @ a ==> ('S1 ('S2 ['K1 (phi m), a])).
Proof. intros; cbn [phi]; evaluate. Qed.

Lemma sapp0_eval :
  forall A B x a b v,
    A @ x ==> a -> B @ x ==> b -> a @ b ==> v -> sapp 0 A B @ x ==> v.
Proof.
  intros A B x a b v Ha Hb Hv; unfold sapp; cbn [phi].
  apply eval_s. eapply eval_pair; [ | exact Hb | exact Hv].
  apply eval_s. eapply eval_pair; [ apply eval_k | exact Ha | apply I_eval].
Qed.

Lemma sappS_eval :
  forall m A B x a b,
    A @ x ==> a -> B @ x ==> b -> sapp (S m) A B @ x ==> sapp m a b.
Proof.
  intros m A B x a b Ha Hb; unfold sapp at 1.
  apply eval_s. eapply eval_pair; [ | exact Hb | apply eval_to_fork].
  apply eval_s. eapply eval_pair; [ apply eval_k | exact Ha | apply phi_eval].
Qed.

(** The S-combinator on a full argument list. *)
Lemma sapp_eval :
  forall m A B xs a b v,
    length xs = S m ->
    apps A xs ==> a -> apps B xs ==> b -> a @ b ==> v ->
    apps (sapp m A B) xs ==> v.
Proof.
  induction m as [|m IH]; intros A B xs a b v Hlen Ha Hb Hv;
    (destruct xs as [|x xs]; [discriminate|]); cbn in Hlen; injection Hlen; intros Hl; clear Hlen.
  - destruct xs; [|discriminate].
    apply apps_cons_inv in Ha as [a' [Ha1 Ha2]]; apply apps_nil_inv in Ha2; subst.
    apply apps_cons_inv in Hb as [b' [Hb1 Hb2]]; apply apps_nil_inv in Hb2; subst.
    eapply apps_cons_intro; [eapply sapp0_eval; eauto | apply apps_nil].
  - apply apps_cons_inv in Ha as [a' [Ha1 Ha2]].
    apply apps_cons_inv in Hb as [b' [Hb1 Hb2]].
    eapply apps_cons_intro; [eapply sappS_eval; eauto |].
    eapply IH; eauto.
Qed.

(** [appn m F [A1; ...; Ak]] applies [F] to [A1], ..., [Ak] pointwise over
    a shared list of [S m] arguments. *)
Definition appn (m : nat) (F : Combination) (As : list Combination) :=
  fold_left (fun acc A => sapp m acc A) As F.

Lemma appn_eval :
  forall m As vs F xs f v,
    length xs = S m ->
    apps F xs ==> f ->
    Forall2 (fun A a => apps A xs ==> a) As vs ->
    apps f vs ==> v ->
    apps (appn m F As) xs ==> v.
Proof.
  intros m As vs F xs f v Hlen HF HAs; revert F f HF.
  induction HAs as [|A a As vs HA HAs IH]; intros F f HF Hv; cbn [appn fold_left].
  - apply apps_nil_inv in Hv; subst; exact HF.
  - apply apps_cons_inv in Hv as [f' [Hf' Hv]].
    apply (IH (sapp m F A) f'); auto.
    eapply sapp_eval; eauto.
Qed.


(** * Recursion through [Z]

    A recursive body [B] takes the recursive program as its first
    argument: [Z B] applied to [x :: xs] behaves as [B] applied to
    [Z B :: x :: xs]. *)

Lemma Z_apps : forall B x xs v, apps B (Z B :: x :: xs) ==> v -> apps (Z B) (x :: xs) ==> v.
Proof.
  intros B x xs v H.
  apply (apps_app_inv B [Z B; x] xs) in H as [w [Hw Hv]].
  eapply apps_cons_intro; [apply Z_unfold; exact Hw | exact Hv].
Qed.


(** * Primitive recursion

    For [g] of arity [S k] and [h] of arity [k+3], the function [f] of
    arity [k+2] satisfies [f 0 xs = g xs] and
    [f (S y) xs = h y (f y xs) xs].  Its program is [Z (rec_body k G H)]
    where, given [self] and [y], the body dispatches by triage on [y]:
    a leaf selects [G]; a stem [Sm y'] selects [rec_T k H @ y' @ self],
    where [rec_T k H y' self xs = H y' (self y' xs) xs].  Forks are not
    numerals; they are mapped to [G]. *)

Definition rec_T (k : nat) (H : Combination) : Combination :=
  appn (S (S k)) (konst (S (S (S k))) H)
    (proj 0 (S (S k))
     :: appn (S (S k)) (proj 1 (S k)) (proj 0 (S (S k)) :: projs 2 (S k))
     :: projs 2 (S k)).

Definition rec_D (k : nat) (G H : Combination) : Combination :=
  'triage ['K1 G, rec_T k H, 'K1 ('K1 ('K1 G))].

Definition rec_body (k : nat) (G H : Combination) : Combination :=
  appn 1 (konst 2 (rec_D k G H)) [proj 1 0; proj 0 1].

Definition rec_prog (k : nat) (G H : Combination) := Z (rec_body k G H).

Lemma rec_T_eval :
  forall k H s y xs r v,
    length xs = S k ->
    apps s (y :: xs) ==> r ->
    apps H (y :: r :: xs) ==> v ->
    apps (rec_T k H) (y :: s :: xs) ==> v.
Proof.
  intros k H s y xs r v Hl Hs Hh; unfold rec_T.
  eapply appn_eval; [cbn; rewrite Hl; reflexivity | | | exact Hh].
  - apply konst_eval_n; cbn; rewrite Hl; reflexivity.
  - constructor; [apply (proj_eval_n 0 _ [] y (s :: xs)); cbn; auto; rewrite Hl; auto|].
    constructor.
    + eapply appn_eval; [cbn; rewrite Hl; reflexivity | | | exact Hs].
      * apply (proj_eval_n 1 _ [y] s xs); auto.
      * constructor; [apply (proj_eval_n 0 _ [] y (s :: xs)); cbn; auto; rewrite Hl; auto|].
        apply (projs_eval_n 2 (S k) [y; s] xs); auto.
    + apply (projs_eval_n 2 (S k) [y; s] xs); auto.
Qed.

Lemma rec_body_eval :
  forall k G H s y w,
    apps (rec_D k G H) [y; s] ==> w ->
    apps (rec_body k G H) [s; y] ==> w.
Proof.
  intros k G H s y w Hw; unfold rec_body.
  eapply appn_eval; [reflexivity | apply (konst_eval_n 2 [s; y]); reflexivity | | exact Hw].
  constructor; [apply (proj_eval_n 1 0 [s] y []); reflexivity|].
  constructor; [apply (proj_eval_n 0 1 [] s [y]); reflexivity|].
  constructor.
Qed.

Lemma rec_prog_zero :
  forall k G H xs v, apps G xs ==> v -> apps (rec_prog k G H) (Lf :: xs) ==> v.
Proof.
  intros k G H xs v Hv; unfold rec_prog; apply Z_apps.
  apply (apps_app_intro _ [Z (rec_body k G H); Lf] xs G); [|exact Hv].
  apply rec_body_eval; unfold rec_D; cbn; evaluate.
Qed.

Lemma rec_prog_succ :
  forall k G H y xs r v,
    length xs = S k ->
    apps (rec_prog k G H) (y :: xs) ==> r ->
    apps H (y :: r :: xs) ==> v ->
    apps (rec_prog k G H) (Sm y :: xs) ==> v.
Proof.
  intros k G H y xs r v Hl Hr Hh.
  pose proof (rec_T_eval k H _ _ _ _ _ Hl Hr Hh) as HT; clear Hr Hh.
  apply (apps_app_inv _ [y; rec_prog k G H] xs) in HT as [w [Hw Hv]].
  unfold rec_prog at 1; apply Z_apps.
  apply (apps_app_intro _ [Z (rec_body k G H); Sm y] xs w); [|exact Hv].
  apply rec_body_eval.
  apply apps_cons_inv in Hw as [t [Ht Hw]].
  eapply apps_cons_intro; [apply eval_stem; exact Ht | exact Hw].
Qed.


(** * Minimisation

    For [f] of arity [k+2], the search program [Z (min_body k F)] of
    arity [k+2] takes a candidate [z] and the arguments [xs].  Its body,
    given [self], [z] and [xs], first computes [F z xs] and dispatches by
    triage on the result: zero selects [min_ret], which returns [z]; a
    successor selects [min_rec], which continues with [self (S z) xs].
    The recursive call is therefore computed only when needed.  The
    minimisation program starts the search at [0]. *)

Definition min_ret (k : nat) := proj 1 (S k).

Definition min_rec (k : nat) : Combination :=
  appn (S (S k)) (proj 0 (S (S k)))
    (appn (S (S k)) (konst (S (S (S k))) Lf) [proj 1 (S k)] :: projs 2 (S k)).

Definition min_E (k : nat) : Combination :=
  'triage [min_ret k, 'K1 (min_rec k), 'K1 ('K1 (min_ret k))].

Definition min_test (k : nat) (F : Combination) : Combination :=
  appn (S (S k)) (konst (S (S (S k))) (min_E k))
    [appn (S (S k)) (konst (S (S (S k))) F) (proj 1 (S k) :: projs 2 (S k))].

Definition min_body (k : nat) (F : Combination) : Combination :=
  appn (S (S k)) (min_test k F)
    (proj 0 (S (S k)) :: proj 1 (S k) :: projs 2 (S k)).

Definition min_search_prog (k : nat) (F : Combination) := Z (min_body k F).

Definition min_prog (k : nat) (F : Combination) : Combination :=
  appn k (konst (S k) (min_search_prog k F)) (konst (S k) Lf :: projs 0 (S k)).

Lemma min_body_eval :
  forall k F s z xs fr e v,
    length xs = S k ->
    apps F (z :: xs) ==> fr ->
    min_E k @ fr ==> e ->
    apps e (s :: z :: xs) ==> v ->
    apps (min_body k F) (s :: z :: xs) ==> v.
Proof.
  intros k F s z xs fr e v Hl HF HE Hv; unfold min_body.
  assert (Hl3 : length (s :: z :: xs) = S (S (S k))) by (cbn; rewrite Hl; reflexivity).
  eapply appn_eval; [exact Hl3 | | | exact Hv].
  - unfold min_test; eapply appn_eval; [exact Hl3 | apply konst_eval_n; exact Hl3 | |].
    + constructor; [|constructor].
      eapply appn_eval; [exact Hl3 | apply konst_eval_n; exact Hl3 | | exact HF].
      constructor; [apply (proj_eval_n 1 _ [s] z xs); auto|].
      apply (projs_eval_n 2 (S k) [s; z] xs); auto.
    + eapply apps_cons_intro; [exact HE | apply apps_nil].
  - constructor; [apply (proj_eval_n 0 _ [] s (z :: xs)); cbn; auto; rewrite Hl; auto|].
    constructor; [apply (proj_eval_n 1 _ [s] z xs); auto|].
    apply (projs_eval_n 2 (S k) [s; z] xs); auto.
Qed.

Lemma min_found :
  forall k F z xs,
    length xs = S k -> apps F (z :: xs) ==> Lf ->
    apps (min_search_prog k F) (z :: xs) ==> z.
Proof.
  intros k F z xs Hl HF; unfold min_search_prog; apply Z_apps.
  eapply min_body_eval; [exact Hl | exact HF | apply eval_leaf |].
  apply (proj_eval_n 1 _ [_] z xs); auto.
Qed.

Lemma min_next :
  forall k F z r xs v,
    length xs = S k -> apps F (z :: xs) ==> Sm r ->
    apps (min_search_prog k F) (Sm z :: xs) ==> v ->
    apps (min_search_prog k F) (z :: xs) ==> v.
Proof.
  intros k F z r xs v Hl HF Hv; unfold min_search_prog at 1; apply Z_apps.
  eapply min_body_eval; [exact Hl | exact HF | apply eval_stem, eval_k |].
  unfold min_rec.
  eapply appn_eval; [cbn; rewrite Hl; reflexivity | | | exact Hv].
  - apply (proj_eval_n 0 _ [] _ (z :: xs)); cbn; auto; rewrite Hl; auto.
  - constructor.
    + eapply appn_eval; [cbn; rewrite Hl; reflexivity | apply konst_eval_n; cbn; rewrite Hl; reflexivity
                        | | ].
      * constructor; [apply (proj_eval_n 1 _ [_] z xs); auto | constructor].
      * eapply apps_cons_intro; [apply eval_to_stem | apply apps_nil].
    + apply (projs_eval_n 2 (S k) [_; z] xs); auto.
Qed.

Lemma min_prog_eval :
  forall k F xs v,
    length xs = S k ->
    apps (min_search_prog k F) (Lf :: xs) ==> v ->
    apps (min_prog k F) xs ==> v.
Proof.
  intros k F xs v Hl Hv; unfold min_prog.
  eapply appn_eval; [exact Hl | apply konst_eval_n; exact Hl | | exact Hv].
  constructor; [apply konst_eval_n; exact Hl|].
  apply (projs_eval_n 0 (S k) [] xs); auto.
Qed.


(** * Mu-recursive functions

    [mu_fun n] is the syntax of functions of arity [n]; every arity is
    positive.  [mu_proj i j] has arity [i + 1 + j] and returns the
    argument at position [i].  [mu_comp k m h gs] composes [h] (arity
    [S m]) with [S m] functions [gs] of arity [S k].  [mu_rec k g h] is
    defined by primitive recursion on its first argument, and
    [mu_min k f] searches for the least first argument of [f] at which
    [f] returns 0. *)

Inductive mu_fun : nat -> Type :=
| mu_zero : forall k, mu_fun (S k)
| mu_succ : mu_fun 1
| mu_proj : forall i j, mu_fun (S (i + j))
| mu_comp : forall k m, mu_fun (S m) -> mu_funs (S k) (S m) -> mu_fun (S k)
| mu_rec : forall k, mu_fun (S k) -> mu_fun (S (S (S k))) -> mu_fun (S (S k))
| mu_min : forall k, mu_fun (S (S k)) -> mu_fun (S k)
with mu_funs : nat -> nat -> Type :=
| mu_nil : forall n, mu_funs n 0
| mu_cons : forall n m, mu_fun n -> mu_funs n m -> mu_funs n (S m).

(** Relational, partial semantics.  [mu_search k f xs z y] says that the
    search for a zero of [f _ xs], started at [z], halts with [y]: every
    candidate from [z] below [y] gives a successor, and [y] gives zero. *)

Inductive mu_eval : forall n, mu_fun n -> list nat -> nat -> Prop :=
| ev_zero : forall k xs, length xs = S k -> mu_eval (S k) (mu_zero k) xs 0
| ev_succ : forall x, mu_eval 1 mu_succ [x] (S x)
| ev_proj : forall i j ys x zs,
    length ys = i -> length zs = j ->
    mu_eval (S (i + j)) (mu_proj i j) (ys ++ x :: zs) x
| ev_comp : forall k m h gs xs ys v,
    mu_evals (S k) (S m) gs xs ys -> mu_eval (S m) h ys v ->
    mu_eval (S k) (mu_comp k m h gs) xs v
| ev_rec_zero : forall k g h xs v,
    mu_eval (S k) g xs v -> mu_eval (S (S k)) (mu_rec k g h) (0 :: xs) v
| ev_rec_succ : forall k g h y xs r v,
    mu_eval (S (S k)) (mu_rec k g h) (y :: xs) r ->
    mu_eval (S (S (S k))) h (y :: r :: xs) v ->
    mu_eval (S (S k)) (mu_rec k g h) (S y :: xs) v
| ev_min : forall k f xs y,
    mu_search k f xs 0 y -> mu_eval (S k) (mu_min k f) xs y
with mu_evals : forall n m, mu_funs n m -> list nat -> list nat -> Prop :=
| evs_nil : forall n xs, mu_evals n 0 (mu_nil n) xs []
| evs_cons : forall n m g gs xs y ys,
    mu_eval n g xs y -> mu_evals n m gs xs ys ->
    mu_evals n (S m) (mu_cons n m g gs) xs (y :: ys)
with mu_search : forall k, mu_fun (S (S k)) -> list nat -> nat -> nat -> Prop :=
| search_found : forall k f xs z,
    mu_eval (S (S k)) f (z :: xs) 0 -> mu_search k f xs z z
| search_next : forall k f xs z r y,
    mu_eval (S (S k)) f (z :: xs) (S r) -> mu_search k f xs (S z) y ->
    mu_search k f xs z y.

Scheme mu_eval_ind2 := Induction for mu_eval Sort Prop
  with mu_evals_ind2 := Induction for mu_evals Sort Prop
  with mu_search_ind2 := Induction for mu_search Sort Prop.
Combined Scheme mu_eval_mutind from mu_eval_ind2, mu_evals_ind2, mu_search_ind2.

(** [mu_search] is the usual unbounded search. *)
Lemma mu_search_spec :
  forall k f xs z y,
    mu_search k f xs z y <->
    z <= y /\ mu_eval (S (S k)) f (y :: xs) 0 /\
    (forall w, z <= w < y -> exists r, mu_eval (S (S k)) f (w :: xs) (S r)).
Proof.
  intros k f xs z y; split.
  - intros H; induction H as [k f xs z H0 | k f xs z r y Hr Hs IH].
    + split; [lia | split; [exact H0 | intros w Hw; lia]].
    + destruct IH as [Hle [H0 Hlt]]; split; [lia | split; [exact H0|]].
      intros w Hw; destruct (Nat.eq_dec w z) as [->|Hne]; [eauto|].
      apply Hlt; lia.
  - intros [Hle [H0 Hlt]].
    remember (y - z) as d eqn:Hd; revert z Hle Hlt Hd.
    induction d as [|d IH]; intros z Hle Hlt Hd.
    + assert (z = y) by lia; subst; apply search_found; exact H0.
    + destruct (Hlt z) as [r Hr]; [lia|].
      eapply search_next; [exact Hr|].
      apply IH; [lia | intros w Hw; apply Hlt; lia | lia].
Qed.


(** * Compilation *)

Fixpoint compile {n} (f : mu_fun n) {struct f} : Combination :=
  match f with
  | mu_zero k => konst (S k) Lf
  | mu_succ => Lf
  | mu_proj i j => proj i j
  | mu_comp k m h gs => appn k (konst (S k) (compile h)) (compiles gs)
  | mu_rec k g h => rec_prog k (compile g) (compile h)
  | mu_min k f => min_prog k (compile f)
  end
with compiles {n m} (gs : mu_funs n m) {struct gs} : list Combination :=
  match gs with
  | mu_nil _ => []
  | mu_cons _ _ g gs => compile g :: compiles gs
  end.


(** * Theorem B: compiled programs compute their functions *)

Lemma compile_sound_all :
  (forall n f xs v, mu_eval n f xs v ->
     length xs = n /\ apps (compile f) (map num xs) ==> num v) /\
  (forall n m gs xs ys, mu_evals n m gs xs ys ->
     (m = 0 \/ length xs = n) /\
     Forall2 (fun G w => apps G (map num xs) ==> w) (compiles gs) (map num ys)) /\
  (forall k f xs z y, mu_search k f xs z y ->
     length xs = S k /\
     apps (min_search_prog k (compile f)) (num z :: map num xs) ==> num y).
Proof.
  apply (mu_eval_mutind
    (fun n f xs v _ => length xs = n /\ apps (compile f) (map num xs) ==> num v)
    (fun n m gs xs ys _ => (m = 0 \/ length xs = n) /\
       Forall2 (fun G w => apps G (map num xs) ==> w) (compiles gs) (map num ys))
    (fun k f xs z y _ => length xs = S k /\
       apps (min_search_prog k (compile f)) (num z :: map num xs) ==> num y));
    cbn [compile compiles].
  - (* zero *)
    intros k xs Hl; split; [exact Hl|].
    apply konst_eval_n; rewrite length_map; exact Hl.
  - (* successor *)
    intros x; split; [reflexivity|]; cbn.
    apply eval_to_stem.
  - (* projection *)
    intros i j ys x zs Hy Hz; split.
    + rewrite length_app; cbn; lia.
    + rewrite map_app; cbn.
      apply proj_eval_n; rewrite length_map; auto.
  - (* composition *)
    intros k m h gs xs ys v _ [[Hm|Hl] Hgs] _ [_ Hh]; [discriminate|].
    split; [exact Hl|].
    eapply appn_eval; [rewrite length_map; exact Hl
                      | apply konst_eval_n; rewrite length_map; exact Hl
                      | exact Hgs | exact Hh].
  - (* primitive recursion, zero *)
    intros k g h xs v _ [Hl Hg]; split; [cbn; rewrite Hl; reflexivity|]; cbn [map num].
    apply rec_prog_zero; exact Hg.
  - (* primitive recursion, successor *)
    intros k g h y xs r v _ [Hl Hr] _ [_ Hh]; split; [exact Hl|].
    cbn [map num length] in *; injection Hl; intros Hl'; clear Hl.
    eapply rec_prog_succ; [rewrite length_map; exact Hl' | exact Hr | exact Hh].
  - (* minimisation *)
    intros k f xs y _ [Hl Hs]; split; [exact Hl|].
    apply min_prog_eval; [rewrite length_map; exact Hl | exact Hs].
  - (* no functions *)
    intros n xs; split; [left; reflexivity | constructor].
  - (* one more function *)
    intros n m g gs xs y ys _ [Hl Hg] _ [_ Hgs]; split; [right; exact Hl|].
    constructor; auto.
  - (* search succeeds *)
    intros k f xs z _ [Hl Hf]; cbn [map num length] in *; injection Hl; intros Hl'; clear Hl.
    split; [exact Hl'|].
    apply min_found; [rewrite length_map; exact Hl' | exact Hf].
  - (* search continues *)
    intros k f xs z r y _ [Hl Hf] _ [_ Hs]; cbn [map num length] in *; injection Hl; intros Hl'; clear Hl.
    split; [exact Hl'|].
    eapply min_next; [rewrite length_map; exact Hl' | exact Hf | exact Hs].
Qed.

Lemma compile_sound :
  forall n (f : mu_fun n) xs y,
    mu_eval n f xs y -> apps (compile f) (map num xs) ==> num y.
Proof. intros n f xs y H; apply (proj1 compile_sound_all) in H; tauto. Qed.


(** * Theorem A: compiled programs are concrete, hence tag-free

    A fork [Fk u v] of concrete trees is concrete unless [u] is
    [K] and [v] has the shape [K1 n].  Every fork built below has an
    operator other than [K], except in [I], whose argument is [K]. *)

Lemma lf_fork :
  forall u v, concrete u -> concrete v -> u <> Sm (Sm Lf) ->
  concrete (Fk u v).
Proof. setoid_rewrite concrete_iff_rules; intros u v Hu Hv Hne; cbn; repeat split; auto; intros [E _]; contradiction. Qed.

Lemma lf_stem : forall u, concrete u -> concrete (Sm u).
Proof. setoid_rewrite concrete_iff_rules; intros u Hu; exact Hu. Qed.

Lemma lf_leaf : concrete Lf.
Proof. apply concrete_iff_rules; exact I. Qed.

Lemma lf_I : concrete 'I.
Proof. apply concrete_iff_rules; cbn; repeat split; auto; intros [_ [n E]]; discriminate. Qed.

Ltac lf_tac :=
  repeat match goal with
    | |- concrete Lf => exact lf_leaf
    | H : concrete ?c |- concrete ?c => exact H
    | |- concrete 'I => apply lf_I
    | |- concrete (Sm _) => apply lf_stem
    | |- concrete (Fk _ _) => apply lf_fork; [ | | discriminate ]
    end.

(** ** Run-time labels and pattern testers are concrete *)

Lemma label_not_concrete : forall n, ~ concrete ('label[n]).
Proof. setoid_rewrite concrete_iff_rules; intros n [H _]; apply H; split; eauto. Qed.


Lemma tagger_concrete : forall n, concrete n -> concrete ('tagger[n]).
Proof. intros n Hn; lf_tac. Qed.
