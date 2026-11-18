(** * Step 82, stage 3: the plain translation of lambda terms (paper section 4.2).

    A pure named lambda term translates to an expression: an abstraction is
    a quoted program built by plain bracket abstraction,
    tr (\x.M) = Sm (prog x M), and an application is an expression node,
    tr (M N) = Fk (tr M) (tr N).  Every term translates to a concrete tree.
    (Ported unchanged from src_type36; only the example is redone.) *)
From Stdlib Require Import String List Arith Bool.
From BigStep Require Import tree typing booleans self_typing.
Open Scope string_scope.
Set Default Proof Using "Type".
(** Pure named lambda terms. *)
Inductive Lam : Set :=
| LV : string -> Lam
| LA : Lam -> Lam -> Lam
| LL : string -> Lam -> Lam.

(** Programs with free variables: trees built from K1 and S2 over
    variables and closed trees. *)
Inductive P : Set :=
| PV : string -> P
| PC : Combination -> P
| PK1 : P -> P
| PS2 : P -> P -> P.

Fixpoint to_comb (p : P) : Combination :=
  match p with
  | PV _ => Lf                       (* junk; absent from closed terms *)
  | PC c => c
  | PK1 a => 'K1 (to_comb a)
  | PS2 a b => 'S2 [to_comb a, to_comb b]
  end.

(** Uniform plain abstraction over a program:
    [x]x = I, [x]y = K1 y, [x]c = K1 c,
    [x](K1 a) = [x](K a)          = S2[K1 K, [x]a],
    [x](S2[a,b]) = [x](Lf (Lf a) b) = S2[S2[K1 Lf, S2[K1 Lf, [x]a]], [x]b]. *)
Fixpoint absP (x : string) (p : P) : P :=
  match p with
  | PV y => if String.eqb x y then PC 'I else PK1 (PV y)
  | PC c => PC ('K1 c)
  | PK1 a => PS2 (PC ('K1 'K)) (absP x a)
  | PS2 a b => PS2 (PS2 (PC ('K1 Lf)) (PS2 (PC ('K1 Lf)) (absP x a))) (absP x b)
  end.

(** Uniform plain abstraction over a lambda body:
    [x]x = I, [x]y = K1 y, [x](M N) = S2[[x]M, [x]N], [x](\y.N) = [x]([y]N). *)
Fixpoint absL (x : string) (M : Lam) : P :=
  match M with
  | LV y => if String.eqb x y then PC 'I else PK1 (PV y)
  | LA M1 M2 => PS2 (absL x M1) (absL x M2)
  | LL y N => absP x (absL y N)
  end.

(** The translation to expressions: an abstraction is a quoted value
    (its program), an application is an expression node. *)
Fixpoint tr (t : Lam) : Combination :=
  match t with
  | LV _ => Lf                       (* junk; absent from closed terms *)
  | LA M N => Fk (tr M) (tr N)
  | LL x M => Sm (to_comb (absL x M))
  end.

Definition prog (x : string) (M : Lam) := to_comb (absL x M).

(** ** Shape: every abstraction yields a fork, never [K]. *)
Ltac cr_tac :=
  cbn; repeat match goal with
  | |- _ /\ _ => split
  | |- ~ _ => let E1 := fresh in let n := fresh in let E2 := fresh in
               intros [E1 [n E2]]; discriminate
  | |- True => exact I
  end; auto.

Definition is_fork (c : Combination) : Prop := exists a b, c = Fk a b.

Lemma absP_fork : forall x p, is_fork (to_comb (absP x p)).
Proof.
  intros x p; destruct p as [y|c|a|a b]; cbn [absP to_comb];
    try destruct (String.eqb x y); cbn [to_comb]; eexists; eexists; reflexivity.
Qed.

Lemma absL_fork : forall x M, is_fork (to_comb (absL x M)).
Proof.
  intros x M; destruct M as [y|M1 M2|y N]; cbn [absL].
  - destruct (String.eqb x y); cbn; eexists; eexists; reflexivity.
  - cbn; eexists; eexists; reflexivity.
  - apply absP_fork.
Qed.

(** ** Concreteness, by the rules. *)
Lemma absP_concrete : forall x p,
  concrete_rules (to_comb p) -> concrete_rules (to_comb (absP x p)).
Proof.
  intros x p; induction p as [y|c|a IH|a IHa b IHb]; cbn [absP to_comb]; intros H.
  - destruct (String.eqb x y); cbn; cr_tac.
  - cr_tac.
  - cbn in H; destruct H as [_ [_ Ha]].
    cr_tac.
  - cbn in H; destruct H as [_ [Ha Hb]].
    cr_tac.
Qed.

Lemma absL_concrete : forall x M, concrete_rules (to_comb (absL x M)).
Proof.
  intros x M; revert x; induction M as [y|M1 IH1 M2 IH2|y N IH]; intros x; cbn [absL].
  - destruct (String.eqb x y); cr_tac.
  - cbn [to_comb concrete_rules]; split; [|split; [apply IH1|apply IH2]].
    intros [E _]; injection E as E.
    destruct (absL_fork x M1) as [a [b Hab]]; rewrite Hab in E; discriminate.
  - apply absP_concrete, IH.
Qed.

Lemma tr_concrete_rules : forall t, concrete_rules (tr t).
Proof.
  induction t as [y|M IHM N IHN|x M IH]; cbn [tr].
  - exact I.
  - cbn [concrete_rules]; split; [|split; [apply IHM|apply IHN]].
    intros [E _]; destruct M as [| |z B]; cbn [tr] in E; try discriminate.
    injection E as E; destruct (absL_fork z B) as [a [b Hab]];
      rewrite Hab in E; discriminate.
  - cbn; apply absL_concrete.
Qed.

(** Every pure lambda term (closed or not) translates to a concrete tree. *)
Theorem plain_translation_concrete : forall t, concrete (tr t).
Proof. intros t; apply concrete_iff_rules, tr_concrete_rules. Qed.

(** An abstraction translates to a quoted concrete program
    (no beta-normality needed). *)
Theorem plain_translation_program : forall x M,
  tr (LL x M) = Sm (prog x M) /\ concrete (prog x M).
Proof.
  intros x M; split; [reflexivity|].
  apply concrete_iff_rules, absL_concrete.
Qed.

(** ** An example: a redex and its value have the same type. *)
Definition tKy := LL "y" (LL "z" (LV "y")).
Definition tW := LL "w" (LV "w").
Definition t_redex := LA tKy tW.   (* (\y.\z.y)(\w.w) *)

Lemma redex_typed :
  infer_expression O_ex @ tr t_redex ==> Sm ('KI) /\ infer O_ex @ 'KI ==> Sm ('KI).
Proof.
  split.
  - apply (runp_sound 40); vm_done.
  - apply concrete_is_self_typed; vm_compute; reflexivity.
Qed.
