(** * Step 82 (stage 1): soundness, with labels as abstract types.

    For an ontology [O]:
    - a declaration [D] at [n] is sound by typing when every carrier type
      admitted by its guard applies as its eliminator says
      ([decl_sound_by_typing]);
    - it is sound by values when an admitted carrier, applied to a value
      of the argument type, gives a value of the type the eliminator
      promises, assuming soundness of application up to that evaluation
      ([decl_sound]);
    - the ontology is sound (by typing, by values) when every declaration
      it gives is.

    Soundness of type application ([tp_sound]) is proved by strong
    induction on the height of the evaluation of [f @ u]; evaluation
    preserves typing ([evaluation_preserves_typing], [ept_by_typing]) then
    follows by induction on the expression.  A typed expression never
    evaluates to a bare label ([no_runtime_label]). *)

From Stdlib Require Import Arith Lia.
From BigStep Require Import tree typing.
Set Default Proof Using "Type".

(** ** Height-indexed evaluation *)

Inductive evaln : nat -> Combination -> Combination -> Prop :=
| evaln_val : forall n v,
    evaln (S n) (Sm v) v
| evaln_appl : forall n e11 e12 e2 v1 v,
    evaln n (Fk e11 e12) v1 ->
    evaln n (Fk (Sm v1) e2) v ->
    evaln (S n) (Fk (Fk e11 e12) e2) v
| evaln_appr : forall n v1 e21 e22 v2 v,
    evaln n (Fk e21 e22) v2 ->
    evaln n (Fk (Sm v1) (Sm v2)) v ->
    evaln (S n) (Fk (Sm v1) (Fk e21 e22)) v
| evaln_to_stem : forall n v2,
    evaln (S n) (Fk (Sm Lf) (Sm v2)) (Sm v2)
| evaln_to_fork : forall n v1 v2,
    evaln (S n) (Fk (Sm (Sm v1)) (Sm v2)) (Fk v1 v2)
| evaln_k : forall n v1 v2,
    evaln (S n) (Fk (Sm (Fk Lf v1)) (Sm v2)) v1
| evaln_s : forall n g f v2 v,
    evaln n (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2))) v ->
    evaln (S n) (Fk (Sm (Fk (Sm g) f)) (Sm v2)) v
| evaln_leaf : forall n f0 f1 f2,
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm Lf)) f0
| evaln_stem : forall n f0 f1 f2 v2 v,
    evaln n (Fk (Sm f1) (Sm v2)) v ->
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm (Sm v2))) v
| evaln_fork : forall n f0 f1 f2 v21 v22 v,
    evaln n (Fk (Fk (Sm f2) (Sm v21)) (Sm v22)) v ->
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm (Fk v21 v22))) v.

Lemma evaln_mono : forall n e v, evaln n e v -> forall m, n <= m -> evaln m e v.
Proof.
  intros n e v H; induction H; intros m Hm;
    (destruct m as [|m]; [lia|]);
    econstructor; try apply IHevaln; try apply IHevaln1; try apply IHevaln2; lia.
Qed.

Lemma evaln_eval : forall n e v, evaln n e v -> e ==> v.
Proof. intros n e v H; induction H; econstructor; eauto. Qed.

Lemma eval_evaln : forall e v, e ==> v -> exists n, evaln n e v.
Proof.
  intros e v H; induction H;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    try (exists 1; constructor; fail).
  all: try (exists (S x); constructor; assumption).
  all: exists (S (Nat.max x x0));
    first [eapply evaln_appl | eapply evaln_appr];
    eapply evaln_mono; eauto; lia.
Qed.

(** *** Height-aware inversions at value applications *)

Lemma evaln_S2_inv : forall k g h u w, evaln k ('S2[g,h] @ u) w ->
  exists j a b, j < k /\ evaln j (g @ u) a /\ evaln j (h @ u) b /\ evaln j (a @ b) w.
Proof.
  intros k g h u w H; inversion H; subst.
  match goal with H1 : evaln _ (Fk (Fk _ _) _) _ |- _ => inversion H1; subst end.
  match goal with H1 : evaln _ (Fk (Sm _) (Fk _ _)) _ |- _ => inversion H1; subst end.
  match goal with Ha : evaln ?m (g @ u) ?a, Hb : evaln _ (h @ u) ?b, Hw : evaln _ (?a @ ?b) w |- _ =>
    exists m, a, b end.
  repeat split; [lia| | |]; (eapply evaln_mono; [eassumption|lia]).
Qed.

Lemma evaln_stem_inv : forall k f0 f1 f2 x w, evaln k ('triage[f0,f1,f2] @ Sm x) w ->
  exists j, j < k /\ evaln j (f1 @ x) w.
Proof. intros k f0 f1 f2 x w H; inversion H; subst; eexists; split; [|eassumption]; lia. Qed.

Lemma evaln_fork_inv : forall k f0 f1 f2 x1 x2 w, evaln k ('triage[f0,f1,f2] @ Fk x1 x2) w ->
  exists j a, j < k /\ evaln j (f2 @ x1) a /\ evaln j (a @ x2) w.
Proof.
  intros k f0 f1 f2 x1 x2 w H; inversion H; subst.
  match goal with H1 : evaln _ (Fk (Fk _ _) _) _ |- _ => inversion H1; subst end.
  match goal with Ha : evaln ?m (f2 @ x1) ?a |- _ => exists m, a end.
  repeat split; [lia| |]; (eapply evaln_mono; [eassumption|lia]).
Qed.

Lemma label_app : forall n u, 'label[n] @ u ==> u.
Proof. intros; evaluate. Qed.

(** Applying a tag applies its carrier, at a smaller height. *)
Lemma evaln_tagged_inv : forall k c n u w, evaln k ('tagged[c,n] @ u) w ->
  exists j, j < k /\ evaln j (c @ u) w.
Proof.
  intros k c n u w H; destruct (evaln_S2_inv _ _ _ _ _ H) as [j [a [b [Hj [Ha [Hb Hw]]]]]].
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ Ha) _ (eval_k c u)) as ->.
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ Hb) _ (label_app n u)) as ->.
  exists j; split; assumption.
Qed.

(** ** Sound ontologies *)

Section Soundness.
Variable O : Combination.
Local Notation "t ':' T" := (infer O @ t ==> Sm T) (at level 70).
Local Notation "F # U" := (tp O @ F @r U) (at level 45, left associativity).

(** Soundness of application for evaluations of height at most [k]. *)
Definition app_sound_upto (k : nat) : Prop :=
  forall j f u w F U R, j <= k -> evaln j (f @ u) w -> f : F -> u : U -> F # U ==> Sm R -> w : R.

(** Soundness by typing (paper Fig. 7, first form). *)
Definition decl_sound_by_typing (n D : Combination) : Prop :=
  forall C U V, guard_of @ D @r C ==> 'K -> elim_of @ D @r n @r tp O @r U ==> Sm V -> C # U ==> Sm V.

Definition ontology_sound_by_typing : Prop :=
  forall n D, O @ n @r tp O ==> Sm D -> decl_sound_by_typing n D.

(** Soundness by values (paper Fig. 7, second form). *)
Definition decl_sound (n D : Combination) : Prop :=
  forall k C U V c v w, guard_of @ D @r C ==> 'K -> elim_of @ D @r n @r tp O @r U ==> Sm V ->
    c : C -> v : U -> app_sound_upto k -> evaln k (c @ v) w -> w : V.

Definition ontology_sound : Prop :=
  forall n D, O @ n @r tp O ==> Sm D -> decl_sound n D.

Lemma decl_sound_by_typing_values : forall n D, decl_sound_by_typing n D -> decl_sound n D.
Proof.
  intros n D HD k C U V c v w HC HE Hc Hv Hk Hw.
  exact (Hk k c v w C U V (le_n k) Hw Hc Hv (HD C U V HC HE)).
Qed.

Theorem ontology_sound_by_typing_values : ontology_sound_by_typing -> ontology_sound.
Proof. intros H n D HD; apply decl_sound_by_typing_values, H, HD. Qed.

(** *** Soundness of type application *)

Lemma not_tag_of_typed : forall g u U, u : U -> tag_of (Fk g u) = None.
Proof.
  intros g u U Hu; destruct (tag_of (Fk g u)) as [[c m]|] eqn:E; [|reflexivity].
  apply tag_of_some in E; inversion E; subst.
  exfalso; exact (bare_label_untyped O m U Hu).
Qed.

Lemma app_sound_step : ontology_sound -> forall k, (forall j, j < k -> app_sound_upto j) ->
  forall f u w F U R, evaln k (f @ u) w -> f : F -> u : U -> F # U ==> Sm R -> w : R.
Proof.
  intros HO k IH f u w F U R Hev Hf Hu HR.
  assert (IHj : forall j f u w F U R, j < k -> evaln j (f @ u) w -> f : F -> u : U -> F # U ==> Sm R -> w : R)
    by (intros j f' u' w' F' U' R' Hj; exact (IH j Hj j f' u' w' F' U' R' (le_n j))).
  apply tp_inv in HR; destruct HR as
    [n U0 D R0 HD HE | U0 | G U0 HL | Y U0 | G H U0 V W R0 HLS HG HH HVW
    | F0 F1 F2 Hres | F0 F1 F2 X R0 Hres H1 | F0 F1 F2 X Y G R0 Hres HLU H2 HG].
  - (* abstract type *)
    destruct (no_junk O f n Hf) as [c [C [D' [-> [_ [Hc [HD' HC]]]]]]].
    pose proof (eval_deterministic _ _ HD _ HD') as E; inversion E; subst; clear E.
    destruct (evaln_tagged_inv _ _ _ _ _ Hev) as [j [Hj Hcu]].
    exact (HO n D' HD' j C U0 R0 c u w HC HE Hc Hu (IH j Hj) Hcu).
  - (* leaf *)
    pose proof (type_Lf_inv O f Hf) as ->.
    inversion Hev; subst; apply infer_stem; exact Hu.
  - (* stem *)
    destruct (type_Sm_inv O f G Hf) as [g [-> Hg]].
    inversion Hev; subst.
    apply infer_fork; auto. eapply not_tag_of_typed; exact Hu.
  - (* K1 *)
    destruct (type_Fk_inv O f Lf Y Hf) as [[m E]|[u1 [y [-> [_ [H1 [Hy _]]]]]]]; [discriminate|].
    pose proof (type_Lf_inv O u1 H1) as ->.
    inversion Hev; subst; exact Hy.
  - (* S2 *)
    destruct (type_Fk_inv O f (Sm G) H Hf) as [[m E]|[u1 [h [-> [_ [H1 [Hh _]]]]]]];
      [rewrite E in HLS; cbn in HLS; discriminate|].
    destruct (type_Sm_inv O u1 G H1) as [g [-> Hg]].
    destruct (evaln_S2_inv _ _ _ _ _ Hev) as [j [a [b [Hj [Ha [Hb Hw]]]]]].
    exact (IHj j a b w V W R0 Hj Hw (IHj j g u a G U0 V Hj Ha Hg Hu HG)
             (IHj j h u b H U0 W Hj Hb Hh Hu HH) HVW).
  - (* triage, leaf argument *)
    destruct (type_Fk_inv O f (Fk F0 F1) F2 Hf) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
    destruct (type_Fk_inv O x F0 F1 Hx) as [[m E]|[f0 [f1 [-> [_ [H0 [H1' _]]]]]]];
      [rewrite E in Hres; cbn in Hres; discriminate|].
    pose proof (type_Lf_inv O u Hu) as ->.
    inversion Hev; subst; exact H0.
  - (* triage, stem argument *)
    destruct (type_Fk_inv O f (Fk F0 F1) F2 Hf) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
    destruct (type_Fk_inv O x F0 F1 Hx) as [[m E]|[f0 [f1 [-> [_ [H0 [H1' _]]]]]]];
      [rewrite E in Hres; cbn in Hres; discriminate|].
    destruct (type_Sm_inv O u X Hu) as [x [-> Hx']].
    destruct (evaln_stem_inv _ _ _ _ _ _ Hev) as [j [Hj Hw]].
    exact (IHj j f1 x w F1 X R0 Hj Hw H1' Hx' H1).
  - (* triage, fork argument *)
    destruct (type_Fk_inv O f (Fk F0 F1) F2 Hf) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
    destruct (type_Fk_inv O x F0 F1 Hx) as [[m E]|[f0 [f1 [-> [_ [H0 [H1' _]]]]]]];
      [rewrite E in Hres; cbn in Hres; discriminate|].
    destruct (type_Fk_inv O u X Y Hu) as [[m E]|[x1 [x2 [-> [_ [Hx1 [Hx2 _]]]]]]];
      [rewrite E in HLU; cbn in HLU; discriminate|].
    destruct (evaln_fork_inv _ _ _ _ _ _ _ Hev) as [j [a [Hj [Ha Hw]]]].
    exact (IHj j a x2 w G Y R0 Hj Hw (IHj j y x1 a F2 X G Hj Ha Hy Hx1 H2) Hx2 HG).
Qed.

Lemma app_sound_all : ontology_sound -> forall k, app_sound_upto k.
Proof.
  intros HO k; induction k as [k IH] using lt_wf_ind.
  intros j f u w F U R Hj Hev Hf Hu HR.
  refine (app_sound_step HO j _ f u w F U R Hev Hf Hu HR).
  intros i Hi; apply IH; lia.
Qed.

(** Soundness of type application: applying a value of type [F] to a
    value of type [U] gives a value of type [F # U]. *)
Theorem tp_sound : ontology_sound -> forall f u w F U R,
  f : F -> u : U -> F # U ==> Sm R -> f @ u ==> w -> w : R.
Proof.
  intros HO f u w F U R Hf Hu HR Hw.
  destruct (eval_evaln _ _ Hw) as [k Hk].
  exact (app_sound_all HO k k f u w F U R (le_n k) Hk Hf Hu HR).
Qed.

Corollary tp_sound_by_typing : ontology_sound_by_typing -> forall f u w F U R,
  f : F -> u : U -> F # U ==> Sm R -> f @ u ==> w -> w : R.
Proof. intros HO; apply tp_sound, ontology_sound_by_typing_values, HO. Qed.

(** *** Evaluation preserves typing *)

Inductive leaf_free_expression : Combination -> Prop :=
| lfe_value : forall v, leaf_free_expression (Sm v)
| lfe_app : forall e1 e2, leaf_free_expression e1 -> leaf_free_expression e2 ->
    leaf_free_expression (Fk e1 e2).

Lemma expression_typed_leaf_free : forall e T,
  infer_expression O @ e ==> Sm T -> leaf_free_expression e.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intros T H;
    destruct (ie_inv O _ _ H) as [[u0 [E _]]|[e1' [e2' [T1 [T2 [E [H1 [H2 _]]]]]]]];
    inversion E; subst.
  - constructor.
  - constructor; [eapply IH1|eapply IH2]; eassumption.
Qed.

Lemma preservation : ontology_sound -> forall e v T, e ==> v ->
  infer_expression O @ e ==> Sm T -> v : T.
Proof.
  intros HO e; induction e as [|u _|e1 IH1 e2 IH2]; intros v T Hev HT;
    destruct (ie_inv O _ _ HT) as [[u0 [E Hu]]|[e1' [e2' [T1 [T2 [E [H1 [H2 H3]]]]]]]];
    inversion E; subst.
  - inversion Hev; subst; exact Hu.
  - destruct (eval_pair_inv _ _ _ Hev) as [v1 [v2 [Hv1 [Hv2 Hv]]]].
    exact (tp_sound HO v1 v2 v T1 T2 T (IH1 v1 T1 Hv1 H1) (IH2 v2 T2 Hv2 H2) H3 Hv).
Qed.

(** Typing is sound: progress (typed expressions are leaf-free) and
    evaluation preserves typing. *)
Definition typing_sound : Prop :=
  (forall e T, infer_expression O @ e ==> Sm T -> leaf_free_expression e) /\
  (forall e v T, e ==> v -> infer_expression O @ e ==> Sm T -> v : T).

Theorem evaluation_preserves_typing : ontology_sound -> typing_sound.
Proof. intros HO; split; [exact expression_typed_leaf_free|exact (preservation HO)]. Qed.

Theorem ept_by_typing : ontology_sound_by_typing -> typing_sound.
Proof. intros HO; apply evaluation_preserves_typing, ontology_sound_by_typing_values, HO. Qed.

(** *** Bare labels at run time *)

(** A typed expression never evaluates to a bare label. *)
Theorem no_runtime_label : ontology_sound -> forall e n T,
  infer_expression O @ e ==> Sm T -> ~ (e ==> 'label[n]).
Proof.
  intros HO e n T HT Hev.
  exact (bare_label_untyped O n T (preservation HO e _ T Hev HT)).
Qed.
End Soundness.
