(** * Step 82, stage 7, part 3: typed optimisation.

    [optimise] replaces the operator of each application in an expression by
    its carrier, repeatedly while the carrier is itself tagged.  Applying a
    tag applies its carrier, so evaluation is unchanged
    ([optimise_preserves_evaluation]).

    Typing is preserved at a head [tagged[t,n]] when the declaration at
    [n] is sound by typing: then the carrier type [C] of [t] satisfies
    [C # U ==> Sm V] whenever [label[n] # U ==> Sm V].  Call such a head
    safe.  In the new design the declarations that are sound by values only
    are those of updates and queries, as before, and also every
    constructor (its carrier is [tagger[m]], whose type application has no
    result, [tagger_application_untyped]).  The counterexamples are
    computed below for a query head and for a constructor head. *)

From Stdlib Require Import String List Bool Lia PeanoNat.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries_core queries self_typing sums paper_ontology poly equality_queries.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Notation PO := paper_ontology.
Ltac by_runO := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** The optimisation as a function *)

Fixpoint untag (v : Combination) : Combination :=
  match v with
  | Fk (Sm (Fk Lf t)) (Fk (Sm (Sm Lf)) (Fk Lf _)) => untag t
  | _ => v
  end.

Fixpoint optimise_fn (e : Combination) : Combination :=
  match e with
  | Fk e1 e2 =>
      Fk (match e1 with
          | Sm v => Sm (untag v)
          | _ => optimise_fn e1
          end) (optimise_fn e2)
  | _ => e
  end.

Lemma untag_tagged : forall t n, untag ('tagged[t,n]) = untag t.
Proof. reflexivity. Qed.

Lemma untag_plain : forall v, (forall t n, v <> 'tagged[t,n]) -> untag v = v.
Proof.
  intros v H.
  destruct v as [|a|a b]; cbn [untag]; try reflexivity;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => is_var x; destruct x
         end;
  try reflexivity; exfalso; eapply H; reflexivity.
Qed.

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

(** ** Evaluation is unchanged *)

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
  Fk e1 e2 ==> v <-> exists v1 v2, e1 ==> v1 /\ e2 ==> v2 /\ v1 @ v2 ==> v.
Proof.
  intros e1 e2 v; split; [apply eval_pair_inv|].
  intros [v1 [v2 [H1 [H2 H]]]]; eapply eval_pair; eassumption.
Qed.

(** [tagged[t,n] @ u] evaluates exactly as [t @ u]. *)
Lemma tagged_app_eval_iff : forall t n u v, 'tagged[t,n] @ u ==> v <-> t @ u ==> v.
Proof.
  intros t n u v; split; intro H.
  - inversion H; subst.
    apply app_eval_iff in H4.
    destruct H4 as [v1 [v2 [H1 [H2 H3]]]].
    inversion H1; subst.
    assert (v2 = u) by (eapply eval_deterministic; [exact H2|evaluate]).
    subst; exact H3.
  - apply tagged_eval; exact H.
Qed.

Lemma untag_app_eval_iff : forall v u w, v @ u ==> w <-> untag v @ u ==> w.
Proof.
  intro v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v _ u w; reflexivity.
  - intros t n x IH u w; rewrite tagged_app_eval_iff; apply IH.
Qed.

Theorem optimise_preserves_evaluation : forall e v, e ==> v <-> optimise_fn e ==> v.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intro v; cbn [optimise_fn]; try reflexivity.
  destruct e1 as [|u|a b].
  - split; intro H; inversion H.
  - rewrite !value_app_eval_iff; split; intros [v2 [H2 H]];
      exists v2; split;
      [apply IH2; exact H2|apply (proj1 (untag_app_eval_iff _ _ _)); exact H|
       apply IH2; exact H2|apply (proj2 (untag_app_eval_iff _ _ _)); exact H].
  - rewrite !app_eval_iff; split; intros [v1 [v2 [H1 [H2 H]]]];
      exists v1, v2; repeat split;
      [apply IH1; exact H1|apply IH2; exact H2|exact H|
       apply IH1; exact H1|apply IH2; exact H2|exact H].
Qed.

(** ** The optimisation as a program *)

Definition untag_body : Combination := Eval cbn in to_tree
  (star "rec" (star "v"
     (''triage [Ref "v", ''triage [Val Lf, Val Lf, star "C" (star "N" (Ref "rec" @@ Ref "C"))], Val Lf]
        @@ (Val get_tagged @@ Ref "v")))).
Definition untag_program : Combination := Z untag_body.

Local Opaque get_tagged.
Lemma untag_program_eval : forall v, untag_program @ v ==> untag v.
Proof.
  intro v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v Hp. pose proof (get_tagged_none v Hp) as Hg.
    unfold untag_program; eapply Z_unfold; cbv -[get_tagged Z]; evaluate.
  - intros t n w IH. pose proof (get_tagged_some t n) as Hg.
    unfold untag_program; eapply Z_unfold; cbv -[get_tagged Z]; evaluate.
Qed.

Definition optimise_body : Combination := Eval cbn -[untag_program] in to_tree
  (star "rec"
     (''triage [Val Lf, Val Lf,
        star "e1" (star "e2"
          (Val Lf @@ (''triage [Val Lf,
                                star "u" (Val Lf @@ (Val untag_program @@ Ref "u")),
                                star "a" (star "b" (Ref "rec" @@ (Val Lf @@ Ref "a" @@ Ref "b")))]
                        @@ Ref "e1")
                  @@ (Ref "rec" @@ Ref "e2")))])).
Definition optimise : Combination := Z optimise_body.

Lemma optimise_eval : forall e, optimise @ e ==> optimise_fn e.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2].
  - unfold optimise; eapply Z_unfold; cbv -[untag_program Z]; evaluate.
  - unfold optimise; eapply Z_unfold; cbv -[untag_program Z]; evaluate.
  - destruct e1 as [|u|a b]; cbn [optimise_fn].
    + unfold optimise; eapply Z_unfold; cbv -[untag_program Z]; evaluate.
    + pose proof (untag_program_eval u) as Hu.
      unfold optimise; eapply Z_unfold; cbv -[untag_program Z]; evaluate.
    + unfold optimise; eapply Z_unfold; cbv -[untag_program Z]; evaluate.
Qed.
Local Transparent get_tagged.

Lemma optimise_concrete : concreteb optimise = true.
Proof. vm_compute; reflexivity. Qed.

(** ** Typing: safe heads *)

Section Typing.
Variable O : Combination.
Local Notation "t ':' T" := (infer O @ t ==> Sm T) (at level 70).

(** Every tag removed by [untag] from [v] has a declaration that is sound by typing. *)
Fixpoint tags_sound (v : Combination) : Prop :=
  match v with
  | Fk (Sm (Fk Lf t)) (Fk (Sm (Sm Lf)) (Fk Lf n)) =>
      (forall D, O @ n @r tp O ==> Sm D -> decl_sound_by_typing O n D) /\ tags_sound t
  | _ => True
  end.

(** Every head of [e] is safe. *)
Fixpoint heads_safe (e : Combination) : Prop :=
  match e with
  | Fk (Sm v) e2 => tags_sound v /\ heads_safe e2
  | Fk e1 e2 => heads_safe e1 /\ heads_safe e2
  | _ => True
  end.

Lemma tagged_typing_inv : forall t n F, 'tagged[t,n] : F ->
  exists C D, F = 'label[n] /\ t : C /\ O @ n @r tp O ==> Sm D /\ guard_of @ D @r C ==> 'K.
Proof.
  intros t n F H; apply infer_inv in H; inversion H; subst.
  - eexists; eexists; split; [reflexivity|split; [eassumption|split; eassumption]].
  - match goal with E : tag_of _ = None |- _ => cbn in E; discriminate end.
Qed.

Lemma label_app_inv : forall n D U V, O @ n @r tp O ==> Sm D -> tp O @ 'label[n] @r U ==> Sm V ->
  elim_of @ D @r n @r tp O @r U ==> Sm V.
Proof.
  intros n D U V HD H; apply tp_inv in H.
  inversion H as [n' U0 D' R0 HD' HEl | | | | G H0 U0 V0 W R0 HL _ _ _ | | |]; subst.
  - pose proof (eval_deterministic _ _ HD' _ HD) as E; inversion E; subst; exact HEl.
  - cbn in HL; discriminate.
Qed.

Lemma untag_typing : forall v F U V, tags_sound v -> v : F -> tp O @ F @r U ==> Sm V ->
  exists F', untag v : F' /\ tp O @ F' @r U ==> Sm V.
Proof.
  intros v; pattern v, (untag v); apply untag_ind; clear v.
  - intros v _ F U V _ HF Happ; exists F; split; assumption.
  - intros t n x IH F U V [Hn Ht] HF Happ.
    destruct (tagged_typing_inv _ _ _ HF) as [C [D [-> [HC [HD HG]]]]].
    pose proof (label_app_inv _ _ _ _ HD Happ) as HE.
    exact (IH C U V Ht HC (Hn D HD C U V HG HE)).
Qed.

Theorem optimise_preserves_expression_typing : forall e T,
  heads_safe e -> infer_expression O @ e ==> Sm T -> infer_expression O @ optimise_fn e ==> Sm T.
Proof.
  induction e as [|u _|e1 IH1 e2 IH2]; intros T Hs H; cbn [optimise_fn]; try exact H.
  destruct (ie_inv O _ _ H) as [[u [E _]]|[e1' [e2' [T1 [T2 [E [H1 [H2 Happ]]]]]]]]; [discriminate|].
  inversion E; subst e1' e2'; clear E.
  destruct e1 as [|u|a b].
  - destruct (ie_inv O _ _ H1) as [[u [E _]]|[x [y [_ [_ [E _]]]]]]; discriminate.
  - destruct Hs as [Hu Hs2].
    destruct (ie_inv O _ _ H1) as [[u' [E Hu']]|[x [y [_ [_ [E _]]]]]]; [|discriminate].
    inversion E; subst u'; clear E.
    destruct (untag_typing u T1 T2 T Hu Hu' Happ) as [F' [HF' HF'app]].
    eapply ie_fork; [apply ie_stem; exact HF'|exact (IH2 T2 Hs2 H2)|exact HF'app].
  - destruct Hs as [Hs1 Hs2].
    eapply ie_fork; [exact (IH1 T1 Hs1 H1)|exact (IH2 T2 Hs2 H2)|exact Happ].
Qed.
End Typing.

(** ** Safe names of the paper ontology *)

Ltac tpsB := repeat first
  [ eassumption
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].

Theorem bool_decl_sound_by_typing : forall O, decl_sound_by_typing O bool_nm D_bool.
Proof.
  intros O C U V HC HE.
  apply guard_of_bool in HC; apply elim_of_inv, bool_elim_inv in HE; subst U.
  destruct HC as [-> | ->]; tpsB.
Qed.

Theorem nat_decl_sound_by_typing : forall O, decl_sound_by_typing O nat_nm D_nat.
Proof.
  intros O C U V HC HE.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  apply nat_guard_spec in HC'. apply elim_of_inv, nat_eliminator_inv in HE.
  destruct HE as [S [-> HS]].
  destruct HC' as [-> | ->]; tpsB.
Qed.

Theorem list_decl_sound_by_typing : forall O r, decl_sound_by_typing O (list_tag r) (D_list r).
Proof.
  intros O r C U V HC HE.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (lg_inv _ _ HC') as [A [HA [-> | ->]]];
  apply elim_of_inv in HE; unfold list_elim in HE;
  apply name_elim_iff, le_inv in HE; cbn [right_of list_tag] in HE; destruct HE as [A' [S [HA' [-> HS]]]];
  rewrite HA in HA'; inversion HA'; subst A'; tpsB.
Qed.

(** ** The theorem for paper_ontology *)

Definition safe_heads (e : Combination) : Prop := heads_safe PO e.

Theorem optimise_typed :
  infer PO @ optimise ==> Sm optimise /\
  optimise @ (Kq Nat zero @ tt) ==> (('K1 zero) @ tt) /\
  (forall e T e', infer_expression PO @ e ==> Sm T -> safe_heads e -> optimise @ e ==> e' ->
     infer_expression PO @ e' ==> Sm T).
Proof.
  split; [apply concrete_is_self_typed, optimise_concrete|split].
  - exact (optimise_eval (Kq Nat zero @ tt)).
  - intros e T e' H Hs He.
    pose proof (eval_deterministic _ _ He _ (optimise_eval e)) as ->.
    exact (optimise_preserves_expression_typing PO e T Hs H).
Qed.

(** ** Unsafe heads: the optimised form can lose its type *)

(** A query head (the paper's example). *)
Definition tq_example : Combination := triageq Bool tt (Kq Bool tt) (Kq (Query Bool) (Kq Bool tt)) (Kq (Query Bool) (Kq Bool tt)).
Theorem optimise_unsafe_head_untyped :
  infer_expression PO @ (tq_example @ tt) ==> Sm Bool /\
  infer_expression PO @ optimise_fn (tq_example @ tt) ==> Lf.
Proof. split; by_runO. Qed.

(** A constructor head: [mk_nat @ S2[snd, K1 zero]] has type Nat; its optimised
    form applies [tagger[nat_nm]], whose type application has no result. *)
Theorem optimise_generator_head_untyped :
  infer_expression PO @ (mk_nat @ 'S2['snd, 'K1 zero]) ==> Sm Nat /\
  infer_expression PO @ optimise_fn (mk_nat @ 'S2['snd, 'K1 zero]) ==> Lf.
Proof. split; by_runO. Qed.

(** A safe head: the numeral [succ zero] applied to a pair of branches. *)
Example optimise_safe_example :
  infer_expression PO @ (succ zero @ (zero '* 'I)) ==> Sm Nat /\
  infer_expression PO @ optimise_fn (succ zero @ (zero '* 'I)) ==> Sm Nat.
Proof. split; by_runO. Qed.
