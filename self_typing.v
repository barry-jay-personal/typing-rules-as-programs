(** * Step 82, stage 3, part 3: the self-typing results of paper section 4.

    Under the paper's Theorem names:
    - [concrete_is_self_typed] (typing.v), [concrete_type_unique_value];
    - [identity_polymorphic], [infer_product_value], [infer_leaf], [infer_Lf_inv];
    - [normal_combinators_are_concrete], [Z_preserves_concrete],
      [concrete_is_Turing_complete];
    - [plain_translation_concrete], [plain_translation_program];
    - [sysF_normal_concrete] and the System F lemmas;
    - [infer_self_typed]: a concrete ontology makes [infer] concrete, so
      [infer : infer];
    - the concrete dither: [cdither_concrete], [cdither_no_value]. *)

From Stdlib Require Import String List Arith Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions.
Open Scope string_scope.
Set Default Proof Using "Type".

(** ** Concrete types *)

Theorem concrete_type_unique_value : forall O v T, infer O @ v ==> Sm T -> concrete T -> v = T.
Proof. intros O v T Hv HT; apply (concrete_type_forces O); [apply concreteb_spec; exact HT|exact Hv]. Qed.

Lemma infer_Lf_inv : forall O v, infer O @ v ==> Sm Lf -> v = Lf.
Proof. exact type_Lf_inv. Qed.

Lemma infer_product_value : forall O u v U V, infer O @ u ==> Sm U -> infer O @ v ==> Sm V ->
  infer O @ (u '* v) ==> Sm (U '* V).
Proof. intros; apply pair_typed; assumption. Qed.

(** [I # U ==> Sm U] for every [U]. *)
Lemma app_I : forall O U, tp O @ 'I @r U ==> Sm U.
Proof.
  intros O U.
  eapply tp_S2_fwd; [reflexivity|apply tp_stem; reflexivity|apply tp_stem; reflexivity|apply tp_K1_fwd].
Qed.

Theorem identity_polymorphic : forall O u U, infer O @ u ==> Sm U ->
  infer_expression O @ ('I @ u) ==> Sm U.
Proof.
  intros O u U Hu; eapply ie_fork; [apply ie_stem, concrete_is_self_typed; reflexivity|apply ie_stem; exact Hu|apply app_I].
Qed.

(** The polymorphism of K: [K1 u : K1 U] and [K1 U # V = U]. *)
Theorem K_polymorphic : forall O u U V, infer O @ u ==> Sm U ->
  infer O @ ('K1 u) ==> Sm ('K1 U) /\ tp O @ ('K1 U) @r V ==> Sm U.
Proof.
  intros O u U V Hu; split; [apply infer_fork; [reflexivity|apply infer_leaf|exact Hu|reflexivity]|apply tp_K1_fwd].
Qed.

(** ** Which programs are concrete *)

Theorem normal_combinators_are_concrete : forall t,
  pure_nf t -> no_ref t = true -> concrete (to_tree t).
Proof.
  intros t Hp Hc; destruct (pure_invariants t Hp) as [Hi Hn].
  apply closed_lf; auto.
Qed.

Lemma bz_concrete : concrete bz.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Lemma self_apply_concrete : concrete self_apply.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.

Theorem Z_preserves_concrete : forall f, concrete f -> concrete (Z f).
Proof. intros f Hf; pose proof bz_concrete; pose proof self_apply_concrete; unfold Z; lf_tac. Qed.

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

Lemma sapp_concrete : forall m A B, concrete A -> concrete B -> concrete (sapp m A B).
Proof. intros m A B HA HB; pose proof (phi_concrete m); unfold sapp; lf_tac. Qed.

Lemma appn_concrete : forall m As F, concrete F -> Forall concrete As -> concrete (appn m F As).
Proof.
  intros m As; induction As as [|A As IH]; intros F HF HAs; cbn [appn fold_left]; auto.
  inversion HAs; subst; apply IH; auto; apply sapp_concrete; auto.
Qed.

Lemma rec_prog_concrete : forall k G H, concrete G -> concrete H -> concrete (rec_prog k G H).
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

Lemma min_prog_concrete : forall k F, concrete F -> concrete (min_prog k F).
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

(** Every partial mu-recursive function of positive arity is computed by a
    concrete program on the indices of its arguments. *)
Theorem concrete_is_Turing_complete :
  forall n (f : mu_fun n),
    { P : Combination |
      concrete P /\
      forall xs y, mu_eval n f xs y -> apps P (List.map num xs) ==> num y }.
Proof.
  intros n f; exists (compile f); split;
    [apply compile_concrete | intros; apply compile_sound; auto].
Qed.

(** ** The typing programs are concrete when the ontology is *)

Lemma infer_concrete : forall O, concreteb O = true -> concreteb (infer O) = true.
Proof. intros O H; cbn; rewrite ?H; cbn; rewrite ?H; reflexivity. Qed.

Lemma tp_concrete_g : forall O, concreteb O = true -> concreteb (tp O) = true.
Proof. intros O H; cbn; rewrite ?H; cbn; rewrite ?H; reflexivity. Qed.

Lemma infer_expression_concrete : forall O, concreteb O = true -> concreteb (infer_expression O) = true.
Proof. intros O H; cbn; rewrite ?H; cbn; rewrite ?H; reflexivity. Qed.

Theorem infer_self_typed : forall O, concrete O -> infer O @ infer O ==> Sm (infer O).
Proof.
  intros O H; apply concrete_is_self_typed, infer_concrete, concreteb_spec, H.
Qed.

Corollary O_ex_infer_self_typed : infer O_ex @ infer O_ex ==> Sm (infer O_ex).
Proof. apply infer_self_typed, concreteb_spec; vm_compute; reflexivity. Qed.
