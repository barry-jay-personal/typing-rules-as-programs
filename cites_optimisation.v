(** Stage 10 (step 83), group D: the specialising walk on concrete programs. *)
From Stdlib Require Import String List Bool Lia PeanoNat.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology poly optimisation_rt specialise_check specialise_rt.

Local Notation PO := paper_ontology.
Local Opaque equal1.

Lemma spec_Fk_shape : forall a b, exists x y, specialise_fn (Fk a b) = Fk x y.
Proof.
  intros a b; destruct (site (Fk a b)) as [c|] eqn:E.
  - unfold specialise_fn; fold specialise_fn; rewrite E.
    destruct c; [destruct (equal1_shape Lf) as [p [q [r ->]]]|eauto|destruct (equal1_shape (Fk c1 c2)) as [p [q [r ->]]]]; eauto.
  - rewrite (specialise_fn_site_none _ E); eauto.
Qed.

Lemma spec_Lf_inv : forall t, specialise_fn t = Lf -> t = Lf.
Proof.
  intros [|u|a b] H; [reflexivity| |].
  - rewrite specialise_fn_site_none in H by reflexivity; discriminate.
  - destruct (spec_Fk_shape a b) as [x [y E]]; rewrite E in H; discriminate.
Qed.

Lemma spec_Sm_inv : forall t z, specialise_fn t = Sm z -> exists x, t = Sm x /\ specialise_fn x = z.
Proof.
  intros [|u|a b] z H.
  - discriminate.
  - rewrite specialise_fn_site_none in H by reflexivity; inversion H; eauto.
  - destruct (spec_Fk_shape a b) as [x [y E]]; rewrite E in H; discriminate.
Qed.

Lemma spec_K1_inv : forall a b w, specialise_fn (Fk a b) = Fk Lf w -> a = Lf.
Proof.
  intros a b w H; destruct (site (Fk a b)) as [c|] eqn:E.
  - unfold specialise_fn in H; fold specialise_fn in H; rewrite E in H.
    destruct c as [|c|c1 c2].
    + destruct (equal1_shape Lf) as [p [q [r E1]]]; rewrite E1 in H; discriminate.
    + inversion H; reflexivity.
    + destruct (equal1_shape (Fk c1 c2)) as [p [q [r E1]]]; rewrite E1 in H; discriminate.
  - rewrite (specialise_fn_site_none _ E) in H; injection H as H1 _; apply spec_Lf_inv; exact H1.
Qed.

Lemma spec_label_pair : forall a b, label_pair a b = false ->
  label_pair (specialise_fn a) (specialise_fn b) = false.
Proof.
  intros a b H; destruct (label_pair (specialise_fn a) (specialise_fn b)) eqn:E; [|reflexivity].
  exfalso; unfold label_pair in E.
  destruct (specialise_fn a) as [|x0|x0 y0] eqn:Ea; try discriminate.
  destruct x0 as [|x1|x1 y1]; try discriminate.
  destruct x1; try discriminate.
  destruct (specialise_fn b) as [|w0|b0 w] eqn:Eb; try discriminate.
  destruct b0; try discriminate.
  destruct (spec_Sm_inv _ _ Ea) as [x [-> Ex]].
  destruct (spec_Sm_inv _ _ Ex) as [y [-> Ey]].
  apply spec_Lf_inv in Ey; subst y.
  destruct b as [|u|b1 b2]; [discriminate| |].
  - rewrite specialise_fn_site_none in Eb by reflexivity; discriminate.
  - apply spec_K1_inv in Eb; subst b1; cbn in H; discriminate.
Qed.

(** The walk preserves concreteness. *)
Theorem specialise_concrete : forall t, concreteb t = true -> concreteb (specialise_fn t) = true.
Proof.
  induction t as [|u IH|a IHa b IHb]; intros H.
  - reflexivity.
  - rewrite specialise_fn_site_none by reflexivity; exact (IH H).
  - destruct (site (Fk a b)) as [c|] eqn:E.
    + unfold specialise_fn; fold specialise_fn; rewrite E.
      destruct c; [apply equal1_concrete|exact H|apply equal1_concrete].
    + rewrite (specialise_fn_site_none _ E).
      cbn [concreteb] in *.
      apply andb_prop in H as [H Hb]; apply andb_prop in H as [Hl Ha].
      apply negb_true_iff in Hl.
      rewrite (spec_label_pair _ _ Hl), (IHa Ha), (IHb Hb); reflexivity.
Qed.

(** So a concrete program stays self-typed. *)
Theorem specialise_self_typed : forall O t, concreteb t = true ->
  infer O @ specialise_fn t ==> Sm (specialise_fn t).
Proof. intros O t H; apply concrete_is_self_typed, specialise_concrete, H. Qed.

(** The ontology after the walk on [paper_ontology] is concrete, so [infer]
    built using it is self-typed. *)
Theorem specialised_infer_self_typed :
  infer (specialise_fn PO) @ infer (specialise_fn PO) ==> Sm (infer (specialise_fn PO)).
Proof.
  apply infer_self_typed, concreteb_spec, specialise_concrete.
  Local Transparent equal1. vm_compute; reflexivity.
Qed.

