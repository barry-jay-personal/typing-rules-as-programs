(** * Step 82, stage 3: closed System F terms by star abstraction (paper section 4.2).

    System F types are coded as label-free trees (unit = Lf, U -> V = Fk U V,
    forall b.T = Sm (K (\b.T))); a term translates by [star], dropping
    annotations.  Closed beta-normal terms translate to concrete programs
    ([sysF_normal_concrete]); type redexes are ordinary redexes; their type
    application agrees with evaluation.  (Ported from src_type36; the type
    application lemmas are reproved with the stage 2-3 forward rules.) *)
From Stdlib Require Import List Arith Lia String.
From BigStep Require Import tree typing booleans functions self_typing.
Open Scope string_scope.
(** System F types and beta-normal terms (annotations kept only to be dropped). *)
Inductive fty : Set :=
| TVar : string -> fty
| TUnit : fty
| TArr : fty -> fty -> fty
| TAll : string -> fty -> fty.

Inductive fnf : Set :=
| NNe : fne -> fnf
| NLam : string -> fty -> fnf -> fnf
| NTLam : string -> fnf -> fnf
with fne : Set :=
| NVar : string -> fne
| NApp : fne -> fnf -> fne
| NTApp : fne -> fty -> fne.

(** Tag-free type coding: 1 = Lf, U->V = Fk U V, ∀b.T = Sm (K (λb.T)). *)
Fixpoint tr_ty (T : fty) : Term :=
  match T with
  | TVar a => Ref a
  | TUnit => Val Lf
  | TArr U V => Val Lf @@ tr_ty U @@ tr_ty V
  | TAll b U => Val Lf @@ (Val 'K @@ star b (tr_ty U))
  end.

Fixpoint tr_nf (t : fnf) : Term :=
  match t with
  | NNe n => tr_ne n
  | NLam x _ b => star x (tr_nf b)
  | NTLam a b => star a (tr_nf b)
  end
with tr_ne (n : fne) : Term :=
  match n with
  | NVar x => Ref x
  | NApp m u => tr_ne m @@ tr_nf u
  | NTApp m U => tr_ne m @@ tr_ty U
  end.

Ltac nolab_tac :=
  unfold label_shape; intros [u [v [E [Hk _]]]]; inversion E; subst;
  repeat match goal with
  | H : tr_ty ?U = _ |- _ => destruct U; cbn [tr_ty] in H; try discriminate; inversion H; subst; clear H
  end;
  unfold denotes_K in Hk; destruct Hk as [Hk|Hk]; discriminate.

Ltac inv_tac :=
  first [ assumption | exact I | reflexivity
        | (left; reflexivity) | (right; reflexivity) | (right; left; reflexivity)
        | (right; right; left; reflexivity) | (right; right; right; eexists; reflexivity)
        | apply star_inv; assumption | apply star_nolab; assumption
        | nolab_tac ].

Lemma tr_ty_inv : forall T, ops_ok (tr_ty T) /\ no_label (tr_ty T).
Proof.
  induction T as [a| |U [IU NU] V [IV NV]|b U [IU NU]]; cbn [tr_ty ops_ok no_label op_ok];
    repeat split; inv_tac.
Qed.

Lemma neutral_not_label : forall n a, neutral n -> ~ label_shape (n @@ a).
Proof.
  intros n a Hn [u [v [E _]]]; inversion E; subst.
  inversion Hn as [|n1 a1 Hn1]; subst; inversion Hn1.
Qed.

Scheme fnf_mut := Induction for fnf Sort Prop
  with fne_mut := Induction for fne Sort Prop.
Combined Scheme fnf_fne_mut from fnf_mut, fne_mut.

Lemma tr_inv :
  (forall t, ops_ok (tr_nf t) /\ no_label (tr_nf t)) /\
  (forall n, neutral (tr_ne n) /\ ops_ok (tr_ne n) /\ no_label (tr_ne n)).
Proof.
  apply fnf_fne_mut; cbn [tr_nf tr_ne].
  - intros n [Hn [Hi Hl]]; auto.
  - intros x _ b [Hi Hl]; split; [apply star_inv|apply star_nolab]; auto.
  - intros a b [Hi Hl]; split; [apply star_inv|apply star_nolab]; auto.
  - intros x; repeat split; constructor.
  - intros m [Hn [Hi Hl]] u [Hui Hul]; repeat split; auto.
    + constructor; auto.
    + left; auto.
    + apply neutral_not_label; auto.
  - intros m [Hn [Hi Hl]] U; destruct (tr_ty_inv U) as [Hui Hul]; repeat split; auto.
    + constructor; auto.
    + left; auto.
    + apply neutral_not_label; auto.
Qed.


Theorem sysF_normal_concrete : forall t,
  no_ref (tr_nf t) = true -> concrete (to_tree (tr_nf t)).
Proof.
  intros t Hc; destruct (proj1 tr_inv t) as [Hi Hl]; apply closed_lf; auto.
Qed.



(** Type coding, tag-free: unit = Lf, U -> V = Fk U V (the fork of the two codes). *)
Definition arr (U V : Term) : Term := Val Lf @@ U @@ V.
Definition one : Term := Val Lf.

(** code = Λα.λx:α.x *)
Definition idF := Eval cbv in to_tree (star "a" (star "x" (Ref "x"))).
Definition idF_inst := Eval cbv in to_tree (star "x" (Ref "x")).
(** K = Λα.Λβ.λx:α.λy:β.x *)
Definition KF := Eval cbv in to_tree (star "a" (star "b" (star "x" (star "y" (Ref "x"))))).
Definition KF_inst := Eval cbv in to_tree (star "b" (star "x" (star "y" (Ref "x")))).
(** twice = Λα.λf:α→α.λx:α. f (f x) *)
Definition twF := Eval cbv in to_tree (star "a" (star "f" (star "x" (Ref "f" @@ (Ref "f" @@ Ref "x"))))).
Definition twF_inst := Eval cbv in to_tree (star "f" (star "x" (Ref "f" @@ (Ref "f" @@ Ref "x")))).
(** rank 2: g = λf:(∀α.α→α). f[1] (f[1] ⟨⟩) *)
Definition gF := Eval cbv in to_tree (star "f" (Ref "f" @@ one @@ (Ref "f" @@ one @@ Val Lf))).
(** non-vacuous: h = Λα.λf:(∀β.β→β). f[α→α] (f[α]) *)
Definition hF_term := star "a" (star "f" (Ref "f" @@ arr (Ref "a") (Ref "a") @@ (Ref "f" @@ Ref "a"))).
Definition hF := Eval cbv in to_tree hF_term.
Definition hF_inst (U : Combination) :=
  to_tree (star "f" (Ref "f" @@ arr (Val U) (Val U) @@ (Ref "f" @@ Val U))).

Lemma idF_is_K : idF = 'K1 idF_inst.
Proof. reflexivity. Qed.
Lemma KF_is_K : KF = 'K1 KF_inst.
Proof. reflexivity. Qed.
Lemma twF_is_K : twF = 'K1 twF_inst.
Proof. reflexivity. Qed.


Lemma idF_tyredex : forall U, idF @ U ==> idF_inst.
Proof. intros; unfold idF, idF_inst, KF, KF_inst, twF, twF_inst; evaluate. Qed.
Lemma KF_tyredex : forall U, KF @ U ==> KF_inst.
Proof. intros; unfold idF, idF_inst, KF, KF_inst, twF, twF_inst; evaluate. Qed.
Lemma twF_tyredex : forall U, twF @ U ==> twF_inst.
Proof. intros; unfold idF, idF_inst, KF, KF_inst, twF, twF_inst; evaluate. Qed.
Lemma hF_tyredex : forall U, hF @ U ==> hF_inst U.
Proof. intros; unfold hF, hF_inst; cbn; evaluate. Qed.




Lemma idF_concrete : concrete idF.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.
Lemma KF_concrete : concrete KF.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.
Lemma twF_concrete : concrete twF.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.
Lemma gF_concrete : concrete gF.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.
Lemma hF_concrete : concrete hF.
Proof. apply concreteb_sound; vm_compute; reflexivity. Qed.


Lemma label_pair_self : forall U, label_pair U U = false.
Proof. intros [|[|[|x|x y]|x y]|x y]; reflexivity. Qed.

Section T.
Variable O : Combination.

Lemma idF_type_app : forall U, tp O @ idF @r U ==> Sm idF_inst.
Proof. intros; rewrite idF_is_K; apply tp_K1_fwd. Qed.
Lemma KF_type_app : forall U, tp O @ KF @r U ==> Sm KF_inst.
Proof. intros; rewrite KF_is_K; apply tp_K1_fwd. Qed.
Lemma twF_type_app : forall U, tp O @ twF @r U ==> Sm twF_inst.
Proof. intros; rewrite twF_is_K; apply tp_K1_fwd. Qed.

Ltac tpf := repeat first
  [ eassumption
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [reflexivity| | |])
  | (apply tp_stem; reflexivity)
  | (apply tp_stem; apply label_pair_self)
  | apply tp_leaf_fwd ].

Lemma hF_type_app : forall U, tp O @ hF @r U ==> Sm (hF_inst U).
Proof. intros; unfold hF, hF_inst; cbn; tpf. Qed.
End T.

Lemma gF_type_app_id : tp O_ex @ gF @r idF ==> Sm Lf.
Proof. apply (runp_sound 40); vm_done. Qed.
Lemma h1_type_app_id : tp O_ex @ hF_inst Lf @r idF ==> Sm idF_inst.
Proof. apply (runp_sound 40); vm_done. Qed.

Lemma gF_eval_id : gF @ idF ==> Lf.
Proof. unfold gF, idF; evaluate. Qed.
Lemma h1_eval_id : hF_inst Lf @ idF ==> idF_inst.
Proof. unfold hF_inst, idF, idF_inst; cbn; evaluate. Qed.

(** A naive coding of ∀b.T as the stem of λb.T builds a label:
    (∀b.1→b)→(1→1) codes to S2[K, K1 Lf]. *)
Definition naive_all_arg := Eval cbv in
  to_tree (Val Lf @@ (Val Lf @@ star "b" (Val Lf @@ Val Lf @@ Ref "b")) @@ (Val Lf @@ Val Lf @@ Val Lf)).
Lemma naive_all_arg_is_label : naive_all_arg = 'S2['K, 'K1 Lf].
Proof. reflexivity. Qed.
Lemma naive_all_not_concrete :
  concreteb (to_tree (star "f" (Ref "f" @@ Val naive_all_arg))) = false.
Proof. vm_compute; reflexivity. Qed.


