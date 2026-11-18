(** * Step 83 (stage 10), group C: cited results on recursion and function types. *)
From Stdlib Require Import String List Bool Lia Arith PeanoNat.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists sums glam department lists_rt queries self_typing paper_ontology fun_ontology logic_paper logic_typing poly scott_arithmetic size_queries numbers_rt typed_mu_rt numbers_paper function_types_paper function_recursion_paper.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Notation FO := fun_ontology.
Local Notation PO := paper_ontology.
Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Ltac by_runC := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** minimisation_other (function-types.tex:16) *)
Theorem minimisation_other : forall p x, type_of x <> Nat ->
  exists u, minimisation @ p ==> u /\ u @ x ==> x.
Proof.
  intros p x Hx; destruct (minimisation_eval p) as [Bv [HB HBv]].
  exists (upd_of Bv); split; [exact HB|].
  destruct (HBv (upd_of Bv)) as [Adv [HA _]].
  apply rt_update_unfold; eapply eval_appl; [exact HA|].
  change ('tagged['wait3[sp_body, code Nat, Adv, identity_update], update_nm]) with (special_type Nat Adv identity_update).
  apply special_type_miss; [exact Hx|unfold identity_update; apply tagged_eval; evaluate].
Qed.

(** ** infer_mul_lam, infer_collatz_lam (function-types.tex:82) *)
Definition mul_lam : Combination := lam mul (Nat '* Nat) Nat.
Theorem infer_mul_lam : infer FO @ mul_lam ==> Sm (Fun (Nat '* Nat) Nat). Proof. by_runC. Qed.
Definition collatz_lam : Combination := lam collatz_ext Nat Nat.
Theorem infer_collatz_lam : infer FO @ collatz_lam ==> Sm (Fun Nat Nat). Proof. by_runC. Qed.
Example mul_lam_eval : mul_lam @ (numeral 2 '* numeral 3) ==> numeral 6. Proof. by_runC. Qed.
Example collatz_lam_six : collatz_lam @ numeral 6 ==> numeral 8. Proof. by_runC. Qed.

(** ** seed_constant (function-types.tex:126) *)
Theorem seed_constant : forall U V v, names_concrete U -> names_concrete V ->
  infer FO @ v ==> Sm V -> infer FO @ lam ('K1 v) U V ==> Sm (Fun U V).
Proof.
  intros U V v HU HV Hv.
  eapply infer_lam; [exact HU|exact HV| |apply tp_K1_fwd].
  apply infer_fork; [reflexivity|apply infer_leaf|exact Hv|reflexivity].
Qed.

(** ** minimisation_lam_eval, type_app_min_on_fn (function-types.tex:128) *)
Theorem minimisation_lam_eval : forall p m, minimisation @ p ==> m ->
  minimisation_lam @ p ==> lam m Nat Nat.
Proof.
  intros p m Hm; unfold minimisation_lam; apply lam_eval.
  pose proof (mk_fun_eval Nat Nat m) as Hk.
  unfold minimisation_body; cbv -[mk_fun minimisation lam]; evaluate2; try eassumption; evaluate.
Qed.

Definition T_minF : Combination := Eval vm_compute in
  match runp 40 (infer FO @ minimisation) with Some (Sm A) => A | _ => Lf end.
Theorem type_app_min_on_fn : infer FO @ minimisation ==> Sm T_minF /\
  tp FO @ T_minF @r Fun Nat Bool ==> Sm Update.
Proof. split; by_runC. Qed.

(** ** iterate_polymorphic (recursion.tex:74), run_iter_eval (recursion.tex:77)

    [iterate] is [nitR] at the code of [Nat * Nat]. *)
Definition iterate : Combination := Eval vm_compute in
  match runp 40 (nitR @ code NN) with Some v => v | None => Lf end.
Lemma iterate_eval : nitR @ code NN ==> iterate. Proof. by_runC. Qed.
Definition T_iter : Combination := Eval vm_compute in ty_of iterate.
Lemma infer_iterate : infer PO @ iterate ==> Sm T_iter. Proof. by_runC. Qed.

Theorem iterate_polymorphic : forall G, tp PO @ G @r Nat ==> Sm Nat -> tp PO @ T_iter @r G ==> Sm Update.
Proof. intros G HG; unfold T_iter; repeat (tps; try (apply type_app_Nat; tps)). Qed.

(** As [run_iter] of scott_arithmetic.v at the state type [Nat * Nat]; the code is
    passed through [K @ code @ (Lf @ q)] so that the application is not closed. *)
Definition run_iter_p : Combination := Eval cbn -[nitR] in
  to_tree (star "g" (star "q" (Val 'snd @@ ((op nitR @@ (Val 'K @@ Val (code NN) @@ (Val Lf @@ Ref "q")) @@ Ref "g") @@ Ref "q")))).

(** [run_iter_p @ g] runs [iterate @ g] on a pair [m * a] and takes the second component. *)
Theorem run_iter_eval : forall g m a m' a', iterate @ g @r (m '* a) ==> (m' '* a') ->
  run_iter_p @ g @r (m '* a) ==> a'.
Proof.
  intros g m a m' a' Hv.
  destruct (app2_inv _ _ _ _ Hv) as [c [Ha Hq]].
  pose proof iterate_eval as Hi.
  unfold run_iter_p; cbv -[nitR iterate]; evaluate2; try eassumption; evaluate2; try eassumption; evaluate.
Qed.
Example run_iter_add : run_iter_p @ succ_fn @r (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_runC. Qed.
(** ** fix_function_upd_eval_step (function-types.tex:118) *)
Lemma fu_body_eval : forall U V f r, exists Act,
  fu_body U V f @ r ==> 'tagged['wait3[sp_body, code (Fun U V), Act, identity_update], update_nm] /\
  forall w v, f @ lam ('wait[r, w]) U V ==> v -> Act @ w ==> v.
Proof.
  intros U V f r. pose proof (mk_fun_eval U V) as Hk. Local Opaque mk_fun Fun code. eexists; split.
  - unfold fu_body, mk_update. ev2.
  - intros w v H. ev2; apply Hk.
Qed.

(** The seed is not applied: [fix_function_upd[U,V,f,g0] @ x] evaluates as
    [f] applied to the recursive function and then to [x]. *)
Theorem fix_function_upd_eval_step : forall U V f g0 x v, type_of g0 = Fun U V ->
  f @ fix_function_upd U V f g0 @r x ==> v -> fix_function_upd U V f g0 @ x ==> v.
Proof.
  intros U V f g0 x v Ht H.
  destruct (app2_inv _ _ _ _ H) as [w [Hw Hx]].
  destruct (fu_body_eval U V f (fu_update U V f)) as [Act [HB HA]].
  unfold fix_function_upd at 1; apply lam_eval, wait_eval.
  eapply eval_appl; [|exact Hx].
  unfold fu_update at 1, fix_update; apply rt_update_unfold.
  eapply eval_appl; [exact HB|].
  apply sp_tag_fwd; [rewrite Ht; reflexivity|apply HA; exact Hw].
Qed.

Lemma type_of_typed_fun : forall U V g, infer FO @ g ==> Sm (Fun U V) -> type_of g = Fun U V.
Proof.
  intros U V g H; destruct (no_junk FO g _ H) as [c [F [D [-> _]]]]; reflexivity.
Qed.

Corollary fix_function_upd_eval_step_typed : forall U V f g0 x v, infer FO @ g0 ==> Sm (Fun U V) ->
  f @ fix_function_upd U V f g0 @r x ==> v -> fix_function_upd U V f g0 @ x ==> v.
Proof. intros U V f g0 x v Hg; apply fix_function_upd_eval_step, (type_of_typed_fun _ _ _ Hg). Qed.

(** ** Addition of Scott numerals with the case analysis of [add_Z] *)
Definition sadd_body : Combination := Eval cbn -[mk_fun mk_nat] in to_tree
  (star "r" (op (mk_fun NN Nat) @@ star "q"
     ((Val 'fst @@ Ref "q") @@ ((Val 'snd @@ Ref "q") ''* star "p" (succ_t (Ref "r" @@ (Ref "p" ''* (Val 'snd @@ Ref "q")))))))).
Definition sadd_f : Combination := lam sadd_body (Fun NN Nat) (Fun NN Nat).
Definition sadd_seed : Combination := lam ('K1 zero) NN Nat.
Definition sadd_fu : Combination := fix_function_upd NN Nat sadd_f sadd_seed.

Lemma infer_sadd_f : infer FO @ sadd_f ==> Sm (Fun (Fun NN Nat) (Fun NN Nat)). Proof. by_runC. Qed.
Lemma infer_sadd_seed : infer FO @ sadd_seed ==> Sm (Fun NN Nat). Proof. by_runC. Qed.

Theorem infer_sadd_fu : infer FO @ sadd_fu ==> Sm (Fun (Nat '* Nat) Nat).
Proof.
  apply infer_fix_function_upd; [vm_compute; auto|vm_compute; reflexivity|exact infer_sadd_f|exact infer_sadd_seed].
Qed.
Theorem sadd_fu_eval : sadd_fu @ (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_runC. Qed.

(** ** fix_function_upd_seed_typed (function-types.tex:126): what the typing of
    [fix_function_upd] needs of the seed, and a seed of another type. *)
Theorem fix_function_upd_seed_typed : forall U V f g0,
  infer FO @ fix_function_upd U V f g0 ==> Sm (Fun U V) ->
  exists G0, infer FO @ g0 ==> Sm G0 /\ tp FO @ G0 @r U ==> Sm V.
Proof.
  intros U V f g0 H.
  unfold fix_function_upd, lam in H.
  pose proof (infer_inv FO _ _ H) as Hi; inversion Hi as [| |c n F D Hn Hc HD HG|u1 u2 U1 U2 Ht _ _ _]; subst;
    [|cbn in Ht; discriminate].
  pose proof (eval_deterministic _ _ HD _ (FO_fun (Fk (code U) (code V)))) as ED; inversion ED; subst D; clear ED HD.
  destruct (app2_inv _ _ _ _ HG) as [g [Hg1 Hg2]]; pose proof (eval_deterministic _ _ Hg1 _ (guard_of_pair _ _)) as ->.
  apply fun_guard_inv in Hg2; destruct Hg2 as [A [B [HA [HB HFA]]]]; cbn [left_of right_of] in HA, HB;
    rewrite decode_code in HA, HB; inversion HA; inversion HB; subst A B; clear HA HB HG Hg1.
  apply infer_inv in Hc; inversion Hc as [| |? ? ? ? _ _ _ _|a1 a2 A1 A2 _ H1 H2 _]; subst; clear Hc.
  apply infer_inv in H1; inversion H1 as [|w W Hw| |]; subst; clear H1.
  apply infer_inv in Hw; inversion Hw as [| |? ? ? ? _ _ _ _|b1 b2 B1 B2 _ H3 H4 _]; subst; clear Hw.
  apply infer_inv in H3; inversion H3 as [|w W Hw| |]; subst; clear H3.
  apply infer_inv in Hw; inversion Hw as [| |? ? ? ? _ _ _ _|c1 c2 C1 C2 _ H5 H6 _]; subst; clear Hw.
  apply infer_inv in H4; inversion H4 as [| |? ? ? ? _ _ _ _|d1 d2 D1 D2 _ H7 H8 _]; subst; clear H4.
  apply infer_inv in H5; inversion H5; subst; clear H5.
  apply infer_inv in H7; inversion H7; subst; clear H7.
  pose proof (eval_deterministic _ _ H2 _ (concrete_is_self_typed FO 'I eq_refl)) as E; inversion E; subst A2; clear E H2.
  unfold fu_update, fix_update in H6; apply infer_inv in H6; inversion H6 as [| |? ? ? ? _ _ _ _|? ? ? ? Ht _ _ _]; subst;
    [|cbn in Ht; discriminate]; clear H6.
  exists D2; split; [exact H8|].
  apply tp_inv in HFA; inversion HFA as [| | | |G H0 U0 V1 W R0 _ HG HH HVW| | |]; subst; clear HFA.
  pose proof (eval_deterministic _ _ HH _ (app_I FO U)) as E; inversion E; subst W; clear E HH.
  apply tp_inv in HG; inversion HG as [| | | |G' H' U' X1 X2 R1 _ HG1 HH1 HX| | |]; subst; clear HG.
  apply tp_inv in HG1; inversion HG1; subst; clear HG1.
  apply tp_inv in HH1; inversion HH1; subst; clear HH1.
  pose proof (eval_deterministic _ _ HX _ (FO_type_app_Update _)) as E; inversion E; subst; exact HVW.
Qed.

(** A seed of another type: [K1 zero], of type [K1 Nat], not [Nat -> Nat].
    [fix_function_upd] is still typed at [Nat -> Nat], and at run time the
    type test of the update misses, so the seed is applied. *)
Definition id_fun_nn : Combination := lam 'I (Fun Nat Nat) (Fun Nat Nat).
Definition const_seed : Combination := 'K1 zero.
Theorem fix_function_upd_untyped_seed :
  infer FO @ fix_function_upd Nat Nat id_fun_nn const_seed ==> Sm (Fun Nat Nat) /\
  infer FO @ const_seed ==> Sm ('K1 Nat) /\ ~ (infer FO @ const_seed ==> Sm (Fun Nat Nat)) /\
  fix_function_upd Nat Nat id_fun_nn const_seed @ numeral 4 ==> zero.
Proof.
  assert (H1 : infer FO @ const_seed ==> Sm ('K1 Nat)) by by_runC.
  split; [by_runC|split; [exact H1|split; [|by_runC]]].
  intros H2; pose proof (eval_deterministic _ _ H1 _ H2) as E; inversion E.
Qed.

