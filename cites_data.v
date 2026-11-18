(** * Step 83 (stage 10), group A: citations about options, lists and divergence. *)

From Stdlib Require Import String List Bool Lia Arith.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department self_typing divergence lists_rt paper_ontology poly numbers_rt steps.
Open Scope string_scope.
Import ListNotations.
Set Default Proof Using "Type".

Local Notation PO := paper_ontology.

(** ** Options: on application the type is discarded (abstraction.tex:158) *)

Theorem none2_apply : forall A b f, none A @ (b '* f) ==> b.
Proof. intros; unfold none; apply tagged_eval, fst_pair. Qed.

Theorem some2_apply : forall A x b f v, f @ x ==> v -> some A x @ (b '* f) ==> v.
Proof. intros A x b f v H; unfold some; apply tagged_eval; cbv; evaluate2; try exact H; evaluate. Qed.

(** ** Reading a name is a triage, refused at [List A] (abstraction.tex:229) *)

Theorem get_tagname_List2_untyped : forall O A,
  infer O @ get_tagname ==> Sm get_tagname /\ forall R, ~ (tp O @ get_tagname @r List A ==> Sm R).
Proof.
  intros O A; split; [apply concrete_is_self_typed; vm_compute; reflexivity|].
  intros R H; apply tp_inv in H; inversion H; subst; try discriminate;
    match goal with HL : label_of _ = None |- _ => cbn in HL; discriminate HL end.
Qed.

(** ** Removing the head of a list (abstraction.tex:278) *)

Definition uncons_or (d : Combination) : Combination := swap (d '* 'I).

Theorem uncons_or_cons : forall d A x t, uncons_or d @ cons A x t ==> (x '* t).
Proof. intros; unfold uncons_or, swap, cons; cbv; evaluate. Qed.

Theorem uncons_or_nil : forall d A, uncons_or d @ nil A ==> d.
Proof. intros; unfold uncons_or, swap, nil; cbv; evaluate. Qed.

(** ** omega @ omega (typing.tex:135) *)

Lemma self_apply_self_typed : forall O, infer O @ self_apply ==> Sm self_apply.
Proof. intros; apply concrete_is_self_typed; vm_compute; reflexivity. Qed.

Theorem tp_omega_no_value : forall O v, ~ (tp O @ self_apply @r self_apply ==> v).
Proof.
  intros O v H. destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (eval_evaln _ _ Hq) as [k Hk]; clear Hq.
  revert v Hk. induction k as [k IH] using lt_wf_ind. intros v Hk.
  destruct (tp_S2_h_any O 'I 'I p self_apply v k eq_refl Hp Hk)
    as [pG [pH [a [b [j1 [j2 [HpG [Ha [HpH [Hb [Hj1 [Hj2 Hcont]]]]]]]]]]]].
  assert (Ea : a = Sm self_apply).
  { pose proof (eval_appl _ _ _ _ _ HpG (evaln_eval _ _ _ Ha)) as E.
    exact (eval_deterministic _ _ E _ (app_I O self_apply)). }
  assert (Eb : b = Sm self_apply).
  { pose proof (eval_appl _ _ _ _ _ HpH (evaln_eval _ _ _ Hb)) as E.
    exact (eval_deterministic _ _ E _ (app_I O self_apply)). }
  destruct (Hcont _ _ Ea Eb) as [q [j3 [Hq3 [Hq3e Hj3]]]].
  pose proof (eval_deterministic _ _ Hq3 _ Hp) as ->.
  exact (IH j3 Hj3 v Hq3e).
Qed.

(** [omega @ omega] has no type: its typing has no value at all. *)
Theorem infer_expression_omega_omega_no_value : forall O v,
  ~ (infer_expression O @ (self_apply @ self_apply) ==> v).
Proof.
  intros O v H.
  Local Transparent infer_expression.
  unfold infer_expression in H; apply Z_unfold_inv in H; fold (infer_expression O) in H.
  unfold ie_body in H.
  pose proof (ie_stem O _ _ (self_apply_self_typed O)) as H1.
  unfold infer_expression in H1.
  crunch.
  match goal with H7 : tp O @ self_apply ==> ?p, H9 : ?p @ self_apply ==> ?w |- _ =>
    exact (tp_omega_no_value O w (eval_appl _ _ _ _ _ H7 H9)) end.
Qed.

(** When [d : A * List A], the type of [uncons_or d] takes [List A] to [A * List A]. *)
Theorem type_app_uncons_or : forall A d, infer PO @ d ==> Sm (A '* List A) ->
  infer PO @ uncons_or d ==> Sm (swap ((A '* List A) '* 'I)) /\
  tp PO @ swap ((A '* List A) '* 'I) @r List A ==> Sm (A '* List A).
Proof.
  intros A d Hd; split.
  - unfold uncons_or, swap.
    apply infer_fork; [reflexivity| |
      |reflexivity].
    + apply infer_stem, concrete_is_self_typed; vm_compute; reflexivity.
    + apply infer_fork; [reflexivity|apply infer_leaf| |reflexivity].
      apply pair_typed; [exact Hd|apply concrete_is_self_typed; vm_compute; reflexivity].
  - unfold swap; eapply tp_S2_fwd; [reflexivity|apply app_I|apply tp_K1_fwd|].
    apply type_app_List, app_I.
Qed.

(** ** The list programs append and map (recursion.tex:113)

    The programs [appendR] and [mapR] of lists_rt.v are run on lists of
    any length, whose element code is any [c].  The proofs follow the
    evaluation by the rules of Figure 4 ([rule_steps], steps.v) on open
    trees up to a frontier: an application of the iteration [litR] to a
    state with an unknown list, or of an unknown function.  The step
    counts (144, 168, 659, ...) are found by computation. *)

(** ** Evaluation through a frontier *)

Fixpoint first_ready (e : Combination) : option (Combination * Combination) :=
  match e with
  | Fk (Sm f) (Sm u) => Some (f, u)
  | Fk (Sm f) (Fk _ _ as e2) => first_ready e2
  | Fk (Fk _ _ as e1) _ => first_ready e1
  | _ => None
  end.
Fixpoint replace_first (e w : Combination) : Combination :=
  match e with
  | Fk (Sm f) (Sm u) => w
  | Fk (Sm f) (Fk _ _ as e2) => Fk (Sm f) (replace_first e2 w)
  | Fk (Fk _ _ as e1) e2 => Fk (replace_first e1 w) e2
  | _ => e
  end.

Lemma replace_first_eval : forall e f u w v, first_ready e = Some (f, u) -> f @ u ==> w ->
  replace_first e (Sm w) ==> v -> e ==> v.
Proof.
  induction e as [|a _|e1 IH1 e2 IH2]; intros f u w v Hr Hw Hv; [discriminate|discriminate|].
  destruct e1 as [|x|a b]; [discriminate| |].
  - destruct e2 as [|y|c d]; [discriminate| |].
    + cbn in Hr; inversion Hr; subst; cbn in Hv; inv_out Hv; exact Hw.
    + cbn in Hr, Hv.
      destruct (eval_arg_value_inv _ _ _ Hv) as [w2 [H1 H2]].
      eapply eval_arg_value; [eapply IH2; eassumption|exact H2].
  - cbn in Hr, Hv.
    destruct (eval_pair_inv _ _ _ Hv) as [v1 [v2 [H1 [H2 H3]]]].
    eapply eval_pair; [eapply IH1; eassumption|exact H2|exact H3].
Qed.

Lemma rule_steps_back : forall k e v, rule_steps k e ==> v -> e ==> v.
Proof.
  induction k; intros e v H; [exact H|].
  apply (step_with_back rule_rewrite rule_rewrite_ok), IHk, H.
Qed.

(** ** The iteration [litR] at a state of a list and an accumulator *)

Definition litv := Eval vm_compute in fun cT g =>
  match runp 12 (litR @ cT @r g) with Some v => v | None => Lf end.
Lemma litR_eval : forall cT g, litR @ cT @r g ==> litv cT g.
Proof. intros; apply (runp_sound 12); vm_compute; reflexivity. Qed.

Definition SV := Eval vm_compute in fun cT g =>
  match rule_steps 144 (litv cT g @ Lf) with
  | Fk (Sm (Fk (Sm (Fk (Sm (Fk (Sm (Fk (Sm (Fk Lf M)) (Fk Lf N))) (Fk Lf x))) (Fk Lf y))) _)) _ => x | _ => Lf end.

Lemma litv_unfold : forall cT g s v, code (type_of s) = cT -> SV cT g @ s ==> v -> litv cT g @ s ==> v.
Proof.
  intros cT g s v E H; apply (rule_steps_back 144).
  replace (rule_steps 144 (litv cT g @ s)) with ('wait3[sp_body, cT, SV cT g, identity_update] @ s)
    by (vm_compute; reflexivity).
  apply sp_fwd; destruct (combination_eq_dec cT (code (type_of s))) as [_|n]; [exact H|congruence].
Qed.

Definition consv (c h tl : Combination) := 'tagged['S2['snd, 'K1 (h '* tl)], Fk list_nm c].
Definition nilv (c : Combination) := 'tagged['fst, Fk list_nm c].

Lemma litv_nil : forall cT g c a, code (type_of (nilv c '* a)) = cT -> litv cT g @ (nilv c '* a) ==> (nilv c '* a).
Proof. intros cT g c a E; apply litv_unfold; [exact E|]. apply (runp_sound 12); vm_compute; reflexivity. Qed.

Lemma litv_cons : forall cT g c h tl a a' v, code (type_of (consv c h tl '* a)) = cT ->
  g @ (h '* a) ==> a' -> litv cT g @ (tl '* a') ==> v -> litv cT g @ (consv c h tl '* a) ==> v.
Proof.
  intros cT g c h tl a a' v E Hg Hv; apply litv_unfold; [exact E|].
  apply (rule_steps_back 168).
  eapply replace_first_eval; [vm_compute; reflexivity|exact Hg|].
  apply (rule_steps_back 2).
  replace (rule_steps 2 _) with (litv cT g @ (tl '* a')) by (vm_compute; reflexivity).
  exact Hv.
Qed.

Fixpoint lv (c : Combination) (xs : list Combination) : Combination :=
  match xs with [] => nilv c | x :: r => consv c x (lv c r) end.

Lemma type_of_lv : forall c xs, type_of (lv c xs) = 'label[Fk list_nm c].
Proof. intros c [|x r]; reflexivity. Qed.
Lemma type_of_pair_v : forall x y, type_of (x '* y) = type_of x '* type_of y.
Proof. reflexivity. Qed.

Lemma litv_loop : forall cT g c (P : Combination -> Prop) (sf : Combination -> Combination -> Combination) xs,
  (forall a ys, P a -> code (type_of (lv c ys '* a)) = cT) ->
  Forall (fun h => forall a, P a -> g @ (h '* a) ==> sf h a /\ P (sf h a)) xs ->
  forall a, P a -> litv cT g @ (lv c xs '* a) ==> (nilv c '* fold_left (fun a h => sf h a) xs a).
Proof.
  intros cT g c P sf xs HT Hg; induction Hg as [|h r Hh Hr IH]; intros a Ha.
  - apply litv_nil, (HT a []), Ha.
  - destruct (Hh a Ha) as [H1 H2].
    eapply litv_cons; [apply (HT a (h :: r)), Ha|exact H1|apply IH, H2].
Qed.

Definition ceqb (x y : Combination) : bool := if combination_eq_dec x y then true else false.
Fixpoint find_path (m t : Combination) : option (list nat) :=
  if ceqb m t then Some [] else
  match t with
  | Lf => None
  | Sm a => option_map (fun p => (0%nat :: p)%list) (find_path m a)
  | Fk a b => match find_path m a with Some p => Some (1%nat :: p)%list | None => option_map (fun p => (2%nat :: p)%list) (find_path m b) end
  end.
Fixpoint at_path (p : list nat) (t : Combination) : Combination :=
  match p, t with
  | List.nil, _ => t
  | (0 :: p)%list, Sm a => at_path p a
  | (1 :: p)%list, Fk a _ => at_path p a
  | (2 :: p)%list, Fk _ b => at_path p b
  | _, _ => Lf
  end.
Definition mk1 := Nat.iter 61 Sm Lf. Definition mk2 := Nat.iter 62 Sm Lf.
Definition pg := Eval vm_compute in match find_path mk2 (litv mk1 mk2) with Some p => p | None => List.nil end.
Definition Lc (c : Combination) := 'label[Fk list_nm c].

Lemma fold_cons : forall c xs acc, fold_left (fun a h => consv c h a) xs (lv c acc) = lv c (rev xs ++ acc).
Proof.
  intros c xs; induction xs as [|x r IH]; intros acc; [reflexivity|].
  cbn [fold_left]; change (consv c x (lv c acc)) with (lv c (x :: acc)); rewrite IH.
  cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

(** rev_append: the iteration with the step that conses onto the accumulator. *)
Definition E1 := Eval vm_compute in fun c L1 L2 => rule_steps 659 (appendR @ (c '* (L1 '* L2))).
Definition ga := Eval vm_compute in fun c => at_path pg (match first_ready (E1 c mk1 mk2) with Some (f, _) => f | None => Lf end).

Lemma ga_step : forall c h a, ga c @ (h '* a) ==> consv c h a.
Proof. intros; apply (runp_sound 12); vm_compute; reflexivity. Qed.

Lemma rev_loop : forall c xs acc,
  litv (code (Lc c '* Lc c)) (ga c) @ (lv c xs '* lv c acc) ==> (nilv c '* lv c (rev xs ++ acc)).
Proof.
  intros c xs acc; rewrite <- fold_cons.
  apply (litv_loop _ _ c (fun a => type_of a = Lc c)); [| |apply type_of_lv].
  - intros a ys Ha; rewrite type_of_pair_v, type_of_lv, Ha; reflexivity.
  - apply Forall_forall; intros h _ a Ha; split; [apply ga_step|reflexivity].
Qed.

Lemma appendR_phases : forall c L1 L2 R R2,
  litv (code (Lc c '* Lc c)) (ga c) @ (L1 '* nilv c) ==> (nilv c '* R) ->
  litv (code (Lc c '* Lc c)) (ga c) @ (R '* L2) ==> (nilv c '* R2) ->
  appendR @ (c '* (L1 '* L2)) ==> R2.
Proof.
  intros c L1 L2 R R2 H1 H2.
  apply (rule_steps_back 659); eapply replace_first_eval; [vm_compute; reflexivity|exact H1|].
  apply (rule_steps_back 485); eapply replace_first_eval; [vm_compute; reflexivity|exact H2|].
  apply (rule_steps_back 19); replace (rule_steps 19 _) with (Sm R2) by (vm_compute; reflexivity).
  constructor.
Qed.

(** [append] on lists: for every code [c], in particular [code A]. *)
Theorem append_list : forall A xs ys,
  appendR @ (code A '* (lv (code A) xs '* lv (code A) ys)) ==> lv (code A) (xs ++ ys).
Proof.
  intros A xs ys; eapply appendR_phases.
  - pose proof (rev_loop (code A) xs []) as H; rewrite app_nil_r in H; exact H.
  - pose proof (rev_loop (code A) (rev xs) ys) as H; rewrite rev_involutive in H; exact H.
Qed.

(** map: the iteration whose step applies [f] and conses. *)
Definition M1 := Eval vm_compute in fun ca cb f L => rule_steps 752 (mapR @ (ca '* (cb '* (f '* L)))).
Definition gm := Eval vm_compute in fun ca cb f =>
  at_path pg (match first_ready (M1 ca cb f mk1) with Some (g, _) => g | None => Lf end).

Lemma gm_step : forall ca cb f h a fh, f @ h ==> fh -> gm ca cb f @ (h '* a) ==> consv cb fh a.
Proof.
  intros ca cb f h a fh Hf.
  apply (rule_steps_back 29); eapply replace_first_eval; [vm_compute; reflexivity|exact Hf|].
  apply (runp_sound 12); vm_compute; reflexivity.
Qed.

Lemma mapR_phases : forall ca cb f L R R2,
  litv (code (Lc ca '* Lc cb)) (gm ca cb f) @ (L '* nilv cb) ==> (nilv ca '* R) ->
  litv (code (Lc cb '* Lc cb)) (ga cb) @ (R '* nilv cb) ==> (nilv cb '* R2) ->
  mapR @ (ca '* (cb '* (f '* L))) ==> R2.
Proof.
  intros ca cb f L R R2 H1 H2.
  apply (rule_steps_back 752); eapply replace_first_eval; [vm_compute; reflexivity|exact H1|].
  apply (rule_steps_back 566); eapply replace_first_eval; [vm_compute; reflexivity|exact H2|].
  apply (rule_steps_back 19); replace (rule_steps 19 _) with (Sm R2) by (vm_compute; reflexivity).
  constructor.
Qed.

Theorem map_list : forall A B f (fv : Combination -> Combination) xs,
  Forall (fun x => f @ x ==> fv x) xs ->
  mapR @ (code A '* (code B '* (f '* lv (code A) xs))) ==> lv (code B) (List.map fv xs).
Proof.
  intros A B f fv xs Hf; apply (mapR_phases _ _ _ _ (lv (code B) (rev (List.map fv xs)))).
  - assert (E : forall acc, fold_left (fun a h => consv (code B) (fv h) a) xs (lv (code B) acc)
                  = lv (code B) (rev (List.map fv xs) ++ acc)).
    { clear Hf; induction xs as [|x r IH]; intros acc; [reflexivity|].
      cbn [fold_left List.map]; change (consv (code B) (fv x) (lv (code B) acc)) with (lv (code B) (fv x :: acc)).
      rewrite IH; cbn [rev]; rewrite <- app_assoc; reflexivity. }
    pose proof (E []) as E0; rewrite app_nil_r in E0; rewrite <- E0.
    apply (litv_loop _ _ (code A) (fun a => type_of a = Lc (code B)) (fun h a => consv (code B) (fv h) a));
      [|apply Forall_forall; intros h Hh a Ha; split; [apply gm_step; rewrite Forall_forall in Hf; exact (Hf h Hh)|reflexivity]
       |apply type_of_lv].
    intros a ys Ha; rewrite type_of_pair_v, type_of_lv, Ha; reflexivity.
  - pose proof (rev_loop (code B) (rev (List.map fv xs)) []) as H.
    rewrite rev_involutive, app_nil_r in H; exact H.
Qed.

(** The lists of the paper are these lists. *)
Lemma lv_cons_nil : forall A x xs, lv (code A) [] = nil A /\ lv (code A) (x :: xs) = cons A x (lv (code A) xs).
Proof. split; reflexivity. Qed.

(** ** A list map by [Z] alone (recursion.tex:107)

      map_Z @ xs = xs @ (nil[Nat] * \p. gen_cons @ (code Nat * (succ (fst p) * map_Z @ snd p)))

    At [List Nat] the eliminator of lists checks the cons case at
    [Nat * List Nat], which applies the type of [map_Z] at [List Nat]
    again: the typing contains itself ([cycle_check], numbers_rt.v). *)
Definition map_Z_term : Term :=
  star "self" (star "xs"
    (Ref "xs" @@ (Val (nil Nat) ''* star "p"
       (op gen_cons @@ (Val (code Nat) ''* ((Val succ_fn @@ (Val 'fst @@ Ref "p")) ''* (Ref "self" @@ (Val 'snd @@ Ref "p")))))))).
Definition map_Z_body : Combination := Eval cbn -[gen_cons] in to_tree map_Z_term.
Definition map_Z : Combination := Z map_Z_body.
Definition T_mapZ : Combination := Eval vm_compute in tyP map_Z.

Lemma infer_map_Z : infer PO @ map_Z ==> Sm T_mapZ. Proof. by_runN. Qed.
Example map_Z_eval : map_Z @ cons Nat zero (cons Nat (succ zero) (nil Nat)) ==> cons Nat (succ zero) (cons Nat (succ (succ zero)) (nil Nat)).
Proof. by_runN. Qed.

Definition w_mapZ : Combination := Eval vm_compute in
  match runp 40 (tp PO @ T_mapZ) with Some w => w | None => Lf end.
Lemma tp_mapZ_partial : tp PO @ T_mapZ ==> w_mapZ. Proof. by_runN. Qed.

Theorem list_map_Z_typing_diverges : forall R, ~ tp PO @ T_mapZ @r List Nat ==> R.
Proof. intros R; apply (cycle_check_diverges 3000 _ _ _ _ R tp_mapZ_partial); vm_compute; reflexivity. Qed.

