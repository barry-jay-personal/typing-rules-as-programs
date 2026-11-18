(** * Step 82, stage 6, part 2: the typings of the logic, at [fun_ontology].

    Every axiom program has the type of its scheme, for all types whose
    names are concrete ([infer_ax_*]), so every derivable proposition has
    a typed expression ([propositions_as_types]), and its value, of that
    type, realizes it ([derivation_evaluates]). *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists sums department lists_rt queries self_typing array_family paper_ontology fun_ontology logic_paper.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation FO := fun_ontology.

(** ** The constructors of functions and sums at [fun_ontology] *)

Lemma mkfun_entry_hit : forall r a, concreteb r = true -> mkfun_entry @ Fk mkfun_nm r @r a ==> Sm (mk_D r a).
Proof.
  intros r a Hr; unfold mkfun_entry.
  pose proof (get_par_spec mkfun_nm (Fk mkfun_nm r)) as Hp; cbn [par_of] in Hp.
  pose proof (is_concrete_bt r) as Hc; rewrite Hr in Hc; cbn [bt] in Hc.
  destruct (combination_eq_dec mkfun_nm mkfun_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma FO_mkfun : forall r, concreteb r = true -> FO @ Fk mkfun_nm r @r tp FO ==> Sm (mk_D r (tp FO)).
Proof.
  intros r Hr; unfold FO; apply rows_f_miss; [reflexivity|].
  apply alt_none; [apply PO_fam_miss_fun; right; reflexivity|].
  unfold fam_fun; apply alt_none; [apply fun_entry_miss, par_of_other; discriminate|].
  apply alt_some; [apply mkfun_entry_hit, Hr|unfold no_rows; eexists; evaluate].
Qed.

Lemma FO_mksum : forall r, concreteb r = true -> FO @ Fk mksum_nm r @r tp FO ==> Sm (D_mksum r).
Proof.
  intros r Hr; unfold FO; apply rows_f_miss; [reflexivity|].
  apply alt_some; [|apply fam_fun_partial]. unfold PO_fam; apply alt_some; [|apply arr_fam_partial]. unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; discriminate|].
  apply sum_fam_mksum, Hr.
Qed.

Lemma code_pair_concrete : forall A B, names_concrete A -> names_concrete B -> concreteb (Fk (code A) (code B)) = true.
Proof.
  intros A B HA HB; cbn [concreteb]; rewrite (code_concrete A HA), (code_concrete B HB).
  assert (HL : label_pair (code A) (code B) = false)
    by (destruct (label_pair (code A) (code B)) eqn:E; [destruct (label_pair_K1 _ _ E) as [m Em];
        exfalso; exact (code_not_K1 B m Em)|reflexivity]).
  rewrite HL; reflexivity.
Qed.

Lemma name_concrete : forall h r, concreteb h = true -> label_pair h r = false -> concreteb r = true ->
  concreteb (Fk h r) = true.
Proof. intros h r H1 H2 H3; cbn [concreteb]; rewrite H1, H2, H3; reflexivity. Qed.
Lemma concreteb_tagger : forall n, concreteb ('tagger[n]) = concreteb n.
Proof. intros n; cbn; destruct (concreteb n); reflexivity. Qed.

Definition MkFun (A B : Combination) : Combination := 'label[Fk mkfun_nm (Fk (code A) (code B))].
Definition MkSum (A B : Combination) : Combination := 'label[Fk mksum_nm (Fk (code A) (code B))].

Section Ctors.
Variables A B : Combination.
Hypothesis HA : names_concrete A.
Hypothesis HB : names_concrete B.
Let Hc := code_pair_concrete A B HA HB.

Theorem type_app_mk_fun : forall C, tp FO @ C @r A ==> Sm B -> tp FO @ MkFun A B @r C ==> Sm (Fun A B).
Proof using HA HB.
  intros C H; eapply tp_abs; [apply FO_mkfun, Hc|].
  apply elim_of_fwd, ctor_elim_fwd, fun_guard_hit, H.
Qed.

Theorem infer_mk_fun : infer FO @ mk_fun A B ==> Sm (MkFun A B).
Proof using HA HB.
  eapply infer_tag; [apply name_concrete; [reflexivity|reflexivity|exact Hc]| |apply FO_mkfun, Hc|].
  - apply concrete_is_self_typed; rewrite concreteb_tagger; apply name_concrete; [reflexivity|reflexivity|exact Hc].
  - eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec ('tagger[fun_tag (code A) (code B)]) ('tagger[fun_tag (code A) (code B)])) as G.
    destruct combination_eq_dec; [exact G|contradiction].
Qed.

Theorem type_app_mk_sum : forall C, C = 'S2['fst, 'K1 A] \/ C = 'S2['snd, 'K1 B] ->
  tp FO @ MkSum A B @r C ==> Sm (Sum A B).
Proof using HA HB.
  intros C H; eapply tp_abs; [apply FO_mksum, Hc|].
  apply elim_of_fwd, ctor_elim_fwd, sg_hit, H.
Qed.

Theorem infer_mk_sum : infer FO @ mk_sum A B ==> Sm (MkSum A B).
Proof using HA HB.
  eapply infer_tag; [apply name_concrete; [reflexivity|reflexivity|exact Hc]| |apply FO_mksum, Hc|].
  - apply concrete_is_self_typed; rewrite concreteb_tagger; apply name_concrete; [reflexivity|reflexivity|exact Hc].
  - eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec ('tagger[Fk sum_nm (Fk (code A) (code B))]) ('tagger[Fk sum_nm (Fk (code A) (code B))])) as G.
    destruct combination_eq_dec; [exact G|contradiction].
Qed.

Theorem infer_lam : forall f F, infer FO @ f ==> Sm F -> tp FO @ F @r A ==> Sm B ->
  infer FO @ lam f A B ==> Sm (Fun A B).
Proof using HA HB.
  intros f F Hf HF; eapply infer_tag; [apply name_concrete; [reflexivity|reflexivity|exact Hc]|exact Hf|apply FO_fun|].
  eapply app2; [apply guard_of_pair|apply fun_guard_hit; exact HF].
Qed.

Theorem type_app_Fun : tp FO @ Fun A B @r A ==> Sm B.
Proof. eapply tp_abs; [apply FO_fun|apply elim_of_fwd, fun_elim_hit]. Qed.
End Ctors.

Lemma names_concrete_pair : forall A B, names_concrete A -> names_concrete B -> names_concrete (A '* B).
Proof. intros A B HA HB; cbn; repeat split; assumption. Qed.

Lemma names_concrete_Fun : forall A B, names_concrete A -> names_concrete B -> names_concrete (Fun A B).
Proof. intros A B HA HB; cbn [names_concrete Fun label_of]; apply name_concrete; [reflexivity|reflexivity|apply code_pair_concrete; assumption]. Qed.
Lemma names_concrete_Sum : forall A B, names_concrete A -> names_concrete B -> names_concrete (Sum A B).
Proof. intros A B HA HB; cbn [names_concrete Sum label_of]; apply name_concrete; [reflexivity|reflexivity|apply code_pair_concrete; assumption]. Qed.

(** ** Symbolic inference and type application *)

Ltac lp_false := match goal with |- label_pair ?a ?b = false =>
  let EL := fresh "EL" in destruct (label_pair a b) eqn:EL; [exfalso; let m := fresh "m" in let Em := fresh "Em" in
  destruct (label_pair_K1 _ _ EL) as [m Em]; first [discriminate Em | exact (code_not_K1 _ _ Em)]|reflexivity] end.
Ltac lo_none := match goal with |- label_of ?t = None =>
  let EL := fresh "EL" in destruct (label_of t) eqn:EL; [exfalso; apply label_of_some in EL; discriminate EL|reflexivity] end.

Ltac buildF := first
  [ eassumption
  | apply infer_leaf
  | (apply infer_stem; buildF)
  | (apply infer_mk_fun; assumption)
  | (apply infer_mk_sum; assumption)
  | (apply concrete_is_self_typed; vm_compute; reflexivity)
  | (eapply infer_fork; [reflexivity|buildF|buildF|first [reflexivity|lp_false]]) ].

Ltac tpsF := repeat first
  [ eassumption
  | (apply type_app_Fun; assumption)
  | (apply type_app_Sum; [apply FO_sum| |])
  | (apply type_app_mk_fun; [assumption|assumption|])
  | (apply type_app_mk_sum; [assumption|assumption|first [left; reflexivity|right; reflexivity]])
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd
  | apply app_I ].

Section Axioms.
Variables A B C : Combination.
Hypothesis HA : names_concrete A.
Hypothesis HB : names_concrete B.
Hypothesis HC : names_concrete C.

Theorem infer_ax_fst : infer FO @ ax_fst A B ==> Sm (Fun (A '* B) A).
Proof using HA HB.
  unfold ax_fst; eapply infer_lam; [apply names_concrete_pair; assumption|assumption|apply concrete_is_self_typed; reflexivity|].
  tpsF.
Qed.

Theorem infer_ax_snd : infer FO @ ax_snd A B ==> Sm (Fun (A '* B) B).
Proof using HA HB.
  unfold ax_snd; eapply infer_lam; [apply names_concrete_pair; assumption|assumption|apply concrete_is_self_typed; reflexivity|].
  tpsF.
Qed.

Let HAB := names_concrete_Fun A B HA HB.
Let HAC := names_concrete_Fun A C HA HC.
Let HBC := names_concrete_Fun B C HB HC.
Let HBA := names_concrete_Fun B A HB HA.
Let HABC := names_concrete_Fun A (Fun B C) HA HBC.
Let HSAB := names_concrete_Sum A B HA HB.
Let HSABC := names_concrete_Fun (Sum A B) C HSAB HC.
Let HPAB := names_concrete_pair A B HA HB.
Let HFAB := names_concrete_Fun B (A '* B) HB HPAB.

Theorem infer_ax_K : infer FO @ ax_K A B ==> Sm (Fun A (Fun B A)).
Proof using HA HB.
  unfold ax_K, axK_body; eapply infer_lam; [assumption|exact HBA|buildF|tpsF].
Qed.

Theorem infer_ax_S : infer FO @ ax_S A B C ==> Sm (Fun (Fun A (Fun B C)) (Fun (Fun A B) (Fun A C))).
Proof using HA HB HC.
  pose proof (names_concrete_Fun _ _ HAB HAC) as H1.
  unfold ax_S, axS_body; eapply infer_lam; [exact HABC|exact H1|buildF|tpsF].
Qed.

Theorem infer_ax_pair : infer FO @ ax_pair A B ==> Sm (Fun A (Fun B (A '* B))).
Proof using HA HB.
  unfold ax_pair, axpair_body; eapply infer_lam; [assumption|exact HFAB|buildF|tpsF].
Qed.

Theorem infer_ax_left : infer FO @ ax_left A B ==> Sm (Fun A (Sum A B)).
Proof using HA HB.
  unfold ax_left, axleft_body; eapply infer_lam; [assumption|exact HSAB|buildF|tpsF].
Qed.

Theorem infer_ax_right : infer FO @ ax_right A B ==> Sm (Fun B (Sum A B)).
Proof using HA HB.
  unfold ax_right, axright_body; eapply infer_lam; [assumption|exact HSAB|buildF|tpsF].
Qed.

Theorem infer_ax_case : infer FO @ ax_case A B C ==> Sm (Fun (Fun A C) (Fun (Fun B C) (Fun (Sum A B) C))).
Proof using HA HB HC.
  pose proof (names_concrete_Fun _ _ HBC HSABC) as H1.
  unfold ax_case, axcase_body; eapply infer_lam; [exact HAC|exact H1|buildF|tpsF].
Qed.
End Axioms.

Theorem infer_ax_top : infer FO @ Lf ==> Sm Lf.
Proof. apply infer_leaf. Qed.

(** ** Propositions as types *)

Lemma iter_concrete : forall k, concreteb (Nat.iter k Sm Lf) = true.
Proof. induction k as [|k IH]; [reflexivity|change (concreteb (Sm (Nat.iter k Sm Lf)) = true); exact IH]. Qed.

Lemma denote_names_concrete : forall p, names_concrete (denote p).
Proof.
  induction p as [i| | |p IHp q IHq|p IHp q IHq|p IHp q IHq]; cbn [denote].
  - unfold Atom, atom_nm, atom_head; change (concreteb (Nat.iter 30 Sm Lf) && concreteb (Nat.iter i Sm Lf) = true); rewrite !iter_concrete; reflexivity.
  - exact I.
  - reflexivity.
  - apply names_concrete_pair; assumption.
  - apply names_concrete_Sum; assumption.
  - apply names_concrete_Fun; assumption.
Qed.

Lemma derivation_typed_evaluates : forall p, derivable p ->
  exists e v, infer_expression FO @ e ==> Sm (denote p) /\ e ==> v /\ realizes p v.
Proof.
  intros p D; induction D.
  - exists (Sm (ax_K (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_K; apply denote_names_concrete|split; [apply eval_val|apply realizes_K]].
  - exists (Sm (ax_S (denote p) (denote q) (denote r))); eexists; split; [apply ie_stem, infer_ax_S; apply denote_names_concrete|split; [apply eval_val|apply realizes_S]].
  - exists (Sm (ax_pair (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_pair; apply denote_names_concrete|split; [apply eval_val|apply realizes_pair]].
  - exists (Sm (ax_fst (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_fst; apply denote_names_concrete|split; [apply eval_val|apply realizes_fst]].
  - exists (Sm (ax_snd (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_snd; apply denote_names_concrete|split; [apply eval_val|apply realizes_snd]].
  - exists (Sm (ax_left (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_left; apply denote_names_concrete|split; [apply eval_val|apply realizes_left]].
  - exists (Sm (ax_right (denote p) (denote q))); eexists; split; [apply ie_stem, infer_ax_right; apply denote_names_concrete|split; [apply eval_val|apply realizes_right]].
  - exists (Sm (ax_case (denote p) (denote q) (denote r))); eexists; split; [apply ie_stem, infer_ax_case; apply denote_names_concrete|split; [apply eval_val|apply realizes_case]].
  - exists (Sm Lf), Lf; split; [apply ie_stem, infer_ax_top|split; [apply eval_val|apply realizes_top]].
  - exists (Sm (absurd (denote p))); eexists; split; [apply ie_stem, infer_absurd; apply denote_names_concrete|split; [apply eval_val|apply realizes_exfalso]].
  - destruct IHD1 as [e1 [f [T1 [He1 Hf]]]]; destruct IHD2 as [e2 [a [T2 [He2 Ha]]]].
    destruct (Hf a Ha) as [w [Hw Hwr]].
    exists (Fk e1 e2), w; split; [|split; [eapply eval_pair; eassumption|exact Hwr]].
    eapply ie_fork; [exact T1|exact T2|apply type_app_Fun].
Qed.

Theorem propositions_as_types : forall p, derivable p -> exists e, infer_expression FO @ e ==> Sm (denote p).
Proof. intros p D; destruct (derivation_typed_evaluates p D) as [e [v [H _]]]; exists e; exact H. Qed.

Theorem derivation_evaluates : forall p, derivable p ->
  exists e v, infer_expression FO @ e ==> Sm (denote p) /\ e ==> v /\ infer FO @ v ==> Sm (denote p) /\ realizes p v.
Proof.
  intros p D; destruct (derivation_typed_evaluates p D) as [e [v [He [Hv Hr]]]].
  exists e, v; repeat split; try assumption.
  destruct fun_ontology_typing_sound as [_ P]; exact (P e v _ Hv He).
Qed.

(** Examples at atoms: [P * Q -> Q * P] and contraposition. *)
Definition conj_swap_body : Combination := Eval cbn in to_tree
  (star "p" ((Val 'snd @@ Ref "p") ''* (Val 'fst @@ Ref "p"))).
Definition conj_swap (P Q : Combination) : Combination := lam conj_swap_body (P '* Q) (Q '* P).
Theorem example_conj_swap : infer FO @ conj_swap (Atom 0) (Atom 1) ==> Sm (Fun (Atom 0 '* Atom 1) (Atom 1 '* Atom 0)).
Proof. apply (runp_sound 40); vm_done. Qed.

(** Stage 10 (step 83): contraposition, for all types with concrete names and at atoms. *)
Definition Neg (X : Combination) : Combination := Fun X Empty.

Definition contrapositive_body (P Q : Combination) : Combination := Eval cbn -[mk_fun Fun] in to_tree
  (star "f" (op (mk_fun (Fun Q Empty) (Fun P Empty)) @@
     star "g" (op (mk_fun P Empty) @@ star "x" (Ref "g" @@ (Ref "f" @@ Ref "x"))))).
Definition contrapositive (P Q : Combination) : Combination :=
  lam (contrapositive_body P Q) (Fun P Q) (Fun (Neg Q) (Neg P)).

Local Opaque mk_fun Fun.
Lemma names_concrete_Empty : names_concrete Empty.
Proof. reflexivity. Qed.

Theorem infer_contrapositive : forall P Q, names_concrete P -> names_concrete Q ->
  infer FO @ contrapositive P Q ==> Sm (Fun (Fun P Q) (Fun (Neg Q) (Neg P))).
Proof.
  intros P Q HP HQ.
  pose proof names_concrete_Empty as HE.
  pose proof (names_concrete_Fun _ _ HP HQ) as HPQ.
  pose proof (names_concrete_Fun _ _ HQ HE) as HNQ.
  pose proof (names_concrete_Fun _ _ HP HE) as HNP.
  pose proof (names_concrete_Fun _ _ HNQ HNP) as H1.
  unfold contrapositive, contrapositive_body, Neg; eapply infer_lam; [exact HPQ|exact H1|buildF|tpsF].
Qed.

Theorem example_contraposition :
  infer FO @ contrapositive (Atom 0) (Atom 1) ==> Sm (Fun (Fun (Atom 0) (Atom 1)) (Fun (Neg (Atom 1)) (Neg (Atom 0)))).
Proof. apply (runp_sound 60); vm_done. Qed.
