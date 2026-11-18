(** * Step 82, stage 5, part 2: general polymorphism.

    Type application is proved symbolically, for every type parameter, by
    the forward rules of the clauses ([tps]).  The parameter enters only
    through its code [code A] (decoded by the eliminators and guards) and
    through the hypotheses on the argument types; every other step is the
    computation of a closed program on types. *)
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries array_family.
Set Default Proof Using "Type".
Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

(** [PO_mku] is in size_queries.v since step 89. *)

Lemma bool_elim_fwd : forall n r A, bool_elim @ n @r r @r (A '* A) ==> Sm A.
Proof.
  intros n r A; unfold bool_elim. pose proof (get_rr_spec (A '* A)) as Hr. cbn [rr] in Hr.
  pose proof (equal_eq (A '* A)) as He. ev2.
Qed.
Lemma type_app_Bool : forall A, tp PO @ Bool @r (A '* A) ==> Sm A.
Proof. intros A; eapply tp_abs; [apply PO_static; reflexivity|apply elim_of_fwd, bool_elim_fwd]. Qed.

Lemma type_app_mk_nat : tp PO @ 'label[mkn_nm] @r 'S2['snd, 'K1 Nat] ==> Sm Nat.
Proof.
  eapply tp_abs; [apply PO_static; reflexivity|apply elim_of_fwd, ctor_elim_fwd].
  apply nat_guard_hit; right; reflexivity.
Qed.

(** [gsp_hit_code] is in size_queries.v since step 89. *)

Local Opaque gce_prog gne_prog le_prog lg_prog.
Lemma gce_fwd : forall A n a, names_concrete A -> gce_prog @ n @r a @r (code A '* (A '* List A)) ==> Sm (List A).
Proof.
  intros A n a HA. Local Transparent gce_prog. unfold gce_prog. Local Opaque gce_prog.
  pose proof (is_concrete_bt (code A)) as Hc; rewrite (code_concrete A HA) in Hc; cbn [bt] in Hc.
  pose proof (decode_p_code A) as Hd. pose proof (equal_eq (code A '* (A '* List A))) as He.
  unfold List, list_tag.
  split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | progress cbn [left_of right_of stem_of] | progress evaluate2].
Qed.
Lemma type_app_gen_cons : forall A, names_concrete A ->
  tp PO @ 'label[gen_cons_nm] @r (code A '* (A '* List A)) ==> Sm (List A).
Proof. intros A HA; eapply tp_abs; [apply PO_static; reflexivity|apply elim_of_fwd, gce_fwd, HA]. Qed.

Lemma gne_fwd : forall A n a, names_concrete A -> gne_prog @ n @r a @r code A ==> Sm (List A).
Proof.
  intros A n a HA. Local Transparent gne_prog. unfold gne_prog. Local Opaque gne_prog.
  pose proof (is_concrete_bt (code A)) as Hc; rewrite (code_concrete A HA) in Hc; cbn [bt] in Hc.
  pose proof (decode_p_code A) as Hd. unfold List, list_tag. ev2.
Qed.
Lemma type_app_gen_nil : forall A, names_concrete A -> tp PO @ 'label[gen_nil_nm] @r code A ==> Sm (List A).
Proof. intros A HA; eapply tp_abs; [apply PO_static; reflexivity|apply elim_of_fwd, gne_fwd, HA]. Qed.

Lemma le_fwd : forall r A n a B S, decode r = Some A -> a @ S @r (A '* 'label[Fk list_nm r]) ==> Sm B ->
  'wait[le_prog, r] @ n @r a @r (B '* S) ==> Sm B.
Proof.
  intros r A n a B S HA H. destruct (app2_inv _ _ _ _ H) as [p [Hp1 Hp2]].
  pose proof (decode_p_eval r) as Hd; rewrite HA in Hd; cbn [opt] in Hd.
  pose proof (equal_eq (B '* S)) as He1; pose proof (equal_eq B) as He2.
  eapply eval_appl; [eapply app2; [apply wait_eval|]|].
  Local Transparent le_prog. unfold le_prog. Local Opaque le_prog.
  all: split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | progress cbn [left_of right_of stem_of] | progress evaluate2].
Qed.

Lemma type_app_List : forall A B S, tp PO @ S @r (A '* List A) ==> Sm B -> tp PO @ List A @r (B '* S) ==> Sm B.
Proof.
  intros A B S H; eapply tp_abs; [apply PO_list|apply elim_of_fwd].
  unfold list_elim; apply name_elim_iff; cbn [right_of]; eapply le_fwd; [apply decode_code|exact H].
Qed.

Ltac lp_false := match goal with |- label_pair ?a ?b = false =>
  let EL := fresh "EL" in destruct (label_pair a b) eqn:EL; [exfalso; let m := fresh "m" in let Em := fresh "Em" in
  destruct (label_pair_K1 _ _ EL) as [m Em]; discriminate Em|reflexivity] end.
Ltac lo_none := match goal with |- label_of ?t = None =>
  let EL := fresh "EL" in destruct (label_of t) eqn:EL; [exfalso; apply label_of_some in EL; discriminate EL|reflexivity] end.
Ltac tps := repeat first
  [ eassumption
  | apply type_app_mk_nat
  | apply type_app_Bool
  | apply type_app_Update
  | (apply type_app_gen_cons; assumption)
  | (apply type_app_gen_nil; assumption)
  | apply type_app_List
  | (apply (mku_app PO PO_mku); unfold upd_guard;
       first [ (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gch_miss; discriminate|reflexivity|]; apply or_g_l; eapply gsp_hit_code; [vm_compute; reflexivity|])
             | (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gch_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit]) ])
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].


Ltac by_runP2 := apply (runp_sound 40); vm_done.

(** ** Lists *)

Definition T_app : Combination := Eval vm_compute in ty_of appendR.
Definition T_rev : Combination := Eval vm_compute in ty_of reverseR.
Definition T_len : Combination := Eval vm_compute in ty_of lengthR.
Definition T_map : Combination := Eval vm_compute in ty_of mapR.

Lemma infer_appendR : infer PO @ appendR ==> Sm T_app. Proof. by_runP2. Qed.
Lemma infer_reverseR : infer PO @ reverseR ==> Sm T_rev. Proof. by_runP2. Qed.
Lemma infer_lengthR : infer PO @ lengthR ==> Sm T_len. Proof. by_runP2. Qed.
Lemma infer_mapR : infer PO @ mapR ==> Sm T_map. Proof. by_runP2. Qed.

Section ListPoly.
Variable A : Combination.
Hypothesis HA : names_concrete A.

Lemma append_type_app : tp PO @ T_app @r (code A '* (List A '* List A)) ==> Sm (List A).
Proof using HA. unfold T_app; tps. Qed.

Theorem reverse_polymorphic : tp PO @ T_rev @r (code A '* List A) ==> Sm (List A).
Proof using HA. unfold T_rev; tps. Qed.

Theorem length_polymorphic : tp PO @ T_len @r (code A '* List A) ==> Sm Nat.
Proof using HA. unfold T_len; tps. Qed.

Variable B F : Combination.
Hypothesis HB : names_concrete B.
Hypothesis HF : tp PO @ F @r A ==> Sm B.

Lemma map_type_app : tp PO @ T_map @r (code A '* (code B '* (F '* List A))) ==> Sm (List B).
Proof using HA HB HF. unfold T_map; tps. Qed.
End ListPoly.

(** Step 87: the paper's statements, with the inferred type and its
    type applications in one Theorem. *)
Theorem append_polymorphic : exists T, infer PO @ appendR ==> Sm T /\
  forall A, names_concrete A -> tp PO @ T @r (code A '* (List A '* List A)) ==> Sm (List A).
Proof. exists T_app; split; [exact infer_appendR|exact append_type_app]. Qed.

Theorem map_polymorphic : exists T, infer PO @ mapR ==> Sm T /\
  forall A B F, names_concrete A -> names_concrete B -> tp PO @ F @r A ==> Sm B ->
    tp PO @ T @r (code A '* (code B '* (F '* List A))) ==> Sm (List B).
Proof.
  exists T_map; split; [exact infer_mapR|].
  intros A B F HA HB HF; exact (map_type_app A HA B F HB HF).
Qed.

(** The element type of a typed list has concrete names. *)
Lemma list_type_names : forall O xs A, infer O @ xs ==> Sm (List A) -> names_concrete A.
Proof.
  intros O xs A H; apply code_concrete_inv. unfold List in H.
  destruct (no_junk O xs _ H) as [f [F [D [_ [Hn _]]]]].
  unfold list_tag in Hn; cbn in Hn; exact Hn.
Qed.

Theorem infer_append_application : forall A xs ys,
  infer PO @ xs ==> Sm (List A) -> infer PO @ ys ==> Sm (List A) ->
  infer_expression PO @ (appendR @ (code A '* (xs '* ys))) ==> Sm (List A).
Proof.
  intros A xs ys Hx Hy; pose proof (list_type_names _ _ _ Hx) as HA.
  assert (Hq : infer PO @ (code A '* (xs '* ys)) ==> Sm (code A '* (List A '* List A)))
    by (apply pair_typed; [apply code_self_typed, HA|apply pair_typed; assumption]).
  eapply ie_fork; [apply ie_stem, infer_appendR|apply ie_stem, Hq|apply append_type_app, HA].
Qed.

Theorem infer_map_application : forall A B f F xs, names_concrete B ->
  infer PO @ f ==> Sm F -> tp PO @ F @r A ==> Sm B -> infer PO @ xs ==> Sm (List A) ->
  infer_expression PO @ (mapR @ (code A '* (code B '* (f '* xs)))) ==> Sm (List B).
Proof.
  intros A B f F xs HB Hf HF Hx; pose proof (list_type_names _ _ _ Hx) as HA.
  assert (Hq : infer PO @ (code A '* (code B '* (f '* xs))) ==> Sm (code A '* (code B '* (F '* List A))))
    by (apply pair_typed; [apply code_self_typed, HA|apply pair_typed; [apply code_self_typed, HB|apply pair_typed; assumption]]).
  eapply ie_fork; [apply ie_stem, infer_mapR|apply ie_stem, Hq|apply map_type_app; assumption].
Qed.

(** ** Minimisation *)

Definition T_min : Combination := Eval vm_compute in ty_of minimisation.
Lemma infer_minimisation : infer PO @ minimisation ==> Sm T_min. Proof. by_runP2. Qed.

Lemma minimisation_type_app : forall P, tp PO @ P @r Nat ==> Sm Bool -> tp PO @ T_min @r P ==> Sm Update.
Proof. intros P HP; unfold T_min; tps. Qed.

(** Step 87: the paper's statement, with the inferred type in the Theorem. *)
Theorem minimisation_polymorphic : forall P, tp PO @ P @r Nat ==> Sm Bool ->
  exists M, infer PO @ minimisation ==> Sm M /\ tp PO @ M @r P ==> Sm Update.
Proof. intros P HP; exists T_min; split; [exact infer_minimisation|exact (minimisation_type_app P HP)]. Qed.

(** ** Addition and multiplication (no type parameter) *)

Definition T_add : Combination := Eval vm_compute in ty_of add.
Definition T_mul : Combination := Eval vm_compute in ty_of mul.
Theorem add_typed : infer PO @ add ==> Sm T_add /\ tp PO @ T_add @r (Nat '* Nat) ==> Sm Nat.
Proof. split; by_runP2. Qed.
Theorem mul_typed : infer PO @ mul ==> Sm T_mul /\ tp PO @ T_mul @r (Nat '* Nat) ==> Sm Nat.
Proof. split; by_runP2. Qed.

(** ** Parity and comparison (no type parameter)

    Step 88: the paper's typings of [is_odd] and [ge], at [paper_ontology].
    The versions at [O_gen] are [is_odd_typed_gen] and [type_app_ge_gen]. *)

Definition T_is_odd : Combination := Eval vm_compute in ty_of is_odd.
Definition T_ge : Combination := Eval vm_compute in ty_of ge.
Theorem is_odd_typed : infer PO @ is_odd ==> Sm T_is_odd /\ tp PO @ T_is_odd @r Nat ==> Sm Bool.
Proof. split; by_runP2. Qed.
Theorem type_app_ge : infer PO @ ge ==> Sm T_ge /\ tp PO @ T_ge @r (Nat '* Nat) ==> Sm Bool.
Proof. split; by_runP2. Qed.

(** ** Minimisation at is_odd *)

Theorem minimise_is_odd : minimisation @ is_odd @r zero ==> succ zero /\
  infer_expression PO @ (minimisation @ is_odd @r zero) ==> Sm Nat.
Proof. split; by_runP2. Qed.
