(** * Step 82, stage 9: the extension of paper_ontology by function types.

    [fun_ontology = rows_f (PO_rows ++ [gen_lam]) (alt PO_fam fam_fun)]:
    the rows and families of [paper_ontology] (arrays included since
    stage 8), then the generic lambda constructor as a row and the
    function family (function types and their constructors).  It is sound
    by values: the rows and families as for [paper_ontology]
    ([paper_parts_sound], [gpre_decl_sound], [gemp_decl_sound],
    [array_decl_sound]), the function declaration by typing
    ([fun_decl_sound_by_typing], any ontology), and the constructors as
    constructors. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums glam array_family gen_none paper_ontology.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition F_fam : Combination := alt PO_fam fam_fun.
(** Stage 6: the generic lambda constructor [gen_lam] is a row. *)
Definition FO_rows : list (Combination * Combination) := (PO_rows ++ [(gen_lam_nm, D_glam)])%list.
Definition fun_ontology : Combination := rows_f FO_rows F_fam.

(** [lookup_app] is in paper_ontology.v (stage 8). *)
Local Notation FO := fun_ontology.

Lemma F_fam_partial : forall n, exists p, F_fam @ n ==> p.
Proof. intros n; apply alt_partial, PO_fam_partial. Qed.

(** [arr_fam_miss_fk] is in paper_ontology.v (step 87). *)
(** [PO_fam] misses the function family. *)
Lemma PO_fam_miss_fun : forall h r a, h = fun_nm \/ h = mkfun_nm -> PO_fam @ Fk h r @r a ==> Lf.
Proof.
  intros h r a Hh; unfold PO_fam; apply alt_none; [apply P_fam_miss_fun, Hh|].
  apply arr_fam_miss_fk; destruct Hh as [->| ->]; discriminate.
Qed.

Lemma FO_static : forall n D, lookup P_rows n = Some D -> FO @ n @r tp FO ==> Sm D.
Proof.
  intros n D H; destruct (F_fam_partial n) as [p Hp]; unfold FO; eapply rows_f_hit; [eassumption|].
  unfold FO_rows, PO_rows; rewrite !lookup_app, H; reflexivity.
Qed.

Lemma FO_gpre : FO @ gen_prepend_nm @r tp FO ==> Sm D_gpre.
Proof.
  destruct (F_fam_partial gen_prepend_nm) as [p Hp]; unfold FO; eapply rows_f_hit; [eassumption|].
  unfold FO_rows, PO_rows; rewrite !lookup_app; reflexivity.
Qed.

Lemma FO_gemp : FO @ gen_empty_nm @r tp FO ==> Sm D_gemp.
Proof.
  destruct (F_fam_partial gen_empty_nm) as [p Hp]; unfold FO; eapply rows_f_hit; [eassumption|].
  unfold FO_rows, PO_rows; rewrite !lookup_app; reflexivity.
Qed.

Lemma FO_glam : FO @ gen_lam_nm @r tp FO ==> Sm D_glam.
Proof.
  destruct (F_fam_partial gen_lam_nm) as [p Hp]; unfold FO; eapply rows_f_hit; [eassumption|].
  unfold FO_rows, PO_rows; rewrite !lookup_app; reflexivity.
Qed.

Lemma FO_gnone : FO @ gen_none_nm @r tp FO ==> Sm D_gnone.
Proof.
  destruct (F_fam_partial gen_none_nm) as [p Hp]; unfold FO; eapply rows_f_hit; [eassumption|].
  unfold FO_rows, PO_rows; rewrite !lookup_app; reflexivity.
Qed.

Lemma FO_opt : forall r, FO @ opt_tag r @r tp FO ==> Sm (D_opt r).
Proof. intros r; unfold FO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply alt_some; [apply P_fam_opt|apply arr_fam_partial]|apply fam_fun_partial]. Qed.

Lemma FO_update : FO @ update_nm @r tp FO ==> Sm (D_upd update_nm (tp FO)).
Proof. unfold FO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply alt_some; [apply P_fam_update|apply arr_fam_partial]|apply fam_fun_partial]. Qed.

Lemma FO_mku : FO @ mku_nm @r tp FO ==> Sm (D_mku (tp FO)).
Proof. unfold FO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply alt_some; [apply P_fam_mku|apply arr_fam_partial]|apply fam_fun_partial]. Qed.

Lemma FO_list : forall r, FO @ list_tag r @r tp FO ==> Sm (D_list r).
Proof. intros r; unfold FO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply alt_some; [apply P_fam_list|apply arr_fam_partial]|apply fam_fun_partial]. Qed.

Lemma FO_query : forall r, concreteb r = true -> FO @ query_tag r @r tp FO ==> Sm (D_query r (tp FO)).
Proof.
  intros r Hr; unfold FO; apply rows_f_miss; [reflexivity|].
  apply alt_some; [apply alt_some; [apply P_fam_query; exact Hr|apply arr_fam_partial]|apply fam_fun_partial].
Qed.

Lemma FO_fun : forall r, FO @ Fk fun_nm r @r tp FO ==> Sm (fun_D r (tp FO)).
Proof.
  intros r; unfold FO; apply rows_f_miss; [reflexivity|].
  apply alt_none; [apply PO_fam_miss_fun; left; reflexivity|].
  unfold fam_fun; apply alt_some; [apply fun_entry_hit|].
  apply alt_partial. pose proof (get_par_spec mkfun_nm (Fk fun_nm r)) as Hp; cbn [par_of] in Hp.
  destruct (combination_eq_dec mkfun_nm fun_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  Local Transparent get_par is_concrete. unfold mkfun_entry; eexists; ev2.
Qed.
Local Opaque get_par is_concrete.

Lemma FO_array : forall r, FO @ Fk array_nm r @r tp FO ==> Sm (D_array r).
Proof.
  intros r; unfold FO; apply rows_f_miss; [reflexivity|].
  apply alt_some; [|apply fam_fun_partial]. unfold PO_fam.
  apply alt_none; [apply P_fam_miss_array|].
  unfold arr_fam; apply alt_some; [apply array_entry_hit|]. unfold no_rows; eexists; evaluate.
Qed.

Lemma FO_sum : forall r, FO @ Fk sum_nm r @r tp FO ==> Sm (D_sum r).
Proof. intros r; unfold FO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply alt_some; [apply P_fam_sum|apply arr_fam_partial]|apply fam_fun_partial]. Qed.

Theorem fun_ontology_sound : ontology_sound FO.
Proof.
  intros n D H.
  destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst. unfold FO_rows, PO_rows in HL; rewrite !lookup_app in HL.
    destruct (lookup P_rows n) as [D0|] eqn:HL0.
    + inversion HL; subst. apply (paper_parts_sound FO FO_static FO_update FO_list FO_query FO_sum); left; exact HL0.
    + cbn [lookup] in HL; destruct (combination_eq_dec gen_prepend_nm n) as [<-|Hn].
      * inversion HL; subst. apply gpre_decl_sound, FO_array.
      * destruct (combination_eq_dec gen_empty_nm n) as [<-|Hn2].
        -- inversion HL; subst. apply gemp_decl_sound, FO_array.
        -- destruct (combination_eq_dec gen_none_nm n) as [<-|Hn3].
           ++ inversion HL; subst. apply gen_none_decl_sound, FO_opt.
           ++ destruct (combination_eq_dec gen_lam_nm n) as [<-|Hn4]; [|discriminate HL].
              inversion HL; subst. apply glam_decl_sound, FO_fun.
  - unfold F_fam in HF.
    destruct (alt_inv _ _ _ _ _ HF) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst. unfold PO_fam in H1.
      destruct (alt_inv _ _ _ _ _ H1) as [[D2 [H3 E']]|[[H3 H4]|[x [y [_ E']]]]]; [|..|discriminate].
      * inversion E'; subst. apply (paper_parts_sound FO FO_static FO_update FO_list FO_query FO_sum); right; exact H3.
      * destruct (arr_fam_inv _ _ _ H4) as [r [-> ->]]. apply array_decl_sound.
    + destruct (fam_fun_inv _ _ _ H2) as [[r [-> ->]]|[r [-> [Hc ->]]]].
      * apply decl_sound_by_typing_values, fun_decl_sound_by_typing.
      * eapply ctor_decl_sound; [cbn; exact Hc|apply FO_fun|apply guard_of_pair].
Qed.

Corollary fun_ontology_typing_sound : typing_sound FO.
Proof. apply evaluation_preserves_typing, fun_ontology_sound. Qed.

Theorem fun_ontology_concrete : concrete FO.
Proof. apply concreteb_spec; vm_compute; reflexivity. Qed.

Theorem fun_infer_self_typed : infer FO @ infer FO ==> Sm (infer FO).
Proof. apply infer_self_typed, fun_ontology_concrete. Qed.

(** ** Empty and ex falso at the extension *)

Theorem fun_type_app_Empty : forall A, tp FO @ Empty @r code A ==> Sm A.
Proof. intros A; eapply tp_abs; [apply FO_static; reflexivity|apply elim_of_fwd, empty_elim_eval]. Qed.

Definition absurd (A : Combination) : Combination := lam (swap (code A)) Empty A.

Theorem infer_absurd : forall A, names_concrete A -> infer FO @ absurd A ==> Sm (Fun Empty A).
Proof.
  intros A HA; unfold absurd, lam, Fun.
  assert (HL : label_pair (code Empty) (code A) = false)
    by (destruct (label_pair (code Empty) (code A)) eqn:E; [destruct (label_pair_K1 _ _ E) as [m Em];
        exfalso; exact (code_not_K1 A m Em)|reflexivity]).
  eapply infer_tag; [| |apply FO_fun|].
  - unfold fun_tag; cbn [concreteb]; rewrite (code_concrete A HA), HL; reflexivity.
  - apply concrete_is_self_typed; unfold swap; cbn; rewrite (code_concrete A HA).
    destruct (code A) as [| |[| |] m] eqn:E; try reflexivity; exfalso; exact (code_not_K1 A m E).
  - eapply app2; [apply guard_of_pair|apply fun_guard_hit].
    unfold swap; eapply tp_S2_fwd; [reflexivity|apply app_I|apply tp_K1_fwd|apply fun_type_app_Empty].
Qed.

Example FO_absurd_Nat : infer FO @ absurd Nat ==> Sm (Fun Empty Nat). Proof. apply infer_absurd; cbn; reflexivity. Qed.

(** ** Step 87: atoms are undeclared at [fun_ontology] too *)

Lemma FO_atom_undeclared : forall i, FO @ atom_nm i @r tp FO ==> Lf.
Proof.
  intros i; unfold FO; apply rows_f_miss; [reflexivity|].
  unfold F_fam; apply alt_none; [apply PO_fam_miss_atom|].
  unfold atom_nm; apply fam_fun_miss_fk; discriminate.
Qed.

Theorem no_value_Atom_FO : forall i v, ~ (infer FO @ v ==> Sm (Atom i)).
Proof.
  intros i v; apply undeclared_no_value; intros D H.
  pose proof (eval_deterministic _ _ H _ (FO_atom_undeclared i)); discriminate.
Qed.
