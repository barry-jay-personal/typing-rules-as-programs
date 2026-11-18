(** * Step 82, stage 4, part 4: one combined ontology.

    [paper_ontology = rows_f PO_rows PO_fam], with
    [PO_rows = P_rows ++ [gen_prepend; gen_empty; gen_none]] and
    [PO_fam = alt P_fam arr_fam] (stage 8: arrays, array_family.v), declares
    - by rows: Bool, Nat (Scott numerals with their eliminator), the Bool
      and Nat constructors, Salary, Employee, Department and the Salary
      constructor, the generic constructors gen_cons and gen_nil, and Empty
      (whose eliminator decodes codes);
    - by families: Update and its constructor, lists and the cell
      constructors, queries and the query constructor, options, and sums
      and the sum constructor (stage 6);
    - arrays (stage 8): the array family by [arr_fam], and the generic
      constructors gen_prepend and gen_empty by rows;
    - step 84: the generic constructor gen_none by a row.
    Step 87: the atoms are not declared.  Their names [atom_nm i] have
    the head [atom_head], which no row or family matches, so no atom has
    a value ([no_value_Atom], every i).
    Function types are not in it (Barry, stage 5): they are in the
    extension [fun_ontology] (fun_ontology.v).
    It is sound by values, assembled from the declaration lemmas, and it
    is concrete, so [infer : infer] at it. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums array_family gen_none.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

(** Step 87: an atom name is a fork with the head [atom_head], so that
    it differs from every declared name, for every [i]. *)
Definition atom_head : Combination := Nat.iter 30 Sm Lf.
Definition atom_nm (i : nat) : Combination := Fk atom_head (Nat.iter i Sm Lf).
Definition Atom (i : nat) : Combination := 'label[atom_nm i].

Definition P_rows : list (Combination * Combination) :=
  (G_rows ++ [(empty_nm, D_empty)])%list.
Definition P_fam : Combination := alt L_fam (alt query_entry (alt opt_entry (alt mkq_entry sum_fam))).
Definition PO_rows : list (Combination * Combination) := (P_rows ++ [(gen_prepend_nm, D_gpre); (gen_empty_nm, D_gemp); (gen_none_nm, D_gnone)])%list.
Definition PO_fam : Combination := alt P_fam arr_fam.
Definition paper_ontology : Combination := rows_f PO_rows PO_fam.
Local Notation PO := paper_ontology.

(** ** Misses and partial applications of the family entries *)

Lemma query_entry_partial : forall n, exists p, query_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec query_nm n) as Hp.
  destruct (par_of query_nm n); cbn [opt] in Hp; unfold query_entry; eexists; ev2.
Qed.

Lemma query_entry_miss : forall n a, par_of query_nm n = None -> query_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold query_entry; pose proof (get_par_spec query_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma fun_entry_miss : forall n a, par_of fun_nm n = None -> fun_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold fun_entry; pose proof (get_par_spec fun_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma mkfun_entry_miss : forall n a, par_of mkfun_nm n = None -> mkfun_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold mkfun_entry; pose proof (get_par_spec mkfun_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma mkcons_entry_miss : forall n a, par_of mkcons_nm n = None -> mkcons_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold mkcons_entry; pose proof (get_par_spec mkcons_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma par_of_other : forall h h2 r, h <> h2 -> par_of h (Fk h2 r) = None.
Proof. intros h h2 r H; cbn; destruct (combination_eq_dec h h2); [contradiction|reflexivity]. Qed.

Lemma L_fam_miss_fk : forall h r a, h <> list_nm -> h <> mkcons_nm -> L_fam @ Fk h r @r a ==> Lf.
Proof.
  intros h r a H1 H2; unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_none; [apply list_entry_miss, par_of_other; congruence|].
  apply alt_none; [apply mkcons_entry_miss, par_of_other; congruence|unfold no_rows; evaluate].
Qed.

Lemma fam_fun_miss_fk : forall h r a, h <> fun_nm -> h <> mkfun_nm -> fam_fun @ Fk h r @r a ==> Lf.
Proof.
  intros h r a H1 H2; unfold fam_fun.
  apply alt_none; [apply fun_entry_miss, par_of_other; congruence|].
  apply alt_none; [apply mkfun_entry_miss, par_of_other; congruence|unfold no_rows; evaluate].
Qed.

Lemma fam_fun_partial' : forall n, exists p, fam_fun @ n ==> p.
Proof. exact fam_fun_partial. Qed.

Lemma tail_partial : forall n, exists p, alt query_entry (alt opt_entry (alt mkq_entry sum_fam)) @ n ==> p.
Proof. intros n; apply alt_partial, query_entry_partial. Qed.

Lemma opt_entry_miss : forall n a, par_of opt_nm n = None -> opt_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold opt_entry; pose proof (get_par_spec opt_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

(** ** The families, for any type application [a] *)

Lemma P_fam_partial : forall n, exists p, P_fam @ n ==> p.
Proof. intros n; apply alt_partial, L_fam_partial. Qed.

Lemma P_fam_update : forall a, P_fam @ update_nm @r a ==> Sm (D_upd update_nm a).
Proof.
  intros a; unfold P_fam; apply alt_some; [|apply tail_partial].
  unfold L_fam; apply alt_some; [apply upd_fam_update|]. apply alt_partial, list_entry_partial.
Qed.

Lemma P_fam_mku : forall a, P_fam @ mku_nm @r a ==> Sm (D_mku a).
Proof.
  intros a; unfold P_fam; apply alt_some; [|apply tail_partial].
  unfold L_fam; apply alt_some; [apply upd_fam_mku|]. apply alt_partial, list_entry_partial.
Qed.

Lemma P_fam_list : forall r a, P_fam @ list_tag r @r a ==> Sm (D_list r).
Proof.
  intros r a; unfold P_fam; apply alt_some; [|apply tail_partial].
  unfold L_fam. apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_some; [apply list_entry_hit|]. apply alt_partial.
  pose proof (get_par_spec mkcons_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm list_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  Local Transparent get_par is_concrete. unfold mkcons_entry; eexists; ev2.
Qed.
Local Opaque get_par is_concrete.

Lemma P_fam_query : forall r a, concreteb r = true -> P_fam @ query_tag r @r a ==> Sm (D_query r a).
Proof.
  intros r a Hr; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_some; [apply query_entry_hit; exact Hr|]. apply alt_partial, opt_entry_partial.
Qed.

Lemma P_fam_miss_fun : forall h r a, h = fun_nm \/ h = mkfun_nm -> P_fam @ Fk h r @r a ==> Lf.
Proof.
  intros h r a Hh; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; destruct Hh as [->| ->]; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; destruct Hh as [->| ->]; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; destruct Hh as [->| ->]; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; destruct Hh as [->| ->]; discriminate|].
  apply sum_fam_miss; apply par_of_other; destruct Hh as [->| ->]; discriminate.
Qed.

Lemma P_fam_inv : forall n a D, P_fam @ n @r a ==> Sm D ->
  L_fam @ n @r a ==> Sm D \/
  (exists r, n = query_tag r /\ concreteb r = true /\ D = D_query r a) \/
  (exists r, n = opt_tag r /\ D = D_opt r) \/
  (exists r, n = Fk mkq_nm r /\ concreteb r = true /\ D = D_mkq r a) \/
  (exists r, n = Fk sum_nm r /\ D = D_sum r) \/
  (exists r, n = Fk mksum_nm r /\ concreteb r = true /\ D = D_mksum r).
Proof.
  intros n a D HF; unfold P_fam in HF.
  destruct (alt_inv _ _ _ _ _ HF) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  { inversion E; subst; left; exact H1. }
  destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
  { inversion E; subst; right; left; eapply query_entry_inv; exact H3. }
  destruct (alt_inv _ _ _ _ _ H4) as [[D' [H5 E]]|[[H5 H6]|[x [y [_ E]]]]]; [|..|discriminate].
  { inversion E; subst; right; right; left; eapply opt_entry_inv; exact H5. }
  destruct (alt_inv _ _ _ _ _ H6) as [[D' [H7 E]]|[[H7 H8]|[x [y [_ E]]]]]; [|..|discriminate].
  + inversion E; subst; right; right; right; left; eapply mkq_entry_inv; exact H7.
  + right; right; right; right; apply (sum_fam_inv _ _ _ H8).
Qed.

(** ** Soundness of the rows and families, in any ontology that gives them *)

Section PaperParts.
Variable O : Combination.
Hypothesis HS : forall n D, lookup P_rows n = Some D -> O @ n @r tp O ==> Sm D.
Hypothesis HU : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).
Hypothesis HL : forall r, O @ list_tag r @r tp O ==> Sm (D_list r).
Hypothesis HQ : forall r, concreteb r = true -> O @ query_tag r @r tp O ==> Sm (D_query r (tp O)).
Hypothesis HSm : forall r, O @ Fk sum_nm r @r tp O ==> Sm (D_sum r).

Theorem paper_parts_sound : forall n D,
  lookup P_rows n = Some D \/ P_fam @ n @r tp O ==> Sm D -> decl_sound O n D.
Proof using HS HU HL HQ HSm.
  intros n D [HR|HF].
  - unfold P_rows, G_rows, D_rows, L_rows, O_rows in HR; cbn [lookup List.app] in HR.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HR; subst|]); try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply HS; reflexivity|apply guard_of_pair].
    + eapply ctor_decl_sound; [reflexivity|apply HS; reflexivity|apply guard_of_pair].
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply HS; reflexivity|apply guard_of_pair].
    + apply gcons_decl_sound, HL.
    + apply gnil_decl_sound, HL.
    + unfold D_empty; apply nothing_decl_sound.
  - destruct (P_fam_inv _ _ _ HF) as [HF'|[[r [-> [Hr ->]]]|[[r [-> ->]]|[[r [-> [Hq ->]]]|[[r [-> ->]]|[r [-> [Hc ->]]]]]]]].
    + destruct (L_fam_inv _ _ _ HF') as [[-> ->]|[[-> ->]|[[r [-> ->]]|[r [-> [Hc ->]]]]]].
      * apply upd_decl_sound_g, HU.
      * apply mku_decl_sound_g, HU.
      * apply list_decl_sound.
      * eapply ctor_decl_sound; [cbn; exact Hc|apply HL|apply guard_of_pair].
    + apply query_decl_sound_g; [apply HQ|exact Hr].
    + apply opt_decl_sound.
    + eapply ctor_decl_sound; [|apply HQ; exact Hq|apply guard_of_pair].
      unfold query_tag; cbn [concreteb]; rewrite Hq; reflexivity.
    + apply sum_decl_sound.
    + apply mksum_decl_sound; [exact HSm|exact Hc].
Qed.
End PaperParts.

(** ** Look-ups *)

Lemma lookup_app : forall l1 l2 n, lookup (l1 ++ l2) n = match lookup l1 n with Some D => Some D | None => lookup l2 n end.
Proof. induction l1 as [|[m D] l1 IH]; intros l2 n; cbn; [reflexivity|]. destruct (combination_eq_dec m n); [reflexivity|apply IH]. Qed.

Lemma PO_fam_partial : forall n, exists p, PO_fam @ n ==> p.
Proof. intros n; apply alt_partial, P_fam_partial. Qed.

Lemma PO_static : forall n D, lookup P_rows n = Some D -> PO @ n @r tp PO ==> Sm D.
Proof.
  intros n D H; destruct (PO_fam_partial n) as [p Hp]; unfold PO; eapply rows_f_hit; [eassumption|].
  unfold PO_rows; rewrite lookup_app, H; reflexivity.
Qed.

Lemma PO_gpre : PO @ gen_prepend_nm @r tp PO ==> Sm D_gpre.
Proof.
  destruct (PO_fam_partial gen_prepend_nm) as [p Hp]; unfold PO; eapply rows_f_hit; [eassumption|].
  unfold PO_rows; rewrite lookup_app; reflexivity.
Qed.

Lemma PO_gemp : PO @ gen_empty_nm @r tp PO ==> Sm D_gemp.
Proof.
  destruct (PO_fam_partial gen_empty_nm) as [p Hp]; unfold PO; eapply rows_f_hit; [eassumption|].
  unfold PO_rows; rewrite lookup_app; reflexivity.
Qed.

Lemma PO_gnone : PO @ gen_none_nm @r tp PO ==> Sm D_gnone.
Proof.
  destruct (PO_fam_partial gen_none_nm) as [p Hp]; unfold PO; eapply rows_f_hit; [eassumption|].
  unfold PO_rows; rewrite lookup_app; reflexivity.
Qed.

Lemma P_fam_opt : forall r a, P_fam @ opt_tag r @r a ==> Sm (D_opt r).
Proof.
  intros r a; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_some; [apply opt_entry_hit|]. apply alt_partial, mkq_entry_partial.
Qed.

Lemma PO_opt : forall r, PO @ opt_tag r @r tp PO ==> Sm (D_opt r).
Proof. intros r; unfold PO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply P_fam_opt|apply arr_fam_partial]. Qed.

Lemma PO_update : PO @ update_nm @r tp PO ==> Sm (D_upd update_nm (tp PO)).
Proof. unfold PO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply P_fam_update|apply arr_fam_partial]. Qed.

Lemma PO_list : forall r, PO @ list_tag r @r tp PO ==> Sm (D_list r).
Proof. intros r; unfold PO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply P_fam_list|apply arr_fam_partial]. Qed.

Lemma PO_query : forall r, concreteb r = true -> PO @ query_tag r @r tp PO ==> Sm (D_query r (tp PO)).
Proof.
  intros r Hr; unfold PO; apply rows_f_miss; [reflexivity|].
  apply alt_some; [apply P_fam_query; exact Hr|apply arr_fam_partial].
Qed.

Lemma P_fam_sum : forall r a, P_fam @ Fk sum_nm r @r a ==> Sm (D_sum r).
Proof.
  intros r a; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; discriminate|].
  apply sum_fam_sum.
Qed.

Lemma PO_sum : forall r, PO @ Fk sum_nm r @r tp PO ==> Sm (D_sum r).
Proof. intros r; unfold PO; apply rows_f_miss; [reflexivity|]. apply alt_some; [apply P_fam_sum|apply arr_fam_partial]. Qed.

Lemma P_fam_miss_array : forall r a, P_fam @ Fk array_nm r @r a ==> Lf.
Proof.
  intros r a; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; discriminate|].
  apply sum_fam_miss; apply par_of_other; discriminate.
Qed.

Lemma PO_array : forall r, PO @ Fk array_nm r @r tp PO ==> Sm (D_array r).
Proof.
  intros r; unfold PO; apply rows_f_miss; [reflexivity|].
  apply alt_none; [apply P_fam_miss_array|].
  unfold arr_fam; apply alt_some; [apply array_entry_hit|]. unfold no_rows; eexists; evaluate.
Qed.

(** ** Soundness *)

Theorem paper_ontology_sound : ontology_sound PO.
Proof.
  intros n D H.
  destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst. unfold PO_rows in HL; rewrite lookup_app in HL.
    destruct (lookup P_rows n) as [D0|] eqn:HL0.
    + inversion HL; subst. apply (paper_parts_sound PO PO_static PO_update PO_list PO_query PO_sum); left; exact HL0.
    + cbn [lookup] in HL; destruct (combination_eq_dec gen_prepend_nm n) as [<-|Hn].
      * inversion HL; subst. apply gpre_decl_sound, PO_array.
      * destruct (combination_eq_dec gen_empty_nm n) as [<-|Hn2].
        -- inversion HL; subst. apply gemp_decl_sound, PO_array.
        -- destruct (combination_eq_dec gen_none_nm n) as [<-|Hn3]; [|discriminate HL].
           inversion HL; subst. apply gen_none_decl_sound, PO_opt.
  - unfold PO_fam in HF.
    destruct (alt_inv _ _ _ _ _ HF) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst. apply (paper_parts_sound PO PO_static PO_update PO_list PO_query PO_sum); right; exact H1.
    + destruct (arr_fam_inv _ _ _ H2) as [r [-> ->]]. apply array_decl_sound.
Qed.

Corollary paper_ontology_typing_sound : typing_sound PO.
Proof. apply evaluation_preserves_typing, paper_ontology_sound. Qed.

Theorem paper_ontology_concrete : concrete PO.
Proof. apply concreteb_spec; vm_compute; reflexivity. Qed.

Theorem paper_infer_self_typed : infer PO @ infer PO ==> Sm (infer PO).
Proof. apply infer_self_typed, paper_ontology_concrete. Qed.

(** ** Empty, ex falso, atoms *)

(** A name at which the ontology gives no declaration labels no value. *)
Lemma undeclared_no_value : forall O n v, (forall D, ~ (O @ n @r tp O ==> Sm D)) ->
  ~ (infer O @ v ==> Sm ('label[n])).
Proof.
  intros O n v Hn H; destruct (no_junk O v n H) as [f [F [D [_ [_ [_ [HD _]]]]]]].
  exact (Hn D HD).
Qed.

Lemma arr_fam_miss_fk : forall h r a, h <> array_nm -> arr_fam @ Fk h r @r a ==> Lf.
Proof.
  intros h r a H; unfold arr_fam.
  apply alt_none; [|unfold no_rows; evaluate].
  unfold array_entry; pose proof (get_par_spec array_nm (Fk h r)) as Hp.
  rewrite par_of_other in Hp by congruence; cbn [opt] in Hp; ev2.
Qed.

Lemma P_fam_miss_atom : forall r a, P_fam @ Fk atom_head r @r a ==> Lf.
Proof.
  intros r a; unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; discriminate|].
  apply sum_fam_miss; apply par_of_other; discriminate.
Qed.

Lemma PO_fam_miss_atom : forall i a, PO_fam @ atom_nm i @r a ==> Lf.
Proof.
  intros i a; unfold PO_fam, atom_nm; apply alt_none; [apply P_fam_miss_atom|].
  apply arr_fam_miss_fk; discriminate.
Qed.

Lemma PO_atom_undeclared : forall i, PO @ atom_nm i @r tp PO ==> Lf.
Proof. intros i; unfold PO; apply rows_f_miss; [reflexivity|apply PO_fam_miss_atom]. Qed.

Theorem type_app_Empty : forall A, tp PO @ Empty @r code A ==> Sm A.
Proof.
  intros A; eapply tp_abs; [apply PO_static; reflexivity|].
  apply elim_of_fwd, empty_elim_eval.
Qed.

Lemma nothing_no_value : forall n v, lookup P_rows n = Some (('K1 'KI) '* refuse_elim) \/ n = empty_nm ->
  ~ (infer PO @ v ==> Sm ('label[n])).
Proof.
  intros n v Hn H; destruct (no_junk PO v n H) as [f [F [D [_ [_ [_ [HD HG]]]]]]].
  destruct (app2_inv _ _ _ _ HG) as [g [Hg HC]].
  assert (E : exists e, D = ('K1 'KI) '* e).
  { destruct Hn as [HL| ->].
    - pose proof (eval_deterministic _ _ HD _ (PO_static n _ HL)) as E; inversion E; subst; eauto.
    - pose proof (eval_deterministic _ _ HD _ (PO_static empty_nm D_empty eq_refl)) as E; inversion E; subst.
      unfold D_empty; eauto. }
  destruct E as [e ->].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  assert (H0 : ('K1 'KI) @ F ==> 'KI) by evaluate.
  pose proof (eval_deterministic _ _ HC _ H0); discriminate.
Qed.

Theorem no_value_Empty : forall v, ~ (infer PO @ v ==> Sm Empty).
Proof. intros v; apply nothing_no_value; right; reflexivity. Qed.

Theorem no_value_Atom : forall i v, ~ (infer PO @ v ==> Sm (Atom i)).
Proof.
  intros i v; apply undeclared_no_value; intros D H.
  pose proof (eval_deterministic _ _ H _ (PO_atom_undeclared i)); discriminate.
Qed.
Definition paper_Atom_no_introductions := no_value_Atom.

(** ** Nat elimination in the combined ontology *)
Theorem type_app_Nat : forall B S, tp PO @ S @r Nat ==> Sm B -> tp PO @ Nat @r (B '* S) ==> Sm B.
Proof.
  intros B S H; eapply tp_abs; [apply PO_static; reflexivity|].
  apply elim_of_fwd, nat_eliminator_eval; exact H.
Qed.

Theorem paper_infer_zero : infer PO @ zero ==> Sm Nat.
Proof. apply infer_zero, PO_static; reflexivity. Qed.
Theorem paper_infer_succ : forall m, infer PO @ m ==> Sm Nat -> infer PO @ succ m ==> Sm Nat.
Proof. apply infer_succ, PO_static; reflexivity. Qed.

(** Examples in the combined ontology, by computation. *)
Ltac by_runP := apply (runp_sound 40); vm_done.
Example PO_Nat_elim : infer_expression PO @ (succ zero @ (zero '* succ_fn)) ==> Sm Nat. Proof. by_runP. Qed.
Example PO_pred_eval : succ (succ zero) @ (zero '* 'I) ==> succ zero. Proof. by_runP. Qed.

(** ** Sums in the combined ontology (stage 6) *)
Theorem paper_ontology_supports_sums :
  (forall r, PO @ Fk sum_nm r @r tp PO ==> Sm (D_sum r)) /\
  (forall r, concreteb r = true -> PO @ Fk mksum_nm r @r tp PO ==> Sm (D_mksum r)).
Proof.
  split; [exact PO_sum|]. intros r Hr; unfold PO; apply rows_f_miss; [reflexivity|].
  apply alt_some; [|apply arr_fam_partial]. unfold P_fam.
  apply alt_none; [apply L_fam_miss_fk; discriminate|].
  apply alt_none; [apply query_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply opt_entry_miss, par_of_other; discriminate|].
  apply alt_none; [apply mkq_entry_miss, par_of_other; discriminate|].
  apply sum_fam_mksum, Hr.
Qed.

Theorem paper_inleft_typed : forall A B a, names_concrete A -> names_concrete B -> infer PO @ a ==> Sm A ->
  infer PO @ inleft A B a ==> Sm (Sum A B).
Proof. apply inleft_typed, PO_sum. Qed.
Theorem paper_inright_typed : forall A B b, names_concrete A -> names_concrete B -> infer PO @ b ==> Sm B ->
  infer PO @ inright A B b ==> Sm (Sum A B).
Proof. apply inright_typed, PO_sum. Qed.
Theorem paper_type_app_Sum : forall A B F G C, tp PO @ F @r A ==> Sm C -> tp PO @ G @r B ==> Sm C ->
  tp PO @ Sum A B @r (F '* G) ==> Sm C.
Proof. apply type_app_Sum, PO_sum. Qed.

Example inleft_Nat_Bool : infer PO @ inleft Nat Bool zero ==> Sm (Sum Nat Bool). Proof. by_runP. Qed.
Example mk_sum_inright : infer_expression PO @ (mk_sum Nat Bool @ 'S2['snd, 'K1 tt]) ==> Sm (Sum Nat Bool). Proof. by_runP. Qed.
Example mk_sum_refuses : infer_expression PO @ (mk_sum Nat Bool @ 'S2['snd, 'K1 zero]) ==> Lf. Proof. by_runP. Qed.
Example sum_case : infer_expression PO @ (inright Nat Bool tt @ (('K1 tt) '* 'I)) ==> Sm Bool. Proof. by_runP. Qed.
Example sum_case_eval : inright Nat Bool ff @ (('K1 tt) '* 'I) ==> ff. Proof. by_runP. Qed.
Example sum_case_refused : tp PO @ Sum Nat Bool @r (('K1 Bool) '* ('K1 Nat)) ==> Lf. Proof. by_runP. Qed.




