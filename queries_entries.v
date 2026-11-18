(** * Step 82: queries, part 2 of 3 (split for build time): the family entries and the query ontology [O_q]. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries_core.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Opaque qK_prog qS_prog qsp_prog qe_prog gdq_prog or_prog gtq_prog.

Lemma query_entry_inv : forall n a D, query_entry @ n @r a ==> Sm D ->
  exists r, n = query_tag r /\ concreteb r = true /\ D = D_query r a.
Proof.
  intros n a D H; unfold query_entry in H.
  pose proof (get_par_spec query_nm n) as Hp.
  destruct (par_of query_nm n) as [r|] eqn:E; cbn [opt] in Hp; [|crunch].
  pose proof (is_concrete_bt r) as Hc; destruct (concreteb r) eqn:Ec; cbn [bt] in Hc; crunch;
    eexists; split; [apply par_of_some; eassumption|split; [eassumption|reflexivity]].
Qed.

Lemma query_entry_hit : forall r a, concreteb r = true -> query_entry @ query_tag r @r a ==> Sm (D_query r a).
Proof.
  intros r a Hr; unfold query_entry.
  pose proof (get_par_spec query_nm (query_tag r)) as Hp; cbn [par_of query_tag] in Hp.
  pose proof (is_concrete_bt r) as Hc; rewrite Hr in Hc; cbn [bt] in Hc.
  destruct (combination_eq_dec query_nm query_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma mkq_entry_inv : forall n a D, mkq_entry @ n @r a ==> Sm D ->
  exists r, n = Fk mkq_nm r /\ concreteb r = true /\ D = D_mkq r a.
Proof.
  intros n a D H; unfold mkq_entry in H.
  pose proof (get_par_spec mkq_nm n) as Hp.
  destruct (par_of mkq_nm n) as [r|] eqn:E; cbn [opt] in Hp; [|crunch].
  pose proof (is_concrete_bt r) as Hc; destruct (concreteb r) eqn:Ec; cbn [bt] in Hc; crunch;
    eexists; split; [apply par_of_some; eassumption|split; [eassumption|reflexivity]].
Qed.

Lemma mkq_entry_hit : forall r a, concreteb r = true -> mkq_entry @ Fk mkq_nm r @r a ==> Sm (D_mkq r a).
Proof.
  intros r a Hr; unfold mkq_entry.
  pose proof (get_par_spec mkq_nm (Fk mkq_nm r)) as Hp; cbn [par_of] in Hp.
  pose proof (is_concrete_bt r) as Hc; rewrite Hr in Hc; cbn [bt] in Hc.
  destruct (combination_eq_dec mkq_nm mkq_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma mkq_entry_partial : forall n, exists p, mkq_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec mkq_nm n) as Hp.
  destruct (par_of mkq_nm n); cbn [opt] in Hp; unfold mkq_entry; eexists; ev2.
Qed.

Lemma mkq_entry_miss : forall n a, par_of mkq_nm n = None -> mkq_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold mkq_entry; pose proof (get_par_spec mkq_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

(** ** The query ontology *)

Lemma Q_fam_inv : forall n a D, Q_fam @ n @r a ==> Sm D ->
  L_fam @ n @r a ==> Sm D \/ (exists r, n = query_tag r /\ concreteb r = true /\ D = D_query r a) \/
  (exists r, n = Fk mkq_nm r /\ concreteb r = true /\ D = D_mkq r a).
Proof.
  intros n a D H; unfold Q_fam in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst; left; exact H1.
  - destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst; right; left; eapply query_entry_inv; exact H3.
    + destruct (alt_inv _ _ _ _ _ H4) as [[D' [H5 E]]|[[H5 H6]|[x [y [_ E]]]]]; [|..|discriminate].
      * inversion E; subst; right; right; eapply mkq_entry_inv; exact H5.
      * apply no_rows_inv in H6; discriminate.
Qed.

Lemma Q_fam_partial : forall n, exists p, Q_fam @ n ==> p.
Proof. intros n; apply alt_partial, L_fam_partial. Qed.

Lemma O_q_static : forall n D, lookup G_rows n = Some D -> O_q @ n @r tp O_q ==> Sm D.
Proof. intros n D H; destruct (Q_fam_partial n) as [p Hp]; unfold O_q; eapply rows_f_hit; eassumption. Qed.

Lemma L_fam_hit_to_Q : forall n a D, L_fam @ n @r a ==> Sm D -> Q_fam @ n @r a ==> Sm D.
Proof.
  intros n a D H; unfold Q_fam; apply alt_some; [exact H|].
  apply alt_partial. pose proof (get_par_spec query_nm n) as Hp.
  destruct (par_of query_nm n); cbn [opt] in Hp; unfold query_entry; eexists; ev2.
Qed.

Lemma O_q_update : O_q @ update_nm @r tp O_q ==> Sm (D_upd update_nm (tp O_q)).
Proof.
  unfold O_q; apply rows_f_miss; [reflexivity|]. apply L_fam_hit_to_Q.
  unfold L_fam; apply alt_some; [apply upd_fam_update|]. apply alt_partial, list_entry_partial.
Qed.

Lemma O_q_list : forall r, O_q @ list_tag r @r tp O_q ==> Sm (D_list r).
Proof.
  intros r; unfold O_q; apply rows_f_miss; [reflexivity|]. apply L_fam_hit_to_Q. unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_some; [apply list_entry_hit|]. apply alt_partial.
  pose proof (get_par_spec mkcons_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm list_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  Local Transparent get_par is_concrete. unfold mkcons_entry; eexists; ev2.
Qed.
Local Opaque get_par is_concrete.

Lemma L_fam_miss_query : forall r a, L_fam @ query_tag r @r a ==> Lf.
Proof.
  intros r a; unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_none; [apply list_entry_miss; reflexivity|].
  apply alt_none; [|unfold no_rows; evaluate].
  Local Transparent get_par is_concrete.
  unfold mkcons_entry; pose proof (get_par_spec mkcons_nm (query_tag r)) as Hp; cbn [par_of query_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm query_nm) as [E|]; [discriminate|]; cbn [opt] in Hp. ev2.
Qed.
Local Opaque get_par is_concrete.

Lemma O_q_query : forall r, concreteb r = true -> O_q @ query_tag r @r tp O_q ==> Sm (D_query r (tp O_q)).
Proof.
  intros r Hr; unfold O_q; apply rows_f_miss; [reflexivity|]. unfold Q_fam.
  apply alt_none; [apply L_fam_miss_query|]. apply alt_some; [apply query_entry_hit; exact Hr|].
  apply alt_partial, mkq_entry_partial.
Qed.

Lemma Query_app_r : forall r B U, concreteb r = true -> decode r = Some B ->
  tp O_q @ 'label[query_tag r] @r U ==> Sm B.
Proof. intros r B U Hr H; eapply tp_abs; [apply O_q_query; exact Hr|apply elim_of_fwd, qe_fwd; exact H]. Qed.

Theorem Query_app : forall B U, names_concrete B -> tp O_q @ Query B @r U ==> Sm B.
Proof. intros B U HB; apply Query_app_r; [apply code_concrete, HB|apply decode_code]. Qed.

Lemma Fk_name_concrete : forall O g h c, infer O @ g ==> Sm ('label[Fk h c]) -> concreteb c = true.
Proof.
  intros O g h c H; destruct (no_junk O g _ H) as [f [F [D [_ [Hn _]]]]].
  cbn in Hn; apply andb_prop in Hn as [_ Hc]; exact Hc.
Qed.

