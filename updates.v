(** * Step 82, stage 2B: updates.

    [Update = label[update_nm]] with [Update # U ==> Sm U].  Its values
    are tags [tagged[c, update_nm]] whose carrier type is admitted by the
    Update guard, which receives type application:

      identity_update        carrier I
      children[r]            carrier wait[ch_body, r]          type wait[ch_body, Update]
      special_type[T,f,d]    carrier wait3[sp_body, code T, f, d]
                             type wait3[sp_body, code T, F, Update]  with F # T ==> Sm T
      fix_update[b]          carrier Z (b o tagger[update_nm])
                             type Z (B o tagger[update_nm])   with B # Update ==> Sm Update

    [sp_body] is the run-time type test: it compares the code
    [code (type_of x)] of the argument's type with [code T]; [type_of] computes
    self-typing types (concrete parts copied, a tag [tagged[_,n]] read as
    [label[n]]).  The declaration is sound by values. *)

From BigStep Require Import tree typing soundness rows identifiers booleans functions.
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal.

(** ** The run-time type *)

Fixpoint type_of (t : Combination) : Combination :=
  match t with
  | Lf => Lf
  | Sm u => Sm (type_of u)
  | Fk u v => match tag_of (Fk u v) with
              | Some (_, n) => 'label[n]
              | None => Fk (type_of u) (type_of v)
              end
  end.

Definition type_of_body : Combination := Eval cbn -[get_tagged] in to_tree
  (star "rec" (star "t"
    (''triage[Val Lf,
              star "u" (Val Lf @@ (Ref "rec" @@ Ref "u")),
              star "u" (star "v"
                (''triage[star "w" (Val Lf @@ (Ref "rec" @@ Ref "u") @@ (Ref "rec" @@ Ref "v")),
                          star "p" (star "w" (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ (op get_r @@ Ref "p")))),
                          Val ('K1 ('K1 ('K1 Lf)))]
                   @@ (op get_tagged @@ (Val Lf @@ Ref "u" @@ Ref "v")) @@ Ref "rec"))]
       @@ Ref "t"))).

Definition type_of_p : Combination := Z type_of_body.

(** ** The carriers *)

Definition update_nm : Combination := Nat.iter 11 Sm Lf.
Definition Update : Combination := 'label[update_nm].

Local Opaque get_tagged get_r get_l isK.

Definition lab (m : Term) : Term := Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ m).
Definition tagger_t (m : Term) : Term := ''S2[Val 'tag_head, ''S2[''K1 (Val 'make_label), ''K1 m]].

(** [ch_body r x]: a tag [tagged[c,n]] becomes [tagged[r @ c, n]] (the
    carrier is rewritten and the name kept); otherwise [r] is applied to
    the immediate children. *)
Definition ch_body : Combination := Eval cbn -[get_tagged get_l get_r] in to_tree
  (star "r" (star "x"
    (''triage[star "x2" (''triage[Val Lf,
                                  star "y" (Val Lf @@ (Ref "r" @@ Ref "y")),
                                  star "y" (star "z" (Val Lf @@ (Ref "r" @@ Ref "y") @@ (Ref "r" @@ Ref "z")))]
                           @@ Ref "x2"),
              star "p" (star "x2" (tagger_t (op get_r @@ Ref "p") @@ (Ref "r" @@ (op get_l @@ Ref "p")))),
              Val ('K1 ('K1 ('K1 Lf)))]
       @@ (op get_tagged @@ Ref "x") @@ Ref "x"))).

Definition sp_body : Combination := Eval cbn -[equal code_p type_of_p] in to_tree
  (star "cT" (star "f" (star "d" (star "x"
    (op equal @@ Ref "cT" @@ (op code_p @@ (op type_of_p @@ Ref "x")) @@ Ref "f" @@ Ref "d" @@ Ref "x"))))).

Definition identity_update : Combination := 'tagged['I, update_nm].
Definition children (r : Combination) : Combination := 'tagged['wait[ch_body, r], update_nm].
Definition special_type (T f d : Combination) : Combination := 'tagged['wait3[sp_body, code T, f, d], update_nm].
Definition fix_update (b : Combination) : Combination := 'tagged[Z (b 'C 'tagger[update_nm]), update_nm].

(** ** The guard *)

(** [or_g g1 g2 @ C ==> K] when [g1] or else [g2] admits [C]. *)
Definition or_prog : Combination := Eval cbn -[isK] in to_tree
  (star "g1" (star "g2" (star "C"
    (op isK @@ (Ref "g1" @@ Ref "C") @@ Val ('K1 'K) @@ Ref "g2" @@ Ref "C")))).
Definition or_g (g1 g2 : Combination) : Combination := 'wait2[or_prog, g1, g2].

Definition get_s : Combination := 'triage[Lf, 'I, 'K1 ('K1 Lf)].
Definition stem_of (t : Combination) := match t with Sm a => a | _ => Lf end.
Lemma get_s_spec : forall t, get_s @ t ==> stem_of t.
Proof. intros [|t|a b]; unfold get_s; evaluate. Qed.
Local Opaque get_s.


(** Paths, as terms: [l], [s], [r] read the left, stem and right parts. *)
Definition pl (t : Term) : Term := op get_l @@ t.
Definition ps (t : Term) : Term := op get_s @@ t.
Definition pr (t : Term) : Term := op get_r @@ t.

(** children: [C = wait[ch_body, Update]] *)
Definition gch_prog : Combination := Eval cbn -[equal] in to_tree
  (star "m" (star "C" (op equal @@ Ref "C" @@ ''wait[Val ch_body, lab (Ref "m")]))).

(** special: [C = wait3[sp_body, cT, F, Update]] with [F # T ==> Sm T], [T = decode cT]. *)
Definition w3 (cT F D : Term) : Term :=
  ''S2[''S2[''S2[''S2[''K1 (Val sp_body), ''K1 cT], ''K1 F], ''K1 D], ''I].
Definition P1 (C : Term) := pr (pr (ps (pl C))).
Definition P2 (C : Term) := pr (pr (ps (pl (ps (pl C))))).
Definition P3 (C : Term) := pr (pr (ps (pl (ps (pl (ps (pl C))))))).

Definition gsp_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s] in to_tree
  (star "m" (star "a" (star "C"
    (op equal @@ Ref "C" @@ w3 (P3 (Ref "C")) (P2 (Ref "C")) (P1 (Ref "C"))
       @@ star "C2" (''onStem1 (star "T"
             (op equal @@ P1 (Ref "C2") @@ lab (Ref "m")
                @@ star "C3" (''onStem1 (star "R" (op equal @@ Ref "R" @@ Ref "T"))
                               @@ (Ref "a" @@ P2 (Ref "C3") @@ Ref "T"))
                @@ Val ('K1 'KI) @@ Ref "C2"))
           @@ (op decode_p @@ P3 (Ref "C2")))
       @@ Val ('K1 'KI) @@ Ref "C")))).

(** fix: [C = Z (B o tagger[update_nm])] with [B # Update ==> Sm Update]. *)
Definition zb (B m : Term) : Term := ''wait[Val self_apply, (B ''C tagger_t m) ''C Val bz].
Definition PB (C : Term) := pr (ps (pl (pr (ps (pl (pr (pr (ps (pl C))))))))).

Definition gfx_prog : Combination := Eval cbn -[equal get_l get_r get_s] in to_tree
  (star "m" (star "a" (star "C"
    (op equal @@ Ref "C" @@ zb (PB (Ref "C")) (Ref "m")
       @@ star "C2" (''onStem1 (star "R" (op equal @@ Ref "R" @@ lab (Ref "m")))
                       @@ (Ref "a" @@ PB (Ref "C2") @@ lab (Ref "m")))
       @@ Val ('K1 'KI) @@ Ref "C")))).

Definition upd_guard (m a : Combination) : Combination :=
  or_g (guard1 'I) (or_g ('wait[gch_prog, m]) (or_g ('wait2[gsp_prog, m, a]) ('wait2[gfx_prog, m, a]))).
Definition upd_elim : Combination := 'K1 ('K1 Lf).
Definition D_upd (m a : Combination) : Combination := upd_guard m a '* upd_elim.

Definition upd_entry : Combination := Eval cbn -[equal update_nm] in to_tree
  (star "n" (star "a"
    (op equal @@ Ref "n" @@ Val update_nm
       @@ (Val Lf @@ (''wait2[Val or_prog, ''wait[Val equal, ''I],
                        ''wait2[Val or_prog, ''wait[Val gch_prog, Ref "n"],
                          ''wait2[Val or_prog, ''wait2[Val gsp_prog, Ref "n", Ref "a"],
                                               ''wait2[Val gfx_prog, Ref "n", Ref "a"]]]]
                      ''* Val upd_elim))
       @@ Val Lf))).

(** The Update constructor, so that programs can build updates at run time. *)
Definition mku_nm : Combination := Nat.iter 13 Sm Lf.
Definition mk_update : Combination := 'tagged['tagger[update_nm], mku_nm].
Definition D_mku (a : Combination) : Combination :=
  guard1 ('tagger[update_nm]) '* ctor_elim (upd_guard update_nm a) update_nm.

Definition mku_entry : Combination := Eval cbn -[equal update_nm mku_nm] in to_tree
  (star "n" (star "a"
    (op equal @@ Ref "n" @@ Val mku_nm
       @@ (Val Lf @@ (''wait[Val equal, tagger_t (Val update_nm)]
                      ''* ''wait2[Val ctor_prog,
                             ''wait2[Val or_prog, ''wait[Val equal, ''I],
                               ''wait2[Val or_prog, ''wait[Val gch_prog, Val update_nm],
                                 ''wait2[Val or_prog, ''wait2[Val gsp_prog, Val update_nm, Ref "a"],
                                                      ''wait2[Val gfx_prog, Val update_nm, Ref "a"]]]],
                             Val update_nm]))
       @@ Val Lf))).

Definition upd_fam : Combination := alt upd_entry (alt mku_entry no_rows).
Definition O_upd : Combination := rows_f O_rows upd_fam.

Ltac by_run := apply (runp_sound 40); vm_done.

Definition NN : Combination := Nat '* Nat.
Definition reset : Combination := special_type NN ('K1 (zero '* zero)) identity_update.

(** ** Tactics *)

Ltac spec_of H L := let E := fresh "E" in pose proof (eval_deterministic _ _ H _ L) as E; clear H;
  first [subst | inversion E; clear E; subst].
Ltac use_specs := repeat match goal with
  | H : get_l @ ?x ==> _ |- _ => spec_of H (get_l_spec x)
  | H : get_r @ ?x ==> _ |- _ => spec_of H (get_r_spec x)
  | H : get_s @ ?x ==> _ |- _ => spec_of H (get_s_spec x)
  end.

Ltac inv_evaln := repeat match goal with
  | H : evaln _ (Sm _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Fk _ _) _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm _) (Fk _ _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm Lf) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Sm _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk Lf _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk (Fk _ _) _)) (Sm _)) _ |- _ => inv_out H
  end.
Ltac add_evals := repeat match goal with H : evaln _ ?e ?v |- _ =>
  lazymatch goal with _ : eval e v |- _ => fail | _ => pose proof (evaln_eval _ _ _ H) end end.
Ltac eq_case2 := match goal with H : equal @ ?x ==> ?e, H' : ?e @ ?y ==> _ |- _ =>
  let He := fresh "He" in pose proof (equal_bt x y) as He; inv_out He; dedup;
  destruct (combination_eq_dec x y); cbn [bt] in * end.
Ltac dec_step := match goal with H : decode_p @ ?x ==> Sm ?t |- _ =>
  let E := fresh "Ed" in
  assert (E : decode x = Some t) by (pose proof (eval_deterministic _ _ H _ (decode_p_eval x)) as E2;
    destruct (decode x); inversion E2; reflexivity); clear H end.
Ltac crunchn := do 5 (try (inv_evaln; add_evals; dedup)).

(** ** The run-time type *)

Lemma type_of_p_eval : forall t, type_of_p @ t ==> type_of t.
Proof.
  induction t as [|u IH|u IHu v IHv]; unfold type_of_p in *; apply Z_unfold; unfold type_of_body.
  - evaluate.
  - cbn [type_of]; evaluate2; repeat first [exact IH|progress evaluate2].
  - pose proof (get_tagged_spec (Fk u v)) as HG; cbn [type_of].
    destruct (tag_of (Fk u v)) as [[f n]|] eqn:E.
    + apply tag_of_some in E; inversion E; subst.
      pose proof (get_r_spec (Fk f n)) as HR; cbn [right_of] in HR.
      evaluate2; repeat first [eassumption|progress evaluate2].
    + evaluate2; repeat first [eassumption|progress evaluate2].
Qed.

Section TypeOf.
Variable O : Combination.

Theorem type_of_agrees : forall v V, infer O @ v ==> Sm V -> type_of v = V.
Proof.
  induction v as [|u IH|u IHu w IHw]; intros V H; apply infer_inv in H; inversion H; subst;
  first [reflexivity
        | cbn; f_equal; apply IH; assumption
        | cbn [type_of]; match goal with E : tag_of _ = None |- _ => rewrite E end;
          f_equal; [apply IHu|apply IHw]; assumption].
Qed.

(** Every label in a value's type has a concrete name. *)
Theorem type_names_concrete : forall v V, infer O @ v ==> Sm V -> names_concrete V.
Proof.
  induction v as [|u IH|u IHu w IHw]; intros V H; apply infer_inv in H; inversion H; subst;
  first [exact I
        | cbn; eapply IH; eassumption
        | cbn; assumption
        | cbn [names_concrete];
          match goal with HL : label_pair ?a ?b = false |- _ => rewrite label_pair_of in HL;
            destruct (label_of (Fk a b)); [discriminate|] end;
          split; [eapply IHu|eapply IHw]; eassumption].
Qed.
End TypeOf.

(** ** The guard pieces *)

Lemma or_g_inv : forall g1 g2 C, or_g g1 g2 @ C ==> 'K -> g1 @ C ==> 'K \/ g2 @ C ==> 'K.
Proof.
  intros g1 g2 C H; apply wait2_eval_inv in H; unfold or_prog in H.
  crunch.
  match goal with H : isK @ ?x ==> _ |- _ => pose proof (isK_spec x) as HK;
    destruct (is_Kb x) eqn:EK; cbn [bt] in HK end; crunch;
  first [apply is_Kb_true in EK; subst; left; assumption | right; assumption].
Qed.

Lemma or_g_l : forall g1 g2 C, g1 @ C ==> 'K -> or_g g1 g2 @ C ==> 'K.
Proof.
  intros g1 g2 C H; apply wait2_eval; unfold or_prog.
  pose proof (isK_spec 'K) as HK; cbn in HK. ev2.
Qed.

Lemma or_g_r : forall g1 g2 C r, g1 @ C ==> r -> is_Kb r = false -> g2 @ C ==> 'K -> or_g g1 g2 @ C ==> 'K.
Proof.
  intros g1 g2 C r H Hr H2; apply wait2_eval; unfold or_prog.
  pose proof (isK_spec r) as HK; rewrite Hr in HK; cbn in HK. ev2.
Qed.

Lemma gch_inv : forall m C, 'wait[gch_prog, m] @ C ==> 'K -> C = 'wait[ch_body, 'label[m]].
Proof.
  intros m C H; apply wait_eval_inv in H; unfold gch_prog in H.
  crunch; eq_case; crunch; reflexivity.
Qed.

Local Opaque decode_p.

Lemma gsp_inv : forall m a C, 'wait2[gsp_prog, m, a] @ C ==> 'K ->
  exists cT F T, C = 'wait3[sp_body, cT, F, 'label[m]] /\ decode cT = Some T /\ a @ F @r T ==> Sm T.
Proof.
  intros m a C H; apply wait2_eval_inv in H; unfold gsp_prog in H.
  crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs.
  dec_step. eq_case2; crunch. eq_case2; crunch.
  all: try discriminate.
  all: use_specs; subst.
  all: match goal with E0 : right_of (right_of (stem_of (left_of ?C))) = 'label[?m], E : ?C = _ |- _ =>
         rewrite E0 in E end.
  all: do 3 eexists; split; [eassumption|].
  all: split; [eassumption|].
  all: eapply eval_appl; [eassumption|eassumption].
Qed.

Lemma gfx_inv : forall m a C, 'wait2[gfx_prog, m, a] @ C ==> 'K ->
  exists B, C = Z (B 'C 'tagger[m]) /\ a @ B @r 'label[m] ==> Sm ('label[m]).
Proof.
  intros m a C H; apply wait2_eval_inv in H; unfold gfx_prog in H.
  crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs.
  eq_case2; crunch.
  all: try discriminate.
  all: use_specs; subst.
  all: eexists; split; [unfold Z; eassumption|eapply eval_appl; eassumption].
Qed.

(** ** The Update declaration *)

Lemma upd_entry_inv : forall n a D, upd_entry @ n @r a ==> Sm D -> n = update_nm /\ D = D_upd n a.
Proof.
  intros n a D H; unfold upd_entry in H.
  crunch; eq_case2; crunch; try discriminate; split; reflexivity.
Qed.

Lemma upd_entry_hit : forall a, upd_entry @ update_nm @r a ==> Sm (D_upd update_nm a).
Proof.
  intros a; unfold upd_entry.
  pose proof (equal_eq update_nm) as He.
  ev2.
Qed.

Lemma upd_entry_partial : forall n, exists p, upd_entry @ n ==> p.
Proof.
  intros n; pose proof (equal_bt n update_nm) as He; inv_out He.
  unfold upd_entry; eexists; ev2.
Qed.

Lemma mku_entry_inv : forall n a D, mku_entry @ n @r a ==> Sm D -> n = mku_nm /\ D = D_mku a.
Proof.
  intros n a D H; unfold mku_entry in H.
  crunch; eq_case2; crunch; try discriminate; split; reflexivity.
Qed.

Lemma mku_entry_hit : forall a, mku_entry @ mku_nm @r a ==> Sm (D_mku a).
Proof. intros a; unfold mku_entry; pose proof (equal_eq mku_nm) as He; ev2. Qed.

Lemma mku_entry_partial : forall n, exists p, mku_entry @ n ==> p.
Proof.
  intros n; pose proof (equal_bt n mku_nm) as He; inv_out He.
  unfold mku_entry; eexists; ev2.
Qed.

Lemma upd_fam_inv : forall n a D, upd_fam @ n @r a ==> Sm D ->
  (n = update_nm /\ D = D_upd update_nm a) \/ (n = mku_nm /\ D = D_mku a).
Proof.
  intros n a D H; unfold upd_fam in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst; destruct (upd_entry_inv _ _ _ H1) as [-> ->]; auto.
  - destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst; destruct (mku_entry_inv _ _ _ H3) as [-> ->]; auto.
    + apply no_rows_inv in H4; discriminate.
Qed.

Lemma upd_fam_partial : forall n, exists p, upd_fam @ n ==> p.
Proof.
  intros n; destruct (upd_entry_partial n) as [p Hp].
  unfold upd_fam, alt; eexists; apply wait2_eval; unfold alt_prog; ev2.
Qed.

Lemma upd_fam_update : forall a, upd_fam @ update_nm @r a ==> Sm (D_upd update_nm a).
Proof.
  intros a; unfold upd_fam; apply alt_some; [apply upd_entry_hit|].
  destruct (mku_entry_partial update_nm) as [p Hp].
  eexists; unfold alt; apply wait2_eval; unfold alt_prog; ev2.
Qed.

Lemma upd_entry_miss : forall n a, n <> update_nm -> upd_entry @ n @r a ==> Lf.
Proof.
  intros n a Hn; unfold upd_entry; pose proof (equal_neq _ _ Hn) as He; ev2.
Qed.

Lemma upd_fam_mku : forall a, upd_fam @ mku_nm @r a ==> Sm (D_mku a).
Proof.
  intros a; unfold upd_fam; apply alt_none; [apply upd_entry_miss; discriminate|].
  apply alt_some; [apply mku_entry_hit|]. eexists; unfold no_rows; evaluate.
Qed.

Lemma O_upd_update : O_upd @ update_nm @r tp O_upd ==> Sm (D_upd update_nm (tp O_upd)).
Proof. unfold O_upd; apply rows_f_miss; [reflexivity|apply upd_fam_update]. Qed.

Lemma O_upd_mku : O_upd @ mku_nm @r tp O_upd ==> Sm (D_mku (tp O_upd)).
Proof. unfold O_upd; apply rows_f_miss; [reflexivity|apply upd_fam_mku]. Qed.

Lemma O_upd_inv : forall n D, O_upd @ n @r tp O_upd ==> Sm D ->
  lookup O_rows n = Some D \/ (n = update_nm /\ D = D_upd update_nm (tp O_upd)) \/
  (n = mku_nm /\ D = D_mku (tp O_upd)).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; apply upd_fam_inv; exact HF.
Qed.

Lemma O_upd_static : forall n D, lookup O_rows n = Some D -> O_upd @ n @r tp O_upd ==> Sm D.
Proof.
  intros n D H; destruct (upd_fam_partial n) as [p Hp]; unfold O_upd; eapply rows_f_hit; eassumption.
Qed.

Lemma upd_elim_inv : forall m a n r U V, elim_of @ D_upd m a @r n @r r @r U ==> Sm V -> V = U.
Proof.
  intros m a n r U V H; apply elim_of_inv in H; unfold upd_elim in H; invert_eval; reflexivity.
Qed.

Theorem Update_app_g : forall O, O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)) ->
  forall U, tp O @ Update @r U ==> Sm U.
Proof.
  intros O HO U; eapply tp_abs; [apply HO|].
  apply elim_of_fwd; unfold upd_elim; evaluate.
Qed.

Theorem Update_app : forall U, tp O_upd @ Update @r U ==> Sm U.
Proof. apply Update_app_g, O_upd_update. Qed.

Lemma upd_guard_inv : forall m a C, guard_of @ D_upd m a @r C ==> 'K ->
  C = 'I \/ C = 'wait[ch_body, 'label[m]] \/
  (exists cT F T, C = 'wait3[sp_body, cT, F, 'label[m]] /\ decode cT = Some T /\ a @ F @r T ==> Sm T) \/
  (exists B, C = Z (B 'C 'tagger[m]) /\ a @ B @r 'label[m] ==> Sm ('label[m])).
Proof.
  intros m a C H; destruct (app2_inv _ _ _ _ H) as [g [Hg HC]].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  unfold upd_guard in HC.
  destruct (or_g_inv _ _ _ HC) as [H1|H1].
  - left; pose proof (eval_deterministic _ _ H1 _ (guard1_spec 'I C)) as E.
    destruct (combination_eq_dec 'I C); [auto|discriminate].
  - destruct (or_g_inv _ _ _ H1) as [H2|H2]; [right; left; apply gch_inv; exact H2|].
    destruct (or_g_inv _ _ _ H2) as [H3|H3]; [right; right; left; eapply gsp_inv; exact H3|].
    right; right; right; eapply gfx_inv; exact H3.
Qed.

(** ** Height-aware inversion of the carriers *)

Ltac finl := match goal with
 | |- _ \/ _ => first [left; finl | right; finl]
 | |- exists _, _ => eexists; finl
 | |- _ /\ _ => split; finl
 | |- _ => solve [reflexivity | eassumption | lia | auto ]
end.

Local Opaque type_of_p code_p.

Lemma get_l_fk : forall a b, get_l @ Fk a b ==> a. Proof. intros; apply get_l_spec. Qed.
Lemma get_r_fk : forall a b, get_r @ Fk a b ==> b. Proof. intros; apply get_r_spec. Qed.

Lemma ch_inv_h : forall k r v w, evaln k ('wait[ch_body, r] @ v) w ->
  (exists c n c' j, v = 'tagged[c,n] /\ evaln j (r @ c) c' /\ w = 'tagged[c',n] /\ j < k) \/
  (v = Lf /\ w = Lf) \/
  (exists y y' j, v = Sm y /\ evaln j (r @ y) y' /\ w = Sm y' /\ j < k) \/
  (exists y z y' z' j1 j2, v = Fk y z /\ tag_of v = None /\ evaln j1 (r @ y) y' /\ evaln j2 (r @ z) z' /\
     w = Fk y' z' /\ j1 < k /\ j2 < k).
Proof.
  intros k r v w H.
  pose proof (get_tagged_spec v) as HG.
  destruct (tag_of v) as [[f n]|] eqn:E.
  - apply tag_of_some in E; subst v. left.
    pose proof (get_l_fk f n) as Hl; pose proof (get_r_fk f n) as Hr.
    unfold ch_body in H; crunchn; finl.
  - right. destruct v as [|y|y z].
    + left; split; [reflexivity|]. unfold ch_body in H; crunchn; reflexivity.
    + right; left. unfold ch_body in H; crunchn; finl.
    + right; right. unfold ch_body in H; crunchn; finl.
Qed.

Lemma sp_inv_h : forall k cTv f d v w, evaln k ('wait3[sp_body, cTv, f, d] @ v) w ->
  exists j, ((cTv = code (type_of v) /\ evaln j (f @ v) w) \/ (cTv <> code (type_of v) /\ evaln j (d @ v) w)) /\ j < k.
Proof.
  intros k cTv f d v w H.
  pose proof (type_of_p_eval v) as HT; pose proof (code_p_eval (type_of v)) as HI.
  pose proof (equal_bt cTv (code (type_of v))) as He; inv_out He.
  unfold sp_body in H.
  destruct (combination_eq_dec cTv (code (type_of v))); cbn [bt] in *; crunchn; finl.
Qed.

Lemma fix_inv_h : forall k b m v w, evaln k (Z (b 'C 'tagger[m]) @ v) w ->
  exists j1 j2 g, evaln j1 (b @ 'tagged[Z (b 'C 'tagger[m]), m]) g /\ evaln j2 (g @ v) w /\ j1 < k /\ j2 < k.
Proof.
  intros k b m v w H; unfold Z, self_apply, wait1 in *; crunchn; finl.
Qed.

(** ** Forcing values of structured types *)

Ltac force O := repeat match goal with
  | H : infer O @ ?v ==> Sm Lf |- _ => is_var v; apply (type_Lf_inv O) in H; subst v
  | H : infer O @ ?v ==> Sm (Sm ?A) |- _ => is_var v;
      let u := fresh "u" in let Hu := fresh "Hu" in
      destruct (type_Sm_inv O v A H) as [u [-> Hu]]; clear H
  | H : infer O @ ?v ==> Sm (Fk ?A ?B) |- _ => is_var v;
      let x := fresh "x" in let y := fresh "y" in let H1 := fresh "Hx" in let H2 := fresh "Hy" in
      let m := fresh "m" in let E := fresh "E" in
      destruct (type_Fk_inv O v A B H) as [[m E]|[x [y [-> [_ [H1 [H2 _]]]]]]]; [discriminate E|clear H]
  | H : infer O @ ?v ==> Sm ?C |- _ => is_var v; apply (concrete_type_forces O) in H;
      [subst v|vm_compute; reflexivity]
  end.

(** ** Soundness of the Update declaration, by values *)

Section GenericUpdate.
Variable O : Combination.
Hypothesis HO : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).

Theorem upd_decl_sound_g : decl_sound O update_nm (D_upd update_nm (tp O)).
Proof using HO.
  intros k C U V c v w HC HE Hc Hv Hk Hw.
  apply upd_elim_inv in HE; subst V.
  destruct (upd_guard_inv _ _ _ HC) as [->|[->|[[cT [F [T [-> [HT HF]]]]]|[B [-> HB]]]]].
  - (* identity *)
    apply (concrete_type_forces O) in Hc; [subst c|reflexivity].
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (I_eval v)) as ->; exact Hv.
  - (* children *)
    force O.
    destruct (ch_inv_h _ _ _ _ Hw) as [H0|[H0|[H0|H0]]];
      repeat match goal with H : exists _, _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end; subst.
    + apply infer_inv in Hv; inversion Hv; subst;
        try (match goal with H : tag_of _ = None |- _ => cbn in H; discriminate H end).
      match goal with H1 : evaln _ (?r @ ?c) ?c', Hr : infer O @ ?r ==> Sm _,
                      Hf : infer O @ ?c ==> Sm ?F0, HG : guard_of @ _ @r ?F0 ==> 'K |- _ =>
        assert (Hc' : infer O @ c' ==> Sm F0) by (eapply Hk; [|exact H1|exact Hr|exact Hf|exact ((Update_app_g O HO) F0)]; lia);
        eapply infer_tag; [eassumption|exact Hc'|eassumption|exact HG] end.
    + exact Hv.
    + apply infer_inv in Hv; inversion Hv as [|u0 Y HY| |]; subst.
      apply infer_stem.
      eapply Hk; [|eassumption|eassumption|exact HY|exact ((Update_app_g O HO) Y)]; lia.
    + apply infer_inv in Hv; inversion Hv as [| |f n F D _ _ _ _|a b Y Z Hn HY HZ HL]; subst;
        [match goal with H : tag_of _ = None |- _ => discriminate H end|].
      match goal with H1 : evaln _ (?r @ ?a) ?y', H2 : evaln _ (?r @ ?b) ?z',
                      HA : infer O @ ?a ==> Sm ?Y, HB : infer O @ ?b ==> Sm ?Z,
                      HL : label_pair ?Y ?Z = false |- _ =>
        assert (Hy' : infer O @ y' ==> Sm Y) by (eapply Hk; [|exact H1|eassumption|exact HA|exact ((Update_app_g O HO) Y)]; lia);
        assert (Hz' : infer O @ z' ==> Sm Z) by (eapply Hk; [|exact H2|eassumption|exact HB|exact ((Update_app_g O HO) Z)]; lia);
        apply infer_fork; [eapply not_tag_of_typed; exact Hz'|exact Hy'|exact Hz'|exact HL]
      end.
  - (* special *)
    force O.
    match goal with Hw : evaln k ('wait3[sp_body, ?cv, ?f, ?d] @ v) w,
                    Hcv : infer O @ ?cv ==> Sm cT, Hf : infer O @ ?f ==> Sm F,
                    Hd : infer O @ ?d ==> Sm _ |- _ =>
      destruct (sp_inv_h _ _ _ _ _ _ Hw) as [j [[[E Hj]|[E Hj]] Hjk]];
      [ rewrite (type_of_agrees O v U Hv) in E; subst;
        pose proof (concrete_is_self_typed O _ (code_concrete U (type_names_concrete O v U Hv))) as Hs;
        pose proof (eval_deterministic _ _ Hs _ Hcv) as E1; inversion E1; subst;
        rewrite decode_code in HT; inversion HT; subst;
        eapply Hk; [|exact Hj|exact Hf|exact Hv|exact HF]; lia
      | eapply Hk; [|exact Hj|exact Hd|exact Hv|exact ((Update_app_g O HO) U)]; lia ]
    end.
  - (* recursion *)
    pose proof Hc as Hc0.
    unfold Z in Hc; force O.
    match goal with Hb : infer O @ ?b ==> Sm B |- _ =>
      change ('wait[self_apply, (b 'C 'tagger[update_nm]) 'C bz]) with (Z (b 'C 'tagger[update_nm])) in *;
      destruct (fix_inv_h _ _ _ _ _ Hw) as [j1 [j2 [g [Hj1 [Hj2 [Hk1 Hk2]]]]]];
      assert (Hu : infer O @ fix_update b ==> Sm Update)
        by (eapply infer_tag; [reflexivity|exact Hc0|exact HO|exact HC]);
      assert (Hg : infer O @ g ==> Sm Update)
        by (eapply Hk; [|exact Hj1|exact Hb|exact Hu|exact HB]; lia);
      eapply Hk; [|exact Hj2|exact Hg|exact Hv|exact ((Update_app_g O HO) U)]; lia
    end.
Qed.

Theorem mku_decl_sound_g : decl_sound O mku_nm (D_mku (tp O)).
Proof using HO. eapply ctor_decl_sound; [reflexivity|exact HO|apply guard_of_pair]. Qed.
End GenericUpdate.

Theorem upd_decl_sound : decl_sound O_upd update_nm (D_upd update_nm (tp O_upd)).
Proof. apply upd_decl_sound_g, O_upd_update. Qed.

Theorem O_upd_sound : ontology_sound O_upd.
Proof.
  intros n D H.
  destruct (O_upd_inv n D H) as [HL|[[-> ->]|[-> ->]]];
    [|apply upd_decl_sound|apply mku_decl_sound_g, O_upd_update].
  unfold O_rows in HL; cbn [lookup] in HL.
  repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
  - apply bool_decl_sound.
  - apply nat_decl_sound.
  - eapply ctor_decl_sound; [reflexivity|apply O_upd_static; reflexivity|apply guard_of_pair].
Qed.

Corollary O_upd_typing_sound : typing_sound O_upd.
Proof. apply evaluation_preserves_typing, O_upd_sound. Qed.



(** ** The typing of special_type *)

Lemma get_s_sm : forall a, get_s @ Sm a ==> a. Proof. intros; apply get_s_spec. Qed.

Ltac ev_many := split2; evaluate2; repeat first [eassumption | apply get_l_fk | apply get_r_fk | apply get_s_sm
  | apply equal_eval | apply equal1_eq | apply decode_p_code | progress evaluate2].

Lemma gsp_hit : forall m a T F, a @ F @r T ==> Sm T ->
  'wait2[gsp_prog, m, a] @ 'wait3[sp_body, code T, F, 'label[m]] ==> 'K.
Proof. intros m a T F H; apply wait2_eval; unfold gsp_prog; ev_many. Qed.

Lemma guard1_miss : forall c C, c <> C -> guard1 c @ C ==> 'KI.
Proof.
  intros c C H; pose proof (guard1_spec c C) as E; destruct (combination_eq_dec c C); [contradiction|exact E].
Qed.

Lemma gch_miss : forall m C, C <> 'wait[ch_body, 'label[m]] -> 'wait[gch_prog, m] @ C ==> 'KI.
Proof.
  intros m C H; apply wait_eval; unfold gch_prog.
  pose proof (equal_neq _ _ H) as He; ev2.
Qed.

Ltac build O := repeat first
  [ eassumption
  | apply infer_leaf
  | apply infer_stem
  | (apply concrete_is_self_typed; vm_compute; reflexivity)
  | (apply infer_fork; [reflexivity| | |reflexivity]) ].

Theorem special_type_typed_g : forall O, O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)) ->
  forall T f d F, names_concrete T ->
  infer O @ f ==> Sm F -> tp O @ F @r T ==> Sm T -> infer O @ d ==> Sm Update ->
  infer O @ special_type T f d ==> Sm Update.
Proof.
  intros O HO T f d F HT Hf HF Hd.
  pose proof (code_self_typed O T HT) as HiT.
  assert (Hc : infer O @ 'wait3[sp_body, code T, f, d] ==> Sm ('wait3[sp_body, code T, F, 'label[update_nm]]))
    by (unfold Update in Hd; build O).
  eapply infer_tag; [reflexivity|exact Hc|exact HO|].
  - eapply app2; [apply guard_of_pair|]. unfold upd_guard.
    eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
    eapply or_g_r; [apply gch_miss; discriminate|reflexivity|].
    apply or_g_l. apply gsp_hit; exact HF.
Qed.


Theorem special_type_typed : forall T f d F, names_concrete T ->
  infer O_upd @ f ==> Sm F -> tp O_upd @ F @r T ==> Sm T -> infer O_upd @ d ==> Sm Update ->
  infer O_upd @ special_type T f d ==> Sm Update.
Proof. apply special_type_typed_g, O_upd_update. Qed.

(** The run-time behaviour of special_type. *)
Lemma sp_fwd : forall cT f d x v, (if combination_eq_dec cT (code (type_of x)) then f else d) @ x ==> v ->
  'wait3[sp_body, cT, f, d] @ x ==> v.
Proof.
  intros cT f d x v H; apply wait3_eval; unfold sp_body.
  pose proof (type_of_p_eval x) as HT; pose proof (code_p_eval (type_of x)) as HI.
  pose proof (equal_bt cT (code (type_of x))) as He.
  destruct (combination_eq_dec cT (code (type_of x))); cbn [bt] in He; ev2.
Qed.

Theorem special_type_hit : forall T f d x v, type_of x = T -> f @ x ==> v -> special_type T f d @ x ==> v.
Proof.
  intros T f d x v E H; apply tagged_eval, sp_fwd.
  destruct (combination_eq_dec (code T) (code (type_of x))) as [_|n]; [exact H|rewrite E in n; contradiction].
Qed.

Theorem special_type_miss : forall T f d x v, type_of x <> T -> d @ x ==> v -> special_type T f d @ x ==> v.
Proof.
  intros T f d x v E H; apply tagged_eval, sp_fwd.
  destruct (combination_eq_dec (code T) (code (type_of x))) as [e|_]; [|exact H].
  apply code_inj in e; subst; contradiction.
Qed.

(** ** Examples *)

Example identity_update_typed : infer O_upd @ identity_update ==> Sm Update. Proof. by_run. Qed.
Example children_typed : infer O_upd @ children identity_update ==> Sm Update. Proof. by_run. Qed.
Example reset_typed : infer O_upd @ reset ==> Sm Update. Proof. by_run. Qed.
Example reset_app_typed : infer_expression O_upd @ (reset @ (zero '* succ zero)) ==> Sm NN. Proof. by_run. Qed.
Example reset_fires : reset @ (zero '* succ zero) ==> (zero '* zero). Proof. by_run. Qed.
Example reset_skips_Nat : reset @ zero ==> zero. Proof. by_run. Qed.
Example reset_skips_Bool_pair : reset @ (tt '* ff) ==> (tt '* ff). Proof. by_run. Qed.
Example reset_skips_forged : reset @ ('K '* 'K1 zero) ==> ('K '* 'K1 zero). Proof. by_run. Qed.
(** The types as data, [Nat * Nat], contain bare labels and so have no type;
    [type_of] reads them as themselves, and the test fires.  This is
    harmless: soundness speaks only of typed arguments. *)
Example reset_on_types : reset @ (Nat '* Nat) ==> (zero '* zero). Proof. by_run. Qed.
Example types_as_data_untyped : forall T, ~ (infer O_upd @ (Nat '* Nat) ==> Sm T).
Proof.
  intros T H. apply infer_inv in H; inversion H as [| | |u1 u2 U1 U2 _ H1 H2 _]; subst.
  apply infer_inv in H2; inversion H2 as [| | |a b A B _ Ha Hb _]; subst.
  exact (bare_label_untyped O_upd nat_nm B Hb).
Qed.
Example children_reset : children reset @ Sm (zero '* succ zero) ==> Sm (zero '* zero). Proof. by_run. Qed.
Example wrong_f_untyped : infer O_upd @ special_type NN ('K1 zero) identity_update ==> Lf. Proof. by_run. Qed.
Example wrong_d_untyped : infer O_upd @ special_type NN ('K1 (zero '* zero)) 'I ==> Lf. Proof. by_run. Qed.
Example fix_typed : infer O_upd @ fix_update ('K1 identity_update) ==> Sm Update. Proof. by_run. Qed.
Example fix_eval : fix_update ('K1 identity_update) @ zero ==> zero. Proof. by_run. Qed.
Example Update_Nat : tp O_upd @ Update @r Nat ==> Sm Nat. Proof. apply Update_app. Qed.
Example upd_tp_concrete : concreteb (tp O_upd) = true. Proof. vm_compute; reflexivity. Qed.
Example upd_O_concrete : concreteb O_upd = true. Proof. vm_compute; reflexivity. Qed.
