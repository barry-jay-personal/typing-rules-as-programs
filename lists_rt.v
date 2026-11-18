(** * Step 82, stage 4, part 1: generic constructors with run-time codes.

    Codes are concrete, so the type of a code [c] is [c] itself.

      gen_cons = tagged[gcons_carrier, gen_cons_nm]
      gcons_carrier @ (c * (x * xs)) = tagged[S2[snd, K1 (x*xs)], list_tag[c]]
      declaration at gen_cons_nm:
        guard  admits exactly gcons_carrier (its own type)
        elim   gen_cons # (C * (X * L)) = Sm (List A)
               when C is concrete, A = decode C, X = A and L = List A

      gen_nil = tagged[gnil_carrier, gen_nil_nm]
      gnil_carrier @ c = tagged[fst, list_tag[c]]
      elim   gen_nil # C = Sm (List A)   when C is concrete and A = decode C

    The list programs then take their codes at run time. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition gen_cons_nm : Combination := Nat.iter 20 Sm Lf.
Definition gen_nil_nm : Combination := Nat.iter 21 Sm Lf.

Definition LT (c : Term) : Term := Val Lf @@ Val list_nm @@ c.

(** The carriers build tags at run time with tagger. *)
Definition gcons_carrier : Combination := Eval cbn -[list_nm] in to_tree
  (star "q" (tagger_t (LT (Val 'fst @@ Ref "q"))
               @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ (Val 'snd @@ Ref "q"))))).
Definition gnil_carrier : Combination := Eval cbn -[list_nm] in to_tree
  (star "c" (tagger_t (LT (Ref "c")) @@ Val 'fst)).

Definition gen_cons : Combination := 'tagged[gcons_carrier, gen_cons_nm].
Definition gen_nil : Combination := 'tagged[gnil_carrier, gen_nil_nm].

(** elim at gcons: [U = C * (X * L)], checked by rebuilding [C * (A * List A)]. *)
Definition gce_prog : Combination := Eval cbn -[equal decode_p is_concrete get_l get_r get_s list_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ PN (Ref "U")
       @@ star "U2" (''onStem1 (star "A"
             (op equal @@ Ref "U2" @@ (PN (Ref "U2") ''* (Ref "A" ''* LL (PN (Ref "U2"))))
                @@ (Val Lf @@ LL (PN (Ref "U2"))) @@ Val Lf))
           @@ (op decode_p @@ PN (Ref "U2")))
       @@ Val ('K1 Lf) @@ Ref "U")))).

(** elim at gnil: [U = C] *)
Definition gne_prog : Combination := Eval cbn -[decode_p is_concrete list_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ Ref "U"
       @@ star "U2" (''onStem1 (star "A" (Val Lf @@ LL (Ref "U2"))) @@ (op decode_p @@ Ref "U2"))
       @@ Val ('K1 Lf) @@ Ref "U")))).

Definition D_gcons : Combination := guard1 gcons_carrier '* gce_prog.
Definition D_gnil : Combination := guard1 gnil_carrier '* gne_prog.

Definition G_rows : list (Combination * Combination) :=
  (D_rows ++ [(gen_cons_nm, D_gcons); (gen_nil_nm, D_gnil)])%list.
Definition O_gen : Combination := rows_f G_rows L_fam.

(** ** Codes built at run time *)

Definition list_code_t (c : Term) : Term := Val Lf @@ (Val Lf @@ Val Lf @@ Val Lf) @@ LT c.
Definition fk_t (a b : Term) : Term := Val Lf @@ a @@ b.
Definition sm_t (a : Term) : Term := Val Lf @@ a.
Definition pair_code_t (cX cY : Term) : Term :=
  fk_t (sm_t (sm_t (fk_t (sm_t (sm_t (Val (code 'I)))) (fk_t (Val (Sm Lf)) cX)))) (fk_t (Val (Sm Lf)) cY).

(** The iteration at a run-time state code [cT] and step [g]:
    [litR @ cT @ g = fix_update[bR cT g]], built through [mk_update]. *)
Definition litR : Combination := Eval cbn -[mk_update sp_body identity_update self_apply bz] in to_tree
  (star "cT" (star "g"
    (op mk_update @@ ''wait[Val self_apply,
       (star "r" (op mk_update @@ w3 (Ref "cT") (step_t (Ref "g") (Ref "r")) (Val identity_update))
         ''C tagger_t (Val update_nm)) ''C Val bz]))).

Definition fst_t (x : Term) : Term := Val 'fst @@ x.
Definition snd_t (x : Term) : Term := Val 'snd @@ x.

(** [consR @ c @ p = gen_cons @ (c * p)]. *)
Definition consR_t (c : Term) : Term := star "p" (op gen_cons @@ (c ''* Ref "p")).

(** [rev_appendR @ (c * (xs * ys))]. *)
Definition rev_appendR : Combination := Eval cbn -[litR gen_cons] in to_tree
  (star "q" (snd_t ((Val litR @@ pair_code_t (list_code_t (fst_t (Ref "q"))) (list_code_t (fst_t (Ref "q")))
                      @@ consR_t (fst_t (Ref "q"))) @@ snd_t (Ref "q")))).
(** [reverseR @ (c * xs)]. *)
Definition reverseR : Combination := Eval cbn -[rev_appendR gen_nil] in to_tree
  (star "q" (Val rev_appendR @@ (fst_t (Ref "q") ''* (snd_t (Ref "q") ''* (op gen_nil @@ fst_t (Ref "q")))))).
(** [appendR @ (c * (xs * ys))]. *)
Definition appendR : Combination := Eval cbn -[rev_appendR reverseR] in to_tree
  (star "q" (Val rev_appendR @@ (fst_t (Ref "q") ''*
     ((Val reverseR @@ (fst_t (Ref "q") ''* fst_t (snd_t (Ref "q")))) ''* snd_t (snd_t (Ref "q")))))).
(** [lengthR @ (c * xs)]. *)
Definition lengthR : Combination := Eval cbn -[litR succ_step zero] in to_tree
  (star "q" (snd_t ((Val litR @@ pair_code_t (list_code_t (fst_t (Ref "q"))) (Val (code Nat)) @@ Val succ_step)
                      @@ (snd_t (Ref "q") ''* Val zero)))).
(** [filterR @ (c * (p * xs))]. *)
Definition filterR : Combination := Eval cbn -[litR reverseR gen_cons gen_nil] in to_tree
  (star "q" (Val reverseR @@ (fst_t (Ref "q") ''* snd_t
     ((Val litR @@ pair_code_t (list_code_t (fst_t (Ref "q"))) (list_code_t (fst_t (Ref "q")))
         @@ star "s" ((fst_t (snd_t (Ref "q")) @@ fst_t (Ref "s"))
                       @@ ((consR_t (fst_t (Ref "q")) @@ Ref "s") ''* snd_t (Ref "s"))))
      @@ (snd_t (snd_t (Ref "q")) ''* (op gen_nil @@ fst_t (Ref "q"))))))).
(** [mapR @ (ca * (cb * (f * xs)))]. *)
Definition mapR : Combination := Eval cbn -[litR reverseR gen_cons gen_nil] in to_tree
  (star "q" (Val reverseR @@ (fst_t (snd_t (Ref "q")) ''* snd_t
     ((Val litR @@ pair_code_t (list_code_t (fst_t (Ref "q"))) (list_code_t (fst_t (snd_t (Ref "q"))))
         @@ star "s" (consR_t (fst_t (snd_t (Ref "q")))
                       @@ ((fst_t (snd_t (snd_t (Ref "q"))) @@ fst_t (Ref "s")) ''* snd_t (Ref "s"))))
      @@ (snd_t (snd_t (snd_t (Ref "q"))) ''* (op gen_nil @@ fst_t (snd_t (Ref "q")))))))).
(** [foldrightR @ (ca * (cc * (g * (xs * z))))]. *)
Definition foldrightR : Combination := Eval cbn -[litR reverseR] in to_tree
  (star "q" (snd_t ((Val litR @@ pair_code_t (list_code_t (fst_t (Ref "q"))) (fst_t (snd_t (Ref "q")))
                       @@ fst_t (snd_t (snd_t (Ref "q"))))
     @@ ((Val reverseR @@ (fst_t (Ref "q") ''* fst_t (snd_t (snd_t (snd_t (Ref "q"))))))
         ''* snd_t (snd_t (snd_t (snd_t (Ref "q")))))))).

(** ** The generic constructors are sound by values *)

Local Opaque gce_prog gne_prog lg_prog le_prog.

Definition pn (U : Combination) := right_of (right_of (stem_of (left_of U))).

Lemma gce_inv : forall n a U V, gce_prog @ n @r a @r U ==> Sm V ->
  exists C0 A, U = C0 '* (A '* 'label[Fk list_nm C0]) /\ concreteb C0 = true /\ decode C0 = Some A /\
    V = 'label[Fk list_nm C0].
Proof.
  intros n a U V H. Local Transparent gce_prog. unfold gce_prog in H. Local Opaque gce_prog.
  pose proof (get_l_spec U) as H1; pose proof (get_s_spec (left_of U)) as H2;
  pose proof (get_r_spec (stem_of (left_of U))) as H3; pose proof (get_r_spec (right_of (stem_of (left_of U)))) as H4.
  pose proof (is_concrete_bt (pn U)) as Hc. pose proof (decode_p_eval (pn U)) as Hd.
  unfold pn in Hc, Hd.
  destruct (concreteb (right_of (right_of (stem_of (left_of U))))) eqn:Ec; cbn [bt] in Hc; [|crunch].
  destruct (decode (right_of (right_of (stem_of (left_of U))))) as [A|] eqn:Ed; cbn [opt] in Hd; [|crunch].
  crunch; eq_case2; crunch; try discriminate.
  all: eexists; eexists; split; [eassumption|split; [eassumption|split; [eassumption|reflexivity]]].
Qed.

Lemma gne_inv : forall n a U V, gne_prog @ n @r a @r U ==> Sm V ->
  concreteb U = true /\ (exists A, decode U = Some A) /\ V = 'label[Fk list_nm U].
Proof.
  intros n a U V H. Local Transparent gne_prog. unfold gne_prog in H. Local Opaque gne_prog.
  pose proof (is_concrete_bt U) as Hc; pose proof (decode_p_eval U) as Hd.
  destruct (concreteb U) eqn:Ec; cbn [bt] in Hc; [|crunch].
  destruct (decode U) as [A|] eqn:Ed; cbn [opt] in Hd; crunch.
  all: split; [eassumption|split; [eauto|reflexivity]].
Qed.

Lemma gcons_eval : forall c x xs, gcons_carrier @ (c '* (x '* xs)) ==> 'tagged['S2['snd, 'K1 (x '* xs)], Fk list_nm c].
Proof. intros; unfold gcons_carrier; evaluate. Qed.

Lemma gnil_eval : forall c, gnil_carrier @ c ==> 'tagged['fst, Fk list_nm c].
Proof. intros; unfold gnil_carrier; evaluate. Qed.

Section Gen.
Variable O : Combination.
Hypothesis HL : forall r, O @ list_tag r @r tp O ==> Sm (D_list r).

Theorem gcons_decl_sound : decl_sound O gen_cons_nm D_gcons.
Proof using HL.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec gcons_carrier C)) as E.
  destruct (combination_eq_dec gcons_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, gce_inv in HE; destruct HE as [C0 [A [-> [HC0 [HA ->]]]]].
  pose proof (code_decode _ _ HA) as EC0; subst C0.
  destruct (pair_type_inv O v _ _ Hv) as [c0 [p [-> [Hc0 Hp]]]].
  apply (concrete_type_forces O) in Hc0; [subst c0|exact HC0].
  destruct (pair_type_inv O p _ _ Hp) as [x [xs [-> [Hx Hxs]]]].
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (gcons_eval (code A) x xs)) as ->.
  eapply infer_tag; [cbn; rewrite HC0; reflexivity| |apply (HL (code A))|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|apply pair_typed; eassumption|reflexivity].
  - eapply app2; [apply guard_of_pair|apply lg_hit; right; reflexivity].
Qed.

Theorem gnil_decl_sound : decl_sound O gen_nil_nm D_gnil.
Proof using HL.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec gnil_carrier C)) as E.
  destruct (combination_eq_dec gnil_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, gne_inv in HE; destruct HE as [HU [[A HA] ->]].
  apply (concrete_type_forces O) in Hv; [subst v|exact HU].
  pose proof (code_decode _ _ HA) as EU; subst U.
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (gnil_eval (code A))) as ->.
  eapply infer_tag; [cbn; rewrite HU; reflexivity|apply concrete_is_self_typed; reflexivity|apply (HL (code A))|].
  eapply app2; [apply guard_of_pair|apply lg_hit; left; reflexivity].
Qed.
End Gen.

(** ** The ontology with generic constructors *)

Lemma O_gen_inv : forall n D, O_gen @ n @r tp O_gen ==> Sm D ->
  lookup G_rows n = Some D \/
  (n = update_nm /\ D = D_upd update_nm (tp O_gen)) \/ (n = mku_nm /\ D = D_mku (tp O_gen)) \/
  (exists r, n = list_tag r /\ D = D_list r) \/
  (exists r, n = Fk mkcons_nm r /\ concreteb r = true /\ D = D_mkcons r).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; apply L_fam_inv; exact HF.
Qed.

Lemma O_gen_static : forall n D, lookup G_rows n = Some D -> O_gen @ n @r tp O_gen ==> Sm D.
Proof.
  intros n D H; destruct (L_fam_partial n) as [p Hp]; unfold O_gen; eapply rows_f_hit; eassumption.
Qed.

Lemma O_gen_update : O_gen @ update_nm @r tp O_gen ==> Sm (D_upd update_nm (tp O_gen)).
Proof.
  unfold O_gen; apply rows_f_miss; [reflexivity|]. unfold L_fam; apply alt_some; [apply upd_fam_update|].
  apply alt_partial, list_entry_partial.
Qed.

Lemma O_gen_list : forall r, O_gen @ list_tag r @r tp O_gen ==> Sm (D_list r).
Proof.
  intros r; unfold O_gen; apply rows_f_miss; [reflexivity|]. unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_some; [apply list_entry_hit|]. apply alt_partial.
  pose proof (get_par_spec mkcons_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm list_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  Local Transparent get_par is_concrete. unfold mkcons_entry; eexists; ev2.
Qed.
Local Opaque get_par is_concrete.

Theorem O_gen_sound : ontology_sound O_gen.
Proof.
  intros n D H.
  destruct (O_gen_inv n D H) as [HL|[[-> ->]|[[-> ->]|[[r [-> ->]]|[r [-> [Hc ->]]]]]]].
  - unfold G_rows, D_rows, L_rows, O_rows in HL; cbn [lookup List.app] in HL.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_gen_static; reflexivity|apply guard_of_pair].
    + eapply ctor_decl_sound; [reflexivity|apply O_gen_static; reflexivity|apply guard_of_pair].
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_gen_static; reflexivity|apply guard_of_pair].
    + apply gcons_decl_sound, O_gen_list.
    + apply gnil_decl_sound, O_gen_list.
  - apply upd_decl_sound_g, O_gen_update.
  - apply mku_decl_sound_g, O_gen_update.
  - apply list_decl_sound.
  - eapply ctor_decl_sound; [cbn; exact Hc|apply O_gen_list|apply guard_of_pair].
Qed.

Corollary O_gen_typing_sound : typing_sound O_gen.
Proof. apply evaluation_preserves_typing, O_gen_sound. Qed.

(** ** Examples with run-time codes, by computation *)

Ltac by_run3 := apply (runp_sound 40); vm_done.

Example gen_cons_eval : gen_cons @ (code Nat '* (zero '* nil Nat)) ==> l0. Proof. by_run3. Qed.
Example gen_cons_typed : infer_expression O_gen @ (gen_cons @ (code Nat '* (zero '* nil Nat))) ==> Sm (List Nat).
Proof. by_run3. Qed.
Example gen_cons_wrong : infer_expression O_gen @ (gen_cons @ (code Nat '* (tt '* nil Nat))) ==> Lf. Proof. by_run3. Qed.
Example gen_nil_typed : infer_expression O_gen @ (gen_nil @ code Bool) ==> Sm (List Bool). Proof. by_run3. Qed.

Example appendR_Nat_eval : appendR @ (code Nat '* (l12 '* l0)) ==> l120. Proof. by_run3. Qed.
Example appendR_Nat_typed : infer_expression O_gen @ (appendR @ (code Nat '* (l12 '* l0))) ==> Sm (List Nat). Proof. by_run3. Qed.
Example appendR_Bool_typed : infer_expression O_gen @ (appendR @ (code Bool '* (lb '* ltt))) ==> Sm (List Bool). Proof. by_run3. Qed.
Example appendR_LP_typed : infer_expression O_gen @ (appendR @ (code LP '* (lpe '* lpe))) ==> Sm (List LP). Proof. by_run3. Qed.
Example reverseR_eval : reverseR @ (code Nat '* l12) ==> l21. Proof. by_run3. Qed.
Example reverseR_typed : infer_expression O_gen @ (reverseR @ (code Nat '* l12)) ==> Sm (List Nat). Proof. by_run3. Qed.
Example lengthR_eval : lengthR @ (code Nat '* l120) ==> succ two. Proof. by_run3. Qed.
Example lengthR_typed : infer_expression O_gen @ (lengthR @ (code Nat '* l120)) ==> Sm Nat. Proof. by_run3. Qed.
Example lengthR_Bool_typed : infer_expression O_gen @ (lengthR @ (code Bool '* lb)) ==> Sm Nat. Proof. by_run3. Qed.
Example filterR_eval : filterR @ (code Bool '* ('I '* lb)) ==> ltt. Proof. by_run3. Qed.
Example filterR_typed : infer_expression O_gen @ (filterR @ (code Bool '* ('I '* lb))) ==> Sm (List Bool). Proof. by_run3. Qed.
Example mapR_eval : mapR @ (code Nat '* (code Nat '* (succ_fn '* l0))) ==> cons Nat one (nil Nat). Proof. by_run3. Qed.
Example mapR_typed : infer_expression O_gen @ (mapR @ (code Nat '* (code Nat '* (succ_fn '* l12)))) ==> Sm (List Nat). Proof. by_run3. Qed.
Example foldrightR_eval : foldrightR @ (code Nat '* (code (List Nat) '* (cons_fn Nat '* (l12 '* l0)))) ==> l120. Proof. by_run3. Qed.
Example foldrightR_typed :
  infer_expression O_gen @ (foldrightR @ (code Nat '* (code (List Nat) '* (cons_fn Nat '* (l12 '* l0))))) ==> Sm (List Nat).
Proof. by_run3. Qed.
(** A wrong code: at code Bool on lists of Nat the state type does not
    match, so special_type takes its default and the iteration is the
    identity; the result is the second list, typed List Nat (sound, but
    not an append). *)
Example appendR_wrong_code_eval : appendR @ (code Bool '* (l12 '* l0)) ==> l0. Proof. by_run3. Qed.
Example appendR_wrong_code_typed : infer_expression O_gen @ (appendR @ (code Bool '* (l12 '* l0))) ==> Sm (List Nat).
Proof. by_run3. Qed.
