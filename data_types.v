(** * Step 82, stage 2C: options with codes.

    [Option A = label[opt_tag[code A]]] with [opt_tag[c] = Fk opt_nm c].
    Its declaration, computed by the family program [opt_entry] from the
    name, decodes the code to [A]:

      guard:  admits fst                (the carrier of none)
              and S2[snd, K1 A]         (the type of the carrier of some[a], a : A)
      elim:   Option A # (B * S) ==> Sm B   when  S # A ==> Sm B

    Values: [none[A] = tagged[fst, opt_tag[code A]]] and
    [some[A,a] = tagged[S2[snd, K1 a], opt_tag[code A]]], so that
    [none @ (n * s) = n] and [some[a] @ (n * s) = s @ a].
    The declaration is sound by values.  At [A = Empty], [none] is typed
    and [some] has no typed argument. *)

From BigStep Require Import tree typing soundness rows identifiers booleans functions updates.
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par.

Definition opt_nm : Combination := Nat.iter 12 Sm Lf.
Definition opt_tag (c : Combination) : Combination := Fk opt_nm c.
Definition Option (A : Combination) : Combination := 'label[opt_tag (code A)].
Definition none (A : Combination) : Combination := 'tagged['fst, opt_tag (code A)].
Definition some (A a : Combination) : Combination := 'tagged['S2['snd, 'K1 a], opt_tag (code A)].

Definition og_prog : Combination := Eval cbn -[equal decode_p] in to_tree
  (star "r" (star "C"
    (''onStem1 (star "A" (op equal @@ Ref "C" @@ Val 'fst @@ Val 'K
                            @@ (op equal @@ Ref "C" @@ ''S2[Val 'snd, ''K1 (Ref "A")])))
       @@ (op decode_p @@ Ref "r")))).

Definition PN (U : Term) := pr (pr (ps (pl U))).
Definition PS (U : Term) := pr (pr U).

Definition oe_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s] in to_tree
  (star "r" (star "n" (star "a" (star "U"
    (''onStem1 (star "A"
        (op equal @@ Ref "U" @@ (PN (Ref "U") ''* PS (Ref "U"))
           @@ star "U2" (''onStem1 (star "R" (op equal @@ Ref "R" @@ PN (Ref "U2")
                                                 @@ (Val Lf @@ PN (Ref "U2")) @@ Val Lf))
                           @@ (Ref "a" @@ PS (Ref "U2") @@ Ref "A"))
           @@ Val ('K1 Lf) @@ Ref "U"))
       @@ (op decode_p @@ Ref "r")))))).

Definition opt_elim : Combination := name_elim oe_prog.
Definition D_opt (r : Combination) : Combination := 'wait[og_prog, r] '* opt_elim.

Definition opt_entry : Combination := Eval cbn -[get_par opt_nm opt_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (Val Lf @@ (''wait[Val og_prog, Ref "r"] ''* Val opt_elim)))
       @@ (op (get_par opt_nm) @@ Ref "n")))).

Definition O_opt : Combination := rows_f (O_rows ++ [(empty_nm, D_empty)]) opt_entry.

Local Opaque og_prog oe_prog.

(** ** The declaration *)

Lemma og_inv : forall r C, 'wait[og_prog, r] @ C ==> 'K ->
  exists A, decode r = Some A /\ (C = 'fst \/ C = 'S2['snd, 'K1 A]).
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent og_prog. unfold og_prog in H. Local Opaque og_prog.
  pose proof (decode_p_eval r) as Hd.
  destruct (decode r) as [A|]; cbn [opt] in Hd; [|crunch].
  exists A; split; [reflexivity|].
  pose proof (equal_bt C 'fst) as E1; pose proof (equal_bt C ('S2['snd, 'K1 A])) as E2.
  inv_out E1; inv_out E2; dedup.
  destruct (combination_eq_dec C 'fst); [left; assumption|].
  destruct (combination_eq_dec C ('S2['snd, 'K1 A])); [right; assumption|].
  cbn [bt] in *; crunch.
Qed.

Lemma og_hit : forall A C, C = 'fst \/ C = 'S2['snd, 'K1 A] -> 'wait[og_prog, code A] @ C ==> 'K.
Proof.
  intros A C HC; apply wait_eval. Local Transparent og_prog. unfold og_prog. Local Opaque og_prog.
  pose proof (decode_p_code A) as Hd.
  destruct HC as [->| ->].
  - pose proof (equal_eq 'fst) as He.
    assert (Hn : 'fst <> 'S2['snd, 'K1 A]) by discriminate.
    pose proof (equal_neq _ _ Hn) as He2; ev2.
  - assert (Hn : 'S2['snd, 'K1 A] <> 'fst) by discriminate.
    pose proof (equal_neq _ _ Hn) as He; pose proof (equal_eq ('S2['snd, 'K1 A])) as He2; ev2.
Qed.

Lemma oe_inv : forall r n a U V, 'wait[oe_prog, r] @ n @r a @r U ==> Sm V ->
  exists A S, decode r = Some A /\ U = V '* S /\ a @ S @r A ==> Sm V.
Proof.
  intros r n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent oe_prog. unfold oe_prog in Hp1. Local Opaque oe_prog.
  pose proof (decode_p_eval r) as Hd.
  destruct (decode r) as [A|]; cbn [opt] in Hd; crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs; try discriminate.
  eq_case2; crunch; use_specs; try discriminate.
  all: match goal with E : ?U = _ |- _ => is_var U; rewrite E end.
  all: do 2 eexists; split; [reflexivity|split; [reflexivity|eapply eval_appl; eassumption]].
Qed.

Lemma opt_entry_inv : forall n a D, opt_entry @ n @r a ==> Sm D -> exists r, n = opt_tag r /\ D = D_opt r.
Proof.
  intros n a D H; unfold opt_entry in H.
  pose proof (get_par_spec opt_nm n) as Hp.
  destruct (par_of opt_nm n) as [r|] eqn:E; cbn [opt] in Hp; crunch.
  eexists; split; [apply par_of_some; eassumption|reflexivity].
Qed.

Lemma opt_entry_hit : forall r a, opt_entry @ opt_tag r @r a ==> Sm (D_opt r).
Proof.
  intros r a; unfold opt_entry.
  pose proof (get_par_spec opt_nm (opt_tag r)) as Hp; cbn [par_of opt_tag] in Hp.
  destruct (combination_eq_dec opt_nm opt_nm); [|contradiction]; cbn [opt] in Hp.
  ev2.
Qed.

Lemma opt_entry_partial : forall n, exists p, opt_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec opt_nm n) as Hp.
  destruct (par_of opt_nm n); cbn [opt] in Hp; unfold opt_entry; eexists; ev2.
Qed.

Definition P_rows : list (Combination * Combination) := (O_rows ++ [(empty_nm, D_empty)])%list.

Lemma O_opt_opt : forall r, O_opt @ opt_tag r @r tp O_opt ==> Sm (D_opt r).
Proof. intros r; unfold O_opt; apply rows_f_miss; [reflexivity|apply opt_entry_hit]. Qed.

Lemma O_opt_static : forall n D, lookup P_rows n = Some D -> O_opt @ n @r tp O_opt ==> Sm D.
Proof.
  intros n D H; destruct (opt_entry_partial n) as [p Hp]; unfold O_opt; eapply rows_f_hit; eassumption.
Qed.

Lemma O_opt_inv : forall n D, O_opt @ n @r tp O_opt ==> Sm D ->
  lookup P_rows n = Some D \/ (exists r, n = opt_tag r /\ D = D_opt r).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; eapply opt_entry_inv; exact HF.
Qed.

(** The option declaration is sound by values, for every ontology. *)
Theorem opt_decl_sound : forall O r, decl_sound O (opt_tag r) (D_opt r).
Proof.
  intros O r k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (og_inv _ _ HC') as [A [HA [->| ->]]];
  apply elim_of_inv in HE; unfold opt_elim in HE;
  apply name_elim_iff, oe_inv in HE; cbn [right_of opt_tag] in HE; destruct HE as [A' [S [HA' [-> HS]]]];
  rewrite HA in HA'; inversion HA'; subst A'.
  - apply (concrete_type_forces O) in Hc; [subst c|reflexivity].
    destruct (pair_type_inv O v V S Hv) as [b [s [-> [Hb Hs]]]].
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (fst_pair b s)) as ->; exact Hb.
  - destruct (pair_type_inv O v V S Hv) as [b [s [-> [Hb Hs]]]].
    clear Hv; force O.
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (snd_pair b s)) as ->.
    match goal with H2 : evaln _ (('K1 ?x) @ _) _ |- _ =>
      assert (E2 : ('K1 x) @ (b '* s) ==> x) by evaluate;
      pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as -> end.
    eapply Hk; [|exact H3|exact Hs|eassumption|exact HS]; lia.
Qed.

Theorem O_opt_sound : ontology_sound O_opt.
Proof.
  intros n D H.
  destruct (O_opt_inv n D H) as [HL|[r [-> ->]]]; [|apply opt_decl_sound].
  unfold P_rows, O_rows in HL; cbn [lookup app] in HL.
  repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
  - apply bool_decl_sound.
  - apply nat_decl_sound.
  - eapply ctor_decl_sound; [reflexivity|apply O_opt_static; reflexivity|apply guard_of_pair].
  - unfold D_empty; apply nothing_decl_sound.
Qed.

Corollary O_opt_typing_sound : typing_sound O_opt.
Proof. apply evaluation_preserves_typing, O_opt_sound. Qed.

(** ** Typings *)

Local Notation "t ':' T" := (infer O_opt @ t ==> Sm T) (at level 70).

Lemma opt_tag_concrete : forall A, names_concrete A -> concreteb (opt_tag (code A)) = true.
Proof.
  intros A HA; unfold opt_tag; cbn [concreteb]; rewrite (code_concrete A HA).
  assert (E : label_pair opt_nm (code A) = false) by reflexivity.
  rewrite E; reflexivity.
Qed.

Theorem none_typed : forall A, names_concrete A -> none A : Option A.
Proof.
  intros A HA; eapply infer_tag; [apply opt_tag_concrete, HA| |apply O_opt_opt|].
  - apply concrete_is_self_typed; reflexivity.
  - eapply app2; [apply guard_of_pair|apply og_hit; auto].
Qed.

Theorem some_typed : forall A a, names_concrete A -> a : A -> some A a : Option A.
Proof.
  intros A a HA Ha; eapply infer_tag; [apply opt_tag_concrete, HA| |apply O_opt_opt|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|exact Ha|reflexivity].
  - eapply app2; [apply guard_of_pair|apply og_hit; auto].
Qed.

(** Empty has no values here either. *)
Theorem Empty_no_values_opt : forall v, ~ (v : Empty).
Proof.
  intros v H; destruct (no_junk O_opt v empty_nm H) as [f [F [D [_ [_ [_ [HD HG]]]]]]].
  pose proof (eval_deterministic _ _ HD _ (O_opt_static empty_nm D_empty eq_refl)) as E; inversion E; subst.
  destruct (app2_inv _ _ _ _ HG) as [g [Hg HC]].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  assert (H0 : ('K1 'KI) @ F ==> 'KI) by evaluate.
  pose proof (eval_deterministic _ _ HC _ H0); discriminate.
Qed.

Theorem none_Empty_typed : none Empty : Option Empty.
Proof. apply none_typed; cbn; reflexivity. Qed.

(** [some[Empty, a]] is never typed: its argument would have to be a value of Empty. *)
Theorem some_Empty_untyped : forall a T, ~ (some Empty a : T).
Proof.
  intros a T H.
  apply infer_inv in H; inversion H as [| |f n F D _ Hf HD HG|u1 u2 U1 U2 Ht _ _ _]; subst.
  - pose proof (eval_deterministic _ _ HD _ (O_opt_opt (code Empty))) as E; inversion E; subst.
    destruct (app2_inv _ _ _ _ HG) as [g [Hg HC]].
    pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
    destruct (og_inv _ _ HC) as [A [HA [->| ->]]].
    + apply (concrete_type_forces O_opt) in Hf; [discriminate|reflexivity].
    + cbn in HA; inversion HA; subst.
      destruct (pair_type_inv O_opt _ _ _ Hf) as [a0 [b0 [E0 [_ Hb0]]]]; inversion E0; subst.
      exact (Empty_no_values_opt _ Hb0).
  - cbn in Ht; discriminate.
Qed.

(** ** Examples *)

Example none_Nat : none Nat : Option Nat. Proof. by_run. Qed.
Example some_Nat : some Nat zero : Option Nat. Proof. by_run. Qed.
Example some_wrong : infer O_opt @ some Nat tt ==> Lf. Proof. by_run. Qed.
Example opt_elim_some : infer_expression O_opt @ (some Nat zero @ (succ zero '* 'K1 zero)) ==> Sm Nat. Proof. by_run. Qed.
Example opt_elim_some_eval : some Nat (succ zero) @ (zero '* 'I) ==> succ zero. Proof. by_run. Qed.
Example opt_elim_none_eval : none Nat @ (zero '* 'I) ==> zero. Proof. by_run. Qed.
Example opt_elim_wrong : tp O_opt @ Option Nat @r (Nat '* 'K1 Bool) ==> Lf. Proof. by_run. Qed.
Example opt_Empty_elim : tp O_opt @ Option Empty @r (Nat '* 'K1 Nat) ==> Sm Nat. Proof. by_run. Qed.
Example code_Option_Nat : code (Option Nat) = Fk (Fk Lf Lf) (opt_tag (code Nat)). Proof. reflexivity. Qed.
