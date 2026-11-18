(** * Step 82 (stage 1): Bool, Nat, a typed tagger, and the examples.

    The example ontology [O_ex] declares three names:
    - [bool_nm]: [Bool = label[bool_nm]], with carriers [fst] and [snd]
      ([tt], [ff]) and the eliminator [Bool # (A * A) = A];
    - [nat_nm]: [Nat = label[nat_nm]], Scott numerals with carriers [fst]
      and [S2[snd, K1 Nat]] ([zero], [succ n]) and the eliminator
      [Nat # (B * S) = B] when [S # Nat ==> Sm B];
    - [mkb_nm]: the typed tagger for Bool, [mk_bool = tagged[tagger[bool_nm], mkb_nm]],
      whose eliminator gives [label[mkb_nm] # U = Bool] when the Bool
      guard admits [U].
    [O_ex] is sound by values ([O_ex_sound]); the tagger's declaration is
    not sound by typing, because [tagger[n] # U] never succeeds
    ([tagger_application_untyped]). *)

From BigStep Require Import tree typing soundness rows identifiers.
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

(** ** General refusals *)

Section Refusals.
Variable O : Combination.

(** Triage is refused at an abstract argument type. *)
Theorem triage_abstract_refused : forall F0 F1 F2 n R,
  ~ (tp O @ 'triage[F0,F1,F2] @r 'label[n] ==> Sm R).
Proof. intros F0 F1 F2 n R H; apply tp_inv in H; inversion H; subst; cbn in *; discriminate. Qed.

(** A fork type whose left branch is a label (the type of a typed value)
    is refused as a function. *)
Theorem fork_label_refused : forall n Y U R, ~ (tp O @ Fk ('label[n]) Y @r U ==> Sm R).
Proof. intros n Y U R H; apply tp_inv in H; inversion H; subst; cbn in *; discriminate. Qed.

(** The untyped tagger: [tagger[n] @ x] has no type, since it builds the
    bare label [label[n]] on the way (as [make_label @ n]). *)
Theorem tagger_application_untyped : forall n X R, ~ (tp O @ 'tagger[n] @r X ==> Sm R).
Proof.
  intros n X R H.
  apply tp_inv in H; inversion H as [| | | |G H0 U V W R0 _ HG HH HVW| | |]; subst.
  apply tp_inv in HH; inversion HH as [| | | |G1 H1 U1 V1 W1 R1 _ HG1 HH1 HVW1| | |]; subst.
  apply tp_inv in HG1; inversion HG1; subst.
  apply tp_inv in HH1; inversion HH1; subst.
  apply tp_inv in HVW1; inversion HVW1 as [| | | |G2 H2 U2 V2 W2 R2 _ HG2 HH2 HVW2| | |]; subst.
  apply tp_inv in HG2; inversion HG2; subst.
  apply tp_inv in HH2; inversion HH2; subst.
  apply tp_inv in HVW2; inversion HVW2; subst.
  cbn in *; discriminate.
Qed.

(** As a value, the tagger is concrete, so it is its own type. *)
Lemma tagger_self_typed : forall n, concreteb n = true -> infer O @ 'tagger[n] ==> Sm ('tagger[n]).
Proof. intros n Hn; apply concrete_is_self_typed; cbn; rewrite Hn; reflexivity. Qed.
End Refusals.

Lemma tagger_eval : forall n x, 'tagger[n] @ x ==> 'tagged[x, n].
Proof. intros; evaluate. Qed.

(** ** Pairs *)

Section Pairs.
Variable O : Combination.
Local Notation "t ':' T" := (infer O @ t ==> Sm T) (at level 70).

Lemma I_self_typed : 'I : 'I.
Proof. apply concrete_is_self_typed; reflexivity. Qed.

Lemma pair_typed : forall a b A B, a : A -> b : B -> (a '* b) : (A '* B).
Proof.
  intros a b A B Ha Hb.
  apply infer_fork; [reflexivity| |apply infer_fork; [reflexivity|apply infer_leaf|exact Hb|reflexivity]|reflexivity].
  apply infer_stem; apply infer_fork; [reflexivity|apply infer_stem, I_self_typed| |reflexivity].
  apply infer_fork; [reflexivity|apply infer_leaf|exact Ha|reflexivity].
Qed.

Lemma pair_type_inv : forall v A B, v : (A '* B) -> exists a b, v = a '* b /\ a : A /\ b : B.
Proof.
  intros v A B H.
  destruct (type_Fk_inv O _ _ _ H) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
  destruct (type_Sm_inv O _ _ Hx) as [x' [-> Hx']].
  destruct (type_Fk_inv O _ _ _ Hx') as [[m E]|[p [q [-> [_ [Hp [Hq _]]]]]]]; [discriminate|].
  destruct (type_Sm_inv O _ _ Hp) as [p' [-> Hp']].
  apply (concrete_type_forces O) in Hp'; [subst p'|reflexivity].
  destruct (type_Fk_inv O _ _ _ Hq) as [[m E]|[q1 [a [-> [_ [Hq1 [Ha _]]]]]]]; [discriminate|].
  pose proof (type_Lf_inv O _ Hq1) as ->.
  destruct (type_Fk_inv O _ _ _ Hy) as [[m E]|[y1 [b [-> [_ [Hy1 [Hb _]]]]]]]; [discriminate|].
  pose proof (type_Lf_inv O _ Hy1) as ->.
  exists a, b; auto.
Qed.
End Pairs.

(** ** The declarations *)

Local Opaque equal.

Definition get_rr : Combination := 'triage[Lf, 'K1 Lf, 'K1 ('triage[Lf, 'K1 Lf, 'K1 'I])].
Definition rr (t : Combination) : Combination :=
  match t with Fk _ (Fk _ d) => d | _ => Lf end.
Lemma get_rr_spec : forall t, get_rr @ t ==> rr t.
Proof. intros [|t|a [|b|c d]]; unfold get_rr; evaluate. Qed.

(** [bool_elim @ n @ r @ U ==> Sm A] exactly when [U = A '* A]. *)
Definition bool_elim : Combination := Eval cbn -[equal get_rr] in to_tree
  (star "n" (star "r" (star "U"
    (star "A" (op equal @@ Ref "U" @@ (Ref "A" ''* Ref "A") @@ (Val Lf @@ Ref "A") @@ Val Lf)
      @@ (op get_rr @@ Ref "U"))))).

Local Opaque get_rr.

Lemma bool_elim_inv : forall n r U V, bool_elim @ n @r r @r U ==> Sm V -> U = V '* V.
Proof.
  intros n r U V H; unfold bool_elim in H.
  pose proof (get_rr_spec U) as Hr.
  pose proof (equal_bt U (rr U '* rr U)) as He; inv_out He.
  destruct (combination_eq_dec U (rr U '* rr U)) as [E|E]; cbn [bt] in *; crunch; auto.
Qed.

Definition bool_nm : Combination := Sm (Sm (Sm (Sm Lf))).
Definition nat_nm : Combination := Sm (Sm (Sm (Sm (Sm Lf)))).
Definition mkb_nm : Combination := Sm (Sm (Sm (Sm (Sm (Sm Lf))))).

Definition Bool : Combination := 'label[bool_nm].
Definition Nat : Combination := 'label[nat_nm].
Definition tt : Combination := 'tagged['fst, bool_nm].
Definition ff : Combination := 'tagged['snd, bool_nm].
(** Scott numerals: [zero @ (z * s) = z] and [succ[m] @ (z * s) = s @ m]. *)
Definition zero : Combination := 'tagged['fst, nat_nm].
Definition succ (n : Combination) : Combination := 'tagged['S2['snd, 'K1 n], nat_nm].

Definition bool_guard : Combination := guard2 'fst 'snd.
Definition D_bool : Combination := bool_guard '* bool_elim.
(** The Nat guard admits [fst] and [S2[snd, K1 Nat]]. *)
Definition ng_prog : Combination := Eval cbn -[equal] in to_tree
  (star "m" (star "C"
    (op equal @@ Ref "C" @@ Val 'fst @@ Val 'K
       @@ (op equal @@ Ref "C" @@ ''S2[Val 'snd, ''K1 (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "m"))])))).
Definition nat_guard : Combination := 'wait[ng_prog, nat_nm].

(** [pn (Fk (Sm z) _) = rr z], the first component of a pair. *)
Definition get_pn : Combination := 'triage[Lf, 'K1 Lf, 'K 'C 'triage[Lf, get_rr, 'K1 ('K1 Lf)]].
Definition pn (t : Combination) : Combination := match t with Fk (Sm z) _ => rr z | _ => Lf end.
Lemma get_pn_spec : forall t, get_pn @ t ==> pn t.
Proof.
  intros [|t|[|z|a b] y]; unfold get_pn; cbn [pn]; try evaluate.
  pose proof (get_rr_spec z); evaluate.
Qed.

(** The eliminator: [Nat # (B * S) = Sm B] when [S # Nat ==> Sm B].  It
    receives its own name [n] and builds [Nat = label[n]] at run time; it
    needs no recursion. *)
Definition nat_eliminator : Combination := Eval cbn -[equal get_rr get_pn] in to_tree
  (star "n" (star "a" (star "U"
    (op equal @@ Ref "U" @@ ((op get_pn @@ Ref "U") ''* (op get_rr @@ Ref "U"))
       @@ star "U2" (''onStem1 (star "R" (op equal @@ Ref "R" @@ (op get_pn @@ Ref "U2")
                                            @@ (Val Lf @@ (op get_pn @@ Ref "U2")) @@ Val Lf))
                       @@ (Ref "a" @@ (op get_rr @@ Ref "U2") @@ (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "n"))))
       @@ Val ('K1 Lf) @@ Ref "U")))).
Definition nat_elim := nat_eliminator.
Definition D_nat : Combination := nat_guard '* nat_eliminator.

(** The constructor eliminator: [ctor_elim g b @ m @ r @ U ==> Sm label[b]]
    when the guard [g] admits [U]; the label is built at run time. *)
Definition ctor_prog : Combination := Eval cbn -[isK] in to_tree
  (star "g" (star "b" (star "m" (star "r" (star "U"
    (op isK @@ (Ref "g" @@ Ref "U") @@ (Val Lf @@ (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "b"))) @@ Val Lf)))))).
Definition ctor_elim (g b : Combination) : Combination := 'wait2[ctor_prog, g, b].

Local Opaque isK.

Lemma ctor_elim_inv : forall g b m r U V, ctor_elim g b @ m @r r @r U ==> Sm V ->
  g @ U ==> 'K /\ V = 'label[b].
Proof.
  intros g b m r U V H; unfold ctor_elim in H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]].
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]].
  apply wait2_eval_inv in Hp1; unfold ctor_prog in Hp1.
  crunch.
  match goal with H : isK @ ?x ==> _ |- _ => pose proof (isK_spec x) as HK;
    destruct (is_Kb x) eqn:EK; cbn [bt] in HK end; crunch.
  apply is_Kb_true in EK; subst; split; [assumption|reflexivity].
Qed.

Definition mk_bool : Combination := 'tagged['tagger[bool_nm], mkb_nm].
Definition D_mkb : Combination := guard1 ('tagger[bool_nm]) '* ctor_elim bool_guard bool_nm.

Definition O_rows : list (Combination * Combination) :=
  [(bool_nm, D_bool); (nat_nm, D_nat); (mkb_nm, D_mkb)].
Definition O_ex : Combination := rows O_rows.

Local Notation "t ':' T" := (infer O_ex @ t ==> Sm T) (at level 70).

(** ** Soundness of the example ontology (by values) *)

Lemma O_ex_lookup : forall n D, O_ex @ n @r tp O_ex ==> Sm D -> lookup O_rows n = Some D.
Proof.
  intros n D H; pose proof (eval_deterministic _ _ H _ (rows_spec O_rows n (tp O_ex))) as E.
  destruct (lookup O_rows n); cbn in E; inversion E; reflexivity.
Qed.

Lemma O_ex_bool : O_ex @ bool_nm @r tp O_ex ==> Sm D_bool.
Proof. exact (rows_spec O_rows bool_nm (tp O_ex)). Qed.

Lemma guard_of_bool : forall C, guard_of @ D_bool @r C ==> 'K -> C = 'fst \/ C = 'snd.
Proof.
  intros C H; destruct (app2_inv _ _ _ _ H) as [g [Hg HC]].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC _ (guard2_spec 'fst 'snd C)) as E.
  apply in2b_true; destruct (in2b 'fst 'snd C); [reflexivity|discriminate].
Qed.

Lemma guard_of_bool_hit : forall C, C = 'fst \/ C = 'snd -> guard_of @ D_bool @r C ==> 'K.
Proof.
  intros C HC; eapply app2; [apply guard_of_pair|].
  pose proof (guard2_spec 'fst 'snd C) as H; unfold in2b in H.
  destruct HC as [->| ->]; cbn in H; exact H.
Qed.

Lemma elim_of_inv : forall g e n a U V, elim_of @ (g '* e) @r n @r a @r U ==> Sm V -> e @ n @r a @r U ==> Sm V.
Proof.
  intros g e n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]].
  destruct (appl_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]].
  destruct (app2_inv _ _ _ _ Hp1) as [p2 [Hp2 Hq2]].
  pose proof (eval_deterministic _ _ Hp2 _ (elim_of_pair _ _)) as ->.
  eapply eval_appl; [eapply eval_appl; [exact Hq2|exact Hq1]|exact Hq].
Qed.

Lemma bool_decl_sound : forall O, decl_sound O bool_nm D_bool.
Proof.
  intros O k C U V c v w HC HE Hc Hv _ Hw.
  apply guard_of_bool in HC.
  apply elim_of_inv, bool_elim_inv in HE; subst U.
  destruct (pair_type_inv O v V V Hv) as [a [b [-> [Ha Hb]]]].
  apply evaln_eval in Hw.
  destruct HC as [->| ->]; (apply (concrete_type_forces O) in Hc; [subst c|reflexivity]).
  - pose proof (eval_deterministic _ _ Hw _ (fst_pair a b)) as ->; exact Ha.
  - pose proof (eval_deterministic _ _ Hw _ (snd_pair a b)) as ->; exact Hb.
Qed.

(** A declaration whose eliminator refuses everything is sound. *)
Lemma refuse_decl_sound : forall O n g, decl_sound O n (g '* refuse_elim).
Proof.
  intros O n g k C U V c v w _ HE.
  apply elim_of_inv in HE.
  pose proof (eval_deterministic _ _ HE _ (refuse_elim_spec n (tp O) U)); discriminate.
Qed.

Local Opaque get_pn.

Lemma nat_guard_spec : forall C, nat_guard @ C ==> 'K -> C = 'fst \/ C = 'S2['snd, 'K1 Nat].
Proof.
  intros C H; apply wait_eval_inv in H; unfold ng_prog in H.
  pose proof (equal_bt C 'fst) as E1; pose proof (equal_bt C ('S2['snd, 'K1 Nat])) as E2.
  inv_out E1; inv_out E2; dedup.
  destruct (combination_eq_dec C 'fst); [left; assumption|].
  destruct (combination_eq_dec C ('S2['snd, 'K1 Nat])); [right; assumption|].
  cbn [bt] in *; crunch.
Qed.

Lemma nat_guard_hit : forall C, C = 'fst \/ C = 'S2['snd, 'K1 Nat] -> nat_guard @ C ==> 'K.
Proof.
  intros C HC; apply wait_eval; unfold ng_prog.
  destruct HC as [->| ->].
  - pose proof (equal_eq 'fst) as He.
    assert (Hn : 'fst <> 'S2['snd, 'K1 Nat]) by discriminate.
    pose proof (equal_neq _ _ Hn) as He2; ev.
  - assert (Hn : 'S2['snd, 'K1 Nat] <> 'fst) by discriminate.
    pose proof (equal_neq _ _ Hn) as He; pose proof (equal_eq ('S2['snd, 'K1 Nat])) as He2.
    split2; evaluate2; repeat first [eassumption | progress evaluate2].
Qed.

Lemma nat_eliminator_inv : forall n a U V, nat_eliminator @ n @r a @r U ==> Sm V ->
  exists S, U = V '* S /\ a @ S @r 'label[n] ==> Sm V.
Proof.
  intros n a U V H; unfold nat_eliminator in H.
  pose proof (get_pn_spec U) as H1; pose proof (get_rr_spec U) as H2.
  pose proof (equal_bt U (pn U '* rr U)) as He; inv_out He; dedup.
  destruct (combination_eq_dec U (pn U '* rr U)) as [EU|]; cbn [bt] in *; crunch.
  all: match goal with H : equal @ ?x ==> ?e, H' : ?e @ ?y ==> _ |- _ =>
    let He := fresh "He" in pose proof (equal_bt x y) as He; inv_out He; dedup;
    destruct (combination_eq_dec x y); cbn [bt] in * end; crunch; try discriminate.
  all: try subst; eexists; split; [eassumption|eapply eval_appl; eassumption].
Qed.

Lemma nat_eliminator_eval : forall n a B S, a @ S @r 'label[n] ==> Sm B ->
  nat_eliminator @ n @r a @r (B '* S) ==> Sm B.
Proof.
  intros n a B S H; unfold nat_eliminator.
  pose proof (get_pn_spec (B '* S)) as H1; pose proof (get_rr_spec (B '* S)) as H2; cbn in H1, H2.
  pose proof (equal_eq (B '* S)) as He; pose proof (equal_eq B) as He2.
  split2; evaluate2; repeat first [eassumption | progress evaluate2].
Qed.

Lemma carrier_snd_inv0 : forall O c P, infer O @ c ==> Sm ('S2['snd, 'K1 P]) ->
  exists p, c = 'S2['snd, 'K1 p] /\ infer O @ p ==> Sm P.
Proof.
  intros O c P H.
  destruct (type_Fk_inv O _ _ _ H) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
  destruct (type_Sm_inv O _ _ Hx) as [x' [-> Hx']].
  apply (concrete_type_forces O) in Hx'; [subst x'|reflexivity].
  destruct (type_Fk_inv O _ _ _ Hy) as [[m E]|[y1 [p [-> [_ [Hy1 [Hp _]]]]]]]; [discriminate|].
  pose proof (type_Lf_inv O _ Hy1) as ->.
  exists p; auto.
Qed.

(** The Nat declaration is sound by values, for every ontology. *)
Theorem nat_interp_sound : forall O, decl_sound O nat_nm D_nat.
Proof.
  intros O k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  apply elim_of_inv, nat_eliminator_inv in HE; destruct HE as [S [-> HS]].
  destruct (pair_type_inv O v V S Hv) as [b [s [-> [Hb Hs]]]].
  destruct (nat_guard_spec _ HC') as [->| ->].
  - apply (concrete_type_forces O) in Hc; [subst c|reflexivity].
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (fst_pair b s)) as ->; exact Hb.
  - destruct (carrier_snd_inv0 O c _ Hc) as [p [-> Hp]].
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (snd_pair b s)) as ->.
    assert (E2 : ('K1 p) @ (b '* s) ==> p) by evaluate.
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as ->.
    eapply Hk; [|exact H3|exact Hs|exact Hp|exact HS]. lia.
Qed.

Lemma nat_decl_sound : forall O, decl_sound O nat_nm D_nat.
Proof. exact nat_interp_sound. Qed.

Section NatTyping.
Variable O : Combination.
Hypothesis HN : O @ nat_nm @r tp O ==> Sm D_nat.

Theorem infer_zero : infer O @ zero ==> Sm Nat.
Proof using HN.
  eapply infer_tag; [reflexivity|apply concrete_is_self_typed; reflexivity|exact HN|].
  eapply app2; [apply guard_of_pair|apply nat_guard_hit; auto].
Qed.

Theorem infer_succ : forall m, infer O @ m ==> Sm Nat -> infer O @ succ m ==> Sm Nat.
Proof using HN.
  intros m Hm; eapply infer_tag; [reflexivity| |exact HN|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|exact Hm|reflexivity].
  - eapply app2; [apply guard_of_pair|apply nat_guard_hit; auto].
Qed.
End NatTyping.

(** A constructor declaration is sound by values: its carrier is
    [tagger[n]], and its eliminator admits the argument types that the
    guard [g] of [n] admits. *)
Lemma ctor_decl_sound : forall O m n Dn g, concreteb n = true ->
  O @ n @r tp O ==> Sm Dn -> guard_of @ Dn ==> g ->
  decl_sound O m (guard1 ('tagger[n]) '* ctor_elim g n).
Proof.
  intros O m n Dn g Hn HDn Hg0 k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g1 [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec ('tagger[n]) C)) as E.
  destruct (combination_eq_dec ('tagger[n]) C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|cbn; rewrite Hn; reflexivity].
  apply elim_of_inv, ctor_elim_inv in HE; destruct HE as [HU ->].
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (tagger_eval n v)) as ->.
  eapply infer_tag; [exact Hn|exact Hv|exact HDn|].
  eapply app2; [exact Hg0|exact HU].
Qed.

Lemma mkb_decl_sound : decl_sound O_ex mkb_nm D_mkb.
Proof. eapply ctor_decl_sound; [reflexivity|exact O_ex_bool|apply guard_of_pair]. Qed.

Theorem O_ex_sound : ontology_sound O_ex.
Proof.
  intros n D H; apply O_ex_lookup in H; unfold O_rows in H; cbn [lookup] in H.
  destruct (combination_eq_dec bool_nm n) as [<-|]; [inversion H; apply bool_decl_sound|].
  destruct (combination_eq_dec nat_nm n) as [<-|]; [inversion H; apply nat_decl_sound|].
  destruct (combination_eq_dec mkb_nm n) as [<-|]; [inversion H; apply mkb_decl_sound|].
  discriminate.
Qed.

Corollary O_ex_typing_sound : typing_sound O_ex.
Proof. apply evaluation_preserves_typing, O_ex_sound. Qed.

(** The tagger's declaration is sound by values but not by typing. *)
Theorem mkb_not_sound_by_typing : ~ decl_sound_by_typing O_ex mkb_nm D_mkb.
Proof.
  intros H.
  assert (HC : guard_of @ D_mkb @r 'tagger[bool_nm] ==> 'K).
  { eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec ('tagger[bool_nm]) ('tagger[bool_nm])) as E.
    destruct (combination_eq_dec ('tagger[bool_nm]) ('tagger[bool_nm])) as [_|n]; [exact E|contradiction]. }
  assert (HE : elim_of @ D_mkb @r mkb_nm @r tp O_ex @r 'fst ==> Sm Bool).
  { apply (runp_sound 40); vm_done. }
  exact (tagger_application_untyped O_ex bool_nm 'fst Bool (H _ _ _ HC HE)).
Qed.

(** ** Examples, by computation *)

Ltac by_run := apply (runp_sound 40); vm_done.

Example tt_Bool : tt : Bool. Proof. by_run. Qed.
Example ff_Bool : ff : Bool. Proof. by_run. Qed.
Example zero_Nat : zero : Nat. Proof. by_run. Qed.
Example one_Nat : succ zero : Nat. Proof. by_run. Qed.
Example fst_self : 'fst : 'fst. Proof. by_run. Qed.

(** The guards refuse other carriers. *)
Example tagged_K_Bool_untyped : infer O_ex @ 'tagged['K, bool_nm] ==> Lf. Proof. by_run. Qed.
Example tagged_fst_undeclared : infer O_ex @ 'tagged['fst, Lf] ==> Lf. Proof. by_run. Qed.

(** Bool is not a member of itself; it has no type at all. *)
Theorem Bool_untyped : forall T, ~ (Bool : T).
Proof. intros T; apply bare_label_untyped. Qed.
Corollary Bool_not_in_Bool : ~ (Bool : Bool).
Proof. apply Bool_untyped. Qed.

(** If-then-else: [b @ (x * y)] at [Bool # (A * A) = A]. *)
Example Bool_elim_Nat : tp O_ex @ Bool @r (Nat '* Nat) ==> Sm Nat. Proof. by_run. Qed.
Example Bool_elim_mixed : tp O_ex @ Bool @r (Nat '* Bool) ==> Lf. Proof. by_run. Qed.
Example if_then_else_typed : infer_expression O_ex @ (tt @ (zero '* succ zero)) ==> Sm Nat. Proof. by_run. Qed.
Example if_then_else_eval : tt @ (zero '* succ zero) ==> zero. Proof. by_run. Qed.
Example if_bool_typed : infer_expression O_ex @ (ff @ (ff '* tt)) ==> Sm Bool. Proof. by_run. Qed.

(** Triage at Bool is refused, and allowed at a concrete type. *)
Example isLeaf_Bool : tp O_ex @ 'isLeaf @r Bool ==> Lf. Proof. by_run. Qed.
Example isLeaf_Lf : tp O_ex @ 'isLeaf @r Lf ==> Sm 'K. Proof. by_run. Qed.

(** A fork whose left part is a typed value is typed, but not applicable. *)
Example label_left_typed : Fk tt ('K1 ff) : Fk Bool ('K1 Bool). Proof. by_run. Qed.

(** The tagger. *)
Example tagger_typed_value : 'tagger[bool_nm] : 'tagger[bool_nm]. Proof. by_run. Qed.
Example tagger_app_untyped : infer_expression O_ex @ ('tagger[bool_nm] @ 'fst) ==> Lf. Proof. by_run. Qed.
Example mk_bool_typed : mk_bool : 'label[mkb_nm]. Proof. by_run. Qed.
Example mk_bool_app_typed : infer_expression O_ex @ (mk_bool @ 'fst) ==> Sm Bool. Proof. by_run. Qed.
Example mk_bool_app_eval : mk_bool @ 'fst ==> tt. Proof. by_run. Qed.
Example mk_bool_refuses : infer_expression O_ex @ (mk_bool @ 'K) ==> Lf. Proof. by_run. Qed.

(** Codes. *)
Example code_Bool : code Bool = Fk (Fk Lf Lf) bool_nm. Proof. reflexivity. Qed.
Example code_Bool_Nat : code (Bool '* Nat) =
  Fk (Sm (Sm (Fk (Sm (Sm (code 'I))) (Fk (Sm Lf) (Fk (Fk Lf Lf) bool_nm)))))
     (Fk (Sm Lf) (Fk (Fk Lf Lf) nat_nm)).
Proof. reflexivity. Qed.
Example decode_code_Bool : decode (code Bool) = Some Bool. Proof. reflexivity. Qed.
Example decode_code_Bool_Nat : decode (code (Bool '* Nat)) = Some (Bool '* Nat). Proof. reflexivity. Qed.
Example decode_p_Bool_Nat : decode_p @ code (Bool '* Nat) ==> Sm (Bool '* Nat). Proof. apply decode_p_code. Qed.
Example code_p_Bool_Nat : code_p @ (Bool '* Nat) ==> code (Bool '* Nat). Proof. apply code_p_eval. Qed.
Example code_Bool_Nat_self_typed : code (Bool '* Nat) : code (Bool '* Nat).
Proof. apply code_self_typed; cbn; auto. Qed.
Example code_Bool_not_Bool : code Bool <> Bool. Proof. discriminate. Qed.

(** No typing program contains a label: the programs are concrete. *)
Example tp_concrete : concreteb (tp O_ex) = true. Proof. vm_compute; reflexivity. Qed.
Example infer_concrete : concreteb (infer O_ex) = true. Proof. vm_compute; reflexivity. Qed.
Example infer_expression_concrete : concreteb (infer_expression O_ex) = true. Proof. vm_compute; reflexivity. Qed.
Example O_ex_concrete : concreteb O_ex = true. Proof. vm_compute; reflexivity. Qed.
