(** * Step 84: the generic constructor gen_none, in the style of gen_nil.

      gen_none = tagged[gnone_carrier, gen_none_nm]
      gnone_carrier @ c = tagged[fst, opt_tag[c]]
      declaration at gen_none_nm:
        guard  admits exactly gnone_carrier (its own type)
        elim   gen_none # C = Sm (Option A)   when C is concrete and A = decode C

    So [gen_none @ code[A] = none[A]] for every [A]. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition gen_none_nm : Combination := Nat.iter 41 Sm Lf.

Definition OT (c : Term) : Term := Val Lf @@ Val opt_nm @@ c.
Definition OL (r : Term) : Term := lab (OT r).

Definition gnone_carrier : Combination := Eval cbn -[opt_nm] in to_tree
  (star "c" (tagger_t (OT (Ref "c")) @@ Val 'fst)).
Definition gen_none : Combination := 'tagged[gnone_carrier, gen_none_nm].

(** elim at gnone: [U = C] *)
Definition gnoe_prog : Combination := Eval cbn -[decode_p is_concrete opt_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ Ref "U"
       @@ star "U2" (''onStem1 (star "A" (Val Lf @@ OL (Ref "U2"))) @@ (op decode_p @@ Ref "U2"))
       @@ Val ('K1 Lf) @@ Ref "U")))).

Definition D_gnone : Combination := guard1 gnone_carrier '* gnoe_prog.

Local Opaque gnoe_prog.

Lemma gnoe_inv : forall n a U V, gnoe_prog @ n @r a @r U ==> Sm V ->
  concreteb U = true /\ (exists A, decode U = Some A) /\ V = 'label[Fk opt_nm U].
Proof.
  intros n a U V H. Local Transparent gnoe_prog. unfold gnoe_prog in H. Local Opaque gnoe_prog.
  pose proof (is_concrete_bt U) as Hc; pose proof (decode_p_eval U) as Hd.
  destruct (concreteb U) eqn:Ec; cbn [bt] in Hc; [|crunch].
  destruct (decode U) as [A|] eqn:Ed; cbn [opt] in Hd; crunch.
  all: split; [eassumption|split; [eauto|reflexivity]].
Qed.

Lemma gnoe_fwd : forall A n a, names_concrete A -> gnoe_prog @ n @r a @r code A ==> Sm (Option A).
Proof.
  intros A n a HA. Local Transparent gnoe_prog. unfold gnoe_prog. Local Opaque gnoe_prog.
  pose proof (is_concrete_bt (code A)) as Hc; rewrite (code_concrete A HA) in Hc; cbn [bt] in Hc.
  pose proof (decode_p_code A) as Hd. unfold Option, opt_tag. ev2.
Qed.

Lemma gnone_eval : forall c, gnone_carrier @ c ==> 'tagged['fst, Fk opt_nm c].
Proof. intros; unfold gnone_carrier; evaluate. Qed.

Lemma gen_none_apply : forall A, gen_none @ code A ==> none A.
Proof. intros; unfold gen_none, none, opt_tag; apply tagged_eval, gnone_eval. Qed.

Section GenNone.
Variable O : Combination.
Hypothesis HO : forall r, O @ opt_tag r @r tp O ==> Sm (D_opt r).

(** The declaration is sound by values, in every ontology that declares options. *)
Lemma gen_none_decl_sound : decl_sound O gen_none_nm D_gnone.
Proof using HO.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec gnone_carrier C)) as E.
  destruct (combination_eq_dec gnone_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, gnoe_inv in HE; destruct HE as [HU [[A HA] ->]].
  apply (concrete_type_forces O) in Hv; [subst v|exact HU].
  pose proof (code_decode _ _ HA) as EU; subst U.
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (gnone_eval (code A))) as ->.
  eapply infer_tag; [cbn; rewrite HU; reflexivity|apply concrete_is_self_typed; reflexivity|apply (HO (code A))|].
  eapply app2; [apply guard_of_pair|apply og_hit; left; reflexivity].
Qed.
End GenNone.
