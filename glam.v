(** * Step 82, stage 6, part 4: a generic lambda constructor with run-time codes.

      gen_lam = tagged[glam_carrier, gen_lam_nm]
      glam_carrier @ (cA * (cB * f)) = tagged[f, fun_tag[cA, cB]]     (= lam[f,A,B] when cA = code A, cB = code B)
      declaration at gen_lam_nm:
        guard  admits exactly glam_carrier (its own type)
        elim   gen_lam # (C1 * (C2 * F)) = Sm (Fun A B)
               when C1 and C2 are concrete, A = decode C1, B = decode C2 and F # A ==> Sm B

    It is gen_cons for functions: lambda programs whose domains and
    codomains arrive at run time.  The declaration is sound by values. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition gen_lam_nm : Combination := Nat.iter 28 Sm Lf.

Definition fst_t (x : Term) : Term := Val 'fst @@ x.
Definition snd_t (x : Term) : Term := Val 'snd @@ x.

Definition glam_carrier : Combination := Eval cbn -[fun_nm] in to_tree
  (star "q" (tagger_t (Val Lf @@ Val fun_nm @@ (Val Lf @@ fst_t (Ref "q") @@ fst_t (snd_t (Ref "q"))))
               @@ snd_t (snd_t (Ref "q")))).
Definition gen_lam : Combination := 'tagged[glam_carrier, gen_lam_nm].

(** The elim reads [U = C1 * (C2 * F)]. *)
Definition FunL (c1 c2 : Term) : Term := lab (Val Lf @@ Val fun_nm @@ (Val Lf @@ c1 @@ c2)).
Definition glm_body : Term :=
  star "U2" (''onStem1 (star "A" (''onStem1 (star "B"
     (op equal @@ Ref "U2" @@ (PN (Ref "U2") ''* (PN (PS (Ref "U2")) ''* PS (PS (Ref "U2"))))
        @@ star "U3" (''onStem1 (star "R" (op equal @@ Ref "R" @@ Ref "B"
                                            @@ (Val Lf @@ FunL (PN (Ref "U3")) (PN (PS (Ref "U3")))) @@ Val Lf))
                      @@ (Ref "a" @@ PS (PS (Ref "U3")) @@ Ref "A"))
        @@ Val ('K1 Lf) @@ Ref "U2"))
     @@ (op decode_p @@ PN (PS (Ref "U2")))))
   @@ (op decode_p @@ PN (Ref "U2"))).
Definition glm_prog : Combination := Eval cbn -[equal decode_p is_concrete get_l get_r get_s fun_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ PN (Ref "U")
       @@ star "U1" (op is_concrete @@ PN (PS (Ref "U1")) @@ glm_body @@ Val ('K1 Lf) @@ Ref "U1")
       @@ Val ('K1 Lf) @@ Ref "U")))).

Definition D_glam : Combination := guard1 glam_carrier '* glm_prog.

Local Opaque glm_prog.

Definition pn1 (U : Combination) := right_of (right_of (stem_of (left_of U))).
Definition ps1 (U : Combination) := right_of (right_of U).

Lemma pn1_pair : forall x y, pn1 (x '* y) = x. Proof. reflexivity. Qed.
Lemma ps1_pair : forall x y, ps1 (x '* y) = y. Proof. reflexivity. Qed.

Ltac proj_specs U :=
  pose proof (get_l_spec U); pose proof (get_s_spec (left_of U));
  pose proof (get_r_spec (stem_of (left_of U))); pose proof (get_r_spec (right_of (stem_of (left_of U))));
  pose proof (get_r_spec U); pose proof (get_r_spec (right_of U)).

Lemma glm_inv : forall n a U V, glm_prog @ n @r a @r U ==> Sm V ->
  exists A B F, U = code A '* (code B '* F) /\ concreteb (code A) = true /\ concreteb (code B) = true /\
    a @ F @r A ==> Sm B /\ V = Fun A B.
Proof.
  intros n a U V H. Local Transparent glm_prog. unfold glm_prog in H. Local Opaque glm_prog.
  proj_specs U; proj_specs (ps1 U).
  pose proof (is_concrete_bt (pn1 U)) as Hc1; pose proof (is_concrete_bt (pn1 (ps1 U))) as Hc2.
  pose proof (decode_p_eval (pn1 U)) as Hd1; pose proof (decode_p_eval (pn1 (ps1 U))) as Hd2.
  unfold pn1, ps1 in *.
  destruct (concreteb (right_of (right_of (stem_of (left_of U))))) eqn:Ec1; cbn [bt] in Hc1; [|crunch].
  destruct (concreteb (right_of (right_of (stem_of (left_of (right_of (right_of U))))))) eqn:Ec2; cbn [bt] in Hc2;
    [|crunch; crunch].
  destruct (decode (right_of (right_of (stem_of (left_of U))))) as [A|] eqn:EA; cbn [opt] in Hd1; [|crunch; crunch].
  destruct (decode (right_of (right_of (stem_of (left_of (right_of (right_of U))))))) as [B|] eqn:EB; cbn [opt] in Hd2;
    [|crunch; crunch].
  crunch; use_specs; crunch; use_specs; crunch.
  all: try (eq_case2; crunch; use_specs; try discriminate).
  all: try (eq_case2; crunch; use_specs; try discriminate).
  all: try (eq_case2; crunch; use_specs; try discriminate).
  match goal with EA : decode _ = Some ?A, EB : decode _ = Some ?B, e : ?U = _ '* (_ '* ?F) |- _ =>
    exists A, B, F; pose proof (code_decode _ _ EA) as IA; pose proof (code_decode _ _ EB) as IB;
    unfold Fun, fun_tag; rewrite IA, IB; split; [exact e|split; [assumption|split; [assumption|split]]] end.
  - eapply app2; eassumption.
  - reflexivity.
Qed.

Lemma glm_fwd : forall A B F a n, names_concrete A -> names_concrete B -> a @ F @r A ==> Sm B ->
  glm_prog @ n @r a @r (code A '* (code B '* F)) ==> Sm (Fun A B).
Proof.
  intros A B F a n HA HB H. Local Transparent glm_prog. unfold glm_prog. Local Opaque glm_prog.
  set (U := code A '* (code B '* F)).
  proj_specs U; proj_specs (ps1 U). unfold ps1, U in *; cbn [left_of right_of stem_of] in *.
  pose proof (is_concrete_bt (code A)) as Hc1; pose proof (is_concrete_bt (code B)) as Hc2.
  rewrite (code_concrete A HA) in Hc1; rewrite (code_concrete B HB) in Hc2; cbn [bt] in Hc1, Hc2.
  pose proof (decode_p_code A) as Hd1; pose proof (decode_p_code B) as Hd2.
  pose proof (equal_eq (code A '* (code B '* F))) as He; pose proof (equal_eq B) as He2.
  destruct (app2_inv _ _ _ _ H) as [h [Hh1 Hh2]].
  eapply eval_appl; [eapply eval_appl; [|]|]; ev2.
Qed.

Lemma glam_eval : forall cA cB f, glam_carrier @ (cA '* (cB '* f)) ==> 'tagged[f, fun_tag cA cB].
Proof. intros; unfold glam_carrier; evaluate. Qed.

Lemma fun_tag_concrete : forall A B, concreteb (code A) = true -> concreteb (code B) = true ->
  concreteb (fun_tag (code A) (code B)) = true.
Proof.
  intros A B HA HB; unfold fun_tag; cbn [concreteb]; rewrite HA, HB.
  assert (HL : label_pair (code A) (code B) = false)
    by (destruct (label_pair (code A) (code B)) eqn:E; [destruct (label_pair_K1 _ _ E) as [m Em];
        exfalso; exact (code_not_K1 B m Em)|reflexivity]).
  rewrite HL; reflexivity.
Qed.

Section GenLam.
Variable O : Combination.
Hypothesis HF : forall r, O @ Fk fun_nm r @r tp O ==> Sm (fun_D r (tp O)).

Theorem glam_decl_sound : decl_sound O gen_lam_nm D_glam.
Proof using HF.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec glam_carrier C)) as E.
  destruct (combination_eq_dec glam_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, glm_inv in HE; destruct HE as [A [B [F [-> [HcA [HcB [HAB ->]]]]]]].
  destruct (pair_type_inv O v _ _ Hv) as [c1 [p [-> [Hc1 Hp]]]].
  apply (concrete_type_forces O) in Hc1; [subst c1|exact HcA].
  destruct (pair_type_inv O p _ _ Hp) as [c2 [f [-> [Hc2 Hf]]]].
  apply (concrete_type_forces O) in Hc2; [subst c2|exact HcB].
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (glam_eval (code A) (code B) f)) as ->.
  eapply infer_tag; [apply fun_tag_concrete; assumption|exact Hf|apply HF|].
  eapply app2; [apply guard_of_pair|apply fun_guard_hit; exact HAB].
Qed.
End GenLam.
