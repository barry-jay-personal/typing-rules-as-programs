(** * Families of abstract types (support for the paper's Abstract Types and later sections).

    A family at a nametag [N] is an abstractor [AI @ N ==> D] (typing.v):
    [D] maps each carrier type [C] of the family to its eliminator [E],
    [D @ C ==> Sm E], so the type is ['tagged[E,N]], and refuses other
    carriers, [D @ C ==> Lf].

    This file provides the bridge from the soundness of an abstractor
    ([abstractor_sound_by_typing], soundness.v) to the per-clause condition
    of declarations built with [extend] ([plain_clause_sound_for]).  Bool
    (booleans.v), Nat, Option, Sum and List (data_types.v), arrays
    (arrays.v), Query (queries.v) and Update (updates.v) are declared in
    the same form.  Function types are not declared: their introduction
    stays hardwired.  Their eliminator [funty_eliminator U V] is a program
    like any other, the delay of [funty_elim] at [U '* V]. *)

From Stdlib Require Import Arith Lia List String.
From TreeTyping Require Import tree typing soundness.
Import ListNotations.
Set Default Proof Using "Type".
Open Scope string_scope.

(* ================================================================== *)
(** * Bridges from declaration soundness to the per-clause conditions *)
(* ================================================================== *)

(** A clause registers the abstractor [D] at [N] when it selects exactly
    that abstractor, and only at [N]. *)
Definition clause_registers (clause N D : Combination) : Prop :=
  forall M, (M = N /\ clause @ M ==> Sm D) \/
            (M <> N /\ clause @ M ==> Lf).

Lemma tcase_registers : forall N D,
  clause_registers (to_tree (tcase (Val N) (Val D))) N D.
Proof.
  intros N D M; destruct (combination_eq_dec N M) as [->|HM].
  - left; split; [reflexivity|exact (tcase_eq M (Val D))].
  - right; split; [intro HE; apply HM; symmetry; exact HE|exact (tcase_neq N M _ HM)].
Qed.

Lemma clause_registers_inv : forall clause N D M R,
  clause_registers clause N D -> clause @ M ==> Sm R ->
  M = N /\ R = D.
Proof.
  intros clause N D M R Hreg H; destruct (Hreg M) as [[-> HM]|[_ HM]].
  - pose proof (eval_deterministic _ _ H _ HM) as HE; inversion HE; auto.
  - pose proof (eval_deterministic _ _ H _ HM); discriminate.
Qed.

Lemma tcase_never_fork : forall N R M l r,
  to_tree (tcase (Val N) (Val R)) @ M ==> Fk l r -> False.
Proof.
  intros N R M l r H; destruct (combination_eq_dec N M) as [->|HM].
  - pose proof (eval_deterministic _ _ H _ (tcase_eq M (Val R))); discriminate.
  - pose proof (eval_deterministic _ _ H _ (tcase_neq N M _ HM)); discriminate.
Qed.


(** A compiled case [to_tree (tcase (Val N) (Val R))] never returns a
    fork, so it can head an [extend]. *)
Lemma compiled_tcase_never_fork : forall N R c,
  to_tree (tcase (Val N) (Val R)) = c ->
  forall M l r, c @ M ==> Fk l r -> False.
Proof. intros N R c <-; apply tcase_never_fork. Qed.


(** ** Declared wrappers in type application *)


(** The conditional [if_named] is typed through
    the type [IsNamed N], whose eliminator [tagged_by N] runs the name test on
    the argument type.  At an argument type tagged at [N] the test is
    true; at any other argument type it is false. *)
Lemma if_named_application_hit : forall AI N T S D V,
 concrete N -> declared_wrapper AI N T ->
 type_app AI @ S @r wrap_type T N ==> Sm V ->
 type_app AI @ IfNamed N S D @r wrap_type T N ==> Sm V.
Proof.
 intros; eapply if_named_selected; [|apply app_true|apply app_K|eassumption].
 apply app_IsNamed; unfold wrap_type; apply name_test_tag_hit.
Qed.
Lemma if_named_application_miss : forall AI N T S D U V,
 concrete N -> declared_wrapper AI N T -> (forall E, U <> 'tagged[E,N]) ->
 type_app AI @ D @r U ==> Sm V -> type_app AI @ IfNamed N S D @r U ==> Sm V.
Proof.
 intros; eapply if_named_selected; [|apply app_K|apply app_I|eassumption].
 apply app_IsNamed; apply name_test_tag_miss; assumption.
Qed.
(** One-round soundness of the declarations. *)
Lemma plain_declared_sound_for : forall AI clause N D,
  clause_registers clause N ('K1 D) -> abstractor_sound_by_typing AI D ->
  plain_clause_sound_for clause AI.
Proof.
  intros AI clause N D Hreg H2 C M ctor D' R U V Hs Ha Hc HE.
  destruct (clause_registers_inv _ _ _ _ _ Hreg Hs) as [_ ->].
  assert (HK : ('K1 D) @ app AI ==> D) by evaluate.
  pose proof (eval_deterministic _ _ Ha _ HK) as ->.
  exact (H2 C R U V Hc HE).
Qed.

Lemma plain_function_declared_sound_for : forall AI : Decl,
  plain_clause_sound_for function_case AI.
Proof.
  intros AI C N ctor D E U V Hs Hd Hc HE.
  destruct (combination_eq_dec N fun_nm) as [->|HN].
  - pose proof (eval_deterministic _ _ Hs _ function_case_some) as HQ; inversion HQ; subst ctor.
    apply (function_abstractor_sound AI C E U V); [|exact HE].
    eapply eval_appl; eassumption.
  - pose proof (eval_deterministic _ _ Hs _ (function_case_none N HN)); discriminate.
Qed.

Lemma function_case_never_fork : forall N l r, function_case @ N ==> Fk l r -> False.
Proof. exact (compiled_tcase_never_fork _ _ _ eq_refl). Qed.

Lemma plain_empty_ontology_sound_for : forall AI,
  plain_intro_sound_for empty_ontology AI.
Proof.
  intros AI C N E U V Hintro.
  assert (HE : empty_ontology @ N ==> refusal) by (unfold empty_ontology, refusal; evaluate).
  pose proof (declaration_K1_inv _ _ _ _ _ _ HE Hintro) as HC.
  assert (HL : ('K1 Lf) @ C ==> Lf) by evaluate.
  pose proof (eval_deterministic _ _ HC _ HL); discriminate.
Qed.
