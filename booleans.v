(** * The abstract type of booleans (paper: Abstract Types, "Booleans").

    Generic typing support for concrete values, which the booleans need,
    then the abstract type Bool, and the theorem [Bool_untypable] that Bool
    has no type.  The self-typing theorems (paper: Concrete Types) are in
    self_typing.v.

    Build order: this file follows soundness.v, because the soundness of
    the boolean abstractor uses the framework defined there. *)


(**********************************************************************)
(* Generic typing support for concrete values.                        *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness families.

Set Default Proof Using "Type".
Open Scope string_scope.
(** Value-level counterpart of the term-level fork matcher in [terms]. *)
Notation "'onFork1 f" := (Fk ('K1 ('K1 Lf)) f) (at level 10).

Opaque equal.

Definition get_S_fields :=
  Eval cbv -[equal1] in
    to_tree
      (tcase
         (''S2 [Ref "G", Ref "F"])
         (Val Lf @@ Ref "G" @@ Ref "F")).

Lemma get_S_fields_some : forall G F,
  get_S_fields @ ('S2 [G, F]) ==> Sm (Fk G F).
Proof.
  intros G F; unfold get_S_fields.
  repeat (eapply equal1_eq || evaluate).
Qed.

Lemma get_S_fields_inv : forall X G F,
  get_S_fields @ X ==> Sm (Fk G F) ->
  X = 'S2 [G, F].
Proof.
  intros X G F H; unfold get_S_fields in H.
  inv_out H; invert_eval.
Qed.

Lemma get_S_fields_result_inv : forall X R,
  get_S_fields @ X ==> R ->
  R = Lf \/ exists G F, R = Sm (Fk G F) /\ X = 'S2[G,F].
Proof.
  intros X R H; destruct R as [| R | R1 R2].
  - left; reflexivity.
  - destruct R as [| R | G F].
    + unfold get_S_fields in H; inv_out H; invert_eval.
    + unfold get_S_fields in H; inv_out H; invert_eval.
    + right; exists G, F; split; [reflexivity |].
      eapply get_S_fields_inv; exact H.
  - unfold get_S_fields in H; inv_out H; invert_eval.
Qed.

(** Recognize a unary [K] application and recover its payload. *)
Definition get_K1_package :
  { t : Combination |
    to_tree (tcase
      (Val Lf @@ Val Lf @@ Ref "A") (Ref "A")) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition get_K1 :=
  Eval cbn in proj1_sig get_K1_package.

Local Lemma get_K1_compilation :
  to_tree (tcase
    (Val Lf @@ Val Lf @@ Ref "A") (Ref "A")) = get_K1.
Proof.
  unfold get_K1; exact (proj2_sig get_K1_package).
Qed.

Lemma get_K1_some : forall A,
  get_K1 @ ('K1 A) ==> Sm A.
Proof.
  intro A; rewrite <- get_K1_compilation; simpl.
  pose proof (closed_test_eq Lf); evaluate.
Qed.

Lemma get_K1_none_left : forall L A,
  L <> Lf -> get_K1 @ Fk L A ==> Lf.
Proof.
  intros L A Hneq; rewrite <- get_K1_compilation; simpl.
  pose proof (closed_test_neq Lf L ltac:(congruence)); evaluate.
Qed.

Lemma get_K1_inv : forall X A,
  get_K1 @ X ==> Sm A -> X = 'K1 A.
Proof.
  intros X A H; pose proof H as Hwhole.
  rewrite <- get_K1_compilation in H; simpl in H.
  destruct X as [| X | X1 X2].
  - invert_eval.
  - invert_eval.
  - destruct X1 as [| X1 | X11 X12].
    + assert (Sm A = Sm X2)
        by (eapply eval_deterministic;
            [exact Hwhole | apply get_K1_some]).
      inversion H0; reflexivity.
    + pose proof (eval_deterministic _ _ Hwhole _
        (get_K1_none_left (Sm X1) X2 ltac:(discriminate)));
        discriminate.
    + pose proof (eval_deterministic _ _ Hwhole _
        (get_K1_none_left (Fk X11 X12) X2 ltac:(discriminate)));
        discriminate.
Qed.

Lemma K1_decide : forall X,
  (exists A, X = 'K1 A) \/ (forall A, X <> 'K1 A).
Proof.
  intro X; destruct X as [| X | left right].
  - right; intros A H; discriminate H.
  - right; intros A H; discriminate H.
  - destruct left as [| left | left1 left2].
    + left; exists right; reflexivity.
    + right; intros A H; discriminate H.
    + right; intros A H; discriminate H.
Qed.

Lemma get_K1_none : forall X,
  (forall A, X <> 'K1 A) -> get_K1 @ X ==> Lf.
Proof.
  intros X Hnone; destruct X as [| X | left right].
  - rewrite <- get_K1_compilation; simpl; evaluate.
  - rewrite <- get_K1_compilation; simpl; evaluate.
  - destruct left as [| left | left1 left2].
    + exfalso; apply (Hnone right); reflexivity.
    + apply get_K1_none_left; discriminate.
    + apply get_K1_none_left; discriminate.
Qed.

Opaque get_K1.

Definition get_product_parameters :=
  Eval cbv -[equal1] in
    to_tree
      (tcase
         (Val Lf @@ (''S2 [''I, ''K1 Ref "U1"]) @@ (''K1 Ref "U2"))
         (Val Lf @@ Ref "U1" @@ Ref "U2")).

Lemma get_product_parameters_some : forall U1 U2,
  get_product_parameters @
    (Fk ('S2 ['I, 'K1 U1]) ('K1 U2)) ==> Sm (Fk U1 U2).
Proof.
  intros U1 U2; unfold get_product_parameters.
  repeat (eapply equal1_eq || evaluate).
Qed.

Lemma get_product_parameters_inv : forall X U1 U2,
  get_product_parameters @ X ==> Sm (Fk U1 U2) ->
  X = Fk ('S2 ['I, 'K1 U1]) ('K1 U2).
Proof.
  intros X U1 U2 H; unfold get_product_parameters in H.
  inv_out H; invert_eval.
Qed.

(** Recognize the homogeneous product parameters required by eliminators
    such as the Boolean eliminator. *)
Definition get_equal_parameters_continuation :=
  Eval cbv -[equal] in
    to_tree
      (star "eq1"
        (star "U1"
          (star "U2"
            (Ref "eq1" @@ Ref "U2" @@
              (Val Lf @@ (Val Lf @@ Ref "U1")) @@ Val Lf)))).

Definition get_equal_parameters :=
  'onFork1
    ('S2[get_equal_parameters_continuation 'C equal, 'I]).

Lemma get_equal_parameters_some : forall U,
  get_equal_parameters @ (Fk U U) ==> ('S1 U).
Proof.
  intros U; unfold get_equal_parameters.
  evaluate.
  eapply equal_eval.
  unfold get_equal_parameters_continuation; evaluate; evaluate.
  evaluate.
  evaluate.
  eapply equal1_eq.
  evaluate.
  evaluate.
Qed.

Lemma get_equal_parameters_inv : forall X U,
  get_equal_parameters @ X ==> ('S1 U) ->
  X = Fk U U.
Proof.
  intros X U H; unfold get_equal_parameters in H.
  inv_out H; invert_eval.
  eqtac.
  inv_out H8; invert_eval.
  eqtac.
Qed.

Definition check_product_parameters :=
  ('onStem1 get_equal_parameters) 'C get_product_parameters.

Lemma check_product_parameters_some : forall U,
  check_product_parameters @
    (Fk ('S2 ['I, 'K1 U]) ('K1 U)) ==> ('S1 U).
Proof.
  intros U; unfold check_product_parameters.
  evaluate.
  - apply get_product_parameters_some.
  - evaluate; apply get_equal_parameters_some.
Qed.

Lemma check_product_parameters_inv : forall X U,
  check_product_parameters @ X ==> ('S1 U) ->
  X = Fk ('S2 ['I, 'K1 U]) ('K1 U).
Proof.
  intros X U H; unfold check_product_parameters in H.
  invert_eval.
  apply get_equal_parameters_inv in H5; subst v0.
  apply get_product_parameters_inv in H4.
  exact H4.
Qed.

Lemma type_app_fst_product : forall AI A B,
  type_app AI @ 'fst @r (A '* B) ==> Sm A.
Proof.
  intros AI A B.
  new_S. discriminate.
  new_S. discriminate.
  eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  eapply type_app_K_ev.
  eapply type_app_K_ev.
  new_S. discriminate.
  new_S. discriminate.
  eapply type_app_I.
  eapply type_app_K_ev.
  eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  eapply type_app_K_ev.
  eapply type_app_K_ev.
Qed.

Lemma type_app_snd_product : forall AI A B,
  type_app AI @ 'snd @r (A '* B) ==> Sm B.
Proof.
  intros AI A B.
  new_S. discriminate.
  new_S. discriminate.
  eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  eapply type_app_K_ev.
  eapply type_app_K_ev.
  new_S. discriminate.
  new_S. discriminate.
  eapply type_app_I.
  eapply type_app_K_ev.
  eapply type_app_K_ev.
  eapply type_app_K_ev.
  eapply type_app_I.
Qed.

Lemma infer_product_value : forall AI x y X Y,
  infer AI @ x ==> Sm X ->
  infer AI @ y ==> Sm Y ->
  infer AI @ (x '* y) ==> Sm (X '* Y).
Proof. intros; infer_tac. Qed.


(** Recognition of swap and wrapper values, independent of typing. *)
Local Opaque equal1 get_K1 get_S_fields.


(** Structural triage application, shared by concrete programs and abstract examples. *)
Set Default Proof Using "Type".
Local Opaque app equal equal1.
Local Ltac structural_run := first [eassumption | apply equal_eval | apply equal1_eq |
 evaluate_expr_core structural_run structural_structural_run_head | idtac]
with structural_structural_run_head := first [eassumption | apply equal_eval | apply equal1_eq |
 evaluate_head_core structural_run | idtac].
Lemma structural_leaf : forall AI F0 F1 F2,
 (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
 app AI @ 'triage[F0,F1,F2] @r Lf ==> Sm F0.
Proof.
 intros AI F0 F1 F2 HP; apply app_triage_structural.
 pose proof (get_tagged_none _ HP); unfold structural_triage, plain_triage, error_triage; apply wait_eval; structural_run.
Qed.
Lemma structural_stem : forall AI F0 F1 F2 N V,
 (forall E name, Fk F0 F1 <> 'tagged[E,name]) ->
 app AI @ F1 @r N ==> Sm V ->
 app AI @ 'triage[F0,F1,F2] @r Sm N ==> Sm V.
Proof.
 intros AI F0 F1 F2 N V HP HA; apply app_triage_structural.
 pose proof (get_tagged_none _ HP); inv_out HA.
 unfold structural_triage, plain_triage, error_triage; apply wait_eval; structural_run.
Qed.

Definition type_app_structural_triage_leaf := structural_leaf.

Definition type_app_structural_triage_stem := structural_stem.


Unset Default Proof Using.
Transparent equal get_K1 equal1 get_S_fields app.

(**********************************************************************)
(* The Boolean family.                                                *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness families.

Set Default Proof Using "Type".
Open Scope nat_scope.
Open Scope string_scope.

Opaque equal.

(** Bool # (U * U) ==> Sm U *)

Definition bool_product_matcher :=
  ('onStem1 check_product_parameters) 'C get_S_fields.

Lemma bool_product_matcher_some : forall U,
  bool_product_matcher @ (U '* U) ==> ('S1 U).
Proof.
  intros U; unfold bool_product_matcher.
  evaluate.
  - apply get_S_fields_some.
  - evaluate; apply check_product_parameters_some.
Qed.

Lemma bool_product_matcher_inv : forall X U,
  bool_product_matcher @ X ==> ('S1 U) ->
  X = U '* U.
Proof.
  intros X U H; unfold bool_product_matcher in H.
  invert_eval.
  apply check_product_parameters_inv in H5; subst v0.
  apply get_S_fields_inv in H4.
  exact H4.
Qed.

(** The Boolean elimination program: [U '* U] gives [Sm U]. *)
Definition bool_elim0 :=
  ('onStem1 'I) 'C bool_product_matcher.
Definition bool_eliminator := 'K1 bool_elim0.

Lemma bool_eliminator_some : forall a U,
  bool_eliminator @ a @r (U '* U) ==> Sm U.
Proof.
  intros a U; unfold bool_eliminator, bool_elim0.
  evaluate.
  - apply bool_product_matcher_some.
  - evaluate.
Qed.

Lemma bool_eliminator_inv : forall a V U,
  bool_eliminator @ a @r V ==> Sm U ->
  V = U '* U.
Proof.
  intros a V U H; unfold bool_eliminator, bool_elim0 in H.
  invert_eval.
  match goal with
  | Hmatch : bool_product_matcher @ V ==> ('S1 U) |- _ =>
      exact (bool_product_matcher_inv V U Hmatch)
  end.
Qed.

Opaque equal1.

(** The abstractor maps exactly the carriers ['fst] and ['snd] to the
    eliminator [bool_eliminator]. *)
Definition bool_abstractor :=
  Eval cbv -[equal1] in
    to_tree
      (star "C"
        (Val (equal1 'fst) @@ Ref "C"
           @@ Val (Sm bool_eliminator)
           @@ (Val (equal1 'snd) @@ Ref "C"
                 @@ Val (Sm bool_eliminator)
                 @@ Val Lf))).

Definition bool_nm := Sm (Sm (Sm (Sm Lf))).

Notation "'Bool" := ('tagged[bool_eliminator, bool_nm]) (at level 0).
Notation "'tt" := 'tagged['fst, bool_nm].
Notation "'ff" := 'tagged['snd, bool_nm].

Lemma bool_abstractor_fst :
  bool_abstractor @ 'fst ==> Sm bool_eliminator.
Proof.
  unfold bool_abstractor; evaluate.
  evaluate.
  eapply equal1_eq.
  evaluate.
  eapply equal1_neq; discriminate.
  evaluate.
  evaluate.
  evaluate.
Qed.

Lemma bool_abstractor_snd :
  bool_abstractor @ 'snd ==> Sm bool_eliminator.
Proof.
  unfold bool_abstractor; evaluate.
  evaluate.
  eapply equal1_neq; discriminate.
  evaluate.
  eapply equal1_eq.
  evaluate.
  evaluate.
  evaluate.
Qed.

Lemma bool_abstractor_none : forall C,
  'fst <> C -> 'snd <> C ->
  bool_abstractor @ C ==> Lf.
Proof.
  intros C Hfst Hsnd.
  unfold bool_abstractor; evaluate.
  evaluate.
  eapply equal1_neq; exact Hfst.
  evaluate.
  eapply equal1_neq; exact Hsnd.
  evaluate.
  evaluate.
  evaluate.
Qed.

Lemma bool_abstractor_inv : forall C R,
  bool_abstractor @ C ==> Sm R ->
  R = bool_eliminator /\ (C = 'fst \/ C = 'snd).
Proof.
  intros C R H.
  destruct (combination_eq_dec C 'fst) as [-> | Hfst].
  - pose proof (eval_deterministic _ _ H _ bool_abstractor_fst) as HX.
    inversion HX; auto.
  - destruct (combination_eq_dec C 'snd) as [-> | Hsnd].
    + pose proof (eval_deterministic _ _ H _ bool_abstractor_snd) as HX.
      inversion HX; auto.
    + pose proof (eval_deterministic _ _ H _
        (bool_abstractor_none C (not_eq_sym Hfst) (not_eq_sym Hsnd))).
      discriminate.
Qed.

Opaque bool_eliminator.

(** Type application to a Boolean carrier. *)
Lemma bool_carrier_type_app : forall AI C U,
  C = 'fst \/ C = 'snd -> type_app AI @ C @r (U '* U) ==> Sm U.
Proof.
  intros AI C U [-> | ->]; [apply type_app_fst_product | apply type_app_snd_product].
Qed.

Lemma bool_abstractor_sound : forall AI C E U V,
  bool_abstractor @ C ==> Sm E ->
  E @ type_app AI @r U ==> Sm V ->
  type_app AI @ C @r U ==> Sm V.
Proof.
  intros AI C E U V Hconstructor Heliminate.
  destruct (bool_abstractor_inv C E Hconstructor) as [-> HC].
  apply bool_eliminator_inv in Heliminate; subst U.
  apply bool_carrier_type_app; exact HC.
Qed.


Definition supports_booleans declarations :=
  declarations @ bool_nm ==> ('K1 bool_abstractor).

Definition bool_case_package :
  { t : Combination |
    to_tree (tcase (Val bool_nm) (Val ('K1 bool_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition bool_case :=
  Eval cbn in proj1_sig bool_case_package.

Lemma bool_case_compilation :
  to_tree (tcase (Val bool_nm) (Val ('K1 bool_abstractor))) = bool_case.
Proof. unfold bool_case; exact (proj2_sig bool_case_package). Qed.

Lemma bool_case_some : bool_case @ bool_nm ==> Sm ('K1 bool_abstractor).
Proof. rewrite <- bool_case_compilation; apply tcase_eq. Qed.


(** The Boolean clause declares the Boolean family at [bool_nm]. *)
Lemma bool_case_registers :
  clause_registers bool_case bool_nm ('K1 bool_abstractor).
Proof. rewrite <- bool_case_compilation; apply tcase_registers. Qed.


Definition bool_ontology := extend bool_case function_ontology.

Lemma bool_ontology_supports_booleans : supports_booleans bool_ontology.
Proof.
  unfold supports_booleans, bool_ontology.
  eapply extend_some; apply bool_case_some.
Qed.


Lemma bool_abstractor_supported : forall AI a C E,
  supports_booleans AI ->
  bool_abstractor @ C ==> Sm E ->
  AI @ bool_nm @r a @r C ==> Sm E.
Proof.
  intros AI a C E Hsupports Hconstructor.
  eapply declaration_apply; [exact Hsupports | exact Hconstructor].
Qed.

Lemma fst_infer : forall declarations : Combination,
  infer declarations @ 'fst ==> Sm 'fst.
Proof. intro declarations; eapply infer_tag_free; repeat constructor; intros; discriminate. Qed.

Lemma snd_infer : forall declarations : Combination,
  infer declarations @ 'snd ==> Sm 'snd.
Proof. intro declarations; eapply infer_tag_free; repeat constructor; intros; discriminate. Qed.

Lemma tt_infer : forall declarations : Combination,
  supports_booleans declarations ->
  infer declarations @ 'tt ==> Sm ('Bool).
Proof.
  intros declarations Hsupports.
  eapply infer_tagged.
  - exact (fst_infer declarations).
  - eapply infer_tag_free; repeat constructor; intros; discriminate.
  - eapply bool_abstractor_supported.
    + exact Hsupports.
    + apply bool_abstractor_fst.
Qed.

Lemma ff_infer : forall declarations : Combination,
  supports_booleans declarations ->
  infer declarations @ 'ff ==> Sm ('Bool).
Proof.
  intros declarations Hsupports.
  eapply infer_tagged.
  - exact (snd_infer declarations).
  - eapply infer_tag_free; repeat constructor; intros; discriminate.
  - eapply bool_abstractor_supported.
    + exact Hsupports.
    + apply bool_abstractor_snd.
Qed.

(** Raw Boolean negation [neg] and its inferred applicative type. *)
Local Definition neg_package :
  { t | to_tree (\"b1" (Ref "b1" @@ (Val 'ff ''* Val 'tt))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition neg :=
  Eval cbn in proj1_sig neg_package.

Lemma neg_tt : neg @ 'tt ==> 'ff.
Proof. cbv; evaluate. Qed.


Definition Neg : Combination :=
  'S2 ['I, 'K1 ('Bool '* 'Bool)].

Local Ltac boolean_type_step :=
  first
    [ eassumption
    | eapply tt_infer; eassumption
    | eapply ff_infer; eassumption
    | eapply infer_fork
    | eapply infer_stem
    | eapply infer_leaf
    | eapply infer_I
    | eapply type_app_I
    | eapply type_app_leaf_ev
    | eapply type_app_K_ev
    | eapply type_app_abstract
    | eapply type_app_compose; [solve [reject_name]| | |]; [solve [intros E N H; inversion H] |]
    | new_S; [solve [intros E N H; inversion H] |]
    | eapply type_app_stem_ev; eapply type_app_stem_tagged;
      eapply bool_abstractor_supported;
      [eassumption |
       first [apply bool_abstractor_fst | apply bool_abstractor_snd]]
    | eapply type_app_stem_ev; eapply type_app_stem_structural;
      solve [intros E N H; inversion H]
    ].

Lemma neg_infer : forall declarations : Combination,
  supports_booleans declarations ->
  infer declarations @ neg ==> Sm Neg.
Proof.
  intros declarations Hsupports.
  unfold neg, Neg.
  repeat boolean_type_step.
Qed.

Lemma neg_type_app : forall declarations : Combination,
  type_app declarations @ Neg @r ('Bool) ==> Sm ('Bool).
Proof.
  intro declarations.
  unfold Neg.
  new_S.
  - intros; discriminate.
  - eapply type_app_I.
  - eapply type_app_K_ev.
  - eapply type_app_abstract.
    eapply bool_eliminator_some.
Qed.


Unset Default Proof Using.
Transparent equal get_K1 equal1 get_S_fields app.

(**********************************************************************)
(* Totality of the Boolean eliminator.                                *)
(**********************************************************************)

(** Type application of [Bool] returns Lf on every argument type other
    than the one of [bool_eliminator_some] (Bool # (U * U) ==> Sm U): this
    is [bool_eliminator_none].

    The proof follows the composition structure of [bool_eliminator]:
    each matcher ([get_S_fields], [get_product_parameters],
    [get_equal_parameters]) answers [Lf] when its argument has the wrong
    shape, and every stage passes a leaf through unchanged. *)

From TreeTyping Require Import tree.

Set Default Proof Using "Type".

(** ** Failure of the individual matchers *)

Lemma get_S_fields_none : forall X,
  (forall G F, X <> 'S2[G, F]) -> get_S_fields @ X ==> Lf.
Proof.
  intros X Hnone; destruct X as [| X | L R].
  - unfold get_S_fields; evaluate.
  - unfold get_S_fields; evaluate.
  - destruct L as [| L | L1 L2].
    + unfold get_S_fields; evaluate.
    + exfalso; exact (Hnone L R eq_refl).
    + unfold get_S_fields; evaluate.
Qed.

(** Every mismatch of the product-parameter pattern is found by direct
    evaluation once the argument is exposed to the depth of the pattern. *)
Ltac gpp_fail :=
  solve [unfold get_product_parameters; cbn [equal1]; evaluate].

Lemma get_product_parameters_none : forall X,
  (forall U1 U2, X <> Fk ('S2 ['I, 'K1 U1]) ('K1 U2)) ->
  get_product_parameters @ X ==> Lf.
Proof.
  intros X Hnone.
  destruct X as [| X | L R]; try gpp_fail.
  destruct L as [| L | L1 L2]; try gpp_fail.
  destruct L1 as [| M | L1a L1b]; try gpp_fail.
  destruct M as [| M | M1 M2]; try gpp_fail.
  destruct M1 as [| a | M1a M1b]; try gpp_fail.
  destruct a as [| a | aa ab]; try gpp_fail.
  destruct a as [| a | aa ab]; try gpp_fail.
  destruct M2 as [| b | M2a M2b]; try gpp_fail.
  destruct b as [| b | ba bb]; try gpp_fail.
  destruct L2 as [| c | c U1]; try gpp_fail.
  destruct c as [| c | ca cb]; try gpp_fail.
  destruct R as [| d | d U2]; try gpp_fail.
  destruct d as [| d | da db]; try gpp_fail.
  exfalso; exact (Hnone U1 U2 eq_refl).
Qed.

Lemma get_equal_parameters_neq : forall U1 U2,
  U1 <> U2 -> get_equal_parameters @ (Fk U1 U2) ==> Lf.
Proof.
  intros U1 U2 Hneq; unfold get_equal_parameters.
  evaluate.
  eapply equal_eval.
  unfold get_equal_parameters_continuation; evaluate; evaluate.
  evaluate.
  evaluate.
  eapply equal1_neq; exact Hneq.
  evaluate.
  evaluate.
Qed.

(** ** Shape decisions *)

Lemma S2_decide : forall X,
  (exists G F, X = 'S2[G, F]) \/ (forall G F, X <> 'S2[G, F]).
Proof.
  intro X; destruct X as [| X | L R];
    try (right; intros G F H; discriminate H).
  destruct L as [| G | L1 L2];
    try (right; intros G F H; discriminate H).
  left; exists G, R; reflexivity.
Qed.

Lemma product_parameters_decide : forall X,
  (exists U1 U2, X = Fk ('S2 ['I, 'K1 U1]) ('K1 U2)) \/
  (forall U1 U2, X <> Fk ('S2 ['I, 'K1 U1]) ('K1 U2)).
Proof.
  intro X; destruct X as [| X | L R];
    try (right; intros U1 U2 H; discriminate H).
  destruct L as [| L | A B];
    try (right; intros U1 U2 H; discriminate H).
  assert (HA : A = Sm 'I \/ A <> Sm 'I) by (repeat decide equality).
  destruct HA as [-> | HA];
    [| right; intros U1 U2 H; inversion H; congruence].
  destruct B as [| B | B1 U1];
    try (right; intros U1 U2 H; discriminate H).
  destruct B1 as [| B1 | B11 B12];
    try (right; intros U1' U2 H; discriminate H).
  destruct R as [| R | R1 U2];
    try (right; intros U1' U2 H; discriminate H).
  destruct R1 as [| R1 | R11 R12];
    try (right; intros U1' U2' H; discriminate H).
  left; exists U1, U2; reflexivity.
Qed.

(** ** Failure of the composed matchers *)

Lemma check_product_parameters_none : forall X,
  (forall U, X <> Fk ('S2 ['I, 'K1 U]) ('K1 U)) ->
  check_product_parameters @ X ==> Lf.
Proof.
  intros X Hnone; unfold check_product_parameters.
  destruct (product_parameters_decide X) as [[U1 [U2 ->]] | Hshape].
  - assert (Hneq : U1 <> U2)
      by (intros ->; exact (Hnone U2 eq_refl)).
    evaluate.
    + apply get_product_parameters_some.
    + evaluate; apply get_equal_parameters_neq; exact Hneq.
  - evaluate.
    + apply get_product_parameters_none; exact Hshape.
    + evaluate.
Qed.

Lemma bool_product_matcher_none : forall V,
  (forall U, V <> U '* U) -> bool_product_matcher @ V ==> Lf.
Proof.
  intros V Hnone; unfold bool_product_matcher.
  destruct (S2_decide V) as [[G [F ->]] | Hshape].
  - evaluate.
    + apply get_S_fields_some.
    + evaluate; apply check_product_parameters_none.
      intros U Heq; inversion Heq; subst G F.
      exact (Hnone U eq_refl).
  - evaluate.
    + apply get_S_fields_none; exact Hshape.
    + evaluate.
Qed.

Local Transparent bool_eliminator.
Lemma bool_eliminator_none : forall a V,
  (forall U, V <> U '* U) -> bool_eliminator @ a @r V ==> Lf.
Proof.
  intros a V Hnone; unfold bool_eliminator, bool_elim0.
  evaluate.
  - apply bool_product_matcher_none; exact Hnone.
  - evaluate.
Qed.
Local Opaque bool_eliminator.

(* ================================================================== *)
(* The abstract type Bool has no type *)
(* ================================================================== *)
Unset Default Proof Using.
Set Default Proof Using "Type".

(** The type [Bool] is itself an abstract type [tagged[bool_eliminator,bool_nm]].
    Its eliminator is not the concrete type of either selector, so boolean
    introduction rejects it, and [Bool] has no type under any declarations that
    supports booleans (in particular [bool_ontology] and [paper_ontology]). *)
Lemma bool_nm_tag_free : tag_free bool_nm = true.
Proof. vm_compute; reflexivity. Qed.

Local Transparent bool_eliminator.
Lemma bool_eliminator_tag_free : tag_free bool_eliminator = true.
Proof. vm_compute; reflexivity. Qed.
Lemma bool_eliminator_not_fst : bool_eliminator <> 'fst.
Proof. vm_compute; discriminate. Qed.
Lemma bool_eliminator_not_snd : bool_eliminator <> 'snd.
Proof. vm_compute; discriminate. Qed.
Local Opaque bool_eliminator.

Lemma Bool_untypable : forall AI R,
  supports_booleans AI -> ~ (infer AI @ ('Bool) ==> Sm R).
Proof.
  intros AI R HB H.
  destruct (infer_tagged_source_inv AI _ _ _ H)
    as [C [N [E [_ [HC [HN HI]]]]]].
  assert (Ceq : Sm C = Sm bool_eliminator)
    by (eapply eval_deterministic; [exact HC|
        apply infer_tag_free; apply bool_eliminator_tag_free]).
  assert (Neq : Sm N = Sm bool_nm)
    by (eapply eval_deterministic; [exact HN|
        apply infer_tag_free; apply bool_nm_tag_free]).
  inversion Ceq; inversion Neq; subst C N; clear Ceq Neq.
  pose proof (declaration_K1_inv _ _ _ _ _ _ HB HI) as HR0.
  destruct (bool_abstractor_inv _ _ HR0) as [_ [Hf|Hs]].
  - exact (bool_eliminator_not_fst Hf).
  - exact (bool_eliminator_not_snd Hs).
Qed.

(** One-round soundness of the declarations. *)
Lemma plain_bool_cond2 : forall AI, abstractor_sound_by_typing AI bool_abstractor.
Proof. intros AI; exact (bool_abstractor_sound AI). Qed.

(** The Boolean declarations are sound by typing. *)
Lemma bool_ontology_row : bool_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold bool_ontology; apply extend_none_value; [|apply function_ontology_row].
  rewrite <- bool_case_compilation; apply tcase_neq; unfold bool_nm, fun_nm; discriminate.
Qed.
Canonical Structure bool_decl := mkDecl bool_ontology bool_ontology_row.

Lemma bool_ontology_sound_by_typing : ontology_sound_by_typing bool_ontology.
Proof.
  apply plain_ontology_sound_by_typing.
  change (plain_intro_sound_for (extend bool_case function_ontology) (dtree bool_decl)).
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ bool_case_compilation)
    |eapply plain_declared_sound_for; [apply bool_case_registers|apply plain_bool_cond2]|].
  apply plain_extend_intro_sound_for;
    [apply function_case_never_fork|apply plain_function_declared_sound_for|].
  apply plain_empty_ontology_sound_for.
Qed.
