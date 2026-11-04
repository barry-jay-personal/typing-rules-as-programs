(** * Data types (paper: Abstract Types).

    Natural numbers, options, sums and lists. *)


(**********************************************************************)
(* Natural numbers as folds.                                          *)
(**********************************************************************)

(** Numbers are folds: [succ n @ (u * f) = f @ (n @ (u * f))].  So Nat
    eliminates a pair of type U * F, returning U, when F # U ==> Sm U: the
    recursion is in the data and typing checks one step, by type
    application. *)

From Stdlib Require Import String Lia.
From TreeTyping Require Import tree typing soundness families booleans.
From TreeTyping Require Import booleans functions.

Set Default Proof Using "Type".
Open Scope string_scope.
Opaque equal.

Definition nat_nm := Sm (Sm (Sm (Sm (Sm Lf)))).

(** Given type application, the type [U] of the base and the type [F] of
    the step, check that the step takes [U] to [U] and return [Sm U]. *)
Definition nat_step_check :=
  Eval cbn in to_tree
    (star "a" (star "U" (star "F"
      (''onStem1 (star "V" (Val equal @@ Ref "V" @@ Ref "U" @@ (Val Lf @@ Ref "U") @@ Val Lf))
        @@ (Ref "a" @@ Ref "F" @@ Ref "U"))))).

Local Ltac d_atom0 :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else first [ eassumption | apply equal_eval | apply equal1_eq ]
  end.
Local Ltac d_eval0 :=
  first [ d_atom0 | evaluate_expr_core d_eval0 d_head0 | idtac ]
with d_head0 :=
  first [ d_atom0 | evaluate_head_core d_eval0 | idtac ].

Lemma nat_step_check_eval : forall a U F,
  a @ F @r U ==> Sm U -> nat_step_check @ a @r U @r F ==> Sm U.
Proof.
  intros a U F H; inv_out H.
  unfold nat_step_check; cbn; d_eval0.
Qed.

Lemma nat_step_check_inv : forall a A F U,
  nat_step_check @ a @r A @r F ==> Sm U ->
  A = U /\ a @ F @r U ==> Sm U.
Proof.
  intros a A F U H; unfold nat_step_check in H; cbn in H.
  inv_out H; invert_eval.
  all: match goal with
  | H1 : equal @ ?V ==> ?e, H2 : ?e @ ?W ==> ?b |- _ =>
    assert (Hequal : equal @ V @r W ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ Hequal) as [[Hv0 Heq] | [Hv0 Hneq]]; subst b; invert_eval
  end.
  all: subst; split; [reflexivity|]; eapply eval_appl; eassumption.
Qed.

(** The Nat family has no parameters: its parameter is [Lf]. *)
Local Definition nat_core_term a :=
  (''onStem1
    (''onStem1
      (''onFork1 (''wait[Val nat_step_check, a]))
      ''C Val get_product_parameters)
    ''C Val get_S_fields).
Definition nat_elim_package :
  {t : Combination | to_tree (star "X" (star "a" (nat_core_term (Ref "a")))) = t}.
Proof. eexists; cbn; reflexivity. Defined.
Definition nat_elim : Combination := Eval cbn in proj1_sig nat_elim_package.

Definition nat_eliminator := 'wait[nat_elim, Lf].

Notation "'Nat" := ('tagged[nat_eliminator,nat_nm]) (at level 0).

Definition zero := 'tagged['fst,nat_nm].
Definition succ (n : Combination) :=
  'tagged['S2['snd,n],nat_nm].

Local Definition nat_core a :=
  ('onStem1 ('onStem1 ('onFork1 ('wait[nat_step_check, a]))
    'C get_product_parameters)) 'C get_S_fields.
Local Lemma nat_eliminator_head : forall a,
  nat_eliminator @ a ==> nat_core a.
Proof.
  intros; unfold nat_eliminator; apply wait_eval.
  unfold nat_elim, nat_core; cbn; evaluate.
Qed.

Lemma nat_eliminator_app : forall a T V,
  nat_eliminator @ a @r T ==> V <-> nat_core a @ T ==> V.
Proof.
  intros a T V; split; intro H.
  - destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hwu]]]]; inv_out Hu.
    pose proof (eval_deterministic _ _ Hw _ (nat_eliminator_head a)); subst w.
    exact Hwu.
  - eapply eval_appl; [apply nat_eliminator_head | exact H].
Qed.

Lemma nat_core_eval : forall a U F,
  a @ F @r U ==> Sm U -> nat_core a @ (U '* F) ==> Sm U.
Proof.
  intros a U F Hs; pose proof (nat_step_check_eval a U F Hs) as Hcheck.
  inv_out Hcheck.
  match goal with H : nat_step_check @ _ @r _ ==> _ |- _ => inv_out H end.
  unfold nat_core.
  repeat first [eassumption | apply get_S_fields_some |
    apply get_product_parameters_some | progress evaluate].
Qed.

Lemma nat_core_inv : forall a X U,
  nat_core a @ X ==> Sm U -> exists F, X = U '* F /\ a @ F @r U ==> Sm U.
Proof.
  intros a X U H; unfold nat_core in H; invert_eval.
  match goal with
  | H1 : nat_step_check @ ?m ==> ?f, H2 : ?f @ ?b ==> ?g,
    H3 : ?g @ ?c ==> Sm U |- _ =>
      assert (Hcheck : nat_step_check @ m @r b @r c ==> Sm U)
        by (repeat (eapply eval_appl; eauto))
  end.
  apply nat_step_check_inv in Hcheck; destruct Hcheck as [-> HF].
  match goal with H : get_product_parameters @ _ ==> Sm (Fk _ _) |- _ =>
    apply get_product_parameters_inv in H; subst end.
  match goal with H : get_S_fields @ _ ==> Sm _ |- _ =>
    apply get_S_fields_inv in H; subst end.
  eexists; split; [reflexivity|exact HF].
Qed.

Lemma nat_eliminator_eval : forall a U F,
  a @ F @r U ==> Sm U -> nat_eliminator @ a @r (U '* F) ==> Sm U.
Proof. intros; apply nat_eliminator_app; apply nat_core_eval; assumption. Qed.

Lemma type_app_Nat : forall AI U F,
  type_app AI @ F @r U ==> Sm U ->
  type_app AI @ ('Nat) @r (U '* F) ==> Sm U.
Proof.
  intros AI U F H; eapply type_app_abstract.
  apply nat_eliminator_eval; exact H.
Qed.

Lemma nat_eliminator_inv : forall a X U,
  nat_eliminator @ a @r X ==> Sm U ->
  exists F, X = U '* F /\ a @ F @r U ==> Sm U.
Proof. intros a X U H; apply nat_eliminator_app, nat_core_inv in H; exact H. Qed.

(** The abstractor maps exactly the carriers ['fst] (zero) and
    ['S2['snd,'Nat]] (successor) to the eliminator [nat_eliminator].
    The successor carrier mentions [Nat], whose label must stay out of
    the declarations, so it is rebuilt at run time and compared. *)
Definition nat_type_mk := 'S2['K1 ('tagger[nat_nm]), 'K1 nat_eliminator].
Definition nat_succ_carrier := 'S2['snd,'Nat].
Definition nat_abstractor := Eval cbn -[equal nat_eliminator] in to_tree
  (star "C" ((star "q" (star "e"
      (Ref "q" @@ Val 'fst @@ (Val Lf @@ Ref "e")
        @@ (Ref "q" @@ ''S2[Val 'snd, Val ('tagger[nat_nm]) @@ Ref "e"]
          @@ (Val Lf @@ Ref "e") @@ Val Lf))))
    @@ (op equal @@ Ref "C") @@ Val nat_eliminator)).

Lemma nat_type_mk_eval : forall C, nat_type_mk @ C ==> 'Nat.
Proof. intros; unfold nat_type_mk; evaluate. Qed.

Lemma nat_abstractor_eval : forall C, nat_abstractor @ C ==>
  (if ceqb C 'fst then Sm nat_eliminator
   else if ceqb C nat_succ_carrier then Sm nat_eliminator else Lf).
Proof.
  intro C; pose proof (equal_eval C) as H0.
  destruct (equal1_bt_case C 'fst) as [[_ [E1 H1]]|[_ [E1 H1]]];
  destruct (equal1_bt_case C nat_succ_carrier) as [[_ [E2 H2]]|[_ [E2 H2]]];
  rewrite E1; try rewrite E2; unfold nat_succ_carrier in *; unfold nat_abstractor; d_eval0.
Qed.

Lemma nat_abstractor_zero :
  nat_abstractor @ 'fst ==> Sm nat_eliminator.
Proof. pose proof (nat_abstractor_eval 'fst) as H; rewrite ceqb_refl in H; exact H. Qed.

Lemma nat_abstractor_succ :
  nat_abstractor @ ('S2['snd,'Nat]) ==>
    Sm nat_eliminator.
Proof.
  pose proof (nat_abstractor_eval nat_succ_carrier) as H.
  rewrite ceqb_false in H; [|discriminate].
  rewrite ceqb_refl in H; exact H.
Qed.

Lemma nat_abstractor_inv : forall C E,
  nat_abstractor @ C ==> Sm E ->
  E = nat_eliminator /\
    (C = 'fst \/ C = 'S2['snd,'Nat]).
Proof.
  intros C X H; pose proof (eval_deterministic _ _ H _ (nat_abstractor_eval C)) as HE.
  destruct (ceqb C 'fst) eqn:E1.
  - apply ceqb_true in E1; inversion HE; auto.
  - destruct (ceqb C nat_succ_carrier) eqn:E2; [|discriminate].
    apply ceqb_true in E2; inversion HE; auto.
Qed.

Definition supports_number AI := AI @ nat_nm ==> ('K1 (nat_abstractor)).

Lemma nat_abstractor_supported : forall AI a C E,
  supports_number AI ->
  nat_abstractor @ C ==> Sm E ->
  AI @ nat_nm @r a @r C ==> Sm E.
Proof.
  intros AI a C E Hsupports Hconstructor.
  eapply declaration_apply; [exact Hsupports | exact Hconstructor].
Qed.

Lemma nat_is_data : forall declarations C,
  supports_number declarations ->
  infer declarations @ C ==> Sm ('Nat) ->
  C = zero \/
    exists n, C = succ n /\ infer declarations @ n ==> Sm ('Nat).
Proof.
  intros declarations C Hsupport Hinfer.
  destruct (infer_tagged_result_inv declarations C nat_eliminator nat_nm
    Hinfer)
    as [c [n [F [-> [Hc [Hn Hdispatch]]]]]].
  assert (Hconstructor : nat_abstractor @ F ==> Sm nat_eliminator).
  { exact (declaration_K1_inv _ _ _ _ _ _ Hsupport Hdispatch). }

  destruct (nat_abstractor_inv F nat_eliminator Hconstructor)
    as [_ [HF | HF]]; subst F.
  - assert (c = 'fst)
      by (eapply infer_tag_free_inv; eauto; tag_free_tac); subst c.
    assert (n = nat_nm)
      by (eapply infer_tag_free_inv; eauto; tag_free_tac); subst n.
    left; reflexivity.
  - destruct (infer_S2_inv declarations c 'snd ('Nat) ltac:(intros; discriminate) Hc)
      as [g [m [-> [Hg Hm]]]].
    assert (g = 'snd)
      by (eapply infer_tag_free_inv; eauto; tag_free_tac); subst g.
    assert (n = nat_nm)
      by (eapply infer_tag_free_inv; eauto; tag_free_tac); subst n.
    right; exists m; split; [reflexivity | exact Hm].
Qed.

(** Type application to a Nat carrier. *)
Lemma nat_carrier_type_app : forall AI C U F,
  C = 'fst \/ C = 'S2['snd,'Nat] ->
  type_app AI @ F @r U ==> Sm U ->
  type_app AI @ C @r (U '* F) ==> Sm U.
Proof.
  intros AI C U F [-> | ->] H.
  - apply type_app_fst_product.
  - new_S.
    + discriminate.
    + apply type_app_snd_product.
    + apply type_app_Nat; exact H.
    + exact H.
Qed.

Lemma nat_abstractor_sound : forall AI C E X U,
  nat_abstractor @ C ==> Sm E ->
  E @ type_app AI @r X ==> Sm U ->
  type_app AI @ C @r X ==> Sm U.
Proof.
  intros AI C E X U Hconstructor Heliminate.
  destruct (nat_abstractor_inv C E Hconstructor) as [-> HC].
  apply nat_eliminator_inv in Heliminate; destruct Heliminate as [F [-> HF]].
  apply nat_carrier_type_app; assumption.
Qed.


Definition nat_case_package :
  { t : Combination |
    to_tree (tcase (Val nat_nm) (Val ('K1 nat_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition nat_case := Eval cbn in proj1_sig nat_case_package.

Lemma nat_case_compilation :
  to_tree (tcase (Val nat_nm) (Val ('K1 nat_abstractor))) = nat_case.
Proof. unfold nat_case; exact (proj2_sig nat_case_package). Qed.

Lemma nat_case_some : nat_case @ nat_nm ==> Sm ('K1 nat_abstractor).
Proof. rewrite <- nat_case_compilation; apply tcase_eq. Qed.

Lemma nat_case_none : forall N,
  N <> nat_nm -> nat_case @ N ==> Lf.
Proof.
  intros N Hneq; rewrite <- nat_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.

Definition nat_ontology := extend nat_case bool_ontology.

Lemma nat_ontology_row : nat_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold nat_ontology; apply extend_none_value; [apply nat_case_none; unfold nat_nm, fun_nm; discriminate|exact (functions_declared bool_decl)].
Qed.
Canonical Structure nat_decl := mkDecl nat_ontology nat_ontology_row.

Lemma nat_ontology_supports_number : supports_number nat_ontology.
Proof.
  unfold supports_number, nat_ontology; eapply extend_some; apply nat_case_some.
Qed.

Lemma nat_ontology_supports_booleans : supports_booleans nat_ontology.
Proof.
  unfold supports_booleans, nat_ontology.
  eapply extend_none_value.
  - apply nat_case_none; unfold nat_nm, bool_nm; discriminate.
  - exact bool_ontology_supports_booleans.
Qed.

(** The Nat clause declares the Nat family at [nat_nm]. *)
Lemma nat_case_registers :
  clause_registers nat_case nat_nm ('K1 nat_abstractor).
Proof. rewrite <- nat_case_compilation; apply tcase_registers. Qed.


Section NumberExamples.

Set Default Proof Using "All".
Variable AI : Combination.
Hypothesis AI_supports_number : supports_number AI.
Local Abbreviation ontology_3 := AI.

Lemma infer_nat_nm : infer ontology_3 @ nat_nm ==> Sm nat_nm.
Proof.
  unfold nat_nm; eapply infer_tag_free;
    repeat constructor; intros; discriminate.
Qed.

Lemma infer_zero : infer ontology_3 @ zero ==> Sm ('Nat).
Proof.
  unfold zero.
  eapply infer_tagged.
  - eapply infer_tag_free; repeat constructor; intros; discriminate.
  - exact infer_nat_nm.
  - eapply nat_abstractor_supported.
    + exact AI_supports_number.
    + apply nat_abstractor_zero.
Qed.

Lemma infer_succ : forall n,
  infer ontology_3 @ n ==> Sm ('Nat) ->
  infer ontology_3 @ succ n ==> Sm ('Nat).
Proof.
  intros n Hn; unfold succ.
  eapply infer_tagged.
  - infer_tac.
    all: try exact Hn.
    all: eapply infer_tag_free; repeat constructor; intros; discriminate.
  - exact infer_nat_nm.
  - eapply nat_abstractor_supported.
    + exact AI_supports_number.
    + apply nat_abstractor_succ.
Qed.

Definition one := succ zero.
Definition two := succ one.

Lemma infer_one : infer ontology_3 @ one ==> Sm ('Nat).
Proof.
  unfold one.
  apply infer_succ; exact infer_zero.
Qed.

Lemma infer_two : infer ontology_3 @ two ==> Sm ('Nat).
Proof.
  unfold two.
  apply infer_succ; exact infer_one.
Qed.


End NumberExamples.
Set Default Proof Using "Type".

(** * Numerals, predecessor and comparison *)
Fixpoint numeral (n : nat) : Combination :=
  match n with O => zero | S k => succ (numeral k) end.
Lemma numeral_typed : forall AI n,
  supports_number AI -> infer AI @ numeral n ==> Sm ('Nat).
Proof. intros AI n HN; induction n; cbn; [apply infer_zero | apply infer_succ]; assumption. Qed.

(** Programs build numbers at run time, so that they stay tag-free. *)
Definition mk_succ := ('tagger[nat_nm]) 'C (Lf 'C ('K1 'snd)).
Definition mk_zero := ('tagger[nat_nm]) 'C ('K1 'fst).
Lemma mk_zero_eval : forall x, mk_zero @ x ==> zero.
Proof. intros; unfold mk_zero, zero; evaluate. Qed.

(** The predecessor is a fold over pairs. *)
Definition nat_shift := Eval cbn in to_tree
  (star "p" ((Val 'snd @@ Ref "p") ''*
     (Val ('tagger[nat_nm]) @@ ''S2[Val 'snd, Val 'snd @@ Ref "p"]))).
Definition nat_pred := Eval cbn in to_tree
  (star "n" (Val 'fst @@ (Ref "n" @@
     (((Val mk_zero @@ Ref "n") ''* (Val mk_zero @@ Ref "n")) ''* Val nat_shift)))).

Lemma nat_shift_eval : forall a b, nat_shift @ (a '* b) ==> (b '* succ b).
Proof. intros; unfold nat_shift, succ; evaluate. Qed.

(** A successor is a fold step. *)
Lemma succ_apply : forall n u f t r,
  n @ (u '* f) ==> t -> f @ t ==> r -> succ n @ (u '* f) ==> r.
Proof.
  intros n u f t r Hn Hf; unfold succ; apply tagged_eval.
  inv_out Hf; d_eval0.
Qed.
Lemma zero_apply : forall u f, zero @ (u '* f) ==> u.
Proof. intros; unfold zero; apply tagged_eval; evaluate. Qed.

Definition pred_num k := match k with O => O | S j => j end.
Lemma numeral_pair_fold : forall k,
  numeral k @ ((zero '* zero) '* nat_shift) ==> (numeral (pred_num k) '* numeral k).
Proof.
  induction k as [|k IH]; cbn [numeral pred_num].
  - apply zero_apply.
  - eapply succ_apply; [exact IH|apply nat_shift_eval].
Qed.
Lemma nat_pred_numeral : forall k, nat_pred @ numeral k ==> numeral (pred_num k).
Proof.
  intros k; pose proof (numeral_pair_fold k) as H.
  pose proof (mk_zero_eval (numeral k)) as Hz.
  unfold nat_pred; repeat first [eassumption | progress evaluate].
Qed.

(** [nat_split @ n @ (u * f)] is [u] at zero and [f @ m] at [succ m]: the
    fold selects a function, which is then applied to the predecessor. *)
Definition lam_rt (f u : Term) : Term := Val tagged_fun @@ ''decorate[f,u].
Definition nat_split := Eval cbn -[tagged_fun nat_pred mk_zero] in to_tree
  (star "n" (star "p"
    ((Ref "n" @@ (lam_rt (''K1 (Val 'fst @@ Ref "p")) (Val mk_zero @@ Ref "p")
                  ''* ''K1 (Val 'snd @@ Ref "p")))
     @@ (Val ('K1 nat_pred) @@ Ref "p" @@ Ref "n")))).

Lemma numeral_K1_fold : forall k b f, numeral (S k) @ (b '* ('K1 f)) ==> f.
Proof.
  induction k as [|k IH]; intros b f; cbn [numeral] in *.
  - eapply succ_apply; [apply zero_apply|evaluate].
  - eapply succ_apply; [exact (IH b f)|evaluate].
Qed.

Local Ltac split_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply mk_zero_eval | apply tagged_fun_eval ]
  end.
Local Ltac split_eval :=
  first [ split_atom | evaluate_expr_core split_eval split_head | idtac ]
with split_head :=
  first [ split_atom | evaluate_head_core split_eval | idtac ].

Local Opaque nat_pred mk_zero tagged_fun.
Lemma nat_split_eval : forall n u f s p r,
  n @ (lam ('K1 u) zero '* ('K1 f)) ==> s -> nat_pred @ n ==> p -> s @ p ==> r ->
  nat_split @ n @r (u '* f) ==> r.
Proof.
  intros n u f s p r Hn Hp Hr; unfold lam in Hn; unfold nat_split; split_eval.
Qed.
Local Transparent nat_pred mk_zero tagged_fun.

Lemma nat_split_zero : forall u f, nat_split @ zero @r (u '* f) ==> u.
Proof.
  intros u f; eapply nat_split_eval.
  - apply zero_apply.
  - exact (nat_pred_numeral 0).
  - apply lam_eval; evaluate.
Qed.
Lemma nat_split_succ : forall k u f r,
  f @ numeral k ==> r -> nat_split @ succ (numeral k) @r (u '* f) ==> r.
Proof.
  intros k u f r H; eapply nat_split_eval.
  - apply (numeral_K1_fold k).
  - exact (nat_pred_numeral (S k)).
  - exact H.
Qed.



(** Helpers for programs that split a number, used in recursion.v. *)
Local Opaque nat_pred.
Lemma nat_split_parts : forall n, exists w, nat_split @ n ==> w /\
  (forall P r, w @ P ==> r -> nat_split @ n @r P ==> r) /\
  (forall P r, nat_split @ n @r P ==> r -> w @ P ==> r).
Proof.
  intros n.
  assert (Hw : exists w, nat_split @ n ==> w) by (eexists; unfold nat_split; d_eval0).
  destruct Hw as [w Hw]; exists w; split; [exact Hw|split].
  - intros P r H; eapply eval_appl; eassumption.
  - intros P r H; destruct (eval_app_r_inv _ _ _ H) as [w' [Hw' Hr]].
    pose proof (eval_deterministic _ _ Hw' _ Hw) as ->; exact Hr.
Qed.

Local Opaque nat_split.
Ltac ge_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first
      [ eassumption
      | match goal with
        | Hp : forall P r, nat_split @ ?n @r P ==> r -> ?w @ P ==> r,
          Hq : forall P r, ?w @ P ==> r -> nat_split @ ?n @r P ==> r |- eval (Fk (Sm ?w) _) _ =>
            apply Hp;
            first [ apply nat_split_zero
                  | apply nat_split_succ; apply lam_eval; ge_eval ]
        end ]
  end
with ge_eval :=
  first [ ge_atom | evaluate_expr_core ge_eval ge_head | idtac ]
with ge_head :=
  first [ ge_atom | evaluate_head_core ge_eval | idtac ].




Set Default Proof Using "Type".


Unset Default Proof Using.
Transparent equal.

(**********************************************************************)
(* Witnessed Scott options.                                           *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans.

Set Default Proof Using "Type".
Open Scope string_scope.
Opaque equal.

(** The eliminator of a data type reads the two parts of its argument type
    and passes them to a check. *)
Definition fold_core K :=
  ('onStem1 ('onStem1 ('onFork1 K) 'C get_product_parameters)) 'C get_S_fields.
Lemma fold_core_eval : forall K U F V,
  K @ U @r F ==> V -> fold_core K @ (U '* F) ==> V.
Proof.
  intros K U F V H; inv_out H.
  unfold fold_core.
  repeat first [eassumption | apply get_S_fields_some |
    apply get_product_parameters_some | progress evaluate].
Qed.
Lemma fold_core_inv : forall K X V,
  fold_core K @ X ==> Sm V -> exists U F, X = U '* F /\ K @ U @r F ==> Sm V.
Proof.
  intros K X V H; unfold fold_core in H; invert_eval.
  match goal with H : get_product_parameters @ _ ==> Sm (Fk ?a ?b) |- _ =>
    pose proof H as Hp; apply get_product_parameters_inv in Hp; subst;
    exists a, b end.
  match goal with H : get_S_fields @ _ ==> Sm _ |- _ =>
    apply get_S_fields_inv in H; subst end.
  split; [reflexivity|]; eapply eval_appl; eassumption.
Qed.

(** [Option A # (U * F) ==> Sm U] when [F # A ==> Sm U].
    [none witness] stores its type evidence directly in a decoration. Elimination still
    returns the absent branch; generic queries choose whether to inspect the
    annotation evidence. *)

Definition opt_nm := Sm (Sm (Sm (Sm (Sm (Sm Lf))))).

Definition option_step_check := Eval cbn in to_tree
  (star "A" (star "a" (star "U" (star "F"
    (''onStem1 (star "V" (Val equal @@ Ref "V" @@ Ref "U" @@ (Val Lf @@ Ref "U") @@ Val Lf))
      @@ (Ref "a" @@ Ref "F" @@ Ref "A")))))).

Lemma option_step_check_eval : forall A a U F,
  a @ F @r A ==> Sm U -> option_step_check @ A @r a @r U @r F ==> Sm U.
Proof.
  intros A a U F H; inv_out H.
  unfold option_step_check; cbn; d_eval0.
Qed.
Lemma option_step_check_inv : forall A a B F U,
  option_step_check @ A @r a @r B @r F ==> Sm U ->
  B = U /\ a @ F @r A ==> Sm U.
Proof.
  intros A a B F U H; unfold option_step_check in H; cbn in H.
  inv_out H; invert_eval.
  all: match goal with
  | H1 : equal @ ?V ==> ?e, H2 : ?e @ ?W ==> ?b |- _ =>
    assert (Hequal : equal @ V @r W ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ Hequal) as [[Hv0 Heq] | [Hv0 Hneq]]; subst b; invert_eval
  end.
  all: subst; split; [reflexivity|]; eapply eval_appl; eassumption.
Qed.

Definition option_elim := Eval cbn in to_tree
  (star "A" (star "a"
    (''onStem1
      (''onStem1
        (''onFork1 (''wait2[Val option_step_check, Ref "A", Ref "a"]))
        ''C Val get_product_parameters)
      ''C Val get_S_fields))).
Definition option_eliminator (A : Combination) : Combination :=
  'wait[option_elim, A].

Notation "'Option [ A ]" :=
  ('tagged[option_eliminator A, opt_nm]) (at level 0).

Lemma option_eliminator_app : forall A a X V,
  option_eliminator A @ a @r X ==> V <-> fold_core ('wait2[option_step_check, A, a]) @ X ==> V.
Proof.
  intros A a X V.
  assert (Hh : option_eliminator A @ a ==> fold_core ('wait2[option_step_check, A, a])).
  { unfold option_eliminator; apply wait_eval; unfold option_elim, fold_core; cbn; evaluate. }
  split; intro H.
  - destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hwu]]]]; inv_out Hu.
    pose proof (eval_deterministic _ _ Hw _ Hh); subst w; exact Hwu.
  - eapply eval_appl; [exact Hh|exact H].
Qed.
Lemma option_eliminator_eval : forall A a U F,
  a @ F @r A ==> Sm U -> option_eliminator A @ a @r (U '* F) ==> Sm U.
Proof.
  intros A a U F H; apply option_eliminator_app; apply fold_core_eval.
  destruct (eval_app_r_inv _ _ _ (option_step_check_eval A a U F H)) as [w [Hw Hv]].
  eapply eval_appl; [apply wait2_eval; exact Hw|exact Hv].
Qed.
Lemma option_eliminator_inv : forall A a X U,
  option_eliminator A @ a @r X ==> Sm U ->
  exists F, X = U '* F /\ a @ F @r A ==> Sm U.
Proof.
  intros A a X V H; apply option_eliminator_app, fold_core_inv in H.
  destruct H as [U [F [-> H]]].
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]]; apply wait2_eval_inv in Hw.
  pose proof (eval_appl _ _ _ _ _ Hw Hv) as H'; apply option_step_check_inv in H'.
  destruct H' as [-> H']; eexists; split; [reflexivity|exact H'].
Qed.

Lemma type_app_Option : forall AI A U F,
  type_app AI @ F @r A ==> Sm U ->
  type_app AI @ ('Option[A]) @r (U '* F) ==> Sm U.
Proof. intros; eapply type_app_abstract; apply option_eliminator_eval; assumption. Qed.


(** The witness value witnesses [A] in the [none] case.  Decoration does
    not alter execution, but makes that witness visible to inference. *)
Definition none (w : Combination) : Combination :=
  'tagged['decorate['fst,w],opt_nm].

Definition some (value : Combination) : Combination :=
  'tagged['S2['snd,'K1 value],opt_nm].

(** How options apply. *)
Lemma none_apply : forall a b f, none a @ (b '* f) ==> b.
Proof. intros; unfold none; apply tagged_eval; apply wait_eval; evaluate. Qed.
Lemma some_apply : forall x b f v, f @ x ==> v -> some x @ (b '* f) ==> v.
Proof. intros x b f v H; unfold some; apply tagged_eval; inv_out H; d_eval0. Qed.

Definition option_none_type (A : Combination) := 'decorate['fst,A].
Definition option_some_type (A : Combination) :=
  'S2['snd,'K1 A].

Opaque equal1 option_elim.

(** The abstractor of the option family maps the two carriers
    [option_none_type A] and [option_some_type A] to the eliminator
    [option_eliminator A]. *)
Definition option_none_fields := Eval cbv -[equal1 option_elim] in to_tree
  (star "F" (star "D"
    (Val (equal1 'fst) @@ Ref "F"
      @@ (Val Lf @@ (Val Lf @@ ''wait[Val option_elim, Ref "D"]))
      @@ Val Lf))).

Definition option_none_case_package :
  { t : Combination |
    (to_tree (''onStem1 (''onFork1 (Val option_none_fields))))
      'C get_decorate = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition option_none_case :=
  Eval cbn in proj1_sig option_none_case_package.

Local Lemma option_none_case_compilation :
  (to_tree (''onStem1 (''onFork1 (Val option_none_fields))))
    'C get_decorate = option_none_case.
Proof. unfold option_none_case; exact (proj2_sig option_none_case_package). Qed.

Definition option_some_fields :=
  Eval cbn -[equal1 get_K1 option_elim] in to_tree
    (star "G" (star "F"
      (Val (equal1 'snd) @@ Ref "G"
        @@ (''onStem1 (star "A" (Val Lf @@ ''wait[Val option_elim, Ref "A"]))
              @@ (Val get_K1 @@ Ref "F"))
        @@ Val Lf))).

Definition option_some_case_package :
  { t : Combination |
    (to_tree (''onStem1 (''onFork1 (Val option_some_fields))))
      'C get_S_fields = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition option_some_case :=
  Eval cbn in proj1_sig option_some_case_package.

Local Lemma option_some_case_compilation :
  (to_tree (''onStem1 (''onFork1 (Val option_some_fields))))
    'C get_S_fields = option_some_case.
Proof. unfold option_some_case; exact (proj2_sig option_some_case_package). Qed.

Definition option_abstractor := extend option_none_case option_some_case.

Lemma option_none_fields_some : forall A,
  option_none_fields @ 'fst @r (A) ==> ('S1 (option_eliminator A)).
Proof.
  intros; unfold option_none_fields;
    repeat first [apply equal1_eq | progress evaluate].
Qed.
Lemma option_abstractor_none : forall A,
  option_abstractor @ option_none_type A ==> Sm (option_eliminator A).
Proof.
  intros A; pose proof (option_none_fields_some A) as H; inv_out H.
  unfold option_abstractor; apply extend_some.
  rewrite <- option_none_case_compilation; unfold option_none_type; cbn -[option_none_fields].
  repeat first [apply get_decorate_some | progress evaluate].
Qed.

Lemma option_some_fields_some : forall A,
  option_some_fields @ 'snd @r ('K1 A) ==> Sm (option_eliminator A).
Proof.
  intro A; unfold option_some_fields;
    cbn -[equal1 get_K1 option_elim]; evaluate.
  all: first
    [ apply equal1_eq
    | apply get_K1_some
    | evaluate ].
Qed.

Lemma option_abstractor_some : forall A,
  option_abstractor @ option_some_type A ==> Sm (option_eliminator A).
Proof.
  intros A; unfold option_abstractor.
  eapply extend_none_value.
  - rewrite <- option_none_case_compilation; unfold option_some_type.
    evaluate.
    + apply get_decorate_none.
      intros E D H; discriminate H.
    + simpl; evaluate.
  - pose proof (option_some_fields_some A) as HF; inv_out HF.
    rewrite <- option_some_case_compilation; unfold option_some_type.
    evaluate.
    + apply get_S_fields_some.
    + simpl; evaluate.
Qed.

Lemma option_compose_inv : forall g f x v,
  (g 'C f) @ x ==> v ->
  exists y, f @ x ==> y /\ g @ y ==> v.
Proof. intros g f x v H; inv_out H; invert_eval; eauto. Qed.

Lemma option_onStem_onFork_eval : forall f A B R,
  f @ A @r B ==> R ->
  to_tree (''onStem1 (''onFork1 (Val f))) @ Sm (Fk A B) ==> R.
Proof. intros f A B R H; simpl; evaluate. Qed.

Lemma option_some_fields_inv : forall G F E,
  (option_some_fields @ G @r F ==> Sm E) ->
  exists A, G = 'snd /\ F = 'K1 A /\ E = option_eliminator A.
Proof.
  intros G F E H; unfold option_some_fields in H; cbn -[equal1 get_K1 option_elim] in H.
  invert_eval.
  all: match goal with H1 : equal1 'snd @ ?g ==> ?b |- _ =>
    destruct (combination_eq_dec ('snd) g) as [Heq|Hneq];
    [ subst g; pose proof (eval_deterministic _ _ H1 _ (equal1_eq 'snd)); subst b
    | pose proof (eval_deterministic _ _ H1 _ (equal1_neq _ _ Hneq)); subst b ] end;
    invert_eval.
  all: try match goal with H1 : get_K1 @ ?f ==> Sm ?A |- _ => apply get_K1_inv in H1 end.
  all: eexists; repeat split; eassumption.
Qed.

Lemma option_none_fields_inv : forall F D E,
  option_none_fields @ F @r D ==> Sm (Sm E) ->
  F = 'fst /\ E = option_eliminator D.
Proof.
  intros F D E H; unfold option_none_fields in H; invert_eval.
  destruct (combination_eq_dec ('fst) F) as [<-|Hneq].
  - match goal with H1 : equal1 'fst @ 'fst ==> ?b |- _ =>
      pose proof (eval_deterministic _ _ H1 _ (equal1_eq 'fst)); subst b end.
    invert_eval; auto.
  - match goal with H1 : equal1 'fst @ F ==> ?b |- _ =>
      pose proof (eval_deterministic _ _ H1 _ (equal1_neq _ _ Hneq)); subst b end.
    invert_eval.
Qed.

Lemma option_none_case_inv : forall C E,
  (option_none_case @ C ==> ('S1 E)) ->
  exists A, E = option_eliminator A /\ C = option_none_type A.
Proof.
  intros C E H; unfold option_none_case in H; cbn in H; invert_eval.
  assert (HF : option_none_fields @ v21 @r v22 ==> Sm (Sm E))
    by (eapply eval_appl; eauto).
  destruct (option_none_fields_inv _ _ _ HF) as [-> ->].
  eexists; split; [reflexivity|apply get_decorate_inv; assumption].
Qed.

Lemma option_some_case_inv : forall C E,
  (option_some_case @ C ==> Sm E) ->
  exists A, E = option_eliminator A /\ C = option_some_type A.
Proof.
  intros C E H; rewrite <- option_some_case_compilation in H.
  destruct (option_compose_inv _ _ _ _ H) as [R [Hget Huse]].
  clear H.
  destruct (get_S_fields_result_inv C R Hget)
    as [-> | [G [F [-> HC]]]]; clear Hget.
  - simpl in Huse; invert_eval.
  - simpl in Huse; invert_eval.
    assert (HF : option_some_fields @ G @r F ==> Sm E)
      by (eapply eval_appl; eauto).
    destruct (option_some_fields_inv _ _ _ HF) as [A [-> [-> ->]]]; subst.
    eexists; split; reflexivity.
Qed.

(** The abstractor accepts exactly the two option carriers. *)
Lemma option_abstractor_inv : forall C E,
  option_abstractor @ C ==> Sm E ->
  exists A,
    E = option_eliminator A /\
      (C = option_none_type A \/ C = option_some_type A).
Proof.
  intros C E H; unfold option_abstractor in H.
  destruct (extend_inv _ _ _ _ H)
    as [[value [Hnone Heq]] |
        [[Hnone Hsome] |
         [left [right [Hfork Heq]]]]]; clear H.
  - subst value; destruct (option_none_case_inv _ _ Hnone) as [A [-> ->]].
    exists A; split; [reflexivity|left; reflexivity].
  - destruct (option_some_case_inv _ _ Hsome) as [A [-> ->]].
    exists A; split; [reflexivity|right; reflexivity].
  - discriminate Heq.
Qed.

(** Type application to an option carrier. *)
Lemma option_carrier_type_app : forall AI A U F C,
  type_app AI @ F @r A ==> Sm U ->
  C = option_none_type A \/ C = option_some_type A ->
  type_app AI @ C @r (U '* F) ==> Sm U.
Proof.
  intros AI A U F C HF [-> | ->].
  - unfold option_none_type.
    eapply type_app_wait.
    + apply type_app_K_ev.
    + apply type_app_fst_product.
  - unfold option_some_type.
    new_S.
    + discriminate.
    + apply type_app_snd_product.
    + apply type_app_K_ev.
    + exact HF.
Qed.

Lemma option_abstractor_sound : forall AI C E X U,
  option_abstractor @ C ==> Sm E ->
  E @ type_app AI @r X ==> Sm U ->
  type_app AI @ C @r X ==> Sm U.
Proof.
  intros AI C E X U Hconstructor Heliminate.
  destruct (option_abstractor_inv C E Hconstructor) as [A [-> HC]].
  destruct (option_eliminator_inv _ _ _ _ Heliminate) as [F [-> HF]].
  eapply option_carrier_type_app; eassumption.
Qed.


Definition supports_option AI :=
  (AI @ opt_nm ==> ('K1 option_abstractor)).

Lemma option_abstractor_supported : forall AI a C E,
  supports_option AI -> option_abstractor @ C ==> Sm E ->
  AI @ opt_nm @r a @r C ==> Sm E.
Proof.
  intros AI a C E Hsupports Hconstructor.
  eapply declaration_apply; [exact Hsupports | exact Hconstructor].
Qed.

Definition option_case_package :
  { t : Combination |
    to_tree (tcase (Val opt_nm) (Val ('K1 option_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition option_case := Eval cbn in proj1_sig option_case_package.

Lemma option_case_compilation :
  to_tree (tcase (Val opt_nm) (Val ('K1 option_abstractor))) = option_case.
Proof. unfold option_case; exact (proj2_sig option_case_package). Qed.

Lemma option_case_some :
  option_case @ opt_nm ==> Sm ('K1 option_abstractor).
Proof. rewrite <- option_case_compilation; apply tcase_eq. Qed.

Lemma option_case_none : forall N,
  N <> opt_nm -> option_case @ N ==> Lf.
Proof.
  intros N Hneq; rewrite <- option_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.

Definition option_ontology := extend option_case nat_ontology.

Lemma option_ontology_row : option_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold option_ontology; apply extend_none_value; [apply option_case_none; unfold opt_nm, fun_nm; discriminate|exact (functions_declared nat_decl)].
Qed.
Canonical Structure option_decl := mkDecl option_ontology option_ontology_row.

Lemma option_ontology_supports_option : supports_option option_ontology.
Proof.
  unfold option_ontology; apply extend_some; apply option_case_some.
Qed.
Lemma option_ontology_supports_number : supports_number option_ontology.
Proof.
  unfold supports_number, option_ontology.
  apply extend_none_value; [apply option_case_none; discriminate|].
  exact nat_ontology_supports_number.
Qed.
Lemma option_ontology_supports_booleans : supports_booleans option_ontology.
Proof.
  unfold supports_booleans, option_ontology.
  apply extend_none_value; [apply option_case_none; discriminate|].
  exact nat_ontology_supports_booleans.
Qed.

(** The option clause declares the option family at [opt_nm]. *)
Lemma option_case_registers :
  clause_registers option_case opt_nm ('K1 option_abstractor).
Proof. rewrite <- option_case_compilation; apply tcase_registers. Qed.


Section OptionExamples.

Set Default Proof Using "All".
Variable AI : Combination.
Hypothesis AI_supports_option : supports_option AI.
Local Abbreviation ontology_4 := AI.

Lemma infer_opt_nm : infer ontology_4 @ opt_nm ==> Sm opt_nm.
Proof.
  unfold opt_nm; eapply infer_tag_free;
    repeat constructor; intros; discriminate.
Qed.

Lemma infer_none : forall witness A,
  infer ontology_4 @ witness ==> Sm A ->
  infer ontology_4 @ none witness ==> Sm ('Option[A]).
Proof.
  intros witness A Hd; unfold none.
  eapply infer_tagged.
  - eapply infer_decorate.
    + eapply infer_tag_free; repeat constructor; intros; discriminate.
    + exact Hd.
  - exact infer_opt_nm.
  - eapply option_abstractor_supported; [exact AI_supports_option |].
    apply option_abstractor_none.
Qed.

Lemma infer_some : forall value A,
  infer ontology_4 @ value ==> Sm A ->
  infer ontology_4 @ some value ==> Sm ('Option[A]).
Proof.
  intros value A Hv; unfold some.
  eapply infer_tagged.
  - infer_tac.
    all: try exact Hv.
    all: eapply infer_tag_free; repeat constructor; intros; discriminate.
  - exact infer_opt_nm.
  - eapply option_abstractor_supported; [exact AI_supports_option |].
    apply option_abstractor_some.
Qed.

Lemma option_is_data : forall C A,
  infer ontology_4 @ C ==> Sm ('Option[A]) ->
  (exists witness,
      C = none witness /\ infer ontology_4 @ witness ==> Sm A) \/
  (exists value,
      C = some value /\ infer ontology_4 @ value ==> Sm A).
Proof.
  intros C A Hinfer.
  destruct (infer_tagged_result_inv ontology_4 C
    (option_eliminator A) opt_nm Hinfer)
    as [c [n [F [-> [Hc [Hn Hdispatch]]]]]].
  assert (Hconstructor : option_abstractor @ F ==>
    Sm (option_eliminator A)).
  { exact (declaration_K1_inv _ _ _ _ _ _ AI_supports_option Hdispatch). }
  destruct (option_abstractor_inv F (option_eliminator A) Hconstructor)
    as [A0 [HE [HF | HF]]].
  all: inversion HE; subst A0; clear HE; subst F.
  - destruct (infer_decorate_inv ontology_4 c 'fst (A) Hc)
      as [f [witness [-> [Hf Hd]]]].
    assert (f = 'fst) by (eapply infer_tag_free_inv; [exact Hf | tag_free_tac]).
    subst f.
    assert (n = opt_nm)
      by (eapply infer_tag_free_inv; [exact Hn | tag_free_tac]).
    subst n; left; exists witness; split; [reflexivity|exact Hd].
  - destruct (infer_S2_K1_inv ontology_4 c 'snd A)
      as [value [-> Hv]]; [tag_free_tac | discriminate | exact Hc |].
    assert (n = opt_nm)
      by (eapply infer_tag_free_inv; [exact Hn | tag_free_tac]).
    subst n; right; exists value; split; [reflexivity | exact Hv].
Qed.


End OptionExamples.
Set Default Proof Using "Type".


Unset Default Proof Using.
Transparent equal equal1 option_elim.

(**********************************************************************)
(* Witnessed Scott sums.                                              *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans.

Set Default Proof Using "Type".
Open Scope string_scope.
Opaque equal.

(** [Sum A B # ((A --> U) * (B --> U)) ==> Sm U].
    Each injection decorates its executable component with evidence for the
    absent side's type. Annotation-aware queries inspect the executable
    component and ignore that evidence, independently of sum elimination. *)

Definition sum_nm :=
  Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf)))))).

Definition strip_some := 'onStem1 'I.

Definition sum_step_check := Eval cbv -[equal] in to_tree
  (star "P" (star "a" (star "F" (star "G"
    (''onStem1 (star "V" (''onStem1 (star "W"
        (op equal @@ Ref "V" @@ Ref "W" @@ (Val Lf @@ Ref "V") @@ Val Lf))
        @@ (Ref "a" @@ Ref "G" @@ (Ref "P" @@ Val 'KI))))
      @@ (Ref "a" @@ Ref "F" @@ (Ref "P" @@ Val 'K))))))).

Lemma sum_step_check_eval : forall A B a F G U,
  a @ F @r A ==> Sm U -> a @ G @r B ==> Sm U ->
  sum_step_check @ (A '* B) @r a @r F @r G ==> Sm U.
Proof.
  intros A B a F G U H1 H2; inv_out H1; inv_out H2.
  assert (HA : (A '* B) @ 'K ==> A) by evaluate.
  assert (HB : (A '* B) @ 'KI ==> B) by evaluate.
  unfold sum_step_check; d_eval0.
Qed.
Lemma sum_step_check_inv : forall A B a F G U,
  sum_step_check @ (A '* B) @r a @r F @r G ==> Sm U ->
  a @ F @r A ==> Sm U /\ a @ G @r B ==> Sm U.
Proof.
  intros A B a F G U H.
  assert (HA : (A '* B) @ 'K ==> A) by evaluate.
  assert (HB : (A '* B) @ 'KI ==> B) by evaluate.
  revert H HA HB; generalize (A '* B) as P; intros P H HA HB.
  unfold sum_step_check in H.
  inv_out H; invert_eval.
  pose proof (eval_deterministic _ _ H11 _ HA) as ->.
  pose proof (eval_deterministic _ _ H9 _ HB) as ->.
  all: match goal with
  | H1 : equal @ ?V ==> ?e, H2 : ?e @ ?W ==> ?b |- _ =>
    assert (Hequal : equal @ V @r W ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ Hequal) as [[Hv0 Heq] | [Hv0 Hneq]]; subst b; invert_eval
  end.
  all: subst; split; eapply eval_appl; eassumption.
Qed.

Definition sum_elim := Eval cbn in to_tree
  (star "P" (star "a"
    (''onStem1
      (''onStem1
        (''onFork1 (''wait2[Val sum_step_check, Ref "P", Ref "a"]))
        ''C Val get_product_parameters)
      ''C Val get_S_fields))).
Definition sum_eliminator (A B : Combination) : Combination :=
  'wait[sum_elim, A '* B].

Notation "'Sum [ A , B ]" :=
  ('tagged[sum_eliminator A B, sum_nm]) (at level 0).
Notation "A '+ B" := ('Sum[A,B]) (at level 50).

Lemma sum_eliminator_app : forall A B a X V,
  sum_eliminator A B @ a @r X ==> V <->
  fold_core ('wait2[sum_step_check, A '* B, a]) @ X ==> V.
Proof.
  intros A B a X V.
  assert (Hh : sum_eliminator A B @ a ==> fold_core ('wait2[sum_step_check, A '* B, a])).
  { unfold sum_eliminator; apply wait_eval; unfold sum_elim, fold_core; cbn; evaluate. }
  split; intro H.
  - destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hwu]]]]; inv_out Hu.
    pose proof (eval_deterministic _ _ Hw _ Hh); subst w; exact Hwu.
  - eapply eval_appl; [exact Hh|exact H].
Qed.
Lemma sum_eliminator_eval : forall A B a F G U,
  a @ F @r A ==> Sm U -> a @ G @r B ==> Sm U ->
  sum_eliminator A B @ a @r (F '* G) ==> Sm U.
Proof.
  intros A B a F G U H1 H2; apply sum_eliminator_app; apply fold_core_eval.
  destruct (eval_app_r_inv _ _ _ (sum_step_check_eval A B a F G U H1 H2)) as [w [Hw Hv]].
  eapply eval_appl; [apply wait2_eval; exact Hw|exact Hv].
Qed.
Lemma sum_eliminator_inv : forall A B a X U,
  sum_eliminator A B @ a @r X ==> Sm U ->
  exists F G, X = F '* G /\ a @ F @r A ==> Sm U /\ a @ G @r B ==> Sm U.
Proof.
  intros A B a X V H; apply sum_eliminator_app, fold_core_inv in H.
  destruct H as [F [G [-> H]]].
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]]; apply wait2_eval_inv in Hw.
  pose proof (eval_appl _ _ _ _ _ Hw Hv) as H'; apply sum_step_check_inv in H'.
  destruct H' as [H1 H2]; exists F, G; repeat split; assumption.
Qed.

Lemma type_app_Sum : forall AI A B U F G,
  type_app AI @ F @r A ==> Sm U -> type_app AI @ G @r B ==> Sm U ->
  type_app AI @ ('Sum[A,B]) @r (F '* G) ==> Sm U.
Proof. intros; eapply type_app_abstract; apply sum_eliminator_eval; assumption. Qed.


Definition inleft (value w : Combination) : Combination :=
  'tagged['decorate['S2['fst,'K1 value],w],sum_nm].

Definition inright (w value : Combination) : Combination :=
  'tagged['decorate['S2['snd,'K1 value],w],sum_nm].

(** How sums apply. *)
Lemma inleft_apply : forall x w f g v, f @ x ==> v -> inleft x w @ (f '* g) ==> v.
Proof. intros x w f g v H; unfold inleft; apply tagged_eval; apply wait_eval; inv_out H; d_eval0. Qed.
Lemma inright_apply : forall w y f g v, g @ y ==> v -> inright w y @ (f '* g) ==> v.
Proof. intros w y f g v H; unfold inright; apply tagged_eval; apply wait_eval; inv_out H; d_eval0. Qed.

Definition sum_left_type (A B : Combination) :=
  'decorate['S2['fst,'K1 A],B].

Definition sum_right_type (A B : Combination) :=
  'decorate['S2['snd,'K1 B],A].

Definition sum_result_builder :=
  Eval cbn in to_tree
    (star "A" (star "B"
      (Val Lf @@ (Val Lf @@ Ref "A" @@ Ref "B")))).

Definition sum_result_with (A : Combination) :=
  Eval cbn in to_tree
    (star "B" (Val Lf @@ (Val Lf @@ Val A @@ Ref "B"))).

Lemma sum_result_builder_first : forall A,
  sum_result_builder @ A ==> sum_result_with A.
Proof. intros; unfold sum_result_builder, sum_result_with; cbn; evaluate. Qed.

Lemma sum_result_with_eval : forall A B,
  sum_result_with A @ B ==> Sm (Fk A B).
Proof. intros; unfold sum_result_with; cbn; evaluate. Qed.


(** After the payload fork has been exposed, each summand follows the same
    protocol as [some]: test its discriminator and recover the argument from
    a unary [K] application. *)
Definition sum_left_fields :=
  Eval cbn -[equal1 get_K1 sum_result_builder] in to_tree
    (star "G" (star "F" (star "B"
      (Val (equal1 'fst) @@ Ref "G"
        @@ (''onStem1
              (star "A"
                (Val sum_result_builder @@ Ref "A" @@ Ref "B"))
            @@ (Val get_K1 @@ Ref "F"))
        @@ Val Lf)))).

Definition sum_right_fields :=
  Eval cbn -[equal1 get_K1 sum_result_builder] in to_tree
    (star "G" (star "F" (star "A"
      (Val (equal1 'snd) @@ Ref "G"
        @@ (''onStem1
              (star "B"
                (Val sum_result_builder @@ Ref "A" @@ Ref "B"))
            @@ (Val get_K1 @@ Ref "F"))
        @@ Val Lf)))).

Opaque sum_left_fields sum_right_fields.

(** The waits prevent [star] from expanding the already compiled field
    programs while the surrounding payload matcher is built. *)
Definition sum_left_fields_blocked := 'wait['I,sum_left_fields].
Definition sum_right_fields_blocked := 'wait['I,sum_right_fields].

Definition sum_left_shape :=
  Eval cbn -[get_S_fields sum_left_fields] in to_tree
    (star "P" (star "D"
      (''onStem1 (''onFork1
        (star "G" (star "F"
          (Val sum_left_fields_blocked @@ Ref "G" @@ Ref "F" @@ Ref "D"))))
        @@ (Val get_S_fields @@ Ref "P")))).

Definition sum_right_shape :=
  Eval cbn -[get_S_fields sum_right_fields] in to_tree
    (star "P" (star "D"
      (''onStem1 (''onFork1
        (star "G" (star "F"
          (Val sum_right_fields_blocked @@ Ref "G" @@ Ref "F" @@ Ref "D"))))
        @@ (Val get_S_fields @@ Ref "P")))).

Definition sum_left_case_package :
  { t : Combination |
    (to_tree (''onStem1 (''onFork1 (Val sum_left_shape))))
      'C get_decorate = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition sum_left_case :=
  Eval cbn in proj1_sig sum_left_case_package.

Local Lemma sum_left_case_compilation :
  (to_tree (''onStem1 (''onFork1 (Val sum_left_shape))))
    'C get_decorate = sum_left_case.
Proof. unfold sum_left_case; exact (proj2_sig sum_left_case_package). Qed.

Definition sum_right_case_package :
  { t : Combination |
    (to_tree (''onStem1 (''onFork1 (Val sum_right_shape))))
      'C get_decorate = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition sum_right_case :=
  Eval cbn in proj1_sig sum_right_case_package.

Local Lemma sum_right_case_compilation :
  (to_tree (''onStem1 (''onFork1 (Val sum_right_shape))))
    'C get_decorate = sum_right_case.
Proof. unfold sum_right_case; exact (proj2_sig sum_right_case_package). Qed.

Lemma sum_left_fields_some : forall A B,
  sum_left_fields @ 'fst @r ('K1 A) @r B ==> Sm (Fk A B).
Proof.
  Local Transparent sum_left_fields.
  intros; unfold sum_left_fields;
    cbn -[equal1 get_K1 sum_result_builder]; evaluate.
  - apply equal1_eq.
  - apply get_K1_some.
  - evaluate.
    + apply sum_result_builder_first.
    + apply sum_result_with_eval.
  all: evaluate.
  Unshelve. exact ('K1 (Sm (Fk A B))). Unshelve.
  - apply eval_to_fork.
  - apply eval_k.
Local Opaque sum_left_fields.
Qed.

Lemma sum_right_fields_some : forall A B,
  sum_right_fields @ 'snd @r ('K1 B) @r A ==> Sm (Fk A B).
Proof.
  Local Transparent sum_right_fields.
  intros; unfold sum_right_fields;
    cbn -[equal1 get_K1 sum_result_builder]; evaluate.
  - apply equal1_eq.
  - apply get_K1_some.
  - apply sum_result_builder_first.
  - evaluate; apply sum_result_with_eval.
  all: evaluate.
  Unshelve. exact ('K1 (Sm (Fk A B))). Unshelve.
  - apply eval_to_fork.
  - apply eval_k.
Local Opaque sum_right_fields.
Qed.

Lemma sum_left_shape_eval : forall G F D R,
  sum_left_fields @ G @r F @r D ==> R ->
  sum_left_shape @ ('S2[G,F]) @r (D) ==> R.
Proof.
  Local Transparent sum_left_fields.
  intros G F D R H; unfold sum_left_shape;
    cbn -[get_S_fields sum_left_fields].
  inv_out H.
  match goal with Hpartial : sum_left_fields @ G @r F ==> _ |- _ => inv_out Hpartial end.
  unfold sum_left_fields_blocked;
    repeat first [apply get_S_fields_some | progress evaluate].
Local Opaque sum_left_fields.
Qed.

Lemma sum_right_shape_eval : forall G F D R,
  sum_right_fields @ G @r F @r D ==> R ->
  sum_right_shape @ ('S2[G,F]) @r (D) ==> R.
Proof.
  Local Transparent sum_right_fields.
  intros G F D R H; unfold sum_right_shape;
    cbn -[get_S_fields sum_right_fields].
  inv_out H.
  match goal with Hpartial : sum_right_fields @ G @r F ==> _ |- _ => inv_out Hpartial end.
  unfold sum_right_fields_blocked;
    repeat first [apply get_S_fields_some | progress evaluate].
Local Opaque sum_right_fields.
Qed.

Lemma sum_left_case_some : forall A B,
  sum_left_case @ sum_left_type A B ==> Sm (Fk A B).
Proof.
  intros A B; rewrite <- sum_left_case_compilation.
  unfold sum_left_type; evaluate.
  - apply get_decorate_some.
  - apply option_onStem_onFork_eval.
    apply sum_left_shape_eval; apply sum_left_fields_some.
Qed.

Lemma sum_right_case_some : forall A B,
  sum_right_case @ sum_right_type A B ==> Sm (Fk A B).
Proof.
  intros A B; rewrite <- sum_right_case_compilation.
  unfold sum_right_type; evaluate.
  - apply get_decorate_some.
  - apply option_onStem_onFork_eval.
    apply sum_right_shape_eval; apply sum_right_fields_some.
Qed.

Lemma sum_left_fields_wrong_head : forall G F D,
  G <> 'fst -> sum_left_fields @ G @r F @r D ==> Lf.
Proof.
  Local Transparent sum_left_fields.
  intros G F D Hneq.
  destruct (K1_decide F) as [[A ->] | Hnone].
  - unfold sum_left_fields;
      cbn -[equal1 get_K1 sum_result_builder]; evaluate.
    + eapply equal1_neq; congruence.
    + apply get_K1_some.
    + evaluate.
      * apply sum_result_builder_first.
      * apply sum_result_with_eval.
    all: evaluate.
    Unshelve. exact 'I. Unshelve.
    + apply eval_k.
    + exact (I_eval Lf).
  - unfold sum_left_fields;
      cbn -[equal1 get_K1 sum_result_builder]; evaluate.
    all: first
      [ eapply equal1_neq; congruence
      | apply get_K1_none; exact Hnone
      | evaluate
      | apply I_eval ].
Local Opaque sum_left_fields.
Qed.

Lemma sum_left_case_rejects_right : forall A B,
  sum_left_case @ sum_right_type A B ==> Lf.
Proof.
  intros; rewrite <- sum_left_case_compilation.
  unfold sum_right_type; evaluate.
  - apply get_decorate_some.
  - apply option_onStem_onFork_eval.
    apply sum_left_shape_eval.
    apply sum_left_fields_wrong_head; discriminate.
Qed.

Definition sum_fields :=
  extend sum_left_case (strip_some 'C sum_right_case).

(** The abstractor of the sum family runs [sum_fields] and builds from
    its answer [Fk A B] the eliminator [sum_eliminator A B]. *)
Definition sum_eliminator_maker :=
  Eval cbv -[sum_elim] in to_tree
    (star "A" (star "B" (Val Lf @@ ''wait[Val sum_elim, Ref "A" ''* Ref "B"]))).
Definition sum_abstractor := ('onFork1 sum_eliminator_maker) 'C sum_fields.

Lemma sum_eliminator_maker_eval : forall A B,
  sum_eliminator_maker @ A @r B ==> Sm (sum_eliminator A B).
Proof. intros; unfold sum_eliminator_maker, sum_eliminator; evaluate. Qed.

Lemma sum_fields_left : forall A B, sum_fields @ sum_left_type A B ==> Fk A B.
Proof. intros; unfold sum_fields; apply extend_some, sum_left_case_some. Qed.

Lemma sum_fields_right : forall A B, sum_fields @ sum_right_type A B ==> Fk A B.
Proof.
  intros A B; unfold sum_fields; eapply extend_none_value.
  - apply sum_left_case_rejects_right.
  - unfold strip_some; evaluate; [apply sum_right_case_some | evaluate].
Qed.

Lemma sum_abstractor_of_fields : forall C A B,
  sum_fields @ C ==> Fk A B -> sum_abstractor @ C ==> Sm (sum_eliminator A B).
Proof.
  intros C A B H; unfold sum_abstractor; apply eval_c; eapply eval_arg_value;
    [exact H|].
  eapply eval_fork; apply sum_eliminator_maker_eval.
Qed.

Lemma sum_abstractor_left : forall A B,
  sum_abstractor @ sum_left_type A B ==> Sm (sum_eliminator A B).
Proof. intros; apply sum_abstractor_of_fields, sum_fields_left. Qed.

Lemma sum_abstractor_right : forall A B,
  sum_abstractor @ sum_right_type A B ==> Sm (sum_eliminator A B).
Proof. intros; apply sum_abstractor_of_fields, sum_fields_right. Qed.

Lemma sum_left_fields_wrong_tail : forall F D,
  (forall A, F <> 'K1 A) ->
  sum_left_fields @ 'fst @r F @r D ==> Lf.
Proof.
  Local Transparent sum_left_fields.
  intros F D Hnone; unfold sum_left_fields;
    cbn -[equal1 get_K1 sum_result_builder]; evaluate.
  all: first
    [ apply equal1_eq
    | apply get_K1_none; exact Hnone
    | evaluate
    | apply I_eval ].
Local Opaque sum_left_fields.
Qed.

Lemma sum_right_fields_wrong_head : forall G F D,
  G <> 'snd -> sum_right_fields @ G @r F @r D ==> Lf.
Proof.
  Local Transparent sum_right_fields.
  intros G F D Hneq.
  destruct (K1_decide F) as [[B ->] | Hnone].
  - unfold sum_right_fields;
      cbn -[equal1 get_K1 sum_result_builder]; evaluate.
    + eapply equal1_neq; congruence.
    + apply get_K1_some.
    + apply sum_result_builder_first.
    + evaluate; apply sum_result_with_eval.
    all: evaluate.
    Unshelve. exact 'I. Unshelve.
    + apply eval_k.
    + exact (I_eval Lf).
  - unfold sum_right_fields;
      cbn -[equal1 get_K1 sum_result_builder]; evaluate.
    all: first
      [ eapply equal1_neq; congruence
      | apply get_K1_none; exact Hnone
      | evaluate
      | apply I_eval ].
    apply sum_result_builder_first.
Local Opaque sum_right_fields.
Qed.

Lemma sum_right_fields_wrong_tail : forall F D,
  (forall B, F <> 'K1 B) ->
  sum_right_fields @ 'snd @r F @r D ==> Lf.
Proof.
  Local Transparent sum_right_fields.
  intros F D Hnone; unfold sum_right_fields;
    cbn -[equal1 get_K1 sum_result_builder]; evaluate.
  all: first
    [ apply equal1_eq
    | apply get_K1_none; exact Hnone
    | evaluate
    | apply I_eval ].
  apply sum_result_builder_first.
Local Opaque sum_right_fields.
Qed.

Lemma sum_left_fields_inv : forall G F D A B,
  sum_left_fields @ G @r F @r D ==> Sm (Fk A B) ->
  G = 'fst /\ F = 'K1 A /\ D = B.
Proof.
  intros G F D A B H.
  destruct (combination_eq_dec G 'fst) as [-> | Hneq].
  - destruct (K1_decide F) as [[A0 ->] | Hnone].
    + pose proof (eval_deterministic _ _ H _
        (sum_left_fields_some A0 D)) as Heq.
      inversion Heq; auto.
    + pose proof (eval_deterministic _ _ H _
        (sum_left_fields_wrong_tail F D Hnone)); discriminate.
  - pose proof (eval_deterministic _ _ H _
      (sum_left_fields_wrong_head G F D Hneq)); discriminate.
Qed.

Lemma sum_right_fields_inv : forall G F D A B,
  sum_right_fields @ G @r F @r D ==> Sm (Fk A B) ->
  G = 'snd /\ F = 'K1 B /\ D = A.
Proof.
  intros G F D A B H.
  destruct (combination_eq_dec G 'snd) as [-> | Hneq].
  - destruct (K1_decide F) as [[B0 ->] | Hnone].
    + pose proof (eval_deterministic _ _ H _
        (sum_right_fields_some D B0)) as Heq.
      inversion Heq; auto.
    + pose proof (eval_deterministic _ _ H _
        (sum_right_fields_wrong_tail F D Hnone)); discriminate.
  - pose proof (eval_deterministic _ _ H _
      (sum_right_fields_wrong_head G F D Hneq)); discriminate.
Qed.

Lemma sum_left_shape_inv : forall P D A B,
  sum_left_shape @ P @r D ==> Sm (Fk A B) ->
  P = 'S2['fst,'K1 A] /\ D = B.
Proof.
  Local Transparent sum_left_fields.
  intros P D A B H; unfold sum_left_shape in H;
    cbn -[get_S_fields sum_left_fields] in H; invert_eval.
  match goal with
  | HG : get_S_fields @ P ==> Sm (Fk ?G ?F) |- P = _ /\ ?D0 = _ =>
    assert (HF : sum_left_fields @ G @r F @r D0 ==> Sm (Fk A B))
      by (repeat (eapply eval_appl; eauto));
    apply sum_left_fields_inv in HF; destruct HF as [-> [-> ->]];
    apply get_S_fields_inv in HG; auto
  end.
Local Opaque sum_left_fields.
Qed.

Lemma sum_right_shape_inv : forall P D A B,
  sum_right_shape @ P @r D ==> Sm (Fk A B) ->
  P = 'S2['snd,'K1 B] /\ D = A.
Proof.
  Local Transparent sum_right_fields.
  intros P D A B H; unfold sum_right_shape in H;
    cbn -[get_S_fields sum_right_fields] in H; invert_eval.
  match goal with
  | HG : get_S_fields @ P ==> Sm (Fk ?G ?F) |- P = _ /\ ?D0 = _ =>
    assert (HF : sum_right_fields @ G @r F @r D0 ==> Sm (Fk A B))
      by (repeat (eapply eval_appl; eauto));
    apply sum_right_fields_inv in HF; destruct HF as [-> [-> ->]];
    apply get_S_fields_inv in HG; auto
  end.
Local Opaque sum_right_fields.
Qed.

Lemma onStem_onFork_inv : forall f A B R,
  (to_tree (''onStem1 (''onFork1 (Val f))) @ Sm (Fk A B) ==> R) ->
  f @ A @r B ==> R.
Proof.
  intros f A B R H; simpl in H; invert_eval.
  eapply eval_appl; eauto.
Qed.

Lemma sum_left_case_inv : forall C A B,
  sum_left_case @ C ==> Sm (Fk A B) -> C = sum_left_type A B.
Proof.
  intros C A B H; rewrite <- sum_left_case_compilation in H.
  destruct (option_compose_inv _ _ _ _ H) as [R [Hget Huse]].
  clear H.
  destruct (get_decorate_result_inv C R Hget)
    as [-> | [P [D [-> HC]]]]; clear Hget.
  - simpl in Huse; invert_eval.
  - apply onStem_onFork_inv in Huse.
    apply sum_left_shape_inv in Huse.
    destruct Huse as [-> ->]; exact HC.
Qed.

Lemma sum_right_case_inv : forall C A B,
  sum_right_case @ C ==> Sm (Fk A B) -> C = sum_right_type A B.
Proof.
  intros C A B H; rewrite <- sum_right_case_compilation in H.
  destruct (option_compose_inv _ _ _ _ H) as [R [Hget Huse]].
  clear H.
  destruct (get_decorate_result_inv C R Hget)
    as [-> | [P [D [-> HC]]]]; clear Hget.
  - simpl in Huse; invert_eval.
  - apply onStem_onFork_inv in Huse.
    apply sum_right_shape_inv in Huse.
    destruct Huse as [-> ->]; exact HC.
Qed.

Lemma sum_fields_inv : forall C A B,
  sum_fields @ C ==> Fk A B ->
  C = sum_left_type A B \/ C = sum_right_type A B.
Proof.
  intros C A B H; unfold sum_fields in H.
  destruct (extend_inv _ _ _ _ H)
    as [[value [Hleft Heq]] |
        [[Hleft Hright] |
         [l [r [Hfork Heq]]]]].
  - subst value; left; eapply sum_left_case_inv; exact Hleft.
  - clear Hleft; right.
    destruct (option_compose_inv _ _ _ _ Hright) as [R [Hcase Hstrip]].
    unfold strip_some in Hstrip; invert_eval.
    eapply sum_right_case_inv; exact Hcase.
  - discriminate Heq.
Qed.

Lemma sum_abstractor_inv : forall C E,
  sum_abstractor @ C ==> Sm E ->
  exists A B, E = sum_eliminator A B /\
    (C = sum_left_type A B \/ C = sum_right_type A B).
Proof.
  intros C E H; unfold sum_abstractor in H.
  destruct (option_compose_inv _ _ _ _ H) as [v [Hv Hs]].
  destruct v as [|v|A B]; [invert_eval | invert_eval |].
  assert (Hb : sum_eliminator_maker @ A @r B ==> Sm E) by (inv_out Hs; assumption).
  pose proof (eval_deterministic _ _ Hb _ (sum_eliminator_maker_eval A B)) as Heq.
  inversion Heq; subst E.
  exists A, B; split; [reflexivity | eapply sum_fields_inv; exact Hv].
Qed.

(** Type application to a sum carrier. *)
Lemma sum_carrier_type_app : forall AI A B U F G C,
  type_app AI @ F @r A ==> Sm U -> type_app AI @ G @r B ==> Sm U ->
  C = sum_left_type A B \/ C = sum_right_type A B ->
  type_app AI @ C @r (F '* G) ==> Sm U.
Proof.
  intros AI A B U F G C HF HG [-> | ->].
  - unfold sum_left_type.
    eapply type_app_wait.
    + apply type_app_K_ev.
    + new_S.
      * discriminate.
      * apply type_app_fst_product.
      * apply type_app_K_ev.
      * exact HF.
  - unfold sum_right_type.
    eapply type_app_wait.
    + apply type_app_K_ev.
    + new_S.
      * discriminate.
      * apply type_app_snd_product.
      * apply type_app_K_ev.
      * exact HG.
Qed.

Lemma sum_abstractor_sound : forall AI C E X U,
  sum_abstractor @ C ==> Sm E ->
  E @ type_app AI @r X ==> Sm U ->
  type_app AI @ C @r X ==> Sm U.
Proof.
  intros AI C E X U Hconstructor Heliminate.
  destruct (sum_abstractor_inv C E Hconstructor) as [A [B [-> HC]]].
  destruct (sum_eliminator_inv _ _ _ _ _ Heliminate) as [F [G [-> [HF HG]]]].
  eapply sum_carrier_type_app; eassumption.
Qed.


Definition supports_sum AI :=
  (AI @ sum_nm ==> ('K1 sum_abstractor)).

Lemma sum_abstractor_supported : forall AI a C E,
  supports_sum AI -> sum_abstractor @ C ==> Sm E ->
  AI @ sum_nm @r a @r C ==> Sm E.
Proof.
  intros AI a C E Hsupports Hconstructor.
  eapply declaration_apply; [exact Hsupports | exact Hconstructor].
Qed.

Definition sum_case_package :
  { t : Combination |
    to_tree (tcase (Val sum_nm) (Val ('K1 sum_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition sum_case := Eval cbn in proj1_sig sum_case_package.

Lemma sum_case_compilation :
  to_tree (tcase (Val sum_nm) (Val ('K1 sum_abstractor))) = sum_case.
Proof. unfold sum_case; exact (proj2_sig sum_case_package). Qed.

Lemma sum_case_some : sum_case @ sum_nm ==> Sm ('K1 sum_abstractor).
Proof. rewrite <- sum_case_compilation; apply tcase_eq. Qed.

Lemma sum_case_none : forall N,
  N <> sum_nm -> sum_case @ N ==> Lf.
Proof.
  intros N Hneq; rewrite <- sum_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.

Definition ordinary_ontology := extend sum_case option_ontology.

Lemma ordinary_ontology_row : ordinary_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold ordinary_ontology; apply extend_none_value; [apply sum_case_none; unfold sum_nm, fun_nm; discriminate|exact (functions_declared option_decl)].
Qed.
Canonical Structure ordinary_decl := mkDecl ordinary_ontology ordinary_ontology_row.

Lemma ordinary_ontology_supports_sum : supports_sum ordinary_ontology.
Proof.
  unfold ordinary_ontology; apply extend_some; apply sum_case_some.
Qed.
Lemma ordinary_ontology_supports_option : supports_option ordinary_ontology.
Proof.
  unfold ordinary_ontology; apply extend_none_value.
  - apply sum_case_none; discriminate.
  - exact option_ontology_supports_option.
Qed.

Lemma ordinary_ontology_supports_number : supports_number ordinary_ontology.
Proof.
  unfold supports_number, ordinary_ontology.
  eapply extend_none_value.
  - apply sum_case_none; unfold sum_nm, nat_nm; discriminate.
  - exact option_ontology_supports_number.
Qed.

Lemma ordinary_ontology_supports_booleans : supports_booleans ordinary_ontology.
Proof.
  unfold supports_booleans, ordinary_ontology.
  eapply extend_none_value.
  - apply sum_case_none; unfold sum_nm, bool_nm; discriminate.
  - exact option_ontology_supports_booleans.
Qed.

(** The sum clause declares the sum family at [sum_nm]. *)
Lemma sum_case_registers :
  clause_registers sum_case sum_nm ('K1 sum_abstractor).
Proof. rewrite <- sum_case_compilation; apply tcase_registers. Qed.


Section SumExamples.

Set Default Proof Using "All".
Variable AI : Combination.
Hypothesis AI_supports_sum : supports_sum AI.
Local Abbreviation ontology_5 := AI.

Lemma infer_sum_nm : infer ontology_5 @ sum_nm ==> Sm sum_nm.
Proof.
  unfold sum_nm; eapply infer_tag_free;
    repeat constructor; intros; discriminate.
Qed.

Lemma infer_inleft : forall value witness A B,
  infer ontology_5 @ value ==> Sm A ->
  infer ontology_5 @ witness ==> Sm B ->
  infer ontology_5 @ inleft value witness ==> Sm ('Sum[A,B]).
Proof.
  intros value witness A B Hv Hd; unfold inleft.
  eapply infer_tagged.
  - eapply infer_decorate.
    + infer_tac.
      all: try exact Hv.
      all: eapply infer_tag_free; repeat constructor; intros; discriminate.
    + exact Hd.
  - exact infer_sum_nm.
  - eapply sum_abstractor_supported; [exact AI_supports_sum |].
    apply sum_abstractor_left.
Qed.

Lemma infer_inright : forall witness value A B,
  infer ontology_5 @ witness ==> Sm A ->
  infer ontology_5 @ value ==> Sm B ->
  infer ontology_5 @ inright witness value ==> Sm ('Sum[A,B]).
Proof.
  intros witness value A B Hd Hv; unfold inright.
  eapply infer_tagged.
  - eapply infer_decorate.
    + infer_tac.
      all: try exact Hv.
      all: eapply infer_tag_free; repeat constructor; intros; discriminate.
    + exact Hd.
  - exact infer_sum_nm.
  - eapply sum_abstractor_supported; [exact AI_supports_sum |].
    apply sum_abstractor_right.
Qed.

Lemma sum_is_data : forall C A B,
  infer ontology_5 @ C ==> Sm ('Sum[A,B]) ->
  (exists value witness,
      C = inleft value witness /\
      infer ontology_5 @ value ==> Sm A /\
      infer ontology_5 @ witness ==> Sm B) \/
  (exists witness value,
      C = inright witness value /\
      infer ontology_5 @ witness ==> Sm A /\
      infer ontology_5 @ value ==> Sm B).
Proof.
  intros C A B Hinfer.
  destruct (infer_tagged_result_inv ontology_5 C
    (sum_eliminator A B) sum_nm Hinfer)
    as [c [n [F [-> [Hc [Hn Hdispatch]]]]]].
  assert (Hconstructor : sum_abstractor @ F ==>
    Sm (sum_eliminator A B)).
  { exact (declaration_K1_inv _ _ _ _ _ _ AI_supports_sum Hdispatch). }
  destruct (sum_abstractor_inv F (sum_eliminator A B) Hconstructor)
    as [A0 [B0 [HE [HF | HF]]]].
  all: inversion HE; subst A0 B0; clear HE; subst F.
  - destruct (infer_decorate_inv ontology_5 c
      ('S2['fst,'K1 A]) (B) Hc)
      as [carrier [witness [-> [Hcarrier Hd]]]].
    destruct (infer_S2_K1_inv ontology_5 carrier 'fst A)
      as [value [-> Hv]]; [tag_free_tac | discriminate | exact Hcarrier |].
    assert (n = sum_nm)
      by (eapply infer_tag_free_inv; [exact Hn | tag_free_tac]).
    subst n; left; exists value, witness.
    repeat split; assumption.
  - destruct (infer_decorate_inv ontology_5 c
      ('S2['snd,'K1 B]) (A) Hc)
      as [carrier [witness [-> [Hcarrier Hd]]]].
    destruct (infer_S2_K1_inv ontology_5 carrier 'snd B)
      as [value [-> Hv]]; [tag_free_tac | discriminate | exact Hcarrier |].
    assert (n = sum_nm)
      by (eapply infer_tag_free_inv; [exact Hn | tag_free_tac]).
    subst n; right; exists witness, value.
    repeat split; assumption.
Qed.


End SumExamples.
Set Default Proof Using "Type".


Unset Default Proof Using.
Transparent equal equal1 option_elim sum_left_fields sum_right_fields.

(**********************************************************************)
(* Lists, and polymorphic list programs.                             *)
(**********************************************************************)

(** A list is a plain spine with one tag outside:

      nil_value a   = tagged[swap[KI * (a * Lf)], list_nm]
      [x1,x2,x3]    = tagged[swap[K * (x1 * (x2 * (x3 * Lf)))], list_nm]

    The first element sits where the ghost of nil sits, so a non-empty
    list holds no ghost.  The eliminator of [List[A]] accepts exactly four
    selectors, each handed the payload by the swap:

      List[A] # is_empty ==> Sm Bool       List[A] # tail   ==> Sm List[A]
      List[A] # head     ==> Sm A          List[A] # push A ==> Sm List[A]

    [cons x xs] is the message [xs @ push x].  [tail] of a one-element list
    makes a nil from the element leaving.  The family is sound by typing,
    and every value of [List[A]] is a list ([list_canonical]).

    [list_value d l] is the list of a Rocq list; [cons_value x xs] is the
    tree of [xs @ push x].  The final section exposes single polymorphic
    programs for construction, folds, mapping and filtering. *)

From Stdlib Require Import String List Bool.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans.
Set Default Proof Using "Type".
Open Scope string_scope.
Opaque equal.

Definition list_nm : Combination := 'K1 Lf.
Local Opaque equal1.

(** ** Support for the list family *)
Lemma tagger_eval : forall n x, 'tagger[n] @ x ==> 'tagged[x,n].
Proof. intros; evaluate. Qed.

Ltac d_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval | apply path_eval | apply tagged_fun_eval
            | apply tagger_eval ]
  end.
Ltac d_eval :=
  first [ d_atom | evaluate_expr_core d_eval d_head | idtac ]
with d_head :=
  first [ d_atom | evaluate_head_core d_eval | idtac ].

(** Run-time constants: [mk c n] ignores its argument and tags [c] at [n]
    when it runs, so it contains no tag. *)
Definition mk (c n : Combination) : Combination := 'S2['K1 ('tagger[n]), 'K1 c].
Lemma mk_eval : forall c n x, mk c n @ x ==> 'tagged[c,n].
Proof. intros; unfold mk; evaluate. Qed.

Lemma type_app_tagger : forall AI n C E,
  AI @ n @r type_app AI @r C ==> Sm E ->
  type_app AI @ 'tagger[n] @r C ==> Sm ('tagged[E,n]).
Proof.
  intros AI n C E H.
  new_S; [discriminate| | |].
  - new_S; [discriminate|apply type_app_K_ev| |].
    + new_S; [discriminate|apply type_app_K_ev|apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate|].
      apply type_app_leaf_ev.
    + apply type_app_leaf_ev.
  - new_S; [discriminate|apply type_app_K_ev|apply type_app_K_ev|].
    new_S; [discriminate| | |].
    + apply type_app_K_ev.
    + apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
    + apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
  - apply type_app_stem_ev; apply type_app_stem_tagged; exact H.
Qed.

Lemma type_app_mk : forall AI c n U E,
  AI @ n @r type_app AI @r c ==> Sm E ->
  type_app AI @ mk c n @r U ==> Sm ('tagged[E,n]).
Proof.
  intros; unfold mk; new_S; [discriminate|apply type_app_K_ev|apply type_app_K_ev|].
  apply type_app_tagger; assumption.
Qed.

Definition mk_tt := mk 'fst bool_nm.
Definition mk_ff := mk 'snd bool_nm.
Definition mk_Bool := mk bool_eliminator bool_nm.
Lemma mk_tt_eval : forall x, mk_tt @ x ==> 'tt.
Proof. intros; apply mk_eval. Qed.
Lemma mk_ff_eval : forall x, mk_ff @ x ==> 'ff.
Proof. intros; apply mk_eval. Qed.
Lemma mk_Bool_eval : forall x, mk_Bool @ x ==> 'Bool.
Proof. intros; apply mk_eval. Qed.
Lemma type_app_tt_like : forall AI U,
  supports_booleans AI -> type_app AI @ mk_tt @r U ==> Sm ('Bool).
Proof.
  intros AI U HB; unfold mk_tt; apply type_app_mk; eapply bool_abstractor_supported; [exact HB|apply bool_abstractor_fst].
Qed.
Lemma type_app_ff_like : forall AI U,
  supports_booleans AI -> type_app AI @ mk_ff @r U ==> Sm ('Bool).
Proof.
  intros AI U HB; unfold mk_ff; apply type_app_mk; eapply bool_abstractor_supported; [exact HB|apply bool_abstractor_snd].
Qed.

Definition swap_t u := ''S2[Val 'I, ''K1 u].
Lemma type_app_swap2 : forall AI P F R,
  type_app AI @ F @r P ==> R -> type_app AI @ swap P @r F ==> R.
Proof.
  intros AI P F R H; unfold swap;
  new_S; [discriminate|apply type_app_I|apply type_app_K_ev|exact H].
Qed.
Lemma infer_swap : forall AI p P,
  infer AI @ p ==> Sm P -> infer AI @ swap p ==> Sm (swap P).
Proof. intros; unfold swap; infer_tac. Qed.
Lemma infer_wait : forall AI M N M' N',
  infer AI @ M ==> Sm M' -> infer AI @ N ==> Sm N' ->
  infer AI @ 'wait[M,N] ==> Sm ('wait[M',N']).
Proof.
  intros AI M N M' N' HM HN.
  assert (HI := infer_I AI).
  eapply infer_fork.
  - apply infer_stem; eapply infer_fork;
      [apply infer_stem; apply infer_K1; exact HM|apply infer_K1; exact HN|].
    apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
  - exact HI.
  - apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
Qed.
Lemma tagged_fun_direct : forall (AI : Decl) F U V,
  type_app AI @ F @r U ==> Sm V ->
  type_app AI @ tagged_fun @r 'decorate[F,U] ==> Sm (U --> V).
Proof.
  intros; unfold tagged_fun; apply type_app_tagger; apply function_declared.
  apply function_abstractor_direct_eval; assumption.
Qed.

(** The routine steps of type application on compiled programs. *)
Ltac ty_onto_more := fail.
Ltac ty_onto := first
  [ ty_onto_more
  | eapply nat_abstractor_supported;
      [eassumption|first [apply nat_abstractor_zero|apply nat_abstractor_succ]] ].
Ltac ty_elim_more := fail.
Ltac ty_unfold_more := fail.
Ltac ty_elim :=
  first
  [ ty_elim_more
  | apply funty_eliminator_eval
  | apply bool_eliminator_some
  | apply nat_eliminator_eval
  | apply option_eliminator_eval
  | apply sum_eliminator_eval ].
Ltac ty_atom :=
  first
  [ apply type_app_tt_like; assumption
  | apply type_app_ff_like; assumption
  | apply tagged_fun_direct
  | apply type_app_tagged_fun_recursive ].
Ltac ty :=
  lazymatch goal with
  | |- type_app ?AI @ ?T @r ?U ==> _ =>
    first [is_evar T; fail 1 | idtac];
    first
    [ eassumption
    | lazymatch T with
      | mk_tt => ty_atom
      | mk_ff => ty_atom
      | tagged_fun => ty_atom
      | nat_split => unfold nat_split
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | _ --> _ => apply type_app_abstract; ty_elim
      | 'tagger[?n] => apply type_app_tagger; ty_onto
      | 'tagged[?E,?N] => apply type_app_abstract; ty_elim
      | Lf => apply type_app_leaf_ev
      | Fk Lf _ => apply type_app_K_ev
      | 'I => apply type_app_I
      | Sm _ => apply type_app_stem_ev;
          first [apply type_app_stem_function
                |apply type_app_stem_recursive_function
                |apply type_app_stem_structural; solve [intros; discriminate]
                |apply type_app_stem_tagged; ty_onto]
      | Fk (Sm _) _ => new_S; [solve [intros; discriminate] | | |]
      end ]
  end.

Local Transparent nat_split nat_pred.
Lemma infer_nat_split : forall AI, infer AI @ nat_split ==> Sm nat_split.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

(** [nat_ge (a * b)] tests a >= b.  It is a fold: [a] removes [a]
    successors from [b] by [nat_pred], and a zero remainder gives true.  It
    builds its Booleans at run time, so it is tag-free and its own type. *)
Definition nat_ge := Eval cbn -[nat_pred mk_tt mk_ff] in to_tree
  (star "p" (((Val 'fst @@ Ref "p") @@ ((Val 'snd @@ Ref "p") ''* Val nat_pred))
    @@ ((Val mk_tt @@ Ref "p") ''* ''K1 (Val mk_ff @@ Ref "p")))).

Goal tag_free nat_ge = true. Proof. vm_compute; reflexivity. Qed.

Lemma nat_ge_pred_fold : forall a b,
  numeral a @ (numeral b '* nat_pred) ==> numeral (b - a).
Proof.
  induction a as [|a IH]; intros b; cbn [numeral].
  - replace (b - 0) with b by lia; apply zero_apply.
  - eapply succ_apply; [apply IH|].
    replace (b - S a) with (pred_num (b - a)) by (unfold pred_num; destruct (b - a) eqn:E; lia).
    apply nat_pred_numeral.
Qed.

Lemma nat_ge_numerals : forall a b,
  nat_ge @ (numeral a '* numeral b) ==> (if Nat.leb b a then 'tt else 'ff).
Proof.
  intros a b.
  pose proof (nat_ge_pred_fold a b) as HF.
  pose proof (mk_tt_eval (numeral a '* numeral b)) as HT.
  pose proof (mk_ff_eval (numeral a '* numeral b)) as HE.
  assert (HR : numeral (b - a) @ ('tt '* 'K1 'ff) ==> (if Nat.leb b a then 'tt else 'ff)).
  { destruct (Nat.leb b a) eqn:E.
    - apply PeanoNat.Nat.leb_le in E; replace (b - a) with 0 by lia; apply zero_apply.
    - apply PeanoNat.Nat.leb_gt in E; destruct (b - a) as [|k] eqn:Ek; [lia|].
      apply numeral_K1_fold. }
  unfold nat_ge; cbn -[nat_pred mk_tt mk_ff].
  destruct (eval_pair_inv _ _ _ HF) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  evaluate.
Qed.

Section NumberComparisonTyping.
Set Default Proof Using "All".
Variable AI : Decl.
Hypothesis HN : supports_number AI.
Hypothesis HB : supports_booleans AI.

Local Ltac number_type_step := ty.
Local Ltac number_infer_step := first
  [ eassumption
  | apply tt_infer; exact HB
  | apply ff_infer; exact HB
  | apply infer_zero; exact HN
  | apply infer_nat_split
  | eapply infer_lam; [ | |]
  | eapply infer_fork | apply infer_stem | apply infer_leaf ].
Lemma infer_nat_ge : infer AI @ nat_ge ==> Sm nat_ge.
Proof using. apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma type_app_nat_ge : type_app AI @ nat_ge @r ('Nat '* 'Nat) ==> Sm ('Bool).
Proof using AI HN HB.
  assert (HP : type_app AI @ nat_pred @r 'Nat ==> Sm ('Nat)) by (repeat ty).
  unfold nat_ge; repeat ty.
Qed.
End NumberComparisonTyping.

(** ** Addition and multiplication on pairs

    Both are folds, as [append] is: the number carries the recursion, and
    no function type appears.  The base of [mul] is made by [mk_zero], so
    that the program is its own type. *)
Definition succ_step := Eval cbn in to_tree
  (star "r" (Val ('tagger[nat_nm]) @@ ''S2[Val 'snd, Ref "r"])).
Definition add := Eval cbn -[succ_step] in to_tree (star "p"
  ((Val 'fst @@ Ref "p") @@ ((Val 'snd @@ Ref "p") ''* Val succ_step))).
Definition mul := Eval cbn -[add mk_zero] in to_tree (star "p"
  ((Val 'fst @@ Ref "p") @@ ((Val mk_zero @@ Ref "p") ''*
    star "r" (Val add @@ ((Val 'snd @@ Ref "p") ''* Ref "r"))))).

Goal concreteb add = true. Proof. vm_compute; reflexivity. Qed.
Goal concreteb mul = true. Proof. vm_compute; reflexivity. Qed.

Lemma succ_step_eval : forall r, succ_step @ r ==> succ r.
Proof. intros; unfold succ_step, succ; cbn; evaluate. Qed.

Lemma add_eval : forall m n r, m @ (n '* succ_step) ==> r -> add @ (m '* n) ==> r.
Proof. intros m n r H; unfold add; d_eval. Qed.
Lemma add_numeral_fold : forall j k,
  numeral j @ (numeral k '* succ_step) ==> numeral (j + k).
Proof.
  induction j as [|j IH]; intros k; cbn [numeral Nat.add].
  - apply zero_apply.
  - eapply succ_apply; [apply IH|apply succ_step_eval].
Qed.
Lemma add_numerals : forall j k, add @ (numeral j '* numeral k) ==> numeral (j + k).
Proof. intros; apply add_eval, add_numeral_fold. Qed.

(** The step of [mul] at [n], as a value of the run. *)
Definition mul_step n := Eval cbn -[add] in to_tree
  (star "r" (Val add @@ (Val n ''* Ref "r"))).
Lemma mul_step_eval : forall n r v, add @ (n '* r) ==> v -> mul_step n @ r ==> v.
Proof. intros n r v H; unfold mul_step; cbn -[add]; d_eval. Qed.
Lemma mul_eval : forall m n r, m @ (zero '* mul_step n) ==> r -> mul @ (m '* n) ==> r.
Proof.
  intros m n r H; pose proof (mk_zero_eval (m '* n)) as HZ.
  unfold mul, mul_step in *; cbn -[add mk_zero] in *; d_eval.
Qed.
Lemma mul_numeral_fold : forall j k,
  numeral j @ (zero '* mul_step (numeral k)) ==> numeral (j * k).
Proof.
  induction j as [|j IH]; intros k; cbn [numeral Nat.mul].
  - apply zero_apply.
  - eapply succ_apply; [apply IH|apply mul_step_eval; apply add_numerals].
Qed.
Lemma mul_numerals : forall j k, mul @ (numeral j '* numeral k) ==> numeral (j * k).
Proof. intros; apply mul_eval, mul_numeral_fold. Qed.

Lemma type_app_succ_step : forall AI, supports_number AI ->
  type_app AI @ succ_step @r ('Nat) ==> Sm ('Nat).
Proof. intros AI HN; unfold succ_step; repeat ty. Qed.
Lemma type_app_add : forall AI, supports_number AI ->
  type_app AI @ add @r ('Nat '* 'Nat) ==> Sm ('Nat).
Proof.
  intros AI HN; pose proof (type_app_succ_step AI HN) as HC.
  unfold add; repeat ty.
Qed.
Lemma type_app_mul : forall AI, supports_number AI ->
  type_app AI @ mul @r ('Nat '* 'Nat) ==> Sm ('Nat).
Proof.
  intros AI HN; pose proof (type_app_add AI HN) as HC.
  unfold mul; repeat ty.
Qed.
Lemma infer_add : forall AI, infer AI @ add ==> Sm add.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma infer_mul : forall AI, infer AI @ mul ==> Sm mul.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

(** [add] and [mul] are their own types, and take two numbers to a number. *)
Theorem add_typed : forall AI, supports_number AI ->
  infer AI @ add ==> Sm add /\ type_app AI @ add @r ('Nat '* 'Nat) ==> Sm ('Nat).
Proof. intros AI HN; split; [apply infer_add|apply type_app_add; exact HN]. Qed.
Theorem mul_typed : forall AI, supports_number AI ->
  infer AI @ mul ==> Sm mul /\ type_app AI @ mul @r ('Nat '* 'Nat) ==> Sm ('Nat).
Proof. intros AI HN; split; [apply infer_mul|apply type_app_mul; exact HN]. Qed.

(** [rec_f inner s @ p] runs a fixed point built under [\p]: both ghosts
    are made from [p], a value of the domain.  The seed [s] is a program
    of the domain to the codomain, not a function value, and no value of
    the codomain is needed. *)
Definition fix_rt (f : Term) : Term := Val tagged_fun @@ Z2 (f ''C Val tagged_fun).

Definition rec_rfun := Eval cbn -[tagged_fun] in to_tree
  (star "i" (star "p" (star "r" (lam_rt (''wait[Ref "i", Ref "r"]) (Ref "p"))))).
Definition rec_c := Eval cbn -[tagged_fun rec_rfun] in to_tree
  (star "i" (star "s" (star "p"
    (fix_rt (lam_rt (''wait2[Val rec_rfun, Ref "i", Ref "p"]) (lam_rt (Ref "s") (Ref "p")))
     @@ Ref "p")))).
Definition rec_f (inner s : Combination) := 'wait2[rec_c, inner, s].
Definition rec_loop inner s g :=
  fix_function (lam ('wait2[rec_rfun, inner, g]) (lam s g)).

Lemma rec_loop_step : forall inner s g q v,
  inner @ rec_loop inner s g @r q ==> v -> rec_loop inner s g @ q ==> v.
Proof.
  intros inner s g q v H; unfold rec_loop at 1; apply fix_function_eval_step.
  inv_out H.
  eapply eval_appl.
  - apply lam_eval; apply wait2_eval; unfold rec_rfun; fold (rec_loop inner s g); d_eval.
  - apply tagged_eval; apply wait_eval; d_eval.
Qed.

Lemma rec_f_eval : forall inner s p v,
  rec_loop inner s p @ p ==> v -> rec_f inner s @ p ==> v.
Proof.
  intros inner s p v H; unfold rec_loop, fix_function, lam, Z in H.
  unfold rec_f; apply wait2_eval; unfold rec_c; d_eval.
Qed.

(** The recursion principle. *)
Lemma rec_f_typed : forall (AI : Decl) inner s U V W,
  type_app AI @ s @r U ==> Sm V ->
  type_app AI @ inner @r (U --> V) ==> Sm W ->
  type_app AI @ W @r U ==> Sm V ->
  type_app AI @ rec_f inner s @r U ==> Sm V.
Proof.
  intros AI inner s U V W Hs Hi Hw; unfold rec_f, rec_c, rec_rfun.
  repeat ty.
Qed.

(** ** Lists are folds

    [nil[a] @ (b * f) = b] and [cons[x,t] @ (b * f) = f @ (x * (t @ (b * f)))].
    The ghost of a nil sits in a decoration, which application discards,
    so no program can read it.  The carrier of a cons holds its tail, a
    list, so a non-empty list keeps the ghost of its nil at the bottom. *)
Definition nil_value a := 'tagged['decorate['fst,a], list_nm].

(** The carrier of a cons is the delay of one program at the pair of the
    head and the tail: given [b * f], the step gets the head and the fold
    of the tail.  So the pair is a subtree of the carrier, where a
    traversal finds it, and the abstractor reads [A] from its shape. *)
Definition cell_run := Eval cbn in to_tree
  (star "c" (star "p" ((Val 'snd @@ Ref "p") @@
    ((Val 'fst @@ Ref "c") ''* ((Val 'snd @@ Ref "c") @@ Ref "p"))))).
Definition cell_carrier x t := 'wait[cell_run, x '* t].
Definition cell_carrier_t (x t : Term) : Term := ''wait[Val cell_run, x ''* t].
Definition cell x t := 'tagged[cell_carrier x t, list_nm].
Definition cons_value x xs := cell x xs.

Fixpoint list_value d (l : list Combination) : Combination :=
  match l with
  | List.nil => nil_value d
  | List.cons x l' => cell x (list_value d l')
  end.

Notation "'nil [ a ]" := (nil_value a) (at level 0, only parsing).
Notation "'cons [ x , xs ]" := (cons_value x xs) (at level 0, only parsing).

Lemma list_value_cons : forall d x l,
  list_value d (List.cons x l) = cons_value x (list_value d l).
Proof. reflexivity. Qed.

Lemma nil_apply : forall a b f, nil_value a @ (b '* f) ==> b.
Proof. intros; unfold nil_value; apply tagged_eval; apply wait_eval; evaluate. Qed.
Lemma cell_apply : forall x t b f r v,
  t @ (b '* f) ==> r -> f @ (x '* r) ==> v -> cell x t @ (b '* f) ==> v.
Proof.
  intros x t b f r v Ht Hf; unfold cell, cell_carrier; apply tagged_eval; apply wait_eval.
  unfold cell_run; inv_out Hf; d_eval.
Qed.

(** ** The eliminator: one step of the fold, by type application *)
Definition list_step_check := Eval cbn in to_tree
  (star "A" (star "a" (star "U" (star "F"
    (''onStem1 (star "V" (Val equal @@ Ref "V" @@ Ref "U" @@ (Val Lf @@ Ref "U") @@ Val Lf))
      @@ (Ref "a" @@ Ref "F" @@ (Ref "A" ''* Ref "U"))))))).

Lemma list_step_check_eval : forall A a U F,
  a @ F @r (A '* U) ==> Sm U -> list_step_check @ A @r a @r U @r F ==> Sm U.
Proof.
  intros A a U F H; inv_out H.
  unfold list_step_check; cbn; d_eval0.
Qed.
Lemma list_step_check_inv : forall A a B F U,
  list_step_check @ A @r a @r B @r F ==> Sm U ->
  B = U /\ a @ F @r (A '* U) ==> Sm U.
Proof.
  intros A a B F U H; unfold list_step_check in H; cbn in H.
  inv_out H; invert_eval.
  all: match goal with
  | H1 : equal @ ?V ==> ?e, H2 : ?e @ ?W ==> ?b |- _ =>
    assert (Hequal : equal @ V @r W ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ Hequal) as [[Hv0 Heq] | [Hv0 Hneq]]; subst b; invert_eval
  end.
  all: subst; split; [reflexivity|]; eapply eval_appl; eassumption.
Qed.

Definition list_elim := Eval cbn in to_tree
  (star "A" (star "a"
    (''onStem1
      (''onStem1
        (''onFork1 (''wait2[Val list_step_check, Ref "A", Ref "a"]))
        ''C Val get_product_parameters)
      ''C Val get_S_fields))).
Definition list_eliminator A := 'wait[list_elim, A].
Notation "'List [ A ]" := ('tagged[list_eliminator A, list_nm]) (at level 0).

Lemma list_eliminator_app : forall A a X V,
  list_eliminator A @ a @r X ==> V <-> fold_core ('wait2[list_step_check, A, a]) @ X ==> V.
Proof.
  intros A a X V.
  assert (Hh : list_eliminator A @ a ==> fold_core ('wait2[list_step_check, A, a])).
  { unfold list_eliminator; apply wait_eval; unfold list_elim, fold_core; cbn; evaluate. }
  split; intro H.
  - destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hwu]]]]; inv_out Hu.
    pose proof (eval_deterministic _ _ Hw _ Hh); subst w; exact Hwu.
  - eapply eval_appl; [exact Hh|exact H].
Qed.
Lemma list_eliminator_eval : forall A a U F,
  a @ F @r (A '* U) ==> Sm U -> list_eliminator A @ a @r (U '* F) ==> Sm U.
Proof.
  intros A a U F H; apply list_eliminator_app; apply fold_core_eval.
  destruct (eval_app_r_inv _ _ _ (list_step_check_eval A a U F H)) as [w [Hw Hv]].
  eapply eval_appl; [apply wait2_eval; exact Hw|exact Hv].
Qed.
Lemma list_eliminator_inv : forall A a X V,
  list_eliminator A @ a @r X ==> Sm V ->
  exists F, X = V '* F /\ a @ F @r (A '* V) ==> Sm V.
Proof.
  intros A a X V H; apply list_eliminator_app, fold_core_inv in H.
  destruct H as [U [F [-> H]]].
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]]; apply wait2_eval_inv in Hw.
  pose proof (eval_appl _ _ _ _ _ Hw Hv) as H'; apply list_step_check_inv in H'.
  destruct H' as [-> H']; eexists; split; [reflexivity|exact H'].
Qed.

(** ** The abstractor

    It reads [A] from the shape of the carrier, rebuilds the carrier and
    compares; the type [List[A]] in a cons carrier is rebuilt at run time,
    so no abstract type sits in the declarations. *)
Definition path_cell : list dir := List.app path_arg path_arg.
Definition acc_cell := path_prog path_cell.

Definition list_abstractor :=
  Eval cbn -[acc_arg acc_cell list_elim equal] in to_tree
  (star "C"
    ((star "e" (star "a" (star "x"
      (Ref "e" @@ ''decorate[Val 'fst, Ref "a"]
        @@ (Val Lf @@ ''wait[Val list_elim, Ref "a"])
        @@ (Ref "e" @@ cell_carrier_t (Ref "x")
                (Val ('tagger[list_nm]) @@ ''wait[Val list_elim, Ref "x"])
            @@ (Val Lf @@ ''wait[Val list_elim, Ref "x"]) @@ Val Lf)))))
     @@ (op equal @@ Ref "C") @@ (op acc_arg @@ Ref "C") @@ (op acc_cell @@ Ref "C"))).

Goal concreteb list_abstractor = true.
Proof. vm_compute; reflexivity. Qed.

Definition list_abstractor_result C :=
  let a := path_fn path_arg C in let x := path_fn path_cell C in
  if ceqb C ('decorate['fst,a]) then Sm (list_eliminator a) else
  if ceqb C (cell_carrier x ('List[x])) then Sm (list_eliminator x) else Lf.

Lemma list_abstractor_eval : forall C, list_abstractor @ C ==> list_abstractor_result C.
Proof.
  intros C; unfold list_abstractor_result; cbv zeta.
  pose proof (path_eval path_arg C) as HA; pose proof (path_eval path_cell C) as HB.
  fold acc_arg in HA; fold acc_cell in HB.
  set (a := path_fn path_arg C) in *; set (x := path_fn path_cell C) in *; clearbody a x.
  pose proof (equal_eval C) as He.
  destruct (equal1_bt_case C ('decorate['fst,a])) as [[_ [E1 H1]]|[_ [E1 H1]]];
  destruct (equal1_bt_case C (cell_carrier x ('List[x]))) as [[_ [E2 H2]]|[_ [E2 H2]]];
  rewrite ?E1, ?E2; unfold cell_carrier, list_eliminator in *;
  unfold list_abstractor; d_eval.
Qed.

Lemma list_abstractor_nil : forall A,
  list_abstractor @ 'decorate['fst,A] ==> Sm (list_eliminator A).
Proof.
  intros; pose proof (list_abstractor_eval ('decorate['fst,A])) as H;
    unfold list_abstractor_result in H; cbv zeta in H.
  replace (path_fn path_arg ('decorate['fst,A])) with A in H by reflexivity.
  rewrite ceqb_refl in H; exact H.
Qed.
Lemma list_abstractor_cons : forall A,
  list_abstractor @ cell_carrier A ('List[A]) ==> Sm (list_eliminator A).
Proof.
  intros A; pose proof (list_abstractor_eval (cell_carrier A ('List[A]))) as H;
    unfold list_abstractor_result in H; cbv zeta in H.
  replace (path_fn path_cell (cell_carrier A ('List[A]))) with A in H by reflexivity.
  rewrite ceqb_false in H; [|unfold cell_carrier, cell_run; intro HE; discriminate HE].
  rewrite ceqb_refl in H; exact H.
Qed.

(** It accepts exactly the two carriers. *)
Lemma list_abstractor_inv : forall C E,
  list_abstractor @ C ==> Sm E ->
  exists A, E = list_eliminator A /\
    (C = 'decorate['fst,A] \/ C = cell_carrier A ('List[A])).
Proof.
  intros C E H.
  pose proof (eval_deterministic _ _ H _ (list_abstractor_eval C)) as HE.
  unfold list_abstractor_result in HE; cbv zeta in HE.
  destruct (ceqb C ('decorate['fst,path_fn path_arg C])) eqn:E1.
  - apply ceqb_true in E1; inversion HE; eauto.
  - destruct (ceqb C (cell_carrier _ _)) eqn:E2; [|discriminate].
    apply ceqb_true in E2; inversion HE; eauto.
Qed.

Definition supports_list AI := AI @ list_nm ==> ('K1 (list_abstractor)).

Lemma list_abstractor_supported : forall AI a C E,
  supports_list AI -> list_abstractor @ C ==> Sm E -> AI @ list_nm @r a @r C ==> Sm E.
Proof. intros; eapply declaration_apply; eassumption. Qed.

Ltac ty_onto_more ::=
  eapply list_abstractor_supported;
    [eassumption|first [apply list_abstractor_nil|apply list_abstractor_cons]].
Ltac ty_elim_more ::= apply list_eliminator_eval.
Lemma type_app_List : forall AI A B F,
  type_app AI @ F @r (A '* B) ==> Sm B ->
  type_app AI @ ('List[A]) @r (B '* F) ==> Sm B.
Proof. intros; apply type_app_abstract; apply list_eliminator_eval; assumption. Qed.

(** Soundness by typing: one step of the fold. *)
Lemma list_abstractor_sound : forall AI,
  abstractor_sound_by_typing AI list_abstractor.
Proof.
  intros AI C E U V HC HE.
  destruct (list_abstractor_inv _ _ HC) as [A [-> [->| ->]]];
    destruct (list_eliminator_inv _ _ _ _ HE) as [F [-> HF]].
  - eapply type_app_wait; [apply type_app_K_ev|apply type_app_fst_product].
  - pose proof (type_app_List AI A V F HF) as HL.
    unfold cell_carrier, cell_run; repeat ty.
Qed.
Lemma list_abstractor_value_sound : forall AI, sound_abstractor AI list_abstractor.
Proof. intros; apply sound_by_typing_implies_sound, list_abstractor_sound. Qed.

Lemma infer_list_nm : forall AI, infer AI @ list_nm ==> Sm list_nm.
Proof. intros; apply infer_tag_free; tag_free_tac. Qed.

Lemma infer_nil_value : forall AI a A, supports_list AI -> infer AI @ a ==> Sm A ->
  infer AI @ nil_value a ==> Sm ('List[A]).
Proof.
  intros AI a A HL Ha; unfold nil_value; eapply infer_tagged.
  - apply infer_decorate; [apply infer_tag_free; tag_free_tac|exact Ha].
  - apply infer_list_nm.
  - apply list_abstractor_supported; [exact HL|apply list_abstractor_nil].
Qed.

Lemma infer_cell_carrier : forall AI x t X T,
  infer AI @ x ==> Sm X -> infer AI @ t ==> Sm T ->
  infer AI @ cell_carrier x t ==> Sm (cell_carrier X T).
Proof.
  intros; unfold cell_carrier; apply infer_wait;
    [apply infer_tag_free; vm_compute; reflexivity|apply infer_product_value; assumption].
Qed.

Lemma infer_cons_value : forall AI x xs A, supports_list AI ->
  infer AI @ x ==> Sm A -> infer AI @ xs ==> Sm ('List[A]) ->
  infer AI @ cons_value x xs ==> Sm ('List[A]).
Proof.
  intros AI x xs A HL Hx Hxs; unfold cons_value, cell; eapply infer_tagged.
  - apply infer_cell_carrier; eassumption.
  - apply infer_list_nm.
  - apply list_abstractor_supported; [exact HL|apply list_abstractor_cons].
Qed.

Lemma infer_list_value : forall AI d A l, supports_list AI -> infer AI @ d ==> Sm A ->
  List.Forall (fun x => infer AI @ x ==> Sm A) l ->
  infer AI @ list_value d l ==> Sm ('List[A]).
Proof.
  intros AI d A l HL Hd Hl; induction Hl; cbn [list_value].
  - apply infer_nil_value; assumption.
  - apply infer_cons_value; assumption.
Qed.

Definition list_eliminator_builder := Eval cbn in to_tree
  (star "A" (''wait[Val list_elim,Ref "A"])).
Lemma list_eliminator_builder_eval : forall A,
  list_eliminator_builder @ A ==> list_eliminator A.
Proof. intros; unfold list_eliminator_builder, list_eliminator; cbn; evaluate. Qed.

(** The clause of the declarations. *)
Definition list_case_package :
  { t : Combination |
    to_tree (tcase (Val list_nm) (Val ('K1 list_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition list_case := Eval cbn -[list_abstractor] in proj1_sig list_case_package.
Lemma list_case_compilation :
  to_tree (tcase (Val list_nm) (Val ('K1 list_abstractor))) = list_case.
Proof. reflexivity. Qed.
Lemma list_case_some : list_case @ list_nm ==> Sm ('K1 list_abstractor).
Proof. rewrite <- list_case_compilation; apply tcase_eq. Qed.
Lemma list_case_none : forall N, N <> list_nm -> list_case @ N ==> Lf.
Proof.
  intros N Hneq; rewrite <- list_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.
Lemma list_case_registers : clause_registers list_case list_nm ('K1 list_abstractor).
Proof. rewrite <- list_case_compilation; apply tcase_registers. Qed.

(** ** Folds *)
Definition foldright_value step base := swap (base '* step).
Lemma foldright_value_eval : forall step base xs r,
  xs @ (base '* step) ==> r -> foldright_value step base @ xs ==> r.
Proof. intros; unfold foldright_value, swap; inv_out H; evaluate. Qed.
Lemma foldright_value_inv : forall step base xs r,
  foldright_value step base @ xs ==> r -> xs @ (base '* step) ==> r.
Proof. intros step base xs r H; unfold foldright_value, swap in H; invert_eval. Qed.

(** The run of a right fold over a list of elements. *)
Inductive right_to (st b : Combination) : list Combination -> Combination -> Prop :=
| right_nil : right_to st b List.nil b
| right_cons : forall x l r s,
    right_to st b l r -> st @ (x '* r) ==> s -> right_to st b (List.cons x l) s.
Lemma fold_list : forall st b d l r, right_to st b l r ->
  list_value d l @ (b '* st) ==> r.
Proof.
  intros st b d l r H; induction H; cbn [list_value];
    [apply nil_apply|eapply cell_apply; eassumption].
Qed.
Lemma foldright_list : forall st b d l r, right_to st b l r ->
  foldright_value st b @ list_value d l ==> r.
Proof. intros; apply foldright_value_eval; apply fold_list; assumption. Qed.
Lemma foldright_value_nil : forall step base d,
  foldright_value step base @ nil_value d ==> base.
Proof. intros; apply foldright_value_eval; apply nil_apply. Qed.

Lemma type_app_foldright_value : forall AI F B A,
  type_app AI @ F @r (A '* B) ==> Sm B ->
  type_app AI @ foldright_value F B @r 'List[A] ==> Sm B.
Proof.
  intros AI F B A H; unfold foldright_value; apply type_app_swap2.
  apply type_app_List; exact H.
Qed.
Lemma infer_foldright_value : forall AI step base F B,
  infer AI @ step ==> Sm F -> infer AI @ base ==> Sm B ->
  infer AI @ foldright_value step base ==> Sm (foldright_value F B).
Proof.
  intros; unfold foldright_value; apply infer_swap; apply infer_product_value; assumption.
Qed.

(** ** Cons and append *)
Definition cons_step := Eval cbn in to_tree
  (star "p" (Val ('tagger[list_nm]) @@ cell_carrier_t (Val 'fst @@ Ref "p") (Val 'snd @@ Ref "p"))).
Definition cons2 x xs := Val cons_step @@ (x ''* xs).
Definition append := Eval cbn -[cons_step] in to_tree (star "p"
  ((Val 'fst @@ Ref "p") @@ ((Val 'snd @@ Ref "p") ''* Val cons_step))).

Goal concreteb append = true. Proof. vm_compute; reflexivity. Qed.

Lemma cons_step_eval : forall x xs, cons_step @ (x '* xs) ==> cons_value x xs.
Proof. intros; unfold cons_step, cons_value, cell, cell_carrier; cbn; evaluate. Qed.

Lemma type_app_cons_step : forall AI A, supports_list AI ->
  type_app AI @ cons_step @r (A '* 'List[A]) ==> Sm ('List[A]).
Proof. intros AI A HL; unfold cons_step; repeat ty. Qed.

Lemma infer_append : forall AI, infer AI @ append ==> Sm append.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma infer_cons_step : forall AI, infer AI @ cons_step ==> Sm cons_step.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

Lemma type_app_append : forall AI A, supports_list AI ->
  type_app AI @ append @r ('List[A] '* 'List[A]) ==> Sm ('List[A]).
Proof.
  intros AI A HL; pose proof (type_app_cons_step AI A HL) as HC.
  unfold append; repeat ty.
Qed.

(** [append] is its own type, and takes a pair of lists to a list at every
    element type.  The list carries the recursion: it takes no value of
    [A], and no function type appears. *)
Theorem append_polymorphic : forall AI, supports_list AI ->
  infer AI @ append ==> Sm append /\
  forall A, type_app AI @ append @r ('List[A] '* 'List[A]) ==> Sm ('List[A]).
Proof. intros AI HL; split; [apply infer_append|intros; apply type_app_append; exact HL]. Qed.

Theorem infer_append_application : forall (AI : Decl) xs ys A, supports_list AI ->
  infer AI @ xs ==> Sm ('List[A]) -> infer AI @ ys ==> Sm ('List[A]) ->
  infer_expression AI @ (append @ (xs '* ys)) ==> Sm ('List[A]).
Proof.
  intros AI xs ys A HL Hx Hy; eapply infer_application;
    [apply infer_append|apply infer_product_value; eassumption|apply type_app_append; exact HL].
Qed.

Lemma append_right : forall l ys,
  right_to cons_step ys l (fold_right cons_value ys l).
Proof.
  induction l as [|x l IH]; intros ys; cbn [fold_right]; econstructor;
    [apply IH|apply cons_step_eval].
Qed.
Lemma fold_right_cons_app : forall l e m,
  fold_right cons_value (list_value e m) l = list_value e (List.app l m).
Proof. induction l as [|x l IH]; intros; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.
Lemma append_eval : forall xs ys r,
  xs @ (ys '* cons_step) ==> r -> append @ (xs '* ys) ==> r.
Proof. intros xs ys r H; unfold append; d_eval. Qed.
Lemma append_list : forall l d e m,
  append @ (list_value d l '* list_value e m) ==> list_value e (List.app l m).
Proof.
  intros; rewrite <- fold_right_cons_app; apply append_eval; apply fold_list; apply append_right.
Qed.

(** Left identity, for any second argument. *)
Lemma append_nil : forall a ys, append @ (nil_value a '* ys) ==> ys.
Proof. intros; apply append_eval; apply nil_apply. Qed.
(** Right identity: the elements stay, and the ghost is that of the second. *)
Lemma append_nil_right : forall d l b,
  append @ (list_value d l '* nil_value b) ==> list_value b l.
Proof.
  intros d l b; pose proof (append_list l d b List.nil) as H.
  rewrite List.app_nil_r in H; exact H.
Qed.
(** On two empties the result is the second. *)
Lemma append_empties : forall a b, append @ (nil_value a '* nil_value b) ==> nil_value b.
Proof. intros; apply append_nil. Qed.
(** Associativity is exact, for all lists. *)
Lemma append_assoc : forall d e f l m n,
  append @ (list_value d l '* list_value e m) ==> list_value e (List.app l m) /\
  append @ (list_value e m '* list_value f n) ==> list_value f (List.app m n) /\
  append @ (list_value e (List.app l m) '* list_value f n) ==> list_value f (List.app (List.app l m) n) /\
  append @ (list_value d l '* list_value f (List.app m n)) ==> list_value f (List.app (List.app l m) n).
Proof.
  intros; repeat split; try apply append_list.
  rewrite <- List.app_assoc; apply append_list.
Qed.

Definition is_list xs := exists d l, xs = list_value d l.
Lemma is_list_nil : forall d, is_list (nil_value d).
Proof. intros; exists d, List.nil; reflexivity. Qed.
Lemma is_list_cons : forall x xs, is_list xs -> is_list (cons_value x xs).
Proof. intros x xs [d [l ->]]; exists d, (List.cons x l); reflexivity. Qed.

Lemma append_cons : forall x xs ys zs, is_list xs -> is_list ys ->
  append @ (xs '* ys) ==> zs -> append @ (cons_value x xs '* ys) ==> cons_value x zs.
Proof.
  intros x xs ys zs [d [l ->]] [e [m ->]] H.
  pose proof (eval_deterministic _ _ H _ (append_list l d e m)) as ->.
  rewrite <- !list_value_cons; apply append_list.
Qed.

(** ** An empty list like the given one

    Consumers take no value of the element type, and no program reads a
    ghost.  An empty list of the same type is the list itself when it is
    empty, and otherwise the nil whose ghost is its head. *)
Definition nil2 d := Val ('tagger[list_nm]) @@ ''decorate[Val 'fst, d].
Definition emptied := Eval cbn -[tagged_fun] in to_tree
  (star "xs" ((Ref "xs" @@ (lam_rt (Val 'I) (Ref "xs") ''*
      star "p" (lam_rt (''K1 (nil2 (Val 'fst @@ Ref "p"))) (Ref "xs")))) @@ Ref "xs")).

Definition empty_of d l := match l with
  | List.nil => nil_value d | List.cons x _ => nil_value x end.

Lemma emptied_tag_free : forall AI, infer AI @ emptied ==> Sm emptied.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

Lemma type_app_emptied : forall (AI : Decl) A, supports_list AI ->
  type_app AI @ emptied @r 'List[A] ==> Sm ('List[A]).
Proof. intros AI A HL; unfold emptied, nil2; repeat ty. Qed.

Definition empty_step xs := Eval cbn -[tagged_fun] in to_tree
  (star "p" (lam_rt (''K1 (nil2 (Val 'fst @@ Ref "p"))) (Val xs))).
Lemma empty_step_eval : forall xs x r,
  empty_step xs @ (x '* r) ==> lam ('K1 (nil_value x)) xs.
Proof.
  intros; unfold empty_step, lam, nil_value; d_eval.
Qed.
Lemma emptied_eval : forall xs f v,
  xs @ (lam 'I xs '* empty_step xs) ==> f -> f @ xs ==> v -> emptied @ xs ==> v.
Proof.
  intros xs f v H1 H2; unfold lam, empty_step in H1; unfold emptied; d_eval.
Qed.
Lemma emptied_list : forall d l, emptied @ list_value d l ==> empty_of d l.
Proof.
  intros d [|x l].
  - eapply emptied_eval; [apply nil_apply|apply lam_eval; evaluate].
  - set (xs := list_value d (List.cons x l)).
    assert (Hf : forall m, list_value d m @ (lam 'I xs '* empty_step xs) ==>
       match m with List.nil => lam 'I xs | List.cons y _ => lam ('K1 (nil_value y)) xs end).
    { induction m as [|y m IH]; cbn [list_value].
      - apply nil_apply.
      - eapply cell_apply; [exact IH|apply empty_step_eval]. }
    eapply emptied_eval; [apply (Hf (List.cons x l))|apply lam_eval; evaluate].
Qed.

(** ** Reading a list *)

(** The head takes a default: [head] on an empty list no longer exists. *)
Definition head_or d := foldright_value 'fst d.
Lemma head_or_nil : forall d a, head_or d @ nil_value a ==> d.
Proof. intros; apply foldright_value_nil. Qed.
Lemma head_or_cons : forall d x t r, t @ (d '* 'fst) ==> r ->
  head_or d @ cell x t ==> x.
Proof.
  intros d x t r H; apply foldright_value_eval; eapply cell_apply; [exact H|evaluate].
Qed.
Lemma head_or_list : forall d e x l, head_or d @ list_value e (List.cons x l) ==> x.
Proof.
  intros d e x l; apply foldright_value_eval.
  assert (Hr : exists r, right_to 'fst d l r).
  { induction l as [|y l [r IH]]; [eexists; constructor|].
    eexists; econstructor; [exact IH|evaluate]. }
  destruct Hr as [r Hr]; eapply cell_apply; [apply fold_list; exact Hr|evaluate].
Qed.
Lemma type_app_head_or : forall AI D A,
  type_app AI @ 'fst @r (A '* D) ==> Sm A ->
  D = A -> type_app AI @ head_or D @r 'List[A] ==> Sm A.
Proof.
  intros AI D A H ->; apply type_app_foldright_value; exact H.
Qed.

(** The tail is a fold over pairs, as the predecessor is. *)
Definition tail_shift := Eval cbn -[cons_step] in to_tree
  (star "p" ((Val 'snd @@ (Val 'snd @@ Ref "p")) ''*
    (Val cons_step @@ ((Val 'fst @@ Ref "p") ''* (Val 'snd @@ (Val 'snd @@ Ref "p")))))).
Definition list_tail := Eval cbn -[cons_step tail_shift emptied] in to_tree
  (star "xs" (Val 'fst @@ (Ref "xs" @@
     (((Val emptied @@ Ref "xs") ''* (Val emptied @@ Ref "xs")) ''* Val tail_shift)))).
Lemma tail_shift_eval : forall x a c,
  tail_shift @ (x '* (a '* c)) ==> (c '* cons_value x c).
Proof.
  intros; pose proof (cons_step_eval x c); unfold tail_shift; d_eval.
Qed.
Definition tail_of (l : list Combination) := match l with List.nil => l | List.cons _ m => m end.
Lemma list_tail_fold : forall e d l,
  list_value d l @ ((e '* e) '* tail_shift) ==>
    ((match l with List.nil => e | List.cons _ m => fold_right cons_value e m end)
      '* fold_right cons_value e l).
Proof.
  intros e d l; induction l as [|x l IH]; cbn [list_value fold_right].
  - apply nil_apply.
  - eapply cell_apply; [exact IH|apply tail_shift_eval].
Qed.
Lemma list_tail_nil : forall d, list_tail @ nil_value d ==> nil_value d.
Proof.
  intros d; pose proof (emptied_list d List.nil) as He; cbn in He.
  pose proof (list_tail_fold (nil_value d) d List.nil) as H; cbn [list_value fold_right] in H.
  unfold list_tail; d_eval.
Qed.
Lemma fold_right_value : forall e l, fold_right cons_value (nil_value e) l = list_value e l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.
Lemma list_tail_cons : forall d x l, list_tail @ list_value d (List.cons x l) ==> list_value x l.
Proof.
  intros d x l; pose proof (emptied_list d (List.cons x l)) as He; cbn [empty_of] in He.
  pose proof (list_tail_fold (nil_value x) d (List.cons x l)) as H.
  cbn [fold_right] in H; rewrite fold_right_value in H.
  unfold list_tail; d_eval.
Qed.

Lemma type_app_tail_shift : forall (AI : Decl) A, supports_list AI ->
  type_app AI @ tail_shift @r (A '* ('List[A] '* 'List[A])) ==> Sm ('List[A] '* 'List[A]).
Proof.
  intros AI A HL; pose proof (type_app_cons_step AI A HL) as HC.
  unfold tail_shift; repeat ty.
Qed.
Lemma type_app_list_tail : forall (AI : Decl) A, supports_list AI ->
  type_app AI @ list_tail @r 'List[A] ==> Sm ('List[A]).
Proof.
  intros AI A HL; pose proof (type_app_emptied AI A HL) as HE.
  pose proof (type_app_tail_shift AI A HL) as HS.
  unfold list_tail; repeat ty.
Qed.
Lemma infer_list_tail : forall AI, infer AI @ list_tail ==> Sm list_tail.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

(** ** The left fold, as a right fold over functions

    The right fold builds the function of the accumulator; its ghosts are
    the base. *)
Definition foldleft_arm (st b : Term) := star "p"
  (lam_rt (star "acc" ((Val 'snd @@ Ref "p") @@ (st @@ (Ref "acc" ''* (Val 'fst @@ Ref "p"))))) b).
Definition foldleft := Eval cbn -[tagged_fun] in to_tree
  (star "t" (((Val 'snd @@ (Val 'snd @@ Ref "t")) @@
     (lam_rt (Val 'I) (Val 'fst @@ (Val 'snd @@ Ref "t")) ''*
      foldleft_arm (Val 'fst @@ Ref "t") (Val 'fst @@ (Val 'snd @@ Ref "t")))) @@
     (Val 'fst @@ (Val 'snd @@ Ref "t")))).
(** The run of a left fold over a list of elements. *)
Inductive left_to (st : Combination) : Combination -> list Combination -> Combination -> Prop :=
| left_nil : forall a, left_to st a List.nil a
| left_cons : forall a x l a' r,
    st @ (a '* x) ==> a' -> left_to st a' l r -> left_to st a (List.cons x l) r.

Definition foldleft_step st b := Eval cbn -[tagged_fun] in to_tree (foldleft_arm (Val st) (Val b)).
Definition foldleft_body st p := Eval cbn in to_tree
  (star "acc" (Val (p) @@ (Val st @@ (Ref "acc" ''* Val 'I)))).
Lemma foldleft_eval : forall st b xs f v,
  xs @ (lam 'I b '* foldleft_step st b) ==> f -> f @ b ==> v ->
  foldleft @ (st '* (b '* xs)) ==> v.
Proof.
  intros st b xs f v H1 H2; unfold lam, foldleft_step, foldleft_arm in H1.
  unfold foldleft; cbn -[tagged_fun]; d_eval.
Qed.

Lemma foldleft_step_eval : forall st b x g, exists h,
  foldleft_step st b @ (x '* g) ==> lam h b /\
  forall a a' r, st @ (a '* x) ==> a' -> g @ a' ==> r -> h @ a ==> r.
Proof.
  intros st b x g; eexists; split.
  - unfold foldleft_step, foldleft_arm, lam; cbn -[tagged_fun]; d_eval.
  - intros a a' r H1 H2; inv_out H1; d_eval.
Qed.
Lemma foldleft_fold : forall st b d l, exists g,
  list_value d l @ (lam 'I b '* foldleft_step st b) ==> g /\
  forall a r, left_to st a l r -> g @ a ==> r.
Proof.
  intros st b d l; induction l as [|x l [g [Hg Hr]]]; cbn [list_value].
  - eexists; split; [apply nil_apply|].
    intros a r H; inversion H; subst; apply lam_eval; evaluate.
  - destruct (foldleft_step_eval st b x g) as [h [Hh Hb]].
    eexists; split; [eapply cell_apply; [exact Hg|exact Hh]|].
    intros a r H; inversion H; subst.
    apply lam_eval; eapply Hb; [eassumption|apply Hr; assumption].
Qed.
Lemma foldleft_list : forall st a d l r, left_to st a l r ->
  foldleft @ (st '* (a '* list_value d l)) ==> r.
Proof.
  intros st a d l r H; destruct (foldleft_fold st a d l) as [g [Hg Hr]].
  eapply foldleft_eval; [exact Hg|apply Hr; exact H].
Qed.
Lemma type_app_foldleft : forall (AI : Decl) F B A,
  type_app AI @ F @r (B '* A) ==> Sm B ->
  type_app AI @ foldleft @r (F '* (B '* 'List[A])) ==> Sm B.
Proof.
  intros AI F B A HF; unfold foldleft; repeat ty.
Qed.
Lemma infer_foldleft : forall AI, infer AI @ foldleft ==> Sm foldleft.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma infer_wait2 : forall AI M N x M' N' x',
  infer AI @ M ==> Sm M' -> infer AI @ N ==> Sm N' -> infer AI @ x ==> Sm x' ->
  infer AI @ 'wait2[M,N,x] ==> Sm ('wait2[M',N',x']).
Proof.
  intros AI M N x M' N' x' HM HN Hx.
  assert (HI := infer_I AI).
  eapply infer_fork.
  - apply infer_stem; eapply infer_fork.
    + apply infer_stem; eapply infer_fork;
        [apply infer_stem; apply infer_K1; exact HM|apply infer_K1; exact HN|].
      apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
    + apply infer_K1; exact Hx.
    + apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
  - exact HI.
  - apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
Qed.
(** ** List algorithms

    Filtering keeps elements selected by a Boolean predicate; its base is
    the emptied list. *)
Definition singleton := Eval cbn -[cons_step] in to_tree
  (star "u" (Val cons_step @@ (Ref "u" ''* nil2 (Ref "u")))).
Lemma singleton_eval : forall x, singleton @ x ==> cell x (nil_value x).
Proof.
  intros x; pose proof (cons_step_eval x (nil_value x)) as H.
  unfold cons_value in H; unfold singleton, nil_value; cbn -[cons_step]; d_eval.
Qed.

Definition filter_step_term (p : Term) :=
  star "q" ((p @@ (Val 'fst @@ Ref "q")) @@
    ((Val cons_step @@ Ref "q") ''* (Val 'snd @@ Ref "q"))).
Definition filter_step predicate := Eval cbn -[cons_step] in to_tree (filter_step_term (Val predicate)).
Definition filter_value predicate := Eval cbn -[emptied] in to_tree
  (star "xs" (Ref "xs" @@ ((Val emptied @@ Ref "xs") ''* Val (filter_step predicate)))).
Notation "'filter [ p ]" := (filter_value p) (at level 0, only parsing).
Lemma filter_step_true : forall predicate x ys, predicate @ x ==> 'tt ->
  filter_step predicate @ (x '* ys) ==> cons_value x ys.
Proof.
  intros predicate x ys H; pose proof (cons_step_eval x ys) as HP.
  unfold filter_step; cbn -[cons_step]; d_eval.
Qed.
Lemma filter_step_false : forall predicate x ys, predicate @ x ==> 'ff ->
  filter_step predicate @ (x '* ys) ==> ys.
Proof.
  intros predicate x ys H; pose proof (cons_step_eval x ys) as HP.
  unfold filter_step; cbn -[cons_step]; d_eval.
Qed.
Lemma filter_value_eval : forall p xs e r,
  emptied @ xs ==> e -> xs @ (e '* filter_step p) ==> r -> filter_value p @ xs ==> r.
Proof. intros p xs e r H1 H2; unfold filter_value; d_eval. Qed.
Lemma filter_value_nil : forall predicate d,
  filter_value predicate @ nil_value d ==> nil_value d.
Proof.
  intros; eapply filter_value_eval; [apply (emptied_list d List.nil)|apply nil_apply].
Qed.

(** A filter with a known base, for a program that holds a value of the
    element type. *)
Definition filter_from p d := foldright_value (filter_step p) (nil_value d).

(** [filter_from p d] keeps the entries that satisfy [p], in order, and
    ends in [nil_value d]: for a list whose entries [p] decides by [b]. *)
Lemma filter_from_list : forall p d (b : Combination -> bool) d' (l : list Combination),
  List.Forall (fun x => p @ x ==> (if b x then 'tt else 'ff)) l ->
  filter_from p d @ list_value d' l ==> list_value d (List.filter b l).
Proof.
  intros p d b d' l H; unfold filter_from; apply foldright_value_eval.
  induction H as [|x l Hx Hl IH]; cbn [list_value List.filter]; [apply nil_apply|].
  eapply cell_apply; [exact IH|].
  destruct (b x); cbn [list_value];
    [apply filter_step_true|apply filter_step_false]; exact Hx.
Qed.

Section ListAlgorithmsTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Lemma type_app_filter_step : forall P A,
  type_app AI @ P @r A ==> Sm ('Bool) ->
  type_app AI @ filter_step P @r (A '* 'List[A]) ==> Sm ('List[A]).
Proof using AI HL.
  intros P A HP; pose proof (type_app_cons_step AI A HL) as HC.
  unfold filter_step; repeat ty.
Qed.
Lemma type_app_filter_value : forall P A,
  type_app AI @ P @r A ==> Sm ('Bool) ->
  type_app AI @ filter_value P @r 'List[A] ==> Sm ('List[A]).
Proof using AI HL.
  intros P A HP; pose proof (type_app_filter_step P A HP) as HF.
  pose proof (type_app_emptied AI A HL) as HE.
  unfold filter_value; repeat ty.
Qed.
Lemma infer_filter_value : forall p P,
  infer AI @ p ==> Sm P -> infer AI @ filter_value p ==> Sm (filter_value P).
Proof using AI.
  intros p P Hp; unfold filter_value, filter_step.
  repeat first [apply infer_cons_step | apply emptied_tag_free | exact Hp | eapply infer_I
    | eapply infer_fork | eapply infer_stem | eapply infer_leaf | eapply type_app_I
    | eapply type_app_K_ev
    | eapply type_app_stem_ev; eapply type_app_stem_structural; intros; discriminate
    | new_S; [intros; discriminate |] ].
Qed.
Lemma infer_filter_step : forall p P,
  infer AI @ p ==> Sm P -> infer AI @ filter_step p ==> Sm (filter_step P).
Proof using AI.
  intros p P Hp; unfold filter_step.
  repeat first [apply infer_cons_step | exact Hp | eapply infer_I
    | eapply infer_fork | eapply infer_stem | eapply infer_leaf | eapply type_app_I
    | eapply type_app_K_ev
    | eapply type_app_stem_ev; eapply type_app_stem_structural; intros; discriminate
    | new_S; [intros; discriminate |] ].
Qed.
Lemma infer_singleton : infer AI @ singleton ==> Sm singleton.
Proof using AI. apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma type_app_singleton : forall A, type_app AI @ singleton @r A ==> Sm ('List[A]).
Proof using AI HL.
  intros A; pose proof (type_app_cons_step AI A HL) as HC.
  unfold singleton, nil2; repeat ty.
Qed.
End ListAlgorithmsTyping.

(** ** Polymorphic list programs

    Each is one closed program, on a tuple, and each is its own type.
    Only [nil], [singleton] and [map] take a value: each makes a list of a
    new type. *)
Definition nil := Eval cbn in to_tree (star "d" (nil2 (Ref "d"))).
Definition cons := cons_step.
Definition foldright := Eval cbn in to_tree
  (star "t" ((Val 'snd @@ (Val 'snd @@ Ref "t")) @@
    ((Val 'fst @@ (Val 'snd @@ Ref "t")) ''* (Val 'fst @@ Ref "t")))).
Lemma nil_specialises : forall d, nil @ d ==> nil_value d.
Proof. intros; unfold nil, nil2, nil_value; cbn; d_eval. Qed.
Lemma cons_eval : forall x xs, cons @ (x '* xs) ==> cons_value x xs.
Proof. exact cons_step_eval. Qed.
Lemma foldright_eval : forall step base xs r,
  xs @ (base '* step) ==> r -> foldright @ (step '* (base '* xs)) ==> r.
Proof. intros; unfold foldright; cbn; d_eval. Qed.
Lemma type_app_foldright : forall AI F B A,
  type_app AI @ F @r (A '* B) ==> Sm B ->
  type_app AI @ foldright @r (F '* (B '* 'List[A])) ==> Sm B.
Proof. intros AI F B A HF; unfold foldright; repeat ty. Qed.
Lemma infer_foldright : forall AI, infer AI @ foldright ==> Sm foldright.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

Lemma infer_nil_program : forall AI, infer AI @ nil ==> Sm nil.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma type_app_nil : forall AI A, supports_list AI ->
  type_app AI @ nil @r A ==> Sm ('List[A]).
Proof. intros AI A HL; unfold nil, nil2; repeat ty. Qed.

(** Mapping makes a list of a new type, so it takes a value of that type. *)
Definition map_step_term f := star "p"
  (Val cons_step @@ ((f @@ (Val 'fst @@ Ref "p")) ''* (Val 'snd @@ Ref "p"))).
Definition map_step_value f := Eval cbn -[cons_step] in to_tree (map_step_term (Val f)).
Definition map_value f b := foldright_value (map_step_value f) (nil_value b).
Definition map := Eval cbn -[cons_step] in to_tree
  (star "t" ((Val 'snd @@ (Val 'snd @@ Ref "t")) @@
    (nil2 (Val 'fst @@ (Val 'snd @@ Ref "t")) ''* map_step_term (Val 'fst @@ Ref "t")))).
(** The array and matrix programs compose a map before they have its list. *)
Definition map_with := Eval cbn -[cons_step] in to_tree
  (star "f" (star "b" (star "xs"
    (Ref "xs" @@ (nil2 (Ref "b") ''* map_step_term (Ref "f")))))).
Lemma map_step_eval : forall f x y ys, f @ x ==> y ->
  map_step_value f @ (x '* ys) ==> cons_value y ys.
Proof.
  intros f x y ys H; pose proof (cons_step_eval y ys) as HC.
  unfold map_step_value; cbn -[cons_step]; d_eval.
Qed.
Lemma map_value_list : forall f b d xs ys,
  Forall2 (fun x y => f @ x ==> y) xs ys ->
  map_value f b @ list_value d xs ==> list_value b ys.
Proof.
  intros f b d xs ys H; apply foldright_list.
  induction H as [|x y xs ys Hf _ IH]; cbn [list_value]; [constructor|].
  econstructor; [exact IH|apply map_step_eval; exact Hf].
Qed.

Lemma map_eval : forall f b xs r,
  xs @ (nil_value b '* map_step_value f) ==> r -> map @ (f '* (b '* xs)) ==> r.
Proof.
  intros f b xs r H; unfold map_step_value, map_step_term, nil_value in *.
  unfold map, nil2; cbn -[cons_step] in *; d_eval.
Qed.
Lemma map_list : forall f b d xs ys,
  Forall2 (fun x y => f @ x ==> y) xs ys ->
  map @ (f '* (b '* list_value d xs)) ==> list_value b ys.
Proof.
  intros f b d xs ys H; apply map_eval, foldright_value_inv, map_value_list; exact H.
Qed.
Lemma map_with_specialises : forall f b, map_with @ f @r b ==> map_value f b.
Proof.
  intros; unfold map_with, map_value, foldright_value, map_step_value, map_step_term,
    nil_value, swap, nil2; cbn -[cons_step]; d_eval.
Qed.

Section PolymorphicMapTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Lemma infer_map : infer AI @ map ==> Sm map.
Proof using AI. apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma type_app_map : forall F A B,
  type_app AI @ F @r A ==> Sm B ->
  type_app AI @ map @r (F '* (B '* 'List[A])) ==> Sm ('List[B]).
Proof using AI HL.
  intros F A B HF; pose proof (type_app_cons_step AI B HL) as HC.
  unfold map, map_step_term, nil2; cbn -[cons_step]; repeat ty.
Qed.
Lemma infer_map_with : infer AI @ map_with ==> Sm map_with.
Proof using AI. apply infer_tag_free; vm_compute; reflexivity. Qed.
Lemma type_app_map_with : forall F B, exists R, type_app AI @ map_with @r F ==> Sm R /\
  type_app AI @ R @r B ==> Sm (foldright_value (map_step_value F) ('List[B])).
Proof using AI HL.
  intros F B; eexists; split;
    unfold map_with, map_step_value, map_step_term, foldright_value, swap, nil2; cbn -[cons_step].
  all: repeat ty.
Qed.
Lemma infer_map_with_specialisation : forall f b F B,
  infer AI @ f ==> Sm F -> infer AI @ b ==> Sm B ->
  infer_expression AI @ (map_with @ f @r b) ==> Sm (foldright_value (map_step_value F) ('List[B])).
Proof using AI HL.
  intros f b F B Hf Hb; destruct (type_app_map_with F B) as [R [H1 H2]].
  eapply infer_expression_fork; [|apply infer_expression_stem; exact Hb|exact H2].
  eapply infer_expression_fork;
    [apply infer_expression_stem; exact infer_map_with|apply infer_expression_stem; exact Hf|exact H1].
Qed.
Lemma type_app_map_step : forall F A B,
  type_app AI @ F @r A ==> Sm B ->
  type_app AI @ map_step_value F @r (A '* 'List[B]) ==> Sm ('List[B]).
Proof using AI HL.
  intros F A B HF; pose proof (type_app_cons_step AI B HL) as HC.
  unfold map_step_value; repeat ty.
Qed.
Lemma type_app_map_value : forall F A B,
  type_app AI @ F @r A ==> Sm B ->
  type_app AI @ foldright_value (map_step_value F) ('List[B]) @r 'List[A] ==> Sm ('List[B]).
Proof using AI HL.
  intros; apply type_app_foldright_value; apply type_app_map_step; assumption.
Qed.
Lemma infer_map_value : forall f F b B,
  infer AI @ f ==> Sm F -> infer AI @ b ==> Sm B ->
  infer AI @ map_value f b ==> Sm (foldright_value (map_step_value F) ('List[B])).
Proof using AI HL.
  intros f F b B Hf Hb; unfold map_value; apply infer_foldright_value.
  - unfold map_step_value; cbn -[cons_step].
    infer_tac; try apply infer_tag_free; try (vm_compute; reflexivity).
  - apply infer_nil_value; assumption.
Qed.
End PolymorphicMapTyping.

(** [map] is its own type.  Given a value of [B] and a program that takes
    [A] to [B], it takes [List[A]] to [List[B]]. *)
Theorem map_polymorphic : forall (AI : Decl), supports_list AI ->
  infer AI @ map ==> Sm map /\
  forall F A B, type_app AI @ F @r A ==> Sm B ->
    type_app AI @ map @r (F '* (B '* 'List[A])) ==> Sm ('List[B]).
Proof.
  intros AI HL; split; [apply infer_map|intros F A B HF; apply type_app_map; assumption].
Qed.

(** ** Canonical forms: every value of [List[A]] is a list *)
Lemma infer_wait_inv : forall AI u M N,
  infer AI @ u ==> Sm ('wait[M,N]) ->
  exists m n, u = 'wait[m,n] /\ infer AI @ m ==> Sm M /\ infer AI @ n ==> Sm N.
Proof.
  intros AI u M N H.
  destruct (infer_S2_inv AI u ('S2['K1 M,'K1 N]) 'I ltac:(intros; discriminate) H)
    as [g [i [-> [Hg Hi]]]].
  pose proof (infer_tag_free_inv AI _ _ Hi eq_refl) as ->.
  destruct (infer_S2_inv AI g ('K1 M) ('K1 N) ltac:(intros; discriminate) Hg)
    as [km [kn [-> [Hkm Hkn]]]].
  destruct (infer_K1_inv AI km M Hkm) as [m [-> Hm]].
  destruct (infer_K1_inv AI kn N Hkn) as [n [-> Hn]].
  exists m, n; repeat split; assumption.
Qed.
Lemma infer_product_inv : forall AI u A B,
  infer AI @ u ==> Sm (A '* B) ->
  exists a b, u = a '* b /\ infer AI @ a ==> Sm A /\ infer AI @ b ==> Sm B.
Proof.
  intros AI u A B H.
  destruct (infer_S2_inv AI u ('S2['I,'K1 A]) ('K1 B) ltac:(intros; discriminate) H)
    as [g [kb [-> [Hg Hkb]]]].
  destruct (infer_K1_inv AI kb B Hkb) as [b [-> Hb]].
  destruct (infer_S2_inv AI g 'I ('K1 A) ltac:(intros; discriminate) Hg)
    as [i [ka [-> [Hi Hka]]]].
  pose proof (infer_tag_free_inv AI _ _ Hi eq_refl) as ->.
  destruct (infer_K1_inv AI ka A Hka) as [a [-> Ha]].
  exists a, b; repeat split; assumption.
Qed.

Lemma infer_cell_carrier_inv : forall (AI : Decl) c A,
  infer AI @ c ==> Sm (cell_carrier A ('List[A])) ->
  exists x t, c = cell_carrier x t /\ infer AI @ x ==> Sm A /\ infer AI @ t ==> Sm ('List[A]).
Proof.
  intros AI c A H; unfold cell_carrier in H.
  destruct (infer_wait_inv AI _ _ _ H) as [m [q [-> [Hm Hq]]]].
  pose proof (infer_tag_free_inv AI _ _ Hm ltac:(vm_compute; reflexivity)) as ->.
  destruct (infer_product_inv AI _ _ _ Hq) as [x [t [-> [Hx Ht]]]].
  exists x, t; repeat split; assumption.
Qed.

Lemma list_canonical_size : forall (AI : Decl) n v A, supports_list AI ->
  tree_size v <= n -> infer AI @ v ==> Sm ('List[A]) ->
  exists d l, v = list_value d l /\ infer AI @ d ==> Sm A /\
    List.Forall (fun x => infer AI @ x ==> Sm A) l.
Proof.
  intros AI n; induction n as [|n IHn]; intros v A HL Hs H.
  - destruct v; cbn in Hs; lia.
  - destruct (infer_tagged_result_inv AI _ _ _ H) as [f [m [F [-> [Hf [Hn HO]]]]]].
    pose proof (declaration_K1_inv _ _ _ _ _ _ HL HO) as HRF.
    destruct (list_abstractor_inv _ _ HRF) as [A' [HE HC]].
    assert (A' = A) by (unfold list_eliminator in HE; inversion HE; reflexivity); subst A'.
    pose proof (infer_tag_free_inv AI _ _ Hn eq_refl) as ->.
    destruct HC as [->| ->].
    + destruct (infer_decorate_inv AI _ _ _ Hf) as [g [d [-> [Hg Hd]]]].
      exists d, List.nil; split; [|split; [exact Hd|constructor]].
      pose proof (infer_tag_free_inv AI _ _ Hg eq_refl) as ->; reflexivity.
    + destruct (infer_cell_carrier_inv AI _ _ Hf) as [x [t [-> [Hx Ht]]]].
      destruct (IHn t A HL ltac:(unfold cell_carrier in Hs; cbn [tree_size] in Hs; lia) Ht)
        as [d [l [-> [Hd Hl]]]].
      exists d, (List.cons x l); split; [reflexivity|split; [exact Hd|constructor; assumption]].
Qed.
Lemma list_canonical : forall (AI : Decl) v A, supports_list AI ->
  infer AI @ v ==> Sm ('List[A]) ->
  exists d l, v = list_value d l /\ infer AI @ d ==> Sm A /\
    List.Forall (fun x => infer AI @ x ==> Sm A) l.
Proof. intros; eapply list_canonical_size; [eassumption|apply le_n|eassumption]. Qed.

(** One-round soundness of the declarations. *)
Lemma plain_nat_cond2 : forall AI, abstractor_sound_by_typing AI nat_abstractor.
Proof. intros AI; exact (nat_abstractor_sound AI). Qed.

Lemma plain_option_cond2 : forall AI, abstractor_sound_by_typing AI option_abstractor.
Proof. intros AI; exact (option_abstractor_sound AI). Qed.

Lemma plain_sum_cond2 : forall AI, abstractor_sound_by_typing AI sum_abstractor.
Proof. intros AI; exact (sum_abstractor_sound AI). Qed.

Lemma plain_list_cond2 : forall AI, abstractor_sound_by_typing AI list_abstractor.
Proof. intros AI; exact (list_abstractor_sound AI). Qed.

