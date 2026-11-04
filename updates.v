(** * Updates (paper: Updates).

    The update interface and the update constructors, the closed
    declarations for queries and updates, and the ghost-aware queries and
    updates [ghost_case] and [ghost_update]. The salary updates are in customisation.v. *)


(** Update separates five constructions: identity, immediate-child
    traversal, query selection, guarded specialisation, and recursion.
    Query selection ([query_update]) applies the update that a
    [Query[Update]] selects for the argument; it underlies [ghost_update]
    below. Selection uses the
    same conditional [if_named] as Query. A hit stops at the current
    node; a miss traverses its children. At the type level the name test is
    run on the argument type by the IsNamed family; specialisation is sound for
    every inhabited input type, since an inhabited type tagged at a
    declared wrapper name is the declared wrapper type.
    No combined traversal/selection
    rule is installed in type_app. *)
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions conditionals.
From TreeTyping Require Import queries.
From Stdlib Require Import String.
Open Scope string_scope.
Set Default Proof Using "All".
Lemma update_one_level_leaf : forall r, update_one_level r @ Lf ==> Lf.
Proof. intros; unfold update_one_level; evaluate. Qed.
Lemma update_one_level_stem : forall r x y,
  r @ x ==> y -> update_one_level r @ Sm x ==> Sm y.
Proof. intros; unfold update_one_level; evaluate. Qed.
Lemma update_fork_eval : forall r x y x' y',
  r @ x ==> x' -> r @ y ==> y' ->
  update_one_level r @ Fk x y ==> Fk x' y'.
Proof. intros; unfold update_one_level, update_fork; evaluate. Qed.


(** The carrier type [update_one_level Update] has no clause of
    type application; the children carrier is sound for values
    ([children_value_typing]) but not for types. *)

Lemma infer_update_one_level : forall AI r,
 inf AI @ r ==> Sm ('Update) ->
 inf AI @ update_one_level r ==> Sm (update_one_level ('Update)).
Proof. intros; unfold update_one_level, update_fork; inf_tac. Qed.

Definition tagged_update := 'tagger[update_nm].
(** Identity is the base update and supplies the witness for the recursive
    update_body's Update domain. Its typing needs no wrapper declarations entry. *)
Definition identity_update := 'tagged['I,update_nm].
Definition fix_update b := 'tagged[Z (b 'C tagged_update),update_nm].
Lemma tagged_update_eval : forall r,
  tagged_update @ r ==> 'tagged[r,update_nm].
Proof. intros; unfold tagged_update; evaluate. Qed.
(** [update_eliminator_eval] is in typing.v. *)
Lemma update_eliminator_inv : forall a U V,
  update_eliminator @ a @r U ==> Sm V -> V = U.
Proof.
  intros a U V H; pose proof (eval_deterministic _ _ H _ (update_eliminator_eval a U)) as HE.
  inversion HE; reflexivity.
Qed.
Lemma type_app_Update : forall AI U,
  type_app AI @ ('Update) @r U ==> Sm U.
Proof. intros; apply type_app_abstract; apply update_eliminator_eval. Qed.

(** Specialise equality to the Update type once. The matcher is concrete;
    unlike an unspecialised comparison, it does not store Update as data. *)
Local Ltac update_check_eval :=
  first [eassumption |
    match goal with |- ('I @ ?x) @r ?y ==> _ => eapply eval_appl; [apply I_eval | update_check_eval] end |
    (apply wait_eval; update_check_eval) | apply equal_eval | apply equal1_eq |
    evaluate_expr_core update_check_eval update_check_head | idtac]
with update_check_head := first [eassumption |
    match goal with |- ('I @ ?x) @r ?y ==> _ => eapply eval_appl; [apply I_eval | update_check_eval] end |
    (apply wait_eval; update_check_eval) | apply equal_eval | apply equal1_eq |
    evaluate_head_core update_check_eval | idtac].

Definition get_update_composition_fields := Eval cbn in to_tree
  (star "B" (star "R"
    (Val equal @@ Ref "R" @@ Val tagged_update
      @@ (Val Lf @@ Ref "B") @@ Val Lf))).
Definition get_update_composition :=
  ('onStem1 ('onFork1 get_update_composition_fields)) 'C get_composition.
Definition get_recursive_update := ('onStem1 get_update_composition) 'C get_Z.
Lemma get_update_composition_some : forall B,
  get_update_composition @ (B 'C tagged_update) ==> Sm B.
Proof.
  intros; unfold get_update_composition, get_update_composition_fields; cbn.
  repeat first [apply get_composition_some | apply equal_eval | apply equal1_eq | progress evaluate2].
Qed.
Lemma get_update_composition_inv : forall X B,
  get_update_composition @ X ==> Sm B -> X = B 'C tagged_update.
Proof.
  intros X B H; unfold get_update_composition, get_update_composition_fields in H;
    cbn in H; invert_eval.
  assert (Heq : equal @ v22 @r tagged_update ==> v0)
    by (eapply eval_appl; eauto).
  destruct (equal_spec _ _ _ Heq) as [[-> HE] | [-> HE]]; invert_eval.
  eapply get_composition_inv; eassumption.
Qed.
Local Opaque get_update_composition.
Lemma get_recursive_update_some : forall B,
  get_recursive_update @ Z (B 'C tagged_update) ==> Sm B.
Proof.
  intros; unfold get_recursive_update.
  repeat first [apply get_Z_some | apply get_update_composition_some | progress evaluate2].
Qed.
Lemma get_recursive_update_inv : forall C B,
  get_recursive_update @ C ==> Sm B -> C = Z (B 'C tagged_update).
Proof.
  intros C B H; unfold get_recursive_update in H; invert_eval.
  match goal with HG : get_update_composition @ _ ==> Sm _ |- _ =>
    apply get_update_composition_inv in HG; subst end.
  apply get_Z_inv; assumption.
Qed.
(** Identity and a guarded fixed point have independent certificates. A
    clause that needs no type application answers [update_done]. *)
Definition update_done := 'K1 (Sm update_eliminator).
Definition update_identity_case_package : { t : Combination |
  to_tree (tcase (Val ('I)) (Val update_done)) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition update_identity_case := Eval cbn in proj1_sig update_identity_case_package.
Lemma update_identity_case_some :
  update_identity_case @ ('I) ==> Sm update_done.
Proof. unfold update_identity_case; evaluate. Qed.
Lemma update_identity_case_none : forall C,
  C <> 'I -> update_identity_case @ C ==> Lf.
Proof.
  intros C H; change (to_tree (tcase (Val ('I)) (Val update_done)) @ C ==> Lf).
  apply tcase_neq; congruence.
Qed.
Lemma update_identity_case_inv : forall C k,
  update_identity_case @ C ==> Sm k -> C = 'I /\ k = update_done.
Proof.
  intros C k H.
  destruct (combination_eq_dec C ('I)) as [->|HN].
  - pose proof (eval_deterministic _ _ H _ update_identity_case_some) as H0; inversion H0; auto.
  - pose proof (eval_deterministic _ _ H _ (update_identity_case_none C HN)); discriminate.
Qed.
Lemma update_identity_case_never_fork : forall C l r,
  update_identity_case @ C ==> Fk l r -> False.
Proof.
  intros C l r H; destruct (combination_eq_dec C ('I)) as [->|HN].
  - pose proof (eval_deterministic _ _ H _ update_identity_case_some); discriminate.
  - pose proof (eval_deterministic _ _ H _ (update_identity_case_none C HN)); discriminate.
Qed.


(** A carrier that mentions [Update] is rebuilt at run time and compared,
    since a label must stay out of the declarations. *)
Definition eq_built (build result : Combination) := Eval cbn -[equal] in to_tree
  (star "C" (op equal @@ Ref "C" @@ (op build @@ Ref "C") @@ (Val Lf @@ Val result) @@ Val Lf)).
Lemma eq_built_hit : forall b r t, (forall C, b @ C ==> t) -> eq_built b r @ t ==> Sm r.
Proof.
  intros b r t H; pose proof (H t) as H1; pose proof (equal_eval t) as H2.
  pose proof (equal1_eq t) as H3; unfold eq_built; evaluate.
Qed.
Lemma eq_built_miss : forall b r t C, (forall C, b @ C ==> t) -> C <> t -> eq_built b r @ C ==> Lf.
Proof.
  intros b r t C H Hne; pose proof (H C) as H1; pose proof (equal_eval C) as H2.
  pose proof (equal1_neq C t Hne) as H3; unfold eq_built; evaluate.
Qed.

Definition update_type_mk := 'S2['K1 tagged_update, 'K1 update_eliminator].
Lemma update_type_mk_eval : forall C, update_type_mk @ C ==> 'Update.
Proof. intros; unfold update_type_mk, tagged_update; evaluate. Qed.
Lemma eq_built_inv : forall b r t C s, (forall C, b @ C ==> t) ->
  eq_built b r @ C ==> Sm s -> C = t /\ s = r.
Proof.
  intros b r t C s Hb H; destruct (combination_eq_dec C t) as [->|Hne].
  - pose proof (eval_deterministic _ _ H _ (eq_built_hit b r t Hb)) as HE; inversion HE; auto.
  - pose proof (eval_deterministic _ _ H _ (eq_built_miss b r t C Hb Hne)); discriminate.
Qed.

Lemma get_IfNamed_Z_none : forall f, get_IfNamed @ Z f ==> Lf.
Proof.
  intros; unfold get_IfNamed, Z, extend_program; cbn.
  repeat first [apply equal_eval | apply equal1_eq | progress evaluate].
Qed.

(** The recursive carrier [Z(T o tagged_update)] holds the type [T] of the
    body; its check is the application [T # Update ==> Sm Update].  It never
    reopens the update_body to inspect its traversal or specialisation. *)
Local Opaque get_recursive_update equal1.
Definition update_recursive_constructor := Eval cbn -[equal get_recursive_update update_type_mk] in to_tree
  (star "C"
    (''onStem1 (star "T"
      ((star "U"
         (Val Lf @@ (star "a"
           (Val equal @@ (Ref "a" @@ Ref "T" @@ Ref "U") @@ (Val Lf @@ Ref "U")
             @@ Val (Sm update_eliminator) @@ Val Lf))))
       @@ (Val update_type_mk @@ Ref "C")))
     @@ (Val get_recursive_update @@ Ref "C"))).
Lemma update_recursive_constructor_some : forall a T,
  a @ T @r ('Update) ==> Sm ('Update) ->
  exists k, update_recursive_constructor @ Z (T 'C tagged_update) ==> Sm k /\
    k @ a ==> Sm update_eliminator.
Proof.
  intros a T HA.
  pose proof (get_recursive_update_some T) as H1.
  pose proof (update_type_mk_eval (Z (T 'C tagged_update))) as H2.
  pose proof (equal_eval (Sm ('Update))).
  pose proof (equal1_eq (Sm ('Update))).
  destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold update_recursive_constructor; eexists; split; evaluate.
Qed.
Lemma update_recursive_constructor_inv : forall C k a E,
  update_recursive_constructor @ C ==> Sm k -> k @ a ==> Sm E ->
  exists T, C = Z (T 'C tagged_update) /\
    a @ T @r ('Update) ==> Sm ('Update) /\ E = update_eliminator.
Proof.
  intros C k a E H Ha; unfold update_recursive_constructor in H; invert_eval.
  match goal with Hg : update_type_mk @ _ ==> _ |- _ =>
    pose proof (eval_deterministic _ _ Hg _ (update_type_mk_eval C)) as HU; subst end.
  match goal with Hg : get_recursive_update @ C ==> Sm ?T |- _ =>
    apply get_recursive_update_inv in Hg; subst C end.
  match goal with
  | H1 : equal @ ?D ==> ?e, H2 : ?e @ ?U ==> ?b |- _ =>
    assert (HE : equal @ D @r U ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ HE) as [[HB HU]|[HB HU]];
    subst b; invert_eval
  end.
  repeat eexists; eapply eval_appl; eassumption.
Qed.
Lemma update_recursive_constructor_never_fork : forall C l r,
  update_recursive_constructor @ C ==> Fk l r -> False.
Proof. intros C l r H; unfold update_recursive_constructor in H; invert_eval. Qed.


Lemma tagged_update_tag_free : tag_free tagged_update = true.
Proof. unfold tagged_update; tag_free_tac. Qed.

Set Default Proof Using "Type".
Local Opaque equal equal1 get_tagname get_IfNamed get_wrap_payload_type is_concrete app inf.
Local Ltac run := first [eassumption | apply equal_eval | apply equal1_eq |
 evaluate_expr_core run run_head | idtac]
with run_head := first [eassumption | apply equal_eval | apply equal1_eq |
 evaluate_head_core run | idtac].
Lemma preserving_if_named_application : forall AI N T F U,
 concrete N -> declared_wrapper AI N T -> inhabited AI U ->
 app AI @ F @r wrap_type T N ==> Sm (wrap_type T N) ->
 app AI @ IfNamed N F ('Update) @r U ==> Sm U.
Proof.
 intros AI N T F U HN HI HU HF.
 pose proof (inhabited_not_impostor AI N T U HI HU) as Himp.
 destruct (combination_eq_dec U (wrap_type T N)) as [->|Hneq].
 - eapply installed_if_named; eauto using app_Update.
 - eapply if_named_application_miss; [exact HN|exact HI| |apply app_Update].
   intros E HE; apply Hneq; exact (Himp E HE).
Qed.

(** As for Query, wrapper lookup and the application of the action's type
    to the wrapper type suffice. Lookup refuses fun_nm. *)
Definition update_choice_constructor AI := Eval lazy -[get_IfNamed update_eliminator update_nm] in
 to_tree
 (star "C"
  (''onStem1 (''onFork1 (star "N" (star "FD"
   ((''onFork1 (star "F" (star "D"
    (Val (equal1 ('Update)) @@ Ref "D" @@
     (Val Lf @@ (star "a"
      (Val is_concrete @@ Ref "N" @@
       (''onStem1 (star "T"
         ((star "W"
           (Val equal @@ (Ref "a" @@ Ref "F" @@ Ref "W") @@ (Val Lf @@ Ref "W")
            @@ Val (Sm update_eliminator) @@ Val Lf))
          @@ ''tagged[payload_eliminator2 (Ref "T"),Ref "N"]))
        @@ (Val (get_wrap_payload_type AI) @@ Ref "N")) @@ Val Lf)))
     @@ Val Lf))))
    @@ Ref "FD"))))
   @@ (Val get_IfNamed @@ Ref "C"))).

Lemma update_choice_constructor_some : forall AI N T F a,
 concrete N -> declared_wrapper AI N T ->
 a @ F @r wrap_type T N ==> Sm (wrap_type T N) ->
 exists k, update_choice_constructor AI @ IfNamed N F ('Update) ==> Sm k /\
   k @ a ==> Sm update_eliminator.
Proof.
 intros AI N T F a HN HI HA.
 pose proof (get_IfNamed_some N F ('Update)).
 pose proof (equal1_eq ('Update)).
 pose proof (proj2 (is_concrete_true N) HN).
 pose proof (get_wrap_payload_type_some AI N T HI).
 pose proof (equal1_eq (Sm (wrap_type T N))).
 destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
 unfold update_choice_constructor; unfold wrap_type, wrap_eliminator in *.
 eexists; split; run.
Qed.
Lemma update_choice_constructor_inv : forall AI C k a E,
 update_choice_constructor AI @ C ==> Sm k -> k @ a ==> Sm E ->
 exists N T F, C = IfNamed N F ('Update) /\
 concrete N /\ declared_wrapper AI N T /\
 a @ F @r wrap_type T N ==> Sm (wrap_type T N) /\ E = update_eliminator.
Proof.
 intros AI C k a E H Ha; unfold update_choice_constructor in H; cbn in H; invert_eval.
 all: repeat progress recognizer_eqtac.
 all: match goal with Hc : is_concrete @ ?N ==> ?b |- _ =>
  pose proof (is_concrete_spec N) as HC;
  pose proof (eval_deterministic _ _ Hc _ HC) as HB;
  destruct (concreteb N) eqn:HN; cbn in HB; subst b; invert_eval end.
 all: repeat progress recognizer_eqtac.
 all: repeat match goal with
 | H : get_IfNamed @ ?S ==> Sm (Fk ?N (Fk ?F ?D)) |- _ => apply get_IfNamed_inv in H; subst S
 | H : get_wrap_payload_type ?AI @ ?N ==> Sm ?T |- _ => apply get_wrap_payload_type_inv in H
 end.
 all: repeat eexists; first [eassumption|apply concreteb_sound; eassumption|
    match goal with HW : declared_wrapper _ _ _ |- _ =>
      first [exact (proj1 HW)|exact (proj2 HW)] end|
    (eapply eval_appl; eassumption)].
Qed.
Lemma update_choice_constructor_never_fork : forall AI C l r,
 update_choice_constructor AI @ C ==> Fk l r -> False.
Proof.
 intros AI C l r H; unfold update_choice_constructor in H; cbn in H; invert_eval.
 all: repeat progress recognizer_eqtac.
Qed.
Lemma update_choice_constructor_none : forall AI C,
 get_IfNamed @ C ==> Lf -> update_choice_constructor AI @ C ==> Lf.
Proof. intros AI C HG; unfold update_choice_constructor; evaluate. Qed.
Definition specialised_update N f d := 'tagged[if_named N f d,update_nm].


Set Default Proof Using "Type".
Local Opaque equal equal1 app inf.
Definition children_type_mk := Eval cbn -[update_type_mk] in to_tree
  (star "z" ((star "u" (''triage[Val Lf, Val Lf ''C Ref "u",
      star "x" (star "y" (Val Lf @@ (Ref "u" @@ Ref "x") @@ (Ref "u" @@ Ref "y")))]))
    @@ (Val update_type_mk @@ Ref "z"))).
Lemma children_type_mk_eval : forall C, children_type_mk @ C ==> update_one_level ('Update).
Proof.
  intros C; pose proof (update_type_mk_eval C) as H.
  unfold children_type_mk, update_one_level, update_fork; cbn; evaluate.
Qed.
Definition children_constructor_case := eq_built children_type_mk update_done.
Lemma children_constructor_some :
 children_constructor_case @ update_one_level ('Update) ==> Sm update_done.
Proof. apply eq_built_hit; apply children_type_mk_eval. Qed.
Lemma children_constructor_none : forall C,
 C <> update_one_level ('Update) -> children_constructor_case @ C ==> Lf.
Proof. intros; eapply eq_built_miss; [apply children_type_mk_eval|assumption]. Qed.
Lemma children_constructor_inv : forall C k,
 children_constructor_case @ C ==> Sm k ->
 C = update_one_level ('Update) /\ k = update_done.
Proof.
 intros C k H; destruct (combination_eq_dec C (update_one_level ('Update))) as [->|HN].
 - pose proof (eval_deterministic _ _ H _ children_constructor_some) as H0; inversion H0; auto.
 - pose proof (eval_deterministic _ _ H _ (children_constructor_none C HN)); discriminate.
Qed.
Lemma children_constructor_never_fork : forall C l r,
 children_constructor_case @ C ==> Fk l r -> False.
Proof.
 intros C l r H; destruct (combination_eq_dec C (update_one_level ('Update))) as [->|HN].
 - pose proof (eval_deterministic _ _ H _ children_constructor_some); discriminate.
 - pose proof (eval_deterministic _ _ H _ (children_constructor_none C HN)); discriminate.
Qed.
(** Query-selected update: [query_update q @ u = (q @ u) @ u]. A query of
    type [Query[Update]] inspects the argument and selects the update to
    apply to it. The program type [S2[Query[Update], I]] applies to any U
    by the existing S, query-eliminator, identity and Update-eliminator
    rules, so this case needs no new hardwired type-application rule. *)
Definition query_update_type := 'S2['Query['Update],'I].
Definition query_update_type_mk := Eval cbn -[update_type_mk] in to_tree
  (star "z" (''S2[Val ('tagger[query_nm]) @@ ''wait[Val query_elim, Val update_type_mk @@ Ref "z"],
    Val 'I])).
Lemma query_update_type_mk_eval : forall C, query_update_type_mk @ C ==> query_update_type.
Proof.
  intros C; pose proof (update_type_mk_eval C) as H.
  unfold query_update_type_mk, query_update_type, query_eliminator; evaluate.
Qed.
Definition query_update_case := eq_built query_update_type_mk update_done.
Lemma query_update_case_some :
 query_update_case @ query_update_type ==> Sm update_done.
Proof. apply eq_built_hit; apply query_update_type_mk_eval. Qed.
Lemma query_update_case_none : forall C,
 C <> query_update_type -> query_update_case @ C ==> Lf.
Proof. intros; eapply eq_built_miss; [apply query_update_type_mk_eval|assumption]. Qed.
Lemma query_update_case_inv : forall C k,
 query_update_case @ C ==> Sm k ->
 C = query_update_type /\ k = update_done.
Proof.
 intros C k H; destruct (combination_eq_dec C query_update_type) as [->|HN].
 - pose proof (eval_deterministic _ _ H _ query_update_case_some) as H0; inversion H0; auto.
 - pose proof (eval_deterministic _ _ H _ (query_update_case_none C HN)); discriminate.
Qed.
Lemma query_update_case_never_fork : forall C l r,
 query_update_case @ C ==> Fk l r -> False.
Proof.
 intros C l r H; destruct (combination_eq_dec C query_update_type) as [->|HN].
 - pose proof (eval_deterministic _ _ H _ query_update_case_some); discriminate.
 - pose proof (eval_deterministic _ _ H _ (query_update_case_none C HN)); discriminate.
Qed.
Lemma app_query_update : forall AI U,
 app AI @ query_update_type @r U ==> Sm U.
Proof.
 intros; unfold query_update_type; eapply app_S.
 - intros; discriminate.
 - solve [reject_name].
 - apply app_abstract; apply query_eliminator_eval.
 - apply app_I.
 - apply app_Update.
Qed.

(** Trial order follows the paper (the ontology figure): identity,
    children, choice, query update, recursive.  Every clause gives the
    eliminator [update_eliminator] of the Update family. *)
Definition update_core AI := extend update_identity_case
 (extend children_constructor_case
   (extend (update_choice_constructor AI)
     (extend query_update_case
       (extend update_recursive_constructor refusal)))).
Definition update_abstractor AI := abstractor_intro (update_core AI).
(** The abstractor at type application of [AI]. *)
Definition update_abstractor_at AI := 'S2[update_core AI, 'K1 (type_app AI)].
Definition supports AI := AI @ update_nm ==> update_abstractor AI.
Lemma update_abstractor_partial : forall AI, update_abstractor AI @ type_app AI ==> update_abstractor_at AI.
Proof. intros; apply abstractor_intro_partial. Qed.
Lemma update_abstractor_core : forall AI C v,
  update_core AI @ C @r type_app AI ==> v -> update_abstractor_at AI @ C ==> v.
Proof. intros; apply abstractor_at_eval; assumption. Qed.
Lemma update_done_eval : forall a, update_done @ a ==> Sm update_eliminator.
Proof. intros; unfold update_done; evaluate. Qed.
Lemma constructor_identity : forall AI, update_abstractor_at AI @ ('I) ==> Sm update_eliminator.
Proof.
 intros; apply update_abstractor_core; unfold update_core.
 eapply clause_hit; [apply update_identity_case_some|apply update_done_eval].
Qed.
Lemma constructor_children : forall AI,
 update_abstractor_at AI @ update_one_level ('Update) ==> Sm update_eliminator.
Proof.
 intros; apply update_abstractor_core; unfold update_core; apply extend_none;
 [apply update_identity_case_none;discriminate|].
 eapply clause_hit; [apply children_constructor_some|apply update_done_eval].
Qed.
Lemma constructor_choice : forall AI N T F,
 concrete N -> declared_wrapper AI N T ->
 type_app AI @ F @r wrap_type T N ==> Sm (wrap_type T N) ->
 update_abstractor_at AI @ IfNamed N F ('Update) ==> Sm update_eliminator.
Proof.
 intros AI N T F HN HI HF; apply update_abstractor_core; unfold update_core;
 apply extend_none;
 [apply update_identity_case_none;unfold IfNamed;discriminate|].
 apply extend_none;
 [apply children_constructor_none;unfold IfNamed,update_one_level;discriminate|].
 destruct (update_choice_constructor_some AI N T F (type_app AI) HN HI HF) as [k [H1 H2]].
 eapply clause_hit; eassumption.
Qed.
Lemma constructor_query_update : forall AI,
 update_abstractor_at AI @ query_update_type ==> Sm update_eliminator.
Proof.
 intros; apply update_abstractor_core; unfold update_core; apply extend_none;
 [apply update_identity_case_none;discriminate|].
 apply extend_none; [apply children_constructor_none;discriminate|].
 apply extend_none.
 - assert (HG : get_IfNamed @ query_update_type ==> Lf).
   { apply (eval_bounded_sound 2000); vm_compute; reflexivity. }
   apply update_choice_constructor_none; exact HG.
 - eapply clause_hit; [apply query_update_case_some|apply update_done_eval].
Qed.
Lemma constructor_recursive : forall AI T,
 type_app AI @ T @r ('Update) ==> Sm ('Update) ->
 update_abstractor_at AI @ Z (T 'C tagged_update) ==> Sm update_eliminator.
Proof.
 intros AI T HT; apply update_abstractor_core; unfold update_core; apply extend_none;
 [apply update_identity_case_none;unfold Z;discriminate|].
 apply extend_none;
 [apply children_constructor_none;unfold Z,update_one_level;discriminate|].
 apply extend_none.
 - apply update_choice_constructor_none; apply get_IfNamed_Z_none.
 - apply extend_none;
   [apply query_update_case_none;unfold Z,query_update_type;discriminate|].
   destruct (update_recursive_constructor_some _ _ HT) as [k [H1 H2]].
   eapply clause_hit; eassumption.
Qed.
Lemma update_abstractor_supported : forall AI C E,
 supports AI -> update_abstractor_at AI @ C ==> Sm E ->
 AI @ update_nm @r type_app AI @r C ==> Sm E.
Proof.
 intros AI C E HS HC; eapply eval_appl.
 - eapply eval_appl; [exact HS|apply update_abstractor_partial].
 - exact HC.
Qed.
Lemma update_abstractor_applied : forall AI C v,
 supports AI -> AI @ update_nm @r type_app AI @r C ==> v ->
 update_abstractor_at AI @ C ==> v.
Proof.
 intros AI C v HS H; destruct (declaration_apply_inv _ _ _ _ _ H) as [R [D [HR [HD Hv]]]].
 pose proof (eval_deterministic _ _ HR _ HS) as ->.
 pose proof (eval_deterministic _ _ HD _ (update_abstractor_partial AI)) as ->; exact Hv.
Qed.
Lemma app_tagged_update : forall AI C E,
 supports AI -> update_abstractor_at AI @ C ==> Sm E ->
 app AI @ tagged_update @r C ==> Sm ('tagged[E,update_nm]).
Proof.
 intros AI C E HS HC; unfold tagged_update; type_app_tac.
 apply app_stem; apply type_app_stem_tagged; apply update_abstractor_supported; assumption.
Qed.
(** The five clauses of the abstractor, each with the eliminator
    [update_eliminator]. *)
Lemma constructor_inv : forall AI C X,
 update_abstractor_at AI @ C ==> Sm X ->
 X = update_eliminator /\
 (C = 'I \/ C = update_one_level ('Update) \/
  (exists N T F, C = IfNamed N F ('Update) /\ concrete N /\ declared_wrapper AI N T /\
     type_app AI @ F @r wrap_type T N ==> Sm (wrap_type T N)) \/
  C = query_update_type \/
  (exists T, C = Z (T 'C tagged_update) /\ type_app AI @ T @r ('Update) ==> Sm ('Update))).
Proof.
 intros AI C X HC; apply abstractor_at_eval_inv in HC; unfold update_core in HC.
 destruct (clause_inv _ _ _ _ _ (update_identity_case_never_fork _) HC) as [[k [Hk Ha]]|[_ H1]].
 { destruct (update_identity_case_inv _ _ Hk) as [-> ->].
   pose proof (eval_deterministic _ _ Ha _ (update_done_eval _)) as HE; inversion HE; auto. }
 destruct (clause_inv _ _ _ _ _ (children_constructor_never_fork _) H1) as [[k [Hk Ha]]|[_ H2]].
 { destruct (children_constructor_inv _ _ Hk) as [-> ->].
   pose proof (eval_deterministic _ _ Ha _ (update_done_eval _)) as HE; inversion HE; auto. }
 destruct (clause_inv _ _ _ _ _ (update_choice_constructor_never_fork _ _) H2) as [[k [Hk Ha]]|[_ H3]].
 { destruct (update_choice_constructor_inv _ _ _ _ _ Hk Ha) as [N [T [F [-> [HN [HI [HF ->]]]]]]].
   split; [reflexivity|right; right; left; exists N, T, F; auto]. }
 destruct (clause_inv _ _ _ _ _ (query_update_case_never_fork _) H3) as [[k [Hk Ha]]|[_ H4]].
 { destruct (query_update_case_inv _ _ Hk) as [-> ->].
   pose proof (eval_deterministic _ _ Ha _ (update_done_eval _)) as HE; inversion HE; auto 6. }
 destruct (clause_inv _ _ _ _ _ (update_recursive_constructor_never_fork _) H4) as [[k [Hk Ha]]|[_ H5]].
 { destruct (update_recursive_constructor_inv _ _ _ _ Hk Ha) as [T [-> [HT ->]]].
   split; [reflexivity|right; right; right; right; eauto]. }
 exfalso; eapply refusal_inv; exact H5.
Qed.


Lemma update_abstractor_sound : forall AI C E U V,
 supports AI -> C <> update_one_level ('Update) -> (choice_free C \/ inhabited AI U) ->
 update_abstractor_at AI @ C ==> Sm E -> E @ app AI @r U ==> Sm V ->
 app AI @ C @r U ==> Sm V.
Proof.
 intros AI C E U V HS Hch Hc HC HE.
 destruct (constructor_inv _ _ _ HC) as [-> [-> | [-> | [[N [T [F [-> [HN [HI HF]]]]]] | [-> | [T [-> HT]]]]]]];
 apply update_eliminator_inv in HE; subst V.
 - apply app_I.
 - contradiction.
 - destruct Hc as [Hc|HU]; [|eapply preserving_if_named_application; eassumption].
   exfalso; eapply Hc; reflexivity.
 - apply app_query_update.
 - eapply app_Z.
   + eapply app_compose; [solve [reject_name]| | |]; [intros;discriminate| |].
     * eapply app_tagged_update; [exact HS|exact HC].
     * exact HT.
   + apply app_Update.
Qed.



Definition children r := 'tagged[update_one_level r,update_nm].
Lemma inf_identity : forall AI, supports AI -> inf AI @ identity_update ==> Sm ('Update).
Proof.
 intros; unfold identity_update; eapply inf_tagged;
 [apply inf_I|apply inf_tag_free;reflexivity|].
 eapply update_abstractor_supported;
 [exact H|apply constructor_identity].
Qed.
Lemma inf_children : forall AI r,
 supports AI -> inf AI @ r ==> Sm ('Update) -> inf AI @ children r ==> Sm ('Update).
Proof.
 intros; unfold children; eapply inf_tagged;
 [apply infer_update_one_level;exact H0|apply inf_tag_free;reflexivity|].
 eapply update_abstractor_supported;
 [exact H|apply constructor_children].
Qed.
Lemma inf_specialise : forall AI N T f F d,
 supports AI -> supports_is_named AI -> concrete N -> declared_wrapper AI N T ->
 inf AI @ f ==> Sm F -> type_app AI @ F @r wrap_type T N ==> Sm (wrap_type T N) ->
 inf AI @ d ==> Sm ('Update) ->
 inf AI @ specialised_update N f d ==> Sm ('Update).
Proof.
 intros AI N T f F d HS HT HN HI Hf HF HD; unfold specialised_update; eapply inf_tagged.
 - apply inf_if_named;[exact HN|exact HT|exact Hf|exact HD].
 - apply inf_tag_free;reflexivity.
 - eapply update_abstractor_supported;
   [exact HS|eapply constructor_choice; eassumption].
Qed.
Definition query_update q := 'tagged['S2[q,'I],update_nm].
Lemma inf_query_update : forall AI q,
 supports AI -> inf AI @ q ==> Sm ('Query['Update]) ->
 inf AI @ query_update q ==> Sm ('Update).
Proof.
 intros AI q HS Hq.
 assert (HC : inf AI @ ('S2[q,'I]) ==> Sm query_update_type) by (unfold query_update_type; inf_tac).
 unfold query_update; eapply inf_tagged.
 - exact HC.
 - apply inf_tag_free;reflexivity.
 - eapply update_abstractor_supported;
 [exact HS|apply constructor_query_update].
Qed.
Lemma query_update_eval : forall q u r v,
 q @ u ==> r -> r @ u ==> v -> query_update q @ u ==> v.
Proof. intros; unfold query_update; apply tagged_eval; evaluate. Qed.

(** Children updates may use different updaters for a stem's child and
    for the two children of a fork. The program type is still
    [update_one_level Update], so the children case types it. *)
Definition update_fork2 rl rr := Eval cbn in to_tree
  (star "x" (star "y"
    (Val Lf @@ (Val rl @@ Ref "x") @@ (Val rr @@ Ref "y")))).
Definition update_one_level2 rs rl rr := 'triage[Lf, Lf 'C rs, update_fork2 rl rr].
Definition children2 rs rl rr := 'tagged[update_one_level2 rs rl rr,update_nm].
Lemma inf_children2 : forall AI rs rl rr,
 supports AI -> inf AI @ rs ==> Sm ('Update) -> inf AI @ rl ==> Sm ('Update) ->
 inf AI @ rr ==> Sm ('Update) -> inf AI @ children2 rs rl rr ==> Sm ('Update).
Proof.
 intros AI rs rl rr HS Hs Hl Hr.
 assert (HC : inf AI @ update_one_level2 rs rl rr ==> Sm (update_one_level ('Update)))
   by (unfold update_one_level2, update_one_level, update_fork2, update_fork; inf_tac).
 unfold children2; eapply inf_tagged.
 - exact HC.
 - apply inf_tag_free;reflexivity.
 - eapply update_abstractor_supported;
 [exact HS|apply constructor_children].
Qed.
Lemma children2_leaf : forall rs rl rr, children2 rs rl rr @ Lf ==> Lf.
Proof. intros; unfold children2, update_one_level2; apply tagged_eval; evaluate. Qed.
Lemma children2_stem : forall rs rl rr x x',
 rs @ x ==> x' -> children2 rs rl rr @ Sm x ==> Sm x'.
Proof. intros; unfold children2, update_one_level2; apply tagged_eval; evaluate. Qed.
Lemma children2_fork : forall rs rl rr x y x' y',
 rl @ x ==> x' -> rr @ y ==> y' -> children2 rs rl rr @ Fk x y ==> Fk x' y'.
Proof. intros; unfold children2, update_one_level2, update_fork2; apply tagged_eval; evaluate. Qed.
Lemma identity_update_eval : forall x, identity_update @ x ==> x.
Proof. intros; unfold identity_update; apply tagged_eval; evaluate. Qed.

(** Rebuild [decorate[f,w]] as [decorate[f',w]] where k updates f. Each
    level follows the path to f and applies the identity elsewhere, so
    the ghost w is untouched. *)
Definition ghost_rebuild k :=
 let i := identity_update in
 children2 i (children2 (children2 i (children2 (children2 i i (children2 i i k)) i i) i) i i) i.
Lemma ghost_rebuild_eval : forall k f f' w,
 k @ f ==> f' -> ghost_rebuild k @ 'decorate[f,w] ==> 'decorate[f',w].
Proof.
 intros; unfold ghost_rebuild.
 repeat first [eassumption | apply identity_update_eval | apply children2_fork |
   apply children2_stem | apply children2_leaf].
Qed.
Lemma inf_ghost_rebuild : forall AI k,
 supports AI -> inf AI @ k ==> Sm ('Update) -> inf AI @ ghost_rebuild k ==> Sm ('Update).
Proof.
 intros AI k HS Hk; assert (Hi : inf AI @ identity_update ==> Sm ('Update)) by (apply inf_identity; exact HS).
 unfold ghost_rebuild; repeat first [assumption | apply inf_children2].
Qed.

Lemma inf_fix : forall AI b T,
 supports AI -> inf AI @ b ==> Sm T ->
 type_app AI @ T @r ('Update) ==> Sm ('Update) ->
 inf AI @ fix_update b ==> Sm ('Update).
Proof.
 intros AI b T HS HB HT.
 assert (HU : inf AI @ tagged_update ==> Sm tagged_update)
 by (apply inf_tag_free;apply tagged_update_tag_free).
 unfold fix_update; eapply inf_tagged.
 - apply inf_Z; inf_tac.
 - apply inf_tag_free;reflexivity.
 - eapply update_abstractor_supported;
   [exact HS|apply constructor_recursive; exact HT].
Qed.

Set Default Proof Using "All".
Local Opaque equal equal1 get_tagname inf app.
Definition step N f r := specialised_update N f (children r).
(** The body, as a function of its name test [w] ([is_named N]) and action [g]; its type is
    the body at [IsNamed N] and the action type ([update_body_type]). *)
Definition update_body_with w g := Eval cbn in to_tree
 (star "r"
  (let ch := ''tagged[
    ''triage[Val Lf,Val Lf ''C Ref "r",
     star "x" (star "y" (Val Lf @@ (Ref "r" @@ Ref "x") @@ (Ref "r" @@ Ref "y")))],
    Val update_nm] in
   ''tagged[''S2[''S2[''S2[Val w, ''K1 (Val g)], ''K1 ch],Val 'I],
    Val update_nm])).
Definition update_body N f := update_body_with (is_named N) f.
Definition update_body_type N F := update_body_with (IsNamed N) F.
Definition update N f := fix_update (update_body N f).
Lemma body_eval : forall N f r, update_body N f @ r ==> step N f r.
Proof.
 intros; unfold update_body, update_body_with, step, specialised_update, if_named, children, update_one_level,
 update_fork; cbn; evaluate.
Qed.
Lemma update_unfold : forall N f u v,
 step N f (update N f) @ u ==> v -> update N f @ u ==> v.
Proof.
 intros N f u v H; unfold update, fix_update at 1; apply tagged_eval; apply Z_unfold.
 eapply eval_appl; [|exact H].
 eapply eval_c; eapply eval_appr;
 [apply tagged_update_eval|apply body_eval].
Qed.
Lemma update_hit : forall N f p v,
 f @ 'tagged[p,N] ==> v -> update N f @ 'tagged[p,N] ==> v.
Proof.
 intros; apply update_unfold; unfold step,specialised_update; apply tagged_eval.
 eapply if_named_hit; [apply get_tagname_some|exact H].
Qed.
Lemma update_default : forall N f u v,
 (forall p, u <> 'tagged[p,N]) -> update_one_level (update N f) @ u ==> v ->
 update N f @ u ==> v.
Proof.
 intros; apply update_unfold; unfold step,specialised_update; apply tagged_eval.
 apply if_named_default; [exact H|].
 unfold children; apply tagged_eval;exact H0.
Qed.

Section Typing.
Variable AI : Decl.
Variable N T f : Combination.
Hypothesis HS : supports AI.
Hypothesis HT : supports_is_named AI.
Hypothesis HN : concrete N.
Hypothesis HI : declared_wrapper AI N T.
Variable F : Combination.
Hypothesis HF : inf AI @ f ==> Sm F.
Hypothesis HFW : type_app AI @ F @r wrap_type T N ==> Sm (wrap_type T N).
Lemma inf_body : inf AI @ update_body N f ==> Sm (update_body_type N F).
Proof.
 pose proof (inf_is_named AI N HN HT) as HW.
 unfold update_body, update_body_type, update_body_with; cbn; inf_tac.
Qed.
Local Ltac body_app := first
 [eassumption | apply app_Update | apply app_I | apply app_K | apply app_leaf
 | new_S; [solve[intros;discriminate]| | |]
 | apply app_stem; first
   [apply type_app_stem_structural; solve[intros;discriminate]
   |apply type_app_stem_tagged; eapply update_abstractor_supported;[exact HS|];first
     [apply constructor_children
     |eapply constructor_choice;[exact HN|exact HI|exact HFW]]]].
Lemma app_body : app AI @ update_body_type N F @r ('Update) ==> Sm ('Update).
Proof.
 unfold update_body_type, update_body_with; cbn; repeat body_app.
Qed.
Lemma inf_updater : inf AI @ update N f ==> Sm ('Update).
Proof. unfold update; eapply inf_fix;[exact HS|apply inf_body|apply app_body]. Qed.
End Typing.

Lemma update_leaf : forall N f, update N f @ Lf ==> Lf.
Proof. intros; apply update_default;[intros;discriminate|apply update_one_level_leaf]. Qed.
Lemma update_stem : forall N f x y,
 update N f @ x ==> y -> update N f @ Sm x ==> Sm y.
Proof. intros; apply update_default;[intros;discriminate|apply update_one_level_stem;exact H]. Qed.
Lemma update_miss : forall N f x y x' y',
 (forall p, Fk x y <> 'tagged[p,N]) ->
 update N f @ x ==> x' -> update N f @ y ==> y' ->
 update N f @ Fk x y ==> Fk x' y'.
Proof. intros; apply update_default;[exact H|apply update_fork_eval;assumption]. Qed.

Definition supports_updates := supports.
(** The Update family is sound for values: the children carrier by
    [children_value_typing], every other carrier because it is sound for
    types. *)
Lemma update_abstractor_value_sound : forall AI,
  supports_updates AI -> sound_abstractor AI (update_abstractor_at AI).
Proof.
  intros AI HS n C E U V c v w HC HE Hc Hv He Ht.
  destruct (combination_eq_dec C (update_one_level ('Update))) as [->|Hch].
  - unfold update_abstractor_at in HC.
    destruct (constructor_inv _ _ _ HC) as [-> _].
    apply update_eliminator_inv in HE; subst V.
    eapply children_value_typing; eassumption.
  - eapply carrier_value_typing; [|exact Hc|exact Hv|exact He|exact Ht].
    eapply update_abstractor_sound; [eassumption|eassumption|right; exists v; exact Hv|eassumption|eassumption].
Qed.
Lemma infer_update : forall (AI : Decl) nm f F T,
 supports_updates AI -> supports_is_named AI ->
 concrete nm -> get_wrap_payload_type AI @ nm ==> Sm T ->
 infer AI @ f ==> Sm F ->
 type_app AI @ F @r wrap_type T nm ==> Sm (wrap_type T nm) ->
 infer AI @ update nm f ==> Sm ('Update).
Proof. intros; eapply inf_updater; try eassumption; apply get_wrap_payload_type_inv; assumption. Qed.
Definition update_case_package AI : {t : Combination |
  to_tree (tcase (Val update_nm) (Val (update_abstractor AI))) = t}.
Proof. eexists; cbn; reflexivity. Defined.
Definition update_case AI := Eval cbn in proj1_sig (update_case_package AI).
Local Lemma update_case_compilation : forall AI,
  to_tree (tcase (Val update_nm) (Val (update_abstractor AI))) = update_case AI.
Proof. intros; exact (proj2_sig (update_case_package AI)). Qed.
Lemma update_case_some : forall AI,
  update_case AI @ update_nm ==> Sm (update_abstractor AI).
Proof. intros; rewrite <- update_case_compilation; apply tcase_eq. Qed.
Lemma update_case_none : forall AI N, N <> update_nm -> update_case AI @ N ==> Lf.
Proof. intros; rewrite <- update_case_compilation; apply tcase_neq; congruence. Qed.
(** ** The Update clause registers the update abstractor, which is
    sound in declarations that support updates
    ([update_abstractor_sound]). *)


(** EPT turns the abstract Update contract into preservation of every
    argument type, including types unrelated to the selected wrapper. *)
Theorem abstract_update_preserves_typing : forall AI u x U y,
  ontology_sound AI ->
  infer AI @ u ==> Sm ('Update) -> infer AI @ x ==> Sm U ->
  u @ x ==> y -> infer AI @ y ==> Sm U.
Proof.
  intros AI u x U y HS Hu Hx HE.
  eapply evaluation_preserves_typing; eauto.
  eapply infer_expression_fork.
  - apply infer_expression_stem; exact Hu.
  - apply infer_expression_stem; exact Hx.
  - apply type_app_Update.
Qed.


Unset Default Proof Using.
Transparent get_update_composition get_recursive_update equal1 equal get_tagname get_IfNamed get_wrap_payload_type is_concrete app inf.

(** Close the name declarations captured by Query and Update introduction.

    The fixed point supplies the declarations to these two constructors.
    Looking up an ordinary name delegates to the base declarations; it does
    not recursively type an application. The lookup equations and their
    converse are the public interface used by concrete example declarations. *)
From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness.
Open Scope string_scope.
Set Default Proof Using "Type".

(** Reify just the construction of a closure containing [self]. Closed
    subtrees remain quoted constants. This is bracket-abstraction support,
    not an external implementation of name lookup or type inference.
    The constructors are unconditional, so reification compiles directly to
    a tree. There is no configuration-dependent projection.
    Keep the evaluation proofs opaque: projecting the compiled tree must
    not simplify the proof stored beside it. *)
Local Ltac ontology_term self tree :=
  lazymatch tree with
  | self => constr:(Ref "declarations")
  | context[self] =>
      let shape := eval hnf in tree in
      lazymatch shape with
      | Sm ?x => let tx := ontology_term self x in constr:(Val Lf @@ tx)
      | Fk ?x ?y =>
          let tx := ontology_term self x in
          let ty := ontology_term self y in constr:(Val Lf @@ tx @@ ty)
      end
  | _ => constr:(Val tree)
  end.

Definition query_case_builder_package :
  { b : Combination | forall AI, b @ AI ==> query_case AI }.
Proof.
  unfold query_case, query_case_package, query_abstractor, abstractor_intro, query_core, query_rest, query_fix_rest, choice_constructor.
  eexists; intro AI;
    match goal with |- ?program @ ?ai ==> ?target =>
      let t := ontology_term ai target in
      let b := eval cbn in (to_tree (star "declarations" t)) in
      unify program b
    end;
    abstract (cbn; evaluate).
Defined.
Definition query_case_builder : Combination :=
  Eval cbn in proj1_sig query_case_builder_package.
Lemma query_case_builder_eval : forall AI,
  query_case_builder @ AI ==> query_case AI.
Proof.
  intro AI; pose proof (proj2_sig query_case_builder_package AI) as H.
  unfold query_case_builder, query_case_builder_package,
    query_case, query_case_package, query_abstractor, abstractor_intro, query_core, query_rest, query_fix_rest, choice_constructor in *.
  exact H.
Qed.

Definition update_case_builder_package :
  { b : Combination | forall AI, b @ AI ==> update_case AI }.
Proof.
  unfold update_case, update_case_package, update_abstractor, abstractor_intro, update_core, update_choice_constructor.
  eexists; intro AI;
    match goal with |- ?program @ ?ai ==> ?target =>
      let t := ontology_term ai target in
      let b := eval cbn in (to_tree (star "declarations" t)) in
      unify program b
    end;
    abstract (cbn; evaluate).
Defined.
Definition update_case_builder : Combination :=
  Eval cbn in proj1_sig update_case_builder_package.
Lemma update_case_builder_eval : forall AI,
  update_case_builder @ AI ==> update_case AI.
Proof.
  intro AI; pose proof (proj2_sig update_case_builder_package AI) as H.
  unfold update_case_builder, update_case_builder_package,
    update_case, update_case_package, update_abstractor, abstractor_intro, update_core, update_choice_constructor in *.
  exact H.
Qed.

Definition generic_ontology_body base := Eval cbn in to_tree
  (star "declarations"
    (extend2 (Val query_case_builder @@ Ref "declarations")
      (extend2 (Val update_case_builder @@ Ref "declarations") (Val base)))).
Definition generic_ontology base := Z (generic_ontology_body base).

Lemma generic_ontology_body_eval : forall base AI,
  generic_ontology_body base @ AI ==>
    extend (query_case AI) (extend (update_case AI) base).
Proof.
  intros; unfold generic_ontology_body.
  pose proof (query_case_builder_eval AI).
  pose proof (update_case_builder_eval AI).
  evaluate.
Qed.
Lemma generic_ontology_step : forall base N C,
  extend (query_case (generic_ontology base))
    (extend (update_case (generic_ontology base)) base) @ N ==> C ->
  generic_ontology base @ N ==> C.
Proof.
  intros base N C H; unfold generic_ontology at 1; apply Z_unfold.
  eapply eval_appl; [apply generic_ontology_body_eval | exact H].
Qed.
Lemma generic_ontology_inv : forall base N C,
  generic_ontology base @ N ==> C ->
  extend (query_case (generic_ontology base))
    (extend (update_case (generic_ontology base)) base) @ N ==> C.
Proof.
  intros base N C H; unfold generic_ontology in H; apply Z_unfold_inv in H; inv_out H.
  match goal with HB : generic_ontology_body base @ Z (generic_ontology_body base) ==> ?b |- _ =>
    pose proof (eval_deterministic _ _ HB _ (generic_ontology_body_eval base _)) as HE;
    subst b end.
  assumption.
Qed.
Lemma generic_ontology_queries : forall base, supports_queries (generic_ontology base).
Proof. intros; apply generic_ontology_step; apply extend_some; apply query_case_some. Qed.
Lemma generic_ontology_updates : forall base, supports_updates (generic_ontology base).
Proof.
  intros; apply generic_ontology_step; apply extend_none_value.
  - apply query_case_none; discriminate.
  - apply extend_some; apply update_case_some.
Qed.
Lemma generic_ontology_ordinary : forall base N C,
  N <> query_nm -> N <> update_nm -> base @ N ==> C ->
  generic_ontology base @ N ==> C.
Proof.
  intros; apply generic_ontology_step.
  apply extend_none_value; [apply query_case_none; assumption |].
  apply extend_none_value; [apply update_case_none; assumption |assumption].
Qed.


Unset Default Proof Using.
Transparent get_update_composition get_recursive_update equal1 equal get_tagname get_IfNamed get_wrap_payload_type is_concrete app inf.

(** Treat decoration evidence as annotations.

    The target equations are
      ghost_case b q g (decorate[f,d]) = q f
      ghost_case b q g u = g u             when u is not decorated.
    Taking g=q gives the transformation q(decorate[f,d]) = q f;
    taking q as the recursive continuation and g as the ordinary traversal
    body gives the corresponding case for a recursive query.
    A Boolean query first recognises the whole decoration shape. On a hit,
    a query follows the six structural steps to f; on a miss, g receives
    the original input. The selected query runs only after this decision.
    Neither recognition nor the selected path visits d. The default b
    makes the path query total even off that path; the guard ensures this
    default is irrelevant on a decoration.

    All components use existing Query constructors, including diagonal
    application. There is no new type-application rule or Query constructor.
    The finite pattern and path describe the existing decoration encoding;
    no additional marker or runtime representation is introduced.

    The final two parts give closed examples and recursive annotation
    skipping. Employee collection and counting use this machinery in
    customisation.v, after its ordinary salary-update examples. *)
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans conditionals. (* merge: queries imported at the top *)
From Stdlib Require Import String Bool.
Open Scope string_scope.
Set Default Proof Using "Type".

(** Each path step is itself a query. A left-fork step delays its result
    in a constant query over the unused right branch. *)
Definition query_left b q :=
  'tq[b,'Kq b,'S_q['Kq typed_K_q,q]].
Definition query_right b q := 'tq[b,'Kq b,'Kq q].
Definition query_stem b q := 'tq[b,q,'Kq ('Kq b)].

Lemma query_left_eval : forall b q x y v,
  q @ x ==> v -> query_left b q @ Fk x y ==> v.
Proof.
  intros; unfold query_left; eapply triage_q_fork_eval.
  - eapply S_q_eval; [apply K_q_eval|exact H|apply typed_K_q_eval].
  - apply K_q_eval.
Qed.
Lemma query_right_eval : forall b q x y v,
  q @ y ==> v -> query_right b q @ Fk x y ==> v.
Proof. intros; unfold query_right; eapply triage_q_fork_eval; [apply K_q_eval|exact H]. Qed.
Lemma query_stem_eval : forall b q x v,
  q @ x ==> v -> query_stem b q @ Sm x ==> v.
Proof. intros; apply triage_q_stem_eval; exact H. Qed.

Section PathTyping.
Variable AI : Decl.
Hypothesis HQ : supports_queries AI.
Lemma query_left_typed : forall b B q,
  infer AI @ b ==> Sm B -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ query_left b q ==> Sm ('Query[B]).
Proof using AI HQ .
  intros b B q Hb Hq.
  assert (HK : infer AI @ ('Kq b) ==> Sm ('Query[B])) by (apply infer_Kq; assumption).
  assert (HL : infer AI @ ('S_q['Kq typed_K_q,q]) ==> Sm ('Query['Query[B]])).
  { eapply infer_S_q; [exact HQ| |exact Hq|apply type_app_typed_K_q; exact HQ].
    apply infer_Kq; [exact HQ|apply infer_typed_K_q_any]. }
  unfold query_left; apply infer_tq; [exact HQ|]; infer_tac.
Qed.
Lemma query_right_typed : forall b B q,
  infer AI @ b ==> Sm B -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ query_right b q ==> Sm ('Query[B]).
Proof using AI HQ.
  intros b B q Hb Hq.
  assert (HK : infer AI @ ('Kq b) ==> Sm ('Query[B])) by (apply infer_Kq; assumption).
  assert (HL : infer AI @ ('Kq q) ==> Sm ('Query['Query[B]])) by (apply infer_Kq; assumption).
  unfold query_right; apply infer_tq; [exact HQ|]; infer_tac.
Qed.
Lemma query_stem_typed : forall b B q,
  infer AI @ b ==> Sm B -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ query_stem b q ==> Sm ('Query[B]).
Proof using AI HQ.
  intros b B q Hb Hq.
  assert (HK : infer AI @ ('Kq ('Kq b)) ==> Sm ('Query['Query[B]]))
    by (repeat apply infer_Kq; assumption).
  unfold query_stem; apply infer_tq; [exact HQ|]; infer_tac.
Qed.
End PathTyping.

Definition query_decorated_program b q :=
  query_left b (query_stem b (query_left b (query_stem b
    (query_right b (query_right b q))))).
Lemma query_decorated_program_eval : forall b q f d v,
  q @ f ==> v -> query_decorated_program b q @ 'decorate[f,d] ==> v.
Proof.
  intros; unfold query_decorated_program.
  repeat first [apply query_left_eval | apply query_stem_eval | apply query_right_eval | assumption].
Qed.
Lemma query_decorated_program_typed : forall (AI : Decl) b B q,
  supports_queries AI -> 
  infer AI @ b ==> Sm B -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ query_decorated_program b q ==> Sm ('Query[B]).
Proof.
  intros; unfold query_decorated_program.
  repeat first [assumption | apply query_left_typed | apply query_stem_typed | apply query_right_typed].
Qed.

(** Both component positions are holes: recognition inspects neither f nor d. *)
Definition decoration_pattern :=
  PFork (PStem (PFork (PStem (PFork PLeaf (PFork PLeaf PAny)))
                     (PFork PLeaf PAny)))
        (PFork (PStem (PStem PLeaf)) (PStem PLeaf)).
Definition is_decoration_query := pattern_query decoration_pattern.
Lemma decoration_pattern_hit : forall f d,
  pattern_matches decoration_pattern ('decorate[f,d]) = true.
Proof. reflexivity. Qed.
Lemma decoration_pattern_inv : forall u,
  pattern_matches decoration_pattern u = true ->
  exists f d, u = 'decorate[f,d].
Proof.
  intro u; unfold decoration_pattern; cbn [pattern_matches]; intro H.
  repeat match type of H with
  | context [match ?v with Lf => _ | Sm _ => _ | Fk _ _ => _ end] =>
    destruct v; cbn in H; try discriminate
  end.
  do 2 eexists; reflexivity.
Qed.
Lemma is_decoration_query_typed : forall AI,
  supports_queries AI -> supports_booleans AI -> 
  infer AI @ is_decoration_query ==> Sm ('Query['Bool]).
Proof. intros; apply pattern_query_typed; assumption. Qed.
Lemma is_decoration_query_hit : forall f d,
  is_decoration_query @ 'decorate[f,d] ==> 'tt.
Proof. intros; exact (pattern_query_eval decoration_pattern ('decorate[f,d])). Qed.
Lemma is_decoration_query_miss : forall u,
  (forall f d, u <> 'decorate[f,d]) -> is_decoration_query @ u ==> 'ff.
Proof.
  intros u H; pose proof (pattern_query_eval decoration_pattern u) as HP.
  destruct (pattern_matches decoration_pattern u) eqn:E; [|exact HP].
  apply decoration_pattern_inv in E; destruct E as [f [d ->]].
  contradiction (H f d eq_refl).
Qed.

(** Select the query value before running either action. *)
Definition choose_queries p q := 'S2['I,'K1 (p '* q)].
Definition choose_type B := 'S2['I,'K1 (('Query[B]) '* ('Query[B]))].
Lemma choose_queries_typed : forall (AI : Decl) p q B,
  infer AI @ p ==> Sm ('Query[B]) -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ choose_queries p q ==> Sm (choose_type B).
Proof. intros; unfold choose_queries, choose_type; infer_tac. Qed.
Lemma type_app_choose : forall (AI : Decl) B, supports_booleans AI ->
  type_app AI @ choose_type B @r ('Bool) ==> Sm ('Query[B]).
Proof.
  intros AI B HB; unfold choose_type.
  new_S; [discriminate|apply type_app_I|apply type_app_K_ev|].
  apply type_app_abstract; apply bool_eliminator_some.
Qed.
Lemma choose_queries_true : forall p q, choose_queries p q @ ('tt) ==> p.
Proof. intros; unfold choose_queries; evaluate. Qed.
Lemma choose_queries_false : forall p q, choose_queries p q @ ('ff) ==> q.
Proof. intros; unfold choose_queries; evaluate. Qed.

(** q handles the executable part; g handles a non-decoration. Keeping
    these separate permits a recursive q with an ordinary triage as g.
    Taking g=q gives the nonrecursive transformation discussed above. *)
Definition ghost_case b q g :=
  diagonal_query ('S_q['Kq (choose_queries (query_decorated_program b q) g),
    is_decoration_query]).
Lemma ghost_case_typed : forall (AI : Decl) b B q g,
  supports_queries AI -> supports_booleans AI -> 
  infer AI @ b ==> Sm B ->
  infer AI @ q ==> Sm ('Query[B]) -> infer AI @ g ==> Sm ('Query[B]) ->
  infer AI @ ghost_case b q g ==> Sm ('Query[B]).
Proof.
  intros AI b B q g HQ HB Hb Hq Hg; unfold ghost_case.
  apply infer_diagonal_query; [exact HQ|].
  eapply infer_S_q; [exact HQ| | |apply type_app_choose; exact HB].
  - apply infer_Kq; [exact HQ|].
    apply choose_queries_typed; try assumption.
    apply query_decorated_program_typed; assumption.
  - apply is_decoration_query_typed; assumption.
Qed.
Lemma ghost_case_hit : forall b q g f d v,
  q @ f ==> v -> ghost_case b q g @ 'decorate[f,d] ==> v.
Proof.
  intros; unfold ghost_case; eapply diagonal_query_eval.
  - eapply S_q_eval; [apply K_q_eval|apply is_decoration_query_hit|apply choose_queries_true].
  - apply query_decorated_program_eval; assumption.
Qed.
Lemma ghost_case_miss : forall b q g u v,
  (forall f d, u <> 'decorate[f,d]) -> g @ u ==> v ->
  ghost_case b q g @ u ==> v.
Proof.
  intros; unfold ghost_case; eapply diagonal_query_eval.
  - eapply S_q_eval; [apply K_q_eval|apply is_decoration_query_miss; assumption|apply choose_queries_false].
  - assumption.
Qed.

(** The conditional [ghost_case[b,q,h]]: a haunted program
    [decorate[f,w]] goes to [q @ f], ignoring the ghost [w], and any other
    value [u] to [h @ u]. *)
Example ghost_case_haunted : forall b q h f w v,
  q @ f ==> v -> ghost_case b q h @ 'decorate[f,w] ==> v.
Proof. exact ghost_case_hit. Qed.
Example ghost_case_other : forall b q h u v,
  (forall f w, u <> 'decorate[f,w]) -> h @ u ==> v -> ghost_case b q h @ u ==> v.
Proof. exact ghost_case_miss. Qed.

(** Function annotation needs no declarations entry or extra witness marker. *)
Example annotation_lam_shape : forall f d,
  lam f d = 'tagged['decorate[f,d],fun_nm].
Proof. reflexivity. Qed.
Lemma annotation_lam_typed : forall (AI : Decl) f F d U V,
  infer AI @ f ==> Sm F -> infer AI @ d ==> Sm U ->
  type_app AI @ F @r U ==> Sm V ->
  infer AI @ lam f d ==> Sm (U --> V).
Proof.
  intros; apply infer_lam with (F:=F); assumption.
Qed.
Lemma annotation_lam_eval : forall f d u v,
  f @ u ==> v -> lam f d @ u ==> v.
Proof. intros; unfold lam; apply tagged_eval; apply wait_eval; evaluate. Qed.

(** The body is inspected and the annotation ignored; these results are
    deliberately different. Neither theorem constrains the annotation. *)
Example inspect_leaf_program : forall d,
  ghost_case ('ff) equality_leaf equality_leaf @ 'decorate[Lf,d] ==> 'tt.
Proof. intros; apply ghost_case_hit; apply triage_q_leaf_eval. Qed.
Example inspect_stem_program : forall x d,
  ghost_case ('tt) equality_leaf equality_leaf @ 'decorate[Sm x,d] ==> 'ff.
Proof. intros; apply ghost_case_hit; apply triage_q_stem_eval; apply K_q_eval. Qed.
Example fallback_sees_original :
  ghost_case ('tt) ('Kq 'tt) equality_leaf @ Sm Lf ==> 'ff.
Proof.
  apply ghost_case_miss; [intros; discriminate|].
  apply triage_q_stem_eval; apply K_q_eval.
Qed.

(** Term forms for abstraction over the recursive query. Closed defaults
    and coefficients stay quoted; no extra runtime constructor is added. *)
Definition query_decorated_program_term b q :=
  let left r := ''tq[Val b,Val ('Kq b),
    ''S_q[''Kq (Val typed_K_q),r]] in
  let stem r := ''tq[Val b,r,Val ('Kq ('Kq b))] in
  let right r := ''tq[Val b,Val ('Kq b),''Kq r] in
  left (stem (left (stem (right (right q))))).
Definition ghost_case_term b q g :=
  ''tagged[''S2[
    ''S_q[''Kq (''S2[Val 'I,''K1 (query_decorated_program_term b q ''* g)]),
      Val is_decoration_query],Val 'I],Val query_nm].


(** Direct-annotation examples with a concrete Boolean/Query declarations. *)

Lemma generic_ontology_row : forall base,
  base @ fun_nm ==> function_abstractor -> generic_ontology base @ fun_nm ==> function_abstractor.
Proof.
  intros base H; apply generic_ontology_ordinary;
    [unfold query_nm, fun_nm; discriminate|unfold update_nm, fun_nm; discriminate|exact H].
Qed.
Definition annotation_ontology := generic_ontology bool_ontology.
Canonical Structure annotation_decl :=
  mkDecl annotation_ontology (generic_ontology_row _ bool_ontology_row).
Lemma annotation_ontology_queries : supports_queries annotation_ontology.
Proof. apply generic_ontology_queries. Qed.
Lemma annotation_ontology_booleans : supports_booleans annotation_ontology.
Proof.
  unfold supports_booleans, annotation_ontology.
  apply generic_ontology_ordinary; try discriminate.
  apply bool_ontology_supports_booleans.
Qed.


(** The test inspects the executable part, rather than returning one fixed
    result for every decoration. It needs no witness declarations entry. *)
Definition inspect_program := ghost_case ('ff) equality_leaf equality_leaf.
Lemma inspect_program_typed :
  infer annotation_ontology @ inspect_program ==> Sm ('Query['Bool]).
Proof.
  unfold inspect_program; apply ghost_case_typed;
    auto using annotation_ontology_queries, annotation_ontology_booleans.
  - apply ff_infer; apply annotation_ontology_booleans.
  - apply infer_equality_leaf; auto using annotation_ontology_queries,
      annotation_ontology_booleans.
  - apply infer_equality_leaf; auto using annotation_ontology_queries,
      annotation_ontology_booleans.
Qed.
Example inspect_leaf_ignores_evidence : forall d,
  inspect_program @ 'decorate[Lf,d] ==> 'tt.
Proof. apply inspect_leaf_program. Qed.
Example direct_identity_in_empty_ontology : 
  infer function_ontology @ lam ('I) Lf ==> Sm (Lf --> Lf).
Proof.
  apply annotation_lam_typed with (F:='I);
    [apply infer_I|apply infer_leaf|apply type_app_I].
Qed.
Example direct_identity_eval : forall d u,
  lam ('I) d @ u ==> u.
Proof. intros; apply annotation_lam_eval; evaluate. Qed.

(** Two levels of case composition demonstrate that nested annotations can
    be stripped while retaining the actual executable leaf. *)
Example nested_annotations : forall d e,
  ghost_case ('ff) inspect_program equality_leaf @
    'decorate['decorate[Lf,d],e] ==> 'tt.
Proof. intros; apply ghost_case_hit; apply inspect_leaf_ignores_evidence. Qed.


(** A closed recursive Query satisfying q(decorate[f,d]) = q f.
    At the first non-decoration it uses equality_leaf. Thus the test still
    distinguishes a leaf program from a stem program, after arbitrarily
    many decorations. Recursion is the existing guarded Query fixed point. *)

(** Quote only the occurrences of the recursive query. Closed coefficients
    remain quoted constants, as in the existing declarations closure compiler. *)
Local Ltac quote_query q tree :=
  lazymatch tree with
  | q => constr:(Ref "q")
  | context[q] =>
    let shape := eval hnf in tree in
    lazymatch shape with
    | Sm ?x => let tx := quote_query q x in constr:(Val Lf @@ tx)
    | Fk ?x ?y => let tx := quote_query q x in let ty := quote_query q y in
      constr:(Val Lf @@ tx @@ ty)
    end
  | _ => constr:(Val tree)
  end.
Definition strip_annotations_body_package :
  {body : Combination | forall q,
    body @ q ==> ghost_case ('ff) q equality_leaf}.
Proof.
  eexists; intro q.
  let term := quote_query q constr:(ghost_case ('ff) q equality_leaf) in
  let body := eval cbn in (to_tree (star "q" term)) in
  match goal with |- ?p @ q ==> _ => unify p body end.
  evaluate.
Defined.
Definition strip_annotations_body := Eval cbn in proj1_sig strip_annotations_body_package.
Lemma strip_annotations_body_eval : forall q,
  strip_annotations_body @ q ==> ghost_case ('ff) q equality_leaf.
Proof. exact (proj2_sig strip_annotations_body_package). Qed.
Definition strip_annotations_function := 'decorate[strip_annotations_body, equality_leaf].
Definition strip_annotations := fix_query strip_annotations_function.
Lemma strip_annotations_function_eval : forall q,
  strip_annotations_function @ q ==> ghost_case ('ff) q equality_leaf.
Proof.
  intros; unfold strip_annotations_function; apply wait_eval.
  pose proof (strip_annotations_body_eval q); evaluate.
Qed.

Local Lemma fix_query_eval_step : forall f u v,
  f @ fix_query f @r u ==> v -> fix_query f @ u ==> v.
Proof.
  intros f u v H; inv_out H.
  unfold fix_query at 1; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|eassumption].
  eapply eval_c; eapply eval_appr.
  - unfold tagged_query; evaluate.
  - eassumption.
Qed.
Lemma strip_annotations_step : forall u v,
  ghost_case ('ff) strip_annotations equality_leaf @ u ==> v ->
  strip_annotations @ u ==> v.
Proof.
  intros; unfold strip_annotations at 1; apply fix_query_eval_step.
  eapply eval_appl; [apply strip_annotations_function_eval|exact H].
Qed.

Section Typing.
Local Ltac query_app := first
  [ lazymatch goal with
    | |- type_app _ @ ('Query[?B]) @r _ ==> _ =>
        apply type_app_abstract; apply query_eliminator_eval
    | |- type_app _ @ Sm _ @r _ ==> _ => eapply type_app_stem_ev
    | |- type_app _ @ ('Bool) @r _ ==> _ =>
        apply type_app_abstract; apply bool_eliminator_some
    | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
        apply type_app_stem_tagged; eapply query_abstractor_supported; [apply annotation_ontology_queries|];
          first [apply query_abstractor_K | eapply query_abstractor_S |
            apply query_abstractor_triage | apply query_abstractor_diagonal]
    end
  | progress type_app_tac ].
Local Definition strip_annotations_body_type :
  { F : Combination |
    infer annotation_ontology @ strip_annotations_body ==> Sm F /\
    type_app annotation_ontology @ F @r ('Query['Bool]) ==> Sm ('Query['Bool]) }.
Proof.
  assert (Htt : infer annotation_ontology @ ('tt) ==> Sm ('Bool))
    by (apply tt_infer; apply annotation_ontology_booleans).
  assert (Hff : infer annotation_ontology @ ('ff) ==> Sm ('Bool))
    by (apply ff_infer; apply annotation_ontology_booleans).
  assert (Hpred : infer annotation_ontology @ is_decoration_query ==> Sm ('Query['Bool]))
    by (apply is_decoration_query_typed; auto using annotation_ontology_queries,
      annotation_ontology_booleans).
  assert (Hleaf : infer annotation_ontology @ equality_leaf ==> Sm ('Query['Bool]))
    by (apply infer_equality_leaf; auto using annotation_ontology_queries,
      annotation_ontology_booleans).
  pose proof (infer_typed_K_q_any annotation_ontology) as Hconst.
  pose proof (type_app_typed_K_q annotation_ontology ('Bool) annotation_ontology_queries) as HconstB.
  pose proof (type_app_choose annotation_ontology ('Bool) annotation_ontology_booleans) as Hchoose.
  eexists; split; unfold strip_annotations_body, strip_annotations_body_package; cbn.
  all: timeout 60 repeat first [eassumption | apply bool_eliminator_some | progress infer_tac | query_app].

Defined.
Lemma strip_annotations_typed :
  infer annotation_ontology @ strip_annotations ==> Sm ('Query['Bool]).
Proof.
  unfold strip_annotations, strip_annotations_function; eapply infer_fix_query;
    [apply annotation_ontology_queries| | |].
  - exact (proj1 (proj2_sig strip_annotations_body_type)).
  - apply infer_equality_leaf; auto using annotation_ontology_queries,
      annotation_ontology_booleans.
  - exact (proj2 (proj2_sig strip_annotations_body_type)).
Qed.
End Typing.

(** * Ghost updates

    The update counterpart of [ghost_case]. [ghost_update k h] maps a
    haunted program [decorate[f,w]] to [decorate[f',w]], where k updates f
    to f', and leaves the ghost w untouched; any other value u goes to
    [h @ u]. It is a query-selected update: the ghost-aware query
    [ghost_query k h] selects [ghost_rebuild k] on a haunted program and h
    otherwise, and the selected update is applied to the same argument.
    Its typing uses the query-update case of the Update introduction;
    the rebuilding of [decorate[f',w]] is typed by the
    children case. The default of [ghost_case] is the identity
    update; it is never selected on a decoration. *)
Definition ghost_query k h :=
  ghost_case identity_update ('Kq (ghost_rebuild k)) ('Kq h).
Definition ghost_update k h := query_update (ghost_query k h).

Lemma ghost_update_haunted : forall k h f f' w,
  k @ f ==> f' -> ghost_update k h @ 'decorate[f,w] ==> 'decorate[f',w].
Proof.
  intros; unfold ghost_update; eapply query_update_eval.
  - unfold ghost_query; apply ghost_case_hit; apply K_q_eval.
  - apply ghost_rebuild_eval; assumption.
Qed.
Lemma ghost_update_other : forall k h u v,
  (forall f w, u <> 'decorate[f,w]) -> h @ u ==> v -> ghost_update k h @ u ==> v.
Proof.
  intros; unfold ghost_update; eapply query_update_eval; [|eassumption].
  unfold ghost_query; apply ghost_case_miss; [assumption|apply K_q_eval].
Qed.
Lemma ghost_update_typed : forall (AI : Decl) k h,
  supports_queries AI -> supports_booleans AI -> supports_updates AI ->
  infer AI @ k ==> Sm ('Update) -> infer AI @ h ==> Sm ('Update) ->
  infer AI @ ghost_update k h ==> Sm ('Update).
Proof.
  intros AI k h HQ HB HU Hk Hh; unfold ghost_update, ghost_query.
  apply inf_query_update; [exact HU|].
  apply ghost_case_typed; try assumption.
  - apply inf_identity; exact HU.
  - apply infer_Kq; [exact HQ|]; apply inf_ghost_rebuild; assumption.
  - apply infer_Kq; assumption.
Qed.

(** Term forms, for abstraction over the recursive update. *)
Definition children2_term rs rl rr :=
  ''tagged[''triage[Val Lf, Val Lf ''C rs,
    star "x" (star "y" (Val Lf @@ (rl @@ Ref "x") @@ (rr @@ Ref "y")))], Val update_nm].
Definition ghost_rebuild_term k :=
  let i := Val identity_update in
  children2_term i (children2_term (children2_term i (children2_term
    (children2_term i i (children2_term i i k)) i i) i) i i) i.
Definition ghost_update_term k h :=
  ''tagged[''S2[ghost_case_term identity_update
    (''Kq (ghost_rebuild_term k)) (''Kq h), Val 'I], Val update_nm].

(** * The list tag

    A list has one tag.  [cons_case] tests it once by name, then walks the
    plain spine; at nil it gives its default, so a ghost is not read.  The
    test [is_list_q] is a compact compilation of a pattern, by nested triage
    queries.  No new typing rule is used. *)
From TreeTyping Require Import data_types.
From Stdlib Require List.
Fixpoint exact_pat (t : Combination) : query_pattern :=
  match t with
  | Lf => PLeaf
  | Sm u => PStem (exact_pat u)
  | Fk u v => PFork (exact_pat u) (exact_pat v)
  end.

Definition tag_pat body name :=
  PFork (PStem (PFork PLeaf body)) (PFork (PStem (PStem PLeaf)) (PFork PLeaf name)).
Definition swap_pat p := PFork (PStem (exact_pat 'I)) (PFork PLeaf p).
Definition pair_pat p q :=
  PFork (PStem (PFork (PStem (exact_pat 'I)) (PFork PLeaf p))) (PFork PLeaf q).

Definition cond p a c :=
  diagonal_query ('S_q['Kq (choose_queries a c), p]).

Lemma cond_typed : forall (AI : Decl) p a c B,
  supports_queries AI -> supports_booleans AI ->
  infer AI @ p ==> Sm ('Query['Bool]) ->
  infer AI @ a ==> Sm ('Query[B]) -> infer AI @ c ==> Sm ('Query[B]) ->
  infer AI @ cond p a c ==> Sm ('Query[B]).
Proof.
  intros AI p a c B HQ HB Hp Ha Hc; unfold cond.
  apply infer_diagonal_query; [exact HQ|].
  eapply infer_S_q; [exact HQ| |exact Hp|apply type_app_choose; exact HB].
  apply infer_Kq; [exact HQ|]; apply choose_queries_typed; assumption.
Qed.
Lemma cond_hit : forall p a c u v,
  p @ u ==> 'tt -> a @ u ==> v -> cond p a c @ u ==> v.
Proof.
  intros; unfold cond; eapply diagonal_query_eval;
    [eapply S_q_eval; [apply K_q_eval|eassumption|apply choose_queries_true]|assumption].
Qed.
Lemma cond_miss : forall p a c u v,
  p @ u ==> 'ff -> c @ u ==> v -> cond p a c @ u ==> v.
Proof.
  intros; unfold cond; eapply diagonal_query_eval;
    [eapply S_q_eval; [apply K_q_eval|eassumption|apply choose_queries_false]|assumption].
Qed.

(** A path of [query_left], [query_right] and [query_stem]. *)
Fixpoint path_query b (ds : list dir) q :=
  match ds with
  | List.nil => q
  | List.cons dir_l ds' => query_left b (path_query b ds' q)
  | List.cons dir_r ds' => query_right b (path_query b ds' q)
  | List.cons dir_s ds' => query_stem b (path_query b ds' q)
  end.

Fixpoint path_valid (ds : list dir) x : Prop :=
  match ds, x with
  | List.nil, _ => True
  | List.cons dir_l ds', Fk a _ => path_valid ds' a
  | List.cons dir_r ds', Fk _ c => path_valid ds' c
  | List.cons dir_s ds', Sm a => path_valid ds' a
  | _, _ => False
  end.

Lemma path_query_eval : forall ds b q x v,
  path_valid ds x -> q @ path_fn ds x ==> v -> path_query b ds q @ x ==> v.
Proof.
  induction ds as [|[] ds IH]; intros b q x v Hp Hv; cbn [path_query];
    [exact Hv|..]; destruct x; cbn in Hp; try contradiction.
  - apply query_left_eval; apply IH; assumption.
  - apply query_right_eval; apply IH; assumption.
  - apply query_stem_eval; apply IH; assumption.
Qed.

Lemma path_query_typed : forall (AI : Decl) ds b B q,
  supports_queries AI -> infer AI @ b ==> Sm B -> infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ path_query b ds q ==> Sm ('Query[B]).
Proof.
  induction ds as [|[] ds IH]; intros b B q HQ Hb Hq; cbn [path_query]; [exact Hq|..].
  - apply query_left_typed; [exact HQ|exact Hb|apply IH; assumption].
  - apply query_right_typed; [exact HQ|exact Hb|apply IH; assumption].
  - apply query_stem_typed; [exact HQ|exact Hb|apply IH; assumption].
Qed.

Definition path_cell_q : list dir :=
  List.cons dir_l (List.cons dir_s (List.cons dir_r (List.cons dir_l (List.cons dir_s
  (List.cons dir_r (List.cons dir_r List.nil)))))).

Fixpoint path_update (ds : list dir) k :=
  let i := identity_update in
  match ds with
  | List.nil => k
  | List.cons dir_l ds' => children2 i (path_update ds' k) i
  | List.cons dir_r ds' => children2 i i (path_update ds' k)
  | List.cons dir_s ds' => children2 (path_update ds' k) i i
  end.

Fixpoint path_set (ds : list dir) x y :=
  match ds, x with
  | List.nil, _ => y
  | List.cons dir_l ds', Fk a c => Fk (path_set ds' a y) c
  | List.cons dir_r ds', Fk a c => Fk a (path_set ds' c y)
  | List.cons dir_s ds', Sm a => Sm (path_set ds' a y)
  | _, _ => x
  end.

Lemma path_update_eval : forall ds k x y,
  path_valid ds x -> k @ path_fn ds x ==> y -> path_update ds k @ x ==> path_set ds x y.
Proof.
  induction ds as [|[] ds IH]; intros k x y Hp Hv; cbn [path_update];
    [exact Hv|..]; destruct x; cbn in Hp; try contradiction; cbn [path_set].
  - apply children2_fork; [apply IH; assumption|apply identity_update_eval].
  - apply children2_fork; [apply identity_update_eval|apply IH; assumption].
  - apply children2_stem; apply IH; assumption.
Qed.

Lemma path_update_typed : forall AI ds k,
  supports_updates AI -> infer AI @ k ==> Sm ('Update) ->
  infer AI @ path_update ds k ==> Sm ('Update).
Proof.
  induction ds as [|[] ds IH]; intros k HU Hk; cbn [path_update]; [exact Hk|..];
    apply inf_children2; try exact HU; try (apply inf_identity; exact HU); apply IH; assumption.
Qed.

Fixpoint path_query_t b (ds : list dir) (q : Term) : Term :=
  match ds with
  | List.nil => q
  | List.cons dir_l ds' => ''tq[Val b,Val ('Kq b),
      ''S_q[''Kq (Val typed_K_q), path_query_t b ds' q]]
  | List.cons dir_r ds' => ''tq[Val b,Val ('Kq b),''Kq (path_query_t b ds' q)]
  | List.cons dir_s ds' => ''tq[Val b,path_query_t b ds' q,Val ('Kq ('Kq b))]
  end.
Definition cond_t p (a c : Term) : Term :=
  ''tagged[''S2[''S_q[''Kq (''S2[Val 'I,''K1 (a ''* c)]),Val p],Val 'I],
    Val query_nm].
Fixpoint path_update_t (ds : list dir) (k : Term) : Term :=
  let i := Val identity_update in
  match ds with
  | List.nil => k
  | List.cons dir_l ds' => children2_term i (path_update_t ds' k) i
  | List.cons dir_r ds' => children2_term i i (path_update_t ds' k)
  | List.cons dir_s ds' => children2_term (path_update_t ds' k) i i
  end.
Ltac pat_inv H :=
  cbn [pattern_matches] in H;
  repeat match type of H with
  | context [match ?v with Lf => _ | Sm _ => _ | Fk _ _ => _ end] =>
    destruct v; cbn in H; try discriminate
  end.

Definition list_pat := Eval cbv in tag_pat PAny (exact_pat list_nm).
Definition is_list_q := pattern_query list_pat.

Lemma is_list_q_eval : forall u, is_list_q @ u ==> (if pattern_matches list_pat u then 'tt else 'ff).
Proof. intros; apply pattern_query_eval. Qed.
Lemma list_pat_nil : forall a, pattern_matches list_pat (nil_value a) = true.
Proof. reflexivity. Qed.
Lemma list_pat_cell : forall x s, pattern_matches list_pat (cell x s) = true.
Proof. reflexivity. Qed.

(** One test of the name. *)
Lemma list_pat_inv : forall u, pattern_matches list_pat u = true ->
  exists C, u = 'tagged[C, list_nm].
Proof.
  intros u H; unfold list_pat in H; pat_inv H; eexists; reflexivity.
Qed.

Lemma is_list_q_typed : forall AI, supports_queries AI -> supports_booleans AI ->
  infer AI @ is_list_q ==> Sm ('Query['Bool]).
Proof. intros; apply pattern_query_typed; assumption. Qed.

(** Past the list tag there is no second name test: a carrier of a list is
    the delay ['wait[M,c]], and the walk goes to its left part.  The
    program [M] tells a nil from a cons: at a cons the query goes on to
    the pair [c] of head and tail, and at a nil it stops at [b], so the
    ghost is never reached. *)
Definition path_to_cell : list dir :=
  List.cons dir_l (List.cons dir_s (List.cons dir_r (List.cons dir_l (List.cons dir_s List.nil)))).
Definition flag_pat := Eval cbv in
  PStem (PFork PLeaf (PFork (PStem PAny) PAny)).
Definition cell_payload c := Fk (Sm ('K1 cell_run)) ('K1 c).
Definition nil_payload a := Fk (Sm ('K1 ('K1 'fst))) ('K1 a).

Definition payload_q b next := 'tq[b, 'Kq b, pc flag_pat ('Kq b) next].
Definition inner_q b q := payload_q b ('tq[b, 'Kq b, 'Kq q]).

Definition cons_case b q h :=
  cond is_list_q (path_query b path_to_cell (inner_q b q)) h.

Lemma payload_q_typed : forall AI b B n, supports_queries AI -> infer AI @ b ==> Sm B ->
  infer AI @ n ==> Sm ('Query[B]) -> infer AI @ payload_q b n ==> Sm ('Query[B]).
Proof.
  intros AI b B n HQ Hb Hn; unfold payload_q.
  apply infer_tq_intro; try assumption; [apply infer_Kq; assumption|].
  apply pc_typed; [assumption|apply infer_Kq; assumption|assumption].
Qed.

Lemma inner_q_typed : forall AI b B q, supports_queries AI -> infer AI @ b ==> Sm B ->
  infer AI @ q ==> Sm ('Query[B]) -> infer AI @ inner_q b q ==> Sm ('Query[B]).
Proof.
  intros AI b B q HQ Hb Hq; unfold inner_q; apply payload_q_typed with (B := B); try assumption.
  apply infer_tq_intro; try assumption; repeat apply infer_Kq; assumption.
Qed.

Lemma cons_case_typed : forall (AI : Decl) b B q h,
  supports_queries AI -> supports_booleans AI -> infer AI @ b ==> Sm B ->
  infer AI @ q ==> Sm ('Query[B]) -> infer AI @ h ==> Sm ('Query[B]) ->
  infer AI @ cons_case b q h ==> Sm ('Query[B]).
Proof.
  intros AI b B q h HQ HB Hb Hq Hh; unfold cons_case.
  apply cond_typed; try assumption; [apply is_list_q_typed; assumption|].
  apply path_query_typed with (B := B); try assumption.
  apply inner_q_typed with (B := B); assumption.
Qed.

Lemma payload_q_K : forall b n y v, n @ ('K1 y) ==> v ->
  payload_q b n @ cell_payload y ==> v.
Proof.
  intros; unfold payload_q; eapply triage_q_fork_eval; [apply (pc_eval flag_pat)|].
  exact H.
Qed.
Lemma payload_q_KI : forall b n y, payload_q b n @ nil_payload y ==> b.
Proof.
  intros; unfold payload_q; eapply triage_q_fork_eval; [apply (pc_eval flag_pat)|].
  apply K_q_eval.
Qed.

Lemma cons_case_cell : forall b q h x s v,
  q @ (x '* s) ==> v -> cons_case b q h @ cell x s ==> v.
Proof.
  intros b q h x s v H; unfold cons_case; apply cond_hit.
  - pose proof (is_list_q_eval (cell x s)) as E; rewrite list_pat_cell in E; exact E.
  - apply (path_query_eval path_to_cell b (inner_q b q) (cell x s) v); [exact I|].
    change (inner_q b q @ cell_payload (x '* s) ==> v).
    unfold inner_q; apply payload_q_K; eapply triage_q_fork_eval; [apply K_q_eval|exact H].
Qed.
Lemma cons_case_nil : forall b q h a, cons_case b q h @ nil_value a ==> b.
Proof.
  intros b q h a; unfold cons_case; apply cond_hit.
  - pose proof (is_list_q_eval (nil_value a)) as E; rewrite list_pat_nil in E; exact E.
  - apply (path_query_eval path_to_cell b (inner_q b q) (nil_value a) b); [exact I|].
    change (inner_q b q @ nil_payload a ==> b); apply payload_q_KI.
Qed.
Lemma cons_case_miss : forall b q h u v,
  pattern_matches list_pat u = false -> h @ u ==> v -> cons_case b q h @ u ==> v.
Proof.
  intros b q h u v H1 H; unfold cons_case; apply cond_miss; [|exact H].
  pose proof (is_list_q_eval u) as E; rewrite H1 in E; exact E.
Qed.

(** The update: selected by the same queries. *)
Definition cons_update_q k h :=
  cond is_list_q
    (path_query identity_update path_to_cell
      (payload_q identity_update ('Kq (path_update path_cell_q k))))
    ('Kq h).
Definition cons_update k h := query_update (cons_update_q k h).

Lemma cons_update_typed : forall (AI : Decl) k h,
  supports_queries AI -> supports_booleans AI -> supports_updates AI ->
  infer AI @ k ==> Sm ('Update) -> infer AI @ h ==> Sm ('Update) ->
  infer AI @ cons_update k h ==> Sm ('Update).
Proof.
  intros AI k h HQ HB HU Hk Hh; unfold cons_update, cons_update_q.
  assert (Hi : infer AI @ identity_update ==> Sm ('Update)) by (apply inf_identity; exact HU).
  apply inf_query_update; [exact HU|].
  apply cond_typed; try assumption; [apply is_list_q_typed; assumption| |apply infer_Kq; assumption].
  apply path_query_typed with (B := 'Update); try assumption.
  apply payload_q_typed with (B := 'Update); try assumption.
  apply infer_Kq; [assumption|apply path_update_typed; assumption].
Qed.

Lemma cons_update_cell : forall k h x s y,
  k @ (x '* s) ==> y -> cons_update k h @ cell x s ==>
    path_set path_cell_q (cell x s) y.
Proof.
  intros k h x s y H; unfold cons_update;
    eapply query_update_eval with (r := path_update path_cell_q k).
  - unfold cons_update_q; apply cond_hit.
    + pose proof (is_list_q_eval (cell x s)) as E; rewrite list_pat_cell in E; exact E.
    + apply (path_query_eval path_to_cell _ _ (cell x s) _); [exact I|].
      change (payload_q identity_update ('Kq (path_update path_cell_q k)) @
        cell_payload (x '* s) ==> path_update path_cell_q k).
      apply payload_q_K; apply K_q_eval.
  - apply (path_update_eval path_cell_q k (cell x s) y); [exact I|exact H].
Qed.
Lemma cons_update_nil : forall k h a, cons_update k h @ nil_value a ==> nil_value a.
Proof.
  intros k h a; unfold cons_update; eapply query_update_eval with (r := identity_update).
  - unfold cons_update_q; apply cond_hit.
    + pose proof (is_list_q_eval (nil_value a)) as E; rewrite list_pat_nil in E; exact E.
    + apply (path_query_eval path_to_cell _ _ (nil_value a) identity_update); [exact I|].
      change (payload_q identity_update ('Kq (path_update path_cell_q k)) @
        nil_payload a ==> identity_update).
      apply payload_q_KI.
  - apply identity_update_eval.
Qed.
Lemma cons_update_miss : forall k h u v,
  pattern_matches list_pat u = false -> h @ u ==> v -> cons_update k h @ u ==> v.
Proof.
  intros k h u v H1 H; unfold cons_update; eapply query_update_eval; [|exact H].
  unfold cons_update_q; apply cond_miss; [|apply K_q_eval].
  pose proof (is_list_q_eval u) as E; rewrite H1 in E; exact E.
Qed.

Fixpoint pc_t (p : query_pattern) (f s : Term) : Term :=
  match p with
  | PAny => ''Kq s
  | PLeaf => ''tq[s, ''Kq f, ''Kq (''Kq f)]
  | PStem p' => ''tq[f, pc_t p' f s, ''Kq (''Kq f)]
  | PFork a c => ''tq[f, ''Kq f, pc_t a (''Kq f) (pc_t c f s)]
  end.
Definition payload_t b (n : Term) : Term :=
  ''tq[Val b, Val ('Kq b), pc_t flag_pat (Val ('Kq b)) n].

Definition cons_case_term b (q h : Term) : Term :=
  cond_t is_list_q (path_query_t b path_to_cell
    (payload_t b (''tq[Val b, Val ('Kq b), ''Kq q]))) h.
Definition cons_update_term (k h : Term) : Term :=
  ''tagged[''S2[
    cond_t is_list_q (path_query_t identity_update path_to_cell
      (payload_t identity_update (''Kq (path_update_t path_cell_q k))))
      (''Kq h), Val 'I], Val update_nm].

(** * Ghost-guarded recursive updates

    [ghost_guarded_update N f] is [update[N,f]] with its recursion guarded
    by [ghost_update]: at a haunted program it recurses into the program
    and keeps the ghost; elsewhere it takes the ordinary step (act on a
    node named N, otherwise update the children). *)
Definition ghost_guarded_body N f := Eval cbn in to_tree
  (star "r" (cons_update_term (Ref "r") (ghost_update_term (Ref "r")
    (''tagged[''S2[''S2[''S2[Val (is_named N), ''K1 (Val f)],
      ''K1 (children2_term (Ref "r") (Ref "r") (Ref "r"))],Val 'I], Val update_nm])))).
Definition ghost_guarded_update N f := fix_update (ghost_guarded_body N f).

Lemma ghost_guarded_body_eval : forall N f r,
  ghost_guarded_body N f @ r ==> cons_update r (ghost_update r (step N f r)).
Proof.
  intros; unfold ghost_guarded_body, cons_update_term, cons_update, cons_update_q, ghost_update,
    ghost_update_term, ghost_query, query_update, cond, cond_t, path_query, payload_q, payload_t,
    pc, path_update, flag_pat, path_to_cell, path_cell_q,
    ghost_case, query_decorated_program, query_left, query_right, query_stem,
    diagonal_query, choose_queries, ghost_rebuild, children2, update_one_level2,
    update_fork2, step, specialised_update, if_named, children, update_one_level, update_fork;
    cbn; evaluate.
Qed.
Lemma ghost_guarded_unfold : forall N f u v,
  cons_update (ghost_guarded_update N f)
    (ghost_update (ghost_guarded_update N f) (step N f (ghost_guarded_update N f))) @ u ==> v ->
  ghost_guarded_update N f @ u ==> v.
Proof.
  intros N f u v H; unfold ghost_guarded_update at 1, fix_update; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|exact H].
  eapply eval_c; eapply eval_appr; [apply tagged_update_eval|].
  apply ghost_guarded_body_eval.
Qed.
Definition off_list u := pattern_matches list_pat u = false.
Lemma off_tagged : forall C N, N <> list_nm -> off_list ('tagged[C,N]).
Proof.
  intros C N H; unfold off_list, list_pat; cbn [pattern_matches].
  destruct N as [|n|[|a|a b] [|c|c d]]; cbn; try reflexivity;
    contradiction H; reflexivity.
Qed.
Lemma ghost_guarded_off : forall N f u v, off_list u ->
  ghost_update (ghost_guarded_update N f) (step N f (ghost_guarded_update N f)) @ u ==> v ->
  ghost_guarded_update N f @ u ==> v.
Proof. intros; apply ghost_guarded_unfold; apply cons_update_miss; assumption. Qed.
Lemma ghost_guarded_nil : forall N f a, ghost_guarded_update N f @ nil_value a ==> nil_value a.
Proof. intros; apply ghost_guarded_unfold; apply cons_update_nil. Qed.
Lemma ghost_guarded_cell : forall N f x s x' s',
  ghost_guarded_update N f @ (x '* s) ==> (x' '* s') ->
  ghost_guarded_update N f @ cell x s ==> cell x' s'.
Proof. intros; apply ghost_guarded_unfold; apply cons_update_cell; assumption. Qed.
Lemma ghost_guarded_decoration : forall N f g g' w,
  ghost_guarded_update N f @ g ==> g' ->
  ghost_guarded_update N f @ 'decorate[g,w] ==> 'decorate[g',w].
Proof.
  intros; apply ghost_guarded_off; [reflexivity|apply ghost_update_haunted; assumption].
Qed.
Lemma ghost_guarded_step : forall N f u v, off_list u ->
  (forall g w, u <> 'decorate[g,w]) -> step N f (ghost_guarded_update N f) @ u ==> v ->
  ghost_guarded_update N f @ u ==> v.
Proof. intros; apply ghost_guarded_off; [assumption|apply ghost_update_other; assumption]. Qed.
Lemma ghost_guarded_hit : forall N f p v, off_list ('tagged[p,N]) ->
  f @ 'tagged[p,N] ==> v -> ghost_guarded_update N f @ 'tagged[p,N] ==> v.
Proof.
  intros; apply ghost_guarded_step; [assumption|intros; discriminate|].
  unfold step, specialised_update; apply tagged_eval.
  eapply if_named_hit; [apply get_tagname_some|exact H0].
Qed.
Lemma ghost_guarded_leaf : forall N f, ghost_guarded_update N f @ Lf ==> Lf.
Proof.
  intros; apply ghost_guarded_step; [reflexivity|intros; discriminate|].
  unfold step, specialised_update; apply tagged_eval.
  apply if_named_default; [intros; discriminate|].
  unfold children; apply tagged_eval; apply update_one_level_leaf.
Qed.
Lemma ghost_guarded_stem : forall N f x y,
  ghost_guarded_update N f @ x ==> y -> ghost_guarded_update N f @ Sm x ==> Sm y.
Proof.
  intros; apply ghost_guarded_step; [reflexivity|intros; discriminate|].
  unfold step, specialised_update; apply tagged_eval.
  apply if_named_default; [intros; discriminate|].
  unfold children; apply tagged_eval; apply update_one_level_stem; assumption.
Qed.
Lemma ghost_guarded_miss : forall N f x y x' y', off_list (Fk x y) ->
  (forall g w, Fk x y <> 'decorate[g,w]) -> (forall p, Fk x y <> 'tagged[p,N]) ->
  ghost_guarded_update N f @ x ==> x' -> ghost_guarded_update N f @ y ==> y' ->
  ghost_guarded_update N f @ Fk x y ==> Fk x' y'.
Proof.
  intros; apply ghost_guarded_step; [assumption|assumption|].
  unfold step, specialised_update; apply tagged_eval.
  apply if_named_default; [assumption|].
  unfold children; apply tagged_eval; apply update_fork_eval; assumption.
Qed.

Section GhostGuardedTyping.
Variable AI : Decl.
Variable N T f : Combination.
Hypothesis HU : supports_updates AI.
Hypothesis HQ : supports_queries AI.
Hypothesis HB : supports_booleans AI.
Hypothesis HT : supports_is_named AI.
Hypothesis HN : concrete N.
Hypothesis HI : declared_wrapper AI N T.
Variable F : Combination.
Hypothesis HF : infer AI @ f ==> Sm F.
Hypothesis HFW : type_app AI @ F @r wrap_type T N ==> Sm (wrap_type T N).

Local Ltac guarded_app := first
  [ eassumption
  | apply app_Update | apply app_I | apply app_K | apply app_leaf
  | lazymatch goal with
    | |- type_app _ @ ('Query[?B]) @r _ ==> _ =>
        apply type_app_abstract; apply query_eliminator_eval
    | |- type_app _ @ ('Bool) @r _ ==> _ =>
        apply type_app_abstract; apply bool_eliminator_some
    end
  | new_S; [solve [intros; discriminate]| | |]
  | apply app_stem; first
    [ apply type_app_stem_structural; solve [intros; discriminate]
    | apply type_app_stem_tagged; eapply update_abstractor_supported; [exact HU|];
      first [apply constructor_children | apply constructor_query_update |
        eapply constructor_choice; [exact HN|exact HI|exact HFW] | apply constructor_identity]
    | apply type_app_stem_tagged; eapply query_abstractor_supported; [exact HQ|];
      first [apply query_abstractor_K | eapply query_abstractor_S |
        apply query_abstractor_triage | apply query_abstractor_diagonal]] ].

Local Definition ghost_guarded_body_type :
  { F : Combination | infer AI @ ghost_guarded_body N f ==> Sm F /\
    type_app AI @ F @r ('Update) ==> Sm ('Update) }.
Proof using All.
  assert (Hid : infer AI @ identity_update ==> Sm ('Update)) by (apply inf_identity; exact HU).
  assert (Htt : infer AI @ ('tt) ==> Sm ('Bool)) by (apply tt_infer; exact HB).
  assert (Hpred : infer AI @ is_decoration_query ==> Sm ('Query['Bool]))
    by (apply is_decoration_query_typed; assumption).
  pose proof (infer_typed_K_q_any AI) as Hconst.
  pose proof (type_app_typed_K_q AI ('Update) HQ) as HconstU.
  pose proof (type_app_choose AI ('Update) HB) as HchooseU.
  assert (HKid : infer AI @ ('Kq identity_update) ==> Sm ('Query['Update]))
    by (apply infer_Kq; assumption).
  pose proof (inf_is_named AI N HN HT) as HW.
  assert (Hdq : infer AI @ is_list_q ==> Sm ('Query['Bool])) by (apply is_list_q_typed; assumption).
  eexists; split; unfold ghost_guarded_body; cbn.
  all: repeat first [eassumption | eapply infer_Kq; [exact HQ|] | apply inf_leaf | apply inf_stem
    | apply inf_K1 | eapply inf_fork | guarded_app].
  Unshelve. all: repeat first [eassumption | eapply infer_Kq; [exact HQ|] | apply inf_leaf | apply inf_stem
    | apply inf_K1 | eapply inf_fork | guarded_app].
Defined.
Lemma ghost_guarded_update_typed :
  infer AI @ ghost_guarded_update N f ==> Sm ('Update).
Proof using All.
  unfold ghost_guarded_update; eapply inf_fix; [exact HU| |].
  - exact (proj1 (proj2_sig ghost_guarded_body_type)).
  - exact (proj2 (proj2_sig ghost_guarded_body_type)).
Qed.
End GhostGuardedTyping.

(** One-round soundness of the declarations. *)
Lemma plain_update_cond2 : forall AI, supports_updates AI ->
  sound_abstractor AI (update_abstractor_at AI).
Proof. exact update_abstractor_value_sound. Qed.

(** * No declarations that support queries, updates or the IsNamed family are sound by typing

    The one-level carriers are accepted by the Query and Update
    abstractors, and the carrier [name_test N] by the IsNamed family, but a
    triage type (in [name_test N], the tag name reader [get_tagname])
    refuses a tagged argument type. *)
Lemma app_triage_tagged_none : forall AI F0 F1 F2 E N V,
  app AI @ 'triage[F0,F1,F2] @r 'tagged[E,N] ==> Sm V -> False.
Proof.
  intros AI F0 F1 F2 E N V H.
  pose proof (app_plain_inv AI _ _ _ (abstract_case_triage_none F0 F1 F2) H) as HD.
  apply default_triage_inv in HD; apply triage_case_inv in HD.
  destruct (structural_triage_inv _ _ _ _ _ _ HD)
    as [[_ [[HU _]|[M [HU _]]]]|[X [Y [G [HU [HXY _]]]]]]; try discriminate.
  apply (HXY E N); rewrite <- HU; reflexivity.
Qed.

Lemma queries_not_sound_by_typing : forall AI, supports_queries AI -> ~ ontology_sound_by_typing AI.
Proof.
  intros AI HQ Hs.
  apply (app_triage_tagged_none AI Lf ('Query[Lf]) ('Query['Query[Lf]]) Lf Lf Lf).
  change ('triage[Lf, 'Query[Lf], 'Query['Query[Lf]]]) with (query_one_level Lf).
  eapply (ontology_sound_by_typing_plain AI Hs (query_one_level Lf) query_nm (query_eliminator Lf)).
  - apply query_abstractor_supported; [exact HQ|apply query_abstractor_triage].
  - apply query_eliminator_eval.
Qed.

Lemma updates_not_sound_by_typing : forall AI, supports_updates AI -> ~ ontology_sound_by_typing AI.
Proof.
  intros AI HU Hs.
  apply (app_triage_tagged_none AI Lf (Lf 'C ('Update)) (update_fork ('Update)) Lf Lf ('tagged[Lf,Lf])).
  change ('triage[Lf, Lf 'C ('Update), update_fork ('Update)]) with (update_one_level ('Update)).
  eapply (ontology_sound_by_typing_plain AI Hs (update_one_level ('Update)) update_nm update_eliminator).
  - eapply update_abstractor_supported;
 [exact HU|apply constructor_children].
  - apply update_eliminator_eval.
Qed.

Lemma is_named_not_sound_by_typing : forall AI, supports_is_named AI -> ~ ontology_sound_by_typing AI.
Proof.
  intros AI HT Hs.
  destruct (name_test_total Lf ('tagged[Lf,Lf])) as [B HB].
  assert (HA : app AI @ name_test Lf @r 'tagged[Lf,Lf] ==> Sm B).
  { eapply (ontology_sound_by_typing_plain AI Hs (name_test Lf) is_named_nm (tagged_by Lf)).
    - eapply declaration_apply; [exact HT|apply is_named_abstractor_some; exact lf_leaf].
    - apply tagged_by_eval; exact HB. }
  apply app_plain_inv in HA;
    [|apply abstract_case_plain; intros E N HE; unfold name_test, get_tagname in HE; discriminate].
  unfold name_test in HA.
  destruct (default_S_inv _ _ _ _ _ _ HA) as [VG [VF [_ [HF _]]]].
  assert (Hg : exists F0 F1 F2, get_tagname = 'triage[F0,F1,F2])
    by (unfold get_tagname; do 3 eexists; reflexivity).
  destruct Hg as [F0 [F1 [F2 Hg]]]; rewrite Hg in HF.
  exact (app_triage_tagged_none AI F0 F1 F2 Lf Lf VF HF).
Qed.
