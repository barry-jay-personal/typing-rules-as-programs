(** * Array traversals (support for the paper's "Reading an array" and "Matrices").

    The array support used by the matrices: the sequence
    specification of arrays, conversions to and from lists, builders,
    readers, map, reading with no index, and checks against a live declarations.

    This material was split from arrays.v only to keep each file under the
    3-minute compilation limit. *)


(** A sequence specification for consumer arrays.

    array_value d [x1;...;xn] is a reference value built with empty/prepend.
    supplies xs f v says that the elements of xs are supplied to the curried
    consumer f, in order, producing v. These Coq definitions specify runtime
    behaviour; they are not runtime getters or a replacement type checker.

    This interface lets later mapping and matrix proofs state preservation
    of elements and order, independently of a particular consumer. Append
    satisfies the same interface although its result is represented by
    composition rather than a canonical chain of prepend constructors. *)
From Stdlib Require Import List.
From TreeTyping Require Import tree typing soundness.
From TreeTyping Require Import arrays.

Set Default Proof Using "Type".

Fixpoint sequence_index (xs : List.list Combination) :=
  match xs with List.nil => Lf | _ :: tail => Sm (sequence_index tail) end.
Lemma sequence_index_unary : forall xs, unary_index (sequence_index xs).
Proof. induction xs; cbn; [apply unary_leaf|apply unary_stem; assumption]. Qed.
Lemma sequence_index_append : forall xs ys,
  sequence_index (xs ++ ys) = index_sum (sequence_index xs) (sequence_index ys).
Proof. induction xs; intros; cbn; congruence. Qed.

Fixpoint array_value (d : Combination) (xs : Datatypes.list Combination) :=
  match xs with
  | Datatypes.nil => arrays.empty d
  | Datatypes.cons x tail => arrays.prepend x (array_value d tail)
  end.

Inductive supplies : Datatypes.list Combination -> Combination -> Combination -> Prop :=
| supplies_nil : forall f, supplies Datatypes.nil f f
| supplies_cons : forall x xs f g v,
    f @ x ==> g -> supplies xs g v -> supplies (Datatypes.cons x xs) f v.

Lemma array_value_typed : forall AI d A xs,
  supports_arrays AI -> infer AI @ d ==> Sm A ->
  Forall (fun x => infer AI @ x ==> Sm A) xs ->
  infer AI @ array_value d xs ==> Sm (Array A (sequence_index xs)).
Proof.
  intros AI d A xs HS Hd Hxs; induction Hxs; cbn.
  - apply infer_empty; assumption.
  - apply infer_prepend; assumption.
Qed.

Lemma array_value_supplies : forall d xs f v,
  supplies xs f v -> array_value d xs @ f ==> v.
Proof.
  intros d xs f v H; induction H; cbn.
  - apply empty_eval.
  - eapply prepend_eval; eassumption.
Qed.

Lemma supplies_append : forall xs ys f v,
  supplies (xs ++ ys) f v <->
  exists g, supplies xs f g /\ supplies ys g v.
Proof.
  induction xs as [|x xs IH]; intros ys f v; cbn.
  - split.
    + intro H; exists f; split; [constructor|exact H].
    + intros [g [Hfg Hgv]]; inversion Hfg; subst; exact Hgv.
  - split.
    + intro H; inversion H; subst.
      match goal with Htail : supplies (xs ++ ys) ?g v |- _ =>
        apply IH in Htail; destruct Htail as [mid [Hxs Hys]];
        exists mid; split; [econstructor; eassumption|exact Hys] end.
    + intros [mid [Hxs Hys]]; inversion Hxs; subst.
      econstructor; [eassumption|apply IH; exists mid; auto].
Qed.

Lemma append_supplies : forall d e xs ys f v,
  supplies (xs ++ ys) f v ->
  arrays.append_value (array_value d xs) (array_value e ys) @ f ==> v.
Proof.
  intros d e xs ys f v H; apply supplies_append in H.
  destruct H as [g [HX HY]]; eapply append_value_eval;
    apply array_value_supplies; eassumption.
Qed.

Lemma append_program_supplies : forall d e xs ys f v,
  supplies (xs ++ ys) f v ->
  array_append @ (array_value d xs '* array_value e ys) @r f ==> v.
Proof.
  intros; eapply eval_appl; [apply array_append_eval|apply append_supplies; assumption].
Qed.

Lemma append_program_typed : forall (AI : Decl) d e A xs ys,
  supports_arrays AI -> infer AI @ d ==> Sm A -> infer AI @ e ==> Sm A ->
  Forall (fun x => infer AI @ x ==> Sm A) xs ->
  Forall (fun x => infer AI @ x ==> Sm A) ys ->
  infer_expression AI @ (array_append @ (array_value d xs '* array_value e ys))
    ==> Sm (Array A (sequence_index (xs ++ ys))).
Proof.
  intros; rewrite sequence_index_append; apply infer_array_append_application;
    auto using array_value_typed.
Qed.


(** What the successful list mapper does not yet give us.

    Nil and a singleton have the same List[A] type. Consequently a fixed
    program type F cannot, by application to List[A] alone, produce Array A Lf
    for one and Array A (Sm Lf) for the other: type application is deterministic.
    Operational length preservation does not restore information erased from
    the type. This rules out only an unannotated, length-recovering conversion
    through List[A], not array mapping itself. The Array A n input still has
    the index, and a successful array mapper must retain/use that information.

    The reference sequences below specify values; they do not implement
    runtime type analysis in Coq. *)
From Stdlib Require Import List.
From TreeTyping Require Import tree typing soundness.
From TreeTyping Require Import data_types.

Set Default Proof Using "Type".

Lemma list_type_forgets_length : forall (AI : Decl) a A,
  supports_list AI -> infer AI @ a ==> Sm A ->
  infer AI @ nil_value a ==> Sm ('List[A]) /\
  infer AI @ cons_value a (nil_value a) ==> Sm ('List[A]).
Proof.
  intros; split; [apply infer_nil_value|apply infer_cons_value];
    auto using infer_nil_value.
Qed.

Lemma no_length_recovery_from_List_alone : forall (AI : Decl) a A,
  infer AI @ a ==> Sm A ->
  ~ exists F, forall xs : Datatypes.list Combination,
    Forall (fun x => infer AI @ x ==> Sm A) xs ->
    type_app AI @ F @r ('List[A]) ==> Sm (Array A (sequence_index xs)).
Proof.
  intros AI a A Ha [F HF].
  pose proof (HF Datatypes.nil (Forall_nil _)) as Hzero.
  assert (Hone : type_app AI @ F @r ('List[A]) ==> Sm (Array A (Sm Lf))).
  { apply (HF (Datatypes.cons a Datatypes.nil)); constructor; auto. }
  pose proof (eval_deterministic _ _ Hzero _ Hone) as Hsame.
  discriminate Hsame.
Qed.


(** Runtime conversions between lists and consumer arrays.

    take_array b receives a tree length n, then a list. It pads short lists
    with b and truncates long lists. read_array a receives n, then an array,
    and returns its elements in order. Both generate their consumers by a
    recursive triage over the runtime index; no Rocq natural drives generation.

    Canonical indices are Lf and Sm n, which infer as themselves. The folds
    also execute on forks, ignoring the left branch, but their application
    typing theorems here use canonical indices. The main-line guarded
    structural triage rules type these folds; no additional rule is assumed.

    The tree-recursive definitions array_builder, array_collector and
    array_reader specify generated values. They support the operational
    proofs, while take_array and read_array are the actual calculus programs.
    The final theorems establish typing of their generating applications and
    exact preservation of the element sequence.

    The final section abstracts the element witness too: take_array_program
    and read_array_program receive a witness by calculus application. It
    may itself be computed, as demonstrated by generated_row_reader. The
    original specialised interfaces are retained, with exact correspondence
    lemmas. No additional abstract constructor or typing rule is needed. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types.

Open Scope string_scope.
Set Default Proof Using "Type".

(** The head of a list takes a default; the tail is [list_tail].  The tail
    of a one-element list is the empty list whose ghost is the element
    leaving. *)
Definition head2 (b : Term) : Term := swap_t (b ''* Val 'fst).

Lemma infer_head_or : forall AI b B, infer AI @ b ==> Sm B ->
  infer AI @ head_or b ==> Sm (head_or B).
Proof. intros; unfold head_or; apply infer_foldright_value; [apply infer_tag_free; reflexivity|assumption]. Qed.
Lemma type_app_head_or_list : forall AI B, type_app AI @ head_or B @r 'List[B] ==> Sm B.
Proof. intros; apply type_app_foldright_value; apply type_app_fst_product. Qed.

Definition take_step b r := Eval cbn -[list_tail] in to_tree
  (star "xs" (''tagged[
    (Val r @@ (Val list_tail @@ Ref "xs")) ''C
      ''S2[Val 'I,''K1 (head2 (Val b) @@ Ref "xs")], Val array_nm])).

Lemma take_step_eval : forall b r xs h t ys,
  head_or b @ xs ==> h -> list_tail @ xs ==> t -> r @ t ==> ys ->
  take_step b r @ xs ==> arrays.prepend h ys.
Proof.
  intros b r xs h t ys H1 H2 H3; unfold head_or, foldright_value, swap in H1.
  unfold take_step, arrays.prepend, swap; d_eval.
Qed.

Definition collect_argument a r acc := Eval cbn -[cons_step] in to_tree
  (star "x" (Val r @@ (Val data_types.append @@
    (Val acc ''* cons2 (Ref "x") (Val (nil_value a)))))).
Definition collect_consumer a r acc := lam (collect_argument a r acc) a.
Definition collect_body a r := Eval cbn -[cons_step] in to_tree
  (star "acc" (lam2
    (star "x" (Val r @@ (Val data_types.append @@
      (Ref "acc" ''* cons2 (Ref "x") (Val (nil_value a)))))) (Val a))).
Lemma collect_consumer_eval : forall a r acc x next c,
  data_types.append @ (acc '* cons_value x (nil_value a)) ==> next ->
  r @ next ==> c -> collect_consumer a r acc @ x ==> c.
Proof.
  intros a r acc x next c H1 H2.
  pose proof (cons_step_eval x (nil_value a)) as H3.
  unfold collect_consumer, collect_argument, cons2; apply lam_eval; cbn -[cons_step]; d_eval.
Qed.

Definition unary_fold_body z s := Eval cbn in to_tree
  (star "r" (''triage[Val z, Val s ''C Ref "r",
    ''K1 (Val s ''C Ref "r")])).
Definition unary_fold z s := Z (unary_fold_body z s).

Lemma unary_fold_leaf : forall z s, unary_fold z s @ Lf ==> z.
Proof. intros; unfold unary_fold; apply Z_unfold; unfold unary_fold_body; evaluate. Qed.
Lemma unary_fold_stem : forall z s n v w,
  unary_fold z s @ n ==> v -> s @ v ==> w ->
  unary_fold z s @ Sm n ==> w.
Proof.
  intros; unfold unary_fold in *; apply Z_unfold; unfold unary_fold_body; evaluate.
Qed.
Lemma unary_fold_fork : forall z s x n v w,
  unary_fold z s @ n ==> v -> s @ v ==> w ->
  unary_fold z s @ Fk x n ==> w.
Proof.
  intros; unfold unary_fold in *; apply Z_unfold; unfold unary_fold_body; evaluate.
Qed.


Definition take_array_step b := Eval cbn -[list_tail] in to_tree
  (star "r" (lam2
    (star "xs" (''tagged[
      (Ref "r" @@ (Val list_tail @@ Ref "xs")) ''C
        ''S2[Val 'I,''K1 (head2 (Val b) @@ Ref "xs")], Val array_nm]))
    (Val (nil_value b)))).
Definition take_array b := unary_fold
  (lam ('K1 (arrays.empty b)) (nil_value b)) (take_array_step b).
Fixpoint array_builder b n :=
  match n with
  | Lf => lam ('K1 (arrays.empty b)) (nil_value b)
  | Sm k | Fk _ k => lam (take_step b (array_builder b k)) (nil_value b)
  end.
Lemma take_array_step_eval : forall b r,
  take_array_step b @ r ==> lam (take_step b r) (nil_value b).
Proof. intros; unfold take_array_step, take_step, lam; evaluate. Qed.
Lemma take_array_eval : forall b n,
  take_array b @ n ==> array_builder b n.
Proof.
  intros b n; induction n; cbn [array_builder]; unfold take_array in *.
  - apply unary_fold_leaf.
  - eapply unary_fold_stem; [exact IHn|apply take_array_step_eval].
  - eapply unary_fold_fork; [exact IHn2|apply take_array_step_eval].
Qed.

Section BuilderTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Local Definition builder_step_type b r B n (Hb : infer AI @ b ==> Sm B)
  (Hr : infer AI @ r ==> Sm ('List[B] --> Array B n)) :
  { F : Combination | infer AI @ take_step b r ==> Sm F /\
    type_app AI @ F @r ('List[B]) ==> Sm (Array B (Sm n)) }.
Proof using AI HA HL.
  pose proof (infer_list_tail AI) as HT.
  pose proof (type_app_list_tail AI B HL) as HT1.
  pose proof (type_app_head_or_list AI B) as HH1.
  unfold head_or, foldright_value, swap in HH1.
  eexists; split; unfold take_step.
  - infer_tac.
  - repeat first [apply funty_eliminator_eval | progress type_app_tac].
    apply type_app_stem_ev; apply type_app_stem_tagged.
    eapply declaration_apply; [exact HA|apply array_abstractor_step].
Defined.
Lemma infer_array_builder : forall n b B, unary_index n ->
  infer AI @ b ==> Sm B ->
  infer AI @ array_builder b n ==> Sm ('List[B] --> Array B n).
Proof using AI HL HA.
  intros n b B Hn; revert b B; induction Hn as [|n Hn IHn] using unary_index_ind; intros b B Hb; cbn [array_builder].
  - eapply infer_lam; [ | |apply type_app_K_ev].
    + apply infer_K1; apply infer_empty; assumption.
    + apply infer_nil_value; assumption.
  - destruct (builder_step_type b (array_builder b n) B n Hb (IHn b B Hb))
      as [F [HI HT]].
    eapply infer_lam; [exact HI|apply infer_nil_value; assumption|exact HT].
Qed.
End BuilderTyping.

Lemma take_array_result_typed : forall (AI : Decl) b B n,
  supports_list AI -> supports_arrays AI ->
  infer AI @ b ==> Sm B -> unary_index n ->
  exists p, take_array b @ n ==> p /\
    infer AI @ p ==> Sm ('List[B] --> Array B n).
Proof.
  intros; exists (array_builder b n); split.
  - apply take_array_eval.
  - apply infer_array_builder; assumption.
Qed.

(** Padding and truncation are specified directly against the tree index.
    Padding repeats the default. *)
Fixpoint array_elements d n (xs : List.list Combination) :=
  match n with
  | Lf => List.nil
  | Sm k | Fk _ k =>
      match xs with
      | List.nil => d :: array_elements d k List.nil
      | x :: tail => x :: array_elements d k tail
      end
  end.

Lemma array_builder_zero : forall b xs,
  array_builder b Lf @ xs ==> arrays.empty b.
Proof. intros; cbn [array_builder]; unfold lam; evaluate. Qed.
Lemma array_builder_step : forall b n xs h t ys,
  head_or b @ xs ==> h -> list_tail @ xs ==> t ->
  array_builder b n @ t ==> ys ->
  array_builder b (Sm n) @ xs ==> arrays.prepend h ys.
Proof.
  intros; cbn [array_builder]; unfold lam; apply tagged_eval; apply wait_eval.
  evaluate; eapply take_step_eval; eassumption.
Qed.
Lemma array_builder_list : forall n b d xs,
  array_builder b n @ list_value d xs ==>
    array_value b (array_elements b n xs).
Proof.
  assert (Hc : forall n b d xs,
    (forall d l, array_builder b n @ list_value d l ==> array_value b (array_elements b n l)) ->
    array_builder b (Sm n) @ list_value d xs ==>
      array_value b (array_elements b (Sm n) xs)).
  { intros n b d xs IH; destruct xs as [|x l]; cbn [array_elements array_value].
    - eapply array_builder_step;
        [apply head_or_nil|apply list_tail_nil|exact (IH d List.nil)].
    - eapply array_builder_step;
        [apply head_or_list|apply list_tail_cons|apply IH]. }
  induction n; intros b d xs.
  - apply array_builder_zero.
  - apply Hc; intros; apply IHn.
  - exact (Hc n2 b d xs (fun d l => IHn2 b d l)).
Qed.
Lemma take_array_list : forall b n d xs,
  take_array b @ n @r list_value d xs ==>
    array_value b (array_elements b n xs).
Proof.
  intros; eapply eval_appl; [apply take_array_eval|apply array_builder_list].
Qed.

Section GeneratorStep.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.

Definition infer_generator_step b B (Hb : infer AI @ b ==> Sm B) :
  { S : Combination | infer AI @ take_array_step b ==> Sm S /\
    forall n, type_app AI @ S @r ('List[B] --> Array B n) ==>
      Sm ('List[B] --> Array B (Sm n)) }.
Proof using AI HL HA.
  pose proof (infer_list_tail AI) as HT.
  pose proof (type_app_head_or_list AI B) as HH1.
  unfold head_or, foldright_value, swap in HH1.
  pose proof (type_app_list_tail AI B HL) as HT1.
  pose proof (infer_nil_value AI b B HL Hb) as Hnil.
  eexists; split.
  - unfold take_array_step; infer_tac.
  - intro n.
    repeat first [apply funty_eliminator_eval | progress type_app_tac].
    apply type_app_stem_ev; apply type_app_stem_function.
    repeat first [apply funty_eliminator_eval | progress type_app_tac].
    apply type_app_stem_ev; apply type_app_stem_tagged.
    eapply declaration_apply; [exact HA|apply array_abstractor_step].
Defined.

Definition take_array_type b B (Hb : infer AI @ b ==> Sm B) :=
  Z (unary_fold_body ('List[B] --> Array B Lf)
    (proj1_sig (infer_generator_step b B Hb))).

Lemma infer_take_array : forall b B (Hb : infer AI @ b ==> Sm B),
  infer AI @ take_array b ==> Sm (take_array_type b B Hb).
Proof using AI HL HA.
  intros b B Hb.
  destruct (infer_generator_step b B Hb) as [S [HS Happ]] eqn:HE.
  unfold take_array_type; rewrite HE; cbn [proj1_sig].
  assert (Hbase : infer AI @ lam ('K1 (arrays.empty b)) (nil_value b) ==>
    Sm ('List[B] --> Array B Lf)).
  { apply (infer_array_builder AI HL HA Lf b B unary_leaf Hb). }
  unfold take_array, unary_fold; apply infer_Z.
  unfold unary_fold_body; infer_tac.
Qed.
End GeneratorStep.

Lemma generator_body_application : forall AI B S Q,
  type_app AI @ unary_fold_body ('List[B] --> Array B Lf) S @r (Z Q) ==>
    Sm ('triage['List[B] --> Array B Lf, S 'C (Z Q),'K1 (S 'C (Z Q))]).
Proof.
  intros; unfold unary_fold_body; type_app_tac.
Qed.

(** Unary indices use the structural leaf/stem rules directly. *)
Section GeneratorApplication.
Variable AI : Decl.
Lemma generator_application : forall B S,
  (forall n,
    type_app AI @ S @r ('List[B] --> Array B n) ==>
      Sm ('List[B] --> Array B (Sm n))) ->
  forall n, unary_index n ->
  type_app AI @ Z (unary_fold_body ('List[B] --> Array B Lf) S) @r n ==>
    Sm ('List[B] --> Array B n).
Proof using AI.
  intros B S HS n Hn; induction Hn as [|? ? IHHn] using unary_index_ind.
  - eapply type_app_Z.
    + apply generator_body_application.
    + apply type_app_structural_triage_leaf.
      * intros; discriminate.
  - eapply type_app_Z.
    + apply generator_body_application.
    + eapply type_app_structural_triage_stem.
      * intros; discriminate.
      * eapply type_app_compose; [solve [reject_name]| | |].
        -- intros; discriminate.
        -- exact IHHn.
        -- apply HS.
Qed.

Lemma take_array_application : forall b B,
  supports_list AI -> supports_arrays AI ->
  infer AI @ b ==> Sm B ->
  exists G, infer AI @ take_array b ==> Sm G /\
    forall n, unary_index n ->
      type_app AI @ G @r n ==> Sm ('List[B] --> Array B n).
Proof using AI.
  intros b B HL HA Hb.
  exists (take_array_type AI HL HA b B Hb); split.
  - apply infer_take_array.
  - unfold take_array_type.
    destruct (infer_generator_step AI HL HA b B Hb) as [S [HI HS]].
    cbn [proj1_sig]. apply generator_application; exact HS.
Qed.
Lemma take_array_type_application : forall b B
   (HL : supports_list AI) (HA : supports_arrays AI)
  (Hb : infer AI @ b ==> Sm B) n,
  unary_index n ->
  type_app AI @ take_array_type AI HL HA b B Hb @r n ==>
    Sm ('List[B] --> Array B n).
Proof using AI.
  intros b B HL HA Hb n Hn.
  unfold take_array_type.
  destruct (infer_generator_step AI HL HA b B Hb) as [S [HS HT]]; cbn [proj1_sig].
  apply generator_application; assumption.
Qed.

Lemma infer_take_array_application : forall b B n,
  supports_list AI -> supports_arrays AI ->
  infer AI @ b ==> Sm B -> unary_index n ->
  infer_expression AI @ (take_array b @ n) ==>
    Sm ('List[B] --> Array B n).
Proof using AI.
  intros b B n HL HA Hb Hn.
  destruct (take_array_application b B HL HA Hb) as [G [HG Happ]].
  eapply infer_expression_fork.
  - apply infer_expression_stem; exact HG.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply Happ; exact Hn.
Qed.

Lemma infer_take_array_list_application : forall b B n xs,
  supports_list AI -> supports_arrays AI ->
  infer AI @ b ==> Sm B -> unary_index n ->
  infer AI @ xs ==> Sm ('List[B]) ->
  infer_expression AI @ (take_array b @ n @r xs) ==> Sm (Array B n).
Proof using AI.
  intros b B n xs HL HA Hb Hn Hxs.
  eapply infer_expression_fork.
  - eapply infer_take_array_application; eassumption.
  - apply infer_expression_stem; exact Hxs.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End GeneratorApplication.

Definition collect_array_step a := Eval cbn in to_tree
  (star "r" (lam2
    (star "acc" (lam2
      (star "x" (Ref "r" @@ (Val data_types.append @@
        (Ref "acc" ''* cons2 (Ref "x") (Val (nil_value a)))))) (Val a)))
    (Val (nil_value a)))).
Definition collect_array a := unary_fold (lam 'I (nil_value a)) (collect_array_step a).
Fixpoint array_collector a n :=
  match n with
  | Lf => lam 'I (nil_value a)
  | Sm k | Fk _ k => lam (collect_body a (array_collector a k)) (nil_value a)
  end.
Lemma collect_array_step_eval : forall a r,
  collect_array_step a @ r ==> lam (collect_body a r) (nil_value a).
Proof. intros; unfold collect_array_step, collect_body, lam; evaluate. Qed.
Lemma collect_array_eval : forall a n, collect_array a @ n ==> array_collector a n.
Proof.
  intros a n; induction n; cbn [array_collector]; unfold collect_array in *.
  - apply unary_fold_leaf.
  - eapply unary_fold_stem; [exact IHn|apply collect_array_step_eval].
  - eapply unary_fold_fork; [exact IHn2|apply collect_array_step_eval].
Qed.

(** Arrow-valued folds use the same structural rules as the array builder.
    P is a reference family of output types, not a runtime type inspector. *)
Lemma arrow_fold_body_application : forall AI D C S Q,
  type_app AI @ unary_fold_body (D --> C) S @r Z Q ==>
    Sm ('triage[D --> C,S 'C (Z Q),'K1 (S 'C (Z Q))]).
Proof. intros; unfold unary_fold_body; type_app_tac. Qed.
Lemma arrow_fold_application : forall AI D C (P : Combination -> Combination) S,
  P Lf = (D --> C) ->
  (forall n, type_app AI @ S @r P n ==> Sm (P (Sm n))) ->
  forall n, unary_index n ->
  type_app AI @ Z (unary_fold_body (D --> C) S) @r n ==> Sm (P n).
Proof.
  intros AI D C P S Hzero HS n Hn; induction Hn as [|? ? IHHn] using unary_index_ind.
  - rewrite Hzero; eapply type_app_Z.
    + apply arrow_fold_body_application.
    + apply type_app_structural_triage_leaf;
        [intros; discriminate].
  - eapply type_app_Z.
    + apply arrow_fold_body_application.
    + eapply type_app_structural_triage_stem;
        [intros; discriminate|].
      eapply type_app_compose; [solve [reject_name]| | |]; [intros; discriminate|exact IHHn|apply HS].
Qed.

Section CollectorTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.

Local Ltac collect_app := first
  [ eassumption | ty_elim
  | progress type_app_tac
  | apply type_app_stem_ev
  | apply type_app_stem_function
  | apply type_app_stem_tagged; apply list_abstractor_supported; [exact HL|apply list_abstractor_cons; first [assumption|reflexivity]]
  | apply type_app_stem_structural; intros; discriminate ].

Definition infer_collect_array_step a A (Ha : infer AI @ a ==> Sm A) :
  { S : Combination | infer AI @ collect_array_step a ==> Sm S /\
    forall U, type_app AI @ S @r ('List[A] --> U) ==>
      Sm ('List[A] --> (A --> U)) }.
Proof using AI HL.
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  pose proof (infer_append AI) as Happ.
  pose proof (type_app_append AI A HL) as Happ1.
  eexists; split; [|intro U]; unfold collect_array_step, lam2, cons2; cbn.
  all: repeat first [progress infer_tac | collect_app].
Defined.

Definition collect_array_type a A (Ha : infer AI @ a ==> Sm A) :=
  Z (unary_fold_body ('List[A] --> 'List[A])
    (proj1_sig (infer_collect_array_step a A Ha))).
Lemma infer_collect_array : forall a A (Ha : infer AI @ a ==> Sm A),
  infer AI @ collect_array a ==> Sm (collect_array_type a A Ha).
Proof using AI HL.
  intros a A Ha; unfold collect_array_type.
  destruct (infer_collect_array_step a A Ha) as [S [HS HT]]; cbn [proj1_sig].
  assert (Hseed : infer AI @ lam 'I (nil_value a) ==> Sm ('List[A] --> 'List[A])).
  { eapply infer_lam; [apply infer_I|apply infer_nil_value; assumption|apply type_app_I]. }
  unfold collect_array, unary_fold; apply infer_Z; unfold unary_fold_body; infer_tac.
Qed.
Lemma collect_array_application : forall a A (Ha : infer AI @ a ==> Sm A) n,
  unary_index n ->
  type_app AI @ collect_array_type a A Ha @r n ==>
    Sm ('List[A] --> consumer_type A n ('List[A])).
Proof using AI HL.
  intros a A Ha n Hn; unfold collect_array_type.
  destruct (infer_collect_array_step a A Ha) as [S [HS HT]]; cbn [proj1_sig].
  eapply arrow_fold_application with
    (P := fun n => 'List[A] --> consumer_type A n ('List[A]));
    [reflexivity|intro k; apply HT|exact Hn].
Qed.
Lemma infer_collect_array_application : forall a A n,
  infer AI @ a ==> Sm A -> unary_index n ->
  infer_expression AI @ (collect_array a @ n) ==>
    Sm ('List[A] --> consumer_type A n ('List[A])).
Proof using AI HL.
  intros a A n Ha Hn; eapply infer_expression_fork.
  - apply infer_expression_stem; apply (infer_collect_array a A Ha).
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply collect_array_application; assumption.
Qed.
End CollectorTyping.

(** The reader uses a consumer and an array witness. Both are generated
    from the same runtime index, keeping their types in agreement. *)
Definition reader_from_consumer := Eval cbn in to_tree
  (star "c" (star "w" (lam2 (''S2[Val 'I,''K1 (Ref "c")]) (Ref "w")))).
Lemma reader_from_consumer_eval : forall c w,
  reader_from_consumer @ c @r w ==> lam (swap c) w.
Proof. intros; unfold reader_from_consumer, lam, swap; evaluate. Qed.
Lemma infer_reader_from_consumer : forall AI,
  infer AI @ reader_from_consumer ==> Sm reader_from_consumer.
Proof. intros; apply infer_tag_free; unfold reader_from_consumer; tag_free_tac. Qed.
Lemma type_app_reader_from_consumer : forall (AI : Decl) C W V,
  type_app AI @ W @r C ==> Sm V ->
  exists F, type_app AI @ reader_from_consumer @r C ==> Sm F /\
    type_app AI @ F @r W ==> Sm (W --> V).
Proof.
  intros AI C W V Happ; eexists; split.
  - unfold reader_from_consumer; type_app_tac.
  - type_app_tac.
    type_app_tac.
    apply type_app_stem_ev; apply type_app_stem_function.
    type_app_tac.
Qed.

Definition read_array a := Eval cbn in to_tree
  (star "n" (Val reader_from_consumer @@
    (Val (collect_array a) @@ Ref "n" @@ Val (nil_value a)) @@
    (Val (take_array a) @@ Ref "n" @@ Val (nil_value a)))).
Definition reader_consumer a n :=
  match n with
  | Lf => nil_value a
  | Sm k | Fk _ k => collect_consumer a (array_collector a k) (nil_value a)
  end.
Definition array_reader a n :=
  lam (swap (reader_consumer a n))
    (array_value a (array_elements a n List.nil)).
Lemma array_collector_zero : forall a acc, array_collector a Lf @ acc ==> acc.
Proof. intros; cbn [array_collector]; unfold lam; evaluate. Qed.
Lemma array_collector_successor : forall a n acc,
  array_collector a (Sm n) @ acc ==> collect_consumer a (array_collector a n) acc.
Proof.
  intros; cbn [array_collector]; unfold lam at 1; apply tagged_eval; apply wait_eval.
  unfold collect_body, collect_consumer, collect_argument, lam2, lam; cbn; evaluate.
Qed.
Lemma reader_consumer_eval : forall a n,
  array_collector a n @ nil_value a ==> reader_consumer a n.
Proof.
  intros a [|n|x n]; cbn [reader_consumer];
    [apply array_collector_zero|apply array_collector_successor|apply array_collector_successor].
Qed.
Lemma read_array_eval : forall a n, read_array a @ n ==> array_reader a n.
Proof.
  intros a n.
  pose proof (collect_array_eval a n) as HC.
  pose proof (reader_consumer_eval a n) as HR.
  pose proof (take_array_eval a n) as HB.
  pose proof (array_builder_list n a a List.nil) as HW.
  pose proof (reader_from_consumer_eval (reader_consumer a n)
    (array_value a (array_elements a n List.nil))) as HM.
  inv_out HM; unfold read_array, array_reader; cbn [list_value] in HW; evaluate.
Qed.

Section ReaderTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Definition infer_read_array a A (Ha : infer AI @ a ==> Sm A) :
  { R : Combination | infer AI @ read_array a ==> Sm R /\
    forall n, unary_index n -> type_app AI @ R @r n ==>
      Sm (Array A n --> 'List[A]) }.
Proof using AI HL HA.
  pose proof (infer_collect_array AI HL a A Ha) as HC.
  pose proof (infer_take_array AI HL HA a A Ha) as HB.
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  pose proof (infer_reader_from_consumer AI) as HM.
  eexists; split.
  - unfold read_array; infer_tac.
  - intros n Hn.
    pose proof (collect_array_application AI HL a A Ha n Hn) as HCA.
    assert (HBA : type_app AI @ take_array_type AI HL HA a A Ha @r n ==>
      Sm ('List[A] --> Array A n)).
    { unfold take_array_type.
      destruct (infer_generator_step AI HL HA a A Ha) as [S [HS HT]]; cbn [proj1_sig].
      apply generator_application; assumption. }
    destruct (type_app_reader_from_consumer AI
      (consumer_type A n ('List[A])) (Array A n) ('List[A]) (type_app_Array AI A n ('List[A]))) as [F [HMF HMW]].
    repeat first [eassumption|apply funty_eliminator_eval|progress type_app_tac].
Defined.
Lemma infer_read_array_application : forall a A n,
  infer AI @ a ==> Sm A -> unary_index n ->
  infer_expression AI @ (read_array a @ n) ==> Sm (Array A n --> 'List[A]).
Proof using AI HL HA.
  intros a A n Ha Hn; destruct (infer_read_array a A Ha) as [R [HR HT]].
  eapply infer_expression_fork.
  - apply infer_expression_stem; exact HR.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HT; exact Hn.
Qed.
Lemma infer_read_array_array : forall a A n xs,
  infer AI @ a ==> Sm A -> unary_index n ->
  infer AI @ xs ==> Sm (Array A n) ->
  infer_expression AI @ (read_array a @ n @r xs) ==> Sm ('List[A]).
Proof using AI HL HA.
  intros a A n xs Ha Hn HX; eapply infer_expression_fork.
  - eapply infer_read_array_application; eassumption.
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End ReaderTyping.

(** The generated reader returns the complete sequence, in order. This also
    covers arrays represented by append composition rather than prepend. *)
Lemma array_collector_sequence : forall a xs acc,
  exists c, array_collector a (sequence_index xs) @ list_value a acc ==> c /\
    supplies xs c (list_value a (acc ++ xs)).
Proof.
  intros a xs; induction xs as [|x xs IH]; intro acc; cbn [sequence_index].
  - exists (list_value a acc); rewrite List.app_nil_r; split;
      [apply array_collector_zero|constructor].
  - destruct (IH (acc ++ Datatypes.cons x Datatypes.nil)%list) as [c [HC HS]].
    exists (collect_consumer a (array_collector a (sequence_index xs)) (list_value a acc)).
    split; [apply array_collector_successor|].
    eapply supplies_cons with (g:=c).
    + eapply collect_consumer_eval;
        [exact (append_list acc a a (Datatypes.cons x Datatypes.nil))|exact HC].
    + rewrite <- List.app_assoc in HS; cbn [List.app] in HS; exact HS.
Qed.
Lemma reader_consumer_sequence : forall a xs,
  supplies xs (reader_consumer a (sequence_index xs)) (list_value a xs).
Proof.
  intros a [|x xs]; [constructor|].
  destruct (array_collector_sequence a (x :: xs) List.nil) as [c [HC HS]].
  pose proof (eval_deterministic _ _ HC _
    (array_collector_successor a (sequence_index xs) (nil_value a))) as HE.
  subst c; exact HS.
Qed.
Lemma array_reader_eval : forall a n xs ls,
  xs @ reader_consumer a n ==> ls -> array_reader a n @ xs ==> ls.
Proof. intros; unfold array_reader, lam, swap; evaluate. Qed.

(** Runtime witness arguments. *)
Definition empty2 b := ''tagged[(''wait[Val ('KI),b]),Val array_nm].
Definition unary_fold2 z s := Z2
  (star "r" (''triage[z,s ''C Ref "r",''K1 (s ''C Ref "r")])).
Definition take_array2 b := unary_fold2
  (lam2 (''K1 (empty2 b)) (nil2 b))
  (star "r" (lam2
    (star "xs" (''tagged[
      (Ref "r" @@ (Val list_tail @@ Ref "xs")) ''C
        ''S2[Val 'I,''K1 (head2 b @@ Ref "xs")], Val array_nm]))
    (nil2 b))).
(** Keep the fixed-point combinator and tags named for downstream proofs. *)
Definition take_array_program := Eval lazy -[bz array_nm fun_nm list_nm] in to_tree
  (star "b" (take_array2 (Ref "b"))).

Lemma take_array_specialises : forall b,
  take_array_program @ b ==> take_array b.
Proof.
  intros; unfold take_array_program, take_array2, unary_fold2, swap_t,
    empty2, lam2, nil2, take_array, unary_fold, unary_fold_body,
    take_array_step, nil_value, arrays.empty, lam, swap, Z2, Z; cbn; evaluate.
Qed.
Lemma take_array_program_eval : forall b n,
  take_array_program @ b @r n ==> array_builder b n.
Proof. intros; eapply eval_appl; [apply take_array_specialises|apply take_array_eval]. Qed.

(** Bind the already polymorphic list append program once, when the
    witness is supplied; the resulting collector is the existing one. *)
Local Opaque data_types.append take_array_program.
Definition collect_array2 a app := unary_fold2
  (lam2 (Val 'I) (nil2 a))
  (star "r" (lam2
    (star "acc" (lam2
      (star "x" (Ref "r" @@ (app @@
        (Ref "acc" ''* cons2 (Ref "x") (nil2 a))))) a)) (nil2 a))).
Definition collect_array_program := Eval lazy -[bz array_nm fun_nm list_nm] in to_tree
  (star "a" (collect_array2 (Ref "a") (Val data_types.append))).
Lemma collect_array_specialises : forall a,
  collect_array_program @ a ==> collect_array a.
Proof.
  intro a.
  unfold collect_array_program, collect_array2, unary_fold2, collect_array,
    collect_array_step, unary_fold, unary_fold_body, lam2, nil2, cons2, swap_t,
    nil_value, lam, swap, Z2, Z; cbn; evaluate.
Qed.

Local Opaque collect_array_program.
Definition read_array_program := Eval cbn in to_tree
  (star "a" ((star "collect" (star "take" (star "n"
    (Val reader_from_consumer @@
      (Ref "collect" @@ Ref "n" @@ nil2 (Ref "a")) @@
      (Ref "take" @@ Ref "n" @@ nil2 (Ref "a")))))) @@
    (Val collect_array_program @@ Ref "a") @@
    (Val take_array_program @@ Ref "a"))).
Lemma read_array_specialises : forall a,
  read_array_program @ a ==> read_array a.
Proof.
  intro a; pose proof (take_array_specialises a); pose proof (collect_array_specialises a).
  unfold read_array_program, read_array, nil2, nil_value; cbn; evaluate.
Qed.
Lemma read_array_program_eval : forall a n,
  read_array_program @ a @r n ==> array_reader a n.
Proof. intros; eapply eval_appl; [apply read_array_specialises|apply read_array_eval]. Qed.

Section WitnessTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Local Ltac witness_app := first
  [apply funty_eliminator_eval | ty_elim | eassumption
  | lazymatch goal with
    | |- type_app _ @ ?T @r _ ==> _ =>
      first [is_evar T; fail 1|idtac];
      first [eapply type_app_I
        | new_S; [solve [intros; discriminate]| | |]
        | eapply type_app_K_ev | eapply type_app_leaf_ev
        | eapply type_app_abstract | eapply type_app_stem_ev]
    | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
      first [apply type_app_stem_function
        | apply type_app_stem_tagged; eapply declaration_apply; [exact HA|apply array_abstractor_step]
        | apply type_app_stem_tagged; eapply declaration_apply; [exact HA|apply array_abstractor_zero]
        | apply type_app_stem_tagged; apply list_abstractor_supported; [exact HL|first [apply list_abstractor_nil|apply list_abstractor_cons; first [assumption|reflexivity]]]
        | apply type_app_stem_structural; intros; discriminate
        | apply type_app_stem_structural; solve [intros; discriminate]]
    end].

Definition infer_take_array_program :
  { T : Combination | infer AI @ take_array_program ==> Sm T /\
    forall B, exists S,
      type_app AI @ T @r B ==> Sm (Z (unary_fold_body ('List[B] --> Array B Lf) S)) /\
      forall n, unary_index n ->
        type_app AI @ Z (unary_fold_body ('List[B] --> Array B Lf) S) @r n ==>
        Sm ('List[B] --> Array B n) }.
Proof using AI HL HA.
  Local Transparent take_array_program.
  eexists; split.
  - unfold take_array_program, take_array2, unary_fold2, swap_t, empty2, lam2, nil2, Z2, Z; cbn.
    repeat first [progress infer_tac|witness_app].
  - intro B.
    eexists; split.
    + repeat witness_app.
    + intros n Hn.
      eapply generator_application; [ |exact Hn].
      intro k; repeat witness_app.
Local Opaque take_array_program.
Defined.

Definition infer_collect_array_program :
  { T : Combination | infer AI @ collect_array_program ==> Sm T /\
    forall A, exists S,
      type_app AI @ T @r A ==> Sm (Z (unary_fold_body ('List[A] --> 'List[A]) S)) /\
      forall n, unary_index n ->
        type_app AI @ Z (unary_fold_body ('List[A] --> 'List[A]) S) @r n ==>
        Sm ('List[A] --> consumer_type A n ('List[A])) }.
Proof using AI HL.
  Local Transparent collect_array_program.
  pose proof (infer_append AI) as Happ.
  eexists; split.
  - unfold collect_array_program, collect_array2, unary_fold2,
      lam2, nil2, cons2, swap_t, Z2, Z; cbn.
    repeat first [progress infer_tac|witness_app].
  - intro A; pose proof (type_app_append AI A HL).
    eexists; split.
    + repeat witness_app.
    + intros n Hn.
      eapply arrow_fold_application with
        (P := fun n => 'List[A] --> consumer_type A n ('List[A]));
        [reflexivity| |exact Hn].
      intro k; cbn [consumer_type]; repeat witness_app.
Local Opaque collect_array_program.
Defined.

Local Opaque take_array_program collect_array_program.
Definition infer_read_array_program :
  { T : Combination | infer AI @ read_array_program ==> Sm T /\
    forall A, exists G, type_app AI @ T @r A ==> Sm G /\
      forall n, unary_index n -> type_app AI @ G @r n ==>
        Sm (Array A n --> 'List[A]) }.
Proof using AI HL HA.
  pose proof (proj2_sig infer_take_array_program) as [HT HTA].
  pose proof (proj2_sig infer_collect_array_program) as [HC HCA].
  pose proof (infer_reader_from_consumer AI) as HR.
  eexists; split.
  - unfold read_array_program, nil2; cbn.
    repeat first [progress infer_tac|witness_app].
  - intro A.
    destruct (HTA A) as [T [HAT HTn]].
    destruct (HCA A) as [C [HAC HCn]].
    eexists; split.
    + repeat witness_app.
    + intros n Hn.
      pose proof (HTn n Hn); pose proof (HCn n Hn).
      destruct (type_app_reader_from_consumer AI
        (consumer_type A n ('List[A])) (Array A n) ('List[A]) (type_app_Array AI A n ('List[A]))) as [F [HRF HFW]].
      repeat witness_app.
Defined.

(** These theorems type the witness-producing expression itself. *)
Lemma infer_take_array_witness : forall e A n,
  infer_expression AI @ e ==> Sm A -> unary_index n ->
  infer_expression AI @ Fk (Fk (Sm take_array_program) e) (Sm n) ==>
    Sm ('List[A] --> Array A n).
Proof using AI HL HA.
  intros e A n He Hn.
  destruct infer_take_array_program as [T [HT HTA]].
  destruct (HTA A) as [G [HG HGn]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork.
    + apply infer_expression_stem; exact HT.
    + exact He.
    + exact HG.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HGn; exact Hn.
Qed.
Lemma infer_read_array_witness : forall e A n,
  infer_expression AI @ e ==> Sm A -> unary_index n ->
  infer_expression AI @ Fk (Fk (Sm read_array_program) e) (Sm n) ==>
    Sm (Array A n --> 'List[A]).
Proof using AI HL HA.
  intros e A n He Hn.
  destruct infer_read_array_program as [T [HT HTA]].
  destruct (HTA A) as [G [HG HGn]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork.
    + apply infer_expression_stem; exact HT.
    + exact He.
    + exact HG.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HGn; exact Hn.
Qed.

Lemma infer_take_array_program_application : forall a A n xs,
  infer AI @ a ==> Sm A -> unary_index n -> infer AI @ xs ==> Sm ('List[A]) ->
  infer_expression AI @ (take_array_program @ a @r n @r xs) ==> Sm (Array A n).
Proof using AI HL HA.
  intros a A n xs Ha Hn HX; eapply infer_expression_fork.
  - apply infer_take_array_witness; [apply infer_expression_stem; exact Ha|exact Hn].
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
Lemma infer_read_array_program_application : forall a A n xs,
  infer AI @ a ==> Sm A -> unary_index n -> infer AI @ xs ==> Sm (Array A n) ->
  infer_expression AI @ (read_array_program @ a @r n @r xs) ==> Sm ('List[A]).
Proof using AI HL HA.
  intros a A n xs Ha Hn HX; eapply infer_expression_fork.
  - apply infer_read_array_witness; [apply infer_expression_stem; exact Ha|exact Hn].
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** Construct a row witness, then supply it as the element witness for an
    outer-array reader. Both dimensions are supplied as tree values. *)
Definition generated_row_reader a m n :=
  Fk (Fk (Sm read_array_program)
    (take_array_program @ a @r n @r nil_value a)) (Sm m).
Lemma infer_generated_row_reader : forall a A m n,
  infer AI @ a ==> Sm A -> unary_index m -> unary_index n ->
  infer_expression AI @ generated_row_reader a m n ==>
    Sm (Array (Array A n) m --> 'List[Array A n]).
Proof using AI HL HA.
  intros a A m n Ha Hm Hn; unfold generated_row_reader.
  apply infer_read_array_witness; [|exact Hm].
  apply infer_take_array_program_application; [exact Ha|exact Hn|].
  apply infer_nil_value; assumption.
Qed.
End WitnessTyping.

Lemma take_array_program_list : forall b n d xs,
  take_array_program @ b @r n @r list_value d xs ==>
    array_value b (array_elements b n xs).
Proof. intros; eapply eval_appl; [apply take_array_program_eval|apply array_builder_list]. Qed.
Lemma generated_row_reader_eval : forall a m n,
  generated_row_reader a m n ==>
    array_reader (array_value a (array_elements a n List.nil)) m.
Proof.
  intros; unfold generated_row_reader; eapply eval_pair.
  - eapply eval_pair.
    + evaluate.
    + apply (take_array_program_list a n a List.nil).
    + apply read_array_specialises.
  - evaluate.
  - apply read_array_eval.
Qed.


(** Array mapping with a runtime tree index.
    map_array a b f n generates a function which reads its array, maps f
    over the resulting list and rebuilds an array with the same tree index.
    Its witness, reader and builder are all generated inside the calculus.
    No Rocq natural-number parameter chooses code for this program. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types.

Open Scope string_scope.
Set Default Proof Using "Type".

(** The uniform composition can also be supplied with existing readers and
    builders. This interface is independent of how those values are obtained. *)
Definition map_via_lists := Eval cbn in to_tree
  (star "read" (star "build" (star "mapper" (star "xs"
    (Ref "build" @@ (Ref "mapper" @@ (Ref "read" @@ Ref "xs"))))))).

Lemma infer_map_via_lists : forall AI,
  infer AI @ map_via_lists ==> Sm map_via_lists.
Proof. intros; apply infer_tag_free; vm_compute; reflexivity. Qed.

Lemma type_app_map_via_lists : forall AI A B n M,
  type_app AI @ M @r 'List[A] ==> Sm ('List[B]) ->
  exists T1 T2 T3,
    type_app AI @ map_via_lists @r (Array A n --> 'List[A]) ==> Sm T1 /\
    type_app AI @ T1 @r ('List[B] --> Array B n) ==> Sm T2 /\
    type_app AI @ T2 @r M ==> Sm T3 /\
    type_app AI @ T3 @r Array A n ==> Sm (Array B n).
Proof.
  intros; do 3 eexists; repeat split; unfold map_via_lists;
    repeat first [eassumption | apply funty_eliminator_eval | progress type_app_tac].
Qed.

(** The mapper argument is an expression computing the list function, not
    a Coq substitution of its output. Thus the theorem checks all runtime
    applications, including the polymorphic list-map specialisation. *)
Definition map_array_expression read build f b xs :=
  Fk (Fk (map_via_lists @ read @r build) (map_with @ f @r b)) (Sm xs).

Lemma infer_map_array_expression : forall (AI : Decl) read build f b xs A B F n,
  supports_list AI ->
  infer AI @ read ==> Sm (Array A n --> 'List[A]) ->
  infer AI @ build ==> Sm ('List[B] --> Array B n) ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r A ==> Sm B -> infer AI @ b ==> Sm B ->
  infer AI @ xs ==> Sm (Array A n) ->
  infer_expression AI @ map_array_expression read build f b xs ==> Sm (Array B n).
Proof.
  intros AI read build f b xs A B F n HL Hr Hw Hf HFA Hb Hxs.
  destruct (type_app_map_via_lists AI A B n _ (type_app_map_value AI HL F A B HFA))
    as [T1 [T2 [T3 [HT1 [HT2 [HT3 HT4]]]]]].
  unfold map_array_expression.
  eapply infer_expression_fork; [|apply infer_expression_stem; exact Hxs|exact HT4].
  eapply infer_expression_fork; [|apply infer_map_with_specialisation; eassumption|exact HT3].
  eapply infer_expression_fork; [|apply infer_expression_stem; exact Hw|exact HT2].
  eapply infer_expression_fork;
    [apply infer_expression_stem; apply infer_map_via_lists|
      apply infer_expression_stem; exact Hr|exact HT1].
Qed.

Definition map_array a b f := Eval cbn in to_tree
  (star "n" (lam2
    ((Val (take_array b) @@ Ref "n") ''C
      (Val (map_value f b) ''C (Val (read_array a) @@ Ref "n")))
    (Val (take_array a) @@ Ref "n" @@ Val (nil_value a)))).
Definition array_mapper a b f n :=
  lam (array_builder b n 'C (map_value f b 'C array_reader a n))
    (array_value a (array_elements a n List.nil)).
Lemma map_array_eval : forall a b f n,
  map_array a b f @ n ==> array_mapper a b f n.
Proof.
  intros; pose proof (take_array_eval a n); pose proof (take_array_eval b n).
  pose proof (read_array_eval a n).
  pose proof (array_builder_list n a a List.nil) as HW; cbn [list_value] in HW.
  unfold map_array, array_mapper, lam; evaluate.
Qed.

Section MapTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Definition infer_map_array a b f A B F
  (Ha : infer AI @ a ==> Sm A) (Hb : infer AI @ b ==> Sm B)
  (Hf : infer AI @ f ==> Sm F) (HFA : type_app AI @ F @r A ==> Sm B) :
  { M : Combination | infer AI @ map_array a b f ==> Sm M /\
    forall n, unary_index n -> type_app AI @ M @r n ==>
      Sm (Array A n --> Array B n) }.
Proof using AI HL HA.
  pose proof (proj2_sig (infer_read_array AI HL HA a A Ha)) as [HR HRT].
  pose proof (infer_take_array AI HL HA a A Ha) as HBa.
  pose proof (infer_take_array AI HL HA b B Hb) as HBb.
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  pose proof (infer_map_value AI HL f F b B Hf Hb) as HM.
  pose proof (type_app_map_value AI HL F A B HFA) as HM1.
  eexists; split.
  - unfold map_array; infer_tac.
  - intros n Hn.
    pose proof (HRT n Hn) as HRA.
    pose proof (take_array_type_application AI a A HL HA Ha n Hn) as HAA.
    pose proof (take_array_type_application AI b B HL HA Hb n Hn) as HBB.
    repeat first [eassumption|apply funty_eliminator_eval|progress type_app_tac].
    type_app_tac.
    apply type_app_stem_ev; apply type_app_stem_function.
    repeat first [eassumption|apply funty_eliminator_eval|progress type_app_tac].
Defined.
Lemma infer_map_array_specialisation : forall a b f A B F n,
  infer AI @ a ==> Sm A -> infer AI @ b ==> Sm B ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r A ==> Sm B -> unary_index n ->
  infer_expression AI @ (map_array a b f @ n) ==>
    Sm (Array A n --> Array B n).
Proof using AI HL HA.
  intros a b f A B F n Ha Hb Hf HFA Hn.
  destruct (infer_map_array a b f A B F Ha Hb Hf HFA) as [M [HM HMT]].
  eapply infer_expression_fork.
  - apply infer_expression_stem; exact HM.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HMT; exact Hn.
Qed.
Lemma infer_map_array_application : forall a b f A B F n xs,
  infer AI @ a ==> Sm A -> infer AI @ b ==> Sm B ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r A ==> Sm B -> unary_index n ->
  infer AI @ xs ==> Sm (Array A n) ->
  infer_expression AI @ (map_array a b f @ n @r xs) ==> Sm (Array B n).
Proof using AI HL HA.
  intros a b f A B F n xs Ha Hb Hf HFA Hn HX.
  eapply infer_expression_fork.
  - eapply infer_map_array_specialisation; eassumption.
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End MapTyping.

Lemma array_elements_exact : forall b xs,
  array_elements b (sequence_index xs) xs = xs.
Proof. intros b xs; revert b; induction xs; intro b; cbn; congruence. Qed.
Lemma array_builder_exact : forall b d xs,
  array_builder b (sequence_index xs) @ list_value d xs ==> array_value b xs.
Proof. intros; pose proof (array_builder_list (sequence_index xs) b d xs) as H;
  rewrite array_elements_exact in H; exact H. Qed.
Lemma array_mapper_eval : forall a b f n xs ls ms ys,
  array_reader a n @ xs ==> ls -> map_value f b @ ls ==> ms ->
  array_builder b n @ ms ==> ys -> array_mapper a b f n @ xs ==> ys.
Proof. intros; unfold array_mapper, lam; evaluate. Qed.
Lemma array_mapper_exact : forall a b f d xs ys,
  Forall2 (fun x y => f @ x ==> y) xs ys ->
  array_mapper a b f (sequence_index xs) @ array_value d xs ==> array_value b ys.
Proof.
  intros a b f d xs ys H.
  assert (HI : sequence_index xs = sequence_index ys) by (induction H; cbn; congruence).
  eapply array_mapper_eval.
  - apply array_reader_eval; apply array_value_supplies; apply reader_consumer_sequence.
  - exact (map_value_list f b a xs ys H).
  - rewrite HI; apply array_builder_exact.
Qed.

(** Accept the action at runtime too, so that a generated row mapper can
    itself be passed to the outer array map. Witnesses remain explicit. *)
Definition map_array_with a b := Eval cbn in to_tree
  (star "f" (star "n" (lam2
    ((Val (take_array b) @@ Ref "n") ''C
      ((Val map_with @@ Ref "f" @@ Val b) ''C
        (Val (read_array a) @@ Ref "n")))
    (Val (take_array a) @@ Ref "n" @@ Val (nil_value a))))).
Lemma map_array_with_eval : forall a b f n,
  map_array_with a b @ f @r n ==> array_mapper a b f n.
Proof.
  intros; pose proof (take_array_eval a n); pose proof (take_array_eval b n).
  pose proof (read_array_eval a n).
  pose proof (array_builder_list n a a List.nil) as HW; cbn [list_value] in HW.
  pose proof (map_with_specialises f b) as HM.
  unfold map_array_with, array_mapper, lam; evaluate.
Qed.

Section RuntimeAction.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Definition infer_map_array_with a b A B
  (Ha : infer AI @ a ==> Sm A) (Hb : infer AI @ b ==> Sm B) :
  { M : Combination | infer AI @ map_array_with a b ==> Sm M /\
    forall F, type_app AI @ F @r A ==> Sm B ->
    exists T, type_app AI @ M @r F ==> Sm T /\
      forall n, unary_index n -> type_app AI @ T @r n ==>
        Sm (Array A n --> Array B n) }.
Proof using AI HL HA.
  pose proof (proj2_sig (infer_read_array AI HL HA a A Ha)) as [HR HRT].
  pose proof (infer_take_array AI HL HA a A Ha) as HBa.
  pose proof (infer_take_array AI HL HA b B Hb) as HBb.
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  pose proof (infer_map_with AI) as HM.
  eexists; split.
  - unfold map_array_with; infer_tac.
  - intros F HFA.
    destruct (type_app_map_with AI HL F B) as [R0 [HMF HMF2]].
    pose proof (type_app_map_value AI HL F A B HFA) as HMV.
    eexists; split; [type_app_tac|].
    intros n Hn.
    pose proof (HRT n Hn) as HRA.
    pose proof (take_array_type_application AI a A HL HA Ha n Hn) as HAA.
    pose proof (take_array_type_application AI b B HL HA Hb n Hn) as HBB.
    repeat first [eassumption|apply funty_eliminator_eval|progress type_app_tac].
    type_app_tac.
    apply type_app_stem_ev; apply type_app_stem_function.
    repeat first [eassumption|apply funty_eliminator_eval|progress type_app_tac].
Defined.
Lemma infer_map_array_with_expression : forall a b A B F e n,
  infer AI @ a ==> Sm A -> infer AI @ b ==> Sm B ->
  infer_expression AI @ e ==> Sm F -> type_app AI @ F @r A ==> Sm B -> unary_index n ->
  infer_expression AI @ Fk (Fk (Sm (map_array_with a b)) e) (Sm n) ==>
    Sm (Array A n --> Array B n).
Proof using AI HL HA.
  intros a b A B F e n Ha Hb He HFA Hn.
  destruct (infer_map_array_with a b A B Ha Hb) as [M [HM HMT]].
  destruct (HMT F HFA) as [T [HT HTn]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork.
    + apply infer_expression_stem; exact HM.
    + exact He.
    + exact HT.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HTn; exact Hn.
Qed.
End RuntimeAction.


(** Shared sample arrays. *)
Unset Default Proof Using.
Definition two_index := Sm (Sm Lf).
Definition number_row := array_value zero (numeral 1 :: numeral 2 :: List.nil).
Lemma number_row_typed : infer array_ontology @ number_row ==> Sm (Array ('Nat) two_index).
Proof.
  unfold number_row; change (infer array_ontology @ array_value zero
    (numeral 1 :: numeral 2 :: List.nil) ==>
    Sm (Array ('Nat) (sequence_index (numeral 1 :: numeral 2 :: List.nil)))).
  apply array_value_typed.
  - apply array_ontology_support.
  - apply infer_zero; apply array_ontology_supports_number.
  - repeat first [apply Forall_cons|apply Forall_nil|apply conj|reflexivity]; apply numeral_typed; apply array_ontology_supports_number.
Qed.


(** Live-declarations checks for runtime tree-indexed arrays and matrices. Dimensions are tree values.
    The numerals 1,2,3,4 below are array elements, not Rocq length indices. *)
From Stdlib Require Import List.
From TreeTyping Require Import tree typing soundness.
From TreeTyping Require Import functions data_types.

Unset Default Proof Using.
From TreeTyping Require Import booleans.

Section FunctionEnabledExamples.
(** Runtime boundary checks: a short list is padded with the default, and
    a long one truncated.
    Both use a runtime tree index, not a Coq natural-number parameter. *)
Example take_two_pads : forall b x,
  take_array b @ Sm (Sm Lf) @r list_value b (x :: List.nil) ==>
    array_value b (x :: b :: List.nil).
Proof. intros; apply take_array_list. Qed.

Example take_two_truncates : forall b x y z,
  take_array b @ Sm (Sm Lf) @r list_value b (x :: y :: z :: List.nil) ==>
    array_value b (x :: y :: List.nil).
Proof. intros; apply take_array_list. Qed.

(** Instantiate the support obligations with the live, sound declarations. *)
Example all_take_two_padded : infer_expression array_ontology @
    (take_array Lf @ Sm (Sm Lf) @r nil_value Lf) ==>
    Sm (Array Lf (Sm (Sm Lf))).
Proof.
   apply infer_take_array_list_application.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.
  - apply infer_leaf.
  - first [unary_tac|repeat constructor].
  - apply infer_nil_value; [apply array_ontology_supports_list|apply infer_leaf].
Qed.

Example all_take_two_padded_preserved :
  infer array_ontology @ array_value Lf (Lf :: Lf :: List.nil) ==>
    Sm (Array Lf (Sm (Sm Lf))).
Proof.
   eapply array_ontology_EPT.

  - exact (take_array_list Lf (Sm (Sm Lf)) Lf List.nil).
  - apply all_take_two_padded.
Qed.


(** Computed array witnesses. *)
Example computed_witness_reader_typed : infer_expression array_ontology @ generated_row_reader Lf Lf (Sm (Sm Lf)) ==>
    Sm (Array (Array Lf (Sm (Sm Lf))) Lf --> 'List[Array Lf (Sm (Sm Lf))]).
Proof.
   apply infer_generated_row_reader.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.

  - apply infer_leaf.
  - first [unary_tac|constructor].
  - first [unary_tac|repeat constructor].
Qed.
Example computed_witness_reader_preserved :
  infer array_ontology @ array_reader (array_value Lf (Lf :: Lf :: List.nil)) Lf ==>
    Sm (Array (Array Lf (Sm (Sm Lf))) Lf --> 'List[Array Lf (Sm (Sm Lf))]).
Proof.
   eapply array_ontology_EPT.

  - apply (generated_row_reader_eval Lf Lf (Sm (Sm Lf))).
  - apply computed_witness_reader_typed.
Qed.

End FunctionEnabledExamples.

(** Arrays use the same declarations as the generic and other data families. *)
Example all_arrays_append_two_singletons :
  infer_expression array_ontology @
    (array_append @ (arrays.prepend Lf (arrays.empty Lf)
      '* arrays.prepend Lf (arrays.empty Lf))) ==> Sm (Array Lf (Sm (Sm Lf))).
Proof.
  eapply infer_array_append_application with (n := Sm Lf) (m := Sm Lf);
    repeat first [apply array_ontology_support|apply arrays.infer_prepend|
      apply arrays.infer_empty|apply infer_leaf].
Qed.


(** * Reading an array with no index

    An array applies a consumer once per entry, and the consumer's type may
    change at each step, so a consumer can accumulate, and a program that
    reads an array needs no length.  [reading s f] is the delay
    ['wait[array_loop, s '* f]]: given an entry [x] it becomes
    [reading (f @ (s '* x)) f].  Typing goes one step per entry and follows
    no recursion.  The result is read back from the delay by [acc_cell].
    Results are built by prepending and reversed once, so that a result is
    the canonical [array_value]. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans data_types arrays.
Local Open Scope string_scope.

(** ** The reading loop *)
Definition array_loop_body := Eval cbn in to_tree
  (star "self" (star "p" (star "x"
    (''wait[Ref "self", ((Val 'snd @@ Ref "p") @@ ((Val 'fst @@ Ref "p") ''* Ref "x")) ''* (Val 'snd @@ Ref "p")])))).
Definition array_loop := Z array_loop_body.
Definition reading s f := 'wait[array_loop, s '* f].

Lemma array_loop_tag_free : tag_free array_loop = true.
Proof. vm_compute; reflexivity. Qed.

Lemma reading_eval : forall s f x s',
  f @ (s '* x) ==> s' -> reading s f @ x ==> reading s' f.
Proof.
  intros s f x s' H; unfold reading; apply wait_eval.
  eapply eval_appl; [unfold array_loop; apply Z_unfold|].
  { unfold array_loop_body; cbn; d_eval. }
  cbn. d_eval.
Qed.

Section LoopTyping.
Variable AI : Combination.

Lemma type_app_reading : forall S F A S',
  type_app AI @ F @r (S '* A) ==> Sm S' ->
  type_app AI @ reading S F @r A ==> Sm (reading S' F).
Proof.
  intros S F A S' H.
  pose proof (type_app_fst_product AI) as Hf. pose proof (type_app_snd_product AI) as Hs.
  unfold reading; eapply type_app_wait; [|].
  - unfold array_loop; eapply type_app_Z.
    + unfold array_loop_body; cbn; repeat ty.
    + cbn; repeat ty.
  - cbn; repeat ty.
Qed.

Local Transparent structural_fork.
Lemma type_app_triage_fork : forall F0 F1 F2 X Y G V,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  (forall E N, Fk X Y <> 'tagged[E,N]) ->
  type_app AI @ F2 @r X ==> Sm G -> type_app AI @ G @r Y ==> Sm V ->
  type_app AI @ 'triage[F0,F1,F2] @r Fk X Y ==> Sm V.
Proof.
  intros F0 F1 F2 X Y G V HP HX H1 H2; apply app_triage_structural.
  apply (proj2 (structural_triage_plain _ _ _ _ _ _ HP)).
  unfold plain_triage, structural_fork.
  pose proof (get_tagged_none _ HX).
  destruct (eval_app_r_inv _ _ _ H1) as [w [Hw HR]].
  destruct (eval_app_r_inv _ _ _ H2) as [w2 [Hw2 HR2]].
  cbn; repeat first [eassumption | progress evaluate].
Qed.
Local Opaque structural_fork.

Lemma type_app_dir_l : forall X Y, (forall E N, Fk X Y <> 'tagged[E,N]) ->
  type_app AI @ dir_prog dir_l @r Fk X Y ==> Sm X.
Proof. intros; eapply type_app_triage_fork; [intros; discriminate|assumption|repeat ty|repeat ty]. Qed.
Lemma type_app_dir_r : forall X Y, (forall E N, Fk X Y <> 'tagged[E,N]) ->
  type_app AI @ dir_prog dir_r @r Fk X Y ==> Sm Y.
Proof. intros; eapply type_app_triage_fork; [intros; discriminate|assumption|repeat ty|repeat ty]. Qed.
Lemma type_app_dir_s : forall N, type_app AI @ dir_prog dir_s @r Sm N ==> Sm N.
Proof. intros; apply type_app_structural_triage_stem; [intros; discriminate|apply type_app_I]. Qed.

Lemma type_app_read_cell : forall M S F,
  type_app AI @ acc_cell @r 'wait[M, S '* F] ==> Sm S.
Proof.
  intros M S F; unfold acc_cell, path_cell, path_arg; cbn [List.app path_prog].
  repeat (eapply type_app_compose; [reject_name|intros; discriminate|
    first [apply type_app_dir_s|apply type_app_dir_l; intros; discriminate
          |apply type_app_dir_r; intros; discriminate]|]).
  apply type_app_I.
Qed.
End LoopTyping.

(** ** Reversal and map *)
Definition empty_t b := Val ('tagger[array_nm]) @@ ''wait[Val 'KI, b].
Definition cons_t x s := Val ('tagger[array_nm]) @@ (s ''C swap_t x).
Definition read_t xs s f := Val acc_cell @@ (xs @@ ''wait[Val array_loop, s ''* f]).

Definition array_cons := Eval cbn in to_tree
  (star "p" (cons_t (Val 'snd @@ Ref "p") (Val 'fst @@ Ref "p"))).
Definition entry_step := Eval cbn in to_tree
  (star "f" (star "p" (cons_t (Ref "f" @@ (Val 'snd @@ Ref "p")) (Val 'fst @@ Ref "p")))).
Definition array_rev := Eval cbn -[array_loop acc_cell array_cons] in to_tree
  (star "q" (read_t (Val 'snd @@ Ref "q") (empty_t (Val 'fst @@ Ref "q")) (Val array_cons))).
Definition array_map := Eval cbn -[array_loop acc_cell array_rev] in to_tree
  (star "t" (Val array_rev @@ ((Val 'fst @@ (Val 'snd @@ Ref "t")) ''*
     (read_t (Val 'snd @@ (Val 'snd @@ Ref "t")) (empty_t (Val 'fst @@ (Val 'snd @@ Ref "t")))
        (''wait[Val entry_step, Val 'fst @@ Ref "t"]))))).

Lemma index_sum_succ : forall n j, index_sum n (Sm j) = Sm (index_sum n j).
Proof. induction n as [|k IH|i _ k IH]; intro j; cbn; [reflexivity|rewrite IH; reflexivity|rewrite IH; reflexivity]. Qed.
Lemma index_sum_leaf : forall n, unary_index n -> index_sum n Lf = n.
Proof. intros n Hn; induction Hn as [|n _ IH] using unary_index_ind; cbn; congruence. Qed.

Section Reading.
Variable AI : Combination.
Hypothesis HA : supports_arrays AI.

(** Reading [n] entries from a reading whose type counts up. *)
Lemma reading_takes : forall (S : Combination -> Combination) F A,
  (forall j, type_app AI @ F @r (S j '* A) ==> Sm (S (Sm j))) ->
  forall n j, array_takes (type_app AI) A n (reading (S j) F) (reading (S (index_sum n j)) F).
Proof.
  intros S F A H n; induction n as [|k IH|i _ k IH]; intro j; cbn [array_takes index_sum].
  - reflexivity.
  - eexists; split; [apply type_app_reading; apply H|].
    rewrite <- index_sum_succ; apply IH.
  - eexists; split; [apply type_app_reading; apply H|].
    rewrite <- index_sum_succ; apply IH.
Qed.

Lemma type_app_read_array : forall S F A n,
  (forall j, type_app AI @ F @r (S j '* A) ==> Sm (S (Sm j))) -> unary_index n ->
  type_app AI @ Array A n @r reading (S Lf) F ==> Sm (reading (S n) F).
Proof.
  intros S F A n H Hn; apply type_app_abstract, array_eliminator_unary, array_unary_eval.
  pose proof (reading_takes S F A H n Lf) as T; rewrite index_sum_leaf in T by exact Hn; exact T.
Qed.

Local Ltac ty_onto_more ::= eapply declaration_apply; [exact HA|first [apply array_abstractor_zero|apply array_abstractor_step]].

Lemma type_app_array_cons : forall A j,
  type_app AI @ array_cons @r (Array A j '* A) ==> Sm (Array A (Sm j)).
Proof.
  intros A j; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  unfold array_cons; repeat ty.
Qed.
Lemma type_app_entry_step : forall F A B j,
  type_app AI @ F @r A ==> Sm B ->
  type_app AI @ 'wait[entry_step, F] @r (Array B j '* A) ==> Sm (Array B (Sm j)).
Proof.
  intros F A B j HF; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  eapply type_app_wait; unfold entry_step; repeat ty.
Qed.

Local Opaque array_loop acc_cell array_cons.
Local Ltac rd := first [apply type_app_read_cell | ty].
Lemma type_app_array_rev : forall A n, unary_index n ->
  type_app AI @ array_rev @r (A '* Array A n) ==> Sm (Array A n).
Proof.
  intros A n Hn; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_read_array (Array A) array_cons A n (type_app_array_cons A) Hn) as HR.
  unfold reading in HR.
  unfold array_rev; repeat rd.
Qed.
Lemma type_app_array_map : forall F A B n, unary_index n ->
  type_app AI @ F @r A ==> Sm B ->
  type_app AI @ array_map @r (F '* (B '* Array A n)) ==> Sm (Array B n).
Proof.
  intros F A B n Hn HF; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_read_array (Array B) ('wait[entry_step, F]) A n
     (fun j => type_app_entry_step F A B j HF) Hn) as HR.
  pose proof (type_app_array_rev B n Hn) as HV.
  unfold reading in HR.
  unfold array_map; repeat rd.
Qed.
End Reading.
Theorem array_map_polymorphic : forall AI F A B n,
  supports_arrays AI -> unary_index n -> type_app AI @ F @r A ==> Sm B ->
  type_app AI @ array_map @r (F '* (B '* Array A n)) ==> Sm (Array B n).
Proof. intros AI F A B n HS Hn HF; exact (type_app_array_map AI HS F A B n Hn HF). Qed.

(** ** Action on values *)
Inductive folds f : Combination -> List.list Combination -> Combination -> Prop :=
| folds_nil : forall s, folds f s List.nil s
| folds_cons : forall s x xs s1 s', f @ (s '* x) ==> s1 -> folds f s1 xs s' ->
    folds f s (x :: xs) s'.
Definition reads a xs := forall f v, supplies xs f v -> a @ f ==> v.
Lemma array_value_reads : forall d xs, reads (array_value d xs) xs.
Proof. intros d xs f v H; apply array_value_supplies; exact H. Qed.
Lemma folds_supplies : forall f s xs s', folds f s xs s' -> supplies xs (reading s f) (reading s' f).
Proof. intros f s xs s' H; induction H; econstructor; [apply reading_eval; eassumption|assumption]. Qed.
Lemma reading_result : forall s f, acc_cell @ reading s f ==> s.
Proof. intros; apply path_eval. Qed.
Lemma read_folds : forall a xs f s s', reads a xs -> folds f s xs s' ->
  a @ reading s f ==> reading s' f.
Proof. intros; apply H; apply folds_supplies; assumption. Qed.

Lemma array_cons_eval : forall s x, array_cons @ (s '* x) ==> arrays.prepend x s.
Proof. intros; unfold array_cons, arrays.prepend, swap; cbn; d_eval. Qed.
Lemma entry_step_eval : forall f s x y, f @ x ==> y ->
  'wait[entry_step, f] @ (s '* x) ==> arrays.prepend y s.
Proof. intros; apply wait_eval; unfold entry_step, arrays.prepend, swap; cbn; d_eval. Qed.
Lemma folds_map : forall f b xs ys l, List.Forall2 (fun x y => f @ x ==> y) xs ys ->
  folds ('wait[entry_step, f]) (array_value b l) xs (array_value b (List.rev ys ++ l)).
Proof.
  intros f b xs ys l0 H; revert l0; induction H as [|x y xs ys Hxy _ IH]; intro l0; cbn.
  - constructor.
  - econstructor; [apply entry_step_eval; eassumption|].
    rewrite <- List.app_assoc; apply (IH (y :: l0)).
Qed.
Lemma folds_rev : forall b xs l,
  folds array_cons (array_value b l) xs (array_value b (List.rev xs ++ l)).
Proof.
  intros b xs; induction xs as [|x xs IH]; intro l; cbn.
  - constructor.
  - econstructor; [apply array_cons_eval|].
    rewrite <- List.app_assoc; apply (IH (x :: l)).
Qed.

Local Opaque array_loop acc_cell array_cons.
Lemma array_rev_eval : forall b a xs, reads a xs ->
  array_rev @ (b '* a) ==> array_value b (List.rev xs).
Proof.
  intros b a xs Ha.
  pose proof (read_folds a xs _ _ _ Ha (folds_rev b xs List.nil)) as H.
  pose proof (reading_result (array_value b (List.rev xs ++ List.nil)) array_cons) as HR.
  rewrite List.app_nil_r in H, HR; cbn [array_value] in H.
  unfold reading, arrays.empty in *.
  unfold array_rev; cbn; d_eval.
Qed.
Lemma array_map_eval : forall f b a xs ys, reads a xs ->
  List.Forall2 (fun x y => f @ x ==> y) xs ys ->
  array_map @ (f '* (b '* a)) ==> array_value b ys.
Proof.
  intros f b a xs ys Ha H.
  pose proof (read_folds a xs _ _ _ Ha (folds_map f b xs ys List.nil H)) as H1.
  pose proof (reading_result (array_value b (List.rev ys ++ List.nil)) ('wait[entry_step, f])) as HR.
  pose proof (array_rev_eval b _ _ (array_value_reads b (List.rev ys))) as HV.
  rewrite List.rev_involutive in HV.
  rewrite List.app_nil_r in H1, HR; cbn [array_value] in H1.
  unfold reading, arrays.empty in *.
  unfold array_map; cbn; d_eval.
Qed.

(** ** Reading in lock step

    [array_uncons] splits a non-empty array.  It uses no index: its first
    step keeps the head, which is also the witness of the tail. *)
Local Transparent array_cons.
Definition hold_step := Eval cbn in to_tree
  (star "p" ((Val 'fst @@ (Val 'fst @@ Ref "p")) ''*
     cons_t (Val 'snd @@ Ref "p") (Val 'snd @@ (Val 'fst @@ Ref "p")))).
Definition uncons_start := Eval cbn -[array_loop hold_step] in to_tree
  (star "h" (''wait[Val array_loop, (Ref "h" ''* empty_t (Ref "h")) ''* Val hold_step])).
Definition array_uncons := Eval cbn -[array_rev acc_cell uncons_start] in to_tree
  (star "a" ((star "u" ((Val 'fst @@ Ref "u") ''* (Val array_rev @@ Ref "u")))
     @@ (Val acc_cell @@ (Ref "a" @@ Val uncons_start)))).
Definition array_tail := Eval cbn -[array_uncons] in to_tree
  (star "a" (Val 'snd @@ (Val array_uncons @@ Ref "a"))).

(** [lock_step] reads an entry [x] of one array with state [s * rest] and
    takes the next entry [y] off [rest]. *)
Definition lock_step := Eval cbn -[array_uncons] in to_tree
  (star "g" (star "p"
    ((star "u" ((Ref "g" @@ ((Val 'fst @@ (Val 'fst @@ Ref "p")) ''*
                  ((Val 'snd @@ Ref "p") ''* (Val 'fst @@ Ref "u"))))
                ''* (Val 'snd @@ Ref "u")))
     @@ (Val array_uncons @@ (Val 'snd @@ (Val 'fst @@ Ref "p")))))).
Definition array_lock := Eval cbn -[array_loop acc_cell lock_step] in to_tree
  (star "q" (Val 'fst @@ read_t (Val 'fst @@ (Val 'snd @@ (Val 'snd @@ Ref "q")))
     ((Val 'fst @@ (Val 'snd @@ Ref "q")) ''* (Val 'snd @@ (Val 'snd @@ (Val 'snd @@ Ref "q"))))
     (''wait[Val lock_step, Val 'fst @@ Ref "q"]))).
Definition array_zip := Eval cbn -[array_rev array_lock entry_step] in to_tree
  (star "q" (Val array_rev @@ ((Val 'fst @@ (Val 'snd @@ Ref "q")) ''*
     (Val array_lock @@ (''wait[Val entry_step, Val 'fst @@ Ref "q"] ''*
        (empty_t (Val 'fst @@ (Val 'snd @@ Ref "q")) ''* (Val 'snd @@ (Val 'snd @@ Ref "q")))))))).

Section LockTyping.
Variable AI : Combination.
Hypothesis HA : supports_arrays AI.
Local Ltac ty_onto_more ::= eapply declaration_apply; [exact HA|first [apply array_abstractor_zero|apply array_abstractor_step]].
Local Ltac rd := first [apply type_app_read_cell | ty].
Local Opaque array_loop acc_cell array_cons array_rev hold_step array_uncons uncons_start lock_step array_lock entry_step.

Local Transparent hold_step.
Lemma type_app_hold_step : forall R j,
  type_app AI @ hold_step @r ((R '* Array R j) '* R) ==> Sm (R '* Array R (Sm j)).
Proof.
  intros R j; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  unfold hold_step; repeat ty.
Qed.
Local Opaque hold_step.
Local Transparent uncons_start.
Lemma type_app_uncons_start : forall R,
  type_app AI @ uncons_start @r R ==> Sm (reading (R '* Array R Lf) hold_step).
Proof. intros R; unfold uncons_start, reading; repeat ty. Qed.
Local Opaque uncons_start.

Lemma type_app_array_uncons_start : forall R k, unary_index k ->
  type_app AI @ Array R (Sm k) @r uncons_start ==> Sm (reading (R '* Array R k) hold_step).
Proof.
  intros R k Hk; apply type_app_abstract, array_eliminator_unary, array_unary_eval.
  cbn [array_takes]; eexists; split; [apply type_app_uncons_start|].
  pose proof (reading_takes AI (fun j => R '* Array R j) hold_step R (type_app_hold_step R) k Lf) as T.
  rewrite index_sum_leaf in T by exact Hk; exact T.
Qed.

Local Transparent array_uncons.
Lemma type_app_array_uncons : forall R k, unary_index k ->
  type_app AI @ array_uncons @r Array R (Sm k) ==> Sm (R '* Array R k).
Proof.
  intros R k Hk; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_array_uncons_start R k Hk) as H1.
  pose proof (type_app_array_rev AI HA R k Hk) as H2.
  unfold reading in H1.
  unfold array_uncons; repeat rd.
Qed.
Local Opaque array_uncons.
Local Transparent array_tail.
Lemma type_app_array_tail : forall R k, unary_index k ->
  type_app AI @ array_tail @r Array R (Sm k) ==> Sm (Array R k).
Proof.
  intros R k Hk; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_array_uncons R k Hk) as H1.
  unfold array_tail; repeat ty.
Qed.

Local Transparent lock_step.
Lemma type_app_lock_step : forall G S S' R A k, unary_index k ->
  type_app AI @ G @r (S '* (A '* R)) ==> Sm S' ->
  type_app AI @ 'wait[lock_step, G] @r ((S '* Array R (Sm k)) '* A) ==> Sm (S' '* Array R k).
Proof.
  intros G S S' R A k Hk HG; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_array_uncons R k Hk) as H1.
  eapply type_app_wait; unfold lock_step; repeat ty.
Qed.
Local Opaque lock_step.

Lemma lock_takes : forall (S : Combination -> Combination) G A R,
  (forall j, type_app AI @ G @r (S j '* (A '* R)) ==> Sm (S (Sm j))) ->
  forall k, unary_index k -> forall j,
  array_takes (type_app AI) A k (reading (S j '* Array R k) ('wait[lock_step, G]))
    (reading (S (index_sum k j) '* Array R Lf) ('wait[lock_step, G])).
Proof.
  intros S G A R H k Hk; induction Hk as [|k Hk IH] using unary_index_ind; intro j;
    cbn [array_takes index_sum]; [reflexivity|].
  eexists; split; [apply type_app_reading; apply type_app_lock_step; [exact Hk|apply H]|].
  rewrite <- index_sum_succ; apply IH.
Qed.

Local Transparent array_lock.
Lemma type_app_array_lock : forall (S : Combination -> Combination) G A R n, unary_index n ->
  (forall j, type_app AI @ G @r (S j '* (A '* R)) ==> Sm (S (Sm j))) ->
  type_app AI @ array_lock @r (G '* (S Lf '* (Array A n '* Array R n))) ==> Sm (S n).
Proof.
  intros S G A R n Hn H; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  assert (HT : type_app AI @ Array A n @r reading (S Lf '* Array R n) ('wait[lock_step, G]) ==>
     Sm (reading (S n '* Array R Lf) ('wait[lock_step, G]))).
  { apply type_app_abstract, array_eliminator_unary, array_unary_eval.
    pose proof (lock_takes S G A R H n Hn Lf) as T; rewrite index_sum_leaf in T by exact Hn; exact T. }
  unfold reading in HT.
  unfold array_lock; repeat rd.
Qed.
Local Opaque array_lock.
Local Transparent array_zip.
Lemma type_app_array_zip : forall G A C B n, unary_index n ->
  type_app AI @ G @r (A '* C) ==> Sm B ->
  type_app AI @ array_zip @r (G '* (B '* (Array A n '* Array C n))) ==> Sm (Array B n).
Proof.
  intros G A C B n Hn HG; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_array_lock (Array B) ('wait[entry_step, G]) A C n Hn
    (fun j => type_app_entry_step AI HA G (A '* C) B j HG)) as H1.
  pose proof (type_app_array_rev AI HA B n Hn) as H2.
  unfold array_zip; repeat ty.
Qed.
End LockTyping.

(** ** Lock step on values *)
Inductive folds2 g : Combination -> List.list Combination -> List.list Combination -> Combination -> Prop :=
| folds2_nil : forall s, folds2 g s List.nil List.nil s
| folds2_cons : forall s x xs y ys s1 s', g @ (s '* (x '* y)) ==> s1 -> folds2 g s1 xs ys s' ->
    folds2 g s (x :: xs) (y :: ys) s'.

Lemma folds2_lengths : forall g s xs ys s', folds2 g s xs ys s' ->
  sequence_index xs = sequence_index ys.
Proof. intros g s xs ys s' H; induction H; cbn; congruence. Qed.

Local Transparent hold_step uncons_start array_uncons array_tail lock_step array_lock array_zip.
Lemma hold_step_eval : forall h acc y,
  hold_step @ ((h '* acc) '* y) ==> (h '* arrays.prepend y acc).
Proof. intros; unfold hold_step, arrays.prepend, swap; cbn; d_eval. Qed.
Lemma folds_hold : forall h xs l,
  folds hold_step (h '* array_value h l) xs (h '* array_value h (List.rev xs ++ l)).
Proof.
  intros h xs; induction xs as [|x xs IH]; intro l; cbn.
  - constructor.
  - econstructor; [apply hold_step_eval|].
    rewrite <- List.app_assoc; apply (IH (x :: l)).
Qed.
Lemma uncons_start_eval : forall h,
  uncons_start @ h ==> reading (h '* arrays.empty h) hold_step.
Proof. intros; unfold uncons_start, reading, arrays.empty; cbn -[array_loop hold_step]; d_eval. Qed.
Local Opaque hold_step uncons_start.

Lemma array_uncons_eval : forall a x xs, reads a (x :: xs) ->
  array_uncons @ a ==> (x '* array_value x xs).
Proof.
  intros a x xs Ha.
  assert (H0 : a @ uncons_start ==> reading (x '* array_value x (List.rev xs)) hold_step).
  { apply Ha; econstructor; [apply uncons_start_eval|].
    pose proof (folds_supplies _ _ _ _ (folds_hold x xs List.nil)) as H1.
    rewrite List.app_nil_r in H1; exact H1. }
  pose proof (reading_result (x '* array_value x (List.rev xs)) hold_step) as H1.
  pose proof (array_rev_eval x _ _ (array_value_reads x (List.rev xs))) as H2.
  rewrite List.rev_involutive in H2.
  unfold array_uncons; cbn -[array_rev]; d_eval.
Qed.
Lemma array_tail_eval : forall a x xs, reads a (x :: xs) ->
  array_tail @ a ==> array_value x xs.
Proof.
  intros a x xs Ha; pose proof (array_uncons_eval a x xs Ha) as H.
  unfold array_tail; cbn -[array_uncons]; d_eval.
Qed.

Lemma lock_step_eval : forall g s c x y ys s1, reads c (y :: ys) ->
  g @ (s '* (x '* y)) ==> s1 ->
  'wait[lock_step, g] @ ((s '* c) '* x) ==> (s1 '* array_value y ys).
Proof.
  intros g s c x y ys s1 Hc Hg; pose proof (array_uncons_eval c y ys Hc) as H.
  apply wait_eval; unfold lock_step; cbn -[array_uncons]; d_eval.
Qed.
Lemma folds_lock : forall g s xs ys s', folds2 g s xs ys s' ->
  forall c, reads c ys -> exists r, folds ('wait[lock_step, g]) (s '* c) xs (s' '* r).
Proof.
  intros g s xs ys s' H; induction H; intros c Hc.
  - eexists; constructor.
  - destruct (IHfolds2 (array_value y ys) (array_value_reads _ _)) as [r Hr].
    exists r; econstructor; [apply lock_step_eval; eassumption|exact Hr].
Qed.
Lemma array_lock_eval : forall g s a c xs ys s', reads a xs -> reads c ys ->
  folds2 g s xs ys s' -> array_lock @ (g '* (s '* (a '* c))) ==> s'.
Proof.
  intros g s a c xs ys s' Ha Hc H.
  destruct (folds_lock _ _ _ _ _ H c Hc) as [r Hr].
  pose proof (read_folds a xs _ _ _ Ha Hr) as H1.
  pose proof (reading_result (s' '* r) ('wait[lock_step, g])) as H2.
  unfold reading in H1, H2; unfold array_lock; cbn -[array_loop acc_cell lock_step]; d_eval.
Qed.

Inductive zips g : List.list Combination -> List.list Combination -> List.list Combination -> Prop :=
| zips_nil : zips g List.nil List.nil List.nil
| zips_cons : forall x xs y ys z zs, g @ (x '* y) ==> z -> zips g xs ys zs ->
    zips g (x :: xs) (y :: ys) (z :: zs).
Lemma folds2_zips : forall g b xs ys zs l, zips g xs ys zs ->
  folds2 ('wait[entry_step, g]) (array_value b l) xs ys (array_value b (List.rev zs ++ l)).
Proof.
  intros g b xs ys zs l0 H; revert l0; induction H as [|x xs y ys z zs Hz _ IH]; intro l0; cbn.
  - constructor.
  - econstructor; [apply entry_step_eval; eassumption|].
    rewrite <- List.app_assoc; apply (IH (z :: l0)).
Qed.
Lemma array_zip_eval : forall g b a c xs ys zs, reads a xs -> reads c ys ->
  zips g xs ys zs -> array_zip @ (g '* (b '* (a '* c))) ==> array_value b zs.
Proof.
  intros g b a c xs ys zs Ha Hc H.
  pose proof (folds2_zips g b xs ys zs List.nil H) as H0.
  rewrite List.app_nil_r in H0.
  pose proof (array_lock_eval _ _ _ _ _ _ _ Ha Hc H0) as H1.
  pose proof (array_rev_eval b _ _ (array_value_reads b (List.rev zs))) as H2.
  rewrite List.rev_involutive in H2.
  cbn [array_value] in H1; unfold arrays.empty in H1.
  unfold array_zip; cbn -[array_rev array_lock entry_step]; d_eval.
Qed.

Lemma array_programs_tag_free : tag_free array_map = true /\ tag_free array_rev = true /\
  tag_free array_uncons = true /\ tag_free array_tail = true /\ tag_free array_lock = true /\
  tag_free array_zip = true.
Proof. vm_compute; repeat split. Qed.
