(** * Queries (paper: Queries).

    The query interface and the query constructors with the query
    abstractor, size and its totality, typed equality and its totality, and
    finite-pattern queries.  The department queries are in
    customisation.v. *)


(**********************************************************************)
(* The Query family.                                                  *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions conditionals.

Set Default Proof Using "Type".
Open Scope nat_scope.
Open Scope string_scope.

(** A query consumes an argument of arbitrary type and returns a [B].
    Constants, applicative combination and ordinary triage provide its
    basic constructors; fixed points provide recursion. The abstractor takes
    type application [a], as function type introduction does: the [S]
    carrier [S2[Query[F],Query[V]]] gives [Query[B]] when [a @ F @ V] gives
    [B], and the recursive carrier [Z(decorate[F,Query[B]] o tagged_query)]
    when [a @ F @ Query[B]] gives [Query[B]].  No function type is needed.

    Specialisation is the conditional [if_named N f d]: it tests a declared
    wrapper name and passes the whole matching value to an action f of type
    F, with F applied to the wrapper type W giving B; any other value goes to
    a default of type Query[B].

    [choice_constructor] checks the type [IfNamed N F
    ('Query[B])] and introduces the resulting program as Query[B].
    [inf_specialised_query] exposes the name, abstractor, action and default
    obligations. The same untyped [if_named] supports Update in updates.v.
    Its runtime equations are in conditionals.v. At the type level the name
    test is run on the argument type by the IsNamed family. The conditional is
    sound on every inhabited input type: an inhabited type tagged at a
    declared wrapper name is the declared wrapper type.
    Traversal and specialisation remain separate
    constructors, so the fallback controls where traversal continues.

    [diagonal_query] instead takes a query returning a query, and runs the
    selected query on the original input. Its constructor recognises
    [S2[Query[Query[B]],I]]; soundness uses existing S, I and Query rules.
    updates.v uses this to ignore annotation evidence: a
    Boolean shape query selects a query on the executable component or the
    fallback as a value, then only the selected query runs. *)

Notation "'Kq b" := ('tagged['K1 b, query_nm]) (at level 70).
Notation "'S_q [ g , f ]" :=
  ('tagged['S2[g,f], query_nm]) (at level 0).
Notation "'tq [ f0 , f1 , f2 ]" :=
  ('tagged['triage[f0,f1,f2], query_nm]) (at level 0).

(** Term-level query constructors support abstraction without exposing the
    compiled combinations. *)
Notation "''Kq b" :=
  (''tagged[''K1 b, Val query_nm]) (at level 70).
Notation "''S_q [ g , f ]" :=
  (''tagged[''S2[g,f], Val query_nm]) (at level 0).
Notation "''tq [ f0 , f1 , f2 ]" :=
  (''tagged[''triage[f0,f1,f2], Val query_nm]) (at level 0).

(** Applying a query type to any argument type yields its result type
    (the twin of [type_app_Update] in updates.v). *)
Lemma type_app_Query : forall AI B U,
  type_app AI @ ('Query[B]) @r U ==> Sm B.
Proof. intros; apply type_app_abstract; apply query_eliminator_eval. Qed.

(** A generic query applies at every type. *)
Theorem generic_query_application : forall AI q B x U,
  infer AI @ q ==> Sm ('Query[B]) ->
  infer AI @ x ==> Sm U ->
  infer_expression AI @ (q @ x) ==> Sm B.
Proof.
  intros AI q B x U Hq Hx; eapply infer_expression_fork.
  - apply infer_expression_stem; exact Hq.
  - apply infer_expression_stem; exact Hx.
  - apply type_app_Query.
Qed.

(** Query constructors have the same operational behaviour as their
    untagged eliminators.  These lemmas keep clients from unfolding the
    tagged representation. *)
Lemma K_q_eval : forall b x,
  ('Kq b) @ x ==> b.
Proof. intros b x; apply tagged_eval; evaluate. Qed.

Lemma S_q_eval : forall g f x gx fx result,
  g @ x ==> gx ->
  f @ x ==> fx ->
  gx @ fx ==> result ->
  ('S_q[g,f]) @ x ==> result.
Proof. intros; apply tagged_eval; cbv; evaluate. Qed.

Lemma triage_q_leaf_eval : forall f0 f1 f2,
  ('tq[f0,f1,f2]) @ Lf ==> f0.
Proof. intros; apply tagged_eval; evaluate. Qed.

Lemma triage_q_stem_eval : forall f0 f1 f2 x result,
  f1 @ x ==> result ->
  ('tq[f0,f1,f2]) @ Sm x ==> result.
Proof. intros; apply tagged_eval; cbv; evaluate. Qed.

Lemma triage_q_fork_eval : forall f0 f1 f2 x y partial result,
  f2 @ x ==> partial ->
  partial @ y ==> result ->
  ('tq[f0,f1,f2]) @ Fk x y ==> result.
Proof. intros; apply tagged_eval; cbv; evaluate. Qed.

Definition query_K_case_package :
  { t : Combination |
    to_tree
      (tcase (''K1 (Ref "B"))
        (Val Lf @@ Ref "B")) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition query_K_case :=
  Eval cbn in proj1_sig query_K_case_package.

(** Recover the result parameter of an already constructed query type.
    Keep tag removal, name checking, and eliminator decomposition separate
    so that no proof expands one large nested pattern. *)
Definition get_query_name_package :
  { t : Combination |
    to_tree
      (tcase (Val Lf @@ Ref "E" @@ Val query_nm) (Ref "E")) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition get_query_name :=
  Eval cbn -[equal1] in proj1_sig get_query_name_package.

(** The eliminator of [Query[B]] is the delay ['wait[query_elim, B]].
    Its parameter [B] is read with the accessor [acc_arg]; the delay is
    rebuilt from it and compared with the eliminator, so only a genuine
    query eliminator yields its parameter. *)
Definition get_query_eliminator :=
  Eval cbv -[equal acc_arg query_elim] in to_tree
    (star "E" (op equal @@ Ref "E"
       @@ ''wait[Val query_elim, op acc_arg @@ Ref "E"]
       @@ (Val Lf @@ (op acc_arg @@ Ref "E")) @@ Val Lf)).

Definition get_query_eliminator_fn E :=
  if ceqb E (query_eliminator (path_fn path_arg E))
  then Sm (path_fn path_arg E) else Lf.

Lemma get_query_eliminator_eval : forall E,
  get_query_eliminator @ E ==> get_query_eliminator_fn E.
Proof.
  intros E; unfold get_query_eliminator_fn.
  destruct (equal1_bt_case E (query_eliminator (path_fn path_arg E)))
    as [[Hd [Hc He]]|[Hd [Hc He]]]; rewrite Hc;
    unfold get_query_eliminator, query_eliminator in *; fam_eval.
Qed.

Lemma get_query_eliminator_some : forall B,
  get_query_eliminator @ query_eliminator B ==> Sm B.
Proof.
  intros B; pose proof (get_query_eliminator_eval (query_eliminator B)) as H.
  unfold get_query_eliminator_fn in H.
  change (path_fn path_arg (query_eliminator B)) with B in H.
  rewrite ceqb_refl in H; exact H.
Qed.

Lemma get_query_eliminator_inv : forall E B,
  get_query_eliminator @ E ==> Sm B -> E = query_eliminator B.
Proof.
  intros E B H; pose proof (eval_deterministic _ _ H _ (get_query_eliminator_eval E)) as Heq.
  unfold get_query_eliminator_fn in Heq.
  destruct (ceqb _ _) eqn:Hc; [|discriminate].
  apply ceqb_true in Hc; inversion Heq; subst; exact Hc.
Qed.

Local Opaque get_query_eliminator.

Definition get_query_fields :=
  ('onStem1 get_query_eliminator) 'C get_query_name.

Definition get_query := ('onStem1 get_query_fields) 'C get_tagged.

Lemma get_query_some : forall B,
  get_query @ ('Query[B]) ==> Sm B.
Proof.
  intros B; pose proof (get_query_eliminator_some B).
  unfold get_query, get_query_fields, get_query_name; cbn.
  evaluate.
  - apply get_tagged_some.
  - cbv; repeat first
      [eassumption | eapply equal1_eq | progress evaluate].
Qed.

(** [query_handler] stays a constant inside the compiled clause, so that
    its behaviour ([query_handler_spec]) can be used directly. *)
Definition query_triage_case :=
  Eval cbv -[equal1 query_handler] in to_tree
      (''onFork1
        (star "left" (star "F2"
          (''onFork1
            (star "F0" (star "F1"
              (''onStem1
                (''K1
                  (Val Lf @@ Ref "F0"))
                @@ (op query_handler
                      @@ Ref "F0" @@ Ref "F1" @@ Ref "F2" @@ Val Lf))))
            @@ Ref "left")))).

(** The query handler (typing.v) is described by a Rocq function: it
    certifies [query_one_level F0] exactly when [F1 = Query[F0]] and
    [F2 = Query[Query[F0]]]. *)
Local Ltac qrun := first [eassumption | apply equal_eval | apply equal1_eq |
  evaluate_expr_core qrun qrun_head | idtac]
with qrun_head := first [eassumption | apply equal_eval | apply equal1_eq |
  evaluate_head_core qrun | idtac].

Lemma query_handler_miss : forall F0 F1 F2 U,
  (F1 <> 'Query[F0] \/ F2 <> 'Query['Query[F0]]) ->
  query_handler @ F0 @r F1 @r F2 @r U ==> Lf.
Proof.
  intros F0 F1 F2 U H.
  destruct (combination_eq_dec F1 ('Query[F0])) as [->|H1].
  - assert (H2 : F2 <> 'Query['Query[F0]]) by tauto.
    pose proof (equal1_neq ('Query['Query[F0]]) F2 ltac:(congruence)).
    unfold query_handler; cbn; qrun.
  - pose proof (equal1_neq ('Query[F0]) F1 ltac:(congruence)).
    destruct (combination_eq_dec F2 ('Query[F1])) as [->|H2].
    + unfold query_handler; cbn; qrun.
    + pose proof (equal1_neq ('Query[F1]) F2 ltac:(congruence)).
      unfold query_handler; cbn; qrun.
Qed.

Definition query_handler_fn F0 F1 F2 :=
  if (ceqb F1 ('Query[F0]) && ceqb F2 ('Query['Query[F0]]))%bool
  then Sm (query_one_level F0) else Lf.

Lemma query_handler_spec : forall F0 F1 F2 U,
  query_handler @ F0 @r F1 @r F2 @r U ==> query_handler_fn F0 F1 F2.
Proof.
  intros F0 F1 F2 U; unfold query_handler_fn.
  destruct (combination_eq_dec F1 ('Query[F0])) as [->|H1];
    [destruct (combination_eq_dec F2 ('Query['Query[F0]])) as [->|H2]|].
  - rewrite !ceqb_refl; apply query_handler_eval.
  - rewrite ceqb_refl, (ceqb_false _ _ H2); cbn; apply query_handler_miss; right; exact H2.
  - rewrite (ceqb_false _ _ H1); cbn; apply query_handler_miss; left; exact H1.
Qed.

Definition query_triage_fn C :=
  match C with
  | Fk (Fk F0 F1) F2 =>
      match query_handler_fn F0 F1 F2 with Sm _ => Sm F0 | _ => Lf end
  | _ => Lf
  end.

Local Opaque query_handler.
Lemma query_triage_case_eval : forall C,
  query_triage_case @ C ==> query_triage_fn C.
Proof.
  intros C; destruct C as [|x|l F2];
    [unfold query_triage_case; cbn; evaluate|unfold query_triage_case; cbn; evaluate|].
  destruct l as [|a|F0 F1]; [unfold query_triage_case; cbn; evaluate|unfold query_triage_case; cbn; evaluate|].
  pose proof (query_handler_spec F0 F1 F2 Lf) as HH.
  unfold query_triage_fn; unfold query_handler_fn in *.
  destruct (_ && _)%bool;
    repeat match goal with H : Fk (Fk _ _) _ ==> _ |- _ => inv_out H end;
    unfold query_triage_case; qrun.
Qed.
Local Transparent query_handler.

(** The concrete retagger used to guard recursive query occurrences. *)
(** It builds its label at run time. *)
Definition tagged_query_package :
  { t : Combination | t = 'tagger[query_nm] } := exist _ _ eq_refl.

Definition tagged_query : Combination :=
  Eval cbn in proj1_sig tagged_query_package.

Definition fix_query (f : Combination) : Combination :=
  'tagged[Z (f 'C tagged_query), query_nm].

(** Recognize a composition whose right operand is [tagged_query]. *)
Definition get_tagged_query_check_package :
  { t : Combination |
    to_tree
      (star "D" (star "R"
        (Val equal @@ Ref "R" @@ Val tagged_query
          @@ (Val Lf @@ Ref "D") @@ Val Lf))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition get_tagged_query_check :=
  Eval cbn -[equal] in proj1_sig get_tagged_query_check_package.

Definition get_tagged_query := Fk ('K1 ('K1 Lf)) get_tagged_query_check.

Lemma get_tagged_query_inv : forall X D,
  get_tagged_query @ X ==> Sm D -> X = Fk D tagged_query.
Proof.
  intros X D H.
  destruct X as [|X|left right];
    unfold get_tagged_query, get_tagged_query_check in H; cbn in H;
    invert_eval.
  assert (Hequal : equal @ right @r tagged_query ==> v0)
    by (eapply eval_appl; eauto).
  destruct (equal_spec _ _ _ Hequal)
    as [[-> Heq] | [-> Hneq]].
  - subst right; invert_eval.
  - invert_eval.
Qed.

Definition get_tagged_query_composition :=
  ('onStem1 get_tagged_query) 'C get_composition.

Lemma get_tagged_query_composition_some : forall D,
  get_tagged_query_composition @ (D 'C tagged_query) ==> Sm D.
Proof.
  intros D; unfold get_tagged_query_composition,
    get_tagged_query, get_tagged_query_check; cbn.
  repeat first
    [ eapply get_composition_some | eapply equal_eval | eapply equal1_eq
    | progress evaluate ].
Qed.

Lemma get_tagged_query_composition_inv : forall X D,
  get_tagged_query_composition @ X ==> Sm D ->
  X = D 'C tagged_query.
Proof.
  intros X D H; unfold get_tagged_query_composition in H; invert_eval.
  apply get_tagged_query_inv in H5; subst v0.
  apply get_composition_inv in H4; exact H4.
Qed.


Lemma query_K_case_some : forall B,
  query_K_case @ ('K1 B) ==> Sm (Sm B).
Proof.
  intros B; unfold query_K_case, query_eliminator; cbn; evaluate.
Qed.

Lemma query_triage_case_some : forall B,
  query_triage_case @
    query_one_level B ==>
    Sm B.
Proof.
  intros B; pose proof (query_triage_case_eval (query_one_level B)) as H.
  unfold query_one_level in *; cbn [query_triage_fn] in H.
  unfold query_handler_fn in H; rewrite !ceqb_refl in H; exact H.
Qed.
Lemma query_K_case_inv : forall C E,
  query_K_case @ C ==> Sm (Sm E) ->
  exists B, C = 'K1 B /\ E = B.
Proof.
  intros C E H; unfold query_K_case, query_eliminator in H; cbn in H.
  invert_eval; eauto.
Qed.

Lemma get_query_inv : forall X B,
  get_query @ X ==> Sm B -> X = 'Query[B].
Proof.
  intros X B H.
  unfold get_query, get_query_fields,
    get_query_name in H; cbn in H.
  invert_eval.
  match goal with Ht : get_tagged @ X ==> _ |- _ =>
    destruct (get_tagged_success_inv _ _ Ht) as [E [N [HX HP]]]; clear Ht end.
  inversion HP; subst; clear HP.
  match goal with Hq : get_query_eliminator @ _ ==> Sm B |- _ =>
    apply get_query_eliminator_inv in Hq; subst; reflexivity end.
Qed.


Lemma query_triage_case_inv : forall C E,
  query_triage_case @ C ==> Sm E ->
  exists B,
    C = query_one_level B /\
    E = B.
Proof.
  intros C E H; pose proof (eval_deterministic _ _ H _ (query_triage_case_eval C)) as Heq.
  destruct C as [|x|[|a|F0 F1] F2]; cbn in Heq; try discriminate.
  unfold query_handler_fn in Heq.
  destruct (ceqb F1 _) eqn:H1; destruct (ceqb F2 _) eqn:H2; cbn in Heq; try discriminate.
  apply ceqb_true in H1; apply ceqb_true in H2; subst; inversion Heq; subst.
  exists F0; split; reflexivity.
Qed.


Lemma query_eliminator_inv : forall B a X U,
  query_eliminator B @ a @r X ==> Sm U -> U = B.
Proof.
  intros B a X U H; unfold query_eliminator, query_elim in H.
  apply ignores_wait_inv in H; unfold query_elim0 in H; invert_eval.
Qed.
(** The abstractor takes type application.  It is in the shape of
    [function_abstractor]: [abstractor_intro core] waits for type application [a]
    and then for the carrier [C], and runs [core @ C @ a].  A clause of [core]
    maps [C] to [Sm k] when the shape of [C] is its own, and to [Lf]
    otherwise; [k @ a] gives [Sm E], for the eliminator [E], or refuses. *)
Definition abstractor_intro (core : Combination) := Eval cbn in
  to_tree (star "a" (star "C" (Val core @@ Ref "C" @@ Ref "a"))).

Lemma abstractor_intro_partial : forall core a,
  abstractor_intro core @ a ==> 'S2[core, 'K1 a].
Proof. intros; unfold abstractor_intro; evaluate. Qed.

Lemma abstractor_at_eval : forall core a C v,
  core @ C @r a ==> v -> ('S2[core, 'K1 a]) @ C ==> v.
Proof.
  intros core a C v H; destruct (eval_pair_inv _ _ _ H) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  repeat first [eassumption | progress evaluate].
Qed.

Lemma abstractor_at_eval_inv : forall core a C v,
  ('S2[core, 'K1 a]) @ C ==> v -> core @ C @r a ==> v.
Proof. intros core a C v H; invert_eval; eapply eval_appl; eassumption. Qed.

Lemma abstractor_intro_eval : forall core a C v,
  core @ C @r a ==> v -> abstractor_intro core @ a @r C ==> v.
Proof.
  intros core a C v H; eapply eval_appl;
    [apply abstractor_intro_partial|apply abstractor_at_eval; exact H].
Qed.

Lemma clause_hit : forall p d C k a v,
  p @ C ==> Sm k -> k @ a ==> v -> extend p d @ C @r a ==> v.
Proof. intros; eapply eval_appl; [apply extend_some; eassumption|assumption]. Qed.

Lemma clause_inv : forall p d C a E,
  (forall l r, p @ C ==> Fk l r -> False) ->
  extend p d @ C @r a ==> Sm E ->
  (exists k, p @ C ==> Sm k /\ k @ a ==> Sm E) \/
  (p @ C ==> Lf /\ d @ C @r a ==> Sm E).
Proof.
  intros p d C a E Hf H.
  destruct (eval_pair_inv _ _ _ H) as [W [c [HW [Hc Ha]]]]; inv_out Hc.
  destruct (extend_inv _ _ _ _ HW) as [[k [Hk ->]]|[[HL Hd]|[l [r [Hl _]]]]].
  - left; eauto.
  - right; split; [exact HL|eapply eval_appl; eassumption].
  - exfalso; eapply Hf; exact Hl.
Qed.

Lemma refusal_inv : forall C a E, refusal @ C @r a ==> Sm E -> False.
Proof. intros; unfold refusal in *; invert_eval. Qed.

(** A clause that needs no type application answers a constant
    continuation. *)
Definition query_found := Eval cbv -[query_elim] in to_tree
  (star "B" (Val Lf @@ ''wait[Val query_elim, Ref "B"])).
Definition query_answer := Eval cbv -[query_elim] in to_tree
  (star "B" (Val Lf @@ ''K1 (Val Lf @@ ''wait[Val query_elim, Ref "B"]))).
Definition closed1 p := ('onStem1 query_answer) 'C p.
Definition closed2 p := ('onStem1 ('onStem1 query_answer)) 'C p.

Lemma query_found_eval : forall B, query_found @ B ==> Sm (query_eliminator B).
Proof. intros; unfold query_found, query_eliminator; evaluate. Qed.
Lemma query_found_inv : forall B E, query_found @ B ==> Sm E -> E = query_eliminator B.
Proof. intros B E H; pose proof (eval_deterministic _ _ H _ (query_found_eval B)) as HE; inversion HE; reflexivity. Qed.
Lemma query_answer_eval : forall B, query_answer @ B ==> Sm ('K1 (Sm (query_eliminator B))).
Proof. intros; unfold query_answer, query_eliminator; evaluate. Qed.
Lemma query_answer_inv : forall B k, query_answer @ B ==> Sm k -> k = 'K1 (Sm (query_eliminator B)).
Proof. intros B k H; pose proof (eval_deterministic _ _ H _ (query_answer_eval B)) as HE; inversion HE; reflexivity. Qed.
Opaque query_answer query_found.

Lemma closed1_hit : forall p C B a,
  p @ C ==> Sm B -> exists k, closed1 p @ C ==> Sm k /\ k @ a ==> Sm (query_eliminator B).
Proof.
  intros p C B a H; pose proof (query_answer_eval B).
  eexists; split; [unfold closed1; evaluate|evaluate].
Qed.
Lemma closed1_miss : forall p C, p @ C ==> Lf -> closed1 p @ C ==> Lf.
Proof. intros; unfold closed1; evaluate. Qed.
Lemma closed1_inv : forall p C k a E,
  closed1 p @ C ==> Sm k -> k @ a ==> Sm E ->
  exists B, p @ C ==> Sm B /\ E = query_eliminator B.
Proof.
  intros p C k a E H Ha; unfold closed1 in H; invert_eval.
  match goal with Hq : query_answer @ ?B ==> Sm _ |- _ =>
    apply query_answer_inv in Hq; subst; invert_eval; eauto end.
Qed.
Lemma closed1_never_fork : forall p C l r, closed1 p @ C ==> Fk l r -> False.
Proof.
  intros p C l r H; unfold closed1 in H; invert_eval.
  match goal with Hq : query_answer @ ?B ==> _ |- _ =>
    pose proof (eval_deterministic _ _ Hq _ (query_answer_eval B)); discriminate end.
Qed.
Lemma closed2_hit : forall p C B a,
  p @ C ==> Sm (Sm B) -> exists k, closed2 p @ C ==> Sm k /\ k @ a ==> Sm (query_eliminator B).
Proof.
  intros p C B a H; pose proof (query_answer_eval B).
  eexists; split; [unfold closed2; evaluate|evaluate].
Qed.
Lemma closed2_miss : forall p C, p @ C ==> Lf -> closed2 p @ C ==> Lf.
Proof. intros; unfold closed2; evaluate. Qed.
Lemma closed2_inv : forall p C k a E,
  closed2 p @ C ==> Sm k -> k @ a ==> Sm E ->
  exists B, p @ C ==> Sm (Sm B) /\ E = query_eliminator B.
Proof.
  intros p C k a E H Ha; unfold closed2 in H; invert_eval.
  match goal with Hq : query_answer @ ?B ==> Sm _ |- _ =>
    apply query_answer_inv in Hq; subst; invert_eval; eauto end.
Qed.
Lemma closed2_never_fork : forall p C l r, closed2 p @ C ==> Fk l r -> False.
Proof.
  intros p C l r H; unfold closed2 in H; invert_eval.
  match goal with Hq : query_answer @ ?B ==> _ |- _ =>
    pose proof (eval_deterministic _ _ Hq _ (query_answer_eval B)); discriminate end.
Qed.

(** Applicative combination runs the type of the first query at the type
    of the second. *)
Local Transparent get_query get_S_fields.
Definition query_S_case := Eval cbn -[equal query_found] in to_tree
  (star "C"
    (''onStem1 (''onFork1 (star "G" (star "Q"
      (''onStem1 (star "F"
        (''onStem1 (star "V"
          (Val Lf @@ (star "a"
            (''onStem1 (Val query_found) @@ (Ref "a" @@ Ref "F" @@ Ref "V")))))
          @@ (Val get_query @@ Ref "Q")))
        @@ (Val get_query @@ Ref "G")))))
      @@ (Val get_S_fields @@ Ref "C"))).

Local Opaque get_query get_S_fields.
Lemma query_S_case_some : forall a F V B,
  a @ F @r V ==> Sm B ->
  exists k, query_S_case @ ('S2['Query[F],'Query[V]]) ==> Sm k /\
    k @ a ==> Sm (query_eliminator B).
Proof.
  intros a F V B HA.
  pose proof (get_S_fields_some ('Query[F]) ('Query[V])).
  pose proof (get_query_some F).
  pose proof (get_query_some V).
  pose proof (query_found_eval B).
  destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold query_S_case.
  Local Transparent get_query get_S_fields.
  fold get_query get_S_fields.
  Local Opaque get_query get_S_fields.
  cbn; eexists; split; evaluate.
Qed.

Lemma query_S_case_inv : forall C k a E,
  query_S_case @ C ==> Sm k -> k @ a ==> Sm E ->
  exists F V B, C = 'S2['Query[F],'Query[V]] /\ a @ F @r V ==> Sm B /\
    E = query_eliminator B.
Proof.
  intros C k a E H Ha; unfold query_S_case in H.
  Local Transparent get_query get_S_fields.
  fold get_query get_S_fields in H.
  Local Opaque get_query get_S_fields.
  cbn in H; invert_eval.
  repeat match goal with
  | Hget : get_query @ _ ==> Sm _ |- _ => apply get_query_inv in Hget; subst
  | Hget : get_S_fields @ _ ==> Sm (Fk _ _) |- _ => apply get_S_fields_inv in Hget; subst
  end.
  repeat eexists; [eapply eval_appl; eassumption|].
  apply query_found_inv; assumption.
Qed.

Lemma query_S_case_never_fork : forall C l r, query_S_case @ C ==> Fk l r -> False.
Proof. intros C l r H; unfold query_S_case in H; cbn in H; invert_eval. Qed.

(** Registered selection checks its name and payload domain independently
    of its action. The remaining check is the arrow [W --> B]. *)
Local Opaque equal equal1 is_concrete get_wrap_payload_type.
Local Ltac selection_eval :=
  first [eassumption |
    match goal with |- ('I @ ?x) @r ?y ==> _ => eapply eval_appl; [apply I_eval | selection_eval] end |
    (apply wait_eval; selection_eval) | apply equal_eval | apply equal1_eq |
    evaluate_expr_core selection_eval selection_head | idtac]
with selection_head := first [eassumption |
    match goal with |- ('I @ ?x) @r ?y ==> _ => eapply eval_appl; [apply I_eval | selection_eval] end |
    (apply wait_eval; selection_eval) | apply equal_eval | apply equal1_eq |
    evaluate_head_core selection_eval | idtac].
Definition query_diagonal_fields := Eval cbv -[get_query equal1] in to_tree
  (star "G" (star "F"
    (Val (equal1 'I) @@ Ref "F"
      @@ (''onStem1
        ((''onStem1 (star "B"
          (Val Lf @@ (Val Lf @@ Ref "B"))))
          ''C Val get_query))
      @@ Val ('K1 Lf) @@ (Val get_query @@ Ref "G")))).
Definition query_diagonal_case :=
  ('onStem1 ('onFork1 query_diagonal_fields)) 'C get_S_fields.
Lemma query_diagonal_fields_some : forall B,
  query_diagonal_fields @ ('Query['Query[B]]) @r ('I) ==>
    Sm (Sm B).
Proof.
  intros; unfold query_diagonal_fields, query_eliminator;
    repeat first [apply get_query_some | apply equal1_eq | progress evaluate].
Qed.
Lemma query_diagonal_fields_inv : forall G F E,
  query_diagonal_fields @ G @r F ==> Sm E ->
  exists B, G = 'Query['Query[B]] /\ F = 'I /\ E = Sm B.
Proof.
  intros G F E H; unfold query_diagonal_fields in H; invert_eval.
  repeat progress eqtac.
  repeat match goal with
  | Hq : get_query @ _ ==> Sm _ |- _ => apply get_query_inv in Hq; subst
  end.
  eexists; repeat split; reflexivity.
Qed.
Lemma query_diagonal_case_some : forall B,
  query_diagonal_case @ ('S2['Query['Query[B]],'I]) ==>
    Sm (Sm B).
Proof.
  intros; pose proof (query_diagonal_fields_some B) as HF; inv_out HF.
  unfold query_diagonal_case;
    repeat first [apply get_S_fields_some | progress evaluate].
Qed.
Lemma query_diagonal_case_inv : forall C E,
  query_diagonal_case @ C ==> Sm E ->
  exists B, C = 'S2['Query['Query[B]],'I] /\ E = Sm B.
Proof.
  intros C E H; unfold query_diagonal_case in H; invert_eval.
  assert (HF : query_diagonal_fields @ v21 @r v22 ==> Sm E)
    by (eapply eval_appl; eauto).
  apply query_diagonal_fields_inv in HF; destruct HF as [B [-> [-> ->]]].
  apply get_S_fields_inv in H4; exists B; auto.
Qed.
Lemma query_diagonal_application : forall AI B U,
  type_app AI @ ('S2['Query['Query[B]],'I]) @r U ==> Sm B.
Proof.
  intros; new_S; [discriminate| |apply type_app_I|].
  - apply type_app_abstract; apply query_eliminator_eval.
  - apply type_app_abstract; apply query_eliminator_eval.
Qed.

Lemma query_diagonal_case_never_fork : forall C l r,
  query_diagonal_case @ C ==> Fk l r -> False.
Proof.
  intros C l r H; unfold query_diagonal_case in H; invert_eval.
  match goal with Hf : query_diagonal_fields @ _ ==> _ |- _ =>
    unfold query_diagonal_fields in Hf end.
  invert_eval; repeat progress eqtac.
Qed.
Definition diagonal_query q := 'tagged['S2[q,'I],query_nm].

(** The recursive carrier holds the type [F] of the body and a type
    [G = Query[B]], in the decoration of the body, so that unfolding the
    fixed point keeps both.  Its check is the application [F # G ==> Sm G]. *)
Definition get_fix_fields :=
  ('onStem1 get_decorate) 'C (('onStem1 get_tagged_query_composition) 'C get_Z).

Lemma get_fix_fields_some : forall F G,
  get_fix_fields @ Z ('decorate[F,G] 'C tagged_query) ==> Sm (Fk F G).
Proof.
  intros F G; unfold get_fix_fields; repeat first
    [ apply get_decorate_some | apply get_Z_some
    | apply get_tagged_query_composition_some | progress evaluate ].
Qed.

Lemma get_fix_fields_inv : forall X F G,
  get_fix_fields @ X ==> Sm (Fk F G) -> X = Z ('decorate[F,G] 'C tagged_query).
Proof.
  intros X F G H; unfold get_fix_fields in H; invert_eval.
  match goal with Hd : get_decorate @ ?T ==> Sm (Fk F G) |- _ =>
    apply get_decorate_inv in Hd; subst T end.
  match goal with Hc : get_tagged_query_composition @ ?T ==> Sm _ |- _ =>
    apply get_tagged_query_composition_inv in Hc; subst T end.
  match goal with Hz : get_Z @ X ==> Sm _ |- _ =>
    apply get_Z_inv in Hz; exact Hz end.
Qed.

Local Transparent get_query.
Definition query_fix_case := Eval cbn -[equal get_fix_fields query_found] in to_tree
  (star "C"
    (''onStem1 (''onFork1 (star "F" (star "G"
      (''onStem1 (star "B"
        (Val Lf @@ (star "a"
          (Val equal @@ (Ref "a" @@ Ref "F" @@ Ref "G") @@ (Val Lf @@ Ref "G")
            @@ (Val query_found @@ Ref "B") @@ Val Lf))))
        @@ (Val get_query @@ Ref "G")))))
      @@ (Val get_fix_fields @@ Ref "C"))).
Local Opaque get_query get_fix_fields.

Lemma query_fix_case_some : forall a F B,
  a @ F @r ('Query[B]) ==> Sm ('Query[B]) ->
  exists k, query_fix_case @ Z ('decorate[F,'Query[B]] 'C tagged_query) ==> Sm k /\
    k @ a ==> Sm (query_eliminator B).
Proof.
  intros a F B HA.
  pose proof (get_fix_fields_some F ('Query[B])).
  pose proof (get_query_some B).
  pose proof (query_found_eval B).
  pose proof (equal_eval (Sm ('Query[B]))).
  pose proof (equal1_eq (Sm ('Query[B]))).
  destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold query_fix_case.
  Local Transparent get_query.
  fold get_query.
  Local Opaque get_query.
  cbn; eexists; split; evaluate.
Qed.

Lemma query_fix_case_inv : forall C k a E,
  query_fix_case @ C ==> Sm k -> k @ a ==> Sm E ->
  exists F B, C = Z ('decorate[F,'Query[B]] 'C tagged_query) /\
    a @ F @r ('Query[B]) ==> Sm ('Query[B]) /\ E = query_eliminator B.
Proof.
  intros C k a E H Ha; unfold query_fix_case in H.
  Local Transparent get_query.
  fold get_query in H.
  Local Opaque get_query.
  cbn in H; invert_eval.
  match goal with Hq : get_query @ ?G ==> Sm ?B |- _ =>
    apply get_query_inv in Hq; subst G end.
  match goal with Hg : get_fix_fields @ C ==> Sm (Fk _ _) |- _ =>
    apply get_fix_fields_inv in Hg; subst C end.
  match goal with
  | H1 : equal @ ?D ==> ?e, H2 : ?e @ ?U ==> ?b |- _ =>
    assert (HE : equal @ D @r U ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ HE) as [[HB HU]|[HB HU]];
    subst b; invert_eval
  end.
  repeat eexists; [eapply eval_appl; eassumption|].
  apply query_found_inv; assumption.
Qed.

Lemma query_fix_case_none : forall C,
  get_fix_fields @ C ==> Lf -> query_fix_case @ C ==> Lf.
Proof. intros C H; unfold query_fix_case; cbn; evaluate. Qed.

Lemma query_fix_case_never_fork : forall C l r, query_fix_case @ C ==> Fk l r -> False.
Proof. intros C l r H; unfold query_fix_case in H; cbn in H; invert_eval. Qed.

(** Miss lemmas for the trial chain. *)
Lemma get_query_none : forall X,
  (forall C N, X <> 'tagged[C,N]) -> get_query @ X ==> Lf.
Proof.
  Local Transparent get_query.
  intros X H; pose proof (get_tagged_none X H); unfold get_query; evaluate.
  Local Opaque get_query.
Qed.
Lemma query_K_case_S2_none : forall G F,
  query_K_case @ ('S2[G,F]) ==> Lf.
Proof. intros; unfold query_K_case; cbn; evaluate. Qed.
Lemma query_triage_case_S2_none : forall G F,
  query_triage_case @ ('S2[G,F]) ==> Lf.
Proof. intros; unfold query_triage_case; cbn; evaluate. Qed.
Lemma get_query_I_none : get_query @ ('I) ==> Lf.
Proof. apply get_query_none; intros C N Heq; discriminate Heq. Qed.
Lemma query_S_case_query_none : forall G F VF,
  get_query @ G ==> Lf -> get_query @ F ==> VF ->
  query_S_case @ ('S2[G,F]) ==> Lf.
Proof.
  intros G F VF HG HF; pose proof (get_S_fields_some G F).
  unfold query_S_case.
  Local Transparent get_query get_S_fields.
  fold get_query get_S_fields.
  Local Opaque get_query get_S_fields.
  cbn; evaluate.
Qed.
Lemma query_diagonal_case_query_none : forall G,
  get_query @ G ==> Lf -> query_diagonal_case @ ('S2[G,'I]) ==> Lf.
Proof.
  intros G HG; pose proof (get_S_fields_some G ('I)).
  unfold query_diagonal_case, query_diagonal_fields;
    repeat first [apply equal1_eq | apply equal1_neq | progress evaluate].
Qed.
Lemma query_S_case_right_none : forall G B F,
  get_query @ G ==> Sm B -> get_query @ F ==> Lf ->
  query_S_case @ ('S2[G,F]) ==> Lf.
Proof.
  intros G B F HG HF; pose proof (get_S_fields_some G F).
  unfold query_S_case.
  Local Transparent get_query get_S_fields.
  fold get_query get_S_fields.
  Local Opaque get_query get_S_fields.
  cbn; evaluate.
Qed.

Set Default Proof Using "Type".
Local Opaque equal equal1 get_tagname get_IfNamed get_query get_wrap_payload_type is_concrete.
Local Ltac run := first [eassumption | apply equal_eval | apply equal1_eq |
  evaluate_expr_core run run_head | idtac]
with run_head := first [eassumption | apply equal_eval | apply equal1_eq |
  evaluate_head_core run | idtac].
(** Wrapper lookup and the application of the action's type to the wrapper
    type suffice. Lookup itself refuses fun_nm, so no separate test against
    fun_nm is needed. *)
Definition choice_constructor AI := Eval lazy -[get_IfNamed query_elim] in
 to_tree
  (star "C"
    (''onStem1 (''onFork1 (star "N" (star "FD"
      ((''onFork1 (star "F" (star "D"
        (''onStem1 (star "B"
          (Val Lf @@ (star "a"
            (Val is_concrete @@ Ref "N"
              @@ (''onStem1 (star "T"
                  (Val equal @@ (Val Lf @@ Ref "B")
                    @@ (Ref "a" @@ Ref "F" @@ ''tagged[payload_eliminator2 (Ref "T"),Ref "N"])
                    @@ (Val Lf @@ ''wait[Val query_elim, Ref "B"]) @@ Val Lf))
                  @@ (Val (get_wrap_payload_type AI) @@ Ref "N"))
              @@ Val Lf))))
          @@ (Val get_query @@ Ref "D")))))
       @@ Ref "FD"))))
      @@ (Val get_IfNamed @@ Ref "C"))).

Lemma choice_constructor_some : forall AI N T F B a,
  concrete N -> declared_wrapper AI N T ->
  a @ F @r wrap_type T N ==> Sm B ->
  exists k, choice_constructor AI @ IfNamed N F ('Query[B]) ==> Sm k /\
    k @ a ==> Sm (query_eliminator B).
Proof.
  intros AI N T F B a HN HI HA.
  pose proof (get_IfNamed_some N F ('Query[B])).
  pose proof (get_query_some B).
  pose proof (proj2 (is_concrete_true N) HN).
  pose proof (get_wrap_payload_type_some AI N T HI).
  pose proof (equal1_eq (Sm B)).
  destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold choice_constructor, query_eliminator.
  unfold wrap_type, wrap_eliminator in *.
  eexists; split; run.
Qed.

Lemma choice_constructor_inv : forall AI C k a E,
  choice_constructor AI @ C ==> Sm k -> k @ a ==> Sm E ->
  exists N T F B,
    C = IfNamed N F ('Query[B]) /\
    concrete N /\ declared_wrapper AI N T /\
    a @ F @r wrap_type T N ==> Sm B /\
    E = query_eliminator B.
Proof.
  intros AI C k a E H Ha; unfold choice_constructor in H; cbn in H; invert_eval.
  all: repeat progress recognizer_eqtac.
  all: match goal with Hc : is_concrete @ ?N ==> ?b |- _ =>
    pose proof (is_concrete_spec N) as HC;
    pose proof (eval_deterministic _ _ Hc _ HC) as HB;
    destruct (concreteb N) eqn:HN; cbn in HB; subst b; invert_eval end.
  all: repeat progress recognizer_eqtac.
  all: repeat match goal with
  | H : get_query @ ?D ==> Sm ?B |- _ => apply get_query_inv in H; subst D
  | H : get_IfNamed @ ?S ==> Sm (Fk ?N (Fk ?F ?D)) |- _ => apply get_IfNamed_inv in H; subst S
  | H : get_wrap_payload_type ?AI @ ?N ==> Sm ?T |- _ =>
      apply get_wrap_payload_type_inv in H
  end.
  all: repeat eexists; first [eassumption|apply concreteb_sound; eassumption|
    match goal with HW : declared_wrapper _ _ _ |- _ =>
      first [exact (proj1 HW)|exact (proj2 HW)] end|
    (eapply eval_appl; eassumption)].
Qed.

Lemma choice_constructor_never_fork : forall AI C l r,
  choice_constructor AI @ C ==> Fk l r -> False.
Proof. intros AI C l r H; unfold choice_constructor in H; cbn in H; invert_eval. Qed.

Lemma choice_constructor_none : forall AI C,
  get_IfNamed @ C ==> Lf -> choice_constructor AI @ C ==> Lf.
Proof. intros AI C HG; unfold choice_constructor; evaluate. Qed.

(** Soundness of the choice carrier holds for every inhabited U (an
    inhabited type tagged at N is the declared wrapper type). *)
Lemma choice_constructor_application : forall AI N T F B U,
  concrete N -> declared_wrapper AI N T -> inhabited AI U ->
  app AI @ F @r wrap_type T N ==> Sm B ->
  app AI @ IfNamed N F ('Query[B]) @r U ==> Sm B.
Proof.
  intros AI N T F B U HN HI HU HF; eapply installed_if_named; try eassumption.
  - eapply inhabited_not_impostor; eassumption.
  - apply app_abstract; apply query_eliminator_eval.
Qed.

Set Default Proof Using "Type".
Local Opaque equal equal1 get_tagname get_IfNamed get_query.
(** Trial order follows the paper: K, triage, S, diagonal, recursive,
    choice. *)
Definition query_fix_rest AI :=
  extend query_fix_case
    (extend (choice_constructor AI) refusal).
Definition query_rest AI :=
  extend query_S_case (extend (closed2 query_diagonal_case) (query_fix_rest AI)).
Definition query_core AI :=
  extend (closed2 query_K_case) (extend (closed1 query_triage_case) (query_rest AI)).

(** The row of Query: [query_abstractor AI] takes type application. *)
Definition query_abstractor AI := abstractor_intro (query_core AI).
(** The abstractor at type application of [AI]. *)
Definition query_abstractor_at AI := 'S2[query_core AI, 'K1 (type_app AI)].
Definition supports_queries AI := AI @ query_nm ==> query_abstractor AI.

Lemma query_abstractor_partial : forall AI, query_abstractor AI @ type_app AI ==> query_abstractor_at AI.
Proof. intros; apply abstractor_intro_partial. Qed.

Lemma query_abstractor_core : forall AI C v,
  query_core AI @ C @r type_app AI ==> v -> query_abstractor_at AI @ C ==> v.
Proof. intros; apply abstractor_at_eval; assumption. Qed.

(** The clauses at their carriers. *)
Lemma query_core_S2 : forall AI G F a v,
  query_rest AI @ 'S2[G,F] @r a ==> v -> query_core AI @ 'S2[G,F] @r a ==> v.
Proof.
  intros AI G F a v H; unfold query_core.
  apply extend_none; [apply closed2_miss; apply query_K_case_S2_none|].
  apply extend_none; [apply closed1_miss; apply query_triage_case_S2_none|exact H].
Qed.
Lemma query_rest_I : forall AI G a v,
  get_query @ G ==> Lf -> query_fix_rest AI @ 'S2[G,'I] @r a ==> v ->
  query_rest AI @ 'S2[G,'I] @r a ==> v.
Proof.
  intros AI G a v HG H; unfold query_rest.
  apply extend_none; [eapply query_S_case_query_none; [exact HG|apply get_query_I_none]|].
  apply extend_none; [apply closed2_miss; apply query_diagonal_case_query_none; exact HG|exact H].
Qed.

Lemma query_abstractor_K : forall AI B,
  (query_abstractor_at AI) @ ('K1 B) ==> Sm (query_eliminator B).
Proof.
  intros AI B; apply query_abstractor_core; unfold query_core.
  destruct (closed2_hit query_K_case ('K1 B) B (type_app AI) (query_K_case_some B)) as [k [H1 H2]].
  eapply clause_hit; eassumption.
Qed.
Lemma query_abstractor_triage : forall AI B,
  (query_abstractor_at AI) @ query_one_level B ==>
    Sm (query_eliminator B).
Proof.
  intros AI B; apply query_abstractor_core; unfold query_core, query_one_level.
  apply extend_none; [apply closed2_miss; unfold query_K_case; cbn; evaluate|].
  destruct (closed1_hit query_triage_case _ B (type_app AI) (query_triage_case_some B)) as [k [H1 H2]].
  eapply clause_hit; eassumption.
Qed.
Lemma query_abstractor_S : forall AI F V B,
  type_app AI @ F @r V ==> Sm B ->
  (query_abstractor_at AI) @ ('S2['Query[F],'Query[V]]) ==>
    Sm (query_eliminator B).
Proof.
  intros AI F V B HA; apply query_abstractor_core; apply query_core_S2.
  destruct (query_S_case_some _ _ _ _ HA) as [k [H1 H2]].
  eapply clause_hit; eassumption.
Qed.
Lemma query_abstractor_diagonal : forall AI B,
  (query_abstractor_at AI) @ ('S2['Query['Query[B]],'I]) ==>
    Sm (query_eliminator B).
Proof.
  intros AI B; apply query_abstractor_core; apply query_core_S2; unfold query_rest.
  apply extend_none;
    [eapply query_S_case_right_none; [apply get_query_some|apply get_query_I_none]|].
  destruct (closed2_hit query_diagonal_case _ B (type_app AI) (query_diagonal_case_some B)) as [k [H1 H2]].
  eapply clause_hit; eassumption.
Qed.
Lemma query_abstractor_fix : forall AI F B,
  type_app AI @ F @r ('Query[B]) ==> Sm ('Query[B]) ->
  (query_abstractor_at AI) @ Z ('decorate[F,'Query[B]] 'C tagged_query) ==>
    Sm (query_eliminator B).
Proof.
  intros AI F B HA; apply query_abstractor_core; unfold Z; apply query_core_S2.
  apply query_rest_I; [apply get_query_none; intros C N Heq; discriminate Heq|].
  destruct (query_fix_case_some _ _ _ HA) as [k [H1 H2]].
  eapply clause_hit; eassumption.
Qed.
Lemma query_abstractor_choice_cases : forall AI N F B a v,
  query_fix_rest AI @ IfNamed N F ('Query[B]) @r a ==> v ->
  query_core AI @ IfNamed N F ('Query[B]) @r a ==> v.
Proof.
  intros AI N F B a v H; unfold IfNamed; apply query_core_S2.
  apply query_rest_I; [apply get_query_none; intros C M Heq; discriminate Heq|exact H].
Qed.
Lemma constructor_choice : forall AI N T F B,
  concrete N -> declared_wrapper AI N T ->
  type_app AI @ F @r wrap_type T N ==> Sm B ->
  query_abstractor_at AI @ IfNamed N F ('Query[B]) ==> Sm (query_eliminator B).
Proof.
  intros AI N T F B HN HI HF; apply query_abstractor_core.
  apply query_abstractor_choice_cases; unfold query_fix_rest.
  apply extend_none.
  - apply query_fix_case_none.
    Local Transparent get_fix_fields.
    unfold get_fix_fields.
    assert (HZ : get_Z @ IfNamed N F ('Query[B]) ==> Lf).
    { apply get_Z_none; intros f Heq; unfold IfNamed, Z in Heq; discriminate Heq. }
    evaluate.
  - destruct (choice_constructor_some AI N T F B (type_app AI) HN HI HF) as [k [H1 H2]].
    eapply clause_hit; eassumption.
Qed.

(** The carriers that the abstractor accepts. *)
Lemma query_abstractor_inv : forall AI C E,
  query_abstractor_at AI @ C ==> Sm E ->
  (exists B, C = 'K1 B /\ E = query_eliminator B) \/
  (exists B, C = query_one_level B /\ E = query_eliminator B) \/
  (exists F V B, C = 'S2['Query[F],'Query[V]] /\ type_app AI @ F @r V ==> Sm B /\
     E = query_eliminator B) \/
  (exists B, C = 'S2['Query['Query[B]],'I] /\ E = query_eliminator B) \/
  (exists F B, C = Z ('decorate[F,'Query[B]] 'C tagged_query) /\
     type_app AI @ F @r ('Query[B]) ==> Sm ('Query[B]) /\ E = query_eliminator B) \/
  (exists N T F B, C = IfNamed N F ('Query[B]) /\ concrete N /\ declared_wrapper AI N T /\
     type_app AI @ F @r wrap_type T N ==> Sm B /\ E = query_eliminator B).
Proof.
  intros AI C E H; apply abstractor_at_eval_inv in H; unfold query_core in H.
  destruct (clause_inv _ _ _ _ _ (closed2_never_fork _ _) H) as [[k [Hk Ha]]|[_ H1]].
  { destruct (closed2_inv _ _ _ _ _ Hk Ha) as [B [HK ->]].
    destruct (query_K_case_inv _ _ HK) as [B' [-> Hb]]; subst.
    left; eauto. }
  destruct (clause_inv _ _ _ _ _ (closed1_never_fork _ _) H1) as [[k [Hk Ha]]|[_ H2]].
  { destruct (closed1_inv _ _ _ _ _ Hk Ha) as [B [HK ->]].
    destruct (query_triage_case_inv _ _ HK) as [B' [-> Hb]]; subst.
    right; left; eauto. }
  unfold query_rest in H2.
  destruct (clause_inv _ _ _ _ _ (query_S_case_never_fork _) H2) as [[k [Hk Ha]]|[_ H3]].
  { do 2 right; left; eapply query_S_case_inv; eassumption. }
  destruct (clause_inv _ _ _ _ _ (closed2_never_fork _ _) H3) as [[k [Hk Ha]]|[_ H4]].
  { destruct (closed2_inv _ _ _ _ _ Hk Ha) as [B [HK ->]].
    destruct (query_diagonal_case_inv _ _ HK) as [B' [-> Hb]]; inversion Hb; subst.
    do 3 right; left; eauto. }
  unfold query_fix_rest in H4.
  destruct (clause_inv _ _ _ _ _ (query_fix_case_never_fork _) H4) as [[k [Hk Ha]]|[_ H5]].
  { do 4 right; left; eapply query_fix_case_inv; eassumption. }
  destruct (clause_inv _ _ _ _ _ (choice_constructor_never_fork _ _) H5) as [[k [Hk Ha]]|[_ H7]].
  { do 5 right; eapply choice_constructor_inv; eassumption. }
  exfalso; eapply refusal_inv; exact H7.
Qed.

Lemma query_abstractor_supported : forall AI C E,
  supports_queries AI -> (query_abstractor_at AI) @ C ==> Sm E ->
  AI @ query_nm @r type_app AI @r C ==> Sm E.
Proof.
  intros AI C E HS HC; eapply eval_appl.
  - eapply eval_appl; [exact HS|apply query_abstractor_partial].
  - exact HC.
Qed.

Lemma query_abstractor_applied : forall AI C v,
  supports_queries AI -> AI @ query_nm @r type_app AI @r C ==> v ->
  query_abstractor_at AI @ C ==> v.
Proof.
  intros AI C v HS H; destruct (declaration_apply_inv _ _ _ _ _ H) as [R [D [HR [HD Hv]]]].
  pose proof (eval_deterministic _ _ HR _ HS) as ->.
  pose proof (eval_deterministic _ _ HD _ (query_abstractor_partial AI)) as ->; exact Hv.
Qed.

Lemma app_tagged_query : forall AI C E,
  supports_queries AI -> query_abstractor_at AI @ C ==> Sm E ->
  app AI @ tagged_query @r C ==> Sm ('tagged[E,query_nm]).
Proof.
  intros AI C E HQ HC; unfold tagged_query.
  repeat first
    [ eapply app_S; [intros; discriminate|solve [reject_name]| | |]
    | apply app_K
    | apply app_stem; apply type_app_stem_structural; intros; discriminate
    | apply app_leaf ].
  apply app_stem; apply type_app_stem_tagged.
  apply query_abstractor_supported; assumption.
Qed.

(** Choice carriers are sound by typing at inhabited argument types;
    [choice_free C] excludes them. *)
Definition choice_free (C : Combination) : Prop :=
  forall N F D, C <> IfNamed N F D.

(** Every carrier other than a one-level query carrier and a choice
    carrier is sound by typing at every argument type (the one-level
    carrier is sound for values, [query_one_level_value_typing]). *)
Lemma query_abstractor_sound : forall AI C E X U,
  supports_queries AI -> (forall B', C <> query_one_level B') ->
  (choice_free C \/ inhabited AI X) ->
  (query_abstractor_at AI) @ C ==> Sm E -> E @ app AI @r X ==> Sm U ->
  type_app AI @ C @r X ==> Sm U.
Proof.
  intros AI C E U V HQ Hq Hc HC HE.
  destruct (query_abstractor_inv _ _ _ HC) as
    [[B [-> ->]]|[[B [-> ->]]|[[F [W [B [-> [HF ->]]]]]|[[B [-> ->]]|
     [[F [B [-> [HF ->]]]]|[N [T [F [B [-> [HN [HI [HF ->]]]]]]]]]]]]];
    apply query_eliminator_inv in HE; subst V.
  - apply app_K.
  - exfalso; exact (Hq B eq_refl).
  - eapply app_S; [intros; discriminate|solve [reject_name]| | |].
    + apply app_abstract; apply query_eliminator_eval.
    + apply app_abstract; apply query_eliminator_eval.
    + exact HF.
  - eapply app_S; [intros; discriminate|solve [reject_name]| |apply app_I|].
    + apply app_abstract; apply query_eliminator_eval.
    + apply app_abstract; apply query_eliminator_eval.
  - eapply app_Z.
    + eapply app_compose; [solve [reject_name]| | |]; [intros; discriminate| |].
      * eapply app_tagged_query; [exact HQ|exact HC].
      * eapply type_app_wait; [apply app_K|exact HF].
    + apply app_abstract; apply query_eliminator_eval.
  - destruct Hc as [Hc|HU]; [|apply choice_constructor_application with (T := T); assumption].
    exfalso; eapply Hc; reflexivity.
Qed.

Definition specialised_query N f d := 'tagged[if_named N f d,query_nm].
Lemma inf_specialised_query : forall AI N T f F d B,
  supports_queries AI -> supports_is_named AI -> concrete N -> declared_wrapper AI N T ->
  inf AI @ f ==> Sm F -> type_app AI @ F @r wrap_type T N ==> Sm B ->
  inf AI @ d ==> Sm ('Query[B]) ->
  inf AI @ specialised_query N f d ==> Sm ('Query[B]).
Proof.
  intros AI N T f F d B HQ HT HN HI Hf HF Hd.
  unfold specialised_query; eapply inf_tagged.
  - apply inf_if_named; [exact HN|exact HT|exact Hf|exact Hd].
  - apply inf_tag_free; reflexivity.
  - eapply query_abstractor_supported; [exact HQ|].
    eapply constructor_choice; eassumption.
Qed.


(** Whether a carrier is a one-level query carrier. *)
Lemma query_one_level_decide : forall C,
  (exists B, C = query_one_level B) \/ (forall B, C <> query_one_level B).
Proof.
  intros C.
  destruct (combination_eq_dec C (query_one_level
    (match C with Fk (Fk a _) _ => a | _ => Lf end))) as [H|H].
  - left; eexists; exact H.
  - right; intros B HB; apply H; rewrite HB; reflexivity.
Qed.

(** The Query family is sound for values: the one-level carrier by
    [query_one_level_value_typing], every other carrier because it is
    sound by typing. *)
Lemma query_abstractor_value_sound : forall AI,
  supports_queries AI -> sound_abstractor AI (query_abstractor_at AI).
Proof.
  intros AI HS n C E U V c v w HC HE Hc Hv He Ht.
  destruct (query_one_level_decide C) as [[B ->]|Hq].
  - pose proof (eval_deterministic _ _ HC _ (query_abstractor_triage AI B)) as HE';
      inversion HE'; subst E.
    apply query_eliminator_inv in HE; subst V.
    eapply query_one_level_value_typing; eassumption.
  - eapply carrier_value_typing; [|exact Hc|exact Hv|exact He|exact Ht].
    eapply query_abstractor_sound; [eassumption|eassumption|right; exists v; exact Hv|eassumption|eassumption].
Qed.

Definition query_case_package AI :
  { t : Combination |
    to_tree (tcase (Val query_nm) (Val (query_abstractor AI))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition query_case AI := Eval cbn in proj1_sig (query_case_package AI).

Local Lemma query_case_compilation : forall AI,
  to_tree (tcase (Val query_nm) (Val (query_abstractor AI))) = query_case AI.
Proof. intros; unfold query_case; exact (proj2_sig (query_case_package AI)). Qed.

Lemma query_case_some : forall AI,
  query_case AI @ query_nm ==> Sm (query_abstractor AI).
Proof. intros; rewrite <- query_case_compilation; apply tcase_eq. Qed.

Lemma query_case_none : forall AI N,
  N <> query_nm -> query_case AI @ N ==> Lf.
Proof.
  intros AI N Hneq; rewrite <- query_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.

Lemma query_case_never_fork : forall AI N left right,
  query_case AI @ N ==> Fk left right -> False.
Proof.
  intros AI N left right H.
  destruct (combination_eq_dec N query_nm) as [-> | Hneq].
  - pose proof (eval_deterministic _ _ H _ (query_case_some AI)); discriminate.
  - pose proof (eval_deterministic _ _ H _ (query_case_none AI N Hneq)); discriminate.
Qed.


(** ** Queries in declarations that support them *)


Set Default Proof Using "All".
Section QueryInference.

Variable AI : Combination.
Hypothesis AI_supports_queries : supports_queries AI.

Lemma infer_query_nm : infer AI @ query_nm ==> Sm query_nm.
Proof. unfold query_nm; eapply infer_tag_free; repeat constructor. Qed.

Lemma infer_Kq : forall b B,
  infer AI @ b ==> Sm B ->
  infer AI @ ('Kq b) ==> Sm ('Query[B]).
Proof.
  intros b B Hb.
  eapply infer_tagged.
  - eapply infer_K1; exact Hb.
  - apply infer_query_nm.
  - eapply query_abstractor_supported.
    + exact AI_supports_queries.
    + apply query_abstractor_K.
Qed.

Lemma infer_S_q : forall g f F V B,
  infer AI @ g ==> Sm ('Query[F]) ->
  infer AI @ f ==> Sm ('Query[V]) ->
  type_app AI @ F @r V ==> Sm B ->
  infer AI @ ('S_q[g,f]) ==> Sm ('Query[B]).
Proof.
  intros g f F V B Hg Hf HF.
  eapply infer_tagged.
  - eapply infer_fork.
    + eapply infer_stem; exact Hg.
    + exact Hf.
    + eapply type_app_stem_ev; eapply type_app_stem_structural;
        intros; discriminate.
  - apply infer_query_nm.
  - eapply query_abstractor_supported; [exact AI_supports_queries |].
    apply query_abstractor_S; exact HF.
Qed.


Lemma infer_tq : forall f0 f1 f2 B,
  infer AI @ 'triage[f0,f1,f2] ==>
    Sm (query_one_level B) ->
  infer AI @ ('tq[f0,f1,f2]) ==> Sm ('Query[B]).
Proof.
  intros f0 f1 f2 B Htriage.
  eapply infer_tagged.
  - exact Htriage.
  - apply infer_query_nm.
  - eapply query_abstractor_supported.
    + exact AI_supports_queries.
    + apply query_abstractor_triage.
Qed.

Lemma infer_fix_query : forall f F s B,
  infer AI @ f ==> Sm F ->
  infer AI @ s ==> Sm ('Query[B]) ->
  type_app AI @ F @r ('Query[B]) ==> Sm ('Query[B]) ->
  infer AI @ fix_query ('decorate[f,s]) ==> Sm ('Query[B]).
Proof.
  intros f F s B Hf Hs HF.
  assert (Htagged_query :
    infer AI @ tagged_query ==> Sm tagged_query).
  { eapply infer_tag_free.
    unfold tagged_query; repeat constructor; intros; discriminate. }
  assert (Hdecorate : infer AI @ 'decorate[f,s] ==> Sm ('decorate[F,'Query[B]]))
    by (apply infer_decorate; assumption).
  assert (Hcomposition :
    infer AI @ ('decorate[f,s] 'C tagged_query) ==>
      Sm ('decorate[F,'Query[B]] 'C tagged_query)).
  { infer_tac. }
  unfold fix_query.
  eapply infer_tagged.
  - eapply infer_Z; exact Hcomposition.
  - apply infer_query_nm.
  - eapply query_abstractor_supported.
    + exact AI_supports_queries.
    + apply query_abstractor_fix; exact HF.
Qed.


End QueryInference.

(** The triage condition of the triage query splits into three typings:
    the leaf, stem and fork cases have types [B], [Query[B]] and
    [Query[Query[B]]]. *)
Lemma infer_triage_intro : forall AI f0 f1 f2 B,
  infer AI @ f0 ==> Sm B ->
  infer AI @ f1 ==> Sm ('Query[B]) ->
  infer AI @ f2 ==> Sm ('Query['Query[B]]) ->
  infer AI @ 'triage[f0,f1,f2] ==> Sm (query_one_level B).
Proof.
  intros AI f0 f1 f2 B H0 H1 H2.
  unfold query_one_level.
  eapply infer_fork; [|exact H2|].
  - eapply infer_fork; [exact H0|exact H1|].
    eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
  - eapply type_app_stem_ev. eapply type_app_stem_structural; intros; discriminate.
Qed.

Lemma infer_tq_intro : forall AI f0 f1 f2 B,
  supports_queries AI ->
  infer AI @ f0 ==> Sm B ->
  infer AI @ f1 ==> Sm ('Query[B]) ->
  infer AI @ f2 ==> Sm ('Query['Query[B]]) ->
  infer AI @ ('tq[f0,f1,f2]) ==> Sm ('Query[B]).
Proof.
  intros; eapply infer_tq; [assumption|apply infer_triage_intro; assumption].
Qed.
Lemma infer_diagonal_query : forall AI q B,
  supports_queries AI -> infer AI @ q ==> Sm ('Query['Query[B]]) ->
  infer AI @ diagonal_query q ==> Sm ('Query[B]).
Proof.
  intros AI q B HQ Hq; unfold diagonal_query; eapply infer_tagged.
  - infer_tac.
  - apply infer_query_nm; exact HQ.
  - eapply query_abstractor_supported; [exact HQ|apply query_abstractor_diagonal].
Qed.
Lemma diagonal_query_eval : forall q u g v,
  q @ u ==> g -> g @ u ==> v -> diagonal_query q @ u ==> v.
Proof. intros; unfold diagonal_query; apply tagged_eval; evaluate. Qed.

Lemma type_app_tagged_query_constructor : forall AI C E,
 supports_queries AI -> query_abstractor_at AI @ C ==> Sm E ->
 type_app AI @ tagged_query @r C ==> Sm ('tagged[E,query_nm]).
Proof.
 intros; apply app_tagged_query; assumption.
Qed.

Unset Default Proof Using.
Transparent get_query get_S_fields equal equal1 is_concrete get_wrap_payload_type get_tagname get_IfNamed.

(**********************************************************************)
(* A typed query computing the size of a tree.                        *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans data_types recursion.

Set Default Proof Using "Type".
Open Scope string_scope.

(** The leaf contributes its root. *)
Definition size_leaf : Combination := succ zero.

Lemma infer_size_leaf : forall (AI : Decl),
  supports_number AI ->
  infer AI @ size_leaf ==> Sm ('Nat).
Proof.
  intros AI Hnat; unfold size_leaf.
  apply infer_succ; [exact Hnat |].
  apply infer_zero; exact Hnat.
Qed.

Set Default Proof Using "All".
Open Scope string_scope.

Section SizeInference.
Variable AI : Decl.
Hypothesis AI_supports_queries : supports_queries AI.
Hypothesis AI_supports_number : supports_number AI.

(** The fork of a sum applies the recursive query [r] to both children and
    combines the two results by [f]: the first child's result is held by a
    query over the second child. *)
Definition sum_fork_term (f : Term -> Term -> Term) (r : Term) : Term :=
  ''S_q[''Kq (star "n" (''S_q[''Kq (star "m" (f (Ref "n") (Ref "m"))), r])), r].

Definition size_stem_term (q : Term) : Term := ''S_q[''Kq (Val succ_step), q].
Definition size_fork_term (q : Term) : Term :=
  sum_fork_term (fun n m => Val succ_step @@ (Val add @@ (n ''* m))) q.

Definition size_functional_body_package :
  { t : Combination |
    to_tree
      (star "q"
        (''tq[Val size_leaf, size_stem_term (Ref "q"), size_fork_term (Ref "q")])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition size_functional_body :=
  Eval cbn in proj1_sig size_functional_body_package.

Ltac known_size_type_app :=
  lazymatch goal with
  | |- supports_queries AI => exact AI_supports_queries
  | |- supports_number AI => exact AI_supports_number
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | nat_split => unfold nat_split
      | cons_step => unfold cons_step
      | nat_pred => unfold nat_pred
      | nat_shift => unfold nat_shift
      | mk_zero => unfold mk_zero
      | 'Nat => eapply type_app_Nat
      | 'Query[?B] => eapply type_app_abstract; apply query_eliminator_eval
      | tagged_query =>
          eapply type_app_tagged_query_constructor;
          [apply AI_supports_queries |]
      | Lf => eapply type_app_leaf_ev
      | Fk Lf ?x => eapply type_app_K_ev
      | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
      | Sm ?x => eapply type_app_stem_ev
      | Fk (Sm (Fk Lf ?g)) ?f =>
          eapply type_app_compose; [solve [reject_name]| | |];
          [solve [intros E N Heq; discriminate Heq] | |]
      | Fk (Sm ?g) ?f =>
          new_S;
          [solve [intros E N Heq; discriminate Heq] | | |]
      end
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | Fk (Fk ?a ?b) ?c =>
          eapply type_app_stem_structural; intros; discriminate
      | _ => first
        [ eapply type_app_stem_tagged; eapply query_abstractor_supported; [exact AI_supports_queries |]
        | apply type_app_stem_structural; intros; discriminate
        | eapply type_app_stem_structural;
          intros; discriminate
        ]
      end
  end.

Local Ltac size_infer :=
  repeat first
    [ eassumption
    | solve [eapply infer_size_leaf; eauto]
    | eapply infer_Kq; [apply AI_supports_queries |]
    | eapply infer_tq; [apply AI_supports_queries |]
    | eapply query_abstractor_K | eapply query_abstractor_S
    | eapply query_abstractor_triage
    | eapply infer_fork | eapply infer_stem | eapply infer_leaf
    | eapply infer_I | eapply infer_K1
    | progress known_size_type_app ].

Local Definition size_functional_type_package :
  { F : Combination |
      infer AI @ size_functional_body ==> Sm F /\
      type_app AI @ F @r ('Query['Nat]) ==>
        Sm ('Query['Nat]) }.
Proof.
  pose proof (infer_add AI) as Hadd.
  assert (Hsucc : infer AI @ succ_step ==> Sm succ_step)
    by (apply infer_tag_free; vm_compute; reflexivity).
  pose proof (type_app_add AI AI_supports_number) as Hadd_app.
  pose proof (type_app_succ_step AI AI_supports_number) as Hsucc_app.
  eexists; split.
  all: unfold size_functional_body,
      size_functional_body_package; cbn.
  all: size_infer.
  Unshelve. all: size_infer.
Defined.

Definition size := fix_query ('decorate[size_functional_body, 'Kq size_leaf]).

Theorem infer_size :
  infer AI @ size ==> Sm ('Query['Nat]).
Proof.
  unfold size; eapply infer_fix_query.
  - apply AI_supports_queries.
  - exact (proj1 (proj2_sig size_functional_type_package)).
  - eapply infer_Kq; [apply AI_supports_queries|eapply infer_size_leaf; eauto].
  - exact (proj2 (proj2_sig size_functional_type_package)).
Qed.

End SizeInference.

Set Default Proof Using "Type".
Opaque equal.


(** [size @ x :: Nat] (introduction). *)
Lemma size_application_typed : forall (AI : Decl) x X,
  supports_queries AI -> supports_number AI ->
  infer AI @ x ==> Sm X ->
  infer_expression AI @ (size @ x) ==> Sm ('Nat).
Proof.
  intros AI x X Hq Hn Hx; eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_size; assumption.
  - apply infer_expression_stem; exact Hx.
  - apply app_abstract; apply query_eliminator_eval.
Qed.

Opaque zero.
Set Default Proof Using "Type".


Unset Default Proof Using.
Transparent get_query get_S_fields equal equal1 is_concrete get_wrap_payload_type get_tagname get_IfNamed zero.

(** Behaviour of the size query (paper: [size : Query[Nat]] counts nodes).
    [size_eval] shows that [size] returns the numeral of [tree_size]:
    a leaf has size 1, a stem adds one, and a fork adds one to the sum.
    The proof is direct structural induction on the argument; no general
    fixpoint or termination machinery is needed. *)
From Stdlib Require Import Arith.
From TreeTyping Require Import tree.
From TreeTyping Require Import booleans functions data_types recursion.
Set Default Proof Using "Type".

Definition size_stem (q : Combination) : Combination :=
  'S_q['Kq succ_step,q].
Definition size_fork_package (q : Combination) :
  { t : Combination | to_tree (size_fork_term (Val q)) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition size_fork (q : Combination) : Combination :=
  Eval cbn in proj1_sig (size_fork_package q).

(** One unfolding of the fixpoint: [size] selects the triage query whose
    recursive calls are [size] itself. *)
Lemma size_unfold : forall x v,
  'tq[size_leaf, size_stem size, size_fork size] @ x ==> v ->
  size @ x ==> v.
Proof.
  intros x v H; unfold size at 1, fix_query; apply tagged_eval, Z_unfold.
  eapply eval_op; [|exact H].
  eapply eval_c; eapply eval_appr.
  - unfold tagged_query, tagged_query_package; cbn; evaluate.
  - apply wait_eval; eapply eval_appl; [evaluate|].
    unfold size_stem, size_fork, size, fix_query.
    unfold size_functional_body, size_functional_body_package; cbn; evaluate.
Qed.

Lemma size_stem_eval : forall q u n,
  q @ u ==> numeral n -> size_stem q @ u ==> numeral (S n).
Proof.
  intros q u n H; unfold size_stem; eapply S_q_eval;
    [apply K_q_eval | exact H | apply succ_step_eval].
Qed.

Lemma size_fork_eval : forall q u v a b,
  q @ u ==> numeral a -> q @ v ==> numeral b ->
  size_fork q @ u @r v ==> numeral (S (a + b)).
Proof.
  intros q u v a b Hu Hv.
  pose proof (add_numerals a b) as HA.
  pose proof (succ_step_eval (numeral (a + b))) as HS.
  destruct (eval_pair_inv _ _ _ HA) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold size_fork; cbn.
  repeat first [eassumption | apply S_q_eval | apply K_q_eval
               | progress evaluate].
Qed.

Lemma size_eval : forall x, size @ x ==> numeral (tree_size x).
Proof.
  induction x as [|u IHu|u IHu v IHv]; apply size_unfold; cbn [tree_size].
  - apply triage_q_leaf_eval.
  - apply triage_q_stem_eval, size_stem_eval, IHu.
  - pose proof (size_fork_eval _ _ _ _ _ IHu IHv) as H; inv_out H.
    eapply triage_q_fork_eval; eassumption.
Qed.




Unset Default Proof Using.
Transparent get_query get_S_fields equal equal1 is_concrete get_wrap_payload_type get_tagname get_IfNamed zero successor_function.

(**********************************************************************)
(* A compact typing development for structural equality.              *)
(**********************************************************************)

From Stdlib Require Import String.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans.

Set Default Proof Using "All".
Open Scope string_scope.

Section EqualityInference.
Variable AI : Decl.
Hypothesis AI_supports_queries : supports_queries AI.
Hypothesis AI_supports_booleans : supports_booleans AI.

Ltac known_equality_type_app :=
  lazymatch goal with
  | |- type_app _ @ ?T @r ?U ==> _ =>
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | 'triage[?F0, ?F1, ?F2] =>
          apply installed_traversal; intros ? ? ?; discriminate
      | 'Bool =>
          eapply type_app_abstract; apply bool_eliminator_some
      | 'Query[?B] =>
          eapply type_app_abstract; apply query_eliminator_eval
      | Lf => eapply type_app_leaf_ev
      | Fk Lf ?x => eapply type_app_K_ev
      | Fk (Sm (Sm Lf)) (Sm Lf) => eapply type_app_I
      | Sm ?x => eapply type_app_stem_ev
      | Fk (Sm (Fk Lf ?g)) ?f =>
          eapply type_app_compose; [solve [reject_name]| | |];
          [intros E N Heq; inversion Heq | |]
      | Fk (Sm ?g) ?f =>
          new_S;
          [intros E N Heq; discriminate Heq | | |]
      end
  | |- type_app_stem _ @ type_app _ @r ?L @r ?R ==> _ =>
      let T := constr:(Fk L R) in
      first [is_evar T; fail 1 | idtac];
      lazymatch T with
      | Fk (Fk ?a ?b) ?c =>
          eapply type_app_stem_structural; intros; discriminate
      | _ => first
        [ eapply type_app_stem_tagged; eapply query_abstractor_supported;
          [exact AI_supports_queries |]
        | eapply type_app_stem_structural; intros; discriminate
        | apply type_app_stem_structural; intros; discriminate
        ]
      end
  end.

Ltac equality_infer :=
  repeat first
    [ exact AI_supports_queries
    | exact AI_supports_booleans
    | eassumption
    | eapply tt_infer; exact AI_supports_booleans
    | eapply ff_infer; exact AI_supports_booleans
    | eapply infer_Kq; [exact AI_supports_queries |]
    | eapply infer_tq
    | eapply query_abstractor_K
    | eapply query_abstractor_S
    | eapply query_abstractor_triage
    | eapply infer_fork | eapply infer_stem | eapply infer_leaf
    | eapply infer_I | eapply infer_K1
    | progress known_equality_type_app ].

(** Equality against a leaf: true only on a leaf. *)
Definition equality_leaf : Combination :=
  'tq['tt, 'Kq 'ff, 'Kq ('Kq 'ff)].

Lemma infer_equality_leaf :
  infer AI @ equality_leaf ==> Sm ('Query['Bool]).
Proof. unfold equality_leaf; equality_infer. Qed.

(** Boolean conjunction, of two arguments. *)
Definition typed_conjunction_package :
  { t : Combination |
    to_tree (star "b1" (star "b2" (Ref "b1" @@ (Ref "b2" ''* Val 'ff)))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition typed_conjunction := Eval cbn in proj1_sig typed_conjunction_package.

Lemma typed_conjunction_tt : typed_conjunction @ 'tt @r 'tt ==> 'tt.
Proof using. unfold typed_conjunction; cbn; evaluate. Qed.

Local Definition typed_conjunction_type_package :
  { F : Combination | infer AI @ typed_conjunction ==> Sm F }.
Proof. eexists; unfold typed_conjunction; cbn; equality_infer. Defined.
Definition typed_conjunction_type := Eval cbn in proj1_sig typed_conjunction_type_package.
Lemma infer_typed_conjunction :
  infer AI @ typed_conjunction ==> Sm typed_conjunction_type.
Proof. exact (proj2_sig typed_conjunction_type_package). Qed.

Opaque typed_conjunction.

Definition query_conjunction (p q : Combination) : Combination :=
  'S_q['S_q['Kq typed_conjunction,p],q].

(** Pointwise query conjunction, of two arguments. *)
Definition typed_query_conjunction_package :
  { t : Combination |
    to_tree
      (star "p" (star "q"
        (''S_q[''S_q[''Kq (Val typed_conjunction), Ref "p"], Ref "q"]))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition typed_query_conjunction :=
  Eval cbn in proj1_sig typed_query_conjunction_package.

Lemma typed_query_conjunction_eval : forall p q,
  typed_query_conjunction @ p @r q ==> query_conjunction p q.
Proof using.
  intros p q; unfold typed_query_conjunction, query_conjunction; cbn; evaluate.
Qed.

Local Definition typed_query_conjunction_type_package :
  { F : Combination | infer AI @ typed_query_conjunction ==> Sm F }.
Proof.
  pose proof infer_typed_conjunction.
  eexists; unfold typed_query_conjunction; cbn; equality_infer.
Defined.
Definition typed_query_conjunction_type :=
  Eval cbn in proj1_sig typed_query_conjunction_type_package.
Lemma infer_typed_query_conjunction :
  infer AI @ typed_query_conjunction ==> Sm typed_query_conjunction_type.
Proof. exact (proj2_sig typed_query_conjunction_type_package). Qed.

Opaque typed_query_conjunction.

(** Turn a Boolean into its constant Boolean query. *)
Definition typed_K_q_package :
  { t : Combination | to_tree (star "b" (''Kq (Ref "b"))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition typed_K_q := Eval cbn in proj1_sig typed_K_q_package.

Lemma typed_K_q_eval : forall b,
  typed_K_q @ b ==> ('Kq b).
Proof using. intro b; unfold typed_K_q; cbn; evaluate. Qed.

Local Definition typed_K_q_type_package :
  { F : Combination | infer AI @ typed_K_q ==> Sm F }.
Proof. eexists; unfold typed_K_q; cbn; equality_infer. Defined.
Definition typed_K_q_type := Eval cbn in proj1_sig typed_K_q_type_package.
Lemma infer_typed_K_q : infer AI @ typed_K_q ==> Sm typed_K_q_type.
Proof. exact (proj2_sig typed_K_q_type_package). Qed.

Opaque typed_K_q.

(** The first recursive comparison varies with the first component of the
    second fork.  Its Boolean result is converted into a constant query over
    the remaining component. *)
Definition left_fork_comparison (qx : Combination) : Combination :=
  'S_q['Kq typed_K_q,qx].

(** The second recursive comparison is already a Boolean query, and is
    constant with respect to the preceding component. *)
Definition right_fork_comparison (qy : Combination) : Combination :=
  'Kq qy.

(** Once aligned at the same nested-query type, combine the components
    pointwise. *)
Definition combined_fork_comparison
    (left right : Combination) : Combination :=
  'S_q['S_q['Kq typed_query_conjunction,left],right].

Definition left_fork_comparison_term (qx : Term) : Term :=
  ''S_q[''Kq (Val typed_K_q), qx].

Definition right_fork_comparison_term (qy : Term) : Term :=
  ''Kq qy.

Definition combined_fork_comparison_term
    (left right : Term) : Term :=
  ''S_q[
    ''S_q[''Kq (Val typed_query_conjunction), left],
    right].

(** The comparison of a pair from its two recursive comparisons. *)
Definition pair_comparison_builder_package :
  { t : Combination |
    to_tree
      (star "qx" (star "qy"
        (combined_fork_comparison_term
          (left_fork_comparison_term (Ref "qx"))
          (right_fork_comparison_term (Ref "qy"))))) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition pair_comparison_builder :=
  Eval cbn in proj1_sig pair_comparison_builder_package.

(** [pair_comparison_builder] produces the fork branch of a comparison
    query.  Complete it by rejecting leaf and stem arguments. *)
Definition complete_fork_comparison (branch : Combination) : Combination :=
  'tq['ff, 'Kq 'ff, branch].

Definition complete_fork_comparison_builder_package :
  { t : Combination |
    to_tree
      (star "branch"
        (''tq[
          Val 'ff, ''Kq (Val 'ff), Ref "branch"])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition complete_fork_comparison_builder : Combination :=
  Eval cbn in proj1_sig complete_fork_comparison_builder_package.

(** The fork branch: the comparison of the left components selects, for
    each right component, the completed comparison of the pair. *)
Definition equality_fork_branch_value_term (q : Term) : Term :=
  ''S_q[
    ''Kq
      (star "qx"
        (''S_q[
          ''Kq (star "qy"
            (Val complete_fork_comparison_builder
              @@ (Val pair_comparison_builder @@ Ref "qx" @@ Ref "qy"))),
          q])),
    q].

Definition equality_fork_branch_package (q : Combination) :
  { t : Combination | to_tree (equality_fork_branch_value_term (Val q)) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition equality_fork_branch (q : Combination) : Combination :=
  Eval cbn in proj1_sig (equality_fork_branch_package q).

(** A stem comparison must also require a stem on its second argument.
    Once both stems have been removed, [q] compares their payloads. *)
Definition equality_stem_comparison (q : Combination) : Combination :=
  'tq['ff, q, 'Kq ('Kq 'ff)].

Definition equality_stem_builder_package :
  { t : Combination |
    to_tree
      (star "q"
        (''tq[
          Val 'ff, Ref "q", ''Kq (''Kq (Val 'ff))])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition equality_stem_builder :=
  Eval cbn in proj1_sig equality_stem_builder_package.

Definition equality_stem (q : Combination) : Combination :=
  'S_q['Kq equality_stem_builder,q].

Definition equality_stem_value_term (q : Term) : Term :=
  ''S_q[''Kq (Val equality_stem_builder),q].

Lemma equality_stem_builder_eval : forall q,
  equality_stem_builder @ q ==> equality_stem_comparison q.
Proof using.
  intro q; unfold equality_stem_builder, equality_stem_comparison; cbn; evaluate.
Qed.

Lemma equality_stem_eval : forall q x qx,
  q @ x ==> qx ->
  equality_stem q @ x ==> equality_stem_comparison qx.
Proof using.
  intros q x qx Hqx; unfold equality_stem.
  eapply S_q_eval.
  - apply K_q_eval.
  - exact Hqx.
  - apply equality_stem_builder_eval.
Qed.

Local Definition pair_comparison_builder_type_package :
  { F : Combination | infer AI @ pair_comparison_builder ==> Sm F }.
Proof.
  pose proof infer_typed_K_q; pose proof infer_typed_query_conjunction.
  eexists; unfold pair_comparison_builder; cbn; equality_infer.
Defined.
Definition pair_comparison_builder_type :=
  Eval cbn in proj1_sig pair_comparison_builder_type_package.
Lemma infer_pair_comparison_builder :
  infer AI @ pair_comparison_builder ==> Sm pair_comparison_builder_type.
Proof. exact (proj2_sig pair_comparison_builder_type_package). Qed.

Local Definition complete_fork_comparison_builder_type_package :
  { F : Combination | infer AI @ complete_fork_comparison_builder ==> Sm F }.
Proof. eexists; unfold complete_fork_comparison_builder; cbn; equality_infer. Defined.
Definition complete_fork_comparison_builder_type :=
  Eval cbn in proj1_sig complete_fork_comparison_builder_type_package.
Lemma infer_complete_fork_comparison_builder :
  infer AI @ complete_fork_comparison_builder ==> Sm complete_fork_comparison_builder_type.
Proof. exact (proj2_sig complete_fork_comparison_builder_type_package). Qed.

Local Definition equality_stem_builder_type_package :
  { F : Combination | infer AI @ equality_stem_builder ==> Sm F }.
Proof. eexists; unfold equality_stem_builder; cbn; equality_infer. Defined.
Definition equality_stem_builder_type :=
  Eval cbn in proj1_sig equality_stem_builder_type_package.
Lemma infer_equality_stem_builder :
  infer AI @ equality_stem_builder ==> Sm equality_stem_builder_type.
Proof. exact (proj2_sig equality_stem_builder_type_package). Qed.

Opaque pair_comparison_builder complete_fork_comparison_builder equality_stem_builder.

(** The recursive functional follows the three tree shapes.  A leaf is equal
    only to a leaf; a stem constructs a shape-checking comparison query; a
    fork delegates to the separately typed binary comparison builder. *)
Definition equality_functional_body_package :
  { t : Combination |
    to_tree
      (star "q"
        (''tq[
          Val equality_leaf,
          equality_stem_value_term (Ref "q"),
          equality_fork_branch_value_term (Ref "q")
        ])) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition equality_functional_body :=
  Eval cbn in proj1_sig equality_functional_body_package.

Local Ltac assembled_equality_infer :=
  repeat first
    [ exact infer_equality_leaf
    | exact infer_equality_stem_builder
    | exact infer_pair_comparison_builder
    | exact infer_complete_fork_comparison_builder
    | exact infer_typed_K_q
    | exact infer_typed_query_conjunction
    | exact infer_typed_conjunction
    | progress unfold equality_stem_builder_type, pair_comparison_builder_type,
        complete_fork_comparison_builder_type, typed_K_q_type,
        typed_query_conjunction_type, typed_conjunction_type
    | progress equality_infer ].

Local Definition equality_functional_type_package :
  { F : Combination |
      infer AI @ equality_functional_body ==> Sm F /\
      type_app AI @ F @r ('Query['Query['Bool]]) ==>
        Sm ('Query['Query['Bool]]) }.
Proof.
  eexists; split.
  all: unfold equality_functional_body,
      equality_functional_body_package, equality_stem_value_term,
      equality_fork_branch_value_term; cbn.
  all: assembled_equality_infer.
  Unshelve. all: assembled_equality_infer.
Defined.

Definition typed_equal :=
  fix_query ('decorate[equality_functional_body, 'Kq equality_leaf]).

Lemma infer_typed_equal :
  infer AI @ typed_equal ==> Sm ('Query['Query['Bool]]).
Proof.
  unfold typed_equal; eapply infer_fix_query.
  - exact AI_supports_queries.
  - exact (proj1 (proj2_sig equality_functional_type_package)).
  - eapply infer_Kq; [exact AI_supports_queries|exact infer_equality_leaf].
  - exact (proj2 (proj2_sig equality_functional_type_package)).
Qed.

End EqualityInference.

(** * Reflexivity of the typed equality query

    The paper calls [typed_equal] simply [equal]. Comparing a value
    with itself follows matching tree shapes. Leaves give true; stems
    use the child's comparison; forks conjoin the two child comparisons.
    The local lemmas expose the existing builders without unfolding the
    whole recursive program. This result concerns evaluation alone and
    requires no typing assumptions. *)
Transparent typed_conjunction typed_query_conjunction typed_K_q
  pair_comparison_builder complete_fork_comparison_builder equality_stem_builder.
(** The constant-query builder is typed at any declarations, and maps
    every type [B] to [Query[B]]. *)
Lemma infer_typed_K_q_any : forall AI, infer AI @ typed_K_q ==> Sm typed_K_q_type.
Proof. intros; unfold typed_K_q, typed_K_q_type; infer_tac. Qed.
Lemma type_app_typed_K_q : forall (AI : Decl) B, supports_queries AI ->
  type_app AI @ typed_K_q_type @r B ==> Sm ('Query[B]).
Proof.
  intros AI B HQ; unfold typed_K_q_type.
  type_app_tac.
  all: try (apply type_app_stem_tagged; eapply query_abstractor_supported; [exact HQ|apply query_abstractor_K]).
  apply app_stem; apply type_app_stem_tagged.
  eapply query_abstractor_supported; [exact HQ|apply query_abstractor_K].
Qed.

Local Lemma equality_functional_eval : forall q,
  equality_functional_body @ q ==>
    'tq[equality_leaf,equality_stem q,equality_fork_branch q].
Proof.
  intros; unfold equality_functional_body, equality_functional_body_package,
    equality_stem_value_term, equality_fork_branch_value_term,
    equality_stem, equality_fork_branch, equality_fork_branch_package.
  cbn; evaluate.
Qed.

Local Lemma equality_pair_builder_eval : forall qx qy,
  pair_comparison_builder @ qx @r qy ==>
    combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy).
Proof.
  intros; unfold pair_comparison_builder, pair_comparison_builder_package,
    combined_fork_comparison_term, left_fork_comparison_term,
    right_fork_comparison_term, combined_fork_comparison,
    left_fork_comparison, right_fork_comparison; cbn; evaluate.
Qed.

Local Lemma equality_complete_fork_eval : forall branch,
  complete_fork_comparison_builder @ branch ==> complete_fork_comparison branch.
Proof.
  intros; unfold complete_fork_comparison_builder,
    complete_fork_comparison_builder_package, complete_fork_comparison;
    cbn; evaluate.
Qed.

Local Lemma equality_fork_eval : forall q x y qx qy,
  q @ x ==> qx -> q @ y ==> qy ->
  equality_fork_branch q @ x @r y ==>
    complete_fork_comparison
      (combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy)).
Proof.
  intros q x y qx qy Hx Hy.
  pose proof (equality_pair_builder_eval qx qy) as Hp; inv_out Hp.
  pose proof (equality_complete_fork_eval
    (combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy))) as Hc.
  eapply eval_appl.
  - unfold equality_fork_branch; cbn.
    eapply S_q_eval; [apply K_q_eval|exact Hx|]. evaluate.
  - eapply S_q_eval; [apply K_q_eval|exact Hy|]. evaluate.
Qed.


Local Lemma query_conjunction_tt : forall p q x,
  p @ x ==> 'tt -> q @ x ==> 'tt ->
  query_conjunction p q @ x ==> 'tt.
Proof.
  intros p q x Hp Hq.
  pose proof typed_conjunction_tt as Htt; inv_out Htt.
  unfold query_conjunction; eapply S_q_eval.
  - eapply S_q_eval; [apply K_q_eval | exact Hp | eassumption].
  - exact Hq.
  - assumption.
Qed.

Local Lemma equality_fork_diagonal : forall qx qy x y,
  qx @ x ==> 'tt -> qy @ y ==> 'tt ->
  complete_fork_comparison
    (combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy))
    @ Fk x y ==> 'tt.
Proof.
  intros qx qy x y Hx Hy.
  pose proof (typed_query_conjunction_eval ('Kq 'tt) qy) as Hconj; inv_out Hconj.
  unfold complete_fork_comparison; eapply triage_q_fork_eval.
  - unfold combined_fork_comparison; eapply S_q_eval.
    + eapply S_q_eval.
      * apply K_q_eval.
      * unfold left_fork_comparison; eapply S_q_eval;
          [apply K_q_eval | exact Hx | apply typed_K_q_eval].
      * eassumption.
    + unfold right_fork_comparison; apply K_q_eval.
    + eassumption.
  - apply query_conjunction_tt; [apply K_q_eval | exact Hy].
Qed.

Local Lemma typed_equal_step : forall u v,
  ('tq[equality_leaf,equality_stem typed_equal,
    equality_fork_branch typed_equal]) @ u ==> v ->
  typed_equal @ u ==> v.
Proof.
  intros u v H.
  assert (Htag : tagged_query @ Z ('decorate[equality_functional_body, 'Kq equality_leaf]
    'C tagged_query) ==> typed_equal).
  { unfold tagged_query, tagged_query_package, typed_equal, fix_query;
      cbn; evaluate. }
  unfold typed_equal at 1, fix_query; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|exact H].
  apply eval_c; eapply eval_appr; [exact Htag|].
  apply wait_eval; eapply eval_appl; [evaluate|apply equality_functional_eval].
Qed.

(** Each value builds a comparison query which returns true on that value.
    The induction also supplies the intermediate query needed by eager
    application. No typing or declarations hypotheses are required. *)
Lemma typed_equal_refl : forall v,
  typed_equal @ v @r v ==> 'tt.
Proof.
  assert (Hdiagonal : forall v, exists q,
    typed_equal @ v ==> q /\ q @ v ==> 'tt).
  { induction v as [|x [qx [Hx Hxx]]|x [qx [Hx Hxx]] y [qy [Hy Hyy]]].
    - exists equality_leaf; split.
      + apply typed_equal_step; apply triage_q_leaf_eval.
      + unfold equality_leaf; apply triage_q_leaf_eval.
    - exists (equality_stem_comparison qx); split.
      + apply typed_equal_step; apply triage_q_stem_eval.
        apply equality_stem_eval; exact Hx.
      + unfold equality_stem_comparison; apply triage_q_stem_eval; exact Hxx.
    - exists (complete_fork_comparison
        (combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy)));
        split.
      + apply typed_equal_step.
        pose proof (equality_fork_eval typed_equal x y qx qy Hx Hy) as Hfork.
        inv_out Hfork; eapply triage_q_fork_eval; eassumption.
      + apply equality_fork_diagonal; assumption. }
  intro v; destruct (Hdiagonal v) as [q [Hq Htt]].
  eapply eval_appl; eassumption.
Qed.

Lemma typed_equal_self :
  typed_equal @ typed_equal @r typed_equal ==> 'tt.
Proof. apply typed_equal_refl. Qed.

(** [typed_equal] applies to any two types. *)
Theorem typed_equal_polymorphic : forall (AI : Decl),
  supports_queries AI -> supports_booleans AI ->
  infer AI @ typed_equal ==> Sm ('Query['Query['Bool]]) /\
  (forall U V, type_app AI @ ('Query['Query['Bool]]) @r U ==> Sm ('Query['Bool]) /\
    type_app AI @ ('Query['Bool]) @r V ==> Sm ('Bool)) /\
  typed_equal @ typed_equal @r typed_equal ==> 'tt.
Proof.
  intros AI Hq Hb; split; [apply infer_typed_equal; assumption|split; [|exact typed_equal_self]].
  intros U V; split; apply type_app_Query.
Qed.


(** [equal @ x :: Query[Bool]] and [equal @ x @r y :: Bool]
    (introduction).  The paper's [equal] is [typed_equal]. *)
Lemma equal_application_typed : forall (AI : Decl) x X,
  supports_queries AI -> supports_booleans AI ->
  infer AI @ x ==> Sm X ->
  infer_expression AI @ (typed_equal @ x) ==> Sm ('Query['Bool]).
Proof.
  intros AI x X Hq Hb Hx; eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_typed_equal; assumption.
  - apply infer_expression_stem; exact Hx.
  - apply app_abstract; apply query_eliminator_eval.
Qed.

Lemma equal_application2_typed : forall (AI : Decl) x X y Y,
  supports_queries AI -> supports_booleans AI ->
  infer AI @ x ==> Sm X -> infer AI @ y ==> Sm Y ->
  infer_expression AI @ Fk (typed_equal @ x) (Sm y) ==> Sm ('Bool).
Proof.
  intros AI x X y Y Hq Hb Hx Hy; eapply infer_expression_fork.
  - eapply equal_application_typed; eassumption.
  - apply infer_expression_stem; exact Hy.
  - apply app_abstract; apply query_eliminator_eval.
Qed.


Unset Default Proof Using.
Transparent get_query get_S_fields equal equal1 is_concrete get_wrap_payload_type get_tagname get_IfNamed zero successor_function.

(** * Typed equality decides tree equality

    The paper's [equal : Query[Query[Bool]]] is [typed_equal]. It is total
    and correct: [typed_equal @ x @r y] evaluates to ['tt] when [x = y] and
    to ['ff] when [x <> y].

    The first application folds [x] into a residual query, specified here by
    [equality_residual x] (cf. tree.equal1); the second application runs that
    query on [y]. The specification does not replace the runtime program, and
    no typing assumptions are needed. *)
From Stdlib Require Import Bool.
From TreeTyping Require Import tree.
From TreeTyping Require Import functions booleans.
Set Default Proof Using "Type".

Definition bool_tree (b : bool) := if b then 'tt else 'ff.

Fixpoint tree_eqb x y :=
 match x, y with
 | Lf, Lf => true
 | Sm u, Sm v => tree_eqb u v
 | Fk u v, Fk u' v' => andb (tree_eqb u u') (tree_eqb v v')
 | _, _ => false
 end.


(** ** Boolean conjunction of comparison results *)

Lemma conjunction_bool_tree : forall a b,
 typed_conjunction @ bool_tree a @r bool_tree b ==> bool_tree (andb a b).
Proof.
 intros [] []; unfold bool_tree, typed_conjunction; cbn; evaluate.
Qed.

Lemma query_conjunction_bool_tree : forall p q x a b,
 p @ x ==> bool_tree a -> q @ x ==> bool_tree b ->
 query_conjunction p q @ x ==> bool_tree (andb a b).
Proof.
 intros p q x a b Hp Hq.
 pose proof (conjunction_bool_tree a b) as H; inv_out H.
 unfold query_conjunction; eapply S_q_eval.
 - eapply S_q_eval; [apply K_q_eval|exact Hp|eassumption].
 - exact Hq.
 - eassumption.
Qed.

Lemma fork_comparison_bool_tree : forall qx qy x y a b,
 qx @ x ==> bool_tree a -> qy @ y ==> bool_tree b ->
 complete_fork_comparison
   (combined_fork_comparison (left_fork_comparison qx) (right_fork_comparison qy))
   @ Fk x y ==> bool_tree (andb a b).
Proof.
 intros qx qy x y a b Hx Hy.
 pose proof (typed_query_conjunction_eval ('Kq (bool_tree a)) qy) as H; inv_out H.
 unfold complete_fork_comparison; eapply triage_q_fork_eval.
 - unfold combined_fork_comparison; eapply S_q_eval.
   + eapply S_q_eval.
     * apply K_q_eval.
     * unfold left_fork_comparison; eapply S_q_eval;
       [apply K_q_eval|exact Hx|apply typed_K_q_eval].
     * eassumption.
   + unfold right_fork_comparison; apply K_q_eval.
   + eassumption.
 - apply query_conjunction_bool_tree; [apply K_q_eval|exact Hy].
Qed.

(** ** The residual query built by the first application *)

Fixpoint equality_residual x :=
 match x with
 | Lf => equality_leaf
 | Sm u => equality_stem_comparison (equality_residual u)
 | Fk u v => complete_fork_comparison
   (combined_fork_comparison (left_fork_comparison (equality_residual u))
     (right_fork_comparison (equality_residual v)))
 end.

Lemma typed_equal_builds_residual : forall x,
 typed_equal @ x ==> equality_residual x.
Proof.
 induction x; cbn [equality_residual]; apply queries.typed_equal_step.
 - apply triage_q_leaf_eval.
 - apply triage_q_stem_eval; apply equality_stem_eval; exact IHx.
 - pose proof (queries.equality_fork_eval _ _ _ _ _ IHx1 IHx2) as H.
   inv_out H; eapply triage_q_fork_eval; eassumption.
Qed.

Lemma equality_residual_eval : forall x y,
 equality_residual x @ y ==> bool_tree (tree_eqb x y).
Proof.
 induction x; intros [|y|y z]; cbn [equality_residual tree_eqb].
 - unfold equality_leaf; apply triage_q_leaf_eval.
 - unfold equality_leaf; apply triage_q_stem_eval; apply K_q_eval.
 - unfold equality_leaf; eapply triage_q_fork_eval; apply K_q_eval.
 - unfold equality_stem_comparison; apply triage_q_leaf_eval.
 - unfold equality_stem_comparison; apply triage_q_stem_eval; apply IHx.
 - unfold equality_stem_comparison; eapply triage_q_fork_eval; apply K_q_eval.
 - unfold complete_fork_comparison; apply triage_q_leaf_eval.
 - unfold complete_fork_comparison; apply triage_q_stem_eval; apply K_q_eval.
 - apply fork_comparison_bool_tree; [apply IHx1|apply IHx2].
Qed.

(** ** Main results *)

Theorem typed_equal_eval : forall x y,
 typed_equal @ x @r y ==> bool_tree (tree_eqb x y).
Proof.
 intros; eapply eval_appl;
 [apply typed_equal_builds_residual|apply equality_residual_eval].
Qed.


Unset Default Proof Using.
Transparent get_query get_S_fields equal equal1 is_concrete get_wrap_payload_type get_tagname get_IfNamed zero successor_function.

(** Finite structural patterns compiled to typed generic queries. Wildcards
    accept their input without traversing it. *)
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions booleans.
From Stdlib Require Import String Bool.
Open Scope string_scope.
Set Default Proof Using "Type".

(** A finite pattern compiles to an ordinary tree-calculus query. Pattern
    matching at runtime is performed by that query, not by a Rocq function. *)
Inductive query_pattern := PAny | PLeaf | PStem (p : query_pattern)
  | PFork (p q : query_pattern).
Fixpoint pattern_matches p x : bool :=
  match p,x with
  | PAny,_ => true | PLeaf,Lf => true
  | PStem p,Sm x => pattern_matches p x
  | PFork p q,Fk x y => andb (pattern_matches p x) (pattern_matches q y)
  | _,_ => false
  end.
(** A compact compilation: [pc p f s] answers [s] on a match and [f]
    otherwise, by nesting triage queries.  A fork's left part answers a
    query for its right part, so no conjunction is needed. *)
Fixpoint pc (p : query_pattern) (f s : Combination) : Combination :=
  match p with
  | PAny => 'Kq s
  | PLeaf => 'tq[s, 'Kq f, 'Kq ('Kq f)]
  | PStem p' => 'tq[f, pc p' f s, 'Kq ('Kq f)]
  | PFork a c => 'tq[f, 'Kq f, pc a ('Kq f) (pc c f s)]
  end.

Lemma pc_eval : forall p f s x,
  pc p f s @ x ==> (if pattern_matches p x then s else f).
Proof.
  induction p as [| |p IH|a IHa c IHc]; intros f s x; cbn [pc pattern_matches].
  - apply K_q_eval.
  - destruct x as [|x|l r]; cbn [pattern_matches].
    + apply triage_q_leaf_eval.
    + apply triage_q_stem_eval; apply K_q_eval.
    + eapply triage_q_fork_eval; apply K_q_eval.
  - destruct x as [|x|l r]; cbn [pattern_matches].
    + apply triage_q_leaf_eval.
    + apply triage_q_stem_eval; apply IH.
    + eapply triage_q_fork_eval; apply K_q_eval.
  - destruct x as [|x|l r]; cbn [pattern_matches].
    + apply triage_q_leaf_eval.
    + apply triage_q_stem_eval; apply K_q_eval.
    + eapply triage_q_fork_eval; [apply IHa|].
      destruct (pattern_matches a l); cbn [andb]; [apply IHc|apply K_q_eval].
Qed.

Lemma pc_typed : forall AI p f s R,
  supports_queries AI -> infer AI @ f ==> Sm R -> infer AI @ s ==> Sm R ->
  infer AI @ pc p f s ==> Sm ('Query[R]).
Proof.
  intros AI p; induction p as [| |p IH|a IHa c IHc]; intros f s R HQ Hf Hs; cbn [pc].
  - apply infer_Kq; assumption.
  - apply infer_tq_intro; try assumption; repeat apply infer_Kq; assumption.
  - apply infer_tq_intro; try assumption; [apply IH; assumption|].
    repeat apply infer_Kq; assumption.
  - apply infer_tq_intro; try assumption; [apply infer_Kq; assumption|].
    apply IHa; [assumption|apply infer_Kq; assumption|apply IHc; assumption].
Qed.

Definition pattern_query p := pc p 'ff 'tt.
Definition bool_value (b : bool) : Combination := if b then 'tt else 'ff.

Lemma pattern_query_typed : forall AI p,
  supports_queries AI -> supports_booleans AI -> 
  infer AI @ pattern_query p ==> Sm ('Query['Bool]).
Proof.
  intros; apply pc_typed; [assumption|apply ff_infer; assumption|apply tt_infer; assumption].
Qed.
Lemma pattern_query_eval : forall p x,
  pattern_query p @ x ==> bool_value (pattern_matches p x).
Proof.
  intros p x; pose proof (pc_eval p 'ff 'tt x) as H; unfold pattern_query, bool_value.
  destruct (pattern_matches p x); exact H.
Qed.

(** One-round soundness of the declarations. *)
Lemma plain_query_cond2 : forall AI, supports_queries AI ->
  sound_abstractor AI (query_abstractor_at AI).
Proof. exact query_abstractor_value_sound. Qed.