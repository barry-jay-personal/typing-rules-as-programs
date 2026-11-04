(** * Soundness (paper: Typing Rules as Programs, "Soundness by typing", "Soundness by values").

    Sound abstractors and sound declarations ([abstractor_sound_by_typing],
    [ontology_sound]), and evaluation preserves typing
    ([evaluation_preserves_typing]).  The wrapper lemmas used by the
    soundness of the IsNamed family ([is_named_value_typing], [declared_wrapper],
    ...) are here too, although the paper explains them with Type-Directed Conditionals.

    Build order: this file precedes booleans.v, because the boolean
    abstractor is proved sound with the framework defined
    here ([plain_clause_sound_for], [extend_intro_sound_by_typing]). *)


(** Preservation is proved by strong induction on the height of the
    evaluation of type application; the height-indexed evaluation [evaln]
    and the height-aware inversions of the recursive clauses come first. *)
From Stdlib Require Import Arith Lia.
From TreeTyping Require Import tree.
From TreeTyping Require Import typing.
From TreeTyping Require Import typing.
From Stdlib Require Import String.
Open Scope string_scope.
Local Abbreviation app := typing.type_app.
Local Abbreviation inf := typing.infer.
Set Default Proof Using "Type".

(* ================================================================== *)
(** * Declarations

    A family at a nametag [N] is an abstractor [AI @ N ==> D] (typing.v):
    a program mapping each carrier type [C] of the family to its
    eliminator, [D @ C ==> Sm E], and refusing other carriers,
    [D @ C ==> Lf].  Type application applies the abstractor to the
    carrier type.  Eliminators are typically built as ['wait[E,X]] from an
    eliminator program [E] and parameters [X], so ['wait[E,X] @ U] behaves
    as [E @ X @r U].
    A nametag without a family is refused: the declarations answer
    [refusal = 'K1 Lf], which refuses every carrier type.  Parameters with
    several components use the default tupling, the Church pair [A '* B]. *)
(* ================================================================== *)

(** The eliminator ['wait[E,X]] passes its argument to [E] after [X]. *)
Lemma wait_elim : forall E X U V,
  E @ X @r U ==> V -> 'wait[E,X] @ U ==> V.
Proof. intros; apply wait_eval; assumption. Qed.

Lemma wait_elim_inv : forall E X U V,
  'wait[E,X] @ U ==> V -> E @ X @r U ==> V.
Proof. intros; apply wait_eval_inv; assumption. Qed.


(** ** Accessors

    Paths to the components of ['wait[E,X]].  The general machinery ([dir], [path_prog],
    [path_fn], [path_arg], [path_pB], [acc_arg], [acc_pB], [ceqb],
    [equal1_bt_case]) is in typing.v, where the function family uses it. *)


(** ** The refusal *)

(** The refusal refuses every carrier type. *)

Lemma refusal_eval : forall a C, refusal @ a @r C ==> Lf.
Proof. intros; unfold refusal; evaluate. Qed.


(** ** The default tupling *)


(** The default tupling: the parameters [A] and [B] form the Church pair
    [A '* B].  Its components are read by the accessors [acc_arg] and
    [acc_pB]. *)

Ltac fam_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval | apply equal1_bt
            | apply acc_arg_eval | apply acc_pB_eval ]
  end.
Ltac fam_eval :=
  first [ fam_atom | evaluate_expr_core fam_eval fam_head | idtac ]
with fam_head :=
  first [ fam_atom | evaluate_head_core fam_eval | idtac ].


(** * Height-indexed evaluation

    [evaln n e v] has the rules of [eval]; each rule concludes at height
    [S n] from premises of height [n]. *)
Inductive evaln : nat -> Combination -> Combination -> Prop :=
| evaln_val : forall n v,
    evaln (S n) (Sm v) v
| evaln_appl : forall n e11 e12 e2 v1 v,
    evaln n (Fk e11 e12) v1 ->
    evaln n (Fk (Sm v1) e2) v ->
    evaln (S n) (Fk (Fk e11 e12) e2) v
| evaln_appr : forall n v1 e21 e22 v2 v,
    evaln n (Fk e21 e22) v2 ->
    evaln n (Fk (Sm v1) (Sm v2)) v ->
    evaln (S n) (Fk (Sm v1) (Fk e21 e22)) v
| evaln_to_stem : forall n v2,
    evaln (S n) (Fk (Sm Lf) (Sm v2)) (Sm v2)
| evaln_to_fork : forall n v1 v2,
    evaln (S n) (Fk (Sm (Sm v1)) (Sm v2)) (Fk v1 v2)
| evaln_k : forall n v1 v2,
    evaln (S n) (Fk (Sm (Fk Lf v1)) (Sm v2)) v1
| evaln_s : forall n g f v2 v,
    evaln n (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2))) v ->
    evaln (S n) (Fk (Sm (Fk (Sm g) f)) (Sm v2)) v
| evaln_leaf : forall n f0 f1 f2,
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm Lf)) f0
| evaln_stem : forall n f0 f1 f2 v2 v,
    evaln n (Fk (Sm f1) (Sm v2)) v ->
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm (Sm v2))) v
| evaln_fork : forall n f0 f1 f2 v21 v22 v,
    evaln n (Fk (Fk (Sm f2) (Sm v21)) (Sm v22)) v ->
    evaln (S n) (Fk (Sm ('triage [f0, f1, f2])) (Sm (Fk v21 v22))) v.

Lemma evaln_mono : forall n e v, evaln n e v ->
  forall m, n <= m -> evaln m e v.
Proof.
  intros n e v H; induction H; intros m Hm;
    (destruct m as [|m]; [lia|]);
    econstructor; try apply IHevaln; try apply IHevaln1; try apply IHevaln2;
    lia.
Qed.

Lemma evaln_eval : forall n e v, evaln n e v -> e ==> v.
Proof. intros n e v H; induction H; econstructor; eauto. Qed.

Lemma eval_evaln : forall e v, e ==> v -> exists n, evaln n e v.
Proof.
  intros e v H; induction H;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    try (exists 1; constructor; fail).
  all: try (exists (S x); constructor; assumption).
  all: exists (S (Nat.max x x0));
    first [eapply evaln_appl | eapply evaln_appr];
    eapply evaln_mono; eauto; lia.
Qed.

(** Invert height-indexed evaluations whose expression shape determines
    the rule, as [invert_eval] does for [eval]. *)
Ltac invert_evaln :=
  repeat match goal with
  | H : evaln _ (Sm _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Fk _ _) _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm _) (Fk _ _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm Lf) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Sm _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk Lf _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm (Fk (Fk _ _) _)) (Sm _)) _ |- _ => inv_out H
  | H : evaln _ (Fk Lf _) _ |- _ => inv_out H
  end.

Lemma evaln_lt : forall a k e v, evaln a e v -> a <= k -> evaln k e v.
Proof. intros; eapply evaln_mono; eauto. Qed.

Lemma evaln_appl_pred : forall k e11 e12 e2 v1 v,
  0 < k -> evaln (pred k) (Fk e11 e12) v1 -> evaln (pred k) (Fk (Sm v1) e2) v ->
  evaln k (Fk (Fk e11 e12) e2) v.
Proof. intros; destruct k; [lia|]; apply evaln_appl with (v1 := v1); assumption. Qed.

(** Close a goal [evaln k e v] from height-indexed premises in context:
    either a premise for [e] itself, or a reassembly of an application
    whose argument premise determines the intermediate value. *)
Ltac evaln_close :=
  first
  [ match goal with H : evaln ?a ?e ?v |- evaln ?k ?e ?v =>
      apply (evaln_lt a k e v H); lia end
  | match goal with
    | |- evaln ?k (Fk (Fk ?e11 ?e12) ?e2) ?v =>
        match goal with H2 : evaln ?b (Fk (Sm ?v1) e2) ?v' |- _ =>
          unify v v';
          apply (evaln_appl_pred k e11 e12 e2 v1 v);
          [lia|evaln_close|apply (evaln_lt b _ _ _ H2); lia] end
    end
  | eapply evaln_lt; [eassumption|lia] ].

(** Choose the predecessor height for a goal [exists m, m < n /\ ...]. *)
Ltac exists_pred :=
  match goal with
  | |- exists m, m < ?n /\ _ => exists (pred n); split; [lia|]
  | |- exists m w, m < ?n /\ _ => exists (pred n); eexists; split; [lia|]
  end.

(** Convert all height-indexed hypotheses into ordinary evaluations. *)
Ltac evaln_forget :=
  repeat match goal with H : evaln _ _ _ |- _ =>
    apply evaln_eval in H end.

Local Opaque app inf equal equal1 get_tagname.
Local Opaque abstract_case default_body type_app_stem type_app_S
  triage_case get_name_test.

Lemma abstract_case_none : forall T,
 (forall E N, T <> 'tagged[E,N]) -> abstract_case @ T ==> Lf.
Proof.
  Local Transparent abstract_case.
  intros T Hplain; unfold abstract_case.
  destruct T as [|T|X Y]; try (cbv; evaluate; fail).
  destruct X as [|X|X1 X2]; try (cbv; evaluate; fail).
  exact (type_app_abstract_case_S_none X Y Hplain).
  Local Opaque abstract_case.
Qed.

(** * Height-aware inversion of type application *)

(** Fixpoint unfolding and fallback selection, keeping heights. *)
Lemma Z_evaln_inv : forall n f x v,
  evaln n (Z f @ x) v ->
  exists m w, m < n /\ evaln m (f @ Z f) w /\ evaln m (w @ x) v.
Proof.
  intros n f x v H; unfold Z in H; invert_evaln.
  match goal with
  | H : evaln _ (Fk (Sm dup_z) (Sm _)) _ |- _ =>
      unfold dup_z at 1 in H
  end; invert_evaln.
  match goal with
  | H : evaln _ (Fk (Sm bz) (Sm _)) _ |- _ =>
      unfold bz in H
  end; invert_evaln.
  exists_pred; split; [|evaln_close]; unfold Z; evaln_close.
Qed.


Lemma extend_program_evaln_inv : forall n p f x r,
  evaln n (extend_program @ p @r f @r x) r ->
  (exists v, p @ x ==> Sm v /\ r = v) \/
  (p @ x ==> Lf /\ exists m, m < n /\ evaln m (f @ x) r) \/
  (exists l q, p @ x ==> Fk l q /\ r = Lf).
Proof.
  Local Transparent extend_program.
  intros n p f x r H; unfold extend_program in H; cbn in H.
  invert_evaln.
  all: try solve [left; eexists; split; [evaln_forget; eassumption|reflexivity]].
  all: try solve [right; right; do 2 eexists; split; [evaln_forget; eassumption|reflexivity]].
  right; left; split; [evaln_forget; eassumption|].
  exists_pred; evaln_close.
  Local Opaque extend_program.
Qed.

Local Transparent app.
Lemma app_partial_evaln : forall AI n F w,
  (forall E N, F <> 'tagged[E,N]) ->
  evaln n (app AI @ F) w ->
  exists m, m < n /\ evaln m (default_body AI @ app AI @r F) w.
Proof.
  intros AI n F w Hplain H.
  unfold type_app in H.
  destruct (Z_evaln_inv _ _ _ _ H) as [m [b [Hm [Hb Hw]]]]; clear H.
  change (Z (body AI)) with (type_app AI) in Hb, Hw.
  remember (type_app AI) as A eqn:HA.
  rewrite body_components in Hb; cbn in Hb.
  invert_evaln.
  (* a leaf or a stem: the ordinary clauses at once *)
  all: try solve [exists (pred n); split; [lia|evaln_close]].
  (* a fork: the F-level clause, then the ordinary clauses *)
  match goal with Hp : forall E N, ?F0 <> 'tagged[E,N] |- _ => set (F := F0) in * end.
  match goal with
  | H10 : evaln _ (extend_program @ ?p) ?v0,
    H9 : evaln _ (?v0 @ ?d) ?v1,
    H8 : evaln _ (?v1 @ F) w |- _ =>
    assert (HE : evaln (pred n)
      (extend_program @ p @r d @r F) w)
      by evaln_close
  end.
  destruct (extend_program_evaln_inv _ _ _ _ _ HE) as [[v [HS _]]|[[_ [k [Hk Hk']]]|[l [q [HS _]]]]].
  1,3: pose proof (eval_deterministic _ _ HS _ (wait_abstract_wait_plain _ F Hplain)); discriminate.
  exists (pred n); split; [lia|evaln_close].
Qed.
Local Opaque app.

(** Off tagged function types, type application is the application of
    the default clauses, at smaller height. *)
Lemma app_evaln_head : forall AI n F U R,
  (forall E N, F <> 'tagged[E,N]) ->
  evaln n (app AI @ F @r U) R ->
  exists m w, m < n /\ evaln m (default_body AI @ app AI @r F) w /\ evaln m (w @ U) R.
Proof.
  intros AI n F U R Hplain H.
  inv_out H.
  match goal with
  | H1 : evaln _ (Fk (Sm (app AI)) (Sm F)) ?w,
    H2 : evaln ?k (Fk (Sm ?w) (Sm U)) R |- _ =>
    destruct (app_partial_evaln AI _ F w Hplain H1) as [m [Hm HD]]
  end.
  exists n0; eexists; split; [lia|split; [evaln_close|eassumption]].
Qed.


Local Opaque equal index_check.


(** Function introduction from a direct carrier. *)
Lemma function_abstractor_direct_eval : forall type_app0 F U V,
  type_app0 @ F @r U ==> Sm V ->
  function_abstractor_core @ 'decorate[F,U] @r type_app0 ==>
    Sm (funty_eliminator U V).
Proof.
  Local Transparent function_abstractor_core.
  intros type_app0 F U V Htype; inv_out Htype; split_all.
  eapply eval_appl.
  - unfold function_abstractor_core; eapply extend_some.
    unfold check_function_direct; cbn.
    repeat first [apply get_decorate_some | progress evaluate].
  - repeat first [progress evaluate | eassumption].
  Local Opaque function_abstractor_core.
Qed.


(** * Components of types

    A component of a type is reached through stems, untagged forks and the
    parameters of tagged types (one rule for every family: the arrow
    domains and codomains and the query result types are instances). *)
Inductive type_component : Combination -> Combination -> Prop :=
| component_refl : forall T, type_component T T
| component_stem : forall S X, type_component S X -> type_component S (Sm X)
| component_fork_left : forall S X Y,
    (forall E N, Fk X Y <> 'tagged[E,N]) ->
    type_component S X -> type_component S (Fk X Y)
| component_fork_right : forall S X Y,
    (forall E N, Fk X Y <> 'tagged[E,N]) ->
    type_component S Y -> type_component S (Fk X Y)
| component_param : forall S E X N,
    type_component S X -> type_component S ('tagged['wait[E,X],N]).


Lemma component_pair_left : forall S A B,
  type_component S A -> type_component S (A '* B).
Proof.
  intros S A B H.
  apply component_fork_left; [intros ? ? ?; discriminate|].
  apply component_stem, component_fork_right; [intros ? ? ?; discriminate|].
  apply component_fork_right; [intros ? ? ?; discriminate|exact H].
Qed.

Lemma component_pair_right : forall S A B,
  type_component S B -> type_component S (A '* B).
Proof.
  intros S A B H.
  apply component_fork_right; [intros ? ? ?; discriminate|].
  apply component_fork_right; [intros ? ? ?; discriminate|exact H].
Qed.

Lemma component_domain : forall S U V,
  type_component S U -> type_component S ('tagged[funty_eliminator U V,fun_nm]).
Proof. intros; apply component_param, component_pair_left; assumption. Qed.

Lemma component_codomain : forall S U V,
  type_component S V -> type_component S ('tagged[funty_eliminator U V,fun_nm]).
Proof. intros; apply component_param, component_pair_right; assumption. Qed.

Lemma component_query : forall S B,
  type_component S B -> type_component S ('tagged[query_eliminator B,query_nm]).
Proof. intros; apply component_param; assumption. Qed.

(** Find a component path; untagged side conditions are discharged by
    computation. *)
Ltac component_tac :=
  first
  [ apply component_refl
  | apply component_stem; component_tac
  | apply component_query; component_tac
  | apply component_domain; component_tac
  | apply component_codomain; component_tac
  | apply component_fork_left; [intros ? ? ?; discriminate|component_tac]
  | apply component_fork_right; [intros ? ? ?; discriminate|component_tac] ].


Unset Default Proof Using.
Transparent app inf equal equal1 get_tagname abstract_case extend_program default_body type_app_S type_app_stem function_abstractor_core.

(** Evaluation preserves typing, relative to a sound declarations.

    typing.v supplies the auxiliary programs and their recognition facts,
    application and inversion lemmas, inference and its inversions.

    The proof has three ingredients before the main evaluation induction:
    name tests agree on typed values and their types; child reconstruction
    preserves each node's inferred type; and the core direct and recursive
    function constructors are sound.  Wrapper lookup refuses fun_nm, which
    is always dispatched to the core function handler.  The declarations
    have one obligation ([ontology_sound]): at an index, every eliminator
    it makes is sound for values (a carrier applied to a value of the
    argument type yields a value of the result type).

    eval_tree retains the preservation property at every evaluation subtree.
    The final section makes
    abstract-introduction soundness compositional. *)
From TreeTyping Require Import tree.
From TreeTyping Require Import typing.
From TreeTyping Require Import typing.
From Stdlib Require Import String.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque app inf equal equal1 get_tagname.
Definition inhabited (AI U : Combination) : Prop :=
 exists u, inf AI @ u ==> Sm U.

(** Name-test preservation: recover the runtime name and relate its test
    to the test performed on the inferred argument type. *)
Lemma infer_name_test_inv : forall AI m N,
 inf AI @ m ==> Sm (name_test N) ->
 exists n, m = name_test n /\ inf AI @ n ==> Sm N.
Proof.
 intros AI m N H; unfold name_test in H.
 destruct (infer_S2_inv AI m ('K1 ('wait[equal,Sm N])) get_tagname ltac:(intros;discriminate) H)
   as [g [f [-> [Hg Hf]]]].
 pose proof (infer_tag_free_inv AI f get_tagname Hf ltac:(tag_free_tac)) as ->.
 destruct (infer_K1_inv AI g _ Hg) as [w [-> Hw]].
 destruct (infer_S2_inv AI w ('S2['K1 equal,'K1 (Sm N)]) ('I) ltac:(intros;discriminate) Hw)
   as [a [i [-> [Ha Hi]]]].
 pose proof (infer_tag_free_inv AI i ('I) Hi ltac:(tag_free_tac)) as ->.
 destruct (infer_S2_inv AI a ('K1 equal) ('K1 (Sm N)) ltac:(intros;discriminate) Ha)
   as [e [sn [-> [He Hsn]]]].
 pose proof (infer_tag_free_inv AI e ('K1 equal) He ltac:(tag_free_tac)) as ->.
 destruct (infer_K1_inv AI sn _ Hsn) as [s [-> Hs]].
 destruct (infer_stem_result_inv AI s N Hs) as [n [-> Hn]].
 exists n; split; [reflexivity|exact Hn].
Qed.

(** The equal1 presentation is used only to reason about the same name test. *)
Definition tag_matches N := equal1 (Sm N) 'C get_tagname.

Lemma tag_matches_hit : forall N C,
 tag_matches N @ ('tagged[C,N]) ==> 'K.
Proof.
 intros; pose proof (get_tagname_some C N).
 unfold tag_matches; repeat first [eassumption|apply equal1_eq|progress evaluate].
Qed.

Lemma tag_matches_miss : forall N u,
 (forall C, u <> 'tagged[C,N]) -> tag_matches N @ u ==> 'KI.
Proof.
 intros N u H.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - pose proof (get_tagname_some C M).
   assert (Sm N <> Sm M) by (intro HE; inversion HE; subst; eapply H; reflexivity).
   unfold tag_matches; repeat first [eassumption|apply equal1_neq; assumption|progress evaluate].
 - pose proof (get_tagname_none u Hplain).
   unfold tag_matches; repeat first [eassumption|apply equal1_neq; discriminate|progress evaluate].
Qed.

(** [name_test_tag_hit] and [name_test_tag_miss] live in typing.v. *)
Lemma name_test_equivalent : forall N u b,
 name_test N @ u ==> b <-> tag_matches N @ u ==> b.
Proof.
 intros N u b.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + split; intro H.
     * pose proof (eval_deterministic _ _ H _ (name_test_tag_hit M C)) as ->; apply tag_matches_hit.
     * pose proof (eval_deterministic _ _ H _ (tag_matches_hit M C)) as ->; apply name_test_tag_hit.
   + assert (HM : forall D, 'tagged[C,M] <> 'tagged[D,N]) by (intros D HE; inversion HE; congruence).
     split; intro H.
     * pose proof (eval_deterministic _ _ H _ (name_test_tag_miss N _ HM)) as ->; apply tag_matches_miss; exact HM.
     * pose proof (eval_deterministic _ _ H _ (tag_matches_miss N _ HM)) as ->; apply name_test_tag_miss; exact HM.
 - assert (HM : forall C, u <> 'tagged[C,N]) by eauto.
   split; intro H.
   + pose proof (eval_deterministic _ _ H _ (name_test_tag_miss N _ HM)) as ->; apply tag_matches_miss; exact HM.
   + pose proof (eval_deterministic _ _ H _ (tag_matches_miss N _ HM)) as ->; apply name_test_tag_miss; exact HM.
Qed.

Lemma tag_free_tag_iff : forall AI u U N,
 tag_free N = true -> infer AI @ u ==> Sm U ->
 ((exists f, u = 'tagged[f,N]) <-> (exists E, U = 'tagged[E,N])).
Proof.
 intros AI u U N HN HU; split.
 - intros [f ->].
   destruct (infer_tagged_source_inv AI f N U HU)
     as [C [M [E [-> [HC [HM HE]]]]]].
   pose proof (infer_tag_free AI N HN) as Hself.
   pose proof (eval_deterministic _ _ HM _ Hself) as HH.
   inversion HH; subst M; eauto.
 - intros [E ->].
   destruct (infer_tagged_result_inv AI u E N HU)
     as [f [n [C [-> [HC [Hn HE]]]]]].
   pose proof (infer_tag_free_inv AI n N Hn HN) as ->; eauto.
Qed.

Lemma tag_test_preservation : forall AI N u U b,
 tag_free N = true -> infer AI @ u ==> Sm U ->
 tag_matches N @ U ==> b -> tag_matches N @ u ==> b.
Proof.
 intros AI N u U b HN HU HB.
 destruct (tagged_decide U) as [[E [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + pose proof (eval_deterministic _ _ HB _ (tag_matches_hit M E)) as ->.
     destruct (proj2 (tag_free_tag_iff AI u ('tagged[E,M]) M HN HU)
       ltac:(eauto)) as [f ->]; apply tag_matches_hit.
   + assert (HM : forall C, 'tagged[E,M] <> 'tagged[C,N]) by (intros C HE; inversion HE; congruence).
     pose proof (eval_deterministic _ _ HB _ (tag_matches_miss N _ HM)) as ->.
     apply tag_matches_miss; intros C HC.
     destruct (proj1 (tag_free_tag_iff AI u ('tagged[E,M]) N HN HU)
       ltac:(eauto)) as [D HD]; inversion HD; congruence.
 - assert (HM : forall C, U <> 'tagged[C,N]) by eauto.
   pose proof (eval_deterministic _ _ HB _ (tag_matches_miss N U HM)) as ->.
   apply tag_matches_miss; intros C HC.
   destruct (proj1 (tag_free_tag_iff AI u U N HN HU) ltac:(eauto))
     as [E HE]; eapply Hplain; exact HE.
Qed.

(** The name test fires only at concrete names, so only the concrete case
    of name-test preservation is needed. *)
Lemma inferred_name_test_preservation : forall AI n N u U B,
 tag_free N = true -> inf AI @ n ==> Sm N ->
 inf AI @ u ==> Sm U -> name_test N @ U ==> B -> name_test n @ u ==> B.
Proof.
 intros AI n N u U B HN Hn Hu HB.
 pose proof (infer_tag_free_inv AI n N Hn HN) as ->.
 apply name_test_equivalent; eapply tag_test_preservation;
   [exact HN|exact Hu|apply name_test_equivalent;exact HB].
Qed.

Lemma tag_matches_boolean : forall N u b,
 tag_matches N @ u ==> b -> b = 'K \/ b = 'KI.
Proof.
 intros N u b H.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + left; eapply eval_deterministic; [exact H|apply tag_matches_hit].
   + right; eapply eval_deterministic; [exact H|apply tag_matches_miss].
     intros D HE; inversion HE; congruence.
 - right; eapply eval_deterministic; [exact H|apply tag_matches_miss].
   intros C HE; eapply Hplain; exact HE.
Qed.

(* ================================================================== *)
(** * Wrappers *)
(* ================================================================== *)

(** A wrapper family is given by a concrete payload program [p] with
    [p @ Lf ==> Sm T]; the abstract payload type [T] need not be stored in
    the declarations.  Its abstractor maps the carrier [swap T] to the
    eliminator [wrap_eliminator T], which applies the type of an action to
    [T] by type application. *)

Local Opaque equal equal1 get_wait.
Local Ltac run_hw := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|apply get_wait_some|
 evaluate_expr_core run_hw run_head_hw|idtac]
with run_head_hw := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|
 evaluate_head_core run_hw|idtac].


Lemma fixed_payload_eval : forall T, fixed_payload T @ Lf ==> Sm T.
Proof. intros; unfold fixed_payload; evaluate. Qed.

Lemma computed_wrap_abstractor_some : forall p T,
 p @ Lf ==> Sm T -> computed_wrap_abstractor p @ swap T ==> Sm (wrap_eliminator T).
Proof.
 intros; unfold computed_wrap_abstractor, wrap_abstractor_body, wrap_eliminator;
 apply wait_eval; run_hw.
Qed.


Lemma computed_wrap_abstractor_inv : forall p C E,
 computed_wrap_abstractor p @ C ==> Sm E ->
 exists T, p @ Lf ==> Sm T /\ C = swap T /\ E = wrap_eliminator T.
Proof.
 intros p C E H; unfold computed_wrap_abstractor in H; apply wait_eval_inv in H.
 unfold wrap_abstractor_body in H; invert_eval; repeat progress recognizer_eqtac.
 all: eexists; repeat split; eassumption.
Qed.

Lemma wrap_abstractor_inv : forall T C E,
  wrap_abstractor T @ C ==> Sm E ->
  C = ('S2['I,'K1 T]) /\ E = wrap_eliminator T.
Proof.
  intros T C E H; destruct (computed_wrap_abstractor_inv _ _ _ H) as [T' [HT [-> ->]]].
  pose proof (eval_deterministic _ _ HT _ (fixed_payload_eval T)) as HE; inversion HE.
  split; reflexivity.
Qed.


(** Applying [swap T] to [T --> V] gives [V]. *)
Lemma type_app_swap : forall AI T V,
  type_app AI @ swap T @r (T --> V) ==> Sm V.
Proof.
  intros; unfold swap; eapply app_S;
  [intros;discriminate|apply get_name_test_S_right;discriminate|apply app_I|apply app_K|].
  apply app_abstract; apply funty_eliminator_eval.
Qed.


(** ** Wrapper lookup

    The lookup reads the payload program [p] from the abstractor
    (path [path_payload]), rebuilds the abstractor
    [computed_wrap_abstractor p] and compares it with the answer of the declarations;
    on a match it runs [p]. *)


Lemma get_payload_program_eval : forall p,
  get_payload_program @ ('K1 (computed_wrap_abstractor p)) ==> p.
Proof.
  intros; unfold get_payload_program.
  exact (path_eval path_payload ('K1 (computed_wrap_abstractor p))).
Qed.


Lemma computed_wrap_builder_eval : forall p,
  computed_wrap_builder @ p ==> ('K1 (computed_wrap_abstractor p)).
Proof.
  intros; unfold computed_wrap_builder, computed_wrap_abstractor; evaluate.
Qed.

Local Opaque computed_wrap_builder get_payload_program.
Local Lemma equal1_eq' : forall p q, p = q -> equal1 p @ q ==> 'K.
Proof. intros p q <-; apply equal1_eq. Qed.

Lemma get_computed_payload_some : forall p T,
 p @ Lf ==> Sm T -> get_computed_payload @ ('K1 (computed_wrap_abstractor p)) ==> Sm T.
Proof.
 intros; pose proof (get_payload_program_eval p).
 pose proof (computed_wrap_builder_eval p).
 unfold get_computed_payload; run_hw.
Qed.

Lemma get_computed_payload_inv : forall C T,
 get_computed_payload @ C ==> Sm T ->
 exists p, C = ('K1 (computed_wrap_abstractor p)) /\ p @ Lf ==> Sm T.
Proof.
 intros C T H; unfold get_computed_payload in H; invert_eval.
 pose proof (path_eval path_payload C) as HP.
 change (get_payload_program @ C ==> path_fn path_payload C) in HP.
 repeat match goal with
 | H1 : get_payload_program @ C ==> ?x |- _ =>
     pose proof (eval_deterministic _ _ H1 _ HP); subst x; clear H1
 end.
 pose proof (computed_wrap_builder_eval (path_fn path_payload C)) as HB.
 repeat match goal with
 | H1 : computed_wrap_builder @ path_fn path_payload C ==> ?x |- _ =>
     pose proof (eval_deterministic _ _ H1 _ HB); subst x; clear H1
 end.
 match goal with H1 : equal @ C ==> ?e |- _ =>
   pose proof (eval_deterministic _ _ H1 _ (equal_eval C)); subst e; clear H1 end.
 match goal with H1 : equal1 C @ ?R ==> ?b |- _ =>
   destruct (combination_eq_dec C R) as [Heq|Hneq];
   [ pose proof (eval_deterministic _ _ H1 _ (equal1_eq' C R Heq))
   | pose proof (eval_deterministic _ _ H1 _ (equal1_neq C R Hneq)) ];
   subst b; clear H1; invert_eval
 end.
 all: eexists; split; [exact Heq|eassumption].
Qed.

Local Opaque get_computed_payload.
(** declarations entry for a wrapper at N: a fixed or a computed payload. *)
Definition wrapper_entry AI N T :=
 AI @ N ==> ('K1 (wrap_abstractor T)) \/
 exists p, AI @ N ==> ('K1 (computed_wrap_abstractor p)) /\ p @ Lf ==> Sm T.
Definition declared_wrapper AI N T := wrapper_entry AI N T.
Lemma wrapper_lookup_some : forall AI N T,
 wrapper_entry AI N T -> wrapper_lookup AI @ N ==> Sm T.
Proof.
 intros AI N T [HO|[p [HI HP]]]; unfold wrapper_lookup.
 - pose proof (get_computed_payload_some _ T (fixed_payload_eval T)); evaluate.
 - pose proof (get_computed_payload_some p T HP); evaluate.
Qed.
Lemma wrapper_lookup_inv : forall AI N T,
 wrapper_lookup AI @ N ==> Sm T -> wrapper_entry AI N T.
Proof.
 intros AI N T H; unfold wrapper_lookup in H; invert_eval.
 match goal with H : get_computed_payload @ _ ==> Sm _ |- _ =>
   apply get_computed_payload_inv in H; destruct H as [p [-> HP]] end.
 right; exists p; split; assumption.
Qed.
Local Opaque wrapper_lookup equal1.
Lemma get_wrap_payload_type_some : forall AI N T,
 declared_wrapper AI N T -> get_wrap_payload_type AI @ N ==> Sm T.
Proof. intros AI N T H; apply wrapper_lookup_some; exact H. Qed.
Lemma get_wrap_payload_type_inv : forall AI N T,
 get_wrap_payload_type AI @ N ==> Sm T -> declared_wrapper AI N T.
Proof. intros AI N T H; apply wrapper_lookup_inv; exact H. Qed.
Local Transparent get_wait computed_wrap_builder get_payload_program get_computed_payload wrapper_lookup index_check.


(** One-level reconstruction preserves the inferred child types. *)
Lemma inf_children_inv : forall AI f0 f1 f2,
 inf AI @ 'triage[f0,f1,f2] ==> Sm (update_one_level ('Update)) ->
 inf AI @ f0 ==> Sm Lf /\ inf AI @ f1 ==> Sm (Lf 'C ('Update)) /\
 inf AI @ f2 ==> Sm (update_fork ('Update)).
Proof.
 intros AI f0 f1 f2 H; unfold update_one_level in H.
 destruct (typing.infer_plain_fork_inv AI _ (Fk Lf (Lf 'C ('Update)))
  (update_fork ('Update)) ltac:(intros;discriminate) H)
 as [l [r [HE [Hl Hr]]]].
 inversion HE; subst l r.
 destruct (typing.infer_plain_fork_inv AI _ Lf (Lf 'C ('Update)) ltac:(intros;discriminate) Hl)
 as [a [b [HE' [Ha Hb]]]].
 inversion HE'; subst a b; repeat split; assumption.
Qed.

Lemma children_reduct_typing : forall AI f0 f1 f2 x X,
 inf AI @ 'triage[f0,f1,f2] ==> Sm (update_one_level ('Update)) ->
 inf AI @ x ==> Sm X ->
 match x with
 | Lf => inf AI @ f0 ==> Sm X
 | Sm y => infer_expression AI @ (f1 @ y) ==> Sm X
 | Fk y z => infer_expression AI @ (f2 @ y @r z) ==> Sm X
 end.
Proof.
 intros AI f0 f1 f2 x X Htriage Hx.
 destruct (inf_children_inv AI f0 f1 f2 Htriage) as [H0 [H1 H2]].
 destruct x as [|y|y z].
 - pose proof (eval_deterministic _ _ Hx _ (typing.inf_leaf AI)) as HE;
   inversion HE; subst; exact H0.
 - destruct (typing.infer_stem_inv AI _ _ Hx) as [Y [-> Hy]].
   eapply infer_expression_fork;
   [apply infer_expression_stem; exact H1|apply infer_expression_stem; exact Hy|
    apply app_update_stem].
 - destruct (typing.infer_fork_inv AI _ _ _ Hx) as [Y [Z [Hy [Hz HP]]]].
   eapply infer_expression_fork.
   + eapply infer_expression_fork;
     [apply infer_expression_stem; exact H2|apply infer_expression_stem; exact Hy|
      apply app_update_fork_first].
   + apply infer_expression_stem; exact Hz.
   + apply app_update_fork_second; exact HP.
Qed.

(** The two function-introduction cases handled by the core. *)
Section FunctionSoundnessFacts.
Variable AI : Decl.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).
Lemma type_app_stem_recursive_function : forall app U V,
  type_app_stem @ app
    @r (Sm ('K1 (Z (((U --> V) --> (U --> V)) 'C tagged_fun))))
    @r ('S2['K,'K1 fun_nm]) ==> Sm (U --> V).
Proof using AI.
  intros; apply type_app_stem_tagged; apply function_declared.
  apply function_abstractor_recursive_eval.
Qed.

Lemma type_app_tagged_fun_recursive : forall A B,
  tagged_fun # Z (((A --> B) --> (A --> B)) 'C tagged_fun) ==>
    Sm (A --> B).
Proof using AI.
  intros A B; unfold tagged_fun.
  repeat first
    [ new_S; [discriminate | | |]
    | eapply type_app_K_ev
    | eapply type_app_stem_ev; apply type_app_stem_recursive_function
    | eapply type_app_stem_ev; eapply type_app_stem_structural; intros; discriminate
    | eapply type_app_leaf_ev ].
Qed.

Lemma recursive_function_carrier_type_app : forall A B,
  Z (((A --> B) --> (A --> B)) 'C tagged_fun) # A ==> Sm B.
Proof using AI.
  intros A B; eapply type_app_Z.
  - eapply typing.app_compose;[solve [reject_name]| | |].
    + intros; discriminate.
    + apply type_app_tagged_fun_recursive.
    + apply type_app_abstract; apply funty_eliminator_eval.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.

Lemma function_abstractor_core_sound : forall C E U V,
  function_abstractor_core @ C @r type_app ==> Sm E ->
  E @ type_app @r U ==> Sm V -> C # U ==> Sm V.
Proof using AI.
  intros C E U V HC HE.
  destruct (function_abstractor_success_inv _ _ _ HC)
    as [[F [A [B [-> [HF ->]]]]] | [A [B [-> ->]]]].
  - apply funty_eliminator_inv in HE; destruct HE as [-> ->].
    eapply type_app_wait; [apply type_app_K_ev|exact HF].
  - apply funty_eliminator_inv in HE; destruct HE as [-> ->].
    apply recursive_function_carrier_type_app.
Qed.

(** Function type introduction is sound by typing, in declarations with the row. *)
Theorem function_abstractor_sound : forall C E U V,
  function_abstractor @ type_app @r C ==> Sm E ->
  E @ type_app @r U ==> Sm V -> C # U ==> Sm V.
Proof using AI.
  intros C E U V HC HE.
  exact (function_abstractor_core_sound C E U V (function_abstractor_eval_inv _ _ _ HC) HE).
Qed.

End FunctionSoundnessFacts.

Local Opaque equal1.
(** Retain the preservation hypothesis at every evaluation subtree. *)
Inductive eval_tree (P : Combination -> Combination -> Prop) :
  Combination -> Combination -> Prop :=
| tree_val : forall v, P (Sm v) v -> eval_tree P (Sm v) v
| tree_appl : forall e11 e12 e2 v1 v,
    eval_tree P (Fk e11 e12) v1 -> eval_tree P (Fk (Sm v1) e2) v ->
    P (Fk (Fk e11 e12) e2) v -> eval_tree P (Fk (Fk e11 e12) e2) v
| tree_appr : forall v1 e21 e22 v2 v,
    eval_tree P (Fk e21 e22) v2 -> eval_tree P (v1 @ v2) v ->
    P (Fk (Sm v1) (Fk e21 e22)) v -> eval_tree P (Fk (Sm v1) (Fk e21 e22)) v
| tree_to_stem : forall v2, P (Lf @ v2) (Sm v2) -> eval_tree P (Lf @ v2) (Sm v2)
| tree_to_fork : forall v1 v2, P (Sm v1 @ v2) (Fk v1 v2) ->
    eval_tree P (Sm v1 @ v2) (Fk v1 v2)
| tree_k : forall v1 v2, P (('K1 v1) @ v2) v1 -> eval_tree P (('K1 v1) @ v2) v1
| tree_s : forall g f x v,
    eval_tree P (Fk (g @ x) (f @ x)) v ->
    P ('S2[g,f] @ x) v -> eval_tree P ('S2[g,f] @ x) v
| tree_leaf : forall f0 f1 f2, P ('triage[f0,f1,f2] @ Lf) f0 ->
    eval_tree P ('triage[f0,f1,f2] @ Lf) f0
| tree_stem : forall f0 f1 f2 x v,
    eval_tree P (f1 @ x) v -> P ('triage[f0,f1,f2] @ Sm x) v ->
    eval_tree P ('triage[f0,f1,f2] @ Sm x) v
| tree_fork : forall f0 f1 f2 x y v,
    eval_tree P (f2 @ x @r y) v -> P ('triage[f0,f1,f2] @ Fk x y) v ->
    eval_tree P ('triage[f0,f1,f2] @ Fk x y) v.

Lemma eval_tree_root : forall P e v, eval_tree P e v -> P e v.
Proof. intros P e v H; inversion H; assumption. Qed.

Section Soundness.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (inf AI).
Local Abbreviation infer_expression := (infer_expression AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).
Lemma tagged_carrier_redex_typing :
  forall g f u T G F C N U,
    infer @ g ==> Sm G ->
    infer @ f ==> Sm F ->
    infer @ u ==> Sm U ->
    'S2[G,F] = 'tagged[C,N] ->
    C # U ==> Sm T ->
    infer_expression @ Fk (g @ u) (f @ u) ==> Sm T.
Proof.
  intros g f u T G F C N U HG HF HU Htag Hcarrier.
  inv_out Htag.
  eapply typing.infer_expression_fork.
  eapply typing.infer_expression_fork.
  eapply typing.infer_expression_stem; eauto.
  eapply typing.infer_expression_stem; eauto.
  eapply typing.app_K.
  eapply typing.infer_expression_fork.
  eapply typing.infer_expression_stem; eauto.
  eapply typing.infer_expression_stem; eauto.
  new_S. discriminate.
  eapply typing.app_stem.
  eapply type_app_stem_structural; intros; discriminate.
  eapply typing.app_K.
  eapply typing.app_K.
  auto.
Qed.


(** Query application may be used compositionally inside the stem and fork
    reducts of triage. *)
Lemma query_expression_application_typing : forall e u B U,
  infer_expression @ e ==> Sm ('Query[B]) ->
  infer_expression @ u ==> Sm U ->
  infer_expression @ Fk e u ==> Sm B.
Proof.
  intros e u B U He Hu.
  eapply typing.infer_expression_fork; eauto.
  eapply typing.app_abstract.
  apply query_eliminator_eval.
Qed.

Lemma query_triage_reduct_typing : forall f0 f1 f2 x T X,
  infer @ ('triage[f0,f1,f2]) ==> Sm (query_one_level T) ->
  infer @ x ==> Sm X ->
  match x with
  | Lf => infer @ f0 ==> Sm T
  | Sm y => infer_expression @ (f1 @ y) ==> Sm T
  | Fk y z => infer_expression @ (f2 @ y @r z) ==> Sm T
  end.
Proof.
  intros f0 f1 f2 x T X Htriage Hx.
  destruct (typing.infer_triage_inv AI f0 f1 f2 T Htriage) as [Hf0 [Hf1 Hf2]].
  destruct x as [|y|y z].
  - exact Hf0.
  - destruct (typing.infer_stem_inv AI _ _ Hx) as [Y [HX Hy]].
    inversion HX; subst X.
    eapply query_expression_application_typing.
    + eapply typing.infer_expression_stem; exact Hf1.
    + eapply typing.infer_expression_stem; exact Hy.
  - destruct (typing.infer_fork_inv AI _ _ _ Hx) as [Y [Z [Hy [Hz Hpair]]]].
    eapply query_expression_application_typing.
    + eapply query_expression_application_typing.
      * eapply typing.infer_expression_stem; exact Hf2.
      * eapply typing.infer_expression_stem; exact Hy.
    + eapply typing.infer_expression_stem; exact Hz.
Qed.

Lemma structural_triage_reduct_typing : forall f0 f1 f2 F0 F1 F2 x X T,
  infer @ 'triage[f0,f1,f2] ==> Sm ('triage[F0,F1,F2]) ->
  infer @ x ==> Sm X ->
  (((forall E N, Fk F0 F1 <> 'tagged[E,N]) /\
    ((X = Lf /\ T = F0) \/ (exists N, X = Sm N /\ type_app @ F1 @r N ==> Sm T))) \/
    (exists L R G, X = Fk L R /\
      (forall E N, Fk L R <> 'tagged[E,N]) /\
      type_app @ F2 @r L ==> Sm G /\ type_app @ G @r R ==> Sm T)) ->
  match x with
  | Lf => infer @ f0 ==> Sm T
  | Sm y => infer_expression @ (f1 @ y) ==> Sm T
  | Fk y z => infer_expression @ (f2 @ y @r z) ==> Sm T
  end.
Proof.
  intros f0 f1 f2 F0 F1 F2 x X T Htriage Hx Hcase.
  destruct (typing.infer_plain_fork_inv AI _ (Fk F0 F1) F2
    ltac:(intros; discriminate) Htriage) as [p [q [HE [Hp Hq]]]].
  inversion HE; subst p q; clear HE.
  destruct Hcase as [[Hplain HC]|[L [R [G [-> [HP [HL HR]]]]]]].
  - destruct (typing.infer_plain_fork_inv AI _ F0 F1 Hplain Hp)
    as [a [b [HE [Ha Hb]]]].
  inversion HE; subst a b; clear HE.
  destruct HC as [[-> ->]|[N [-> Hstep]]].
  + pose proof (typing.infer_tag_free_inv AI x Lf Hx eq_refl) as ->; exact Ha.
  + destruct (infer_stem_result_inv AI x N Hx) as [y [-> Hy]].
    eapply typing.infer_expression_fork.
    * apply typing.infer_expression_stem; exact Hb.
    * apply typing.infer_expression_stem; exact Hy.
    * exact Hstep.
  - destruct (typing.infer_plain_fork_inv AI x L R HP Hx)
      as [y [z [-> [Hy Hz]]]].
    eapply typing.infer_expression_fork.
    + eapply typing.infer_expression_fork.
      * apply typing.infer_expression_stem; exact Hq.
      * apply typing.infer_expression_stem; exact Hy.
      * exact HL.
    + apply typing.infer_expression_stem; exact Hz.
    + exact HR.
Qed.

Lemma triage_application_typing : forall f0 f1 f2 x T,
 infer_expression @ ('triage[f0,f1,f2] @ x) ==> Sm T ->
 exists X, infer @ x ==> Sm X /\
 ((exists F0 F1 F2,
   infer @ 'triage[f0,f1,f2] ==> Sm ('triage[F0,F1,F2]) /\
   (((forall E N, Fk F0 F1 <> 'tagged[E,N]) /\
     ((X = Lf /\ T = F0) \/
      (exists N, X = Sm N /\ type_app @ F1 @r N ==> Sm T))) \/
    (exists L R G, X = Fk L R /\
      (forall E N, Fk L R <> 'tagged[E,N]) /\
      type_app @ F2 @r L ==> Sm G /\ type_app @ G @r R ==> Sm T))) \/
 infer @ 'triage[f0,f1,f2] ==> Sm (query_one_level T) \/
 (T = X /\ infer @ 'triage[f0,f1,f2] ==> Sm (update_one_level ('Update)))).
Proof.
 intros f0 f1 f2 x T Htyping.
 destruct (typing.infer_expression_fork_inv AI _ _ _ Htyping)
   as [Q [X [Hfunction [Harg Happ]]]].
 apply typing.infer_expression_stem_inv in Hfunction.
 apply typing.infer_expression_stem_inv in Harg.
 exists X; split; [exact Harg|].
 destruct (typing.infer_triage_shape AI _ _ _ _ Hfunction) as [B [Q1 [Q2 ->]]].
 pose proof (app_plain_inv AI _ _ _ (abstract_case_triage_none B Q1 Q2) Happ) as HD.
 apply default_triage_inv in HD.
 pose proof (triage_case_inv _ _ _ _ _ _ HD) as HS.
 pose proof (structural_triage_inv _ _ _ _ _ _ HS) as HC.
 left; exists B,Q1,Q2; split; assumption.
Qed.


(** * Plain soundness

    declarations needs agreement on every argument type. *)
Definition plain_intro_sound : Prop :=
  forall C N E U V,
    AI @ N @r type_app @r C ==> Sm E -> E @ type_app @r U ==> Sm V ->
    type_app @ C @r U ==> Sm V.

Lemma plain_tagged_redex_typing :
  forall g f u T g_ty f_ty C N,
    plain_intro_sound ->
    infer @ g ==> Sm g_ty ->
    infer @ f ==> Sm f_ty ->
    'S2[g_ty,f_ty] = 'tagged[C,N] ->
    infer_expression @ (('S2[g,f]) @ u) ==> Sm T ->
    infer_expression @ Fk (g @ u) (f @ u) ==> Sm T.
Proof.
  intros g f u T G F C N Hplain HG HF Htag Htyping.
  destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
    as [function_ty [U
      [Hfunction_expr [Hargument_expr Hfinal_app]]]].
  pose proof
    (typing.infer_expression_stem_inv _ _ _ Hfunction_expr) as Hfunction.
  pose proof
    (typing.infer_expression_stem_inv _ _ _ Hargument_expr) as Hargument.
  destruct (typing.infer_fork_inv _ _ _ _ Hfunction)
    as [left_ty [f_ty [Hleft [Hf Hconstructor_app]]]].
  destruct (typing.infer_stem_inv _ _ _ Hleft)
    as [g_ty [Hleft_ty Hg]].
  subst left_ty.
  assert (Sm g_ty = Sm G) by (eapply eval_deterministic; eauto).
  inversion H; subst g_ty; clear H.
  assert (Sm f_ty = Sm F) by (eapply eval_deterministic; eauto).
  inversion H; subst f_ty; clear H.
  assert(Hadapt :
    type_app_stem @ type_app @r (Sm G) @r F ==> Sm function_ty).
  { eapply typing.app_stem_inv; eauto. }
  inversion Htag; subst G F.
  destruct (type_app_stem_tagged_success_inv
    AI type_app C N function_ty Hadapt)
    as [E [Hintro Hfunction_ty]].
  subst function_ty.
  assert (Helim : E @ type_app @r U ==> Sm T)
    by (eapply app_abstract_inv; exact Hfinal_app).
  assert (Hcarrier_app : C # U ==> Sm T)
    by (eapply Hplain; eassumption).
  eapply tagged_carrier_redex_typing; eauto.
Qed.

Lemma plain_evaluation_preserves_typing : forall e v,
  plain_intro_sound ->
  e ==> v -> forall T,
  infer_expression @ e ==> Sm T -> infer @ v ==> Sm T.
Proof.
  intros e v plain Heval.
  assert (Htree : eval_tree
    (fun e v => forall T, infer_expression @ e ==> Sm T -> infer @ v ==> Sm T) e v).
  { induction Heval.
  - apply tree_val. intros T Htyping.
    eapply typing.infer_expression_stem_inv; exact Htyping.
  - eapply tree_appl; [exact IHHeval1|exact IHHeval2|]. intros T Htyping.
    rename IHHeval1 into HT1; rename IHHeval2 into HT2.
    pose proof (eval_tree_root _ _ _ HT1) as IHHeval1.
    pose proof (eval_tree_root _ _ _ HT2) as IHHeval2.
    eapply IHHeval2.
    destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
      as [T1 [T2 [He1 [He2 Happ]]]].
    eapply typing.infer_expression_fork.
    + eapply typing.infer_expression_stem.
      eapply IHHeval1; exact He1.
    + exact He2.
    + exact Happ.
  - eapply tree_appr; [exact IHHeval1|exact IHHeval2|]. intros T Htyping.
    rename IHHeval1 into HT1; rename IHHeval2 into HT2.
    pose proof (eval_tree_root _ _ _ HT1) as IHHeval1.
    pose proof (eval_tree_root _ _ _ HT2) as IHHeval2.
    eapply IHHeval2.
    destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
      as [T1 [T2 [He1 [He2 Happ]]]].
    eapply typing.infer_expression_fork.
    + exact He1.
    + eapply typing.infer_expression_stem.
      eapply IHHeval1; exact He2.
    + exact Happ.
  - apply tree_to_stem. intros T Htyping.
    destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
      as [T1 [T2 [HK [Hv2 Happ]]]].
    pose proof (typing.infer_expression_stem_inv _ _ _ HK) as Hleaf.
    pose proof (typing.infer_expression_stem_inv _ _ _ Hv2) as Hv2'.
    pose proof
      (eval_deterministic _ _ Hleaf _ (typing.inf_leaf AI)) as HT1.
    inversion HT1; subst T1.
    assert(Lf # T2 ==> Sm (Sm T2)) by (eapply typing.app_leaf).
    assert(Sm T = 'S1 T2) by (eapply eval_deterministic; eauto).
    inv_out H0.
    eapply typing.inf_stem; auto.
  - apply tree_to_fork. intros T Htyping.
    destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
      as [T1 [T2 [HS1 [Hv2 Happ]]]].
    pose proof (typing.infer_expression_stem_inv _ _ _ HS1) as Hstem_v1.
    pose proof (typing.infer_expression_stem_inv _ _ _ Hv2) as Hv2'.
    destruct (typing.infer_stem_inv _ _ _ Hstem_v1)
      as [V1 [HT1 Hv1]].
    subst T1.
    eapply typing.inf_fork; eauto.
  - apply tree_k. intros T Htyping.
    eapply typing.K_redex_typing; exact Htyping.
  - apply tree_s; [exact IHHeval|]. intros T Htyping.
    rename IHHeval into HT; pose proof (eval_tree_root _ _ _ HT) as IH.
    destruct (typing.infer_expression_fork_inv AI _ _ _ Htyping)
      as [FT [U [Hfunction [Hargument Happ]]]].
    apply typing.infer_expression_stem_inv in Hfunction.
    apply typing.infer_expression_stem_inv in Hargument.
    destruct (typing.infer_fork_inv AI _ _ _ Hfunction)
      as [GT [F [Hleft [Hf Hconstruction]]]].
    destruct (typing.infer_stem_inv AI _ _ Hleft) as [G [-> Hg]].
    destruct (tagged_decide ('S2[G,F])) as [[C [N Htag]]|Hplain].
    + apply IH; eapply plain_tagged_redex_typing; eauto.
    + apply typing.app_stem_inv in Hconstruction.
      pose proof (type_app_stem_structural_inv AI type_app _ _ _ Hplain Hconstruction) as ->.
      assert (HA : abstract_case @ ('S2[G,F]) ==> Lf).
      { unfold abstract_case; apply type_app_abstract_case_S_none; exact Hplain. }
      pose proof (app_plain_inv AI _ _ _ HA Happ) as HD.
      destruct (default_S_inv _ _ _ _ _ _ HD) as [VG [VF [HG [HF HR]]]].
      apply IH; eapply typing.infer_expression_fork.
      * eapply typing.infer_expression_fork;
          [apply typing.infer_expression_stem; exact Hg|
           apply typing.infer_expression_stem; exact Hargument|exact HG].
      * eapply typing.infer_expression_fork;
          [apply typing.infer_expression_stem; exact Hf|
           apply typing.infer_expression_stem; exact Hargument|exact HF].
      * exact HR.
  - apply tree_leaf. intros T Htyping.
    destruct (triage_application_typing f0 f1 f2 Lf T Htyping)
      as [X [Hx [HS|[HQ|[-> HC]]]]].
    + destruct HS as [F0 [F1 [F2 [HF HC]]]].
      exact (structural_triage_reduct_typing f0 f1 f2 F0 F1 F2 Lf X T HF Hx HC).
    + exact (query_triage_reduct_typing f0 f1 f2 Lf T X HQ Hx).
    + exact (children_reduct_typing AI f0 f1 f2 Lf X HC Hx).
  - apply tree_stem; [exact IHHeval|]. intros T Htyping.
    pose proof (eval_tree_root _ _ _ IHHeval) as IH.
    destruct (triage_application_typing f0 f1 f2 (Sm v2) T Htyping)
      as [X [Hx [HS|[HQ|[-> HC]]]]].
    + destruct HS as [F0 [F1 [F2 [HF HC]]]].
      apply IH; exact (structural_triage_reduct_typing f0 f1 f2 F0 F1 F2 (Sm v2) X T HF Hx HC).
    + apply IH; exact (query_triage_reduct_typing f0 f1 f2 (Sm v2) T X HQ Hx).
    + apply IH; exact (children_reduct_typing AI f0 f1 f2 (Sm v2) X HC Hx).
  - apply tree_fork; [exact IHHeval|]. intros T Htyping.
    pose proof (eval_tree_root _ _ _ IHHeval) as IH.
    destruct (triage_application_typing f0 f1 f2 (Fk v21 v22) T Htyping)
      as [X [Hx [HS|[HQ|[-> HC]]]]].
    + destruct HS as [F0 [F1 [F2 [HF HC]]]].
      apply IH; exact (structural_triage_reduct_typing f0 f1 f2 F0 F1 F2 (Fk v21 v22) X T HF Hx HC).
    + apply IH; exact (query_triage_reduct_typing f0 f1 f2 (Fk v21 v22) T X HQ Hx).
    + apply IH; exact (children_reduct_typing AI f0 f1 f2 (Fk v21 v22) X HC Hx).
  }
  exact (eval_tree_root _ _ _ Htree).
Qed.

End Soundness.


(* Print Assumptions closed_evaluation_preserves_typing. (* clean: no axioms *) *)


Definition empty_ontology := 'K1 refusal.

(** The function row. *)
Definition function_case := to_tree (tcase (Val fun_nm) (Val function_abstractor)).
Lemma function_case_some : function_case @ fun_nm ==> Sm function_abstractor.
Proof. apply tcase_eq. Qed.
Lemma function_case_none : forall N, N <> fun_nm -> function_case @ N ==> Lf.
Proof. intros; apply tcase_neq; congruence. Qed.
(** Declarations with the function row and nothing else. *)
Definition function_ontology := extend function_case empty_ontology.
Lemma function_ontology_row : function_ontology @ fun_nm ==> function_abstractor.
Proof. apply extend_some; apply function_case_some. Qed.
Canonical Structure function_decl := mkDecl function_ontology function_ontology_row.


(** * One-round soundness

    An abstractor is sound when every eliminator it makes agrees with the
    carrier type it was made from, on every argument. declarations is
    sound when, at every index, it answers the refusal or a sound
    declaration. No program identifying the types is needed. *)
(** A declaration is a single program [D] from carrier types to
    eliminators.  It is sound when every eliminator it makes agrees with
    the carrier type it was made from, at every argument. *)
Definition abstractor_sound_by_typing (AI D : Combination) : Prop :=
  forall C E U V, D @ C ==> Sm E -> E @ app AI @r U ==> Sm V -> app AI @ C @r U ==> Sm V.

(** The declarations are sound when every abstractor they answer is
    sound.  The refusal is an abstractor too, and trivially sound. *)
Definition ontology_sound_by_typing (AI : Combination) : Prop :=
  forall N R D, AI @ N ==> R -> R @ app AI ==> D ->
    abstractor_sound_by_typing AI D.

(** The function row is sound by typing. *)
Lemma function_abstractor_row_sound : forall (AI : Decl) D,
  function_abstractor @ app AI ==> D -> abstractor_sound_by_typing AI D.
Proof.
  intros AI D HD C E U V HC HE.
  apply (function_abstractor_sound AI C E U V); [|exact HE].
  eapply eval_appl; eassumption.
Qed.

Lemma refusal_sound : forall AI, abstractor_sound_by_typing AI ('K1 Lf).
Proof.
  intros AI C E U V H.
  assert (H0 : ('K1 Lf) @ C ==> Lf) by evaluate.
  pose proof (eval_deterministic _ _ H _ H0); discriminate.
Qed.

(** The abstractors of a refusal, and what it answers at type application. *)
Lemma refusal_head : forall a, refusal @ a ==> ('K1 Lf).
Proof. intros; unfold refusal; evaluate. Qed.

Lemma ontology_sound_by_typing_plain : forall AI, ontology_sound_by_typing AI -> plain_intro_sound AI.
Proof.
  intros AI Hs C N E U V HI HE.
  destruct (declaration_apply_inv _ _ _ _ _ HI) as [R [D [HR [HD HDC]]]].
  exact (Hs N R D HR HD C E U V HDC HE).
Qed.

(** ** Bounded evaluation

    [eval_bounded n e] evaluates the expression [e] with recursion depth
    at most [n]; every subevaluation has a smaller bound.  It agrees with
    [eval] ([eval_bounded_sound], [eval_bounded_complete]). *)
Fixpoint eval_bounded (n : nat) (e : Combination) : option Combination :=
  match n with
  | O => None
  | S n =>
    match e with
    | Lf => None
    | Sm v => Some v
    | Fk (Sm v1) (Sm v2) =>
      match v1 with
      | Lf => Some (Sm v2)
      | Sm v => Some (Fk v v2)
      | Fk Lf y => Some y
      | Fk (Sm g) f => eval_bounded n (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2)))
      | Fk (Fk f0 f1) f2 =>
        match v2 with
        | Lf => Some f0
        | Sm u => eval_bounded n (Fk (Sm f1) (Sm u))
        | Fk u1 u2 => eval_bounded n (Fk (Fk (Sm f2) (Sm u1)) (Sm u2))
        end
      end
    | Fk (Sm v1) (Fk a b) =>
      match eval_bounded n (Fk a b) with
      | Some v2 => eval_bounded n (Fk (Sm v1) (Sm v2))
      | None => None
      end
    | Fk (Fk a b) e2 =>
      match eval_bounded n (Fk a b) with
      | Some v1 => eval_bounded n (Fk (Sm v1) e2)
      | None => None
      end
    | Fk Lf _ | Fk (Sm _) Lf => None
    end
  end.

Lemma eval_bounded_sound : forall n e v, eval_bounded n e = Some v -> e ==> v.
Proof.
  induction n as [|n IH]; intros e v H; [discriminate|].
  destruct e as [|v0|[|v1|a b] e2]; cbn [eval_bounded] in H; try discriminate.
  - inversion H; constructor.
  - destruct e2 as [|v2|c d]; try discriminate.
    + destruct v1 as [|w|[|g|f0 f1] f2].
      * inversion H; constructor.
      * inversion H; constructor.
      * inversion H; constructor.
      * apply eval_s, IH, H.
      * destruct v2 as [|u|u1 u2].
        -- inversion H; constructor.
        -- apply eval_stem, IH, H.
        -- apply eval_fork, IH, H.
    + destruct (eval_bounded n (Fk c d)) as [v2|] eqn:E; [|discriminate].
      eapply eval_appr; [apply IH, E|apply IH, H].
  - destruct (eval_bounded n (Fk a b)) as [w|] eqn:E; [|discriminate].
    eapply eval_appl; [apply IH, E|apply IH, H].
Qed.

Definition eval_bounded_step (n : nat) (e : Combination) : option Combination :=
    match e with
    | Lf => None
    | Sm v => Some v
    | Fk (Sm v1) (Sm v2) =>
      match v1 with
      | Lf => Some (Sm v2)
      | Sm v => Some (Fk v v2)
      | Fk Lf y => Some y
      | Fk (Sm g) f => eval_bounded n (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2)))
      | Fk (Fk f0 f1) f2 =>
        match v2 with
        | Lf => Some f0
        | Sm u => eval_bounded n (Fk (Sm f1) (Sm u))
        | Fk u1 u2 => eval_bounded n (Fk (Fk (Sm f2) (Sm u1)) (Sm u2))
        end
      end
    | Fk (Sm v1) (Fk a b) =>
      match eval_bounded n (Fk a b) with
      | Some v2 => eval_bounded n (Fk (Sm v1) (Sm v2))
      | None => None
      end
    | Fk (Fk a b) e2 =>
      match eval_bounded n (Fk a b) with
      | Some v1 => eval_bounded n (Fk (Sm v1) e2)
      | None => None
      end
    | Fk Lf _ | Fk (Sm _) Lf => None
    end.

Lemma eval_bounded_unfold : forall n e, eval_bounded (S n) e = eval_bounded_step n e.
Proof. reflexivity. Qed.

Lemma eval_bounded_S : forall n e v, eval_bounded n e = Some v -> eval_bounded (S n) e = Some v.
Proof.
  induction n as [|n IH]; intros e v H; [discriminate|].
  rewrite eval_bounded_unfold in H |- *; unfold eval_bounded_step in H |- *.
  destruct e as [|v0|[|v1|a b] e2]; try discriminate; try exact H.
  - destruct e2 as [|v2|c d]; try discriminate.
    + destruct v1 as [|w|[|g|f0 f1] f2]; try exact H.
      * apply IH, H.
      * destruct v2 as [|u|u1 u2]; [exact H|apply IH, H|apply IH, H].
    + destruct (eval_bounded n (Fk c d)) as [v2|] eqn:E; [|discriminate].
      rewrite (IH _ _ E); apply IH, H.
  - destruct (eval_bounded n (Fk a b)) as [w|] eqn:E; [|discriminate].
    rewrite (IH _ _ E); apply IH, H.
Qed.

Lemma eval_bounded_le : forall n m e v, n <= m -> eval_bounded n e = Some v -> eval_bounded m e = Some v.
Proof.
  intros n m e v Hle; induction Hle; intro H; [exact H|apply eval_bounded_S, IHHle, H].
Qed.

Lemma eval_bounded_complete : forall e v, e ==> v -> exists n, eval_bounded n e = Some v.
Proof.
  intros e v H; induction H.
  - exists 1; reflexivity.
  - destruct IHeval1 as [n1 H1]; destruct IHeval2 as [n2 H2].
    exists (S (n1 + n2)); rewrite eval_bounded_unfold; unfold eval_bounded_step.
    rewrite (eval_bounded_le n1 (n1 + n2) _ _ ltac:(lia) H1).
    exact (eval_bounded_le n2 (n1 + n2) _ _ ltac:(lia) H2).
  - destruct IHeval1 as [n1 H1]; destruct IHeval2 as [n2 H2].
    exists (S (n1 + n2)); rewrite eval_bounded_unfold; unfold eval_bounded_step.
    rewrite (eval_bounded_le n1 (n1 + n2) _ _ ltac:(lia) H1).
    exact (eval_bounded_le n2 (n1 + n2) _ _ ltac:(lia) H2).
  - exists 1; reflexivity.
  - exists 1; reflexivity.
  - exists 1; reflexivity.
  - destruct IHeval as [n H1]; exists (S n); exact H1.
  - exists 1; reflexivity.
  - destruct IHeval as [n H1]; exists (S n); exact H1.
  - destruct IHeval as [n H1]; exists (S n); exact H1.
Qed.

(** Evaluation is bounded evaluation at some depth. *)
Theorem eval_iff_bounded : forall e v,
  e ==> v <-> exists n, eval_bounded n e = Some v.
Proof.
  intros e v; split.
  - apply eval_bounded_complete.
  - intros [n H]; exact (eval_bounded_sound n e v H).
Qed.

Lemma eval_bounded_appl_inv : forall n a b e2 w,
  eval_bounded (S n) (Fk (Fk a b) e2) = Some w ->
  exists v1, eval_bounded n (Fk a b) = Some v1 /\ eval_bounded n (Fk (Sm v1) e2) = Some w.
Proof.
  intros n a b e2 w H; rewrite eval_bounded_unfold in H; unfold eval_bounded_step in H.
  destruct (eval_bounded n (Fk a b)) as [v1|]; [eauto|discriminate].
Qed.

Lemma eval_bounded_appr_inv : forall n v1 a b w,
  eval_bounded (S n) (Fk (Sm v1) (Fk a b)) = Some w ->
  exists v2, eval_bounded n (Fk a b) = Some v2 /\ eval_bounded n (v1 @ v2) = Some w.
Proof.
  intros n v1 a b w H; rewrite eval_bounded_unfold in H; unfold eval_bounded_step in H.
  destruct (eval_bounded n (Fk a b)) as [v2|]; [eauto|discriminate].
Qed.

(** ** Soundness for values

    An eliminator [E] of an abstract type with carrier [c] is sound for
    values when [E @ U ==> Sm V], [v : U] and [c @ v ==> w] imply
    [w : V].  The proof that evaluation preserves typing uses it at
    evaluations inside the evaluation being typed, so it may assume that
    evaluation preserves typing ([ept]) at every evaluation of bound at
    most that of [c @ v] ([ept_within]): the induction on evaluation is
    an induction on the bound. *)
Definition ept (AI : Combination) : Combination -> Combination -> Prop :=
  fun e w => forall T, infer_expression AI @ e ==> Sm T -> inf AI @ w ==> Sm T.

Definition ept_within (AI : Combination) (n : nat) : Prop :=
  forall m e w, m <= n -> eval_bounded m e = Some w -> ept AI e w.

Definition sound_abstractor (AI D : Combination) : Prop :=
  forall n C E U V c v w,
    D @ C ==> Sm E -> E @ app AI @r U ==> Sm V ->
    inf AI @ c ==> Sm C -> inf AI @ v ==> Sm U ->
    ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.

(** The declarations are sound when every abstractor they answer is
    sound for values. *)
Definition ontology_sound (AI : Combination) : Prop :=
  forall N R D, AI @ N ==> R -> R @ app AI ==> D -> sound_abstractor AI D.

Lemma carrier_value_typing : forall AI n C U V c v w,
  app AI @ C @r U ==> Sm V -> inf AI @ c ==> Sm C -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.
Proof.
  intros AI n C U V c v w HC Hc Hv He Ht.
  apply (He n _ _ (le_n n) Ht).
  eapply infer_expression_fork;
    [apply infer_expression_stem; exact Hc|apply infer_expression_stem; exact Hv|exact HC].
Qed.

Lemma sound_by_typing_implies_sound : forall AI D,
  abstractor_sound_by_typing AI D -> sound_abstractor AI D.
Proof.
  intros AI D HD n C E U V c v w HDC HE Hc Hv He Ht.
  eapply carrier_value_typing; [eapply HD; eassumption|eassumption|eassumption|exact He|exact Ht].
Qed.

Lemma refusal_value_sound : forall AI, sound_abstractor AI ('K1 Lf).
Proof. intros; apply sound_by_typing_implies_sound, refusal_sound. Qed.

Lemma ontology_sound_by_typing_value : forall AI, ontology_sound_by_typing AI -> ontology_sound AI.
Proof.
  intros AI Hs N R D HR HD; apply sound_by_typing_implies_sound; exact (Hs N R D HR HD).
Qed.

Section ValueSoundness.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (inf AI).
Local Abbreviation infer_expression := (infer_expression AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).

(** Evaluation within bound [n] preserves typing, by induction on [n]. *)
Lemma bounded_evaluation_preserves_typing :
  ontology_sound AI -> forall n, ept_within AI n.
Proof.
  intros HSv n; induction n as [|n IH].
  { intros m e w Hm H; inversion Hm; subst; discriminate. }
  intros m e w Hm H T Htyping.
  destruct (Nat.le_succ_r m n) as [HL _]; destruct (HL Hm) as [Hle| ->];
    [exact (IH m e w Hle H T Htyping)|]; clear HL Hm.
  rewrite eval_bounded_unfold in H; unfold eval_bounded_step in H.
  destruct e as [|v0|[|v1|a b] e2]; try discriminate.
  - (* a value *)
    inversion H; subst.
    eapply typing.infer_expression_stem_inv; exact Htyping.
  - destruct e2 as [|v2|c d]; [discriminate| |].
    + destruct v1 as [|w1|[|g|f0 f1] f2].
      * (* Lf @ v2 *)
        inversion H; subst.
        destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
          as [T1 [T2 [HK [Hv2 Happ]]]].
        pose proof (typing.infer_expression_stem_inv _ _ _ HK) as Hleaf.
        pose proof (typing.infer_expression_stem_inv _ _ _ Hv2) as Hv2'.
        pose proof (eval_deterministic _ _ Hleaf _ (typing.inf_leaf AI)) as HT1.
        inversion HT1; subst T1.
        assert (HA : Lf # T2 ==> Sm (Sm T2)) by (eapply typing.app_leaf).
        assert (HE : Sm T = 'S1 T2) by (eapply eval_deterministic; eauto).
        inv_out HE.
        eapply typing.inf_stem; auto.
      * (* Sm w1 @ v2 *)
        inversion H; subst.
        destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
          as [T1 [T2 [HS1 [Hv2 Happ]]]].
        pose proof (typing.infer_expression_stem_inv _ _ _ HS1) as Hstem_v1.
        pose proof (typing.infer_expression_stem_inv _ _ _ Hv2) as Hv2'.
        destruct (typing.infer_stem_inv _ _ _ Hstem_v1) as [V1 [HT1 Hv1]].
        subst T1.
        eapply typing.inf_fork; eauto.
      * (* K1 f2 @ v2 *)
        inversion H; subst.
        eapply typing.K_redex_typing; exact Htyping.
      * (* S2[g,f2] @ v2 *)
        rename f2 into f.
        destruct (typing.infer_expression_fork_inv AI _ _ _ Htyping)
          as [FT [U [Hfunction [Hargument Happ]]]].
        apply typing.infer_expression_stem_inv in Hfunction.
        apply typing.infer_expression_stem_inv in Hargument.
        destruct (typing.infer_fork_inv AI _ _ _ Hfunction)
          as [GT [F [Hleft [Hf Hconstruction]]]].
        destruct (typing.infer_stem_inv AI _ _ Hleft) as [G [-> Hg]].
        destruct (tagged_decide ('S2[G,F])) as [[C [N Htag]]|Hplain].
        -- (* a tagged value: soundness for values *)
           apply typing.app_stem_inv in Hconstruction.
           pose proof Htag as Htag'; inversion Htag'; subst G F.
           destruct (type_app_stem_tagged_success_inv AI type_app C N FT Hconstruction)
             as [E [Hintro ->]].
           apply app_abstract_inv in Happ.
           destruct (infer_K1_inv AI g C Hg) as [c [-> Hc]].
           destruct n as [|n1]; [discriminate|].
           destruct (eval_bounded_appl_inv _ _ _ _ _ H) as [k [Hk Hrest]].
           pose proof (eval_deterministic _ _ (eval_bounded_sound _ _ _ Hk) _ (eval_k c v2)) as ->.
           destruct n1 as [|n2]; [discriminate|].
           destruct (eval_bounded_appr_inv _ _ _ _ _ Hrest) as [x' [Hx' Hcx]].
           assert (HU : infer @ x' ==> Sm U).
           { apply (IH n2 _ _ ltac:(lia) Hx').
             eapply typing.infer_expression_fork.
             eapply typing.infer_expression_stem; eauto.
             eapply typing.infer_expression_stem; eauto.
             new_S. discriminate.
             eapply typing.app_stem.
             eapply type_app_stem_structural; intros; discriminate.
             eapply typing.app_K.
             eapply typing.app_K. }
           destruct (declaration_apply_inv _ _ _ _ _ Hintro) as [R0 [D0 [HR0 [HD0 HC0]]]].
           apply (HSv N R0 D0 HR0 HD0 n2 C E U T c x' w HC0 Happ Hc HU).
           ++ intros m e' w' Hm; apply IH; lia.
           ++ exact Hcx.
        -- apply typing.app_stem_inv in Hconstruction.
           pose proof (type_app_stem_structural_inv AI type_app _ _ _ Hplain Hconstruction) as ->.
           assert (HA : abstract_case @ ('S2[G,F]) ==> Lf).
           { unfold abstract_case; apply type_app_abstract_case_S_none; exact Hplain. }
           pose proof (app_plain_inv AI _ _ _ HA Happ) as HD.
           destruct (default_S_inv _ _ _ _ _ _ HD) as [VG [VF [HG [HF HR]]]].
           apply (IH n _ _ (le_n n) H); eapply typing.infer_expression_fork.
           ++ eapply typing.infer_expression_fork;
                [apply typing.infer_expression_stem; exact Hg|
                 apply typing.infer_expression_stem; exact Hargument|exact HG].
           ++ eapply typing.infer_expression_fork;
                [apply typing.infer_expression_stem; exact Hf|
                 apply typing.infer_expression_stem; exact Hargument|exact HF].
           ++ exact HR.
      * (* triage[f0,f1,f2] @ v2 *)
        destruct v2 as [|u|u1 u2].
        -- inversion H; subst w.
           destruct (triage_application_typing AI f0 f1 f2 Lf T Htyping)
             as [X [Hx [HS|[HQ|[-> HC]]]]].
           ++ destruct HS as [F0 [F1 [F2 [HF HC]]]].
              exact (structural_triage_reduct_typing AI f0 f1 f2 F0 F1 F2 Lf X T HF Hx HC).
           ++ exact (query_triage_reduct_typing AI f0 f1 f2 Lf T X HQ Hx).
           ++ exact (children_reduct_typing AI f0 f1 f2 Lf X HC Hx).
        -- apply (IH n _ _ (le_n n) H).
           destruct (triage_application_typing AI f0 f1 f2 (Sm u) T Htyping)
             as [X [Hx [HS|[HQ|[-> HC]]]]].
           ++ destruct HS as [F0 [F1 [F2 [HF HC]]]].
              exact (structural_triage_reduct_typing AI f0 f1 f2 F0 F1 F2 (Sm u) X T HF Hx HC).
           ++ exact (query_triage_reduct_typing AI f0 f1 f2 (Sm u) T X HQ Hx).
           ++ exact (children_reduct_typing AI f0 f1 f2 (Sm u) X HC Hx).
        -- apply (IH n _ _ (le_n n) H).
           destruct (triage_application_typing AI f0 f1 f2 (Fk u1 u2) T Htyping)
             as [X [Hx [HS|[HQ|[-> HC]]]]].
           ++ destruct HS as [F0 [F1 [F2 [HF HC]]]].
              exact (structural_triage_reduct_typing AI f0 f1 f2 F0 F1 F2 (Fk u1 u2) X T HF Hx HC).
           ++ exact (query_triage_reduct_typing AI f0 f1 f2 (Fk u1 u2) T X HQ Hx).
           ++ exact (children_reduct_typing AI f0 f1 f2 (Fk u1 u2) X HC Hx).
    + (* v1 @ (Fk c d) *)
      destruct (eval_bounded n (Fk c d)) as [v2|] eqn:H1; [|discriminate]; rename H into H2.
      apply (IH n _ _ (le_n n) H2).
      destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
        as [T1 [T2 [He1 [He2 Happ]]]].
      eapply typing.infer_expression_fork.
      * exact He1.
      * eapply typing.infer_expression_stem.
        exact (IH n _ _ (le_n n) H1 T2 He2).
      * exact Happ.
  - (* (Fk a b) @ e2 *)
    destruct (eval_bounded n (Fk a b)) as [v1|] eqn:H1; [|discriminate]; rename H into H2.
    apply (IH n _ _ (le_n n) H2).
    destruct (typing.infer_expression_fork_inv _ _ _ _ Htyping)
      as [T1 [T2 [He1 [He2 Happ]]]].
    eapply typing.infer_expression_fork.
    + eapply typing.infer_expression_stem.
      exact (IH n _ _ (le_n n) H1 T1 He1).
    + exact He2.
    + exact Happ.
Qed.

End ValueSoundness.

Theorem evaluation_preserves_typing : forall AI e v T,
  ontology_sound AI -> e ==> v ->
  infer_expression AI @ e ==> Sm T -> infer AI @ v ==> Sm T.
Proof.
  intros AI e v T HS He HT.
  destruct (eval_bounded_complete _ _ He) as [n Hn].
  exact (bounded_evaluation_preserves_typing AI HS n n e v (le_n n) Hn T HT).
Qed.

(** The first form of the central theorem, by induction on the evaluation
    ([plain_evaluation_preserves_typing]), with no bound. *)
Theorem ept_by_typing : forall AI e v T,
  ontology_sound_by_typing AI -> e ==> v ->
  infer_expression AI @ e ==> Sm T -> infer AI @ v ==> Sm T.
Proof.
  intros AI e v T HS He HT.
  exact (plain_evaluation_preserves_typing AI e v
           (ontology_sound_by_typing_plain AI HS) He T HT).
Qed.

(** The children carrier [update_one_level r] of the Update family is
    sound for values: every child of the argument is updated by an
    update [r], which preserves its type.  The carrier type
    [update_one_level Update] has no clause of type application, so the
    carrier is not sound by typing. *)
Lemma children_value_typing : forall AI n c v U w,
  inf AI @ c ==> Sm (update_one_level ('Update)) -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm U.
Proof.
  intros AI n c v U w Hc Hv He Ht.
  pose proof Hc as Hc'; unfold update_one_level in Hc'.
  destruct (typing.infer_plain_fork_inv AI _ (Fk Lf (Lf 'C ('Update)))
    (update_fork ('Update)) ltac:(intros;discriminate) Hc')
    as [l [f2 [-> [Hl _]]]].
  destruct (typing.infer_plain_fork_inv AI _ Lf (Lf 'C ('Update)) ltac:(intros;discriminate) Hl)
    as [f0 [f1 [-> _]]].
  pose proof (children_reduct_typing AI f0 f1 f2 v U Hc Hv) as HR.
  destruct n as [|n]; [discriminate|].
  rewrite eval_bounded_unfold in Ht; unfold eval_bounded_step in Ht.
  destruct v as [|x|x y].
  - inversion Ht; subst w; exact HR.
  - exact (He n _ _ ltac:(lia) Ht U HR).
  - exact (He n _ _ ltac:(lia) Ht U HR).
Qed.

(** The carrier [name_test n] of the IsNamed family is sound for values: a
    runtime name n of type N is N itself, and a value of type U is tagged
    at N exactly when U is ([inferred_name_test_preservation]), so the
    name test on the value gives the name test on its type. *)
Lemma is_named_value_typing : forall AI n c v N U V w,
  concrete N -> inf AI @ c ==> Sm (name_test N) -> inf AI @ v ==> Sm U ->
  name_test N @ U ==> V -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.
Proof.
  intros AI n c v N U V w HN Hc Hv HB Ht.
  assert (HF : tag_free N = true) by (apply concrete_tag_free; exact HN).
  destruct (infer_name_test_inv AI c N Hc) as [m [-> Hn]].
  pose proof (inferred_name_test_preservation AI m N v U V HF Hn Hv HB) as HT.
  pose proof (eval_deterministic _ _ (eval_bounded_sound _ _ _ Ht) _ HT) as ->.
  apply name_test_equivalent in HB.
  destruct (tag_matches_boolean N U V HB) as [-> | ->]; apply infer_tag_free; reflexivity.
Qed.

Lemma is_named_abstractor_inv : forall C E,
  is_named_abstractor @ C ==> Sm E ->
  exists N, C = name_test N /\ concrete N /\ E = tagged_by N.
Proof.
  intros C E H; unfold is_named_abstractor in H; cbn in H; invert_eval.
  match goal with H4 : get_name_test @ C ==> Sm ?n |- _ => apply get_name_test_inv in H4; subst C end.
  match goal with H5 : is_concrete @ ?n ==> ?b |- _ =>
    pose proof (is_concrete_spec n) as HC;
    pose proof (eval_deterministic _ _ H5 _ HC) as HB;
    destruct (concreteb n) eqn:HN; cbn in HB; subst b end.
  all: invert_eval; try (eexists; split; [reflexivity|split; [apply concreteb_sound; exact HN|reflexivity]]).
Qed.

(** The IsNamed family is sound for values: its abstractor accepts only
    name tests [name_test N] at concrete [N] ([is_named_value_typing]). *)
Lemma is_named_abstractor_value_sound : forall AI, sound_abstractor AI is_named_abstractor.
Proof.
  intros AI n C E U V c v w HC HE Hc Hv He Ht.
  destruct (is_named_abstractor_inv _ _ HC) as [X [-> [HXc ->]]].
  apply tagged_by_inv in HE.
  eapply is_named_value_typing; eassumption.
Qed.

(** The one-level query carrier is sound for values. *)
Lemma query_one_level_value_typing : forall AI n c v B U w,
  inf AI @ c ==> Sm (query_one_level B) -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm B.
Proof.
  intros AI n c v B U w Hc Hv He Ht.
  pose proof Hc as Hc'; unfold query_one_level in Hc'.
  destruct (typing.infer_plain_fork_inv AI _ (Fk B ('Query[B]))
    ('Query['Query[B]]) ltac:(intros;discriminate) Hc')
    as [l [f2 [-> [Hl _]]]].
  destruct (typing.infer_plain_fork_inv AI _ B ('Query[B]) ltac:(intros;discriminate) Hl)
    as [f0 [f1 [-> _]]].
  pose proof (query_triage_reduct_typing AI f0 f1 f2 v B U Hc Hv) as HR.
  destruct n as [|n]; [discriminate|].
  rewrite eval_bounded_unfold in Ht; unfold eval_bounded_step in Ht.
  destruct v as [|x|x y].
  - inversion Ht; subst w; exact HR.
  - exact (He n _ _ ltac:(lia) Ht B HR).
  - exact (He n _ _ ltac:(lia) Ht B HR).
Qed.

(** Soundness of declarations built by [extend], one clause at a time. *)
Definition plain_clause_sound_for (clause target : Combination) : Prop :=
  forall C N constructor D E U V,
    clause @ N ==> Sm constructor ->
    constructor @ app target ==> D ->
    D @ C ==> Sm E ->
    E @ app target @r U ==> Sm V ->
    typing.type_app target @ C @r U ==> Sm V.

Definition plain_intro_sound_for (source target : Combination) : Prop :=
  forall C N E U V,
    source @ N @r app target @r C ==> Sm E ->
    E @ app target @r U ==> Sm V -> typing.type_app target @ C @r U ==> Sm V.

Lemma plain_extend_intro_sound_for : forall clause default target,
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  plain_clause_sound_for clause target ->
  plain_intro_sound_for default target ->
  plain_intro_sound_for (extend clause default) target.
Proof.
  intros clause default target Hnofork Hclause Hdefault.
  intros C N E U V Hintro HE.
  destruct (declaration_apply_inv _ _ _ _ _ Hintro) as [selected [D [Hchoose [HD Hconstruct]]]].
  clear Hintro.
  destruct (extend_inv _ _ _ _ Hchoose)
    as [[chosen [Hsome Heq]] |
        [[Hnone Hfallback] | [left [right [Hfork Heq]]]]].
  + subst selected; exact (Hclause C N chosen D E U V Hsome HD Hconstruct HE).
  + assert (Hconstructed : default @ N @r app target @r C ==> Sm E)
      by (eapply eval_appl; [eapply eval_appl; eassumption|exact Hconstruct]).
    exact (Hdefault C N E U V Hconstructed HE).
  + exfalso; eapply Hnofork; exact Hfork.
Qed.

(** soundness by typing of declarations built by [extend]. *)
Lemma extend_intro_sound_by_typing : forall clause default,
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  plain_clause_sound_for clause (extend clause default) ->
  plain_intro_sound_for default (extend clause default) ->
  plain_intro_sound (extend clause default).
Proof.
  intros clause default Hnofork Hclause Hdefault.
  exact (plain_extend_intro_sound_for _ _ _ Hnofork Hclause Hdefault).
Qed.

(** Soundness for values of declarations built by [extend]: if every
    abstractor that [clause] answers and every abstractor that [default]
    answers is sound for values in the extended declarations, then the
    extended declarations are sound. *)
Lemma extend_intro_sound : forall AI clause default,
  (forall N r, AI @ N ==> r <-> extend clause default @ N ==> r) ->
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  (forall N R D, clause @ N ==> Sm R -> R @ app AI ==> D ->
     sound_abstractor AI D) ->
  (forall N R D, clause @ N ==> Lf -> default @ N ==> R ->
     R @ app AI ==> D -> sound_abstractor AI D) ->
  ontology_sound AI.
Proof.
  intros AI clause default Hext Hnofork Hclause Hdefault N R D HR HD.
  apply Hext in HR.
  destruct (extend_inv _ _ _ _ HR)
    as [[chosen [Hsome ->]] | [[Hnone Hfallback] | [left [right [Hfork _]]]]].
  - exact (Hclause N chosen D Hsome HD).
  - exact (Hdefault N R D Hnone Hfallback HD).
  - exfalso; eapply Hnofork; exact Hfork.
Qed.

(** soundness by typing of the declarations follows from the soundness for
    types of their abstract introduction. *)
Lemma plain_ontology_sound_by_typing : forall AI, plain_intro_sound AI -> ontology_sound_by_typing AI.
Proof.
  intros AI Hp N R D HR HD C E U V HC HE.
  apply (Hp C N E U V); [|exact HE].
  eapply eval_appl; [eapply eval_appl; eassumption|exact HC].
Qed.
