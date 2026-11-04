(** * Type-directed conditionals (paper: Type-Directed Conditionals).

    Wrapped types with fixed and computed payload programs, the conditional
    [if_named N f d], which applies [f] to a value named [N] and [d] to any
    other value, salaries and the salary conditional [salary_here], and the
    wrapped types of the paper's "Wrapped types and a department" (Salary, Employee, Department), as wrappers.
    The typing of [if_named] ([installed_if_named]) holds at every inhabited
    argument type, because an inhabited type tagged at a declared wrapper
    name is the declared wrapper type ([inhabited_wrapper_tag]).  The
    IsNamed test [is_named] itself is part of type application (typing.v), and the
    wrapper lemmas needed by EPT are in soundness.v. *)


(** Wrappers after ordinary datatypes and function types.

    A concrete ordinary name N declares one payload type T. A value
    wrap N p then has type wrap_type T N exactly when p has type T.
    Construction works for concrete payload types, including I; Bool is
    not needed. Elimination by an action of type F is the type application
    F @ T, so no function type is needed.

    The conditional [if_named] uses the declared name to decide whether
    to pass the whole wrapper to its action. The IsNamed test [is_named]
    is typed by the IsNamed family, whose eliminator runs the name test on the
    argument type. The typing lemmas below cover every inhabited argument
    type. Wrapper declarations and their lookup are in typing.v.

    This file proves wrapper construction sound, derives the typing of
    [if_named], then supplies its recognition program. A computed
    wrapper abstractor stores a program p with p @ Lf ==> Sm T, so an
    abstract payload type need not be stored directly in the introduction
    program. Determinism connects lookup to construction in both cases. *)
From TreeTyping Require Export tree.
From TreeTyping Require Export typing soundness families.

From TreeTyping Require Import booleans.
From TreeTyping Require Import functions.
From Stdlib Require Import String Bool.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Notation "'onFork1 f" := (Fk ('K1 ('K1 Lf)) f) (at level 10).
Definition supports_wrapper AI N T := AI @ N ==> ('K1 (wrap_abstractor T)).

Definition wrapper_case N T := to_tree (tcase (Val N) (Val ('K1 (wrap_abstractor T)))).
Lemma wrapper_case_some : forall N T, wrapper_case N T @ N ==> Sm ('K1 (wrap_abstractor T)).
Proof. intros; apply tcase_eq. Qed.


(** A complete example with concrete payload I and no Boolean abstractor.
    Its name [Sm (Sm (Sm Lf))] is distinct from every other name of the
    development. *)
Definition concrete_wrapper_nm := Sm (Sm (Sm Lf)).
Definition concrete_wrapper_ontology :=
 extend (wrapper_case concrete_wrapper_nm ('I)) empty_ontology.
Lemma concrete_wrapper_support : supports_wrapper concrete_wrapper_ontology concrete_wrapper_nm ('I).
Proof. apply extend_some; apply wrapper_case_some. Qed.


(** A declared wrapper name fixes the carrier of every type bearing that
    name whose eliminator is introduced by the declarations, in particular of
    every inhabited type. *)
Definition ontology_tagged AI U :=
 forall E N, U = 'tagged[E,N] -> exists C, AI @ N @r app AI @r C ==> Sm E.

Lemma inhabited_ontology_tagged : forall AI U, inhabited AI U -> ontology_tagged AI U.
Proof.
 intros AI U [u Hu] E N ->.
 destruct (infer_tagged_result_inv AI u E N Hu) as [f [n [C [_ [_ [_ HC]]]]]].
 exists C; exact HC.
Qed.

Lemma fixed_wrapper_tag : forall AI N T U,
 AI @ N ==> ('K1 (wrap_abstractor T)) -> ontology_tagged AI U ->
 ((exists E, U = 'tagged[E,N]) <-> U = wrap_type T N).
Proof.
 intros AI N T U HI HA; split.
 - intros [E ->].
   destruct (HA E N eq_refl) as [C HC].
   assert (Hctor : wrap_abstractor T @ C ==> Sm E).
   { exact (declaration_K1_inv _ _ _ _ _ _ HI HC). }
   apply wrap_abstractor_inv in Hctor; destruct Hctor as [-> ->]; reflexivity.
 - intros ->; eexists; reflexivity.
Qed.


(** Fixed and computed payload declarations for specialisation. *)
Lemma computed_wrap_abstractor_sound : forall AI p C E U V,
 computed_wrap_abstractor p @ C ==> Sm E -> E @ type_app AI @r U ==> Sm V ->
 type_app AI @ C @r U ==> Sm V.
Proof.
 intros AI p C E U V HC HE; apply computed_wrap_abstractor_inv in HC;
 destruct HC as [T [HP [-> ->]]]; apply payload_eliminator_inv in HE.
 unfold swap; eapply app_S;
 [intros;discriminate|apply get_name_test_S_right;discriminate|apply app_I|apply app_K|exact HE].
Qed.

Lemma computed_declared_fixed : forall AI N p T E,
 AI @ N ==> ('K1 (computed_wrap_abstractor p)) -> p @ Lf ==> Sm T ->
 ontology_tagged AI ('tagged[E,N]) -> E = wrap_eliminator T.
Proof.
 intros AI N p T E HI HP HA.
 destruct (HA E N eq_refl) as [C HC].
 assert (Hctor : computed_wrap_abstractor p @ C ==> Sm E).
 { exact (declaration_K1_inv _ _ _ _ _ _ HI HC). }
 apply computed_wrap_abstractor_inv in Hctor; destruct Hctor as [T' [HT [_ ->]]].
 pose proof (eval_deterministic _ _ HT _ HP) as HE; inversion HE;reflexivity.
Qed.
Lemma ontology_wrapper_tag : forall AI N T U,
 declared_wrapper AI N T -> ontology_tagged AI U ->
 ((exists E, U = 'tagged[E,N]) <-> U = wrap_type T N).
Proof.
 intros AI N T U [HO|[p [HI HP]]] HU.
 - eapply fixed_wrapper_tag; eassumption.
 - split; [intros [E ->]|intros ->; eexists;reflexivity].
   pose proof (computed_declared_fixed AI N p T E HI HP HU) as ->; reflexivity.
Qed.

Lemma inhabited_wrapper_tag : forall AI N T U,
 declared_wrapper AI N T -> inhabited AI U ->
 ((exists E, U = 'tagged[E,N]) <-> U = wrap_type T N).
Proof. intros AI N T U HI HU; exact (ontology_wrapper_tag AI N T U HI (inhabited_ontology_tagged AI U HU)). Qed.


(** An inhabited type is no impostor. *)
Lemma inhabited_not_impostor : forall AI N T U,
 declared_wrapper AI N T -> inhabited AI U ->
 forall E, U = 'tagged[E,N] -> U = wrap_type T N.
Proof.
 intros AI N T U HI HU E HE.
 apply (proj1 (inhabited_wrapper_tag AI N T U HI HU)); eauto.
Qed.


(** The conditional [if_named N f d] applies [f] to an argument whose
    nametag is [N] and [d] to any other argument; its type
    [IfNamed N F D] is built the same way from the type [IsNamed N].  [IsNamed N]
    runs the name test on the argument type, so the typing holds at
    every argument type that is not an impostor, i.e. tagged at [N] but not
    the declared wrapper type. *)
Lemma installed_if_named : forall AI N T F B D U,
 concrete N -> declared_wrapper AI N T ->
 (forall E, U = 'tagged[E,N] -> U = wrap_type T N) ->
 type_app AI @ F @r wrap_type T N ==> Sm B ->
 type_app AI @ D @r U ==> Sm B ->
 type_app AI @ IfNamed N F D @r U ==> Sm B.
Proof.
 intros AI N T F B D U HN HI Himp HF HD.
 destruct (combination_eq_dec U (wrap_type T N)) as [->|Hne].
 - eapply if_named_application_hit; eassumption.
 - eapply if_named_application_miss; try eassumption.
   intros E HE; apply Hne; exact (Himp E HE).
Qed.

(** Evaluation: [f] at a value named [N], [d] elsewhere. *)
Lemma if_named_hit : forall N f d u b,
  get_tagname @ u ==> Sm N -> f @ u ==> b -> if_named N f d @ u ==> b.
Proof.
  intros N f d u b HN Hf.
  assert (HT : name_test N @ u ==> 'K) by (unfold name_test;
    repeat first [eassumption | apply equal_eval | apply wait_eval | apply equal1_eq | progress evaluate]).
  pose proof (is_named_eval _ _ _ HT) as HW.
  unfold if_named; repeat first [eassumption | progress evaluate].
Qed.
Lemma if_named_miss : forall N f d u found v,
  get_tagname @ u ==> found -> found <> Sm N -> d @ u ==> v -> if_named N f d @ u ==> v.
Proof.
  intros N f d u found v HN Hne Hd.
  pose proof (is_named_eval _ _ _ (name_test_miss N u found HN Hne)) as HW.
  unfold if_named; repeat first [eassumption | progress evaluate].
Qed.
Lemma if_named_default : forall N f d u v,
  (forall p, u <> 'tagged[p,N]) -> d @ u ==> v -> if_named N f d @ u ==> v.
Proof.
  intros N f d u v Hnot Hd.
  destruct (get_tagname_total u) as [Hnone | [p [n [Hu Hsome]]]].
  - eapply if_named_miss; [exact Hnone | discriminate | exact Hd].
  - eapply if_named_miss; [exact Hsome | | exact Hd].
    intro HE; inversion HE; subst n; eapply Hnot; exact Hu.
Qed.

(** Recognition shared by Query and Update specialisation constructors. *)
Local Ltac run_wr := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|apply get_wait_some|
 evaluate_expr_core run_wr run_head_wr|idtac]
with run_head_wr := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|
 evaluate_head_core run_wr|idtac].
Local Opaque equal equal1 get_tagname.
Local Lemma update_eval_inv : forall e v, e ==> v ->
  match e with
  | Lf => False
  | Sm u => v = u
  | Fk op arg =>
    match op with
    | Lf => False
    | Fk a b => exists w, Fk a b ==> w /\ Fk (Sm w) arg ==> v
    | Sm f =>
      match arg with
      | Lf => False
      | Fk a b => exists w, Fk a b ==> w /\ f @ w ==> v
      | Sm u =>
        match f with
        | Lf => v = Sm u
        | Sm a => v = Fk a u
        | Fk Lf a => v = a
        | Fk (Sm g) h => Fk (g @ u) (h @ u) ==> v
        | Fk (Fk f0 f1) f2 =>
          (u = Lf /\ v = f0) \/
          (exists x, u = Sm x /\ f1 @ x ==> v) \/
          (exists x y, u = Fk x y /\ f2 @ x @r y ==> v)
        end
      end
    end
  end.
Proof.
  intros e v H; destruct H; cbn; eauto 8.
Qed.

Local Ltac invert_update_eval :=
  match goal with
  | H : eval (Sm _) _ |- _ => apply update_eval_inv in H; subst
  | H : eval (Fk (Fk _ _) _) _ |- _ =>
      apply update_eval_inv in H; destruct H as [? [? ?]]
  | H : eval (Fk (Sm _) (Fk _ _)) _ |- _ =>
      apply update_eval_inv in H; destruct H as [? [? ?]]
  | H : eval (Fk (Sm Lf) (Sm _)) _ |- _ => apply update_eval_inv in H; subst
  | H : eval (Fk (Sm (Sm _)) (Sm _)) _ |- _ => apply update_eval_inv in H; subst
  | H : eval (Fk (Sm (Fk Lf _)) (Sm _)) _ |- _ => apply update_eval_inv in H; subst
  | H : eval (Fk (Sm (Fk (Sm _) _)) (Sm _)) _ |- _ => apply update_eval_inv in H
  | H : eval (Fk (Sm (Fk (Fk _ _) _)) (Sm _)) _ |- _ =>
      apply update_eval_inv in H;
      destruct H as [[? ?]|[[? [? ?]]|[? [? [? ?]]]]]; subst
  | H : eval (Fk Lf _) _ |- _ => apply update_eval_inv in H; contradiction
  | H : Sm _ = Sm _ |- _ => injection H; clear H; intros; subst
  | H : Fk _ _ = Fk _ _ |- _ => injection H; clear H; intros; subst
  end.

(** [get_IfNamed] recognises an IfNamed type and returns its name, action
    type and default type. *)
Definition get_IfNamed := Eval cbn in to_tree
  (tcase
    (''S2[''S2[''S2[
      ''tagged[''K1 (Val Lf ''C ((''wait[Val equal, Val Lf @@ Ref "N"]) ''C Val get_tagname)), Val is_named_nm],
      ''K1 (Ref "F")],''K1 (Ref "D")],Val 'I])
    (Val Lf @@ Ref "N" @@ (Val Lf @@ Ref "F" @@ Ref "D"))).
Lemma get_IfNamed_some : forall N F D,
  get_IfNamed @ IfNamed N F D ==> Sm (Fk N (Fk F D)).
Proof.
  intros; unfold get_IfNamed, IfNamed, IsNamed, tagged_by, name_test, extend_program; cbn.
  repeat first [apply equal_eval | apply equal1_eq | apply closed_test_eq | progress evaluate].
Qed.
Lemma get_IfNamed_inv : forall C N F D,
  get_IfNamed @ C ==> Sm (Fk N (Fk F D)) -> C = IfNamed N F D.
Proof.
  intros C N F D H.
  unfold get_IfNamed, extend_program in H.
  repeat first [solve [discriminate] | match goal with
  | H : equal @ ?a ==> ?v |- _ =>
    pose proof (eval_deterministic _ _ H _ (equal_eval a)); clear H; subst v
  | H : equal1 ?a @ ?b ==> ?v |- _ =>
    let HV := fresh "HV" in
    destruct (combination_eq_dec a b) as [E|E];
    [ assert (HV : v = 'K) by
        (eapply eval_deterministic; [exact H|rewrite <- E; apply equal1_eq]);
      clear H; subst v; subst
    | assert (HV : v = 'KI) by
        (eapply eval_deterministic; [exact H|apply equal1_neq; exact E]);
      clear H; subst v ]
  | H : closed_test ?a @ ?b ==> ?v |- _ =>
    let HV := fresh "HV" in
    destruct (combination_eq_dec a b) as [E|E];
    [ assert (HV : v = 'K) by
        (eapply eval_deterministic; [exact H|rewrite <- E; apply closed_test_eq]);
      clear H; subst v; subst
    | assert (HV : v = 'KI) by
        (eapply eval_deterministic; [exact H|apply closed_test_neq; exact E]);
      clear H; subst v ]
  end | progress invert_update_eval].
  all: reflexivity.
Qed.


Unset Default Proof Using.
Transparent equal equal1 get_tagname get_IfNamed.

(** Salary before traversal.

    Salary wraps Nat. The increment action opens one Salary, applies succ,
    and wraps the result again. [salary_here] specialises identity at Salary:
    it increments a matching argument and leaves every other argument alone.
    It does not inspect children. This separates name-based specialisation
    from the recursive traversal developed later in customisation.v. *)
From Stdlib Require Import String Bool.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import booleans functions data_types.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque type_app infer equal equal1 get_tagname nat_abstractor.
Local Ltac payload_run := first [eassumption|evaluate_expr_core payload_run payload_head|idtac]
with payload_head := first [eassumption|evaluate_head_core payload_run|idtac].

Definition salary_nm := Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf))))))))))).
Definition salary_payload_type := 'Nat.
Definition salary_eliminator := wrap_eliminator salary_payload_type.
Notation "'Salary" := ('tagged[salary_eliminator,salary_nm]) (at level 0).
Definition salary amount := wrap salary_nm amount.
(** Build Nat at run time with its tagger, rather than storing Nat in the
    declarations.  Introduction checks exactly the same payload type. *)
Definition salary_payload_program := Eval cbn -[nat_type_mk] in to_tree
  (star "z" (Val Lf @@ (Val nat_type_mk @@ Ref "z"))).
Lemma salary_payload_program_eval : salary_payload_program @ Lf ==> Sm ('Nat).
Proof.
  pose proof (nat_type_mk_eval Lf) as H.
  unfold salary_payload_program; evaluate.
Qed.
Definition salary_abstractor := computed_wrap_abstractor salary_payload_program.
Definition supports_salary AI := AI @ salary_nm ==> ('K1 (salary_abstractor)).

Lemma salary_eval : forall amount f result,
  f @ amount ==> result -> salary amount @ f ==> result.
Proof. intros; unfold salary, wrap; apply tagged_eval; evaluate. Qed.
Lemma supports_salary_abstractor : forall AI a,
  supports_salary AI ->
  AI @ salary_nm @r a @r swap salary_payload_type ==> Sm salary_eliminator.
Proof.
  intros AI a H; unfold supports_salary, salary_abstractor in H.
  pose proof (computed_wrap_abstractor_some salary_payload_program ('Nat) salary_payload_program_eval) as HC.
  eapply declaration_apply; [exact H | exact HC].
Qed.
Lemma infer_salary : forall AI amount,
  supports_salary AI -> infer AI @ amount ==> Sm ('Nat) ->
  infer AI @ salary amount ==> Sm ('Salary).
Proof.
  intros AI amount HS Ha; unfold salary, wrap; eapply infer_tagged.
  - infer_tac.
  - apply infer_tag_free; reflexivity.
  - apply supports_salary_abstractor; exact HS.
Qed.
Lemma salary_declared : forall AI,
 supports_salary AI -> declared_wrapper AI salary_nm ('Nat).
Proof. intros AI HS; right; exists salary_payload_program; split; [exact HS|apply salary_payload_program_eval]. Qed.
Lemma salary_payload_lookup : forall AI,
  supports_salary AI -> get_wrap_payload_type AI @ salary_nm ==> Sm ('Nat).
Proof. intros; apply get_wrap_payload_type_some; apply salary_declared; exact H. Qed.

Definition salary_case_package : {t : Combination |
  to_tree (tcase (Val salary_nm) (Val ('K1 salary_abstractor))) = t}.
Proof. eexists; simpl; reflexivity. Defined.
Definition salary_case := Eval cbn in proj1_sig salary_case_package.
Lemma salary_case_compilation :
  to_tree (tcase (Val salary_nm) (Val ('K1 salary_abstractor))) = salary_case.
Proof. unfold salary_case; exact (proj2_sig salary_case_package). Qed.
Lemma salary_case_some : salary_case @ salary_nm ==> Sm ('K1 salary_abstractor).
Proof. rewrite <- salary_case_compilation; apply tcase_eq. Qed.
Lemma salary_case_none : forall N,
  N <> salary_nm -> salary_case @ N ==> Lf.
Proof.
  intros N H; rewrite <- salary_case_compilation; apply tcase_neq; congruence.
Qed.


(** The IsNamed family's clause, a base row of the
    declarations, at [is_named_nm]. *)
Definition is_named_case := to_tree (tcase (Val is_named_nm) (Val ('K1 is_named_abstractor))).
Lemma is_named_case_some : is_named_case @ is_named_nm ==> Sm ('K1 is_named_abstractor).
Proof. unfold is_named_case; apply tcase_eq. Qed.
Lemma is_named_case_none : forall N, N <> is_named_nm -> is_named_case @ N ==> Lf.
Proof. intros; unfold is_named_case; apply tcase_neq; congruence. Qed.

Definition salary_base_ontology := extend is_named_case (extend salary_case nat_ontology).


(** [increment_salary s = s (fun n => salary (succ n))]. The wrapper
    passes its amount to this continuation; the result is wrapped again. *)
Definition salary_successor := Eval cbn in to_tree
  (star "n" (''tagged[
    ''S2[Val ('I),''K1 (''tagged[''S2[Val ('snd),Ref "n"],Val nat_nm])],
    Val salary_nm])).
Definition increment_salary :=
  lam (swap (lam salary_successor zero)) (salary zero).
Lemma salary_successor_eval : forall n,
  salary_successor @ n ==> salary (succ n).
Proof. intros; unfold salary_successor, salary, wrap, succ; evaluate. Qed.
Lemma increment_salary_eval : forall n,
  increment_salary @ salary n ==> salary (succ n).
Proof.
  intros; unfold increment_salary, lam; apply tagged_eval; apply wait_eval.
  eapply eval_appl; [evaluate |].
  unfold swap; evaluate; apply salary_eval.
  apply tagged_eval; apply wait_eval; eapply eval_appl; [evaluate |].
  apply salary_successor_eval.
Qed.
Lemma type_app_salary_successor : forall AI,
  supports_salary AI -> supports_number AI ->
  type_app AI @ salary_successor @r ('Nat) ==> Sm ('Salary).
Proof.
  intros AI HS HN; unfold salary_successor; type_app_tac.
  - apply type_app_stem_ev; apply type_app_stem_tagged.
    apply nat_abstractor_supported; [exact HN | apply nat_abstractor_succ].
  - apply type_app_stem_ev; apply type_app_stem_tagged.
    apply supports_salary_abstractor; exact HS.
Qed.
Lemma infer_increment_salary : forall (AI : Decl),
  supports_salary AI -> supports_number AI ->
  infer AI @ increment_salary ==> Sm ('Salary --> 'Salary).
Proof.
  intros AI HS HN.
  assert (HZ : infer AI @ zero ==> Sm ('Nat)) by (apply infer_zero; exact HN).
  assert (HSuc : infer AI @ lam salary_successor zero ==> Sm ('Nat --> 'Salary)).
  { eapply infer_lam; [apply infer_tag_free; reflexivity |exact HZ |].
    apply type_app_salary_successor; assumption. }
  unfold increment_salary; eapply infer_lam; [ | |].
  - unfold swap; infer_tac.
  - apply infer_salary; assumption.
  - unfold swap; type_app_tac.
    apply payload_eliminator_some; apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** The arm of the conditional has no function type: a salary is applied to
    [salary_successor], and the arm holds no tagged subtree, so it is its own type. *)
Definition salary_raise := swap salary_successor.
Lemma salary_raise_tag_free : tag_free salary_raise = true.
Proof. vm_compute; reflexivity. Qed.
Lemma salary_raise_eval : forall n,
  salary_raise @ salary n ==> salary (succ n).
Proof.
  intros; unfold salary_raise, swap; evaluate; apply salary_eval.
  apply salary_successor_eval.
Qed.
Lemma type_app_salary_raise : forall AI,
  supports_salary AI -> supports_number AI ->
  type_app AI @ salary_raise @r 'Salary ==> Sm ('Salary).
Proof.
  intros AI HS HN; pose proof (type_app_salary_successor AI HS HN) as H.
  unfold salary_raise, swap; type_app_tac.
  apply payload_eliminator_some; exact H.
Qed.

Definition salary_here := if_named salary_nm salary_raise ('I).

Lemma salary_here_hit : forall n,
 salary_here @ salary n ==> salary (succ n).
Proof.
 intros; eapply if_named_hit; [apply get_tagname_some|apply salary_raise_eval].
Qed.
Lemma salary_here_miss : forall u,
 (forall C, u <> 'tagged[C,salary_nm]) -> salary_here @ u ==> u.
Proof.
 intros; apply if_named_default; [exact H|evaluate].
Qed.
Example salary_here_does_not_descend :
 salary_here @ Sm (salary zero) ==> Sm (salary zero).
Proof. apply salary_here_miss; intros; discriminate. Qed.

Lemma infer_salary_here : forall (AI : Decl),
 supports_salary AI -> supports_number AI -> supports_is_named AI ->
 infer AI @ salary_here ==> Sm (IfNamed salary_nm salary_raise ('I)).
Proof.
 intros AI HS HN HT; apply inf_if_named;
 [apply concreteb_sound; vm_compute; reflexivity|exact HT|
  apply infer_tag_free; exact salary_raise_tag_free|apply infer_I].
Qed.
(** Holds at every inhabited argument type U.  ([IsNamed salary_nm] runs the
    name test on U, so at an uninhabited impostor 'tagged[E,salary_nm]
    the increment would be selected.) *)
Lemma type_app_salary_here : forall AI U,
 supports_salary AI -> supports_number AI -> inhabited AI U ->
 type_app AI @ IfNamed salary_nm salary_raise ('I) @r U ==> Sm U.
Proof.
 intros AI U HS HN Hinh; pose proof (salary_declared AI HS) as Hreg.
 pose proof (inhabited_not_impostor AI _ _ U Hreg Hinh) as Himp.
 destruct (combination_eq_dec U ('Salary)) as [->|HU].
 - eapply installed_if_named; [apply concreteb_sound; vm_compute; reflexivity|exact Hreg|exact Himp| |apply app_I].
   apply type_app_salary_raise; assumption.
 - eapply if_named_application_miss;
   [apply concreteb_sound; vm_compute; reflexivity|exact Hreg| |apply app_I].
   intros E HE; apply HU; exact (Himp E HE).
Qed.

(** The type of the salary conditional applies as
    the identity at every inhabited argument type. *)
Theorem salary_here_polymorphic : forall (AI : Decl),
 supports_salary AI -> supports_number AI -> supports_is_named AI ->
 infer AI @ salary_here ==> Sm (IfNamed salary_nm salary_raise ('I)) /\
 forall U, inhabited AI U ->
   type_app AI @ IfNamed salary_nm salary_raise ('I) @r U ==> Sm U.
Proof.
 intros AI HS HN HT; split; [apply infer_salary_here; assumption|].
 intros U HU; apply type_app_salary_here; assumption.
Qed.

Lemma salary_here_preserves_typing : forall (AI : Decl) u U v,
 ontology_sound AI -> supports_salary AI -> supports_number AI -> supports_is_named AI ->
 infer AI @ u ==> Sm U -> salary_here @ u ==> v -> infer AI @ v ==> Sm U.
Proof.
 intros AI u U v HA HS HN HT Hu He; eapply evaluation_preserves_typing;
 [exact HA|exact He|].
 eapply infer_expression_fork;
 [apply infer_expression_stem; apply infer_salary_here; assumption|
  apply infer_expression_stem; exact Hu|apply type_app_salary_here; [assumption|assumption|exists u; exact Hu]].
Qed.

(** ** Seek: a wrapped number for searching

    [Seek] wraps a number, as [Salary] does, under its own name.  A search
    over numbers is then an update that acts on values of type [Seek]
    ([minimisation], dither_minimisation.v). *)
Definition seek_nm := Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf))))))).
Definition seek_eliminator := wrap_eliminator ('Nat).
Notation "'Seek" := ('tagged[seek_eliminator,seek_nm]) (at level 0).
Definition seek_at n := wrap seek_nm n.
Definition supports_seek AI := AI @ seek_nm ==> ('K1 salary_abstractor).

Lemma seek_nm_concrete : concrete seek_nm.
Proof. apply concreteb_sound; reflexivity. Qed.
Lemma seek_declared : forall AI,
 supports_seek AI -> declared_wrapper AI seek_nm ('Nat).
Proof. intros AI HS; right; exists salary_payload_program; split; [exact HS|apply salary_payload_program_eval]. Qed.
Lemma supports_seek_abstractor : forall AI a,
  supports_seek AI -> AI @ seek_nm @r a @r swap ('Nat) ==> Sm seek_eliminator.
Proof.
  intros AI a H; unfold supports_seek, salary_abstractor in H.
  pose proof (computed_wrap_abstractor_some salary_payload_program ('Nat) salary_payload_program_eval) as HC.
  eapply declaration_apply; [exact H | exact HC].
Qed.
Lemma infer_seek_at : forall AI n,
  supports_seek AI -> infer AI @ n ==> Sm ('Nat) -> infer AI @ seek_at n ==> Sm ('Seek).
Proof.
  intros AI n HS Hn; unfold seek_at, wrap; eapply infer_tagged.
  - infer_tac.
  - apply infer_tag_free; reflexivity.
  - apply supports_seek_abstractor; exact HS.
Qed.

Definition seek_case_package : {t : Combination |
  to_tree (tcase (Val seek_nm) (Val ('K1 salary_abstractor))) = t}.
Proof. eexists; simpl; reflexivity. Defined.
Definition seek_case := Eval cbn in proj1_sig seek_case_package.
Lemma seek_case_compilation :
  to_tree (tcase (Val seek_nm) (Val ('K1 salary_abstractor))) = seek_case.
Proof. unfold seek_case; exact (proj2_sig seek_case_package). Qed.
Lemma seek_case_some : seek_case @ seek_nm ==> Sm ('K1 salary_abstractor).
Proof. rewrite <- seek_case_compilation; apply tcase_eq. Qed.
Lemma seek_case_none : forall N,
  N <> seek_nm -> seek_case @ N ==> Lf.
Proof.
  intros N H; rewrite <- seek_case_compilation; apply tcase_neq; congruence.
Qed.

(** The next search position: [seek_successor @ n = seek_at (succ n)]. *)
Definition seek_successor := Eval cbn in to_tree
  (star "n" (''tagged[
    ''S2[Val ('I),''K1 (''tagged[''S2[Val ('snd),Ref "n"],Val nat_nm])],
    Val seek_nm])).
Lemma seek_successor_eval : forall n,
  seek_successor @ n ==> seek_at (succ n).
Proof. intros; unfold seek_successor, seek_at, wrap, succ; evaluate. Qed.
Lemma type_app_seek_successor : forall AI,
  supports_seek AI -> supports_number AI ->
  type_app AI @ seek_successor @r ('Nat) ==> Sm ('Seek).
Proof.
  intros AI HS HN; unfold seek_successor; type_app_tac.
  - apply type_app_stem_ev; apply type_app_stem_tagged.
    apply nat_abstractor_supported; [exact HN | apply nat_abstractor_succ].
  - apply type_app_stem_ev; apply type_app_stem_tagged.
    apply supports_seek_abstractor; exact HS.
Qed.


Unset Default Proof Using.
Transparent equal equal1 get_tagname get_IfNamed type_app infer nat_abstractor.

(** Company record types, independently of generic traversal.

    Employee stores [Nat * Salary]; Department stores an Employee manager
    and a List[Employee]. Their concrete payload programs construct these
    types when needed. The generic wrapper interface checks the resulting
    fixed types. *)
From Stdlib Require Import String Bool.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import data_types functions.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque list_eliminator_builder.
Local Ltac run := first [eassumption|apply list_eliminator_builder_eval|
 evaluate_expr_core run run_head|idtac]
with run_head := first [eassumption|apply list_eliminator_builder_eval|
 evaluate_head_core run|idtac].
Definition employee_nm := Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf)))))))).
Definition department_nm := Sm employee_nm.
Definition employee_fields := 'Nat '* 'Salary.
Definition employee id pay := wrap employee_nm (id '* pay).
Notation "'Employee" := (wrap_type employee_fields employee_nm) (at level 0).
Definition department_fields := 'Employee '* 'List['Employee].
Definition department manager workers := wrap department_nm (manager '* workers).
Notation "'Department" := (wrap_type department_fields department_nm) (at level 0).
Definition employee_payload_program :=
 ('onStem1 (to_tree (star "T" (Val Lf @@ (Ref "T" ''*
   (Val ('tagger[salary_nm]) @@ payload_eliminator2 (Ref "T"))))))) 'C salary_payload_program.
Lemma employee_payload_program_eval : employee_payload_program @ Lf ==> Sm employee_fields.
Proof. pose proof salary_payload_program_eval; unfold employee_payload_program; cbn; run. Qed.
Definition department_payload_program :=
 ('onStem1 (to_tree (star "P"
   ((star "A" (Val Lf @@ (Ref "A" ''*
       (Val ('tagger[list_nm]) @@ (Val list_eliminator_builder @@ Ref "A")))))
    @@ (Val ('tagger[employee_nm]) @@ payload_eliminator2 (Ref "P")))))) 'C employee_payload_program.
Lemma department_payload_program_eval : department_payload_program @ Lf ==> Sm department_fields.
Proof. pose proof employee_payload_program_eval; unfold department_payload_program; cbn; run. Qed.

Definition supports_employee AI := AI @ employee_nm ==> ('K1 (computed_wrap_abstractor employee_payload_program)).
Definition supports_department AI := AI @ department_nm ==> ('K1 (computed_wrap_abstractor department_payload_program)).
Lemma employee_declared : forall AI,
 supports_employee AI -> declared_wrapper AI employee_nm employee_fields.
Proof. intros AI H; right; exists employee_payload_program; split; [exact H|apply employee_payload_program_eval]. Qed.
Definition record_case nm constructor := to_tree (tcase (Val nm) (Val ('K1 constructor))).
Definition employee_case := record_case employee_nm (computed_wrap_abstractor employee_payload_program).
Definition department_case := record_case department_nm (computed_wrap_abstractor department_payload_program).
Lemma record_case_some : forall nm ctor,
 record_case nm ctor @ nm ==> Sm ('K1 ctor).
Proof. intros; apply tcase_eq. Qed.
Lemma record_case_none : forall nm ctor N,
 N <> nm -> record_case nm ctor @ N ==> Lf.
Proof. intros; apply tcase_neq; congruence. Qed.


Lemma infer_employee : forall AI id pay,
 supports_employee AI -> infer AI @ id ==> Sm ('Nat) ->
 infer AI @ pay ==> Sm ('Salary) -> infer AI @ employee id pay ==> Sm ('Employee).
Proof.
 intros AI id pay HI HN HS; unfold employee,wrap,wrap_type; eapply infer_tagged.
 - infer_tac.
 - apply infer_tag_free;reflexivity.
 - eapply declaration_apply; [exact HI|apply computed_wrap_abstractor_some; apply employee_payload_program_eval].
Qed.
Lemma infer_department : forall AI manager workers,
 supports_department AI -> infer AI @ manager ==> Sm ('Employee) ->
 infer AI @ workers ==> Sm ('List['Employee]) -> infer AI @ department manager workers ==> Sm ('Department).
Proof.
 intros AI manager workers HI HM HW; unfold department,wrap,wrap_type; eapply infer_tagged.
 - infer_tac.
 - apply infer_tag_free;reflexivity.
 - eapply declaration_apply; [exact HI|apply computed_wrap_abstractor_some; apply department_payload_program_eval].
Qed.

(** One-round soundness of the declarations. *)
Lemma plain_wrap_cond2 : forall AI p, abstractor_sound_by_typing AI (computed_wrap_abstractor p).
Proof. intros AI p; exact (computed_wrap_abstractor_sound AI p). Qed.
