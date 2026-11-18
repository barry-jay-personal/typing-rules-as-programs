(** * Step 82, stage 3, part 1: updates enter tags; the department example.

    Wrapped types, as the old [wrap]: a value of the abstract type
    [W = label[w_nm]] with payload type [T] is [tagged[swap p, w_nm]] with
    [p : T] and [swap p = S2[I, K1 p]], so that [swap p @ f = f @ p].  The
    declaration stores the code [code T]:

      guard  admits S2[I, K1 T]
      elim   W # U = U # T

    Salary (payload Nat), Employee (payload Nat * Salary) and Department
    (payload Employee * List Employee) are such types.

    [update_at[T,f] = fix_update[b]] with
    [b @ r = special_type[T, f, children[r]]], built at run time by the
    Update constructor. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p.

(** ** Wrapped types *)

Definition swap (p : Combination) : Combination := 'S2['I, 'K1 p].

Definition wg_prog : Combination := Eval cbn -[equal decode_p] in to_tree
  (star "c" (star "C"
    (''onStem1 (star "T" (op equal @@ Ref "C" @@ ''S2[''I, ''K1 (Ref "T")])) @@ (op decode_p @@ Ref "c")))).
Definition we_prog : Combination := Eval cbn -[decode_p] in to_tree
  (star "c" (star "n" (star "a" (star "U"
    (''onStem1 (star "T" (Ref "a" @@ Ref "U" @@ Ref "T")) @@ (op decode_p @@ Ref "c")))))).
Definition D_wrap (T : Combination) : Combination := 'wait[wg_prog, code T] '* 'wait[we_prog, code T].

Local Opaque wg_prog we_prog.

Lemma wg_inv : forall c C, 'wait[wg_prog, c] @ C ==> 'K -> exists T, decode c = Some T /\ C = swap T.
Proof.
  intros c C H; apply wait_eval_inv in H. Local Transparent wg_prog. unfold wg_prog in H. Local Opaque wg_prog.
  pose proof (decode_p_eval c) as Hd.
  destruct (decode c) as [T|]; cbn [opt] in Hd; crunch.
  all: eq_case2; crunch.
  all: try discriminate.
  all: eexists; split; [reflexivity|assumption].
Qed.

Lemma we_inv : forall c n a U V, 'wait[we_prog, c] @ n @r a @r U ==> Sm V ->
  exists T, decode c = Some T /\ a @ U @r T ==> Sm V.
Proof.
  intros c n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent we_prog. unfold we_prog in Hp1. Local Opaque we_prog.
  pose proof (decode_p_eval c) as Hd.
  destruct (decode c) as [T|]; cbn [opt] in Hd; crunch; eexists; split; [reflexivity|eapply eval_appl; eassumption].
Qed.

(** The wrapper declaration is sound by values. *)
Theorem wrap_decl_sound : forall O n T, decl_sound O n (D_wrap T).
Proof.
  intros O n T k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (wg_inv _ _ HC') as [T' [HT ->]].
  apply elim_of_inv, we_inv in HE; destruct HE as [T'' [HT' HU]].
  rewrite HT in HT'; inversion HT'; subst T''.
  unfold swap in Hc.
  destruct (type_Fk_inv O _ _ _ Hc) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
  destruct (type_Sm_inv O _ _ Hx) as [x' [-> Hx']].
  apply (concrete_type_forces O) in Hx'; [subst x'|reflexivity].
  destruct (type_Fk_inv O _ _ _ Hy) as [[m E]|[y1 [p [-> [_ [Hy1 [Hp _]]]]]]]; [discriminate|].
  pose proof (type_Lf_inv O _ Hy1) as ->.
  destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (I_eval v)) as ->.
  assert (E2 : ('K1 p) @ v ==> p) by evaluate.
  pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as ->.
  eapply Hk; [|exact H3|exact Hv|exact Hp|exact HU]; lia.
Qed.

(** ** Salary, Employee, Department *)

Definition salary_nm : Combination := Nat.iter 16 Sm Lf.
Definition employee_nm : Combination := Nat.iter 17 Sm Lf.
Definition department_nm : Combination := Nat.iter 18 Sm Lf.
Definition mks_nm : Combination := Nat.iter 19 Sm Lf.

Definition Salary := 'label[salary_nm].
Definition Employee := 'label[employee_nm].
Definition Department := 'label[department_nm].

Definition salary (k : Combination) : Combination := 'tagged[swap k, salary_nm].
Definition employee (i p : Combination) : Combination := 'tagged[swap (i '* p), employee_nm].
Definition department (m ws : Combination) : Combination := 'tagged[swap (m '* ws), department_nm].

(** The Salary constructor and the salary increment
    [salary_increment @ salary[k] = salary[succ k]]. *)
Definition mk_salary : Combination := 'tagged['tagger[salary_nm], mks_nm].
Definition D_mks : Combination := guard1 ('tagger[salary_nm]) '* ctor_elim ('wait[wg_prog, code Nat]) salary_nm.

Definition salary_succ : Combination := Eval cbn -[mk_salary mk_nat] in to_tree
  (star "k" (op mk_salary @@ (Val (Sm (Sm 'I)) @@ (Val 'K @@ (op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ Ref "k"))))))).
Definition salary_increment : Combination := Eval cbn -[salary_succ] in to_tree
  (star "s" (Ref "s" @@ Val salary_succ)).

Definition D_rows : list (Combination * Combination) :=
  (L_rows ++ [(salary_nm, D_wrap Nat); (employee_nm, D_wrap (Nat '* Salary));
              (department_nm, D_wrap (Employee '* List Employee)); (mks_nm, D_mks)])%list.
Definition O_dept : Combination := rows_f D_rows L_fam.

(** ** update_at *)

Definition update_at_b (T f : Combination) : Combination := Eval cbn -[mk_update sp_body code ch_body] in to_tree
  (star "r" (op mk_update @@ w3 (Val (code T)) (Val f) (op mk_update @@ ''wait[Val ch_body, Ref "r"]))).
Definition update_at (T f : Combination) : Combination := fix_update (update_at_b T f).

Definition salary_update : Combination := update_at Salary salary_increment.

(** ** The department *)

Fixpoint numeral (k : nat) : Combination := match k with 0 => zero | S k => succ (numeral k) end.
Definition employee_at (i k : nat) := employee (numeral i) (salary (numeral k)).
Definition department_example :=
  department (employee_at 1 58)
    (cons Employee (employee_at 2 56) (cons Employee (employee_at 3 57) (nil Employee))).
Definition incremented_department :=
  department (employee_at 1 59)
    (cons Employee (employee_at 2 57) (cons Employee (employee_at 3 58) (nil Employee))).

(** ** Soundness of the department ontology *)

Lemma O_dept_inv : forall n D, O_dept @ n @r tp O_dept ==> Sm D ->
  lookup D_rows n = Some D \/
  (n = update_nm /\ D = D_upd update_nm (tp O_dept)) \/ (n = mku_nm /\ D = D_mku (tp O_dept)) \/
  (exists r, n = list_tag r /\ D = D_list r) \/
  (exists r, n = Fk mkcons_nm r /\ concreteb r = true /\ D = D_mkcons r).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; apply L_fam_inv; exact HF.
Qed.

Lemma O_dept_static : forall n D, lookup D_rows n = Some D -> O_dept @ n @r tp O_dept ==> Sm D.
Proof.
  intros n D H; destruct (L_fam_partial n) as [p Hp]; unfold O_dept; eapply rows_f_hit; eassumption.
Qed.

Lemma O_dept_update : O_dept @ update_nm @r tp O_dept ==> Sm (D_upd update_nm (tp O_dept)).
Proof.
  unfold O_dept; apply rows_f_miss; [reflexivity|]. unfold L_fam; apply alt_some; [apply upd_fam_update|].
  apply alt_partial, list_entry_partial.
Qed.

Lemma O_dept_list : forall r, O_dept @ list_tag r @r tp O_dept ==> Sm (D_list r).
Proof.
  intros r; unfold O_dept; apply rows_f_miss; [reflexivity|]. unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_some; [apply list_entry_hit|]. apply alt_partial.
  pose proof (get_par_spec mkcons_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm list_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  Local Transparent get_par is_concrete. unfold mkcons_entry; eexists; ev2.
Qed.
Local Opaque get_par is_concrete.

Theorem O_dept_sound : ontology_sound O_dept.
Proof.
  intros n D H.
  destruct (O_dept_inv n D H) as [HL|[[-> ->]|[[-> ->]|[[r [-> ->]]|[r [-> [Hc ->]]]]]]].
  - unfold D_rows, L_rows, O_rows in HL; cbn [lookup List.app] in HL.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_dept_static; reflexivity|apply guard_of_pair].
    + eapply ctor_decl_sound; [reflexivity|apply O_dept_static; reflexivity|apply guard_of_pair].
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + apply wrap_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_dept_static; reflexivity|apply guard_of_pair].
  - apply upd_decl_sound_g, O_dept_update.
  - apply mku_decl_sound_g, O_dept_update.
  - apply list_decl_sound.
  - eapply ctor_decl_sound; [cbn; exact Hc|apply O_dept_list|apply guard_of_pair].
Qed.

Corollary O_dept_typing_sound : typing_sound O_dept.
Proof. apply evaluation_preserves_typing, O_dept_sound. Qed.

(** ** The department example *)

Ltac by_run_big := apply (runp_sound 40); vm_done.

Example salary_typed : infer O_dept @ salary (numeral 3) ==> Sm Salary. Proof. by_run_big. Qed.
Example employee_typed : infer O_dept @ employee_at 1 3 ==> Sm Employee. Proof. by_run_big. Qed.
Example salary_increment_typed : infer_expression O_dept @ (salary_increment @ salary (numeral 3)) ==> Sm Salary.
Proof. by_run_big. Qed.
Example salary_increment_eval : salary_increment @ salary (numeral 3) ==> salary (numeral 4). Proof. by_run_big. Qed.
Theorem salary_update_typed : infer O_dept @ salary_update ==> Sm Update. Proof. by_run_big. Qed.
Theorem department_example_typed : infer O_dept @ department_example ==> Sm Department. Proof. by_run_big. Qed.
Theorem salary_update_department_2025 : salary_update @ department_example ==> incremented_department.
Proof. by_run_big. Qed.
Theorem salary_update_department_typed :
  infer_expression O_dept @ (salary_update @ department_example) ==> Sm Department.
Proof. by_run_big. Qed.
Theorem incremented_department_typed : infer O_dept @ incremented_department ==> Sm Department.
Proof.
  exact (preservation O_dept O_dept_sound _ _ _ salary_update_department_2025 salary_update_department_typed).
Qed.

(** Children rewrite carriers inside tags: one salary on its own. *)
Example update_at_salary : salary_update @ salary (numeral 3) ==> salary (numeral 4). Proof. by_run_big. Qed.
Example update_at_employee : salary_update @ employee_at 2 56 ==> employee_at 2 57. Proof. by_run_big. Qed.

(** ** The typing of update_at, for every ontology with Update and its constructor *)

Definition update_at_gen (T mk f : Combination) : Combination := Eval cbn -[sp_body code ch_body] in to_tree
  (star "r" (op mk @@ w3 (Val (code T)) (Val f) (op mk @@ ''wait[Val ch_body, Ref "r"]))).

Lemma update_at_b_gen : forall T f, update_at_b T f = update_at_gen T mk_update f.
Proof. reflexivity. Qed.

Local Opaque get_l get_r get_s isK.

Lemma ctor_elim_fwd : forall g b m r U, g @ U ==> 'K -> ctor_elim g b @ m @r r @r U ==> Sm ('label[b]).
Proof.
  intros g b m r U H; unfold ctor_elim.
  pose proof (isK_spec 'K) as HK; cbn in HK.
  eapply eval_appl; [eapply eval_appl; [apply wait2_eval; unfold ctor_prog; evaluate|]|]; ev2.
Qed.

Lemma gch_hit : forall m, 'wait[gch_prog, m] @ 'wait[ch_body, 'label[m]] ==> 'K.
Proof. intros m; apply wait_eval; unfold gch_prog; pose proof (equal_eq ('wait[ch_body, 'label[m]])) as He; ev2. Qed.

Lemma gfx_hit : forall m a B, a @ B @r 'label[m] ==> Sm ('label[m]) ->
  'wait2[gfx_prog, m, a] @ Z (B 'C 'tagger[m]) ==> 'K.
Proof.
  intros m a B H; apply wait2_eval; unfold gfx_prog, Z, self_apply, wait1.
  pose proof (equal_eq ('label[m])) as He2; ev_many.
Qed.

Lemma gsp_miss_Z : forall m a X, 'wait2[gsp_prog, m, a] @ Z X ==> 'KI.
Proof.
  intros m a X; apply wait2_eval; unfold gsp_prog, Z, self_apply, wait1.
  split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | (apply equal1_neq; cbn [left_of right_of stem_of]; discriminate)
    | progress cbn [left_of right_of stem_of] | progress evaluate2].
Qed.

Section UpdateAt.
Variable O : Combination.
Hypothesis HO : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).
Hypothesis HM : O @ mku_nm @r tp O ==> Sm (D_mku (tp O)).

Lemma mku_app : forall X, upd_guard update_nm (tp O) @ X ==> 'K ->
  tp O @ 'label[mku_nm] @r X ==> Sm ('label[update_nm]).
Proof using HM.
  intros X H; eapply tp_abs; [exact HM|]. apply elim_of_fwd, ctor_elim_fwd; exact H.
Qed.

Lemma mk_update_typed_g : infer O @ mk_update ==> Sm ('label[mku_nm]).
Proof using HM.
  eapply infer_tag; [reflexivity|apply concrete_is_self_typed; reflexivity|exact HM|].
  eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec ('tagger[update_nm]) ('tagger[update_nm])) as E.
  destruct (combination_eq_dec ('tagger[update_nm]) ('tagger[update_nm])) as [_|n]; [exact E|contradiction].
Qed.

Ltac tpf := repeat first
  [ eassumption
  | (apply mku_app; unfold upd_guard;
       first [ (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|]; apply or_g_l; apply gch_hit)
             | (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gch_miss; discriminate|reflexivity|]; apply or_g_l; apply gsp_hit; eassumption) ])
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [reflexivity| | |])
  | (apply tp_stem; reflexivity)
  | apply tp_leaf_fwd ].

Theorem update_at_typed : forall T f F, names_concrete T -> infer O @ f ==> Sm F ->
  tp O @ F @r T ==> Sm T -> infer O @ update_at T f ==> Sm Update.
Proof using HO HM.
  intros T f F HT Hf HF.
  pose proof (code_self_typed O T HT) as HiT.
  pose proof mk_update_typed_g as Hmk.
  assert (Hb : infer O @ update_at_b T f ==> Sm (update_at_gen T ('label[mku_nm]) F))
    by (rewrite update_at_b_gen; unfold update_at_gen; build O).
  assert (HB : tp O @ update_at_gen T ('label[mku_nm]) F @r 'label[update_nm] ==> Sm ('label[update_nm]))
    by (unfold update_at_gen; tpf).
  assert (Hc : infer O @ Z (update_at_b T f 'C 'tagger[update_nm]) ==>
               Sm (Z (update_at_gen T ('label[mku_nm]) F 'C 'tagger[update_nm])))
    by (unfold Z, self_apply, wait1; build O).
  eapply infer_tag; [reflexivity|exact Hc|exact HO|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard.
  eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gch_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit; exact HB].
Qed.
End UpdateAt.
