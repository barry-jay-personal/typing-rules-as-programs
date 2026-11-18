(** * Step 82, stage 5, part 5: update theorems, patching, salary queries.

    - [abstract_update_preserves_typing], [update_preserves_expression_typing]
      (every ontology sound by values that declares Update);
    - [infer_update_salary] ([update_at[Salary,f] : Update]);
    - [eval_iff_bounded];
    - the query [paid_over[t]] and the lambda program [paid_at_least[t]],
      which hold their threshold as [salary[t]] in the program tree,
      where the salary update reaches it. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology fun_ontology self_typing size_queries poly.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

Ltac by_run5 := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** Evaluation and bounded evaluation *)

Theorem eval_iff_bounded : forall e v, e ==> v <-> exists k, evaln k e v.
Proof.
  intros e v; split; [apply eval_evaln|intros [k Hk]; exact (evaln_eval _ _ _ Hk)].
Qed.

(** ** Updates preserve value types and expression types *)

Section UpdatesPreserve.
Variable O : Combination.
Hypothesis HS : ontology_sound O.
Hypothesis HO : O @ update_nm @r tp O ==> Sm (D_upd update_nm (tp O)).

Theorem abstract_update_preserves_typing : forall u x y U,
  infer O @ u ==> Sm Update -> infer O @ x ==> Sm U -> u @ x ==> y -> infer O @ y ==> Sm U.
Proof using HS HO.
  intros u x y U Hu Hx Hy; eapply (tp_sound O HS); [exact Hu|exact Hx|apply (Update_app_g O HO)|exact Hy].
Qed.

(** [ie_Lf_none], [ie_K1_none] and [expression_value_type] are in size_queries.v (step 87). *)

Theorem update_preserves_expression_typing : forall u e e' T,
  infer O @ u ==> Sm Update -> infer_expression O @ e ==> Sm T -> u @ e ==> e' ->
  infer_expression O @ e' ==> Sm T.
Proof using HS HO.
  intros u e e' T Hu He Hue.
  destruct (expression_value_type O _ _ He) as [V [Hv Hk]].
  apply Hk; eapply abstract_update_preserves_typing; eassumption.
Qed.
End UpdatesPreserve.

(** ** update[Salary, f] *)

Lemma PO_mku' : PO @ mku_nm @r tp PO ==> Sm (D_mku (tp PO)).
Proof. exact PO_mku. Qed.

Theorem infer_update_salary : forall f F, infer PO @ f ==> Sm F -> tp PO @ F @r Salary ==> Sm Salary ->
  infer PO @ update_at Salary f ==> Sm Update.
Proof.
  intros f F Hf HF; apply (update_at_typed PO PO_update PO_mku Salary f F); [cbn; reflexivity|exact Hf|exact HF].
Qed.

(** ** Selecting employees: the threshold is a salary held in the program *)

(** [ge_sal @ (s1 * s2) = (amount s2 >= amount s1)]. *)
Definition ge_sal : Combination := Eval cbn -[ge] in to_tree
  (star "q" ((Val 'fst @@ Ref "q") @@ star "k1" ((Val 'snd @@ Ref "q") @@ star "k2" (op ge @@ (Ref "k1" ''* Ref "k2"))))).
Definition pred_at (t : nat) : Combination := Eval cbn -[ge_sal salary numeral] in to_tree
  (star "e" (Ref "e" @@ star "q" (op ge_sal @@ (Val (salary (numeral t)) ''* (Val 'snd @@ Ref "q"))))).
Definition select_at (t : nat) : Combination := Eval cbn -[filterR gen_cons pred_at code Employee] in to_tree
  (star "d" (op filterR @@ (Val (code Employee) ''* (op (pred_at t) ''*
     (Ref "d" @@ star "p" (op gen_cons @@ (Val (code Employee) ''* Ref "p"))))))).

Definition paid_over (t : nat) : Combination :=
  special_query (List Employee) Department (select_at t) (Kq (List Employee) (nil Employee)).
Definition paid_at_least (t : nat) : Combination := lam (select_at t) Department (List Employee).

Definition L57 : Combination := cons Employee (employee_at 1 58) (cons Employee (employee_at 3 57) (nil Employee)).
Definition L58 : Combination := cons Employee (employee_at 1 59) (cons Employee (employee_at 3 58) (nil Employee)).

(** [paid_over[t] : Query[List[Emp]]] for every numeral [t] (stage 9).
    Inference is structural, so it follows the spine of the program tree
    down to the threshold [numeral t], which has type Nat by induction;
    the closed subtrees beside the spine are typed by computation. *)
Lemma numeral_Nat : forall t, infer PO @ numeral t ==> Sm Nat.
Proof. induction t as [|t IH]; [apply paper_infer_zero|apply paper_infer_succ, IH]. Qed.

Ltac inf_spine t :=
  lazymatch goal with
  | |- infer PO @ ?X ==> Sm _ =>
    lazymatch X with
    | numeral t => apply numeral_Nat
    | context[t] =>
        let X' := eval hnf in X in
        lazymatch X' with
        | Sm _ => eapply infer_stem; inf_spine t
        | Fk _ _ =>
            let tg := eval vm_compute in (tag_of X') in
            lazymatch tg with
            | None => eapply infer_fork; [vm_compute; reflexivity|inf_spine t|inf_spine t|vm_compute; reflexivity]
            | Some _ => eapply infer_tag; [vm_compute; reflexivity|inf_spine t|by_run5|by_run5]
            end
        end
    | _ => by_run5
    end
  end.

Theorem paid_over_typed : forall t, infer PO @ paid_over t ==> Sm (Query (List Employee)).
Proof. intros t; inf_spine t. Qed.

Theorem paid_over_57_typed : infer PO @ paid_over 57 ==> Sm (Query (List Employee)). Proof. exact (paid_over_typed 57). Qed.
Theorem paid_over_57_original : paid_over 57 @ department_example ==> L57. Proof. by_run5. Qed.




Theorem paid_at_least_57_typed : infer fun_ontology @ paid_at_least 57 ==> Sm (Fun Department (List Employee)).
Proof. by_run5. Qed.
Theorem paid_at_least_58_typed : infer fun_ontology @ paid_at_least 58 ==> Sm (Fun Department (List Employee)).
Proof. by_run5. Qed.
