(** * Step 82, stage 4: the salary bill of the department (a query), and
    the arithmetic examples of the recursion section. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic.
Open Scope string_scope.
Set Default Proof Using "Type".

(** [salary_of @ e]: the salary amount of an employee. *)
Definition salary_of_t (e : Term) : Term := e @@ star "q" ((Val 'snd @@ Ref "q") @@ Val 'I).
Definition bill_step : Combination := Eval cbn -[add] in to_tree
  (star "s" (op add @@ (salary_of_t (Val 'fst @@ Ref "s") ''* (Val 'snd @@ Ref "s")))).
Definition bill_fn : Combination := Eval cbn -[add lit bill_step zero] in to_tree
  (star "d" (Ref "d" @@ star "p" (op add @@ (salary_of_t (Val 'fst @@ Ref "p") ''*
     (Val 'snd @@ (op (lit Employee Nat bill_step) @@ ((Val 'snd @@ Ref "p") ''* Val zero))))))).
Definition salary_bill : Combination := special_query Nat Department bill_fn (Kq Nat zero).

Ltac by_runB := apply (runp_sound 40); vm_done.

Theorem salary_bill_typed : infer O_q @ salary_bill ==> Sm (Query Nat). Proof. by_runB. Qed.
Theorem salary_bill_department : salary_bill @ department_example ==> numeral 171. Proof. by_runB. Qed.
Theorem salary_bill_department_typed : infer_expression O_q @ (salary_bill @ department_example) ==> Sm Nat.
Proof. by_runB. Qed.
