(** * Step 82 (stage 1): ontologies as rows.

    An ontology is a program [O] with [O @ n @r a ==> Sm D] when the name
    [n] is declared with declaration [D], and [O @ n @r a ==> Lf]
    otherwise.  [rows] builds it from a list of names and declarations:
    the first row whose name equals [n] answers.  Declarations are pairs
    [g '* e] of a guard and an eliminator; small guard programs are
    defined here too. *)

From BigStep Require Import tree typing.
From Stdlib Require Import String Bool List.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Lemma wait3_eval : forall M a b c u v, M @ a @r b @r c @r u ==> v -> 'wait3[M, a, b, c] @ u ==> v.
Proof. intros; invert_eval; evaluate; repeat (eapply eval_appl; [eassumption|]); evaluate. Qed.

Lemma wait3_eval_inv : forall M a b c u v, 'wait3[M, a, b, c] @ u ==> v -> M @ a @r b @r c @r u ==> v.
Proof. intros; invert_eval; eapply eval_appl; eauto; eapply eval_appl; eauto; eapply eval_appl; eauto. Qed.

Lemma equal_bt : forall p q, equal @ p @r q ==> bt (if combination_eq_dec p q then true else false).
Proof.
  intros p q; destruct (combination_eq_dec p q) as [->|H]; cbn [bt];
    [apply equal_eq|apply equal_neq; exact H].
Qed.

Local Opaque equal.

(** ** Rows *)

(** [row_prog @ m @ D @ rest @ n ==> K1 (Sm D)] when [m = n], else
    [rest @ n]. *)
Definition row_prog : Combination := Eval cbn -[equal] in to_tree
  (star "m" (star "D" (star "rest" (star "n"
    (op equal @@ Ref "m" @@ Ref "n" @@ (Val 'K @@ (Val Lf @@ Ref "D")) @@ (Ref "rest" @@ Ref "n")))))).

Definition row (m D rest : Combination) : Combination := 'wait3[row_prog, m, D, rest].

Definition no_rows : Combination := 'K1 ('K1 Lf).

Fixpoint rows (rs : list (Combination * Combination)) : Combination :=
  match rs with
  | [] => no_rows
  | (m, D) :: rs' => row m D (rows rs')
  end.

Fixpoint lookup (rs : list (Combination * Combination)) (n : Combination) : option Combination :=
  match rs with
  | [] => None
  | (m, D) :: rs' => if combination_eq_dec m n then Some D else lookup rs' n
  end.

Lemma row_head : forall m D rest n r, rest @ n ==> r ->
  row m D rest @ n ==> (if combination_eq_dec m n then 'K1 (Sm D) else r).
Proof.
  intros m D rest n r Hr; apply wait3_eval; unfold row_prog.
  pose proof (equal_bt m n) as He; inv_out He.
  destruct (combination_eq_dec m n); cbn [bt] in *; evaluate2;
    first [eassumption | evaluate2].
Qed.

Lemma rows_head : forall rs n, exists r, rows rs @ n ==> r /\
  forall a, r @ a ==> opt (lookup rs n).
Proof.
  induction rs as [|[m D] rs IH]; intros n.
  - exists ('K1 Lf); split; [unfold rows, no_rows; evaluate|intros; cbn; evaluate].
  - destruct (IH n) as [r [Hr Ha]]; cbn [rows lookup].
    exists (if combination_eq_dec m n then 'K1 (Sm D) else r); split; [apply row_head; exact Hr|].
    intros a; destruct (combination_eq_dec m n); [cbn; evaluate|apply Ha].
Qed.

Theorem rows_spec : forall rs n a, rows rs @ n @r a ==> opt (lookup rs n).
Proof.
  intros rs n a; destruct (rows_head rs n) as [r [Hr Ha]]; eapply eval_appl; [exact Hr|apply Ha].
Qed.

(** ** Guards *)

(** [guard1 c] admits exactly [c]. *)
Definition guard1 (c : Combination) : Combination := 'wait[equal, c].

Lemma guard1_spec : forall c C, guard1 c @ C ==> bt (if combination_eq_dec c C then true else false).
Proof. intros; apply wait_eval; apply equal_bt. Qed.

(** [guard2 c1 c2] admits exactly [c1] and [c2]. *)
Definition guard2_prog : Combination := Eval cbn -[equal] in to_tree
  (star "c1" (star "c2" (star "C"
    (op equal @@ Ref "C" @@ Ref "c1" @@ Val 'K @@ (op equal @@ Ref "C" @@ Ref "c2"))))).

Definition guard2 (c1 c2 : Combination) : Combination := 'wait2[guard2_prog, c1, c2].

Definition in2b (c1 c2 C : Combination) : bool :=
  (if combination_eq_dec C c1 then true else false) || (if combination_eq_dec C c2 then true else false).

Lemma guard2_spec : forall c1 c2 C, guard2 c1 c2 @ C ==> bt (in2b c1 c2 C).
Proof.
  intros c1 c2 C; apply wait2_eval; unfold guard2_prog, in2b.
  pose proof (equal_bt C c1) as H1; pose proof (equal_bt C c2) as H2.
  destruct (combination_eq_dec C c1); destruct (combination_eq_dec C c2); cbn [bt orb] in *; ev.
Qed.

Lemma in2b_true : forall c1 c2 C, in2b c1 c2 C = true -> C = c1 \/ C = c2.
Proof.
  unfold in2b; intros c1 c2 C H;
  destruct (combination_eq_dec C c1); destruct (combination_eq_dec C c2); cbn in H; auto; discriminate.
Qed.

(** [guard_lab c m] admits exactly [c] and [K1 label[m]]; the label is
    built when the guard runs, so the guard contains none. *)
Definition guard_lab_prog : Combination := Eval cbn -[equal] in to_tree
  (star "c" (star "m" (star "C"
    (op equal @@ Ref "C" @@ Ref "c" @@ Val 'K
       @@ (op equal @@ Ref "C" @@ (Val 'K @@ (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "m")))))))).

Definition guard_lab (c m : Combination) : Combination := 'wait2[guard_lab_prog, c, m].

Lemma guard_lab_spec : forall c m C, guard_lab c m @ C ==> bt (in2b c ('K1 ('label[m])) C).
Proof.
  intros c m C; apply wait2_eval; unfold guard_lab_prog, in2b.
  pose proof (equal_bt C c) as H1; pose proof (equal_bt C ('K1 ('label[m]))) as H2.
  destruct (combination_eq_dec C c); destruct (combination_eq_dec C ('K1 ('label[m]))); cbn [bt orb] in *; ev.
Qed.

(** The eliminator that refuses every argument type. *)
Definition refuse_elim : Combination := 'K1 ('K1 ('K1 Lf)).

Lemma refuse_elim_spec : forall n a U, refuse_elim @ n @r a @r U ==> Lf.
Proof. intros; unfold refuse_elim; evaluate. Qed.

(** ** Rows over a family (stage 2)

    [rows_f rs fam] tries the rows [rs] and then the family program
    [fam], which computes declarations for whole families of names (such
    as function types) from the name and the type application it
    receives.  [alt p q] tries the family [p] and then [q]. *)

Fixpoint rows_f (rs : list (Combination * Combination)) (fam : Combination) : Combination :=
  match rs with
  | [] => fam
  | (m, D) :: rs' => row m D (rows_f rs' fam)
  end.

Lemma row_inv : forall m D rest n a v, row m D rest @ n @r a ==> v ->
  (m = n /\ v = Sm D) \/ (m <> n /\ rest @ n @r a ==> v).
Proof.
  intros m D rest n a v H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  apply wait3_eval_inv in Hp; unfold row_prog in Hp.
  pose proof (equal_bt m n) as He; inv_out He.
  destruct (combination_eq_dec m n) as [E|E]; cbn [bt] in *; crunch; fin.
Qed.

Lemma rows_f_inv : forall rs fam n a v, rows_f rs fam @ n @r a ==> v ->
  (exists D, lookup rs n = Some D /\ v = Sm D) \/ (lookup rs n = None /\ fam @ n @r a ==> v).
Proof.
  induction rs as [|[m D] rs IH]; intros fam n a v H; cbn [rows_f lookup] in *.
  - right; auto.
  - destruct (row_inv _ _ _ _ _ _ H) as [[-> ->]|[E H1]].
    + left; exists D; destruct (combination_eq_dec n n); [auto|contradiction].
    + destruct (combination_eq_dec m n); [contradiction|]. apply IH; exact H1.
Qed.

Lemma rows_f_head : forall rs fam n p, fam @ n ==> p -> exists r, rows_f rs fam @ n ==> r /\
  forall a v, (match lookup rs n with Some D => Sm D = v | None => p @ a ==> v end) -> r @ a ==> v.
Proof.
  induction rs as [|[m D] rs IH]; intros fam n p Hp; cbn [rows_f lookup].
  - exists p; split; [exact Hp|auto].
  - destruct (IH fam n p Hp) as [r [Hr Ha]].
    exists (if combination_eq_dec m n then 'K1 (Sm D) else r); split; [apply row_head; exact Hr|].
    intros a v Hv; destruct (combination_eq_dec m n); [subst; cbn; evaluate|apply Ha; exact Hv].
Qed.

Lemma rows_f_hit : forall rs fam n a D p, fam @ n ==> p -> lookup rs n = Some D ->
  rows_f rs fam @ n @r a ==> Sm D.
Proof.
  intros rs fam n a D p Hp HL; destruct (rows_f_head rs fam n p Hp) as [r [Hr Ha]].
  eapply eval_appl; [exact Hr|apply Ha; rewrite HL; reflexivity].
Qed.

Lemma rows_f_miss : forall rs fam n a v, lookup rs n = None -> fam @ n @r a ==> v ->
  rows_f rs fam @ n @r a ==> v.
Proof.
  intros rs fam n a v HL H; destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]].
  destruct (rows_f_head rs fam n p Hp) as [r [Hr Ha]].
  eapply eval_appl; [exact Hr|apply Ha; rewrite HL; exact Hq].
Qed.

Definition alt_prog : Combination := Eval cbv in to_tree
  (star "p" (star "q" (star "n" (star "a"
    (''triage[Ref "q", star "D" (''K1 (''K1 (Val Lf @@ Ref "D"))), Val ('K1 ('K1 ('K1 ('K1 Lf))))]
       @@ (Ref "p" @@ Ref "n" @@ Ref "a") @@ Ref "n" @@ Ref "a"))))).

Definition alt (p q : Combination) : Combination := 'wait2[alt_prog, p, q].

Lemma alt_inv : forall p q n a v, alt p q @ n @r a ==> v ->
  (exists D, p @ n @r a ==> Sm D /\ v = Sm D) \/
  (p @ n @r a ==> Lf /\ q @ n @r a ==> v) \/
  (exists x y, p @ n @r a ==> Fk x y /\ v = Lf).
Proof.
  intros p q n a v H; destruct (appl_inv _ _ _ _ H) as [w [Hw Hq]]; clear H.
  apply wait2_eval_inv in Hw; unfold alt_prog in Hw.
  crunch; fin.
Qed.

Lemma alt_some : forall p q n a D, p @ n @r a ==> Sm D -> (exists r, q @ n ==> r) -> alt p q @ n @r a ==> Sm D.
Proof.
  intros p q n a D H [r Hr]; unfold alt.
  destruct (appl_inv _ _ _ _ H) as [w [Hw Hq]].
  eapply eval_appl; [apply wait2_eval; unfold alt_prog|]; ev.
Qed.

Lemma alt_none : forall p q n a v, p @ n @r a ==> Lf -> q @ n @r a ==> v -> alt p q @ n @r a ==> v.
Proof.
  intros p q n a v H Hq0; unfold alt.
  destruct (appl_inv _ _ _ _ H) as [w [Hw Hq]].
  destruct (appl_inv _ _ _ _ Hq0) as [w' [Hw' Hq']].
  eapply eval_appl; [apply wait2_eval; unfold alt_prog|]; ev.
Qed.

(** [get_par h @ n ==> Sm r] when [n = Fk h r], and [Lf] otherwise. *)
Definition get_par_prog : Combination := Eval cbn -[equal] in to_tree
  (star "h" (star "n"
    (''triage[Val Lf, Val ('K1 Lf),
              star "h2" (star "r" (op equal @@ Ref "h" @@ Ref "h2" @@ (Val Lf @@ Ref "r") @@ Val Lf))]
       @@ Ref "n"))).
Definition get_par (h : Combination) : Combination := 'wait[get_par_prog, h].

Definition par_of (h n : Combination) : option Combination :=
  match n with Fk h2 r => if combination_eq_dec h h2 then Some r else None | _ => None end.

Lemma get_par_spec : forall h n, get_par h @ n ==> opt (par_of h n).
Proof.
  intros h n; apply wait_eval; unfold get_par_prog.
  pose proof (equal_eval h) as Hh.
  destruct n as [|n|h2 r]; cbn [par_of opt]; [evaluate|evaluate|].
  pose proof (equal_bt h h2) as He; inv_out He; dedup.
  destruct (combination_eq_dec h h2); cbn [bt opt] in *; ev.
Qed.

Lemma par_of_some : forall h n r, par_of h n = Some r -> n = Fk h r.
Proof.
  intros h n r H; destruct n as [|n|h2 r']; cbn in H; try discriminate.
  destruct (combination_eq_dec h h2); inversion H; subst; reflexivity.
Qed.
