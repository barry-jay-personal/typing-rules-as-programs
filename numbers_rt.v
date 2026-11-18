(** * Step 82, stage 7, part 2: numbers.

    - [add_Z]: addition of Scott numerals by [Z] alone.  Its typing at
      [Nat * Nat] contains itself ([add_Z_typing_diverges]), found by
      [cycle_check] (ported from src_type36/step21_recursion.v, with the
      lazily fuelled [runp] for the partial application).
    - Collatz: an update on the plain state [n * c : Nat * Nat], recognised
      by its type; its step chooses between two arms of one type, as the
      search of minimisation does:
        step r @ x = le1 (fst x) @ (S2[K1 identity_update, K1 x] *
                                    S2[K1 r, K1 (next (fst x) * succ (snd x))]) @ x
      and [collatz_ext @ n] reads off the count. *)

From Stdlib Require Import String List Bool Lia PeanoNat.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology scott_arithmetic poly.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

Definition tyP (t : Combination) : Combination :=
  match runp 40 (infer PO @ t) with Some (Sm A) => A | _ => Lf end.
Ltac by_runN := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** Detecting a typing that contains itself (ported from step21_recursion.v) *)

Fixpoint teqr (a b : Combination) : bool :=
  match a, b with
  | Lf, Lf => true
  | Sm x, Sm y => teqr x y
  | Fk x1 x2, Fk y1 y2 => if teqr x2 y2 then teqr x1 y1 else false
  | _, _ => false
  end.
Lemma teqr_eq : forall a b, teqr a b = true -> a = b.
Proof.
  induction a as [|x IH|x1 IH1 x2 IH2]; intros [|y|y1 y2] H; cbn in H; try discriminate.
  - reflexivity.
  - f_equal; apply IH, H.
  - destruct (teqr x2 y2) eqn:E2; [|discriminate].
    rewrite (IH1 _ H), (IH2 _ E2); reflexivity.
Qed.

Inductive fres := FVal (v : Combination) | FFound | FOut.

Fixpoint eval_find (t : Combination) (n : nat) (e : Combination) : fres :=
  let sub n x := if teqr x t then FFound else eval_find t n x in
  match n with
  | O => FOut
  | S n =>
    match e with
    | Lf => FOut
    | Sm v => FVal v
    | Fk (Sm v1) (Sm v2) =>
      match v1 with
      | Lf => FVal (Sm v2)
      | Sm v => FVal (Fk v v2)
      | Fk Lf y => FVal y
      | Fk (Sm g) f => sub n (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2)))
      | Fk (Fk f0 f1) f2 =>
        match v2 with
        | Lf => FVal f0
        | Sm u => sub n (Fk (Sm f1) (Sm u))
        | Fk u1 u2 => sub n (Fk (Fk (Sm f2) (Sm u1)) (Sm u2))
        end
      end
    | Fk (Sm v1) (Fk a b) =>
      match sub n (Fk a b) with
      | FVal v2 => sub n (Fk (Sm v1) (Sm v2))
      | r => r
      end
    | Fk (Fk a b) e2 =>
      match sub n (Fk a b) with
      | FVal v1 => sub n (Fk (Sm v1) e2)
      | r => r
      end
    | Fk Lf _ | Fk (Sm _) Lf => FOut
    end
  end.

Lemma eval_find_val : forall n t e v, eval_find t n e = FVal v -> e ==> v.
Proof.
  induction n as [|n IH]; intros t e v H; [discriminate|].
  assert (Hs : forall x w, (if teqr x t then FFound else eval_find t n x) = FVal w -> x ==> w).
  { intros x w Hx; destruct (teqr x t); [discriminate|exact (IH _ _ _ Hx)]. }
  destruct e as [|v0|[|v1|a b] e2]; cbn [eval_find] in H; try discriminate.
  - inversion H; constructor.
  - destruct e2 as [|v2|c d]; try discriminate.
    + destruct v1 as [|w|[|g|f0 f1] f2].
      * inversion H; constructor.
      * inversion H; constructor.
      * inversion H; constructor.
      * apply eval_s, Hs, H.
      * destruct v2 as [|u|u1 u2].
        -- inversion H; constructor.
        -- apply eval_stem, Hs, H.
        -- apply eval_fork, Hs, H.
    + destruct (if teqr (Fk c d) t then FFound else eval_find t n (Fk c d)) as [v2| |] eqn:E;
        try discriminate.
      eapply eval_appr; [apply Hs, E|apply Hs, H].
  - destruct (if teqr (Fk a b) t then FFound else eval_find t n (Fk a b)) as [w| |] eqn:E;
      try discriminate.
    eapply eval_appl; [apply Hs, E|apply Hs, H].
Qed.

Lemma eval_find_found : forall n t e, eval_find t n e = FFound ->
  forall h v, evaln h e v -> exists m w, m < h /\ evaln m t w.
Proof.
  induction n as [|n IH]; intros t e H h v Hev; [discriminate|].
  assert (Hs : forall x h' w, (if teqr x t then FFound else eval_find t n x) = FFound ->
     evaln h' x w -> exists m w', m <= h' /\ evaln m t w').
  { intros x h' w Hx Hw; destruct (teqr x t) eqn:Et.
    - apply teqr_eq in Et; subst x; exists h', w; split; [lia|exact Hw].
    - destruct (IH _ _ Hx _ _ Hw) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw']. }
  assert (Hv : forall x w, (if teqr x t then FFound else eval_find t n x) = FVal w -> x ==> w).
  { intros x w Hx; destruct (teqr x t); [discriminate|exact (eval_find_val _ _ _ _ Hx)]. }
  destruct e as [|v0|[|v1|a b] e2]; cbn [eval_find] in H; try discriminate.
  - destruct e2 as [|v2|c d]; try discriminate.
    + destruct v1 as [|w|[|g|f0 f1] f2]; try discriminate.
      * inversion Hev; subst;
          match goal with Hp : evaln _ _ _ |- _ =>
            destruct (Hs _ _ _ H Hp) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
      * destruct v2 as [|u|u1 u2]; try discriminate; inversion Hev; subst;
          match goal with Hp : evaln _ _ _ |- _ =>
            destruct (Hs _ _ _ H Hp) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
    + inversion Hev; subst.
      destruct (if teqr (Fk c d) t then FFound else eval_find t n (Fk c d)) as [v2'| |] eqn:E;
        try discriminate.
      * match goal with H1 : evaln _ (Fk c d) ?v2 , H2 : evaln _ (Fk (Sm _) (Sm ?v2)) _ |- _ =>
          pose proof (eval_deterministic _ _ (Hv _ _ E) _ (evaln_eval _ _ _ H1)) as <-;
          destruct (Hs _ _ _ H H2) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
      * match goal with H1 : evaln _ (Fk c d) _ |- _ =>
          destruct (Hs _ _ _ E H1) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
  - inversion Hev; subst.
    destruct (if teqr (Fk a b) t then FFound else eval_find t n (Fk a b)) as [v1'| |] eqn:E;
      try discriminate.
    + match goal with H1 : evaln _ (Fk a b) ?v1 , H2 : evaln _ (Fk (Sm ?v1) e2) _ |- _ =>
        pose proof (eval_deterministic _ _ (Hv _ _ E) _ (evaln_eval _ _ _ H1)) as <-;
        destruct (Hs _ _ _ H H2) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
    + match goal with H1 : evaln _ (Fk a b) _ |- _ =>
        destruct (Hs _ _ _ E H1) as [m [w' [Hm Hw']]]; exists m, w'; split; [lia|exact Hw'] end.
Qed.

Lemma eval_find_diverges : forall n t, eval_find t n t = FFound -> forall v, ~ t ==> v.
Proof.
  intros n t H v Hv; destruct (eval_evaln _ _ Hv) as [h Hh]; clear Hv.
  revert v Hh; induction h as [h IHh] using (well_founded_induction Wf_nat.lt_wf); intros v Hh.
  destruct (eval_find_found _ _ _ H _ _ Hh) as [m [w [Hm Hw]]].
  exact (IHh m Hm w Hw).
Qed.

(** [cycle_check d w X] looks for [w @ X] inside the evaluation of [w @ X]
    (to depth [d]).  If it finds it and [E ==> w], then [E @r X] has no value. *)
Definition cycle_check (d : nat) (w X : Combination) : bool :=
  match eval_find (Fk (Sm w) (Sm X)) d (Fk (Sm w) (Sm X)) with FFound => true | _ => false end.

Lemma cycle_check_diverges : forall d f x w X R, f @ x ==> w -> cycle_check d w X = true -> ~ f @ x @r X ==> R.
Proof.
  intros d f x w X R Ew Hc HR; unfold cycle_check in Hc.
  destruct (eval_find _ d _) eqn:Ef; try discriminate.
  apply (eval_find_diverges _ _ Ef R).
  destruct (app2_inv _ _ _ _ HR) as [w' [Hw' Hr]].
  pose proof (eval_deterministic _ _ Hw' _ Ew) as ->; exact Hr.
Qed.

(** ** Addition by Z alone

      add_Z @ (m * n) = m @ (n * \p. succ[add_Z @ (p * n)])
    with [succ] built by the constructor [mk_nat]. *)
Definition succ_t (x : Term) : Term := op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ x)).
Definition add_Z_term : Term :=
  let q := Ref "q" in
  star "self" (star "q"
    ((Val 'fst @@ q) @@ ((Val 'snd @@ q) ''* (star "p" (succ_t (Ref "self" @@ (Ref "p" ''* (Val 'snd @@ q)))))))).
Definition add_Z_body : Combination := Eval cbn -[mk_nat] in to_tree add_Z_term.
Definition add_Z : Combination := Z add_Z_body.
Definition T_addZ : Combination := Eval vm_compute in tyP add_Z.

Lemma infer_add_Z : infer PO @ add_Z ==> Sm T_addZ. Proof. by_runN. Qed.
Example add_Z_numerals : add_Z @ (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_runN. Qed.

(** The typing of [add_Z] at [Nat * Nat] has no result: it neither
    succeeds nor refuses.  At [Nat * Nat] the eliminator of [Nat] checks the
    successor case at [Nat], which applies [add_Z] at [Nat * Nat] again. *)
Definition w_addZ : Combination := Eval vm_compute in
  match runp 40 (tp PO @ T_addZ) with Some w => w | None => Lf end.
Lemma tp_addZ_partial : tp PO @ T_addZ ==> w_addZ. Proof. by_runN. Qed.

Theorem add_Z_typing_diverges : forall R, ~ tp PO @ T_addZ @r (Nat '* Nat) ==> R.
Proof. intros R; apply (cycle_check_diverges 3000 _ _ _ _ R tp_addZ_partial); vm_compute; reflexivity. Qed.

Corollary add_Z_application_untyped : forall m n T,
  infer PO @ m ==> Sm Nat -> infer PO @ n ==> Sm Nat ->
  ~ infer_expression PO @ (add_Z @ (m '* n)) ==> Sm T.
Proof.
  intros m n T Hm Hn H.
  destruct (ie_inv _ _ _ H) as [[u [E _]]|[e1 [e2 [T1 [T2 [E [H1 [H2 H3]]]]]]]]; [discriminate|].
  inversion E; subst.
  destruct (ie_inv _ _ _ H1) as [[u [E1 Hu]]|[a [b [_ [_ [E1 _]]]]]]; [|discriminate].
  destruct (ie_inv _ _ _ H2) as [[u2 [E2 Hu2]]|[a [b [_ [_ [E2 _]]]]]]; [|discriminate].
  inversion E1; inversion E2; subst.
  pose proof (eval_deterministic _ _ Hu _ infer_add_Z) as E3; inversion E3; subst.
  pose proof (eval_deterministic _ _ Hu2 _ (pair_typed _ _ _ _ _ Hm Hn)) as E4; inversion E4; subst.
  exact (add_Z_typing_diverges _ H3).
Qed.

(** ** Collatz *)

Definition one_v : Combination := succ zero.
(** [le1 n = (1 >= n)], [tp1 n = 3n+1], [half n = n/2], [cnext n]. *)
Definition le1_t (n : Term) : Term := op ge @@ (n ''* Val one_v).
Definition half_g_t (n : Term) : Term := star "a"
  ((op ge @@ ((op add @@ (succ_t (Ref "a") ''* succ_t (Ref "a"))) ''* n)) @@ (succ_t (Ref "a") ''* Ref "a")).
Definition half_t (n : Term) : Term := run_iter (Val (code Nat)) (half_g_t n) (n ''* Val zero).
Definition tp1_t (n : Term) : Term := succ_t (op add @@ (n ''* (op add @@ (n ''* n)))).
Definition cnext_t (n : Term) : Term := (op is_odd @@ n) @@ (tp1_t n ''* half_t n).

Definition cstep_t (r : Term) : Term := star "x"
  ((le1_t (Val 'fst @@ Ref "x"))
     @@ (''S2[''K1 (Val identity_update), ''K1 (Ref "x")]
         ''* ''S2[''K1 r, ''K1 (cnext_t (Val 'fst @@ Ref "x") ''* succ_t (Val 'snd @@ Ref "x"))])
     @@ Ref "x").

(** The recursive update, as a closed value (the generator of minimisation's form). *)
Definition collatz_W : Combination := Eval cbn -[mk_update sp_body identity_update self_apply bz code ge add is_odd nitR mk_nat zero] in
  to_tree (''wait[Val self_apply,
    (star "r" (op mk_update @@ w3 (Val (code NN)) (cstep_t (Ref "r")) (Val identity_update))
       ''C tagger_t (Val update_nm)) ''C Val bz]).

(** [collatz_ext @ n = snd (collatz_upd @ (n * 0))]; the update is built
    through [K1 collatz_W @ n] so that the application is not closed. *)
Definition collatz_ext : Combination := Eval cbn -[mk_update collatz_W zero] in to_tree
  (star "n" (Val 'snd @@ ((op mk_update @@ (Val ('K1 collatz_W) @@ Ref "n")) @@ (Ref "n" ''* Val zero)))).

Definition T_cext : Combination := Eval vm_compute in tyP collatz_ext.

(** The program that reads off the count has a type that takes Nat to Nat. *)
Theorem infer_collatz_ext : infer PO @ collatz_ext ==> Sm T_cext /\ tp PO @ T_cext @r Nat ==> Sm Nat.
Proof. split; by_runN. Qed.

Theorem collatz_ext_six : collatz_ext @ numeral 6 ==> numeral 8. Proof. by_runN. Qed.

Example collatz_ext_six_typed : infer_expression PO @ (collatz_ext @ numeral 6) ==> Sm Nat. Proof. by_runN. Qed.

(** ** Scott numerals and the predecessor (stage 8, ROCQ_DELTA P3) *)
Lemma zero_apply : forall b s, zero @ (b '* s) ==> b.
Proof. intros; unfold zero; apply tagged_eval; evaluate. Qed.
Lemma succ_apply : forall m b s v, s @ m ==> v -> succ m @ (b '* s) ==> v.
Proof. intros; unfold succ; apply tagged_eval; evaluate; eassumption. Qed.
Definition spred : Combination := swap (zero '* 'I).
Lemma spred_eval : forall m v, m @ (zero '* 'I) ==> v -> spred @ m ==> v.
Proof. intros; unfold spred, swap; evaluate; eassumption. Qed.
Lemma spred_zero : spred @ zero ==> zero. Proof. apply spred_eval, zero_apply. Qed.
Lemma spred_succ : forall m, spred @ succ m ==> m. Proof. intros; apply spred_eval, succ_apply; evaluate. Qed.
Lemma infer_spred : infer PO @ spred ==> Sm (swap (Nat '* 'I)). Proof. by_runN. Qed.
Lemma type_app_spred : tp PO @ swap (Nat '* 'I) @r Nat ==> Sm Nat. Proof. by_runN. Qed.
Theorem infer_spred_application : forall m, infer PO @ m ==> Sm Nat -> infer_expression PO @ (spred @ m) ==> Sm Nat.
Proof. intros m H; eapply ie_fork; [apply ie_stem, infer_spred|apply ie_stem, H|apply type_app_spred]. Qed.

