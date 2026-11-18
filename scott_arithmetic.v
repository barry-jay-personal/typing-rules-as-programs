(** * Step 82, stage 4, part 5: recursion on numbers.

    A numeric iteration has a plain pair state [n * a] of type [Nat * C].
    [nitR @ cT @ g] is [fix_update[b]] (built through [mk_update]) with
    [b @ r = special_type[T, nstep g r, identity_update]], T = Nat * C
    given by its code [cT], and

      nstep g r @ (n * a) = n @ ((n * a) * \p. r @ (p * g @ a))

    so [nitR @ cT @ g @ (n * a) = zero * g^n a].  The default of the
    special_type is the identity: the update does not enter the data.

      add  @ (m * n) = n + m          mul @ (m * n) = m * n
      is_odd @ n                      sub @ (m * n) = n - m (truncated)
      ge @ (m * n) = (n >= m)

    Minimisation: [minimisation @ p = fix_update[b]] with
    [b @ r = special_type[Nat, advance[p,r], identity_update]] and
    [advance[p,r] @ n = (p @ n) @ (S2[K1 identity_update, K1 n] * S2[K1 r, K1 (succ n)]) @ n],
    so that [minimisation @ p @ n] searches upwards from [n]. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition NN := Nat '* Nat.

Definition nstep_t (g r : Term) : Term := star "x"
  ((Val 'fst @@ Ref "x") @@ (Ref "x" ''* star "p" (r @@ (Ref "p" ''* (g @@ (Val 'snd @@ Ref "x")))))).

Definition nitR : Combination := Eval cbn -[mk_update sp_body identity_update self_apply bz] in to_tree
  (star "cT" (star "g"
    (op mk_update @@ ''wait[Val self_apply,
       (star "r" (op mk_update @@ w3 (Ref "cT") (nstep_t (Ref "g") (Ref "r")) (Val identity_update))
         ''C tagger_t (Val update_nm)) ''C Val bz]))).

(** [pred_fn @ n = n @ (zero * I)]. *)
Definition pred_fn : Combination := Eval cbn -[zero] in to_tree (star "n" (Ref "n" @@ (Val zero ''* Val 'I))).
(** [neg_fn @ b = b @ (ff * tt)]. *)
Definition neg_fn : Combination := Eval cbn -[ff tt] in to_tree (star "b" (Ref "b" @@ (Val ff ''* Val tt))).
(** [is_zero @ n = n @ (tt * K1 ff)]. *)
Definition is_zero : Combination := Eval cbn -[ff tt] in to_tree (star "n" (Ref "n" @@ (Val tt ''* (Val 'K @@ Val ff)))).

(** The code is passed through [K1 code @ q] so that the iteration is
    built at each call (a closed application would not compile). *)
Definition run_iter (cC g : Term) (q : Term) : Term :=
  Val 'snd @@ ((op nitR @@ (Val 'K @@ pair_code_t (Val (code Nat)) cC @@ q) @@ g) @@ q).

Definition add : Combination := Eval cbn -[nitR succ_fn] in to_tree
  (star "q" (run_iter (Val (code Nat)) (Val succ_fn) ((Val 'fst @@ Ref "q") ''* (Val 'snd @@ Ref "q")))).
Definition mul : Combination := Eval cbn -[nitR add zero] in to_tree
  (star "q" (run_iter (Val (code Nat)) (star "c" (op add @@ ((Val 'snd @@ Ref "q") ''* Ref "c")))
               ((Val 'fst @@ Ref "q") ''* Val zero))).
Definition is_odd : Combination := Eval cbn -[nitR neg_fn ff] in to_tree
  (star "n" (run_iter (Val (code Bool)) (Val neg_fn) (Ref "n" ''* Val ff))).
Definition sub : Combination := Eval cbn -[nitR pred_fn] in to_tree
  (star "q" (run_iter (Val (code Nat)) (Val pred_fn) ((Val 'fst @@ Ref "q") ''* (Val 'snd @@ Ref "q")))).
Definition ge : Combination := Eval cbn -[sub is_zero] in to_tree
  (star "q" (op is_zero @@ (op sub @@ ((Val 'snd @@ Ref "q") ''* (Val 'fst @@ Ref "q"))))).

(** ** Minimisation *)
Definition advance_t (p r : Term) : Term := star "n"
  ((p @@ Ref "n") @@ (''S2[''K1 (Val identity_update), ''K1 (Ref "n")]
                       ''* ''S2[''K1 r, ''K1 (op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ Ref "n")))])
     @@ Ref "n").

Definition minimisation : Combination := Eval cbn -[mk_update sp_body identity_update self_apply bz mk_nat code] in to_tree
  (star "p"
    (op mk_update @@ ''wait[Val self_apply,
       (star "r" (op mk_update @@ w3 (Val (code Nat)) (advance_t (Ref "p") (Ref "r")) (Val identity_update))
         ''C tagger_t (Val update_nm)) ''C Val bz])).

(** ** Collatz *)
Definition two_t := succ (succ zero).

(** ** Typings and examples, by computation in [O_gen] *)

Ltac by_runA := apply (runp_sound 40); vm_done.
Definition ty_of (t : Combination) : Combination :=
  match runp 40 (infer O_gen @ t) with Some (Sm A) => A | _ => Lf end.

Definition add_ty := Eval vm_compute in ty_of add.
Definition mul_ty := Eval vm_compute in ty_of mul.
Definition is_odd_ty := Eval vm_compute in ty_of is_odd.
Definition ge_ty := Eval vm_compute in ty_of ge.
Definition min_ty := Eval vm_compute in ty_of minimisation.

(** The paper's [add : add] becomes [add : add_ty]: add holds the Update
    and Nat constructors, which are typed values, so it is not concrete. *)
Theorem add_typed_gen : infer O_gen @ add ==> Sm add_ty /\ tp O_gen @ add_ty @r NN ==> Sm Nat.
Proof. split; by_runA. Qed.
Theorem mul_typed_gen : infer O_gen @ mul ==> Sm mul_ty /\ tp O_gen @ mul_ty @r NN ==> Sm Nat.
Proof. split; by_runA. Qed.
(** Changed: the type of add does not refuse Bool * Bool.  The iteration's
    special_type does not fire there, so the update is the identity and
    the result is the second component, of type Bool (sound). *)
Theorem add_refuses_changed : tp O_gen @ add_ty @r (Bool '* Bool) ==> Sm Bool. Proof. by_runA. Qed.
Theorem is_odd_typed_gen : infer O_gen @ is_odd ==> Sm is_odd_ty /\ tp O_gen @ is_odd_ty @r Nat ==> Sm Bool.
Proof. split; by_runA. Qed.
Theorem type_app_ge_gen : tp O_gen @ ge_ty @r NN ==> Sm Bool. Proof. by_runA. Qed.

Example add_numerals : add @ (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_runA. Qed.
Example mul_numerals : mul @ (numeral 2 '* numeral 3) ==> numeral 6. Proof. by_runA. Qed.
Example is_odd_numerals : is_odd @ numeral 3 ==> tt. Proof. by_runA. Qed.
Example sub_numerals : sub @ (numeral 2 '* numeral 5) ==> numeral 3. Proof. by_runA. Qed.
Example ge_numerals : ge @ (numeral 2 '* numeral 5) ==> tt. Proof. by_runA. Qed.

(** minimisation: [minimisation : min_ty] and [min_ty # P ==> Sm Update] at the type P of is_odd. *)
Theorem minimisation_polymorphic_gen : infer O_gen @ minimisation ==> Sm min_ty /\
  tp O_gen @ min_ty @r is_odd_ty ==> Sm Update.
Proof. split; by_runA. Qed.
Theorem minimise_is_odd_gen : minimisation @ is_odd @r zero ==> succ zero /\
  infer_expression O_gen @ (minimisation @ is_odd @r zero) ==> Sm Nat.
Proof. split; by_runA. Qed.
