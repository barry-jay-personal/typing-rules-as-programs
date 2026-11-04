(** * The search operator on numbers, nat_search

    [nat_search = p |-> n |-> (minimisation @ p @ seek_at[n]) @ I] wraps its
    number as a search position [seek_at n] (built at run time by
    [seek_wrap], so the program holds no tag), runs the update
    [minimisation @ p], and unwraps the payload by [@ I].  It is tag-free,
    so it is its own type, and for [P # Nat ==> Bool]
    [nat_search # P ==> nat_search_type] with
    [nat_search_type = S2[Update 'C seek_wrap, KI]] and
    [nat_search_type # Nat ==> Nat]. *)
From TreeTyping Require Import tree typing soundness booleans functions data_types.
From TreeTyping Require Import search conditionals queries updates dither_minimisation.
From TreeTyping Require Import paper_ontology self_typing typed_mu.
From Stdlib Require Import String List Lia Bool.
Open Scope string_scope.

Definition seek_wrap := Eval cbn in to_tree (star "n"
  (Val ('tagger[seek_nm]) @@ ''S2[Val 'I, ''K1 (Ref "n")])).
Definition nat_search := Eval cbn -[minimisation seek_wrap] in to_tree (star "p" (star "n"
  (((Val minimisation @@ Ref "p") @@ (Val seek_wrap @@ Ref "n")) @@ Val 'I))).

Lemma seek_wrap_eval : forall n, seek_wrap @ n ==> seek_at n.
Proof. intros; unfold seek_wrap, seek_at, wrap; evaluate. Qed.

Lemma nat_search_eval : forall p n w v,
  minimisation @ p @r seek_at n ==> w -> w @ 'I ==> v ->
  nat_search @ p @r n ==> v.
Proof.
  intros p n w v H Hw; destruct (eval_pair_inv _ _ _ H) as [m [c [Hm [Hc Hv]]]]; inv_out Hc.
  pose proof (seek_wrap_eval n).
  unfold nat_search; d_eval.
Qed.

Section Typing.
Variable AI : Decl.
Hypothesis HK : supports_seek AI.
Hypothesis HU : supports_updates AI.
Hypothesis HT : supports_is_named AI.
Hypothesis HB : supports_booleans AI.
Hypothesis HN : supports_number AI.

Local Ltac ty_onto_more ::= first [ apply supports_seek_abstractor; exact HK ].
Local Ltac ty_elim_more ::= first [apply payload_eliminator_some | apply update_eliminator_eval].

Lemma type_app_seek_wrap : type_app AI @ seek_wrap @r 'Nat ==> Sm ('Seek).
Proof. unfold seek_wrap; repeat ty. Qed.

Definition nat_search_type := 'S2['Update 'C seek_wrap, 'KI].

Lemma type_app_nat_search_type : type_app AI @ nat_search_type @r 'Nat ==> Sm ('Nat).
Proof using All.
  pose proof type_app_seek_wrap as HS.
  assert (HW : type_app AI @ 'Seek @r 'I ==> Sm ('Nat))
    by (unfold seek_eliminator, wrap_eliminator; apply type_app_abstract;
        apply payload_eliminator_some; apply type_app_I).
  unfold nat_search_type; repeat first [apply HS | apply HW | apply type_app_Update | ty].
Qed.

Variable P : Combination.
Hypothesis HP : type_app AI @ P @r ('Nat) ==> Sm ('Bool).

Lemma type_app_nat_search : type_app AI @ nat_search @r P ==> Sm nat_search_type.
Proof using All.
  pose proof (proj2 (minimisation_polymorphic AI _ HK HU HT HB HN HP)) as HM.
  unfold nat_search; repeat first [apply HM | ty].
Qed.
End Typing.

Lemma nat_search_tag_free : tag_free nat_search = true.
Proof. vm_compute; reflexivity. Qed.

(** [nat_search] is its own type; [nat_search # P # Nat ==> Nat]. *)
Theorem nat_search_polymorphic : forall (AI : Decl) P,
  supports_seek AI -> supports_updates AI -> supports_is_named AI ->
  supports_booleans AI -> supports_number AI ->
  type_app AI @ P @r ('Nat) ==> Sm ('Bool) ->
  infer AI @ nat_search ==> Sm nat_search /\
  type_app AI @ nat_search @r P ==> Sm nat_search_type /\
  type_app AI @ nat_search_type @r ('Nat) ==> Sm ('Nat).
Proof.
  intros; split; [apply infer_tag_free; exact nat_search_tag_free|split].
  - apply type_app_nat_search; assumption.
  - apply type_app_nat_search_type; assumption.
Qed.

(** ** Evaluation *)
Lemma nat_search_found : forall p k, p @ k ==> 'tt -> nat_search @ p @r k ==> k.
Proof.
  intros p k H; eapply nat_search_eval; [apply minimisation_found; exact H|apply seek_at_unwrap].
Qed.

Lemma nat_search_found_numeral : forall p k, p @ numeral k ==> 'tt ->
  nat_search @ p @r numeral k ==> numeral k.
Proof. intros; apply nat_search_found; assumption. Qed.

Lemma nat_search_at_eval : forall p,
  nat_search @ p ==> 'S2[minimisation_at p 'C seek_wrap, 'KI].
Proof. intros; unfold nat_search; pose proof (minimisation_eval p); d_eval. Qed.

Lemma nat_search_inv : forall p n v, nat_search @ p @r n ==> v ->
  exists w, minimisation @ p @r seek_at n ==> w /\ w @ 'I ==> v.
Proof.
  intros p n v H; destruct (eval_pair_inv _ _ _ H) as [a [c [Ha [Hc Hv]]]]; clear H; inv_out Hc.
  pose proof (eval_deterministic _ _ Ha _ (nat_search_at_eval p)) as ->; clear Ha.
  inv_out Hv.
  destruct (eval_pair_inv _ _ _ H3) as [g [i [Hg [Hi Hgi]]]]; clear H3.
  assert (HKI : 'KI @ c ==> 'I) by evaluate.
  pose proof (eval_deterministic _ _ Hi _ HKI) as ->; clear Hi HKI.
  inv_out Hg.
  destruct (eval_pair_inv _ _ _ H3) as [m [s [Hm [Hs Hms]]]]; clear H3.
  assert (HK1 : ('K1 (minimisation_at p)) @ c ==> minimisation_at p) by evaluate.
  pose proof (eval_deterministic _ _ Hm _ HK1) as ->; clear Hm HK1.
  pose proof (eval_deterministic _ _ Hs _ (seek_wrap_eval c)) as ->; clear Hs.
  exists g; split; [|exact Hgi].
  eapply eval_appl; [apply minimisation_eval|exact Hms].
Qed.

(** If [p @ k ==> ff], the search at [k] gives whatever the search at
    [succ k] gives. *)
Lemma nat_search_next : forall p k v, p @ k ==> 'ff ->
  nat_search @ p @r succ k ==> v -> nat_search @ p @r k ==> v.
Proof.
  intros p k v H Hn; destruct (nat_search_inv _ _ _ Hn) as [w [Hw Hv]].
  eapply nat_search_eval; [eapply minimisation_next; [exact H|exact Hw]|exact Hv].
Qed.

Lemma nat_search_next_numeral : forall p k v, p @ numeral k ==> 'ff ->
  nat_search @ p @r numeral (S k) ==> v -> nat_search @ p @r numeral k ==> v.
Proof. intros p k v; cbn [numeral]; apply nat_search_next. Qed.

(** ** The first odd number *)
Lemma nat_search_is_odd_eval : nat_search @ is_odd @r zero ==> one.
Proof. eapply nat_search_eval; [exact minimise_is_odd_eval|apply seek_at_unwrap]. Qed.

Theorem nat_search_is_odd : forall (AI : Decl),
  supports_seek AI -> supports_updates AI -> supports_is_named AI ->
  supports_booleans AI -> supports_number AI ->
  nat_search @ is_odd @r zero ==> one /\
  infer_expression AI @ (nat_search @ is_odd @r zero) ==> Sm ('Nat).
Proof.
  intros AI HK HU HT HB HN; split; [exact nat_search_is_odd_eval|].
  pose proof (nat_search_polymorphic AI Odd HK HU HT HB HN (type_app_Odd AI)) as [Hs [HP HNat]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork;
      [apply infer_expression_stem; exact Hs
      |apply infer_expression_stem; apply infer_is_odd; exact HB
      |exact HP].
  - apply infer_expression_stem; apply infer_zero; exact HN.
  - exact HNat.
Qed.

(** ** Sizes *)
Eval vm_compute in (tree_size nat_search, tree_size minimisation,
  tree_size seek_wrap, tree_size nat_search_type).

