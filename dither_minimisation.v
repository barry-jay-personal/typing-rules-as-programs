(** * Recursion with no function types: minimisation as an update,
    dither as a query

    [minimisation @ p] is a recursive update.  At a value [seek_at n] it
    tests [p] at [n]: if [p @ n] holds it gives [seek_at n] unchanged, and
    otherwise it continues at [seek_at (succ n)].  At every other value it is
    the identity.  Both arms of the conditional are updates, and the
    recursive call has the invariant [Update], so typing stops there.
    [minimisation] is tag-free, so it is its own type, and for any [P] with
    [P # Nat ==> Bool], [minimisation # P ==> Update]
    ([minimisation_polymorphic]).

    The function-typed minimisation of recursion.v is [minimisation_fn].
    Dither, at the end, is a query of type [Query[Bool]]. *)
From TreeTyping Require Import tree typing soundness booleans functions data_types.
From TreeTyping Require Import search conditionals queries updates.
From Stdlib Require Import String Arith Lia.
Open Scope string_scope.
Set Default Proof Using "Type".

(** ** The program

    The body [r ↦ specialised_update[seek_nm, step[p,r], identity_update]],
    where, with [n = x @ I],
    [step[p,r] @ x = (p @ n) @ (identity_update * r) @ ((p @ n) @ (x * seek_at (succ n)))].
    The identity update and the IsNamed test [is_named] are built at run time by [mk],
    so that the program holds no tag. *)
Definition minimisation_step_t (p r : Term) := star "x"
  (((p @@ (Ref "x" @@ Val 'I)) @@ ((Val (mk 'I update_nm) @@ Ref "x") ''* r))
     @@ ((p @@ (Ref "x" @@ Val 'I))
           @@ (Ref "x" ''* (Val seek_successor @@ (Ref "x" @@ Val 'I))))).
Definition minimisation_body := Eval cbn in to_tree (star "p" (star "r"
  (''tagged[''S2[''S2[''S2[Val (mk (name_test seek_nm) is_named_nm) @@ Ref "r",
                         ''K1 (minimisation_step_t (Ref "p") (Ref "r"))],
                   ''K1 (Val (mk 'I update_nm) @@ Ref "r")], Val 'I], Val update_nm]))).
(** [minimisation @ p] builds [fix_update ('wait[minimisation_body, p])]. *)
Definition minimisation := Eval cbn -[minimisation_body] in to_tree (star "p"
  (''tagged[''wait[Val dup_z,
     (''wait[Val minimisation_body, Ref "p"] ''C Val tagged_update) ''C Val bz], Val update_nm])).
Definition minimisation_at p := fix_update ('wait[minimisation_body, p]).
Definition minimisation_step p r := to_tree (minimisation_step_t (Val p) (Val r)).

Lemma minimisation_tag_free : tag_free minimisation = true.
Proof. vm_compute; reflexivity. Qed.

(** ** Evaluation *)
Lemma minimisation_eval : forall p, minimisation @ p ==> minimisation_at p.
Proof. intros; unfold minimisation, minimisation_at, fix_update, Z; evaluate. Qed.

Lemma minimisation_body_eval : forall p r,
  'wait[minimisation_body, p] @ r ==>
    specialised_update seek_nm (minimisation_step p r) identity_update.
Proof.
  intros; unfold minimisation_body, minimisation_step, specialised_update, if_named,
    identity_update, is_named; cbn.
  pose proof (mk_eval 'I update_nm r); pose proof (mk_eval (name_test seek_nm) is_named_nm r).
  d_eval.
Qed.

Lemma minimisation_unfold : forall p u v,
  specialised_update seek_nm (minimisation_step p (minimisation_at p)) identity_update @ u ==> v ->
  minimisation_at p @ u ==> v.
Proof.
  intros p u v H; unfold minimisation_at at 1, fix_update; apply tagged_eval; apply Z_unfold.
  eapply eval_appl; [|exact H].
  eapply eval_c; eapply eval_appr; [apply tagged_update_eval|apply minimisation_body_eval].
Qed.

Lemma minimisation_step_found : forall p r k, p @ k ==> 'tt ->
  minimisation_step p r @ seek_at k ==> seek_at k.
Proof.
  intros p r k H; pose proof (mk_eval 'I update_nm (seek_at k)) as HM.
  pose proof (identity_update_eval (seek_at k)) as HI; unfold identity_update in HI.
  pose proof (seek_successor_eval k) as HS.
  unfold minimisation_step, seek_at, wrap in *; cbn; d_eval.
Qed.

Lemma minimisation_step_next : forall p r k v, p @ k ==> 'ff ->
  r @ seek_at (succ k) ==> v -> minimisation_step p r @ seek_at k ==> v.
Proof.
  intros p r k v H Hr; pose proof (seek_successor_eval k) as HS.
  pose proof (mk_eval 'I update_nm (seek_at k)) as HM.
  unfold minimisation_step, seek_at, wrap in *; cbn; d_eval.
Qed.

(** If [p @ k ==> tt] then the search stops at [seek_at k]; if
    [p @ k ==> ff] then it continues at [seek_at (succ k)]. *)
Lemma minimisation_found : forall p k, p @ k ==> 'tt ->
  minimisation @ p @r seek_at k ==> seek_at k.
Proof.
  intros p k H; eapply eval_appl; [apply minimisation_eval|].
  apply minimisation_unfold; unfold specialised_update; apply tagged_eval.
  eapply if_named_hit; [apply get_tagname_some|apply minimisation_step_found; exact H].
Qed.

Lemma minimisation_next : forall p k v, p @ k ==> 'ff ->
  minimisation @ p @r seek_at (succ k) ==> v -> minimisation @ p @r seek_at k ==> v.
Proof.
  intros p k v H Hn; destruct (eval_pair_inv _ _ _ Hn) as [w [c [Hw [Hc Hv]]]].
  pose proof (eval_deterministic _ _ Hw _ (minimisation_eval p)) as ->.
  eapply eval_appl; [apply minimisation_eval|].
  apply minimisation_unfold; unfold specialised_update; apply tagged_eval.
  eapply if_named_hit; [apply get_tagname_some|].
  eapply minimisation_step_next; [exact H|]; inv_out Hc; exact Hv.
Qed.

(** At a value that is not a search position, [minimisation @ p] is the identity. *)
Lemma minimisation_other : forall p u, (forall n, u <> 'tagged[n,seek_nm]) ->
  minimisation @ p @r u ==> u.
Proof.
  intros p u Hu; eapply eval_appl; [apply minimisation_eval|].
  apply minimisation_unfold; unfold specialised_update; apply tagged_eval.
  apply if_named_default; [exact Hu|apply identity_update_eval].
Qed.

(** ** Typing *)
Section Typing.
Variable AI : Decl.
Hypothesis HK : supports_seek AI.
Hypothesis HU : supports_updates AI.
Hypothesis HT : supports_is_named AI.
Hypothesis HB : supports_booleans AI.
Hypothesis HN : supports_number AI.
Variable P : Combination.
Hypothesis HP : type_app AI @ P @r ('Nat) ==> Sm ('Bool).

Local Ltac ty_onto_more ::= first
  [ eapply declaration_apply; [exact HT|apply is_named_abstractor_some; apply seek_nm_concrete]
  | apply supports_seek_abstractor; exact HK
  | eapply update_abstractor_supported; [exact HU|apply constructor_identity]
  | eapply update_abstractor_supported;
      [exact HU|eapply constructor_choice; [apply seek_nm_concrete|apply seek_declared; exact HK|]] ].
Local Ltac ty_elim_more ::= first [apply payload_eliminator_some | apply update_eliminator_eval].

(** The body at [P], applied to the invariant [Update], is an update. *)
Lemma type_app_minimisation_body :
  type_app AI @ ('wait[minimisation_body, P]) @r ('Update) ==> Sm ('Update).
Proof using All.
  pose proof (type_app_seek_successor AI HK HN) as HS.
  assert (HM1 : forall U, type_app AI @ mk (name_test seek_nm) is_named_nm @r U ==> Sm (IsNamed seek_nm))
    by (intros; apply type_app_mk; eapply declaration_apply;
        [exact HT|apply is_named_abstractor_some; apply seek_nm_concrete]).
  assert (HM2 : forall U, type_app AI @ mk 'I update_nm @r U ==> Sm ('Update))
    by (intros; apply type_app_mk; eapply update_abstractor_supported; [exact HU|apply constructor_identity]).
  assert (HW : type_app AI @ wrap_type ('Nat) seek_nm @r 'I ==> Sm ('Nat))
    by (unfold wrap_type, wrap_eliminator; apply type_app_abstract;
        apply payload_eliminator_some; apply type_app_I).
  eapply type_app_wait.
  - unfold minimisation_body; repeat first [apply HM1 | apply HM2 | ty].
  - repeat first [apply HM1 | apply HM2 | ty].
Qed.

Local Ltac ty_onto_more ::= first
  [ eapply update_abstractor_supported;
      [exact HU|apply constructor_recursive; apply type_app_minimisation_body] ].
Lemma type_app_minimisation : type_app AI @ minimisation @r P ==> Sm ('Update).
Proof using All. unfold minimisation; repeat ty. Qed.
End Typing.

(** Minimisation is its own type, and at any predicate type [P] with
    [P # Nat ==> Bool] it gives an update. *)
Theorem minimisation_polymorphic : forall (AI : Decl) P,
  supports_seek AI -> supports_updates AI -> supports_is_named AI ->
  supports_booleans AI -> supports_number AI ->
  type_app AI @ P @r ('Nat) ==> Sm ('Bool) ->
  infer AI @ minimisation ==> Sm minimisation /\
  type_app AI @ minimisation @r P ==> Sm ('Update).
Proof.
  intros; split; [apply infer_tag_free; exact minimisation_tag_free|].
  apply type_app_minimisation; assumption.
Qed.

(** ** The first odd number *)
Lemma minimise_is_odd_eval : minimisation @ is_odd @r seek_at zero ==> seek_at one.
Proof. eapply minimisation_next; [apply is_odd_zero|apply minimisation_found; apply is_odd_one]. Qed.

Theorem minimise_is_odd : forall (AI : Decl),
  supports_seek AI -> supports_updates AI -> supports_is_named AI ->
  supports_booleans AI -> supports_number AI ->
  minimisation @ is_odd @r seek_at zero ==> seek_at one /\
  infer_expression AI @ (minimisation @ is_odd @r seek_at zero) ==> Sm ('Seek).
Proof.
  intros AI HK HU HT HB HN; split; [exact minimise_is_odd_eval|].
  eapply infer_expression_fork.
  - eapply infer_expression_fork;
      [apply infer_expression_stem; apply infer_tag_free; exact minimisation_tag_free
      |apply infer_expression_stem; apply infer_is_odd; exact HB
      |apply minimisation_polymorphic; try assumption; apply type_app_Odd].
  - apply infer_expression_stem; apply infer_seek_at; [exact HK|apply infer_zero; exact HN].
  - apply type_app_Update.
Qed.

(** * Dither as a query

    [dither = fix_query[decorate[d, Kq tt]]] with [d = r ↦ S_q[Kq neg, r]].
    At any argument it negates its own result, so it has no value; its type
    is the invariant [Query[Bool]], so [dither @ x :: Bool] for every typed
    [x].  The function-typed dither of functions.v is [dither_fn]. *)
Definition dither_body := Eval cbn in to_tree (star "r" (''S_q[''Kq (Val neg), Ref "r"])).
Definition dither := fix_query ('decorate[dither_body, 'Kq 'tt]).

Lemma dither_body_eval : forall r, dither_body @ r ==> 'S_q['Kq neg, r].
Proof. intros; unfold dither_body; cbn; evaluate. Qed.

Lemma dither_unfold_eval :
  ('decorate[dither_body, 'Kq 'tt] 'C tagged_query) @
    Z ('decorate[dither_body, 'Kq 'tt] 'C tagged_query) ==> 'S_q['Kq neg, dither].
Proof.
  apply eval_c; eapply eval_appr; [unfold tagged_query; evaluate|].
  apply wait_eval; eapply eval_appl; [evaluate|apply dither_body_eval].
Qed.

Lemma S2_evaln_right_inv : forall n g f x v,
  evaln n ('S2[g,f] @ x) v -> exists m w, m < n /\ evaln m (f @ x) w.
Proof.
  intros n g f x v H; invert_evaln.
  match goal with
  | H : evaln ?m (f @ x) ?w |- _ => exists m, w; split; [lia|exact H]
  end.
Qed.

Lemma dither_tt_evaln_smaller : forall n v,
  evaln n (dither @ 'tt) v -> exists m w, m < n /\ evaln m (dither @ 'tt) w.
Proof.
  intros n v H.
  unfold dither at 1, fix_query in H.
  destruct (tagged_evaln_inv _ _ _ _ _ H) as [m1 [Hm1 H1]]; clear H.
  destruct (Z_evaln_unfold_inv _ _ _ _ H1) as [m2 [w [Hm2 [Hw H2]]]]; clear H1.
  pose proof (eval_deterministic _ _ Hw _ dither_unfold_eval) as Heq; subst w; clear Hw.
  destruct (tagged_evaln_inv _ _ _ _ _ H2) as [m3 [Hm3 H3]]; clear H2.
  destruct (S2_evaln_right_inv _ _ _ _ _ H3) as [m4 [w [Hm4 H4]]].
  exists m4, w; split; [lia|exact H4].
Qed.

Lemma dither_tt_no_value : forall v, ~ (dither @ 'tt ==> v).
Proof.
  intros v H.
  destruct (eval_evaln _ _ H) as [n Hn]; clear H.
  revert v Hn.
  induction n as [n IH] using lt_wf_ind; intros v Hn.
  destruct (dither_tt_evaln_smaller _ _ Hn) as [m [w [Hm Hw]]].
  exact (IH m Hm w Hw).
Qed.

Lemma infer_dither : forall (AI : Decl),
  supports_queries AI -> supports_booleans AI ->
  infer AI @ dither ==> Sm ('Query['Bool]).
Proof.
  intros AI HQ HB.
  pose proof (neg_infer AI HB) as Hn.
  assert (HKn : infer AI @ ('Kq neg) ==> Sm ('Query[Neg])) by (apply infer_Kq; assumption).
  assert (HKt : infer AI @ ('Kq 'tt) ==> Sm ('Query['Bool])) by (apply infer_Kq; [exact HQ|apply tt_infer; exact HB]).
  unfold dither; eapply infer_fix_query; [exact HQ| |exact HKt|].
  - unfold dither_body; cbn; infer_tac.
  - cbn; repeat first [ eassumption | apply type_app_I | apply type_app_K_ev | apply type_app_leaf_ev
      | new_S; [solve [intros; discriminate]| | |]
      | apply type_app_stem_ev; first
        [ apply type_app_stem_structural; solve [intros; discriminate]
        | apply type_app_stem_tagged; eapply query_abstractor_supported;
            [exact HQ|apply query_abstractor_S; apply neg_type_app] ] ].
Qed.

(** [dither @ tt :: Bool], and indeed [dither @ x :: Bool] at every typed [x]. *)
Lemma dither_typed_at : forall (AI : Decl) x X,
  supports_queries AI -> supports_booleans AI -> infer AI @ x ==> Sm X ->
  infer_expression AI @ (dither @ x) ==> Sm ('Bool).
Proof.
  intros AI x X HQ HB Hx; eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_dither; assumption.
  - apply infer_expression_stem; exact Hx.
  - apply type_app_Query.
Qed.
Lemma dither_tt_infer_expression : forall (AI : Decl),
  supports_queries AI -> supports_booleans AI ->
  infer_expression AI @ (dither @ 'tt) ==> Sm ('Bool).
Proof. intros AI HQ HB; eapply dither_typed_at; [exact HQ|exact HB|apply tt_infer; exact HB]. Qed.

Theorem dither_typed_no_value : forall (AI : Decl),
  supports_queries AI -> supports_booleans AI ->
  infer_expression AI @ (dither @ 'tt) ==> Sm ('Bool) /\
  forall v, ~ (dither @ 'tt ==> v).
Proof.
  intros AI HQ HB; split; [exact (dither_tt_infer_expression AI HQ HB)|exact dither_tt_no_value].
Qed.
