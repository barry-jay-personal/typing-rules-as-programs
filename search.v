(** * The family [Search]: possibly unbounded searches over numbers, with
    no function types.  [Nat] stays bounded.
    [done[n]] is a finished search.  [seek[p,n]] tests [p] at [n] and
    otherwise becomes [seek[p, succ n]].  The recursive call is a tagged
    value, so the name [Search] is the invariant at which typing stops. *)
From TreeTyping Require Import tree typing soundness booleans data_types.
From Stdlib Require Import String.
Set Default Proof Using "Type".
Local Open Scope string_scope.
Local Opaque equal.

Definition search_nm := Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf))))))))))))))))))).
Definition search_eliminator := payload_eliminator ('Nat).
Notation "'Search" := ('tagged[search_eliminator, search_nm]) (at level 0).
Definition done n := 'tagged[swap n, search_nm].

Definition done_step := Eval cbn in to_tree
  (star "n" (Val ('tagger[search_nm]) @@ (star "f" (Ref "f" @@ Ref "n")))).
Definition seek_body := Eval cbn -[succ_step done_step] in to_tree
  (star "self" (star "q" (star "f"
    (((Val 'fst @@ Ref "q") @@ (Val 'snd @@ Ref "q"))
       @@ ((Val done_step @@ (Val 'snd @@ Ref "q")) ''*
           (Val ('tagger[search_nm]) @@
              ''wait[Ref "self", (Val 'fst @@ Ref "q") ''* (Val succ_step @@ (Val 'snd @@ Ref "q"))]))
       @@ Ref "f")))).
Definition seek_run := Z seek_body.
Definition seek p n := 'tagged['wait[seek_run, p '* n], search_nm].

(** The abstractor checks the predicate by the type application it receives. *)
Definition bool_mk := 'S2['K1 ('tagger[bool_nm]), 'K1 bool_eliminator].
Definition seek_check := Eval cbn -[equal] in to_tree
  (star "a" (star "P" (star "z"
    (''onStem1 (star "V"
        (Val equal @@ Ref "V" @@ (Val bool_mk @@ Ref "z")
          @@ (Val Lf @@ ''wait[Val payload_elim, Val nat_type_mk @@ Ref "z"]) @@ Val Lf))
      @@ (Ref "a" @@ Ref "P" @@ (Val nat_type_mk @@ Ref "z")))))).
Definition search_row := Eval cbn -[equal seek_check seek_run acc_cell] in to_tree
  (star "a" (star "C"
    ((star "q" (star "n" (star "P"
       (Ref "q" @@ (star "f" (Ref "f" @@ Ref "n"))
         @@ (Val Lf @@ ''wait[Val payload_elim, Ref "n"])
         @@ ((Ref "q" @@ ''wait[Val seek_run, Ref "P" ''* Ref "n"]
              @@ ''wait2[Val seek_check, Ref "a", Ref "P"]
              @@ (''K1 (Val Lf)))
             @@ Val Lf)))))
     @@ (Val equal @@ Ref "C") @@ (Val nat_type_mk @@ Ref "C") @@ (Val acc_cell @@ Ref "C")))).

Definition search_case_package :
  { t : Combination | to_tree (tcase (Val search_nm) (Val search_row)) = t }.
Proof. eexists; reflexivity. Defined.
Definition search_case := Eval cbn in proj1_sig search_case_package.

Lemma search_case_compilation :
  to_tree (tcase (Val search_nm) (Val search_row)) = search_case.
Proof. unfold search_case; exact (proj2_sig search_case_package). Qed.
Lemma search_case_some : search_case @ search_nm ==> Sm search_row.
Proof. rewrite <- search_case_compilation; apply tcase_eq. Qed.
Lemma search_case_none : forall N, N <> search_nm -> search_case @ N ==> Lf.
Proof.
  intros N H; rewrite <- search_case_compilation.
  apply tcase_neq; intro HE; apply H; symmetry; exact HE.
Qed.
Definition supports_search AI := AI @ search_nm ==> search_row.


(** ** Evaluation of the abstractor *)
Lemma bool_mk_eval : forall z, bool_mk @ z ==> 'Bool.
Proof. intros; unfold bool_mk; evaluate. Qed.

Lemma seek_check_eval : forall a P z,
  a @ P @r ('Nat) ==> Sm ('Bool) ->
  seek_check @ a @r P @r z ==> Sm search_eliminator.
Proof.
  intros a P z H.
  pose proof (bool_mk_eval z) as HM; pose proof (nat_type_mk_eval z) as HT.
  pose proof (equal_eq ('Bool)) as HE.
  inv_out H; inv_out HE.
  unfold seek_check, search_eliminator, payload_eliminator; cbn -[equal bool_eliminator]; d_eval.
Qed.

Lemma seek_check_inv : forall a P z E,
  seek_check @ a @r P @r z ==> Sm E ->
  E = search_eliminator /\ a @ P @r ('Nat) ==> Sm ('Bool).
Proof.
  intros a P z E H.
  unfold seek_check in H; cbn -[equal bool_eliminator] in H.
  inv_out H; invert_eval.
  all: repeat match goal with
  | H1 : bool_mk @ ?y ==> ?x |- _ =>
      pose proof (eval_deterministic _ _ H1 _ (bool_mk_eval y)); subst x; clear H1
  | H1 : nat_type_mk @ ?y ==> ?x |- _ =>
      pose proof (eval_deterministic _ _ H1 _ (nat_type_mk_eval y)); subst x; clear H1
  end.
  all: match goal with
  | H1 : equal @ ?V ==> ?e, H2 : ?e @ ?W ==> ?b |- _ =>
    assert (Hequal : equal @ V @r W ==> b) by (eapply eval_appl; eauto);
    destruct (equal_spec _ _ _ Hequal) as [[Hv0 Heq] | [Hv0 Hneq]]; subst b; invert_eval
  end.
  all: subst; split; [unfold search_eliminator, payload_eliminator; try reflexivity|eapply eval_appl; eassumption].
Qed.


Lemma search_row_eval : forall a C r,
  let x := path_fn path_cell C in
  (if ceqb C (swap ('Nat)) then r = Sm search_eliminator
   else if ceqb C ('wait[seek_run, x '* 'Nat])
        then seek_check @ a @r x @r Lf ==> r else r = Lf) ->
  search_row @ a @r C ==> r.
Proof.
  intros a C r x Hr.
  pose proof (path_eval path_cell C) as HB; fold acc_cell in HB; fold x in HB.
  pose proof (equal_eval C) as He.
  pose proof (nat_type_mk_eval C) as HT.
  clearbody x.
  destruct (equal1_bt_case C (swap ('Nat))) as [[_ [E1 H1]]|[_ [E1 H1]]];
  destruct (equal1_bt_case C ('wait[seek_run, x '* 'Nat])) as [[_ [E2 H2]]|[_ [E2 H2]]];
  rewrite ?E1, ?E2 in Hr.
  - exfalso; apply ceqb_true in E1; apply ceqb_true in E2; rewrite E1 in E2; discriminate.
  - subst r; unfold search_row, swap, search_eliminator, payload_eliminator in *;
      cbn -[equal seek_check seek_run acc_cell nat_type_mk]; d_eval.
  - destruct (eval_app_r_inv _ _ _ Hr) as [w2 [H5 H6]].
    destruct (eval_app_r_inv _ _ _ H5) as [w1 [H7 H8]].
    unfold search_row, swap, search_eliminator, payload_eliminator in *;
      cbn -[equal seek_check seek_run acc_cell nat_type_mk]; d_eval.
  - subst r; unfold search_row, swap, search_eliminator, payload_eliminator in *;
      cbn -[equal seek_check seek_run acc_cell nat_type_mk]; d_eval.
Qed.

Lemma search_row_seek_inv : forall a C r,
  let x := path_fn path_cell C in
  ceqb C (swap ('Nat)) = false ->
  C = 'wait[seek_run, x '* 'Nat] ->
  search_row @ a @r C ==> r -> seek_check @ a @r x @r Lf ==> r.
Proof.
  intros a C r x H1 H2 H.
  pose proof (path_eval path_cell C) as HB; fold acc_cell in HB; fold x in HB.
  pose proof (nat_type_mk_eval C) as HT.
  pose proof (equal_eval C) as He.
  destruct (equal1_bt_case C (swap ('Nat))) as [[_ [E1 H3]]|[_ [E1 H3]]]; [congruence|].
  clearbody x; subst C.
  pose proof (equal1_eq ('wait[seek_run, x '* 'Nat])) as H4.
  unfold search_row in H; cbn -[equal equal1 seek_check seek_run acc_cell nat_type_mk] in H.
  inv_out H; invert_eval.
  pose proof (eval_deterministic _ _ H6 _ HB); subst v2.
  pose proof (eval_deterministic _ _ H8 _ HT); subst v4.
  pose proof (eval_deterministic _ _ H10 _ He); subst v9.
  pose proof (eval_deterministic _ _ H14 _ H3); subst v1.
  pose proof (eval_deterministic _ _ H18 _ H4); subst v8.
  assert (Hk : 'K @ ('wait2[seek_check, a, x]) ==> 'K1 ('wait2[seek_check, a, x])) by evaluate.
  pose proof (eval_deterministic _ _ H17 _ Hk); subst v6.
  assert (Hk1 : ('K1 ('wait2[seek_check, a, x])) @ ('K1 Lf) ==> 'wait2[seek_check, a, x]) by evaluate.
  pose proof (eval_deterministic _ _ H16 _ Hk1); subst v5.
  assert (Hki : 'KI @ Sm ('wait[payload_elim, 'Nat]) ==> 'I) by evaluate.
  pose proof (eval_deterministic _ _ H13 _ Hki); subst v3.
  assert (Hi : 'I @ v7 ==> v7) by evaluate.
  pose proof (eval_deterministic _ _ H12 _ Hi); subst r.
  apply wait2_eval_inv in H15; exact H15.
Qed.

(** ** Soundness by typing *)
Lemma type_app_Search : forall AI F U,
  type_app AI @ F @r ('Nat) ==> Sm U -> type_app AI @ ('Search) @r F ==> Sm U.
Proof.
  intros AI F U H; apply type_app_abstract; apply payload_eliminator_some; exact H.
Qed.

Section Sound.
Variable AI : Combination.
Hypothesis HS : supports_search AI.
Hypothesis HN : supports_number AI.

Lemma row_value : exists D, search_row @ type_app AI ==> D.
Proof using. eexists; unfold search_row; cbn -[equal seek_check seek_run acc_cell nat_type_mk]; evaluate. Qed.

Lemma declared_swap :
  AI @ search_nm @r type_app AI @r swap ('Nat) ==> Sm search_eliminator.
Proof using HS.
  destruct row_value as [D HD].
  assert (H : search_row @ type_app AI @r swap ('Nat) ==> Sm search_eliminator).
  { apply search_row_eval; cbv zeta; rewrite ceqb_refl; reflexivity. }
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]].
  eapply eval_appl; [eapply eval_appl; [exact HS|exact Hw]|exact Hv].
Qed.

Lemma declared_seek : forall P, type_app AI @ P @r ('Nat) ==> Sm ('Bool) ->
  AI @ search_nm @r type_app AI @r 'wait[seek_run, P '* 'Nat] ==> Sm search_eliminator.
Proof using HS.
  intros P HP; destruct row_value as [D HD].
  assert (H : search_row @ type_app AI @r 'wait[seek_run, P '* 'Nat] ==> Sm search_eliminator).
  { apply search_row_eval; cbv zeta.
    assert (Hx : path_fn path_cell ('wait[seek_run, P '* 'Nat]) = P) by reflexivity.
    rewrite Hx, ceqb_refl.
    destruct (ceqb _ _) eqn:Hc; [exfalso; apply ceqb_true in Hc; discriminate|].
    apply seek_check_eval; exact HP. }
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]].
  eapply eval_appl; [eapply eval_appl; [exact HS|exact Hw]|exact Hv].
Qed.

Local Ltac ty_onto_more ::= first [apply declared_swap|eapply declared_seek; eassumption|eassumption].
Local Ltac ty_elim_more ::= apply payload_eliminator_some.

Lemma type_app_done_step : type_app AI @ done_step @r ('Nat) ==> Sm ('Search).
Proof using HS. unfold done_step; repeat ty. Qed.

(** The carrier type stops at the name: typing never runs the search. *)
Lemma seek_carrier_typed : forall P F V,
  type_app AI @ P @r ('Nat) ==> Sm ('Bool) ->
  type_app AI @ F @r ('Nat) ==> Sm V ->
  type_app AI @ 'wait[seek_run, P '* 'Nat] @r F ==> Sm V.
Proof using HS HN.
  intros P F V HP HF.
  pose proof (type_app_succ_step AI HN) as HC.
  pose proof type_app_done_step as HD.
  eapply type_app_wait; [|apply type_app_abstract; apply payload_eliminator_some; exact HF].
  unfold seek_run; eapply type_app_Z.
  - unfold seek_body; cbn -[succ_step done_step bool_eliminator]; repeat ty.
  - cbn -[succ_step done_step bool_eliminator]; repeat ty.
Qed.

Lemma search_abstractor_sound : forall D,
  search_row @ type_app AI ==> D -> abstractor_sound_by_typing AI D.
Proof using HS HN.
  intros D HD C E U V HC HE.
  assert (HR : search_row @ type_app AI @r C ==> Sm E) by (eapply eval_appl; eassumption).
  destruct (ceqb C (swap ('Nat))) eqn:H1.
  - apply ceqb_true in H1; subst C.
    assert (H2 : search_row @ type_app AI @r swap ('Nat) ==> Sm search_eliminator)
      by (apply search_row_eval; cbv zeta; rewrite ceqb_refl; reflexivity).
    pose proof (eval_deterministic _ _ HR _ H2) as Hs; inversion Hs; subst E.
    apply payload_eliminator_inv in HE.
    apply type_app_swap2; exact HE.
  - set (x := path_fn path_cell C) in *.
    destruct (ceqb C ('wait[seek_run, x '* 'Nat])) eqn:H2.
    + apply ceqb_true in H2.
      assert (Hk : seek_check @ type_app AI @r x @r Lf ==> Sm E)
        by (eapply search_row_seek_inv; [exact H1|exact H2|exact HR]).
      apply seek_check_inv in Hk; destruct Hk as [-> HP].
      apply payload_eliminator_inv in HE.
      rewrite H2; apply seek_carrier_typed; assumption.
    + exfalso.
      assert (H3 : search_row @ type_app AI @r C ==> Lf)
        by (apply search_row_eval; cbv zeta; fold x; rewrite H1, H2; reflexivity).
      pose proof (eval_deterministic _ _ HR _ H3) as Hs; discriminate.
Qed.

Lemma infer_done : forall n,
  infer AI @ n ==> Sm ('Nat) -> infer AI @ done n ==> Sm ('Search).
Proof using HS.
  intros n Hn; unfold done; eapply infer_tagged.
  - apply infer_swap; exact Hn.
  - apply infer_tag_free; vm_compute; reflexivity.
  - apply declared_swap.
Qed.

Lemma infer_seek : forall p P n,
  infer AI @ p ==> Sm P -> infer AI @ n ==> Sm ('Nat) ->
  type_app AI @ P @r ('Nat) ==> Sm ('Bool) ->
  infer AI @ seek p n ==> Sm ('Search).
Proof using HS.
  intros p P n Hp Hn HP; unfold seek; eapply infer_tagged.
  - apply infer_wait;
      [apply infer_tag_free; vm_compute; reflexivity
      |apply infer_product_value; eassumption].
  - apply infer_tag_free; vm_compute; reflexivity.
  - apply declared_seek; exact HP.
Qed.
End Sound.

(** ** Evaluation *)
Lemma done_step_eval : forall n, done_step @ n ==> done n.
Proof. intros; unfold done_step, done, swap; cbn; evaluate. Qed.

Lemma done_eval : forall n f v, f @ n ==> v -> done n @ f ==> v.
Proof.
  intros n f v H; unfold done, swap; apply tagged_eval; inv_out H; evaluate.
Qed.

Lemma done_eval_inv : forall n f v, done n @ f ==> v -> f @ n ==> v.
Proof.
  intros n f v H; unfold done, swap in H; invert_eval; eapply eval_appl; eassumption.
Qed.

(** One unfolding of the search.  The boolean [b] chooses between the two
    tagged values, and the consumer is applied to the choice. *)
Lemma seek_unfold : forall p n f b r,
  p @ n ==> b ->
  b @ (done n '* seek p (succ n)) @r f ==> r ->
  seek p n @ f ==> r.
Proof.
  intros p n f b r Hb Hr.
  pose proof (done_step_eval n) as HD.
  pose proof (succ_step_eval n) as HS.
  unfold seek; apply tagged_eval; apply wait_eval.
  destruct (eval_app_r_inv _ _ _ Hr) as [c [Hc Hcf]].
  eapply eval_appl; [apply Z_unfold|exact Hcf].
  destruct (eval_app_r_inv _ _ _ Hc) as [w [Hw Hwc]].
  unfold seek_body; cbn -[succ_step done_step]; d_eval.
Qed.

Lemma tagged_eval_inv : forall f t u v, 'tagged[f,t] @ u ==> v -> f @ u ==> v.
Proof. intros f t u v H; invert_eval; assumption. Qed.

Lemma seek_unfold_inv : forall p n f r,
  seek p n @ f ==> r ->
  exists b, p @ n ==> b /\ b @ (done n '* seek p (succ n)) @r f ==> r.
Proof.
  intros p n f r H.
  pose proof (done_step_eval n) as HD.
  pose proof (succ_step_eval n) as HS.
  unfold seek in H; apply tagged_eval_inv, wait_eval_inv in H.
  destruct (eval_app_r_inv _ _ _ H) as [g [Hg Hf]].
  apply Z_unfold_inv in Hg.
  unfold seek_body in Hg; cbn -[succ_step done_step] in Hg.
  invert_eval.
  pose proof (eval_deterministic _ _ H10 _ HD); subst v4.
  pose proof (eval_deterministic _ _ H14 _ HS); subst v9.
  exists v1; split; [exact H9|eapply eval_appl; [exact H8|exact Hf]].
Qed.

Lemma tt_choose : forall a b f r, a @ f ==> r -> 'tt @ (a '* b) @r f ==> r.
Proof.
  intros a b f r H; eapply eval_appl; [apply tagged_eval; apply fst_pair|exact H].
Qed.
Lemma ff_choose : forall a b f r, b @ f ==> r -> 'ff @ (a '* b) @r f ==> r.
Proof.
  intros a b f r H; eapply eval_appl; [apply tagged_eval; apply snd_pair|exact H].
Qed.

Lemma seek_found : forall p n f v,
  p @ n ==> 'tt -> f @ n ==> v -> seek p n @ f ==> v.
Proof.
  intros; eapply seek_unfold; [eassumption|]; apply tt_choose; apply done_eval; assumption.
Qed.

Lemma seek_next : forall p n f v,
  p @ n ==> 'ff -> seek p (succ n) @ f ==> v -> seek p n @ f ==> v.
Proof.
  intros; eapply seek_unfold; [eassumption|]; apply ff_choose; assumption.
Qed.

Lemma seek_found_inv : forall p n f v,
  p @ n ==> 'tt -> seek p n @ f ==> v -> f @ n ==> v.
Proof.
  intros p n f v Hp H; destruct (seek_unfold_inv _ _ _ _ H) as [b [Hb Hr]].
  pose proof (eval_deterministic _ _ Hb _ Hp); subst b.
  destruct (eval_app_r_inv _ _ _ Hr) as [c [Hc Hf]].
  apply tagged_eval_inv in Hc.
  pose proof (eval_deterministic _ _ Hc _ (fst_pair _ _)); subst c.
  apply done_eval_inv; exact Hf.
Qed.

Lemma seek_next_inv : forall p n f v,
  p @ n ==> 'ff -> seek p n @ f ==> v -> seek p (succ n) @ f ==> v.
Proof.
  intros p n f v Hp H; destruct (seek_unfold_inv _ _ _ _ H) as [b [Hb Hr]].
  pose proof (eval_deterministic _ _ Hb _ Hp); subst b.
  destruct (eval_app_r_inv _ _ _ Hr) as [c [Hc Hf]].
  apply tagged_eval_inv in Hc.
  pose proof (eval_deterministic _ _ Hc _ (snd_pair _ _)); subst c.
  exact Hf.
Qed.

Definition is_odd := Eval cbn in to_tree (star "n" (Ref "n" @@ (Val 'ff ''* Val neg))).
Definition Odd := swap ('Bool '* Neg).

Lemma is_odd_swap : is_odd = swap ('ff '* neg).
Proof. reflexivity. Qed.

Lemma neg_ff : neg @ 'ff ==> 'tt.
Proof. cbv; evaluate. Qed.

Lemma is_odd_zero : is_odd @ zero ==> 'ff.
Proof. rewrite is_odd_swap; unfold swap; pose proof (zero_apply ('ff) neg) as H; evaluate. Qed.

Lemma is_odd_one : is_odd @ one ==> 'tt.
Proof.
  rewrite is_odd_swap; unfold swap.
  assert (H : one @ ('ff '* neg) ==> 'tt)
    by (eapply succ_apply; [apply zero_apply|apply neg_ff]).
  evaluate.
Qed.

(** The worked search: the first odd number. *)
Lemma seek_is_odd_eval : seek is_odd zero @ 'I ==> one.
Proof.
  apply seek_next; [apply is_odd_zero|].
  apply seek_found; [apply is_odd_one|evaluate].
Qed.

Lemma infer_is_odd : forall AI, supports_booleans AI -> infer AI @ is_odd ==> Sm Odd.
Proof.
  intros AI HB; rewrite is_odd_swap; unfold Odd; apply infer_swap; apply infer_product_value;
    [apply ff_infer; exact HB|apply neg_infer; exact HB].
Qed.

Lemma type_app_Odd : forall AI, type_app AI @ Odd @r ('Nat) ==> Sm ('Bool).
Proof.
  intros AI; unfold Odd; apply type_app_swap2.
  apply type_app_Nat; apply neg_type_app.
Qed.

Lemma infer_seek_is_odd : forall AI,
  supports_search AI -> supports_booleans AI -> supports_number AI ->
  infer_expression AI @ (seek is_odd zero @ 'I) ==> Sm ('Nat).
Proof.
  intros AI HS HB HN; eapply infer_expression_fork.
  - apply infer_expression_stem; eapply infer_seek;
      [exact HS|apply infer_is_odd; exact HB|apply infer_zero; exact HN|apply type_app_Odd].
  - apply infer_expression_stem; apply infer_I.
  - apply type_app_Search; apply type_app_I.
Qed.

(** ** The same example at a function type

    [minimisation_fn] is the same search with [Nat --> Nat] as invariant.  The
    predicate needs a function type, so [is_odd] is decorated with a witness. *)
From TreeTyping Require Import functions recursion.

Definition typed_is_odd := lam is_odd zero.

Lemma minimise_is_odd_fn_eval : minimisation_fn @ typed_is_odd @r zero ==> one.
Proof.
  pose proof ordinary_ontology_supports_booleans as HB.
  pose proof ordinary_ontology_supports_number as HN.
  eapply (minimisation_false ordinary_decl HB HN).
  - unfold typed_is_odd; apply lam_eval; apply is_odd_zero.
  - apply (minimisation_true ordinary_decl HB HN); unfold typed_is_odd; apply lam_eval; apply is_odd_one.
Qed.

Theorem infer_minimise_is_odd_fn : forall (AI : Decl),
  supports_booleans AI -> supports_number AI ->
  infer_expression AI @ (minimisation_fn @ typed_is_odd @r zero) ==> Sm ('Nat).
Proof.
  intros AI HB HN.
  assert (Hp : infer AI @ typed_is_odd ==> Sm ('Nat --> 'Bool)).
  { unfold typed_is_odd; eapply infer_lam;
      [apply infer_is_odd; exact HB|apply infer_zero; exact HN|apply type_app_Odd]. }
  eapply infer_expression_fork.
  - eapply infer_expression_fork;
      [apply infer_expression_stem; apply infer_minimisation_fn; assumption
      |apply infer_expression_stem; exact Hp
      |apply type_app_abstract; apply funty_eliminator_eval].
  - apply infer_expression_stem; apply infer_zero; exact HN.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.

(** The row can sit in declarations that must stay tag-free. *)
Lemma seek_run_tag_free : tag_free seek_run = true.
Proof. vm_compute; reflexivity. Qed.
Lemma search_row_tag_free : tag_free search_row = true.
Proof. vm_compute; reflexivity. Qed.

(** ** The plain search

    The same search through [Z] with no lazy type: [plain_search @ (p * n) @ u]
    tests [p @ n] and returns [n] or searches on from [succ n].  The argument
    [u] only delays the recursive call.  The arms of its conditional have
    different types, so type application refuses it. *)
Definition plain_search_body := Eval cbn -[succ_step] in to_tree
  (star "self" (star "q" (star "u"
    (((Val 'fst @@ Ref "q") @@ (Val 'snd @@ Ref "q"))
       @@ (''wait[Val 'K, Val 'snd @@ Ref "q"] ''*
           ''wait[Ref "self", (Val 'fst @@ Ref "q") ''* (Val succ_step @@ (Val 'snd @@ Ref "q"))])
       @@ Ref "u")))).
Definition plain_search := Z plain_search_body.

Lemma plain_search_refused :
  type_app nat_ontology @ plain_search @r (('K1 ('Bool)) '* 'Nat) ==> Lf.
Proof. apply (eval_bounded_sound 8000); vm_compute; reflexivity. Qed.

(** It runs, with a predicate that holds at once. *)
Lemma plain_search_runs :
  plain_search @ (('K1 ('tt)) '* numeral 3) @r Lf ==> numeral 3.
Proof. apply (eval_bounded_sound 4000); vm_compute; reflexivity. Qed.

