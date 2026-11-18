(** * Step 82, stage 6, part 1: typed equality.

    [typed_equal = rec_query[Query[Bool], eq_body]].  Applied to [x] it is a
    triage query on [x] whose four cases build, at run time, a triage query
    on the second argument [y]:

      x = Lf          is_leaf
      x = Sm x1       stem_test (typed_equal @ x1)
      x = Fk x1 x2    fork_test (typed_equal @ x1) (typed_equal @ x2)     (not a tag)
      x = tagged[c,n] tag_test  (typed_equal @ c)  (typed_equal @ n)

    and [fork_test q1 q2] answers [tt] at an untagged fork [Fk y1 y2] when
    [q1 @ y1] and [q2 @ y2] do, [ff] elsewhere; [tag_test] likewise at a tag.
    Every run-time query is tagged by the query constructor [mk_query]. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries scott_arithmetic department_queries paper_ontology self_typing size_queries.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

Ltac by_runE := apply (runp_sound 40); vm_compute; reflexivity.

Definition QB : Combination := Query Bool.
Definition QQB : Combination := Query QB.
Definition kq_ff : Combination := Kq Bool ff.
Definition KKff : Combination := Kq QB kq_ff.

(** [is_leaf] answers [tt] at a leaf and [ff] elsewhere. *)
Definition is_leaf : Combination := triageq Bool tt kq_ff KKff KKff.

(** [stem_test q @ y] is [q @ y1] at [y = Sm y1] and [ff] elsewhere. *)
Definition stem_test : Combination := Eval cbn -[mk_query tq_body KKff ff] in to_tree
  (star "q" (op (mk_query Bool) @@ W3 (Val tq_body) (Val ff) (Ref "q") (Val (Fk KKff KKff)))).
Definition ST : Combination := Eval vm_compute in ty_of stem_test.

(** [and_fn b1 b2 = b1 @ (b2 * ff)]. *)
Definition and_fn : Combination := Eval cbn -[ff] in to_tree
  (star "b1" (star "b2" (Ref "b1" @@ (Ref "b2" ''* Val ff)))).
Definition AndT : Combination := Eval vm_compute in ty_of and_fn.
Definition AB : Combination := Eval vm_compute in ap_ty AndT Bool.

(** [and_q q2 b1] is the query [y2 => and b1 (q2 @ y2)]. *)
Definition and_q : Combination := Eval cbn -[mk_query and_fn] in to_tree
  (star "q2" (star "b1" (op (mk_query Bool) @@
     S2t (op (mk_query AB) @@ (Val 'K @@ (op and_fn @@ Ref "b1"))) (Ref "q2")))).
Definition ANDQ : Combination := Eval vm_compute in ty_of and_q.
Definition A1 : Combination := Eval vm_compute in ap_ty ANDQ QB.
Definition kq_and_q : Combination := Kq ANDQ and_q.

(** [pair_q q1 q2 @ y1 @ y2 = and (q1 @ y1) (q2 @ y2)]. *)
Definition pair_q (q1 q2 : Term) : Term :=
  op (mk_query QB) @@ S2t (op (mk_query A1) @@ S2t (Val kq_and_q) (op (mk_query QB) @@ (Val 'K @@ q2))) q1.

Definition fork_test : Combination := Eval cbn -[mk_query tq_body KKff kq_ff kq_and_q ff] in to_tree
  (star "q1" (star "q2" (op (mk_query Bool) @@
     W3 (Val tq_body) (Val ff) (Val kq_ff) (Val Lf @@ pair_q (Ref "q1") (Ref "q2") @@ Val KKff)))).
Definition tag_test : Combination := Eval cbn -[mk_query tq_body KKff kq_ff kq_and_q ff] in to_tree
  (star "q1" (star "q2" (op (mk_query Bool) @@
     W3 (Val tq_body) (Val ff) (Val kq_ff) (Val Lf @@ Val KKff @@ pair_q (Ref "q1") (Ref "q2"))))).
Definition FTT : Combination := Eval vm_compute in ty_of fork_test.
Definition FT2 : Combination := Eval vm_compute in ap_ty FTT QB.
Definition TTT : Combination := Eval vm_compute in ty_of tag_test.
Definition TT2 : Combination := Eval vm_compute in ap_ty TTT QB.

(** [h_fork r q1] is the query [x2 => fork_test q1 (r @ x2)]. *)
Definition h_fork : Combination := Eval cbn -[mk_query fork_test] in to_tree
  (star "r" (star "q1" (op (mk_query QB) @@ S2t (op (mk_query FT2) @@ (Val 'K @@ (op fork_test @@ Ref "q1"))) (Ref "r")))).
Definition h_tag : Combination := Eval cbn -[mk_query tag_test] in to_tree
  (star "r" (star "q1" (op (mk_query QB) @@ S2t (op (mk_query TT2) @@ (Val 'K @@ (op tag_test @@ Ref "q1"))) (Ref "r")))).
Definition HF : Combination := Eval vm_compute in ty_of h_fork.
Definition HFT : Combination := Eval vm_compute in ap_ty HF QQB.
Definition HG : Combination := Eval vm_compute in ty_of h_tag.
Definition HGT : Combination := Eval vm_compute in ap_ty HG QQB.
Definition kq_stem : Combination := Kq ST stem_test.
Definition kq_hfork : Combination := Kq HF h_fork.
Definition kq_htag : Combination := Kq HG h_tag.

Definition eq_body : Combination := Eval cbn -[mk_query tq_body is_leaf kq_stem kq_hfork kq_htag] in to_tree
  (star "r" (op (mk_query QB) @@
     W3 (Val tq_body) (Val is_leaf)
        (op (mk_query QB) @@ S2t (Val kq_stem) (Ref "r"))
        (Val Lf @@
           (op (mk_query QQB) @@ S2t (op (mk_query HFT) @@ S2t (Val kq_hfork) (op (mk_query QQB) @@ (Val 'K @@ Ref "r"))) (Ref "r"))
         @@
           (op (mk_query QQB) @@ S2t (op (mk_query HGT) @@ S2t (Val kq_htag) (op (mk_query QQB) @@ (Val 'K @@ Ref "r"))) (Ref "r"))))).

(** The seed is the constant query [KKff : Query[Query[Bool]]]; it is never applied. *)
Definition typed_equal : Combination := rec_query QB eq_body KKff.
Definition EqBodyT : Combination := Eval vm_compute in ty_of eq_body.

Lemma infer_eq_body : infer PO @ eq_body ==> Sm EqBodyT. Proof. by_runE. Qed.
Lemma eq_body_type_app : tp PO @ EqBodyT @r QQB ==> Sm QQB. Proof. by_runE. Qed.

Theorem infer_typed_equal : infer PO @ typed_equal ==> Sm (Query (Query Bool)).
Proof.
  eapply rec_query_generic; [exact PO_query|exact PO_mkq|exact PO_update|exact PO_mku
    |exact infer_eq_body|exact eq_body_type_app|by_runE].
Qed.

Example typed_equal_tt_tt : typed_equal @ tt @r tt ==> tt. Proof. by_runE. Qed.
Example typed_equal_tt_ff : typed_equal @ tt @r ff ==> ff. Proof. by_runE. Qed.
Example typed_equal_K_Lf : typed_equal @ 'K @r Lf ==> ff. Proof. by_runE. Qed.
Example typed_equal_fork : typed_equal @ Fk 'K Lf @r Fk 'K Lf ==> tt. Proof. by_runE. Qed.
(** A tag and the untagged fork of its carrier and name differ. *)
Example typed_equal_tag_fork : typed_equal @ tt @r Fk 'fst bool_nm ==> ff. Proof. by_runE. Qed.

(** ** Typed equality is tree equality *)

(** [S2_fwd], [K1_fwd], [Kq_fwd] and [mkq_fwd] are in size_queries.v since step 89. *)

Section TQ.
Variables b s g t : Combination.
Let Hgl := get_l_fk g t.
Let Hgr := get_r_fk g t.
Lemma tq_leaf : 'wait3[tq_body, b, s, Fk g t] @ Lf ==> b.
Proof. apply wait3_eval; unfold tq_body; pose proof (get_tagged_spec Lf) as HG; cbn in HG; pose proof Hgl; pose proof Hgr; ev2. Qed.
Lemma tq_stem : forall y w, s @ y ==> w -> 'wait3[tq_body, b, s, Fk g t] @ Sm y ==> w.
Proof. intros y w H; apply wait3_eval; unfold tq_body; pose proof (get_tagged_spec (Sm y)) as HG; cbn in HG; pose proof Hgl; pose proof Hgr; ev2. Qed.
Lemma tq_fork : forall y z h w, tag_of (Fk y z) = None -> g @ y ==> h -> h @ z ==> w ->
  'wait3[tq_body, b, s, Fk g t] @ Fk y z ==> w.
Proof.
  intros y z h w E H1 H2; apply wait3_eval; unfold tq_body; pose proof (get_tagged_spec (Fk y z)) as HG; rewrite E in HG.
  pose proof Hgl; pose proof Hgr. ev2.
Qed.
Lemma tq_tag : forall c n h w, t @ c ==> h -> h @ n ==> w ->
  'wait3[tq_body, b, s, Fk g t] @ 'tagged[c,n] ==> w.
Proof.
  intros c n h w H1 H2; apply wait3_eval; unfold tq_body; pose proof (get_tagged_spec ('tagged[c,n])) as HG;
  rewrite tag_of_tagged in HG.
  pose proof Hgl; pose proof Hgr; pose proof (get_l_fk c n) as Hl2; pose proof (get_r_fk c n) as Hr2. ev2.
Qed.
End TQ.
Definition te_step : Combination := Eval vm_compute in
  match runp 40 (eq_body @ typed_equal) with Some v => v | None => Lf end.
Lemma te_body_eval : eq_body @ typed_equal ==> te_step. Proof. apply (runp_sound 40); vm_done. Qed.
Definition SR : Combination := 'tagged['S2[kq_stem, typed_equal], query_tag (code QB)].
Definition GR : Combination := 'tagged['S2['tagged['S2[kq_hfork, 'tagged['K1 typed_equal, query_tag (code QQB)]], query_tag (code HFT)], typed_equal], query_tag (code QQB)].
Definition TR : Combination := 'tagged['S2['tagged['S2[kq_htag, 'tagged['K1 typed_equal, query_tag (code QQB)]], query_tag (code HGT)], typed_equal], query_tag (code QQB)].
Lemma te_step_shape : te_step = 'tagged['wait3[tq_body, is_leaf, SR, Fk GR TR], query_tag (code QB)].
Proof. vm_compute; reflexivity. Qed.

Definition stemQ (q : Combination) := 'tagged['wait3[tq_body, ff, q, Fk KKff KKff], query_tag (code Bool)].
Definition PQ (q1 q2 : Combination) :=
  'tagged['S2['tagged['S2[kq_and_q, 'tagged['K1 q2, query_tag (code QB)]], query_tag (code A1)], q1], query_tag (code QB)].
Definition forkQ (q1 q2 : Combination) := 'tagged['wait3[tq_body, ff, kq_ff, Fk (PQ q1 q2) KKff], query_tag (code Bool)].
Definition tagQ (q1 q2 : Combination) := 'tagged['wait3[tq_body, ff, kq_ff, Fk KKff (PQ q1 q2)], query_tag (code Bool)].
Local Opaque mk_query KKff kq_ff tq_body kq_and_q ff.
Ltac evm := split2; evaluate2; repeat first [eassumption | apply mkq_fwd | progress evaluate2].
Lemma stem_test_eval : forall q, stem_test @ q ==> stemQ q.
Proof. intros q; unfold stem_test, stemQ; evm. Qed.
Lemma fork_test_eval : forall q1 q2, fork_test @ q1 @r q2 ==> forkQ q1 q2.
Proof. intros q1 q2; unfold fork_test, forkQ, PQ; evm. Qed.
Lemma tag_test_eval : forall q1 q2, tag_test @ q1 @r q2 ==> tagQ q1 q2.
Proof. intros q1 q2; unfold tag_test, tagQ, PQ; evm. Qed.
Local Opaque and_fn.
Definition AQ (q2 f : Combination) := 'tagged['S2['tagged['K1 f, query_tag (code AB)], q2], query_tag (code Bool)].
Lemma and_q_eval : forall q2 b1 f, and_fn @ b1 ==> f -> and_q @ q2 @r b1 ==> AQ q2 f.
Proof. intros q2 b1 f H; unfold and_q, AQ; evm. Qed.
Definition HFq (r q1 f : Combination) := 'tagged['S2['tagged['K1 f, query_tag (code FT2)], r], query_tag (code QB)].
Local Opaque fork_test tag_test.
Lemma h_fork_eval : forall r q1 f, fork_test @ q1 ==> f -> h_fork @ r @r q1 ==> HFq r q1 f.
Proof. intros r q1 f H; unfold h_fork, HFq; evm. Qed.
Definition HTq (r q1 f : Combination) := 'tagged['S2['tagged['K1 f, query_tag (code TT2)], r], query_tag (code QB)].
Lemma h_tag_eval : forall r q1 f, tag_test @ q1 ==> f -> h_tag @ r @r q1 ==> HTq r q1 f.
Proof. intros r q1 f H; unfold h_tag, HTq; evm. Qed.

(** ** The general evaluation *)
Local Transparent ff kq_ff KKff and_fn kq_and_q mk_query tq_body fork_test tag_test.
Definition eqv (x y : Combination) : Combination := if combination_eq_dec x y then tt else ff.
Definition andv (b1 b2 : Combination) : Combination := if combination_eq_dec b1 tt then b2 else ff.

Lemma and_tt : forall b2, and_fn @ tt @r b2 ==> b2.
Proof. intros; unfold and_fn, tt; evaluate. Qed.
Lemma and_ff : forall b2, and_fn @ ff @r b2 ==> ff.
Proof. intros; unfold and_fn, ff; evaluate. Qed.
Lemma and_andv : forall b1 b2, b1 = tt \/ b1 = ff -> and_fn @ b1 @r b2 ==> andv b1 b2.
Proof.
  intros b1 b2 [-> | ->]; unfold andv.
  - destruct (combination_eq_dec tt tt) as [_|n]; [apply and_tt|contradiction].
  - destruct (combination_eq_dec ff tt) as [e|_]; [discriminate|apply and_ff].
Qed.
Lemma eqv_bool : forall x y, eqv x y = tt \/ eqv x y = ff.
Proof. intros; unfold eqv; destruct combination_eq_dec; auto. Qed.

Lemma PQ_spec : forall q1 q2 y1 y2 b1 b2, q1 @ y1 ==> b1 -> q2 @ y2 ==> b2 -> b1 = tt \/ b1 = ff ->
  PQ q1 q2 @ y1 @r y2 ==> andv b1 b2.
Proof.
  intros q1 q2 y1 y2 b1 b2 H1 H2 Hb.
  destruct (app2_inv _ _ _ _ (and_andv b1 b2 Hb)) as [f [Hf Hfb]].
  destruct (app2_inv _ _ _ _ (and_q_eval q2 b1 f Hf)) as [a1 [Ha1 Ha1b]].
  eapply app2.
  - unfold PQ; apply tagged_eval; eapply S2_fwd; [|exact H1|exact Ha1b].
    apply tagged_eval; eapply S2_fwd; [apply Kq_fwd| |exact Ha1]. apply tagged_eval, K1_fwd.
  - unfold AQ; apply tagged_eval; eapply S2_fwd; [apply tagged_eval, K1_fwd|exact H2|exact Hfb].
Qed.

Fixpoint tsize (t : Combination) : nat :=
  match t with Lf => 1 | Sm u => S (tsize u) | Fk u v => S (tsize u + tsize v) end.

Ltac neqv := unfold eqv; destruct combination_eq_dec; [congruence|reflexivity].

(** The four shapes of the second argument, at a run-time triage query. *)
Lemma tq_query_spec : forall b s g t tg y w,
  (y = Lf -> b = w) ->
  (forall y1, y = Sm y1 -> s @ y1 ==> w) ->
  (forall y1 y2, y = Fk y1 y2 -> tag_of (Fk y1 y2) = None -> g @ y1 @r y2 ==> w) ->
  (forall c n, y = 'tagged[c,n] -> t @ c @r n ==> w) ->
  'tagged['wait3[tq_body, b, s, Fk g t], tg] @ y ==> w.
Proof.
  intros b s g t tg y w HL HS HF HT; apply tagged_eval.
  destruct y as [|y1|y1 y2].
  - rewrite <- (HL eq_refl); apply tq_leaf.
  - apply tq_stem, HS; reflexivity.
  - destruct (tag_of (Fk y1 y2)) as [[c n]|] eqn:E.
    + apply tag_of_some in E; rewrite E. destruct (app2_inv _ _ _ _ (HT c n E)) as [h [H1 H2]].
      eapply tq_tag; eassumption.
    + destruct (app2_inv _ _ _ _ (HF y1 y2 eq_refl E)) as [h [H1 H2]]. eapply tq_fork; eassumption.
Qed.

Lemma KKff_2 : forall y1 y2, KKff @ y1 @r y2 ==> ff.
Proof. intros; eapply app2; [apply Kq_fwd|apply Kq_fwd]. Qed.

Theorem typed_equal_spec : forall x, exists q, typed_equal @ x ==> q /\ forall y, q @ y ==> eqv x y.
Proof.
  intros x; remember (tsize x) as m eqn:Em; revert x Em.
  induction m as [m IH] using lt_wf_ind; intros x Em.
  assert (Hunf : forall v, te_step @ x ==> v -> typed_equal @ x ==> v)
    by (intros v Hv; eapply (rec_query_unfold QB eq_body ('K1 kq_ff)); [exact te_body_eval|exact Hv]).
  rewrite te_step_shape in Hunf.
  destruct x as [|x1|x1 x2].
  - (* leaf *)
    exists is_leaf; split; [apply Hunf, tagged_eval, tq_leaf|].
    intros y; unfold is_leaf, triageq; apply tq_query_spec.
    + intros ->; unfold eqv; destruct combination_eq_dec; [reflexivity|congruence].
    + intros y1 ->; replace (eqv Lf (Sm y1)) with ff by neqv; apply Kq_fwd.
    + intros y1 y2 -> _; replace (eqv Lf (Fk y1 y2)) with ff by neqv; apply KKff_2.
    + intros c n ->; replace (eqv Lf ('tagged[c,n])) with ff by neqv; apply KKff_2.
  - (* stem *)
    destruct (IH (tsize x1) ltac:(cbn in Em; lia) x1 eq_refl) as [q1 [Hq1 Hs1]].
    exists (stemQ q1); split.
    + apply Hunf, tagged_eval, tq_stem. unfold SR; apply tagged_eval.
      eapply S2_fwd; [apply Kq_fwd|exact Hq1|apply stem_test_eval].
    + intros y; unfold stemQ; apply tq_query_spec.
      * intros ->; neqv.
      * intros y1 ->. replace (eqv (Sm x1) (Sm y1)) with (eqv x1 y1); [apply Hs1|].
        unfold eqv; do 2 destruct combination_eq_dec; congruence.
      * intros y1 y2 -> _; replace (eqv (Sm x1) (Fk y1 y2)) with ff by neqv; apply KKff_2.
      * intros c n ->; replace (eqv (Sm x1) ('tagged[c,n])) with ff by neqv; apply KKff_2.
  - destruct (tag_of (Fk x1 x2)) as [[c n]|] eqn:Ex.
    + (* tag *)
      apply tag_of_some in Ex. rewrite Ex in Em, Hunf |- *.
      destruct (IH (tsize c) ltac:(cbn in Em; lia) c eq_refl) as [q1 [Hq1 Hs1]].
      destruct (IH (tsize n) ltac:(cbn in Em; lia) n eq_refl) as [q2 [Hq2 Hs2]].
      destruct (app2_inv _ _ _ _ (tag_test_eval q1 q2)) as [f [Hf Hf2]].
      destruct (app2_inv _ _ _ _ (h_tag_eval typed_equal q1 f Hf)) as [h [Hh Hh2]].
      exists (tagQ q1 q2); split.
      * apply Hunf, tagged_eval. eapply tq_tag.
        -- unfold TR; apply tagged_eval. eapply S2_fwd; [|exact Hq1|exact Hh2].
           apply tagged_eval; eapply S2_fwd; [apply Kq_fwd|apply tagged_eval, K1_fwd|exact Hh].
        -- unfold HTq; apply tagged_eval; eapply S2_fwd; [apply tagged_eval, K1_fwd|exact Hq2|exact Hf2].
      * intros y; unfold tagQ; apply tq_query_spec.
        -- intros ->; neqv.
        -- intros y1 ->; replace (eqv ('tagged[c,n]) (Sm y1)) with ff by neqv; apply Kq_fwd.
        -- intros y1 y2 -> Ey. replace (eqv ('tagged[c,n]) (Fk y1 y2)) with ff; [apply KKff_2|].
           unfold eqv; destruct combination_eq_dec as [E|]; [|reflexivity].
           rewrite <- E, tag_of_tagged in Ey; discriminate.
        -- intros c' n' ->.
           replace (eqv ('tagged[c,n]) ('tagged[c',n'])) with (andv (eqv c c') (eqv n n')).
           ++ apply PQ_spec; [apply Hs1|apply Hs2|apply eqv_bool].
           ++ unfold andv, eqv. destruct (combination_eq_dec c c'), (combination_eq_dec n n');
                repeat destruct combination_eq_dec; subst; try congruence;
                match goal with H : 'tagged[_,_] = 'tagged[_,_] |- _ => inversion H; subst; congruence end.
    + (* untagged fork *)
      destruct (IH (tsize x1) ltac:(cbn in Em; lia) x1 eq_refl) as [q1 [Hq1 Hs1]].
      destruct (IH (tsize x2) ltac:(cbn in Em; lia) x2 eq_refl) as [q2 [Hq2 Hs2]].
      destruct (app2_inv _ _ _ _ (fork_test_eval q1 q2)) as [f [Hf Hf2]].
      destruct (app2_inv _ _ _ _ (h_fork_eval typed_equal q1 f Hf)) as [h [Hh Hh2]].
      exists (forkQ q1 q2); split.
      * apply Hunf, tagged_eval. eapply tq_fork; [exact Ex| |].
        -- unfold GR; apply tagged_eval. eapply S2_fwd; [|exact Hq1|exact Hh2].
           apply tagged_eval; eapply S2_fwd; [apply Kq_fwd|apply tagged_eval, K1_fwd|exact Hh].
        -- unfold HFq; apply tagged_eval; eapply S2_fwd; [apply tagged_eval, K1_fwd|exact Hq2|exact Hf2].
      * intros y; unfold forkQ; apply tq_query_spec.
        -- intros ->; neqv.
        -- intros y1 ->; replace (eqv (Fk x1 x2) (Sm y1)) with ff by neqv; apply Kq_fwd.
        -- intros y1 y2 -> Ey.
           replace (eqv (Fk x1 x2) (Fk y1 y2)) with (andv (eqv x1 y1) (eqv x2 y2)).
           ++ apply PQ_spec; [apply Hs1|apply Hs2|apply eqv_bool].
           ++ unfold andv, eqv; repeat destruct combination_eq_dec; subst; congruence.
        -- intros c n ->. replace (eqv (Fk x1 x2) ('tagged[c,n])) with ff; [apply KKff_2|].
           unfold eqv; destruct combination_eq_dec as [E|]; [|reflexivity].
           rewrite E, tag_of_tagged in Ex; discriminate.
Qed.

Theorem typed_equal_eval : forall x y,
  typed_equal @ x @r y ==> (if combination_eq_dec x y then tt else ff).
Proof.
  intros x y; destruct (typed_equal_spec x) as [q [Hq Hs]]; eapply app2; [exact Hq|apply Hs].
Qed.

(** The paper's statement: the type, its applications at any two argument
    types, and equality of [typed_equal] with itself. *)
Theorem typed_equal_polymorphic :
  infer PO @ typed_equal ==> Sm (Query (Query Bool)) /\
  (forall U V, tp PO @ Query (Query Bool) @r U ==> Sm (Query Bool) /\ tp PO @ Query Bool @r V ==> Sm Bool) /\
  typed_equal @ typed_equal @r typed_equal ==> tt.
Proof.
  split; [exact infer_typed_equal|split].
  - intros U V; split; apply type_app_Query; cbn; reflexivity.
  - pose proof (typed_equal_eval typed_equal typed_equal) as H.
    destruct (combination_eq_dec typed_equal typed_equal); [exact H|contradiction].
Qed.

(** Applied to any two typed values, typed equality is typed: [typed_equal @ x @r y :: Bool]. *)
Theorem typed_equal_application : forall x U y V, infer PO @ x ==> Sm U -> infer PO @ y ==> Sm V ->
  infer_expression PO @ (typed_equal @ x @r y) ==> Sm Bool.
Proof.
  intros x U y V Hx Hy.
  eapply ie_fork; [|apply ie_stem, Hy|apply type_app_Query; cbn; reflexivity].
  eapply ie_fork; [apply ie_stem, infer_typed_equal|apply ie_stem, Hx|apply type_app_Query; cbn; reflexivity].
Qed.
