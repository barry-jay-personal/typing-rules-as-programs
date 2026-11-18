(** * Step 82, stage 7, part 2: every partial mu-recursive function, typed by invariant on Nat.

    Each [f : mu_fun (S k)] is compiled to a program [tcompile f] on Scott
    numerals, taking its arguments as one right-nested tuple:
    - zero: [K1 zero]; successor: [succ_fn] (through the constructor [mk_nat]);
    - projection: [snd] repeated, then [fst] unless last;
    - composition: [x |-> H (G1 x * (G2 x * ... Gm x))];
    - primitive recursion: an iteration by an update on the plain state
      [m * (c * a) : Nat * (Nat * Nat)] (remaining count, index counting up,
      accumulator), recognised by its type; the step at count [Sm m] is
      [r @ (m * (succ c * h (c * (a * xs))))], so no subtraction is needed;
    - minimisation: [x |-> minimisation @ wait[pred F, x] @ 0] with
      [pred F @ x @ n = F (n * x) @ (tt * K1 ff)].
    The compiled programs hold constructors and updates, so they are not
    concrete; their types [tycompile f] have the same shape, with the type
    of each constant in place of the constant.  Type application of the
    type to [Nat^(k+1)] gives [Nat] by induction on [f], meeting each
    recursion at [Update]. *)

From Stdlib Require Import String List Bool Lia PeanoNat.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology scott_arithmetic poly size_queries numbers_rt.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK sp_body code_p type_of_p.
Local Notation PO := paper_ontology.

Ltac by_runM := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** ** Tuples *)

Fixpoint nat_tuple (k : nat) : Combination :=
  match k with O => Nat | S k => Nat '* nat_tuple k end.

Fixpoint tuple_of (xs : list Combination) : Combination :=
  match xs with
  | [] => Lf
  | x :: rest => match rest with [] => x | _ => x '* tuple_of rest end
  end.

Lemma tuple_of_cons : forall x rest, rest <> [] -> tuple_of (x :: rest) = x '* tuple_of rest.
Proof. intros x [|y r] H; [contradiction|reflexivity]. Qed.

(** ** The iteration for primitive recursion *)

Definition NNN : Combination := Nat '* (Nat '* Nat).

(** The application of [g] is made to depend on [p] (through [snd (p * c) = c]) so
    that it is not evaluated when the closure is built: at count [zero] the
    step must not apply [g]. *)
Definition pr_step_t (g r : Term) : Term := star "x"
  ((Val 'fst @@ Ref "x") @@ (Ref "x" ''* (star "p" (r @@ (Ref "p" ''*
      (succ_t (Val 'fst @@ (Val 'snd @@ Ref "x")) ''*
       (g @@ ((Val 'snd @@ (Ref "p" ''* (Val 'fst @@ (Val 'snd @@ Ref "x")))) ''* (Val 'snd @@ (Val 'snd @@ Ref "x")))))))))).

Definition pr_iter : Combination := Eval cbn -[mk_update sp_body identity_update self_apply bz mk_nat code] in to_tree
  (star "g"
    (op mk_update @@ ''wait[Val self_apply,
       (star "r" (op mk_update @@ w3 (Val (code NNN)) (pr_step_t (Ref "g") (Ref "r")) (Val identity_update))
         ''C tagger_t (Val update_nm)) ''C Val bz])).

(** ** The skeletons, with their constants as parameters *)

Definition pair_at (A B : Combination) : Combination :=
  to_tree (star "x" ((Val A @@ (Val 'I @@ Ref "x")) ''* (Val B @@ (Val 'I @@ Ref "x")))).

Fixpoint snds (i : nat) : Combination := match i with O => 'I | S i => snds i 'C 'snd end.
Definition tproj (i j : nat) : Combination := match j with O => snds i | S _ => 'fst 'C snds i end.
Definition comp_prog (H T : Combination) : Combination := H 'C (T 'C 'I).

(** [hstep H @ x @ (c * a) = H @ (c * (a * snd x))] *)
Definition hstep (H : Combination) : Combination :=
  to_tree (star "x" (star "q" (Val H @@ ((Val 'fst @@ Ref "q") ''* ((Val 'snd @@ Ref "q") ''* (Val 'snd @@ Ref "x")))))).

(** [rec_s PI Z0 HS G @ x = snd (snd (PI @ wait[HS, x] @ (fst x * (Z0 * G (snd x)))))] *)
Definition rec_s (PI Z0 HS G : Combination) : Combination :=
  to_tree (star "x" (Val 'snd @@ (Val 'snd @@ ((op PI @@ ''wait[Val HS, Ref "x"])
     @@ ((Val 'fst @@ Ref "x") ''* (Val Z0 ''* (Val G @@ (Val 'snd @@ Ref "x")))))))).

(** [min_pred_s T F Fv @ x @ n = F (n * x) @ (T * K1 Fv)] *)
Definition min_pred_s (T F Fv : Combination) : Combination :=
  to_tree (star "x" (star "n" ((Val F @@ (Ref "n" ''* Ref "x")) @@ (Val T ''* (Val 'K @@ Val Fv))))).

(** [min_s M Z1 MP @ x = M @ wait[MP, x] @ (Z1 @ x)] *)
Definition min_s (M Z1 MP : Combination) : Combination :=
  to_tree (star "x" ((op M @@ ''wait[Val MP, Ref "x"]) @@ (Val Z1 @@ Ref "x"))).

Fixpoint tcompile {n} (f : mu_fun n) {struct f} : Combination :=
  match f with
  | mu_zero k => 'K1 zero
  | mu_succ => succ_fn
  | mu_proj i j => tproj i j
  | mu_comp k m h gs => comp_prog (tcompile h) (ttuple gs)
  | mu_rec k g h => rec_s pr_iter zero (hstep (tcompile h)) (tcompile g)
  | mu_min k f => min_s minimisation ('K1 zero) (min_pred_s tt (tcompile f) ff)
  end
with ttuple {n m} (gs : mu_funs n m) {struct gs} : Combination :=
  match gs with
  | mu_nil _ => 'I
  | mu_cons _ m' g gs' =>
      match m' with O => tcompile g 'C 'I | S _ => pair_at (tcompile g) (ttuple gs') end
  end.

Definition T_succ : Combination := Eval vm_compute in tyP succ_fn.
Definition T_pri : Combination := Eval vm_compute in tyP pr_iter.

Fixpoint tycompile {n} (f : mu_fun n) {struct f} : Combination :=
  match f with
  | mu_zero k => 'K1 Nat
  | mu_succ => T_succ
  | mu_proj i j => tproj i j
  | mu_comp k m h gs => comp_prog (tycompile h) (tytuple gs)
  | mu_rec k g h => rec_s T_pri Nat (hstep (tycompile h)) (tycompile g)
  | mu_min k f => min_s T_min ('K1 Nat) (min_pred_s Bool (tycompile f) Bool)
  end
with tytuple {n m} (gs : mu_funs n m) {struct gs} : Combination :=
  match gs with
  | mu_nil _ => 'I
  | mu_cons _ m' g gs' =>
      match m' with O => tycompile g 'C 'I | S _ => pair_at (tycompile g) (tytuple gs') end
  end.

(** ** Inference: the type has the shape of the program *)

Lemma infer_succ_fn : infer PO @ succ_fn ==> Sm T_succ. Proof. by_runM. Qed.
Lemma infer_pr_iter : infer PO @ pr_iter ==> Sm T_pri. Proof. by_runM. Qed.
Lemma infer_minimisation_P : infer PO @ minimisation ==> Sm T_min. Proof. by_runM. Qed.
Lemma infer_tt_P : infer PO @ tt ==> Sm Bool. Proof. by_runM. Qed.
Lemma infer_ff_P : infer PO @ ff ==> Sm Bool. Proof. by_runM. Qed.

Lemma infer_fork' : forall u1 u2 U1 U2, infer PO @ u1 ==> Sm U1 -> infer PO @ u2 ==> Sm U2 ->
  label_pair U1 U2 = false -> tag_of (Fk u1 u2) = None -> infer PO @ Fk u1 u2 ==> Sm (Fk U1 U2).
Proof. intros; apply infer_fork; assumption. Qed.

Ltac inferS := repeat first
  [ eassumption
  | (apply concrete_is_self_typed; reflexivity)
  | apply infer_leaf
  | apply infer_stem
  | (eapply infer_fork'; [ | | first [reflexivity|lp_false] | first [reflexivity | eapply not_tag_of_typed; eassumption]]) ].

Section Infer.
Variables A B : Combination.
Variables TA TB : Combination.
Hypothesis HA : infer PO @ A ==> Sm TA.
Hypothesis HB : infer PO @ B ==> Sm TB.

Lemma infer_pair_at : infer PO @ pair_at A B ==> Sm (pair_at TA TB).
Proof using HA HB. unfold pair_at; cbn; inferS. Qed.
Lemma infer_comp_prog : infer PO @ comp_prog A B ==> Sm (comp_prog TA TB).
Proof using HA HB. unfold comp_prog; inferS. Qed.
Lemma infer_hstep : infer PO @ hstep A ==> Sm (hstep TA).
Proof using HA. unfold hstep; cbn; inferS. Qed.
Lemma infer_rec_s : infer PO @ rec_s pr_iter zero (hstep A) B ==> Sm (rec_s T_pri Nat (hstep TA) TB).
Proof using HA HB.
  pose proof infer_pr_iter; pose proof paper_infer_zero; pose proof infer_hstep.
  unfold rec_s; cbn -[hstep pr_iter T_pri zero]; inferS.
Qed.
Lemma infer_min_s : infer PO @ min_s minimisation ('K1 zero) (min_pred_s tt A ff)
  ==> Sm (min_s T_min ('K1 Nat) (min_pred_s Bool TA Bool)).
Proof using HA.
  pose proof infer_minimisation_P; pose proof paper_infer_zero; pose proof infer_tt_P; pose proof infer_ff_P.
  assert (infer PO @ min_pred_s tt A ff ==> Sm (min_pred_s Bool TA Bool))
    by (unfold min_pred_s; cbn -[tt ff Bool]; inferS).
  unfold min_s; cbn -[min_pred_s minimisation T_min zero]; inferS.
Qed.
End Infer.

Lemma tproj_concrete : forall i j, concreteb (tproj i j) = true.
Proof.
  assert (Hs : forall i, concreteb (snds i) = true) by (induction i; cbn [snds]; [reflexivity|cbn; rewrite IHi; reflexivity]).
  intros i [|j]; cbn [tproj]; [apply Hs|cbn; rewrite Hs; reflexivity].
Qed.

Lemma infer_tcompile_all :
  (forall n (f : mu_fun n), infer PO @ tcompile f ==> Sm (tycompile f)) /\
  (forall n m (gs : mu_funs n m), infer PO @ ttuple gs ==> Sm (tytuple gs)).
Proof.
  apply (mu_fun_mutind (fun n f => infer PO @ tcompile f ==> Sm (tycompile f))
                       (fun n m gs => infer PO @ ttuple gs ==> Sm (tytuple gs)));
    cbn [tcompile ttuple tycompile tytuple]; intros.
  - pose proof paper_infer_zero; inferS.
  - apply infer_succ_fn.
  - apply concrete_is_self_typed, tproj_concrete.
  - apply infer_comp_prog; assumption.
  - apply infer_rec_s; assumption.
  - apply infer_min_s; assumption.
  - apply concrete_is_self_typed; reflexivity.
  - destruct m; [unfold comp_prog; inferS|apply infer_pair_at; assumption].
Qed.

Lemma infer_tcompile : forall n (f : mu_fun n), infer PO @ tcompile f ==> Sm (tycompile f).
Proof. exact (proj1 infer_tcompile_all). Qed.

(** ** Type application *)

Ltac tpsN := repeat first
  [ eassumption
  | apply type_app_Nat
  | apply type_app_mk_nat
  | apply type_app_Bool
  | apply type_app_Update
  | (apply (mku_app PO PO_mku); unfold upd_guard;
       first [ (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gch_miss; discriminate|reflexivity|]; apply or_g_l; eapply gsp_hit_code; [vm_compute; reflexivity|])
             | (eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gch_miss; discriminate|reflexivity|];
                eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit]) ])
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].

Lemma type_app_snds : forall i j, tp PO @ snds i @r nat_tuple (i + j) ==> Sm (nat_tuple j).
Proof.
  induction i as [|i IH]; intros j; cbn [snds Nat.add nat_tuple]; [apply app_I|].
  pose proof (IH j) as H; unfold snds in *; fold snds in *; tpsN.
Qed.

Lemma type_app_tproj : forall i j, tp PO @ tproj i j @r nat_tuple (i + j) ==> Sm Nat.
Proof.
  intros i [|j]; cbn [tproj].
  - exact (type_app_snds i 0).
  - pose proof (type_app_snds i (S j)) as Hs; cbn [nat_tuple] in Hs. tpsN.
Qed.

Lemma type_app_pair_at : forall TA TB X VA VB, tp PO @ TA @r X ==> Sm VA -> tp PO @ TB @r X ==> Sm VB ->
  tp PO @ pair_at TA TB @r X ==> Sm (VA '* VB).
Proof. intros; unfold pair_at; cbn; tpsN. Qed.

Lemma type_app_comp_prog : forall TH TT X V R, tp PO @ TT @r X ==> Sm V -> tp PO @ TH @r V ==> Sm R ->
  tp PO @ comp_prog TH TT @r X ==> Sm R.
Proof. intros; unfold comp_prog; tpsN. Qed.

Lemma type_app_rec_s : forall TG TH XS, tp PO @ TG @r XS ==> Sm Nat ->
  tp PO @ TH @r (Nat '* (Nat '* XS)) ==> Sm Nat ->
  tp PO @ rec_s T_pri Nat (hstep TH) TG @r (Nat '* XS) ==> Sm Nat.
Proof. intros TG TH XS HG HH; unfold rec_s, hstep, T_pri; cbn; tpsN. Qed.

Lemma type_app_min_s : forall TF X, tp PO @ TF @r (Nat '* X) ==> Sm Nat ->
  tp PO @ min_s T_min ('K1 Nat) (min_pred_s Bool TF Bool) @r X ==> Sm Nat.
Proof.
  intros TF X HF.
  assert (HP : tp PO @ 'wait[min_pred_s Bool TF Bool, X] @r Nat ==> Sm Bool)
    by (unfold min_pred_s; cbn; tpsN).
  pose proof (minimisation_type_app _ HP) as HM.
  unfold min_s; cbn -[T_min min_pred_s]; tpsN.
Qed.

Lemma type_app_tcompile_all :
  (forall n (f : mu_fun n), tp PO @ tycompile f @r nat_tuple (Nat.pred n) ==> Sm Nat) /\
  (forall n m (gs : mu_funs n m), m <> 0 -> tp PO @ tytuple gs @r nat_tuple (Nat.pred n) ==> Sm (nat_tuple (Nat.pred m))).
Proof.
  apply (mu_fun_mutind
    (fun n f => tp PO @ tycompile f @r nat_tuple (Nat.pred n) ==> Sm Nat)
    (fun n m gs => m <> 0 -> tp PO @ tytuple gs @r nat_tuple (Nat.pred n) ==> Sm (nat_tuple (Nat.pred m))));
    cbn [tycompile tytuple Nat.pred]; intros.
  - apply tp_K1_fwd.
  - by_runM.
  - apply type_app_tproj.
  - eapply type_app_comp_prog; [apply H0; discriminate|exact H].
  - apply type_app_rec_s; assumption.
  - apply type_app_min_s; assumption.
  - contradiction.
  - destruct m as [|m]; cbn [Nat.pred nat_tuple].
    + unfold comp_prog; tpsN.
    + apply type_app_pair_at; [exact H|apply H0; discriminate].
Qed.

Lemma type_app_tcompile : forall k (f : mu_fun (S k)), tp PO @ tycompile f @r nat_tuple k ==> Sm Nat.
Proof. intros k f; exact (proj1 type_app_tcompile_all (S k) f). Qed.

(** ** Evaluation *)

Definition upd_of (Bv : Combination) : Combination :=
  'tagged['wait[self_apply, (Bv 'C 'tagger[update_nm]) 'C bz], update_nm].

Lemma rt_update_unfold : forall Bv n v, Bv @ upd_of Bv @r n ==> v -> upd_of Bv @ n ==> v.
Proof.
  intros Bv n v H; unfold upd_of in *; apply tagged_eval, wait_eval.
  pose proof (bz_eval ((Bv 'C 'tagger[update_nm]) 'C bz)) as Hb.
  pose proof (tagger_eval update_nm ('wait[self_apply, (Bv 'C 'tagger[update_nm]) 'C bz])) as Ht.
  ev2. apply self_apply_eval; ev2.
Qed.

Lemma sp_tag_fwd : forall cT f d x v, cT = code (type_of x) -> f @ x ==> v ->
  'tagged['wait3[sp_body, cT, f, d], update_nm] @ x ==> v.
Proof.
  intros cT f d x v E H; apply tagged_eval, sp_fwd.
  destruct (combination_eq_dec cT (code (type_of x))); [exact H|contradiction].
Qed.

Lemma type_of_numeral : forall k, type_of (numeral k) = Nat.
Proof. intros [|k]; reflexivity. Qed.
Lemma type_of_pair : forall x y, type_of (x '* y) = type_of x '* type_of y.
Proof. intros; reflexivity. Qed.

Lemma succ_fn_eval : forall m, succ_fn @ m ==> succ m.
Proof. intros m; unfold succ_fn, mk_nat, succ; ev2. Qed.

Lemma pr_iter_eval : forall g, exists Bv, pr_iter @ g ==> upd_of Bv /\
  forall u, exists St, Bv @ u ==> 'tagged['wait3[sp_body, code NNN, St, identity_update], update_nm] /\
    (forall c a, St @ (zero '* (c '* a)) ==> (zero '* (c '* a))) /\
    (forall m c a b v, g @ (c '* a) ==> b -> u @ (m '* (succ c '* b)) ==> v ->
       St @ (succ m '* (c '* a)) ==> v).
Proof.
  intros g. eexists; split.
  - unfold pr_iter, mk_update, upd_of. ev2.
  - intros u. eexists; split; [unfold mk_update; ev2|].
    split; intros; unfold zero, mk_nat, succ in *; ev2.
Qed.

Lemma minimisation_eval : forall p, exists Bv, minimisation @ p ==> upd_of Bv /\
  forall u, exists Adv, Bv @ u ==> 'tagged['wait3[sp_body, code Nat, Adv, identity_update], update_nm] /\
    (forall n, p @ n ==> tt -> Adv @ n ==> n) /\
    (forall n v, p @ n ==> ff -> u @ succ n ==> v -> Adv @ n ==> v).
Proof.
  intros p. eexists; split.
  - unfold minimisation, mk_update, upd_of. ev2.
  - intros u. eexists; split; [unfold mk_update; ev2|].
    split; intros; unfold tt, ff, mk_nat, succ, identity_update in *; ev2.
Qed.

Lemma nnn_type : forall m c a, type_of (numeral m '* (numeral c '* numeral a)) = NNN.
Proof. intros; rewrite !type_of_pair, !type_of_numeral; reflexivity. Qed.

Lemma upd_step : forall Bv cT St x v, Bv @ upd_of Bv ==> 'tagged['wait3[sp_body, cT, St, identity_update], update_nm] ->
  cT = code (type_of x) -> St @ x ==> v -> upd_of Bv @ x ==> v.
Proof. intros; apply rt_update_unfold; eapply eval_appl; [eassumption|apply sp_tag_fwd; assumption]. Qed.

(** The iteration walks a chain of values [vs]: from count [m] at index [c]
    with accumulator [vs c] it ends at [vs y], when [c + m = y]. *)
Lemma pr_chain : forall g (vs : nat -> nat) y,
  (forall c, c < y -> g @ (numeral c '* numeral (vs c)) ==> numeral (vs (S c))) ->
  forall u, pr_iter @ g ==> u -> forall m c, c + m = y ->
  u @ (numeral m '* (numeral c '* numeral (vs c))) ==> (zero '* (numeral y '* numeral (vs y))).
Proof.
  intros g vs y Hg u Hu.
  destruct (pr_iter_eval g) as [Bv [HB HS]]. pose proof (eval_deterministic _ _ Hu _ HB) as ->.
  destruct (HS (upd_of Bv)) as [St [HSt [H0 H1]]].
  induction m as [|m IH]; intros c Hc.
  - replace c with y by lia. eapply upd_step; [exact HSt|rewrite nnn_type; reflexivity|apply H0].
  - eapply upd_step; [exact HSt|rewrite nnn_type; reflexivity|].
    cbn [numeral]. eapply H1; [apply Hg; lia|]. exact (IH (S c) ltac:(lia)).
Qed.

Lemma hstep_eval : forall H y T c a v, H @ (c '* (a '* T)) ==> v -> 'wait[hstep H, y '* T] @ (c '* a) ==> v.
Proof. intros; apply wait_eval; unfold hstep; cbn; ev2. Qed.

Lemma rec_s_eval : forall G H y T (vs : nat -> nat), G @ T ==> numeral (vs 0) ->
  (forall c, c < y -> H @ (numeral c '* (numeral (vs c) '* T)) ==> numeral (vs (S c))) ->
  rec_s pr_iter zero (hstep H) G @ (numeral y '* T) ==> numeral (vs y).
Proof.
  intros G H y T vs HG HH.
  assert (Hg : forall c, c < y -> 'wait[hstep H, numeral y '* T] @ (numeral c '* numeral (vs c)) ==> numeral (vs (S c)))
    by (intros; apply hstep_eval, HH; assumption).
  destruct (pr_iter_eval ('wait[hstep H, numeral y '* T])) as [Bv [HB _]].
  pose proof (pr_chain _ vs y Hg _ HB y 0 ltac:(lia)) as HC; cbn [numeral] in HC.
  unfold rec_s; cbn -[pr_iter hstep zero]; ev2.
Qed.

Lemma pair_at_eval : forall A B x a b, A @ x ==> a -> B @ x ==> b -> pair_at A B @ x ==> (a '* b).
Proof. intros; unfold pair_at; cbn; ev2. Qed.

Lemma comp_prog_eval : forall H T x t v, T @ x ==> t -> H @ t ==> v -> comp_prog H T @ x ==> v.
Proof. intros; unfold comp_prog; ev2. Qed.

Lemma min_pred_tt : forall F T n, F @ (n '* T) ==> zero -> 'wait[min_pred_s tt F ff, T] @ n ==> tt.
Proof. intros F T n H; apply wait_eval; unfold min_pred_s; cbn; unfold zero, tt, ff in *; ev2. Qed.

Lemma min_pred_ff : forall F T n r, F @ (n '* T) ==> numeral (S r) -> 'wait[min_pred_s tt F ff, T] @ n ==> ff.
Proof. intros F T n r H; apply wait_eval; unfold min_pred_s; cbn [numeral] in H; cbn; unfold succ, tt, ff in *; ev2. Qed.

Lemma minim_found : forall p u n, minimisation @ p ==> u -> p @ numeral n ==> tt -> u @ numeral n ==> numeral n.
Proof.
  intros p u n Hu Hp; destruct (minimisation_eval p) as [Bv [HB HS]].
  pose proof (eval_deterministic _ _ Hu _ HB) as ->.
  destruct (HS (upd_of Bv)) as [Adv [HA [Hf _]]].
  eapply upd_step; [exact HA|rewrite type_of_numeral; reflexivity|apply Hf, Hp].
Qed.

Lemma minim_next : forall p u n v, minimisation @ p ==> u -> p @ numeral n ==> ff ->
  u @ numeral (S n) ==> v -> u @ numeral n ==> v.
Proof.
  intros p u n v Hu Hp Hv; destruct (minimisation_eval p) as [Bv [HB HS]].
  pose proof (eval_deterministic _ _ Hu _ HB) as ->.
  destruct (HS (upd_of Bv)) as [Adv [HA [_ Hn]]].
  eapply upd_step; [exact HA|rewrite type_of_numeral; reflexivity|eapply Hn; [exact Hp|exact Hv]].
Qed.

Lemma min_s_eval : forall F T u v, minimisation @ 'wait[min_pred_s tt F ff, T] ==> u -> u @ zero ==> v ->
  min_s minimisation ('K1 zero) (min_pred_s tt F ff) @ T ==> v.
Proof. intros; unfold min_s; cbn -[minimisation min_pred_s zero]; ev2. Qed.

Lemma snds_eval : forall ys rest, rest <> [] ->
  snds (List.length ys) @ tuple_of (ys ++ rest) ==> tuple_of rest.
Proof.
  induction ys as [|y ys IH]; intros rest Hr; cbn [List.length snds List.app].
  - apply I_eval.
  - rewrite tuple_of_cons by (destruct ys; [exact Hr|discriminate]).
    pose proof (IH rest Hr); ev2.
Qed.

Lemma tproj_eval : forall ys x zs, tproj (List.length ys) (List.length zs) @ tuple_of (ys ++ x :: zs) ==> x.
Proof.
  intros ys x [|z zs]; cbn [List.length tproj].
  - exact (snds_eval ys [x] ltac:(discriminate)).
  - pose proof (snds_eval ys (x :: z :: zs) ltac:(discriminate)) as H.
    rewrite tuple_of_cons in H by discriminate. ev2.
Qed.

(** ** Soundness of the compilation *)

Definition tup (xs : list nat) := tuple_of (List.map numeral xs).

Lemma tup_cons : forall x xs, xs <> [] -> tup (x :: xs) = numeral x '* tup xs.
Proof. intros x [|y ys] H; [contradiction|reflexivity]. Qed.

Definition rec_extra {n} (f : mu_fun n) (xs : list nat) (v : nat) : Prop :=
  match f with
  | mu_rec k g h =>
      match xs with
      | y :: xs' => exists vs : nat -> nat,
          tcompile g @ tup xs' ==> numeral (vs 0) /\ vs y = v /\
          forall c, c < y -> tcompile h @ (numeral c '* (numeral (vs c) '* tup xs'))
                               ==> numeral (vs (S c))
      | [] => True
      end
  | _ => True
  end.

Lemma tcompile_sound_all :
  (forall n f xs v, mu_eval n f xs v ->
     List.length xs = n /\ tcompile f @ tup xs ==> numeral v /\ rec_extra f xs v) /\
  (forall n m gs xs ys, mu_evals n m gs xs ys ->
     List.length ys = m /\ (m = 0 \/ List.length xs = n) /\
     (m <> 0 -> ttuple gs @ tup xs ==> tup ys)) /\
  (forall k f xs z y, mu_search k f xs z y ->
     List.length xs = S k /\
     forall u, minimisation @ 'wait[min_pred_s tt (tcompile f) ff, tup xs] ==> u ->
       u @ numeral z ==> numeral y).
Proof.
  apply (mu_eval_mutind
    (fun n f xs v _ => List.length xs = n /\ tcompile f @ tup xs ==> numeral v /\ rec_extra f xs v)
    (fun n m gs xs ys _ => List.length ys = m /\ (m = 0 \/ List.length xs = n) /\
       (m <> 0 -> ttuple gs @ tup xs ==> tup ys))
    (fun k f xs z y _ => List.length xs = S k /\
       forall u, minimisation @ 'wait[min_pred_s tt (tcompile f) ff, tup xs] ==> u ->
         u @ numeral z ==> numeral y));
    cbn [tcompile ttuple rec_extra].
  - (* zero *)
    intros k xs Hl; repeat split; [exact Hl|unfold zero; evaluate].
  - (* successor *)
    intros x; repeat split; apply succ_fn_eval.
  - (* projection *)
    intros i j ys x zs Hy Hz; repeat split.
    + rewrite length_app; cbn; lia.
    + subst; unfold tup; rewrite List.map_app; cbn [List.map].
      rewrite <- (length_map numeral ys), <- (length_map numeral zs); apply tproj_eval.
  - (* composition *)
    intros k m h gs xs ys v _ [Hm [[Hm0|Hl] Hgs]] _ [_ [Hh _]]; [discriminate|].
    repeat split; [exact Hl|].
    eapply comp_prog_eval; [apply Hgs; discriminate|exact Hh].
  - (* primitive recursion, zero *)
    intros k g h xs v _ [Hl [Hg _]].
    assert (Hne : xs <> []) by (intros ->; discriminate).
    split; [cbn; rewrite Hl; reflexivity|].
    rewrite tup_cons by exact Hne; split.
    + exact (rec_s_eval _ _ 0 _ (fun _ => v) Hg ltac:(intros; lia)).
    + exists (fun _ => v); repeat split; [exact Hg|intros; lia].
  - (* primitive recursion, successor *)
    intros k g h y xs r v _ [Hl [_ [vs [HW [Hvy Hc]]]]] _ [_ [Hh _]].
    cbn [List.length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hh by discriminate; rewrite tup_cons in Hh by exact Hne.
    set (vs' := fun c => if Nat.eqb c (S y) then v else vs c).
    assert (H0 : vs' 0 = vs 0) by reflexivity.
    assert (HSy : vs' (S y) = v) by (unfold vs'; rewrite Nat.eqb_refl; reflexivity).
    assert (Hc' : forall c, c < S y ->
      tcompile h @ (numeral c '* (numeral (vs' c) '* tup xs)) ==> numeral (vs' (S c))).
    { intros c Hlt; unfold vs'.
      destruct (Nat.eqb_spec c (S y)) as [E|E]; [lia|].
      destruct (Nat.eqb_spec (S c) (S y)) as [E'|E'].
      - assert (c = y) by lia; subst c; rewrite Hvy; exact Hh.
      - apply Hc; lia. }
    split; [exact Hl|]; rewrite tup_cons by exact Hne; split.
    + rewrite <- HSy; eapply rec_s_eval; [rewrite H0; exact HW|exact Hc'].
    + exists vs'; repeat split; [rewrite H0; exact HW|exact HSy|exact Hc'].
  - (* minimisation *)
    intros k f xs y _ [Hl Hs]; repeat split; [exact Hl|].
    destruct (minimisation_eval ('wait[min_pred_s tt (tcompile f) ff, tup xs])) as [Bv [HB _]].
    eapply min_s_eval; [exact HB|apply (Hs _ HB)].
  - (* no functions *)
    intros n xs; repeat split; [left; reflexivity|intros H; contradiction].
  - (* one more function *)
    intros n m g gs xs y ys _ [Hl [Hg _]] _ [Hm [_ Hgs]].
    repeat split; [cbn; rewrite Hm; reflexivity|right; exact Hl|]; intros _.
    destruct m as [|m].
    + destruct ys; [|discriminate]; cbn; ev2.
    + destruct ys as [|y' ys]; [discriminate|].
      rewrite tup_cons by discriminate.
      apply pair_at_eval; [exact Hg|apply Hgs; discriminate].
  - (* search succeeds *)
    intros k f xs z _ [Hl [Hf _]].
    cbn [List.length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hf by exact Hne.
    split; [exact Hl'|]. intros u Hu.
    apply (minim_found _ _ _ Hu); apply min_pred_tt; exact Hf.
  - (* search continues *)
    intros k f xs z r y _ [Hl [Hf _]] _ [_ Hs].
    cbn [List.length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hf by exact Hne.
    split; [exact Hl'|]. intros u Hu.
    eapply (minim_next _ _ _ _ Hu); [eapply min_pred_ff; exact Hf|exact (Hs u Hu)].
Qed.

Lemma tcompile_sound : forall n (f : mu_fun n) xs y,
  mu_eval n f xs y -> tcompile f @ tuple_of (List.map numeral xs) ==> numeral y.
Proof. intros n f xs y H; apply (proj1 tcompile_sound_all) in H; tauto. Qed.

(** ** The theorems *)

Lemma infer_numeral_P : forall n, infer PO @ numeral n ==> Sm Nat.
Proof. induction n; cbn [numeral]; [apply paper_infer_zero|apply paper_infer_succ; exact IHn]. Qed.

Lemma infer_tup : forall k xs, List.length xs = S k -> infer PO @ tup xs ==> Sm (nat_tuple k).
Proof.
  intros k; induction k as [|k IH]; intros xs Hl.
  - destruct xs as [|x [|]]; try discriminate; apply infer_numeral_P.
  - destruct xs as [|x xs]; [discriminate|]; injection Hl; intros Hl'.
    rewrite tup_cons by (intros ->; discriminate); cbn [nat_tuple].
    apply pair_typed; [apply infer_numeral_P|apply IH; assumption].
Qed.

Theorem typed_mu_complete : forall k (f : mu_fun (S k)),
  exists P R,
    infer PO @ P ==> Sm R /\
    tp PO @ R @r nat_tuple k ==> Sm Nat /\
    forall xs y, mu_eval (S k) f xs y -> P @ tuple_of (List.map numeral xs) ==> numeral y.
Proof.
  intros k f; exists (tcompile f), (tycompile f); split; [|split].
  - apply infer_tcompile.
  - apply type_app_tcompile.
  - intros; apply tcompile_sound; assumption.
Qed.

Theorem typed_mu_values_are_numbers : forall k (f : mu_fun (S k)) xs v,
  List.length xs = S k -> tcompile f @ tuple_of (List.map numeral xs) ==> v -> infer PO @ v ==> Sm Nat.
Proof.
  intros k f xs v Hl He; eapply (proj2 paper_ontology_typing_sound); [exact He|].
  eapply ie_fork; [apply ie_stem, infer_tcompile|apply ie_stem, infer_tup, Hl|apply type_app_tcompile].
Qed.

(** ** An example: addition [add (y, x) = y + x] by recursion on [y]. *)
Definition mu_add : mu_fun 2 :=
  mu_rec 0 (mu_proj 0 0) (mu_comp 2 0 mu_succ (mu_cons 3 0 (mu_proj 1 1) (mu_nil 3))).
Example mu_add_eval : tcompile mu_add @ (numeral 2 '* numeral 3) ==> numeral 5. Proof. by_runM. Qed.
Example mu_add_typed : infer_expression PO @ (tcompile mu_add @ (numeral 2 '* numeral 3)) ==> Sm Nat. Proof. by_runM. Qed.
