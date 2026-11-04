(** * Every partial mu-recursive function, typed by invariant on [Nat]

    [concrete_is_Turing_complete] (self_typing.v) compiles each partial
    mu-recursive function to a concrete program on raw numerals, whose
    type is itself.  Here each [f : mu_fun (S k)] is compiled to a
    tag-free program [tcompile f] on the abstract numbers [numeral n] of
    data_types.v, taking its arguments as one right-nested tuple.  Its
    type is itself, and type application of that type to
    [nat_tuple k = Nat * ... * Nat] gives [Nat], whether or not [f] is
    total: primitive recursion is a fold whose step type is checked once
    by the [Nat] eliminator, and minimisation is the update [minimisation]
    of dither_minimisation.v, whose type stops at the invariant [Update].

    Construction, by induction on [mu_fun]:
    - zero: [mk_zero]; successor: [succ_step];
    - projection: [snd] repeated, then [fst] unless last;
    - composition: [x |-> H (G1 x * (G2 x * ... Gm x))];
    - primitive recursion: [x = y * xs |-> fst (snd (y @ (B * step)))]
      with [B = zero * (G xs * xs)] and
      [step (c * (r * xs)) = succ c * (H (c * (r * xs)) * xs)];
    - minimisation: [x |-> (minimisation @ wait[pred F, x] @ seek_at zero) @ I]
      with [pred F @ x @ n = is_zero (F (n * x))].

    Abstract subprograms only ever occur in [K1] positions ([S2[K1 G, I]]
    for [x |-> G x]), so the side conditions of type application on [S2]
    (not tagged, not a name test) are decided by the known skeleton. *)

From TreeTyping Require Import tree typing soundness booleans functions data_types.
From TreeTyping Require Import search conditionals queries updates dither_minimisation.
From TreeTyping Require Import paper_ontology self_typing.
From Stdlib Require Import String List Lia Bool.
Import ListNotations.
Open Scope string_scope.

(** ** Tuples *)

Fixpoint nat_tuple (k : nat) : Combination :=
  match k with O => 'Nat | S k => 'Nat '* nat_tuple k end.

Fixpoint tuple_of (xs : list Combination) : Combination :=
  match xs with
  | [] => Lf
  | x :: rest => match rest with [] => x | _ => x '* tuple_of rest end
  end.

Lemma tuple_of_cons : forall x rest, rest <> [] -> tuple_of (x :: rest) = x '* tuple_of rest.
Proof. intros x [|y r] H; [contradiction|reflexivity]. Qed.

(** ** The programs *)

(** [x |-> A x * B x] *)
Definition pair_at (A B : Combination) := Eval cbn in to_tree
  (star "x" ((Val A @@ (Val 'I @@ Ref "x")) ''* (Val B @@ (Val 'I @@ Ref "x")))).

Fixpoint snds (i : nat) : Combination :=
  match i with O => 'I | S i => snds i 'C 'snd end.
Definition tproj (i j : nat) : Combination :=
  match j with O => snds i | S _ => 'fst 'C snds i end.

(** [x |-> H (T x)] *)
Definition comp_prog (H T : Combination) := H 'C (T 'C 'I).

(** Primitive recursion *)
Definition rec_base (G : Combination) := Eval cbn -[mk_zero] in to_tree (star "x"
  ((Val mk_zero @@ Ref "x") ''* ((Val G @@ (Val 'snd @@ Ref "x")) ''* (Val 'snd @@ Ref "x")))).
Definition rec_step (H : Combination) := Eval cbn -[succ_step] in to_tree (star "p"
  ((Val succ_step @@ (Val 'fst @@ Ref "p"))
     ''* ((Val H @@ (Val 'I @@ Ref "p")) ''* (Val 'snd @@ (Val 'snd @@ Ref "p"))))).
Definition rec_tprog (G H : Combination) := Eval cbn -[rec_base rec_step] in to_tree (star "x"
  (Val 'fst @@ (Val 'snd @@ ((Val 'fst @@ Ref "x") @@
     ((Val (rec_base G) @@ Ref "x") ''* Val (rec_step H)))))).

(** Minimisation *)
Definition min_pred (F : Combination) := Eval cbn -[mk_tt mk_ff] in to_tree (star "x" (star "n" (
  (Val F @@ (Ref "n" ''* Ref "x")) @@ ((Val mk_tt @@ Ref "n") ''* (''K1 (Val mk_ff @@ Ref "n")))))).
Definition seek_zero := Eval cbn -[mk_zero] in to_tree (star "x"
  (Val ('tagger[seek_nm]) @@ ''S2[Val 'I, ''K1 (Val mk_zero @@ Ref "x")])).
Definition min_tprog (F : Combination) := Eval cbn -[minimisation seek_zero min_pred] in to_tree (star "x"
  (((Val minimisation @@ ''wait[Val (min_pred F), Ref "x"]) @@ (Val seek_zero @@ Ref "x")) @@ Val 'I)).

Fixpoint tcompile {n} (f : mu_fun n) {struct f} : Combination :=
  match f with
  | mu_zero k => mk_zero
  | mu_succ => succ_step
  | mu_proj i j => tproj i j
  | mu_comp k m h gs => comp_prog (tcompile h) (ttuple gs)
  | mu_rec k g h => rec_tprog (tcompile g) (tcompile h)
  | mu_min k f => min_tprog (tcompile f)
  end
with ttuple {n m} (gs : mu_funs n m) {struct gs} : Combination :=
  match gs with
  | mu_nil _ => 'I
  | mu_cons _ m' g gs' =>
      match m' with O => tcompile g 'C 'I | S _ => pair_at (tcompile g) (ttuple gs') end
  end.

(** ** Tag-freeness *)

Lemma tag_free_minimisation : tag_free minimisation = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tag_free_seek_zero : tag_free seek_zero = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tag_free_mk_zero : tag_free mk_zero = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tag_free_mk_tt : tag_free mk_tt = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tag_free_mk_ff : tag_free mk_ff = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tag_free_succ_step : tag_free succ_step = true.
Proof. vm_compute; reflexivity. Qed.

Ltac cb_tac :=
  cbn -[minimisation seek_zero mk_zero mk_tt mk_ff succ_step];
  repeat (rewrite ?tag_free_minimisation, ?tag_free_seek_zero, ?tag_free_mk_zero,
            ?tag_free_mk_tt, ?tag_free_mk_ff, ?tag_free_succ_step;
          cbn -[minimisation seek_zero mk_zero mk_tt mk_ff succ_step]);
  repeat match goal with H : tag_free _ = true |- _ => rewrite H; cbn end;
  try reflexivity.

Lemma tag_free_pair_at : forall A B, tag_free A = true -> tag_free B = true ->
  tag_free (pair_at A B) = true.
Proof. intros A B HA HB; unfold pair_at; cb_tac. Qed.
Lemma tag_free_snds : forall i, tag_free (snds i) = true.
Proof. induction i; cbn [snds]; [reflexivity|]; cb_tac. Qed.
Lemma tag_free_tproj : forall i j, tag_free (tproj i j) = true.
Proof.
  intros i [|j]; cbn [tproj]; [apply tag_free_snds|].
  destruct i; cbn [snds]; [reflexivity|]; pose proof (tag_free_snds i); cb_tac.
Qed.
Lemma tag_free_comp_prog : forall H T, tag_free H = true -> tag_free T = true ->
  tag_free (comp_prog H T) = true.
Proof. intros; unfold comp_prog; cb_tac. Qed.
Lemma tag_free_rec_tprog : forall G H, tag_free G = true -> tag_free H = true ->
  tag_free (rec_tprog G H) = true.
Proof. intros; unfold rec_tprog, rec_base, rec_step; cb_tac. Qed.
Lemma tag_free_min_tprog : forall F, tag_free F = true -> tag_free (min_tprog F) = true.
Proof. intros; unfold min_tprog, min_pred; cb_tac. Qed.

Lemma tcompile_tag_free_all :
  (forall n (f : mu_fun n), tag_free (tcompile f) = true) /\
  (forall n m (gs : mu_funs n m), tag_free (ttuple gs) = true).
Proof.
  apply (mu_fun_mutind (fun n f => tag_free (tcompile f) = true)
                       (fun n m gs => tag_free (ttuple gs) = true));
    cbn [tcompile ttuple]; intros.
  - apply tag_free_mk_zero.
  - apply tag_free_succ_step.
  - apply tag_free_tproj.
  - apply tag_free_comp_prog; assumption.
  - apply tag_free_rec_tprog; assumption.
  - apply tag_free_min_tprog; assumption.
  - reflexivity.
  - destruct m; [cb_tac|apply tag_free_pair_at; assumption].
Qed.

Lemma tcompile_tag_free : forall n (f : mu_fun n), tag_free (tcompile f) = true.
Proof. intros; apply (proj1 tcompile_tag_free_all). Qed.

Lemma infer_tcompile : forall (AI : Decl) n (f : mu_fun n),
  infer AI @ tcompile f ==> Sm (tcompile f).
Proof. intros; apply infer_tag_free, tcompile_tag_free. Qed.

(** ** Typing *)

Section Typing.
Variable AI : Decl.
Hypothesis HK : supports_seek AI.
Hypothesis HU : supports_updates AI.
Hypothesis HT : supports_is_named AI.
Hypothesis HB : supports_booleans AI.
Hypothesis HN : supports_number AI.

Local Ltac ty_onto_more ::= first [ apply supports_seek_abstractor; exact HK ].
Local Ltac ty_elim_more ::= first [apply payload_eliminator_some | apply update_eliminator_eval].

Lemma type_app_snd_pair : forall A B, type_app AI @ 'snd @r (A '* B) ==> Sm B.
Proof. intros; repeat ty. Qed.
Lemma type_app_fst_pair : forall A B, type_app AI @ 'fst @r (A '* B) ==> Sm A.
Proof. intros; repeat ty. Qed.

Lemma type_app_snds : forall i j,
  type_app AI @ snds i @r nat_tuple (i + j) ==> Sm (nat_tuple j).
Proof.
  induction i as [|i IH]; intros j; cbn [snds Nat.add nat_tuple].
  - apply type_app_I.
  - pose proof (type_app_snd_pair ('Nat) (nat_tuple (i + j))).
    pose proof (IH j). repeat ty.
Qed.

Lemma type_app_tproj : forall i j,
  type_app AI @ tproj i j @r nat_tuple (i + j) ==> Sm ('Nat).
Proof.
  intros i [|j]; cbn [tproj].
  - exact (type_app_snds i 0).
  - pose proof (type_app_snds i (S j)) as Hs; cbn [nat_tuple] in Hs.
    pose proof (type_app_fst_pair ('Nat) (nat_tuple j)).
    destruct i; cbn [snds] in *; repeat ty.
Qed.

Lemma type_app_pair_at : forall A B X VA VB,
  type_app AI @ A @r X ==> Sm VA -> type_app AI @ B @r X ==> Sm VB ->
  type_app AI @ pair_at A B @r X ==> Sm (VA '* VB).
Proof. intros; unfold pair_at; repeat ty. Qed.

Lemma type_app_comp_prog : forall H T X V R,
  type_app AI @ T @r X ==> Sm V -> type_app AI @ H @r V ==> R ->
  type_app AI @ comp_prog H T @r X ==> R.
Proof. intros; unfold comp_prog; repeat ty. Qed.

Lemma type_app_rec_step : forall H XS,
  type_app AI @ H @r ('Nat '* ('Nat '* XS)) ==> Sm ('Nat) ->
  type_app AI @ rec_step H @r ('Nat '* ('Nat '* XS)) ==> Sm ('Nat '* ('Nat '* XS)).
Proof.
  intros; pose proof (type_app_succ_step AI HN); unfold rec_step; repeat ty.
Qed.

Lemma type_app_rec_base : forall G XS,
  type_app AI @ G @r XS ==> Sm ('Nat) ->
  type_app AI @ rec_base G @r ('Nat '* XS) ==> Sm ('Nat '* ('Nat '* XS)).
Proof. intros; unfold rec_base; repeat ty. Qed.

Lemma type_app_rec_tprog : forall G H XS,
  type_app AI @ G @r XS ==> Sm ('Nat) ->
  type_app AI @ H @r ('Nat '* ('Nat '* XS)) ==> Sm ('Nat) ->
  type_app AI @ rec_tprog G H @r ('Nat '* XS) ==> Sm ('Nat).
Proof.
  intros G H XS HG HH.
  pose proof (type_app_rec_base G XS HG); pose proof (type_app_rec_step H XS HH).
  unfold rec_tprog; repeat ty.
Qed.

Lemma type_app_min_pred : forall F X,
  type_app AI @ F @r ('Nat '* X) ==> Sm ('Nat) ->
  type_app AI @ 'wait[min_pred F, X] @r ('Nat) ==> Sm ('Bool).
Proof. intros; eapply type_app_wait; unfold min_pred; repeat ty. Qed.

Lemma type_app_seek_zero : forall X, type_app AI @ seek_zero @r X ==> Sm ('Seek).
Proof. intros; unfold seek_zero; repeat ty. Qed.

(** Stage 1: minimisation at a parameter [F]. *)
Lemma type_app_min_tprog : forall F X,
  type_app AI @ F @r ('Nat '* X) ==> Sm ('Nat) ->
  type_app AI @ min_tprog F @r X ==> Sm ('Nat).
Proof.
  intros F X HF.
  pose proof (type_app_min_pred F X HF) as HP.
  pose proof (proj2 (minimisation_polymorphic AI _ HK HU HT HB HN HP)) as HM.
  pose proof (type_app_seek_zero X) as HS.
  unfold min_tprog; repeat first [apply HM | apply HS | ty].
Qed.

Lemma type_app_tcompile_all :
  (forall n (f : mu_fun n),
     type_app AI @ tcompile f @r nat_tuple (pred n) ==> Sm ('Nat)) /\
  (forall n m (gs : mu_funs n m), m <> 0 ->
     type_app AI @ ttuple gs @r nat_tuple (pred n) ==> Sm (nat_tuple (pred m))).
Proof.
  apply (mu_fun_mutind
    (fun n f => type_app AI @ tcompile f @r nat_tuple (pred n) ==> Sm ('Nat))
    (fun n m gs => m <> 0 ->
       type_app AI @ ttuple gs @r nat_tuple (pred n) ==> Sm (nat_tuple (pred m))));
    cbn [tcompile ttuple pred]; intros.
  - unfold mk_zero; repeat ty.
  - apply type_app_succ_step; exact HN.
  - apply type_app_tproj.
  - eapply type_app_comp_prog; [apply H0; discriminate|exact H].
  - apply type_app_rec_tprog; assumption.
  - apply type_app_min_tprog; assumption.
  - contradiction.
  - destruct m as [|m]; cbn [pred nat_tuple].
    + repeat ty.
    + apply type_app_pair_at; [exact H|apply H0; discriminate].
Qed.

Lemma type_app_tcompile : forall k (f : mu_fun (S k)),
  type_app AI @ tcompile f @r nat_tuple k ==> Sm ('Nat).
Proof. intros k f; exact (proj1 type_app_tcompile_all (S k) f). Qed.
End Typing.

(** ** Evaluation *)

Lemma snds_eval : forall ys rest, rest <> [] ->
  snds (length ys) @ tuple_of (ys ++ rest) ==> tuple_of rest.
Proof.
  induction ys as [|y ys IH]; intros rest Hr; cbn [length snds app].
  - evaluate.
  - rewrite tuple_of_cons by (destruct ys; [exact Hr|discriminate]).
    pose proof (IH rest Hr); d_eval.
Qed.

Lemma tproj_eval : forall ys x zs,
  tproj (length ys) (length zs) @ tuple_of (ys ++ x :: zs) ==> x.
Proof.
  intros ys x [|z zs]; cbn [length tproj].
  - exact (snds_eval ys [x] ltac:(discriminate)).
  - pose proof (snds_eval ys (x :: z :: zs) ltac:(discriminate)) as H.
    rewrite tuple_of_cons in H by discriminate. d_eval.
Qed.

Lemma pair_at_eval : forall A B x a b, A @ x ==> a -> B @ x ==> b ->
  pair_at A B @ x ==> (a '* b).
Proof. intros; unfold pair_at; d_eval. Qed.

Lemma comp_prog_eval : forall H T x t v, T @ x ==> t -> H @ t ==> v ->
  comp_prog H T @ x ==> v.
Proof. intros; unfold comp_prog; d_eval. Qed.

Lemma rec_base_eval : forall G Y T W, G @ T ==> W ->
  rec_base G @ (Y '* T) ==> (zero '* (W '* T)).
Proof. intros; pose proof (mk_zero_eval (Y '* T)); unfold rec_base; d_eval. Qed.

Lemma rec_step_eval : forall H c r T v, H @ (c '* (r '* T)) ==> v ->
  rec_step H @ (c '* (r '* T)) ==> (succ c '* (v '* T)).
Proof. intros; pose proof (succ_step_eval c); unfold rec_step; d_eval. Qed.

Lemma rec_tprog_eval : forall G H Y T B Y' V T',
  rec_base G @ (Y '* T) ==> B ->
  Y @ (B '* rec_step H) ==> (Y' '* (V '* T')) ->
  rec_tprog G H @ (Y '* T) ==> V.
Proof. intros; unfold rec_tprog; d_eval. Qed.

Lemma min_pred_tt : forall F T n, F @ (n '* T) ==> zero ->
  'wait[min_pred F, T] @ n ==> 'tt.
Proof.
  intros F T n H; pose proof (mk_tt_eval n); pose proof (mk_ff_eval n).
  pose proof (zero_apply ('tt) ('K1 'ff)).
  apply wait_eval; unfold min_pred; d_eval.
Qed.

Lemma min_pred_ff : forall F T n r, F @ (n '* T) ==> numeral (S r) ->
  'wait[min_pred F, T] @ n ==> 'ff.
Proof.
  intros F T n r H; pose proof (mk_tt_eval n); pose proof (mk_ff_eval n).
  pose proof (numeral_K1_fold r ('tt) ('ff)).
  apply wait_eval; unfold min_pred; d_eval.
Qed.

Lemma seek_zero_eval : forall x, seek_zero @ x ==> seek_at zero.
Proof. intros; pose proof (mk_zero_eval x); unfold seek_zero, seek_at, wrap, zero; d_eval. Qed.

Lemma seek_at_unwrap : forall n, seek_at n @ 'I ==> n.
Proof. intros; unfold seek_at, wrap; apply tagged_eval; evaluate. Qed.

Lemma min_tprog_eval : forall F T n,
  minimisation @ 'wait[min_pred F, T] @r seek_at zero ==> seek_at n ->
  min_tprog F @ T ==> n.
Proof.
  intros F T n H; destruct (eval_pair_inv _ _ _ H) as [w [c [Hw [Hc Hv]]]]; inv_out Hc.
  pose proof (seek_zero_eval T); pose proof (seek_at_unwrap n).
  unfold min_tprog; d_eval.
Qed.

(** ** Soundness of the compilation

    For primitive recursion the motive also records the state of the fold,
    [y @ ((zero * (W * xs)) * step) = y * (v * xs)]. *)
Definition tup (xs : list nat) := tuple_of (map numeral xs).

Definition rec_extra {n} (f : mu_fun n) (xs : list nat) (v : nat) : Prop :=
  match f with
  | mu_rec k g h =>
      match xs with
      | y :: xs' => exists W, tcompile g @ tup xs' ==> W /\
          numeral y @ ((zero '* (W '* tup xs')) '* rec_step (tcompile h))
            ==> (numeral y '* (numeral v '* tup xs'))
      | [] => True
      end
  | _ => True
  end.

Lemma tup_cons : forall x xs, xs <> [] -> tup (x :: xs) = numeral x '* tup xs.
Proof. intros x [|y ys] H; [contradiction|reflexivity]. Qed.

Lemma tcompile_sound_all :
  (forall n f xs v, mu_eval n f xs v ->
     length xs = n /\ tcompile f @ tup xs ==> numeral v /\ rec_extra f xs v) /\
  (forall n m gs xs ys, mu_evals n m gs xs ys ->
     length ys = m /\ (m = 0 \/ length xs = n) /\
     (m <> 0 -> ttuple gs @ tup xs ==> tup ys)) /\
  (forall k f xs z y, mu_search k f xs z y ->
     length xs = S k /\
     minimisation @ 'wait[min_pred (tcompile f), tup xs] @r seek_at (numeral z)
       ==> seek_at (numeral y)).
Proof.
  apply (mu_eval_mutind
    (fun n f xs v _ => length xs = n /\ tcompile f @ tup xs ==> numeral v /\ rec_extra f xs v)
    (fun n m gs xs ys _ => length ys = m /\ (m = 0 \/ length xs = n) /\
       (m <> 0 -> ttuple gs @ tup xs ==> tup ys))
    (fun k f xs z y _ => length xs = S k /\
       minimisation @ 'wait[min_pred (tcompile f), tup xs] @r seek_at (numeral z)
         ==> seek_at (numeral y)));
    cbn [tcompile ttuple rec_extra].
  - (* zero *)
    intros k xs Hl; repeat split; [exact Hl|apply mk_zero_eval].
  - (* successor *)
    intros x; repeat split; apply succ_step_eval.
  - (* projection *)
    intros i j ys x zs Hy Hz; repeat split.
    + rewrite length_app; cbn; lia.
    + subst; unfold tup; rewrite map_app; cbn [map].
      rewrite <- (length_map numeral ys), <- (length_map numeral zs); apply tproj_eval.
  - (* composition *)
    intros k m h gs xs ys v _ [Hm [[Hm0|Hl] Hgs]] _ [_ [Hh _]]; [discriminate|].
    repeat split; [exact Hl|].
    eapply comp_prog_eval; [apply Hgs; discriminate|exact Hh].
  - (* primitive recursion, zero *)
    intros k g h xs v _ [Hl [Hg _]].
    assert (Hne : xs <> []) by (intros ->; discriminate).
    split; [cbn; rewrite Hl; reflexivity|].
    rewrite tup_cons by exact Hne.
    split.
    + eapply rec_tprog_eval; [apply rec_base_eval; exact Hg|apply zero_apply].
    + exists (numeral v); split; [exact Hg|apply zero_apply].
  - (* primitive recursion, successor *)
    intros k g h y xs r v _ [Hl [_ [W [HW Hf]]]] _ [_ [Hh _]].
    cbn [length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hh by discriminate; rewrite tup_cons in Hh by exact Hne.
    assert (HF : numeral (S y) @ ((zero '* (W '* tup xs)) '* rec_step (tcompile h))
                  ==> (numeral (S y) '* (numeral v '* tup xs)))
      by (cbn [numeral]; eapply succ_apply; [exact Hf|apply rec_step_eval; exact Hh]).
    split; [exact Hl|]; rewrite tup_cons by exact Hne; split.
    + eapply rec_tprog_eval; [apply rec_base_eval; exact HW|exact HF].
    + exists W; split; [exact HW|exact HF].
  - (* minimisation *)
    intros k f xs y _ [Hl Hs]; repeat split; [exact Hl|].
    apply min_tprog_eval; exact Hs.
  - (* no functions *)
    intros n xs; repeat split; [left; reflexivity|intros H; contradiction].
  - (* one more function *)
    intros n m g gs xs y ys _ [Hl [Hg _]] _ [Hm [_ Hgs]].
    repeat split; [cbn; rewrite Hm; reflexivity|right; exact Hl|]; intros _.
    destruct m as [|m].
    + destruct ys; [|discriminate]; cbn; d_eval.
    + destruct ys as [|y' ys]; [discriminate|].
      rewrite tup_cons by discriminate.
      apply pair_at_eval; [exact Hg|apply Hgs; discriminate].
  - (* search succeeds *)
    intros k f xs z _ [Hl [Hf _]].
    cbn [length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hf by exact Hne.
    split; [exact Hl'|].
    apply minimisation_found; apply min_pred_tt; exact Hf.
  - (* search continues *)
    intros k f xs z r y _ [Hl [Hf _]] _ [_ Hs].
    cbn [length] in Hl; injection Hl; intros Hl'.
    assert (Hne : xs <> []) by (intros ->; discriminate).
    rewrite tup_cons in Hf by exact Hne.
    split; [exact Hl'|].
    eapply minimisation_next; [eapply min_pred_ff; exact Hf|exact Hs].
Qed.

Lemma tcompile_sound : forall n (f : mu_fun n) xs y,
  mu_eval n f xs y -> tcompile f @ tuple_of (map numeral xs) ==> numeral y.
Proof. intros n f xs y H; apply (proj1 tcompile_sound_all) in H; tauto. Qed.

(** ** The theorem *)

(** For any declarations supporting the types used: each partial
    mu-recursive function has a program [P] whose type [R] (here [P]
    itself) takes [Nat^(k+1)] to [Nat] by type application, and which
    computes the function on numerals wherever it is defined. *)
Theorem typed_mu_complete_at : forall (AI : Decl),
  supports_seek AI -> supports_updates AI -> supports_is_named AI ->
  supports_booleans AI -> supports_number AI ->
  forall k (f : mu_fun (S k)),
  exists P R,
    infer AI @ P ==> Sm R /\
    type_app AI @ R @r nat_tuple k ==> Sm ('Nat) /\
    forall xs y, mu_eval (S k) f xs y -> P @ tuple_of (map numeral xs) ==> numeral y.
Proof.
  intros AI HK HU HT HB HN k f; exists (tcompile f), (tcompile f); split; [|split].
  - apply infer_tcompile.
  - apply type_app_tcompile; assumption.
  - intros; apply tcompile_sound; assumption.
Qed.

Theorem typed_mu_complete : forall k (f : mu_fun (S k)),
  exists P R,
    infer paper_ontology @ P ==> Sm R /\
    type_app paper_ontology @ R @r nat_tuple k ==> Sm ('Nat) /\
    forall xs y, mu_eval (S k) f xs y -> P @ tuple_of (map numeral xs) ==> numeral y.
Proof.
  apply typed_mu_complete_at;
    [apply paper_ontology_supports_seek|apply paper_ontology_supports_updates
    |apply paper_ontology_supports_is_named|apply paper_ontology_supports_booleans
    |apply paper_ontology_supports_number].
Qed.

(** ** Every value is a number

    Evaluation preserves typing, so whatever [tcompile f] returns on a
    tuple of numerals has type [Nat], at every argument, defined or not. *)
Lemma infer_tup : forall (AI : Decl) k xs, supports_number AI -> length xs = S k ->
  infer AI @ tup xs ==> Sm (nat_tuple k).
Proof.
  intros AI k; induction k as [|k IH]; intros xs HN Hl.
  - destruct xs as [|x [|]]; try discriminate; apply numeral_typed; exact HN.
  - destruct xs as [|x xs]; [discriminate|]; injection Hl; intros Hl'.
    rewrite tup_cons by (intros ->; discriminate); cbn [nat_tuple].
    apply infer_product_value; [apply numeral_typed; exact HN|apply IH; assumption].
Qed.

Theorem typed_mu_values_are_numbers : forall k (f : mu_fun (S k)) xs v,
  length xs = S k -> tcompile f @ tuple_of (map numeral xs) ==> v ->
  infer paper_ontology @ v ==> Sm ('Nat).
Proof.
  intros k f xs v Hl He; eapply paper_evaluation_preserves_typing; [exact He|].
  eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_tcompile.
  - apply infer_expression_stem; apply infer_tup;
      [apply paper_ontology_supports_number|exact Hl].
  - apply type_app_tcompile;
      [apply paper_ontology_supports_seek|apply paper_ontology_supports_updates
      |apply paper_ontology_supports_is_named|apply paper_ontology_supports_booleans
      |apply paper_ontology_supports_number].
Qed.

(** ** Examples and sizes *)

(** [add (y, x) = y + x] by recursion on [y]. *)
Definition mu_add : mu_fun 2 :=
  mu_rec 0 (mu_proj 0 0) (mu_comp 2 0 mu_succ (mu_cons 3 0 (mu_proj 1 1) (mu_nil 3))).
(** [pred1 (y, d) = y - 1]; [sub (z, x) = x - z]; [mu_min sub] at [x] is [x]. *)
Definition mu_pred1 : mu_fun 2 := mu_rec 0 (mu_zero 0) (mu_proj 0 2).
Definition mu_sub : mu_fun 2 :=
  mu_rec 0 (mu_proj 0 0)
    (mu_comp 2 1 mu_pred1 (mu_cons 3 1 (mu_proj 1 1) (mu_cons 3 0 (mu_proj 1 1) (mu_nil 3)))).
Definition mu_search_sub : mu_fun 1 := mu_min 0 mu_sub.

Eval vm_compute in (tree_size (tcompile mu_add), tree_size (compile mu_add),
  tree_size (tcompile mu_sub), tree_size (compile mu_sub),
  tree_size (tcompile mu_search_sub), tree_size (compile mu_search_sub),
  tree_size minimisation, tree_size add).

