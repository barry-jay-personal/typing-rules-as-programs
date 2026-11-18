(** * Step 82, stage 7, part 1: arrays with codes and lengths in their names.

    [Array A n = label[array_tag[code A, n]]], [array_tag[c,n] = Fk array_nm (Fk c n)],
    for an index [n = Sm^k Lf] (concrete, so self-typed):

      empty[A]          = tagged[fst, array_tag[code A, Lf]]          empty @ (u*f) = u
      prepend[A,n,x,xs] = tagged[S2[snd, K1 (x*xs)], array_tag[code A, Sm n]]
                                                                   prepend @ (u*f) = f @ (x*xs)

    The declaration at [Fk array_nm r] (A = decode (left_of r), the length
    [right_of r]):
      guard  at length Lf admits fst;
             at length Sm k admits S2[snd, K1 (A * Array'[k])],
             Array'[k] = label[Fk array_nm (Fk (left_of r) k)]
      elim   at length Lf:   Array # (U * F) = Sm U
             at length Sm k: Array # (U * F) = F # (A * Array'[k])
    The eliminator needs no agreement between the branches: the length
    chooses the branch.

    Generic constructors (rows), with run-time codes:
      gen_empty   @ c              = tagged[fst, Fk array_nm (Fk c Lf)]
      gen_prepend @ (c * (x * xs)) = tagged[S2[snd, K1 (x*xs)], Fk array_nm (Fk c (Sm m))]
    where [m] is read from the name of the tail [xs] (a typed array is a tag
    whose name holds its length).  Their eliminators:
      gen_empty   # C               = Sm (Array A Lf)        (C concrete, A = decode C)
      gen_prepend # (C * (X * L))   = Sm Array'[Sm m]        (C concrete, A = decode C,
                                       X = A, L = label[Fk array_nm (Fk C m)])

    Stage 8: the family [arr_fam] and the rows [gen_prepend], [gen_empty]
    are declared in [paper_ontology] (paper_ontology.v), which imports this
    file; the declarations here are sound in any ontology that gives them. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition array_nm : Combination := Nat.iter 24 Sm Lf.
Definition gen_prepend_nm : Combination := Nat.iter 25 Sm Lf.
Definition gen_empty_nm : Combination := Nat.iter 29 Sm Lf.

Definition array_tag (c n : Combination) : Combination := Fk array_nm (Fk c n).
Definition Array (A n : Combination) : Combination := 'label[array_tag (code A) n].
Definition empty (A : Combination) : Combination := 'tagged['fst, array_tag (code A) Lf].
Definition prepend (A n x xs : Combination) : Combination :=
  'tagged['S2['snd, 'K1 (x '* xs)], array_tag (code A) (Sm n)].

(** Indices. *)
Fixpoint idx (k : nat) : Combination := match k with O => Lf | S k => Sm (idx k) end.
Lemma idx_concrete : forall k, concreteb (idx k) = true.
Proof. induction k; cbn; auto. Qed.

(** Run-time terms for names and labels. *)
Definition AT (c m : Term) : Term := Val Lf @@ Val array_nm @@ (Val Lf @@ c @@ m).
Definition AL (c m : Term) : Term := lab (AT c m).

(** ** The declaration *)

Definition ag_prog : Combination := Eval cbn -[equal decode_p get_l get_r array_nm] in to_tree
  (star "r" (star "C"
    (''onStem1 (star "A"
        (''triage[op equal @@ Ref "C" @@ Val 'fst,
                  star "k" (op equal @@ Ref "C" @@ ''S2[Val 'snd, ''K1 (Ref "A" ''* AL (pl (Ref "r")) (Ref "k"))]),
                  Val ('K1 ('K1 'KI))]
           @@ pr (Ref "r")))
       @@ (op decode_p @@ pl (Ref "r"))))).

(** The step of the eliminator, by the length [m]. *)
Definition ae_step : Combination := Eval cbn -[get_l get_r get_s array_nm] in to_tree
  (star "a" (star "A" (star "c" (star "U2" (star "m"
    (''triage[Val Lf @@ PN (Ref "U2"),
              star "k" (''wait[Ref "a", PS (Ref "U2")] @@ (Ref "A" ''* AL (Ref "c") (Ref "k"))),
              Val ('K1 ('K1 Lf))]
       @@ Ref "m")))))).

Definition ae_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s ae_step] in to_tree
  (star "r" (star "n" (star "a" (star "U"
    (''onStem1 (star "A"
        (op equal @@ Ref "U" @@ (PN (Ref "U") ''* PS (Ref "U"))
           @@ star "U2" (op ae_step @@ Ref "a" @@ Ref "A" @@ pl (Ref "r") @@ Ref "U2" @@ pr (Ref "r"))
           @@ Val ('K1 Lf) @@ Ref "U"))
       @@ (op decode_p @@ pl (Ref "r"))))))).

Definition array_guard (r : Combination) : Combination := 'wait[ag_prog, r].
Definition array_elim : Combination := name_elim ae_prog.
Definition D_array (r : Combination) : Combination := array_guard r '* array_elim.

Definition array_entry : Combination := Eval cbn -[get_par array_nm array_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (Val Lf @@ (''wait[Val ag_prog, Ref "r"] ''* Val array_elim)))
       @@ (op (get_par array_nm) @@ Ref "n")))).
Definition arr_fam : Combination := alt array_entry no_rows.

(** ** The generic constructors *)

(** The length in the name of a tagged array: [xs = tagged[f, Fk array_nm (Fk c m)]]. *)
Definition len_t (xs : Term) : Term := pr (pr (pr (pr (pr xs)))).

Definition gemp_carrier : Combination := Eval cbn -[array_nm] in to_tree
  (star "c" (tagger_t (AT (Ref "c") (Val Lf)) @@ Val 'fst)).
Definition gpre_carrier : Combination := Eval cbn -[array_nm get_r] in to_tree
  (star "q" (tagger_t (AT (Val 'fst @@ Ref "q") (Val Lf @@ len_t (Val 'snd @@ (Val 'snd @@ Ref "q"))))
               @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ (Val 'snd @@ Ref "q"))))).

Definition gen_empty : Combination := 'tagged[gemp_carrier, gen_empty_nm].
Definition gen_prepend : Combination := 'tagged[gpre_carrier, gen_prepend_nm].

(** elim at gemp: [U = C] *)
Definition gee_prog : Combination := Eval cbn -[decode_p is_concrete array_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ Ref "U"
       @@ star "U2" (''onStem1 (star "A" (Val Lf @@ AL (Ref "U2") (Val Lf))) @@ (op decode_p @@ Ref "U2"))
       @@ Val ('K1 Lf) @@ Ref "U")))).

(** elim at gpre: [U = C * (X * L)], L's length read from its name. *)
Definition LM (U : Term) : Term := pr (pr (pr (pr (PS (PS U))))).
Definition gpe_prog : Combination := Eval cbn -[equal decode_p is_concrete get_l get_r get_s array_nm] in to_tree
  (star "n" (star "a" (star "U"
    (op is_concrete @@ PN (Ref "U")
       @@ star "U2" (''onStem1 (star "A"
             (op equal @@ Ref "U2" @@ (PN (Ref "U2") ''* (Ref "A" ''* AL (PN (Ref "U2")) (LM (Ref "U2"))))
                @@ (Val Lf @@ AL (PN (Ref "U2")) (Val Lf @@ LM (Ref "U2"))) @@ Val Lf))
           @@ (op decode_p @@ PN (Ref "U2")))
       @@ Val ('K1 Lf) @@ Ref "U")))).

Definition D_gemp : Combination := guard1 gemp_carrier '* gee_prog.
Definition D_gpre : Combination := guard1 gpre_carrier '* gpe_prog.


(** ** Inversions and hits of the declaration programs *)

Local Opaque ag_prog ae_prog ae_step gee_prog gpe_prog.

Definition AN (c k : Combination) : Combination := 'label[Fk array_nm (Fk c k)].

Lemma ag_inv : forall r C, array_guard r @ C ==> 'K ->
  exists A, decode (left_of r) = Some A /\
    ((right_of r = Lf /\ C = 'fst) \/
     (exists k, right_of r = Sm k /\ C = 'S2['snd, 'K1 (A '* AN (left_of r) k)])).
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent ag_prog. unfold ag_prog in H. Local Opaque ag_prog.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as Hd.
  destruct (decode (left_of r)) as [A|]; cbn [opt] in Hd; [|crunch].
  exists A; split; [reflexivity|].
  destruct (right_of r) as [|k|x y] eqn:Er.
  - left; split; [reflexivity|].
    pose proof (equal_bt C 'fst) as E1.
    destruct (combination_eq_dec C 'fst) as [?|Hne]; [assumption|]. cbn [bt] in E1. crunch.
  - right; exists k; split; [reflexivity|].
    pose proof (equal_bt C ('S2['snd, 'K1 (A '* AN (left_of r) k)])) as E1. unfold AN in *.
    destruct (combination_eq_dec C ('S2['snd, 'K1 (A '* 'label[Fk array_nm (Fk (left_of r) k)])])) as [?|Hne]; [assumption|].
    cbn [bt] in E1. crunch.
  - crunch.
Qed.

Lemma ag_hit_leaf : forall A, array_guard (Fk (code A) Lf) @ 'fst ==> 'K.
Proof.
  intros A; apply wait_eval. Local Transparent ag_prog. unfold ag_prog. Local Opaque ag_prog.
  pose proof (get_l_spec (Fk (code A) Lf)) as Hl; pose proof (get_r_spec (Fk (code A) Lf)) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_code A) as Hd. pose proof (equal_eq 'fst) as He. ev2.
Qed.

Lemma ag_hit_succ : forall A c k, decode c = Some A ->
  array_guard (Fk c (Sm k)) @ 'S2['snd, 'K1 (A '* AN c k)] ==> 'K.
Proof.
  intros A c k HA; apply wait_eval. Local Transparent ag_prog. unfold ag_prog. Local Opaque ag_prog.
  pose proof (get_l_spec (Fk c (Sm k))) as Hl; pose proof (get_r_spec (Fk c (Sm k))) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_eval c) as Hd; rewrite HA in Hd; cbn [opt] in Hd.
  pose proof (equal_eq ('S2['snd, 'K1 (A '* AN c k)])) as He.
  pose proof (equal_bt ('S2['snd, 'K1 (A '* AN c k)]) 'fst) as He0. unfold AN in He, He0. ev2.
Qed.

Lemma ae_step_inv : forall a A c U2 m V, ae_step @ a @r A @r c @r U2 @r m ==> Sm V ->
  (m = Lf /\ V = right_of (right_of (stem_of (left_of U2))) \/ False) \/
  (exists k, m = Sm k /\ a @ right_of (right_of U2) @r (A '* AN c k) ==> Sm V).
Proof.
  intros a A c U2 m V H. Local Transparent ae_step. unfold ae_step in H. Local Opaque ae_step.
  destruct m as [|k|x y]; crunch; use_specs; crunch; use_specs; try discriminate.
  all: first [left; left; split; [reflexivity|cbn; reflexivity]
             | right; eexists; split; [reflexivity|]; unfold AN; eapply eval_appl; eassumption
             | idtac].
Qed.

Lemma ae_inv : forall r n a U V, 'wait[ae_prog, r] @ n @r a @r U ==> Sm V ->
  exists A B S, decode (left_of r) = Some A /\ U = B '* S /\
    ((right_of r = Lf /\ V = B) \/
     (exists k, right_of r = Sm k /\ a @ S @r (A '* AN (left_of r) k) ==> Sm V)).
Proof.
  intros r n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent ae_prog. unfold ae_prog in Hp1. Local Opaque ae_prog.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as Hd.
  destruct (decode (left_of r)) as [A|]; cbn [opt] in Hd; [|crunch].
  crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs; try discriminate.
  match goal with H1 : ae_step @ a ==> ?w1, H2 : ?w1 @ ?A ==> ?w2, H3 : ?w2 @ ?c ==> ?w3,
                   H4 : ?w3 @ ?U ==> ?w4, H5 : ?w4 @ ?m ==> Sm V |- _ =>
    assert (Hs : ae_step @ a @r A @r c @r U @r m ==> Sm V)
      by (eapply eval_appl; [eapply eval_appl; [eapply eval_appl; [eapply eval_appl; [exact H1|exact H2]|exact H3]|exact H4]|exact H5]);
    apply ae_step_inv in Hs end.
  match goal with E : ?U = _ |- _ => is_var U; rewrite E end.
  do 3 eexists; split; [reflexivity|split; [reflexivity|]].
  match goal with H : (_ \/ False) \/ _ |- _ => destruct H as [[[-> ->]|[]]|[k [-> Hk]]] end.
  - left; split; [reflexivity|cbn; reflexivity].
  - right; exists k; split; [reflexivity|exact Hk].
Qed.

Lemma pair_parts : forall B S,
  (forall P, get_l @ (B '* S) ==> P -> P = left_of (B '* S)).
Proof. intros B S P H; exact (eval_deterministic _ _ H _ (get_l_spec _)). Qed.

Ltac pair_specs U :=
  pose proof (get_l_spec U) as P1; pose proof (get_s_spec (left_of U)) as P2;
  pose proof (get_r_spec (stem_of (left_of U))) as P3;
  pose proof (get_r_spec (right_of (stem_of (left_of U)))) as P4;
  pose proof (get_r_spec U) as P5; pose proof (get_r_spec (right_of U)) as P6;
  cbn [left_of right_of stem_of] in P1, P2, P3, P4, P5, P6.

Lemma ae_fwd_leaf : forall A n a B S,
  'wait[ae_prog, Fk (code A) Lf] @ n @r a @r (B '* S) ==> Sm B.
Proof.
  intros A n a B S.
  pose proof (get_l_spec (Fk (code A) Lf)) as Hl; pose proof (get_r_spec (Fk (code A) Lf)) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_code A) as HdA.
  pose proof (equal_eq (B '* S)) as He. pair_specs (B '* S).
  eapply eval_appl; [eapply eval_appl; [apply wait_eval|]|].
  Local Transparent ae_prog ae_step. unfold ae_prog, ae_step. Local Opaque ae_prog ae_step.
  all: ev2.
Qed.

Lemma ae_fwd_succ : forall A c k n a B S V, decode c = Some A ->
  a @ S @r (A '* AN c k) ==> Sm V ->
  'wait[ae_prog, Fk c (Sm k)] @ n @r a @r (B '* S) ==> Sm V.
Proof.
  intros A c k n a B S V HA H. destruct (app2_inv _ _ _ _ H) as [p [Hp1 Hp2]].
  pose proof (get_l_spec (Fk c (Sm k))) as Hl; pose proof (get_r_spec (Fk c (Sm k))) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_eval c) as HdA; rewrite HA in HdA; cbn [opt] in HdA.
  pose proof (equal_eq (B '* S)) as He. pair_specs (B '* S).
  unfold AN in Hp1, Hp2.
  eapply eval_appl; [eapply eval_appl; [apply wait_eval|]|].
  Local Transparent ae_prog ae_step. unfold ae_prog, ae_step. Local Opaque ae_prog ae_step.
  all: ev2.
Qed.

(** ** The family entry *)

Lemma array_entry_inv : forall n a D, array_entry @ n @r a ==> Sm D -> exists r, n = Fk array_nm r /\ D = D_array r.
Proof.
  intros n a D H; unfold array_entry in H.
  pose proof (get_par_spec array_nm n) as Hp.
  destruct (par_of array_nm n) as [r|] eqn:E; cbn [opt] in Hp; crunch.
  eexists; split; [apply par_of_some; eassumption|reflexivity].
Qed.

Lemma array_entry_hit : forall r a, array_entry @ Fk array_nm r @r a ==> Sm (D_array r).
Proof.
  intros r a; unfold array_entry.
  pose proof (get_par_spec array_nm (Fk array_nm r)) as Hp; cbn [par_of] in Hp.
  destruct (combination_eq_dec array_nm array_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma array_entry_partial : forall n, exists p, array_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec array_nm n) as Hp.
  destruct (par_of array_nm n); cbn [opt] in Hp; unfold array_entry; eexists; ev2.
Qed.

Lemma arr_fam_inv : forall n a D, arr_fam @ n @r a ==> Sm D -> exists r, n = Fk array_nm r /\ D = D_array r.
Proof.
  intros n a D H; unfold arr_fam in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst; eapply array_entry_inv; exact H1.
  - apply no_rows_inv in H2; discriminate.
Qed.

Lemma arr_fam_partial : forall n, exists p, arr_fam @ n ==> p.
Proof. intros n; apply alt_partial, array_entry_partial. Qed.

(** ** Soundness of the array declaration, by values *)

Theorem array_decl_sound : forall O r, decl_sound O (Fk array_nm r) (D_array r).
Proof.
  intros O r k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (ag_inv _ _ HC') as [A [HA [[Hr ->]|[m [Hr ->]]]]];
  apply elim_of_inv in HE; unfold array_elim in HE;
  apply name_elim_iff, ae_inv in HE; cbn [right_of] in HE;
  destruct HE as [A' [B [S [HA' [-> [[Hr' ->]|[m' [Hr' HS]]]]]]]];
  rewrite HA in HA'; inversion HA'; subst A'; rewrite Hr in Hr'; try discriminate.
  - apply (concrete_type_forces O) in Hc; [subst c|reflexivity].
    destruct (pair_type_inv O v B S Hv) as [b [s [-> [Hb Hs]]]].
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (fst_pair b s)) as ->; exact Hb.
  - inversion Hr'; subst m'.
    destruct (carrier_snd_inv O c _ Hc) as [p [-> Hp]].
    destruct (pair_type_inv O v B S Hv) as [b [s [-> [Hb Hs]]]].
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (snd_pair b s)) as ->.
    assert (E2 : ('K1 p) @ (b '* s) ==> p) by evaluate.
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as ->.
    eapply Hk; [|exact H3|exact Hs|exact Hp|exact HS]; lia.
Qed.

(** ** Soundness of the generic constructors *)

Lemma gee_inv : forall n a U V, gee_prog @ n @r a @r U ==> Sm V ->
  concreteb U = true /\ (exists A, decode U = Some A) /\ V = AN U Lf.
Proof.
  intros n a U V H. Local Transparent gee_prog. unfold gee_prog in H. Local Opaque gee_prog.
  pose proof (is_concrete_bt U) as Hc; pose proof (decode_p_eval U) as Hd.
  destruct (concreteb U) eqn:Ec; cbn [bt] in Hc; [|crunch].
  destruct (decode U) as [A|] eqn:Ed; cbn [opt] in Hd; crunch.
  all: split; [eassumption|split; [eauto|reflexivity]].
Qed.

Definition lm (U : Combination) := right_of (right_of (right_of (right_of (right_of (right_of (right_of U)))))).
Definition pnu (U : Combination) := right_of (right_of (stem_of (left_of U))).

Lemma gpe_inv : forall n a U V, gpe_prog @ n @r a @r U ==> Sm V ->
  exists C0 A m, U = C0 '* (A '* AN C0 m) /\ concreteb C0 = true /\ decode C0 = Some A /\
    V = AN C0 (Sm m).
Proof.
  intros n a U V H. Local Transparent gpe_prog. unfold gpe_prog in H. Local Opaque gpe_prog.
  pose proof (get_l_spec U) as H1; pose proof (get_s_spec (left_of U)) as H2;
  pose proof (get_r_spec (stem_of (left_of U))) as H3; pose proof (get_r_spec (right_of (stem_of (left_of U)))) as H4.
  pose proof (is_concrete_bt (pnu U)) as Hc. pose proof (decode_p_eval (pnu U)) as Hd.
  unfold pnu in Hc, Hd.
  destruct (concreteb (right_of (right_of (stem_of (left_of U))))) eqn:Ec; cbn [bt] in Hc; [|crunch].
  destruct (decode (right_of (right_of (stem_of (left_of U))))) as [A|] eqn:Ed; cbn [opt] in Hd; [|crunch].
  crunch; use_specs; crunch; use_specs; eq_case2; crunch; try discriminate.
  all: do 3 eexists; split; [eassumption|split; [eassumption|split; [eassumption|reflexivity]]].
Qed.

Lemma gemp_eval : forall c, gemp_carrier @ c ==> 'tagged['fst, Fk array_nm (Fk c Lf)].
Proof. intros; unfold gemp_carrier; evaluate. Qed.

Lemma gpre_eval : forall c x f C0 m,
  gpre_carrier @ (c '* (x '* 'tagged[f, Fk array_nm (Fk C0 m)])) ==>
    'tagged['S2['snd, 'K1 (x '* 'tagged[f, Fk array_nm (Fk C0 m)])], Fk array_nm (Fk c (Sm m))].
Proof.
  intros; unfold gpre_carrier.
  pose proof (get_r_spec ('tagged[f, Fk array_nm (Fk C0 m)])) as R1; cbn [right_of] in R1.
  pose proof (get_r_spec ('label[Fk array_nm (Fk C0 m)])) as R2; cbn [right_of] in R2.
  pose proof (get_r_spec ('K1 (Fk array_nm (Fk C0 m)))) as R3; cbn [right_of] in R3.
  pose proof (get_r_spec (Fk array_nm (Fk C0 m))) as R4; cbn [right_of] in R4.
  pose proof (get_r_spec (Fk C0 m)) as R5; cbn [right_of] in R5.
  ev2.
Qed.

Lemma array_tag_concrete : forall c m, concreteb c = true -> concreteb m = true ->
  (forall n, m <> 'K1 n) -> concreteb (Fk array_nm (Fk c m)) = true.
Proof.
  intros c m Hc Hm Hn; cbn [concreteb]; rewrite Hc, Hm.
  assert (E : label_pair array_nm (Fk c m) = false) by reflexivity; rewrite E.
  destruct (label_pair c m) eqn:E2; [|reflexivity].
  destruct (label_pair_K1 _ _ E2) as [k Ek]; exfalso; exact (Hn k Ek).
Qed.

Section Gen.
Variable O : Combination.
Hypothesis HA : forall r, O @ Fk array_nm r @r tp O ==> Sm (D_array r).

Theorem gemp_decl_sound : decl_sound O gen_empty_nm D_gemp.
Proof using HA.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec gemp_carrier C)) as E.
  destruct (combination_eq_dec gemp_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, gee_inv in HE; destruct HE as [HU [[A HA'] ->]].
  apply (concrete_type_forces O) in Hv; [subst v|exact HU].
  pose proof (code_decode _ _ HA') as EU; subst U.
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (gemp_eval (code A))) as ->.
  eapply infer_tag; [apply array_tag_concrete; [exact HU|reflexivity|discriminate]
                    |apply concrete_is_self_typed; reflexivity|apply (HA (Fk (code A) Lf))|].
  eapply app2; [apply guard_of_pair|apply ag_hit_leaf].
Qed.

Theorem gpre_decl_sound : decl_sound O gen_prepend_nm D_gpre.
Proof using HA.
  intros k C U V c v w HC HE Hc Hv _ Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  pose proof (eval_deterministic _ _ HC' _ (guard1_spec gpre_carrier C)) as E.
  destruct (combination_eq_dec gpre_carrier C) as [<-|]; [|discriminate].
  apply (concrete_type_forces O) in Hc; [subst c|vm_compute; reflexivity].
  apply elim_of_inv, gpe_inv in HE; destruct HE as [C0 [A [m [-> [HC0 [HA' ->]]]]]].
  destruct (pair_type_inv O v _ _ Hv) as [c0 [p [-> [Hc0 Hp]]]].
  apply (concrete_type_forces O) in Hc0; [subst c0|exact HC0].
  destruct (pair_type_inv O p _ _ Hp) as [x [xs [-> [Hx Hxs]]]].
  unfold AN in Hxs.
  destruct (no_junk O xs _ Hxs) as [f [F [D [-> [Hn [Hf [HD HG]]]]]]].
  apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (gpre_eval C0 x f C0 m)) as ->.
  destruct (concrete_Fk _ _ Hn) as [_ [_ Hn2]]; destruct (concrete_Fk _ _ Hn2) as [_ [_ Hm]].
  eapply infer_tag; [apply array_tag_concrete; [exact HC0|exact Hm|discriminate]| |apply (HA (Fk C0 (Sm m)))|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|apply pair_typed; [exact Hx|exact Hxs]|reflexivity].
  - eapply app2; [apply guard_of_pair|]. unfold AN. apply ag_hit_succ; exact HA'.
Qed.
End Gen.

(** ** Typings of the values and the eliminator *)

Section Typings.
Variable O : Combination.
Hypothesis HA : forall r, O @ Fk array_nm r @r tp O ==> Sm (D_array r).
Local Notation "t ':' T" := (infer O @ t ==> Sm T) (at level 70).

Lemma Array_tag_concrete : forall A k, names_concrete A -> concreteb (array_tag (code A) (idx k)) = true.
Proof.
  intros A k HA'; unfold array_tag; apply array_tag_concrete;
    [apply code_concrete, HA'|apply idx_concrete|destruct k; discriminate].
Qed.

Theorem empty_typed : forall A, names_concrete A -> empty A : Array A Lf.
Proof using HA.
  intros A HA'; eapply infer_tag; [apply (Array_tag_concrete A 0), HA'| |apply HA|].
  - apply concrete_is_self_typed; reflexivity.
  - eapply app2; [apply guard_of_pair|apply ag_hit_leaf].
Qed.

Theorem prepend_typed : forall A k x xs, names_concrete A -> x : A -> xs : Array A (idx k) ->
  prepend A (idx k) x xs : Array A (Sm (idx k)).
Proof using HA.
  intros A k x xs HA' Hx Hxs; eapply infer_tag; [apply (Array_tag_concrete A (S k)), HA'| |apply HA|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|apply pair_typed; [exact Hx|exact Hxs]|reflexivity].
  - eapply app2; [apply guard_of_pair|]. apply (ag_hit_succ A (code A) (idx k)), decode_code.
Qed.

Theorem type_app_Array_leaf : forall A B S, tp O @ Array A Lf @r (B '* S) ==> Sm B.
Proof using HA.
  intros A B S; eapply tp_abs; [apply HA|apply elim_of_fwd].
  unfold array_elim; apply name_elim_iff; cbn [right_of array_tag]. apply ae_fwd_leaf.
Qed.

Theorem type_app_Array_succ : forall A k B S V, tp O @ S @r (A '* Array A k) ==> Sm V ->
  tp O @ Array A (Sm k) @r (B '* S) ==> Sm V.
Proof using HA.
  intros A k B S V H; eapply tp_abs; [apply HA|apply elim_of_fwd].
  unfold array_elim; apply name_elim_iff; cbn [right_of array_tag].
  eapply ae_fwd_succ; [apply decode_code|exact H].
Qed.

(** The eliminator, inverted. *)
Theorem type_app_Array_inv : forall A k U V, tp O @ Array A k @r U ==> Sm V ->
  exists B S, U = B '* S /\ ((k = Lf /\ V = B) \/
    (exists k', k = Sm k' /\ tp O @ S @r (A '* Array A k') ==> Sm V)).
Proof using HA.
  intros A k U V H; apply tp_inv in H.
  inversion H as [n U0 D R0 HD HEl | | | | G H0 U0 V0 W R0 HL _ _ _ | | |]; subst.
  - pose proof (eval_deterministic _ _ HD _ (HA _)) as E; inversion E; subst; clear E.
    apply elim_of_inv in HEl; unfold array_elim in HEl; apply name_elim_iff in HEl.
    cbn [right_of array_tag] in HEl; apply ae_inv in HEl; cbn [left_of right_of] in HEl.
    destruct HEl as [A' [B [S [HA' [-> [[-> ->]|[k' [-> HS]]]]]]]];
      rewrite decode_code in HA'; inversion HA'; subst A'; exists B, S; split; auto.
    right; exists k'; split; [reflexivity|exact HS].
  - cbn in HL; discriminate.
Qed.
End Typings.

(** The generic constructors in any ontology that declares them. *)
Lemma gee_fwd : forall A n a, names_concrete A -> gee_prog @ n @r a @r code A ==> Sm (Array A Lf).
Proof.
  intros A n a HA. Local Transparent gee_prog. unfold gee_prog. Local Opaque gee_prog.
  pose proof (is_concrete_bt (code A)) as Hc; rewrite (code_concrete A HA) in Hc; cbn [bt] in Hc.
  pose proof (decode_p_code A) as Hd. unfold Array, array_tag. ev2.
Qed.

Section GenTypings.
Variable O : Combination.
Hypothesis HP : O @ gen_prepend_nm @r tp O ==> Sm D_gpre.
Hypothesis HE : O @ gen_empty_nm @r tp O ==> Sm D_gemp.

Theorem type_app_gen_empty : forall A, names_concrete A -> tp O @ 'label[gen_empty_nm] @r code A ==> Sm (Array A Lf).
Proof using HE. intros A HA; eapply tp_abs; [exact HE|apply elim_of_fwd, gee_fwd, HA]. Qed.

End GenTypings.
Lemma gpe_fwd : forall A k n a, names_concrete A ->
  gpe_prog @ n @r a @r (code A '* (A '* Array A k)) ==> Sm (Array A (Sm k)).
Proof.
  intros A k n a HA. Local Transparent gpe_prog. unfold gpe_prog. Local Opaque gpe_prog.
  pose proof (is_concrete_bt (code A)) as Hc; rewrite (code_concrete A HA) in Hc; cbn [bt] in Hc.
  pose proof (decode_p_code A) as Hd. pose proof (equal_eq (code A '* (A '* Array A k))) as He.
  unfold Array, array_tag in *.
  split2; evaluate2; repeat first [eassumption | apply get_l_spec | apply get_r_spec | apply get_s_spec
    | apply equal_eval | progress cbn [left_of right_of stem_of] | progress evaluate2].
Qed.

Section GenTypings2.
Variable O : Combination.
Hypothesis HP : O @ gen_prepend_nm @r tp O ==> Sm D_gpre.
Theorem type_app_gen_prepend : forall A k, names_concrete A ->
  tp O @ 'label[gen_prepend_nm] @r (code A '* (A '* Array A k)) ==> Sm (Array A (Sm k)).
Proof using HP. intros A k HA; eapply tp_abs; [exact HP|apply elim_of_fwd, gpe_fwd, HA]. Qed.
End GenTypings2.

(** The run-time behaviour. *)
Lemma empty_apply : forall A u f, empty A @ (u '* f) ==> u.
Proof. intros; unfold empty; apply tagged_eval; evaluate. Qed.
Lemma prepend_apply : forall A n x xs u f v, f @ (x '* xs) ==> v -> prepend A n x xs @ (u '* f) ==> v.
Proof. intros; unfold prepend; apply tagged_eval; evaluate; eassumption. Qed.
Lemma gen_empty_eval : forall A, gen_empty @ code A ==> empty A.
Proof. intros; unfold gen_empty, empty, array_tag; apply tagged_eval, gemp_eval. Qed.
Lemma gen_prepend_eval : forall A x f m,
  gen_prepend @ (code A '* (x '* 'tagged[f, array_tag (code A) m])) ==> prepend A m x ('tagged[f, array_tag (code A) m]).
Proof. intros; unfold gen_prepend, prepend, array_tag; apply tagged_eval, gpre_eval. Qed.
