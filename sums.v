(** * Step 82, stage 6, part 2: sums with codes.

    [Sum[A,B] = label[sum_tag[code A, code B]]], [sum_tag[cA,cB] = Fk sum_nm (Fk cA cB)].
    The declaration at [Fk sum_nm r] decodes [A] and [B] from the name:

      guard:  admits S2[fst, K1 A]  (the carrier type of inleft[A,B,a], a : A)
              and    S2[snd, K1 B]  (the carrier type of inright[A,B,b], b : B)
      elim:   Sum[A,B] # (F * G) ==> Sm C   when F # A ==> Sm C and G # B ==> Sm C

    Values: [inleft[A,B,a] = tagged[S2[fst, K1 a], sum_tag]] and
    [inright[A,B,b] = tagged[S2[snd, K1 b], sum_tag]], so that
    [inleft[a] @ (f * g) = f @ a] and [inright[b] @ (f * g) = g @ b]: the
    case eliminator is application to a pair.  The constructor
    [mk_sum[A,B]] (family at [Fk mksum_nm r], r concrete) tags a carrier
    admitted by the guard.  The declaration is sound by values. *)

From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists.
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition sum_nm : Combination := Nat.iter 26 Sm Lf.
Definition mksum_nm : Combination := Nat.iter 27 Sm Lf.
Definition sum_tag (cA cB : Combination) : Combination := Fk sum_nm (Fk cA cB).
Definition Sum (A B : Combination) : Combination := 'label[sum_tag (code A) (code B)].
Definition inleft (A B a : Combination) : Combination := 'tagged['S2['fst, 'K1 a], sum_tag (code A) (code B)].
Definition inright (A B b : Combination) : Combination := 'tagged['S2['snd, 'K1 b], sum_tag (code A) (code B)].
Definition mk_sum (A B : Combination) : Combination :=
  'tagged['tagger[sum_tag (code A) (code B)], Fk mksum_nm (Fk (code A) (code B))].

Definition sg_prog : Combination := Eval cbn -[equal decode_p get_l get_r] in to_tree
  (star "r" (star "C"
    (''onStem1 (star "A" (''onStem1 (star "B"
        (op equal @@ Ref "C" @@ ''S2[Val 'fst, ''K1 (Ref "A")] @@ Val 'K
           @@ (op equal @@ Ref "C" @@ ''S2[Val 'snd, ''K1 (Ref "B")])))
       @@ (op decode_p @@ (op get_r @@ Ref "r"))))
     @@ (op decode_p @@ (op get_l @@ Ref "r"))))).

Definition se_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s] in to_tree
  (star "r" (star "n" (star "a" (star "U"
    (''onStem1 (star "A" (''onStem1 (star "B"
       (op equal @@ Ref "U" @@ (PN (Ref "U") ''* PS (Ref "U"))
          @@ star "U2" (''onStem1 (star "R1" (''onStem1 (star "R2"
                 (op equal @@ Ref "R1" @@ Ref "R2" @@ (Val Lf @@ Ref "R1") @@ Val Lf))
                 @@ (Ref "a" @@ PS (Ref "U2") @@ Ref "B")))
               @@ (Ref "a" @@ PN (Ref "U2") @@ Ref "A"))
          @@ Val ('K1 Lf) @@ Ref "U"))
       @@ (op decode_p @@ (op get_r @@ Ref "r"))))
     @@ (op decode_p @@ (op get_l @@ Ref "r"))))))).

Definition sum_guard (r : Combination) : Combination := 'wait[sg_prog, r].
Definition sum_elim : Combination := name_elim se_prog.
Definition D_sum (r : Combination) : Combination := sum_guard r '* sum_elim.
Definition D_mksum (r : Combination) : Combination :=
  guard1 ('tagger[Fk sum_nm r]) '* ctor_elim (sum_guard r) (Fk sum_nm r).

Definition sum_entry : Combination := Eval cbn -[get_par sum_nm sum_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (Val Lf @@ (''wait[Val sg_prog, Ref "r"] ''* Val sum_elim)))
       @@ (op (get_par sum_nm) @@ Ref "n")))).
Definition mksum_entry : Combination := Eval cbn -[get_par sum_nm mksum_nm is_concrete] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (op is_concrete @@ Ref "r" @@ (Val Lf @@
       (''wait[Val equal, tagger_t (Val Lf @@ Val sum_nm @@ Ref "r")]
        ''* ''wait2[Val ctor_prog, ''wait[Val sg_prog, Ref "r"], Val Lf @@ Val sum_nm @@ Ref "r"])) @@ Val Lf))
       @@ (op (get_par mksum_nm) @@ Ref "n")))).
Definition sum_fam : Combination := alt sum_entry (alt mksum_entry no_rows).

Local Opaque sg_prog se_prog.

(** ** Inversions and hits *)

Lemma sg_inv : forall r C, sum_guard r @ C ==> 'K ->
  exists A B, decode (left_of r) = Some A /\ decode (right_of r) = Some B /\
    (C = 'S2['fst, 'K1 A] \/ C = 'S2['snd, 'K1 B]).
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent sg_prog. unfold sg_prog in H. Local Opaque sg_prog.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as Hd1; pose proof (decode_p_eval (right_of r)) as Hd2.
  destruct (decode (left_of r)) as [A|]; cbn [opt] in Hd1; [|crunch].
  destruct (decode (right_of r)) as [B|]; cbn [opt] in Hd2; [|crunch].
  exists A, B; split; [reflexivity|split; [reflexivity|]].
  pose proof (equal_bt C ('S2['fst, 'K1 A])) as E1; pose proof (equal_bt C ('S2['snd, 'K1 B])) as E2.
  inv_out E1; inv_out E2; dedup.
  destruct (combination_eq_dec C ('S2['fst, 'K1 A])); [left; assumption|].
  destruct (combination_eq_dec C ('S2['snd, 'K1 B])); [right; assumption|].
  cbn [bt] in *; crunch.
Qed.

Lemma sg_hit : forall A B C, C = 'S2['fst, 'K1 A] \/ C = 'S2['snd, 'K1 B] ->
  sum_guard (Fk (code A) (code B)) @ C ==> 'K.
Proof.
  intros A B C HC; apply wait_eval. Local Transparent sg_prog. unfold sg_prog. Local Opaque sg_prog.
  pose proof (get_l_spec (Fk (code A) (code B))) as Hl; pose proof (get_r_spec (Fk (code A) (code B))) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_code A) as HdA; pose proof (decode_p_code B) as HdB.
  destruct HC as [->| ->].
  - pose proof (equal_eq ('S2['fst, 'K1 A])) as He.
    assert (Hn : 'S2['fst, 'K1 A] <> 'S2['snd, 'K1 B]) by discriminate.
    pose proof (equal_neq _ _ Hn) as He2; ev2.
  - assert (Hn : 'S2['snd, 'K1 B] <> 'S2['fst, 'K1 A]) by discriminate.
    pose proof (equal_neq _ _ Hn) as He; pose proof (equal_eq ('S2['snd, 'K1 B])) as He2; ev2.
Qed.

Lemma se_inv : forall r n a U V, 'wait[se_prog, r] @ n @r a @r U ==> Sm V ->
  exists A B F G, decode (left_of r) = Some A /\ decode (right_of r) = Some B /\ U = F '* G /\
    a @ F @r A ==> Sm V /\ a @ G @r B ==> Sm V.
Proof.
  intros r n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent se_prog. unfold se_prog in Hp1. Local Opaque se_prog.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as Hd1; pose proof (decode_p_eval (right_of r)) as Hd2.
  destruct (decode (left_of r)) as [A|]; cbn [opt] in Hd1; [|crunch].
  destruct (decode (right_of r)) as [B|]; cbn [opt] in Hd2; crunch; use_specs; crunch; use_specs.
  all: try (eq_case2; crunch; use_specs; try discriminate).
  all: try (eq_case2; crunch; use_specs; try discriminate).
  all: match goal with E : ?U = _ |- _ => is_var U; rewrite E end.
  all: do 4 eexists; split; [reflexivity|split; [reflexivity|split; [reflexivity|split; eapply eval_appl; eassumption]]].
Qed.

Lemma se_fwd : forall A B F G C n a, a @ F @r A ==> Sm C -> a @ G @r B ==> Sm C ->
  'wait[se_prog, Fk (code A) (code B)] @ n @r a @r (F '* G) ==> Sm C.
Proof.
  intros A B F G C n a H1 H2.
  pose proof (get_l_spec (Fk (code A) (code B))) as Hl; pose proof (get_r_spec (Fk (code A) (code B))) as Hr;
  cbn [left_of right_of] in Hl, Hr.
  pose proof (decode_p_code A) as HdA; pose proof (decode_p_code B) as HdB.
  pose proof (equal_eq (F '* G)) as He; pose proof (equal_eq C) as He2.
  pose proof (get_l_spec (F '* G)) as P1; pose proof (get_s_spec (left_of (F '* G))) as P2;
  pose proof (get_r_spec (stem_of (left_of (F '* G)))) as P3;
  pose proof (get_r_spec (right_of (stem_of (left_of (F '* G))))) as P4;
  pose proof (get_r_spec (F '* G)) as P5; pose proof (get_r_spec (right_of (F '* G))) as P6;
  cbn [left_of right_of stem_of] in P1, P2, P3, P4, P5, P6.
  eapply eval_appl; [eapply eval_appl; [apply wait_eval|]|].
  Local Transparent se_prog. unfold se_prog. Local Opaque se_prog.
  all: ev2.
Qed.

(** ** The family entries *)

Lemma sum_entry_inv : forall n a D, sum_entry @ n @r a ==> Sm D -> exists r, n = Fk sum_nm r /\ D = D_sum r.
Proof.
  intros n a D H; unfold sum_entry in H.
  pose proof (get_par_spec sum_nm n) as Hp.
  destruct (par_of sum_nm n) as [r|] eqn:E; cbn [opt] in Hp; crunch.
  eexists; split; [apply par_of_some; eassumption|reflexivity].
Qed.

Lemma sum_entry_hit : forall r a, sum_entry @ Fk sum_nm r @r a ==> Sm (D_sum r).
Proof.
  intros r a; unfold sum_entry.
  pose proof (get_par_spec sum_nm (Fk sum_nm r)) as Hp; cbn [par_of] in Hp.
  destruct (combination_eq_dec sum_nm sum_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma sum_entry_partial : forall n, exists p, sum_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec sum_nm n) as Hp.
  destruct (par_of sum_nm n); cbn [opt] in Hp; unfold sum_entry; eexists; ev2.
Qed.

Lemma sum_entry_miss : forall n a, par_of sum_nm n = None -> sum_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold sum_entry; pose proof (get_par_spec sum_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma mksum_entry_inv : forall n a D, mksum_entry @ n @r a ==> Sm D ->
  exists r, n = Fk mksum_nm r /\ concreteb r = true /\ D = D_mksum r.
Proof.
  intros n a D H; unfold mksum_entry in H.
  pose proof (get_par_spec mksum_nm n) as Hp.
  destruct (par_of mksum_nm n) as [r|] eqn:E; cbn [opt] in Hp; [|crunch].
  pose proof (is_concrete_bt r) as Hc; destruct (concreteb r) eqn:Ec; cbn [bt] in Hc; crunch;
    eexists; split; [apply par_of_some; eassumption|split; [eassumption|reflexivity]].
Qed.

Lemma mksum_entry_hit : forall r a, concreteb r = true -> mksum_entry @ Fk mksum_nm r @r a ==> Sm (D_mksum r).
Proof.
  intros r a Hr; unfold mksum_entry.
  pose proof (get_par_spec mksum_nm (Fk mksum_nm r)) as Hp; cbn [par_of] in Hp.
  pose proof (is_concrete_bt r) as Hc; rewrite Hr in Hc; cbn [bt] in Hc.
  destruct (combination_eq_dec mksum_nm mksum_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma mksum_entry_partial : forall n, exists p, mksum_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec mksum_nm n) as Hp.
  destruct (par_of mksum_nm n) as [c|]; cbn [opt] in Hp;
    [pose proof (is_concrete_bt c) as Hc; destruct (concreteb c); cbn [bt] in Hc|];
    unfold mksum_entry; eexists; ev2.
Qed.

Lemma mksum_entry_miss : forall n a, par_of mksum_nm n = None -> mksum_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold mksum_entry; pose proof (get_par_spec mksum_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma sum_fam_partial : forall n, exists p, sum_fam @ n ==> p.
Proof. intros n; apply alt_partial, sum_entry_partial. Qed.

Lemma sum_fam_inv : forall n a D, sum_fam @ n @r a ==> Sm D ->
  (exists r, n = Fk sum_nm r /\ D = D_sum r) \/ (exists r, n = Fk mksum_nm r /\ concreteb r = true /\ D = D_mksum r).
Proof.
  intros n a D H; unfold sum_fam in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst; left; eapply sum_entry_inv; exact H1.
  - destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst; right; eapply mksum_entry_inv; exact H3.
    + apply no_rows_inv in H4; discriminate.
Qed.

Lemma sum_fam_sum : forall r a, sum_fam @ Fk sum_nm r @r a ==> Sm (D_sum r).
Proof. intros r a; unfold sum_fam; apply alt_some; [apply sum_entry_hit|apply alt_partial, mksum_entry_partial]. Qed.

Lemma sum_fam_mksum : forall r a, concreteb r = true -> sum_fam @ Fk mksum_nm r @r a ==> Sm (D_mksum r).
Proof.
  intros r a Hr; unfold sum_fam; apply alt_none; [apply sum_entry_miss; cbn; reflexivity|].
  apply alt_some; [apply mksum_entry_hit, Hr|unfold no_rows; eexists; evaluate].
Qed.

Lemma sum_fam_miss : forall n a, par_of sum_nm n = None -> par_of mksum_nm n = None -> sum_fam @ n @r a ==> Lf.
Proof.
  intros n a H1 H2; unfold sum_fam; apply alt_none; [apply sum_entry_miss, H1|].
  apply alt_none; [apply mksum_entry_miss, H2|unfold no_rows; evaluate].
Qed.

(** ** Soundness by values *)

Theorem sum_decl_sound : forall O r, decl_sound O (Fk sum_nm r) (D_sum r).
Proof.
  intros O r k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (sg_inv _ _ HC') as [A [B [HA [HB [->| ->]]]]];
  apply elim_of_inv in HE; unfold sum_elim in HE;
  apply name_elim_iff, se_inv in HE; cbn [right_of] in HE;
  destruct HE as [A' [B' [F [G [HA' [HB' [-> [HF HG]]]]]]]];
  rewrite HA in HA'; inversion HA'; subst A'; rewrite HB in HB'; inversion HB'; subst B';
  destruct (pair_type_inv O v F G Hv) as [f [h [-> [Hf Hh]]]]; clear Hv; force O;
  destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
  - pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (fst_pair f h)) as ->.
    match goal with H2 : evaln _ (('K1 ?x) @ _) _ |- _ =>
      assert (E2 : ('K1 x) @ (f '* h) ==> x) by evaluate;
      pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as -> end.
    eapply Hk; [|exact H3|exact Hf|eassumption|exact HF]; lia.
  - pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (snd_pair f h)) as ->.
    match goal with H2 : evaln _ (('K1 ?x) @ _) _ |- _ =>
      assert (E2 : ('K1 x) @ (f '* h) ==> x) by evaluate;
      pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as -> end.
    eapply Hk; [|exact H3|exact Hh|eassumption|exact HG]; lia.
Qed.

Section SumGeneric.
Variable O : Combination.
Hypothesis HS : forall r, O @ Fk sum_nm r @r tp O ==> Sm (D_sum r).

Theorem mksum_decl_sound : forall r, concreteb r = true -> decl_sound O (Fk mksum_nm r) (D_mksum r).
Proof using HS.
  intros r Hr; eapply ctor_decl_sound; [cbn; exact Hr|apply HS|apply guard_of_pair].
Qed.

Lemma sum_tag_concrete : forall A B, names_concrete A -> names_concrete B -> concreteb (sum_tag (code A) (code B)) = true.
Proof.
  intros A B HA HB; unfold sum_tag; cbn [concreteb]; rewrite (code_concrete A HA), (code_concrete B HB).
  assert (E : label_pair sum_nm (Fk (code A) (code B)) = false) by reflexivity; rewrite E.
  assert (E2 : label_pair (code A) (code B) = false).
  { destruct (code A) as [|[|[| |]|]|]; try reflexivity; destruct B as [| |u v]; try reflexivity.
    cbn [code]; destruct (label_of (Fk u v)); reflexivity. }
  rewrite E2; reflexivity.
Qed.

Theorem inleft_typed : forall A B a, names_concrete A -> names_concrete B -> infer O @ a ==> Sm A ->
  infer O @ inleft A B a ==> Sm (Sum A B).
Proof using HS.
  intros A B a HA HB Ha; eapply infer_tag; [apply sum_tag_concrete; assumption| |apply HS|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|exact Ha|reflexivity].
  - eapply app2; [apply guard_of_pair|apply sg_hit; left; reflexivity].
Qed.

Theorem inright_typed : forall A B b, names_concrete A -> names_concrete B -> infer O @ b ==> Sm B ->
  infer O @ inright A B b ==> Sm (Sum A B).
Proof using HS.
  intros A B b HA HB Hb; eapply infer_tag; [apply sum_tag_concrete; assumption| |apply HS|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|exact Hb|reflexivity].
  - eapply app2; [apply guard_of_pair|apply sg_hit; right; reflexivity].
Qed.

(** The case eliminator: [Sum[A,B] # (F * G) ==> Sm C] when [F # A ==> Sm C] and [G # B ==> Sm C]. *)
Theorem type_app_Sum : forall A B F G C, tp O @ F @r A ==> Sm C -> tp O @ G @r B ==> Sm C ->
  tp O @ Sum A B @r (F '* G) ==> Sm C.
Proof using HS.
  intros A B F G C H1 H2; eapply tp_abs; [apply HS|].
  apply elim_of_fwd; unfold sum_elim; apply name_elim_iff; cbn [right_of sum_tag].
  apply se_fwd; assumption.
Qed.
End SumGeneric.

(** The run-time behaviour. *)
Lemma inleft_apply : forall A B a f g v, f @ a ==> v -> inleft A B a @ (f '* g) ==> v.
Proof. intros; unfold inleft; apply tagged_eval; evaluate; eassumption. Qed.
Lemma inright_apply : forall A B b f g v, g @ b ==> v -> inright A B b @ (f '* g) ==> v.
Proof. intros; unfold inright; apply tagged_eval; evaluate; eassumption. Qed.
Lemma mk_sum_eval : forall A B c, mk_sum A B @ c ==> 'tagged[c, sum_tag (code A) (code B)].
Proof. intros; apply tagged_eval, tagger_eval. Qed.
