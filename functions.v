(** * Step 82, stage 2A: function types from codes.

    The function type [Fun[A,B] = label[fun_tag[code A, code B]]] has a
    concrete name, built from the codes of [A] and [B].  Its declaration
    is computed by the family program [fun_entry] from the name and the
    type application [tp] it receives:

      guard:  F  admitted  iff  F # A ==> Sm B         (A, B decoded)
      elim:   Fun[A,B] # X ==> Sm B  if X = A,  and Lf otherwise

    Values are lambda programs [lam[f,A,B] = tagged[f, fun_tag[code A, code B]]],
    or are built at run time by the constructor
    [mk_fun[A,B] = tagged[tagger[fun_tag[..]], mkfun_tag[..]]].
    The declaration is sound by typing, whether or not [A] has values; the
    constructor is sound by values.  [Empty] is declared with a guard that
    admits nothing, so it has no values. *)

From BigStep Require Import tree typing soundness rows identifiers booleans.
From Stdlib Require Import String List Bool.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal.

(** Case analysis on a comparison [equal @ x @ y] found in the context. *)
Ltac eq_case := match goal with H : equal @ ?x ==> ?e, H' : ?e @ ?y ==> _ |- _ =>
  let He := fresh "He" in let Hne := fresh "Hne" in
  destruct (combination_eq_dec x y) as [<-|Hne];
  [pose proof (equal_eq x) as He | pose proof (equal_neq x y Hne) as He]; inv_out He; dedup end.

Ltac splitn := repeat match goal with H : eval (Fk (Fk _ _) (Sm _)) _ |- _ => inv_out H end; dedup.
Ltac ev2 := split2; evaluate2; repeat first [eassumption | progress evaluate2].
Ltac ev3 := splitn; evaluate2; repeat first [eassumption | progress evaluate2].

(** ** Accessors *)

Definition get_l : Combination := 'triage[Lf, 'K1 Lf, 'K].
Definition get_r : Combination := 'triage[Lf, 'K1 Lf, 'K1 'I].
Definition left_of (t : Combination) := match t with Fk a _ => a | _ => Lf end.
Definition right_of (t : Combination) := match t with Fk _ b => b | _ => Lf end.
Lemma get_l_spec : forall t, get_l @ t ==> left_of t.
Proof. intros [|t|a b]; unfold get_l; evaluate. Qed.
Lemma get_r_spec : forall t, get_r @ t ==> right_of t.
Proof. intros [|t|a b]; unfold get_r; evaluate. Qed.

(** ** Eliminators that read the name

    A family eliminator receives the name [n] (as [elim @ n @r tp @r U])
    and reads the code held in it: [name_elim p @ n = p @ right_of n @ n],
    so [p] decodes the code [right_of n] when it applies. *)
Definition name_elim (p : Combination) : Combination := Eval cbn -[get_r] in to_tree
  (star "n" (op p @@ (op get_r @@ Ref "n") @@ Ref "n")).

Lemma name_elim_head : forall p n w, name_elim p @ n ==> w <-> 'wait[p, right_of n] @ n ==> w.
Proof.
  intros p n w; pose proof (get_r_spec n) as Hr; split; intro H.
  - apply wait_eval. Local Transparent get_r. unfold name_elim in H. Local Opaque get_r.
    crunch; dedup; eapply app2; eassumption.
  - apply wait_eval_inv in H. unfold name_elim. ev2.
Qed.

Lemma name_elim_iff : forall p n a U V, name_elim p @ n @r a @r U ==> V <-> 'wait[p, right_of n] @ n @r a @r U ==> V.
Proof.
  intros p n a U V; split; intro H;
    destruct (appl_inv _ _ _ _ H) as [q [Hq HU]]; destruct (app2_inv _ _ _ _ Hq) as [q1 [Hq1 Ha]];
    (eapply eval_appl; [eapply app2; [|exact Ha]|exact HU]); apply name_elim_head; exact Hq1.
Qed.

(** ** Names *)

Definition empty_nm : Combination := Nat.iter 7 Sm Lf.
Definition fun_nm : Combination := Nat.iter 8 Sm Lf.
Definition mkfun_nm : Combination := Nat.iter 9 Sm Lf.
Definition mkn_nm : Combination := Nat.iter 10 Sm Lf.

Definition fun_tag (cA cB : Combination) : Combination := Fk fun_nm (Fk cA cB).
Definition Fun (A B : Combination) : Combination := 'label[fun_tag (code A) (code B)].
Definition lam (f A B : Combination) : Combination := 'tagged[f, fun_tag (code A) (code B)].
Definition Empty : Combination := 'label[empty_nm].

(** ** The declaration of function types *)

Local Opaque decode_p get_l get_r.

(** guard: [fg_prog @ r @ a @ F ==> K] iff [a @ F @ A ==> Sm B], where
    [r = Fk (code A) (code B)]. *)
Definition fg_prog : Combination := Eval cbn -[equal decode_p get_l get_r] in to_tree
  (star "r" (star "a" (star "F"
    (''onStem1 (star "A" (''onStem1 (star "B"
        (''onStem1 (star "R" (op equal @@ Ref "R" @@ Ref "B")) @@ (Ref "a" @@ Ref "F" @@ Ref "A")))
       @@ (op decode_p @@ (op get_r @@ Ref "r"))))
     @@ (op decode_p @@ (op get_l @@ Ref "r")))))).

(** eliminator: [fe_prog @ r @ n @ a @ X ==> Sm B] iff [X = A]. *)
Definition fe_prog : Combination := Eval cbn -[equal decode_p get_l get_r] in to_tree
  (star "r" (star "n" (star "a" (star "X"
    (''onStem1 (star "A" (''onStem1 (star "B"
        (op equal @@ Ref "X" @@ Ref "A" @@ (Val Lf @@ Ref "B") @@ Val Lf))
       @@ (op decode_p @@ (op get_r @@ Ref "r"))))
     @@ (op decode_p @@ (op get_l @@ Ref "r"))))))).

Definition fun_guard (r a : Combination) : Combination := 'wait2[fg_prog, r, a].
Definition fun_elim : Combination := name_elim fe_prog.
Definition fun_D (r a : Combination) : Combination := fun_guard r a '* fun_elim.

Lemma fun_guard_inv : forall r a F, fun_guard r a @ F ==> 'K ->
  exists A B, decode (left_of r) = Some A /\ decode (right_of r) = Some B /\ a @ F @r A ==> Sm B.
Proof.
  intros r a F H; apply wait2_eval_inv in H; unfold fg_prog in H.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as HA; pose proof (decode_p_eval (right_of r)) as HB.
  destruct (decode (left_of r)) as [A|]; destruct (decode (right_of r)) as [B|]; cbn [opt] in *;
    crunch.
  eq_case; crunch; fin.
Qed.

Lemma fun_guard_hit : forall A B a F, a @ F @r A ==> Sm B ->
  fun_guard (Fk (code A) (code B)) a @ F ==> 'K.
Proof.
  intros A B a F H; apply wait2_eval; unfold fg_prog.
  pose proof (get_l_spec (Fk (code A) (code B))) as Hl; pose proof (get_r_spec (Fk (code A) (code B))) as Hr.
  cbn [left_of right_of] in *.
  pose proof (decode_p_code A) as HA; pose proof (decode_p_code B) as HB.
  pose proof (equal_eq B) as He.
  ev2.
Qed.

Lemma fun_elim_inv : forall n a X W, fun_elim @ n @r a @r X ==> Sm W ->
  exists A, decode (left_of (right_of n)) = Some A /\ decode (right_of (right_of n)) = Some W /\ X = A.
Proof.
  intros n a X W H; unfold fun_elim in H; apply name_elim_iff in H; remember (right_of n) as r eqn:Er; clear Er.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1; unfold fe_prog in Hp1.
  pose proof (get_l_spec r) as Hl; pose proof (get_r_spec r) as Hr.
  pose proof (decode_p_eval (left_of r)) as HA; pose proof (decode_p_eval (right_of r)) as HB.
  destruct (decode (left_of r)) as [A|]; destruct (decode (right_of r)) as [B|]; cbn [opt] in *;
    crunch.
  eq_case; crunch; fin.
Qed.

Lemma fun_elim_hit : forall A B a, fun_elim @ fun_tag (code A) (code B) @r a @r A ==> Sm B.
Proof.
  intros A B a; unfold fun_elim; apply name_elim_iff; cbn [right_of fun_tag].
  pose proof (get_l_spec (Fk (code A) (code B))) as Hl; pose proof (get_r_spec (Fk (code A) (code B))) as Hr.
  cbn [left_of right_of] in *.
  pose proof (decode_p_code A) as HA; pose proof (decode_p_code B) as HB.
  pose proof (equal_eq A) as He.
  eapply eval_appl; [eapply eval_appl; [apply wait_eval; unfold fe_prog|]|]; ev2.
Qed.

(** The function declaration is sound by typing, for every ontology and
    every name, whether or not the domain has values. *)
Theorem fun_decl_sound_by_typing : forall O r,
  decl_sound_by_typing O (Fk fun_nm r) (fun_D r (tp O)).
Proof.
  intros O r C X W HC HE.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (fun_guard_inv _ _ _ HC') as [A [B [HA [HB HCA]]]].
  apply elim_of_inv, fun_elim_inv in HE; cbn [right_of] in HE; destruct HE as [A' [HA' [HB' ->]]].
  rewrite HA in HA'; rewrite HB in HB'; inversion HA'; inversion HB'; subst; exact HCA.
Qed.

(** ** The family programs *)

(** [fun_entry @ n @ a ==> Sm (fun_D r a)] when [n = Fk fun_nm r]. *)
Definition fun_entry : Combination := Eval cbn -[get_par fun_nm fun_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (Val Lf @@ (''wait2[Val fg_prog, Ref "r", Ref "a"] ''* Val fun_elim)))
       @@ (op (get_par fun_nm) @@ Ref "n")))).

(** The constructor of [Fun[A,B]], at the name [Fk mkfun_nm r]:
    carrier [tagger[Fk fun_nm r]], eliminator [ctor_elim (fun_guard r a) (Fk fun_nm r)]. *)
Definition mk_D (r a : Combination) : Combination :=
  guard1 ('tagger[Fk fun_nm r]) '* ctor_elim (fun_guard r a) (Fk fun_nm r).

Definition mkfun_entry : Combination := Eval cbn -[get_par is_concrete fun_nm mkfun_nm] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r"
        (op is_concrete @@ Ref "r"
           @@ (Val Lf @@ (''wait[Val equal,
                                ''S2[Val 'tag_head, ''S2[''K1 (Val 'make_label), ''K1 (Val Lf @@ Val fun_nm @@ Ref "r")]]]
                          ''* ''wait2[Val ctor_prog, ''wait2[Val fg_prog, Ref "r", Ref "a"], Val Lf @@ Val fun_nm @@ Ref "r"]))
           @@ Val Lf))
       @@ (op (get_par mkfun_nm) @@ Ref "n")))).

Definition fam_fun : Combination := alt fun_entry (alt mkfun_entry no_rows).

Local Opaque get_par is_concrete fg_prog fe_prog ctor_prog.

Lemma fun_entry_inv : forall n a v, fun_entry @ n @r a ==> v ->
  (exists r, n = Fk fun_nm r /\ v = Sm (fun_D r a)) \/ (par_of fun_nm n = None /\ v = Lf).
Proof.
  intros n a v H; unfold fun_entry in H.
  pose proof (get_par_spec fun_nm n) as Hp.
  destruct (par_of fun_nm n) as [r|] eqn:E; cbn [opt] in Hp; crunch;
    first [left; eexists; split; [apply par_of_some; eassumption|reflexivity] | right; auto].
Qed.

Lemma fun_entry_hit : forall r a, fun_entry @ Fk fun_nm r @r a ==> Sm (fun_D r a).
Proof.
  intros r a; unfold fun_entry.
  pose proof (get_par_spec fun_nm (Fk fun_nm r)) as Hp; cbn [par_of] in Hp.
  destruct (combination_eq_dec fun_nm fun_nm); [|contradiction]; cbn [opt] in Hp.
  ev2.
Qed.

Lemma mkfun_entry_inv : forall n a v, mkfun_entry @ n @r a ==> v ->
  (exists r, n = Fk mkfun_nm r /\ concreteb r = true /\ v = Sm (mk_D r a)) \/ v = Lf.
Proof.
  intros n a v H; unfold mkfun_entry in H.
  pose proof (get_par_spec mkfun_nm n) as Hp.
  destruct (par_of mkfun_nm n) as [r|] eqn:E; cbn [opt] in Hp.
  - pose proof (is_concrete_bt r) as Hc.
    destruct (concreteb r) eqn:Ec; cbn [bt] in Hc; crunch;
      first [left; eexists; split; [apply par_of_some; eassumption|split; [eassumption|reflexivity]] | right; reflexivity].
  - crunch.
Qed.

Lemma no_rows_inv : forall n a v, no_rows @ n @r a ==> v -> v = Lf.
Proof. intros n a v H; unfold no_rows in H; invert_eval. Qed.

Lemma fam_fun_inv : forall n a D, fam_fun @ n @r a ==> Sm D ->
  (exists r, n = Fk fun_nm r /\ D = fun_D r a) \/
  (exists r, n = Fk mkfun_nm r /\ concreteb r = true /\ D = mk_D r a).
Proof.
  intros n a D H; unfold fam_fun in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst. destruct (fun_entry_inv _ _ _ H1) as [[r [-> E']]|[_ E']]; inversion E'; subst.
    left; eauto.
  - destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst. destruct (mkfun_entry_inv _ _ _ H3) as [[r [-> [Hc E']]]|E']; inversion E'; subst.
      right; eauto.
    + apply no_rows_inv in H4; discriminate.
Qed.

(** ** The example ontology for functions *)

(** Empty: the guard admits nothing; the eliminator decodes a code
    argument, [Empty # code[A] = Sm A], and refuses anything that is not a
    code.  So [lam[swap[code A], Empty, A]] is ex falso. *)
Definition empty_elim : Combination := Eval cbn -[decode_p] in to_tree
  (star "n" (star "a" (star "U" (op decode_p @@ Ref "U")))).
Definition D_empty : Combination := ('K1 'KI) '* empty_elim.

(** A declaration whose guard admits nothing is sound, by typing and so by values. *)
Lemma nothing_decl_sound_by_typing : forall O n e, decl_sound_by_typing O n (('K1 'KI) '* e).
Proof.
  intros O n e C U V HC _.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  assert (H0 : ('K1 'KI) @ C ==> 'KI) by evaluate.
  pose proof (eval_deterministic _ _ HC' _ H0); discriminate.
Qed.
Lemma nothing_decl_sound : forall O n e, decl_sound O n (('K1 'KI) '* e).
Proof. intros; apply decl_sound_by_typing_values, nothing_decl_sound_by_typing. Qed.

Lemma empty_elim_eval : forall A n a, empty_elim @ n @r a @r code A ==> Sm A.
Proof.
  intros A n a; pose proof (decode_p_code A) as Hd; unfold empty_elim.
  split2; evaluate2; repeat first [eassumption | progress evaluate2].
Qed.
Definition mk_nat : Combination := 'tagged['tagger[nat_nm], mkn_nm].
Definition D_mkn : Combination := guard1 ('tagger[nat_nm]) '* ctor_elim nat_guard nat_nm.

Definition F_rows : list (Combination * Combination) :=
  O_rows ++ [(empty_nm, D_empty); (mkn_nm, D_mkn)].
Definition O_fun : Combination := rows_f F_rows fam_fun.

Lemma fam_fun_partial : forall n, exists p, fam_fun @ n ==> p.
Proof.
  intros n; unfold fam_fun, alt.
  pose proof (get_par_spec fun_nm n) as H1.
  destruct (par_of fun_nm n); cbn [opt] in H1;
  eexists; apply wait2_eval; unfold alt_prog, fun_entry; ev2.
Qed.

Lemma F_rows_fork : forall x y, lookup F_rows (Fk x y) = None.
Proof. intros; reflexivity. Qed.

Lemma O_fun_fun : forall r, O_fun @ Fk fun_nm r @r tp O_fun ==> Sm (fun_D r (tp O_fun)).
Proof.
  intros r; unfold O_fun; apply rows_f_miss; [apply F_rows_fork|].
  unfold fam_fun; apply alt_some; [apply fun_entry_hit|].
  destruct (fam_fun_partial (Fk fun_nm r)) as [p Hp]; unfold fam_fun, alt in Hp.
  eexists; apply wait2_eval; unfold alt_prog.
  pose proof (get_par_spec mkfun_nm (Fk fun_nm r)) as H1; cbn [par_of] in H1.
  destruct (combination_eq_dec mkfun_nm fun_nm) as [E|]; [discriminate|]; cbn [opt] in H1.
  unfold mkfun_entry; ev2.
Qed.

Lemma O_fun_static : forall n D, lookup F_rows n = Some D -> O_fun @ n @r tp O_fun ==> Sm D.
Proof.
  intros n D H; destruct (fam_fun_partial n) as [p Hp].
  unfold O_fun; eapply rows_f_hit; eassumption.
Qed.

Lemma O_fun_inv : forall n D, O_fun @ n @r tp O_fun ==> Sm D ->
  lookup F_rows n = Some D \/
  (exists r, n = Fk fun_nm r /\ D = fun_D r (tp O_fun)) \/
  (exists r, n = Fk mkfun_nm r /\ concreteb r = true /\ D = mk_D r (tp O_fun)).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; apply fam_fun_inv; exact HF.
Qed.

Theorem O_fun_sound : ontology_sound O_fun.
Proof.
  intros n D H.
  destruct (O_fun_inv n D H) as [HL|[[r [-> ->]]|[r [-> [Hc ->]]]]].
  - unfold F_rows, O_rows in HL; cbn [lookup app] in HL.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]);
      try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_fun_static; reflexivity|apply guard_of_pair].
    + unfold D_empty; apply nothing_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_fun_static; reflexivity|apply guard_of_pair].
  - apply decl_sound_by_typing_values, fun_decl_sound_by_typing.
  - eapply ctor_decl_sound; [cbn; exact Hc|apply O_fun_fun|apply guard_of_pair].
Qed.

Corollary O_fun_typing_sound : typing_sound O_fun.
Proof. apply evaluation_preserves_typing, O_fun_sound. Qed.

(** ** Typing of lambda programs *)

Local Notation "t ':' T" := (infer O_fun @ t ==> Sm T) (at level 70).

Theorem lam_typed : forall f F A B, f : F -> tp O_fun @ F @r A ==> Sm B ->
  names_concrete A -> names_concrete B -> lam f A B : Fun A B.
Proof.
  intros f F A B Hf HF HA HB; unfold lam, Fun.
  eapply infer_tag; [|exact Hf|apply O_fun_fun|].
  - assert (HL : label_pair (code A) (code B) = false)
      by (destruct (label_pair (code A) (code B)) eqn:E; [destruct (label_pair_K1 _ _ E) as [m Em];
          exfalso; exact (code_not_K1 B m Em)|reflexivity]).
    unfold fun_tag; cbn [concreteb]; rewrite (code_concrete A HA), (code_concrete B HB), HL; reflexivity.
  - eapply app2; [apply guard_of_pair|apply fun_guard_hit; exact HF].
Qed.


(** ** Forward rule for the abstract clause *)

Section AbsForward.
Variable O : Combination.
Local Opaque get_label resv label_tst elim_of.

Lemma ord_partial : forall rec, exists p, ord_cl @ rec ==> p.
Proof.
  intros rec; destruct (fk_partial rec) as [q Hq]; unfold ord_cl; eexists; ev2.
Qed.

Lemma abs_cl_fwd : forall n D U v, O @ n @r tp O ==> Sm D -> elim_of @ D @r n @r tp O @r U ==> v ->
  abs_cl O @ tp O @r n @r U ==> v.
Proof. intros n D U v H1 H2; unfold abs_cl. ev3. Qed.

Theorem tp_abs : forall n D U v, O @ n @r tp O ==> Sm D -> elim_of @ D @r n @r tp O @r U ==> v ->
  tp O @ 'label[n] @r U ==> v.
Proof.
  intros n D U v H1 H2.
  destruct (appl_inv _ _ _ _ (abs_cl_fwd n D U v H1 H2)) as [p [Hp Hq]].
  eapply eval_appl; [|exact Hq].
  pose proof (get_label_spec ('label[n])) as HL; cbn in HL.
  destruct (ord_partial (tp O)) as [q Hq'].
  unfold tp at 1; apply Z_unfold; fold (tp O).
  unfold tp_body; ev2.
Qed.

(** Forward rules for the ordinary clauses (stage 3). *)
Lemma tp_head_ord : forall F p, label_of F = None -> ord_cl @ tp O @r F ==> p -> tp O @ F ==> p.
Proof.
  intros F p HL H.
  pose proof (get_label_spec F) as Hg; rewrite HL in Hg; cbn [opt] in Hg.
  destruct (app2_inv _ _ _ _ H) as [q [Hq Hq']].
  destruct (abs_partial O (tp O)) as [a Ha].
  unfold tp at 1; apply Z_unfold; fold (tp O); unfold tp_body. ev3.
Qed.

Lemma ord_fork : forall X Y q, fk_cl @ tp O @r X @r Y ==> q -> ord_cl @ tp O @r Fk X Y ==> q.
Proof.
  intros X Y q H; destruct (fk_partial (tp O)) as [p Hp]; unfold ord_cl. ev3.
Qed.

Lemma fk_K1 : forall rec Y, fk_cl @ rec @r Lf @r Y ==> 'K1 (Sm Y).
Proof.
  intros rec Y; destruct (s_partial rec) as [a Ha]; destruct (tri_partial rec) as [b Hb].
  destruct (resv_spec Lf) as [r [Hr [_ Hiff]]]; specialize (Hiff eq_refl); subst r.
  unfold fk_cl; ev2.
Qed.

Lemma fk_S2 : forall rec G Y q, s_cl @ rec @r G @r Y ==> q -> fk_cl @ rec @r Sm G @r Y ==> q.
Proof.
  intros rec G Y q H; destruct (s_partial rec) as [a Ha]; destruct (tri_partial rec) as [b Hb].
  destruct (resv_spec (Sm G)) as [r [Hr [_ Hiff]]]; specialize (Hiff eq_refl); subst r.
  unfold fk_cl; ev3.
Qed.

Theorem tp_K1_fwd : forall Y U, tp O @ ('K1 Y) @r U ==> Sm Y.
Proof.
  intros Y U; eapply eval_appl; [apply tp_head_ord; [reflexivity|apply ord_fork, fk_K1]|evaluate].
Qed.

Lemma s_fwd : forall G H U V W R, tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Sm W ->
  tp O @ V @r W ==> Sm R -> s_cl @ tp O @r G @r H @r U ==> Sm R.
Proof. intros G H U V W R H1 H2 H3; unfold s_cl; ev3. Qed.

Theorem tp_S2_fwd : forall G H U V W R, label_of ('S2[G,H]) = None ->
  tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Sm W -> tp O @ V @r W ==> Sm R ->
  tp O @ 'S2[G,H] @r U ==> Sm R.
Proof.
  intros G H U V W R HL H1 H2 H3.
  destruct (appl_inv _ _ _ _ (s_fwd G H U V W R H1 H2 H3)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [exact HL|apply ord_fork, fk_S2; exact Hq]|exact Hq'].
Qed.

Theorem tp_leaf_fwd : forall U, tp O @ Lf @r U ==> Sm (Sm U).
Proof.
  intros U; eapply eval_appl; [apply tp_head_ord; [reflexivity|]|].
  - unfold ord_cl. destruct (fk_partial (tp O)) as [p Hp]. ev2.
  - unfold leaf_cl; evaluate.
Qed.
End AbsForward.

Lemma elim_of_fwd : forall g e n a U v, e @ n @r a @r U ==> v -> elim_of @ (g '* e) @r n @r a @r U ==> v.
Proof.
  intros g e n a U v H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]].
  destruct (appl_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]].
  eapply eval_appl; [eapply eval_appl; [eapply app2; [apply elim_of_pair|exact Hp1]|exact Hq1]|exact Hq].
Qed.

(** Function type elimination: [Fun[A,B] # A ==> Sm B], and nothing else. *)
Theorem Fun_elim : forall A B, tp O_fun @ Fun A B @r A ==> Sm B.
Proof. intros A B; eapply tp_abs; [apply O_fun_fun|apply elim_of_fwd, fun_elim_hit]. Qed.

Theorem Fun_elim_inv : forall A B X W, names_concrete A -> names_concrete B ->
  tp O_fun @ Fun A B @r X ==> Sm W -> X = A /\ W = B.
Proof.
  intros A B X W HA HB H; apply tp_inv in H; inversion H; subst;
    try (match goal with H' : label_of _ = None |- _ => cbn in H'; discriminate end).
  match goal with H1 : O_fun @ _ @r _ ==> Sm ?D |- _ =>
    pose proof (eval_deterministic _ _ H1 _ (O_fun_fun (Fk (code A) (code B)))) as E; inversion E; subst end.
  match goal with H2 : elim_of @ _ @r _ @r _ @r _ ==> _ |- _ =>
    apply elim_of_inv, fun_elim_inv in H2; destruct H2 as [A' [H3 [H4 ->]]] end.
  cbn [left_of right_of fun_tag] in *; rewrite decode_code in H3, H4; inversion H3; inversion H4; subst; auto.
Qed.

(** Applying a lambda program to an argument of its domain is typed. *)
Theorem lam_app_typed : forall f F A B a, infer O_fun @ f ==> Sm F -> tp O_fun @ F @r A ==> Sm B ->
  names_concrete A -> names_concrete B -> infer O_fun @ a ==> Sm A ->
  infer_expression O_fun @ (lam f A B @ a) ==> Sm B.
Proof.
  intros f F A B a Hf HF HA HB Ha.
  eapply ie_fork; [apply ie_stem; eapply lam_typed; eassumption|apply ie_stem; exact Ha|apply Fun_elim].
Qed.

(** Empty has no values. *)
Theorem Empty_no_values : forall v, ~ (v : Empty).
Proof.
  intros v H; destruct (no_junk O_fun v empty_nm H) as [f [F [D [_ [_ [_ [HD HG]]]]]]].
  pose proof (eval_deterministic _ _ HD _ (O_fun_static empty_nm D_empty eq_refl)) as E; inversion E; subst.
  destruct (app2_inv _ _ _ _ HG) as [g [Hg HC]].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  assert (H0 : ('K1 'KI) @ F ==> 'KI) by evaluate.
  pose proof (eval_deterministic _ _ HC _ H0); discriminate.
Qed.

(** ** Examples *)

Ltac by_run := apply (runp_sound 40); vm_done.

Definition neg : Combination := 'S2['I, 'K1 (ff '* tt)].
Definition succ_fn : Combination := Eval cbn -[mk_nat] in to_tree
  (star "x" (op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ Ref "x")))).
Definition mk_fun (A B : Combination) : Combination :=
  'tagged['tagger[fun_tag (code A) (code B)], Fk mkfun_nm (Fk (code A) (code B))].

Example id_Empty_typed : lam 'I Empty Empty : Fun Empty Empty. Proof. by_run. Qed.
Example const_Empty_Nat_typed : lam ('K1 zero) Empty Nat : Fun Empty Nat. Proof. by_run. Qed.
Example neg_typed : lam neg Bool Bool : Fun Bool Bool. Proof. by_run. Qed.
Example neg_app : infer_expression O_fun @ (lam neg Bool Bool @ tt) ==> Sm Bool. Proof. by_run. Qed.
Example neg_eval : lam neg Bool Bool @ tt ==> ff. Proof. by_run. Qed.
Example neg_wrong_arg : infer_expression O_fun @ (lam neg Bool Bool @ zero) ==> Lf. Proof. by_run. Qed.
Example neg_wrong_dom : infer O_fun @ lam neg Nat Bool ==> Lf. Proof. by_run. Qed.
Example succ_typed : lam succ_fn Nat Nat : Fun Nat Nat. Proof. by_run. Qed.
Example succ_app : infer_expression O_fun @ (lam succ_fn Nat Nat @ zero) ==> Sm Nat. Proof. by_run. Qed.
Example succ_eval : lam succ_fn Nat Nat @ zero ==> succ zero. Proof. by_run. Qed.
Example Fun_Empty_app : tp O_fun @ Fun Empty Empty @r Empty ==> Sm Empty. Proof. by_run. Qed.
Example Fun_Empty_refuses : tp O_fun @ Fun Empty Empty @r Nat ==> Lf. Proof. by_run. Qed.
Example mk_fun_typed : infer_expression O_fun @ (mk_fun Bool Bool @ neg) ==> Sm (Fun Bool Bool). Proof. by_run. Qed.
Example mk_fun_eval : mk_fun Bool Bool @ neg ==> lam neg Bool Bool. Proof. by_run. Qed.
Example mk_fun_refuses : infer_expression O_fun @ (mk_fun Bool Bool @ 'K) ==> Lf. Proof. by_run. Qed.
Example mk_fun_Empty : infer_expression O_fun @ (mk_fun Empty Empty @ 'I) ==> Sm (Fun Empty Empty). Proof. by_run. Qed.
