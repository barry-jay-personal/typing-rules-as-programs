(** * Step 82, stage 3, part 2: lists, and iterations without the wrapper.

    [List A = label[list_tag[code A]]], [list_tag[c] = Fk list_nm c]:

      nil[A]        = tagged[fst, list_tag[code A]]                nil @ (n*s) = n
      cons[A,x,xs]  = tagged[S2[snd, K1 (x*xs)], list_tag[code A]]  cons @ (n*s) = s @ (x*xs)

    declaration at list_tag[r] (A = decode r, L = label[Fk list_nm r]):
      guard  admits fst and S2[snd, K1 (A * L)]
      elim   L # (B * S) = Sm B   when  S # (A * L) ==> Sm B

    The constructor [mk_cons[A] = tagged[tagger[list_tag[code A]], Fk mkcons_nm (code A)]]
    builds cells at run time.

    The iteration [lit[A,C,g]] is the left fold of [g] over a list, with
    the state a plain pair [xs * c] of type [T = List A * C]:

      lit[A,C,g] = fix_update[b]
      b @ r      = mk_update @ wait3[sp_body, code T, step r, identity_update]
      step r @ x = fst x @ (x * \p. r @ (snd p * g @ (fst p * snd x)))

    so the step acts through special_type at [T]. *)

From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types.
From Stdlib Require Import String List Bool Lia.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete.

Definition list_nm : Combination := Nat.iter 14 Sm Lf.
Definition mkcons_nm : Combination := Nat.iter 15 Sm Lf.
Definition list_tag (c : Combination) : Combination := Fk list_nm c.
Definition List (A : Combination) : Combination := 'label[list_tag (code A)].
Definition nil (A : Combination) : Combination := 'tagged['fst, list_tag (code A)].
Definition cons (A x xs : Combination) : Combination := 'tagged['S2['snd, 'K1 (x '* xs)], list_tag (code A)].

(** ** The declaration *)

Definition LL (r : Term) : Term := lab (Val Lf @@ Val list_nm @@ r).

Definition lg_prog : Combination := Eval cbn -[equal decode_p list_nm] in to_tree
  (star "r" (star "C"
    (''onStem1 (star "A" (op equal @@ Ref "C" @@ Val 'fst @@ Val 'K
                            @@ (op equal @@ Ref "C" @@ ''S2[Val 'snd, ''K1 (Ref "A" ''* LL (Ref "r"))])))
       @@ (op decode_p @@ Ref "r")))).

Definition le_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s list_nm] in to_tree
  (star "r" (star "n" (star "a" (star "U"
    (''onStem1 (star "A"
        (op equal @@ Ref "U" @@ (PN (Ref "U") ''* PS (Ref "U"))
           @@ star "U2" (''onStem1 (star "R" (op equal @@ Ref "R" @@ PN (Ref "U2")
                                                 @@ (Val Lf @@ PN (Ref "U2")) @@ Val Lf))
                           @@ (Ref "a" @@ PS (Ref "U2") @@ (Ref "A" ''* LL (Ref "r"))))
           @@ Val ('K1 Lf) @@ Ref "U"))
       @@ (op decode_p @@ Ref "r")))))).

Definition list_elim : Combination := name_elim le_prog.
Definition D_list (r : Combination) : Combination := 'wait[lg_prog, r] '* list_elim.

Definition list_entry : Combination := Eval cbn -[get_par list_nm list_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (Val Lf @@ (''wait[Val lg_prog, Ref "r"] ''* Val list_elim)))
       @@ (op (get_par list_nm) @@ Ref "n")))).

(** The cell constructor, at [Fk mkcons_nm r] with [r] concrete. *)
Definition D_mkcons (r : Combination) : Combination :=
  guard1 ('tagger[Fk list_nm r]) '* ctor_elim ('wait[lg_prog, r]) (Fk list_nm r).

Definition mkcons_entry : Combination := Eval cbn -[get_par is_concrete list_nm mkcons_nm] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r"
        (op is_concrete @@ Ref "r"
           @@ (Val Lf @@ (''wait[Val equal, tagger_t (Val Lf @@ Val list_nm @@ Ref "r")]
                          ''* ''wait2[Val ctor_prog, ''wait[Val lg_prog, Ref "r"], Val Lf @@ Val list_nm @@ Ref "r"]))
           @@ Val Lf))
       @@ (op (get_par mkcons_nm) @@ Ref "n")))).

Definition mk_cons (A : Combination) : Combination :=
  'tagged['tagger[list_tag (code A)], Fk mkcons_nm (code A)].

(** [cons_fn[A] @ (x * xs) = cons[A,x,xs]], through the constructor. *)
Definition cons_fn (A : Combination) : Combination := Eval cbn -[mk_cons] in to_tree
  (star "p" (op (mk_cons A) @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ Ref "p")))).

Definition L_rows : list (Combination * Combination) := (O_rows ++ [(mkn_nm, D_mkn)])%list.
Definition L_fam : Combination := alt upd_fam (alt list_entry (alt mkcons_entry no_rows)).
Definition O_list : Combination := rows_f L_rows L_fam.

(** ** The iteration *)

Definition step_t (g r : Term) : Term := star "x"
  ((Val 'fst @@ Ref "x") @@
     (Ref "x" ''* star "p" (r @@ ((Val 'snd @@ Ref "p") ''* (g @@ ((Val 'fst @@ Ref "p") ''* (Val 'snd @@ Ref "x"))))))).

Definition lit_b (A C g : Combination) : Combination := Eval cbn -[mk_update sp_body code identity_update List] in to_tree
  (star "r" (op mk_update @@ w3 (Val (code (List A '* C))) (step_t (Val g) (Ref "r")) (Val identity_update))).

Definition lit (A C g : Combination) : Combination := fix_update (lit_b A C g).

(** The programs, each with one type parameter (or two for map), as a
    Rocq parameter whose code is built by [code]. *)
Definition snd_after (f : Term) : Term := star "q" (Val 'snd @@ (f @@ Ref "q")).
Definition rev_append (A : Combination) : Combination := Eval cbn -[lit cons_fn List] in to_tree
  (snd_after (Val (lit A (List A) (cons_fn A)))).
Definition reverse (A : Combination) : Combination := Eval cbn -[rev_append nil] in to_tree
  (star "xs" (Val (rev_append A) @@ (Ref "xs" ''* Val (nil A)))).
Definition append (A : Combination) : Combination := Eval cbn -[rev_append reverse] in to_tree
  (star "q" (Val (rev_append A) @@ ((Val (reverse A) @@ (Val 'fst @@ Ref "q")) ''* (Val 'snd @@ Ref "q")))).
Definition succ_step : Combination := Eval cbn -[mk_nat] in to_tree
  (star "q" (op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ (Val 'snd @@ Ref "q"))))).
Definition length (A : Combination) : Combination := Eval cbn -[lit succ_step zero] in to_tree
  (star "xs" (Val 'snd @@ (Val (lit A Nat succ_step) @@ (Ref "xs" ''* Val zero)))).
Definition filter_step (A p : Combination) : Combination := Eval cbn -[cons_fn] in to_tree
  (star "q" ((Val p @@ (Val 'fst @@ Ref "q")) @@ ((Val (cons_fn A) @@ Ref "q") ''* (Val 'snd @@ Ref "q")))).
Definition filter (A p : Combination) : Combination := Eval cbn -[lit reverse filter_step nil List] in to_tree
  (star "xs" (Val (reverse A) @@ (Val 'snd @@ (Val (lit A (List A) (filter_step A p)) @@ (Ref "xs" ''* Val (nil A)))))).
Definition map_step (B f : Combination) : Combination := Eval cbn -[cons_fn] in to_tree
  (star "q" (Val (cons_fn B) @@ ((Val f @@ (Val 'fst @@ Ref "q")) ''* (Val 'snd @@ Ref "q")))).
Definition map (A B f : Combination) : Combination := Eval cbn -[lit reverse map_step nil List] in to_tree
  (star "xs" (Val (reverse B) @@ (Val 'snd @@ (Val (lit A (List B) (map_step B f)) @@ (Ref "xs" ''* Val (nil B)))))).
Definition foldright (A C g : Combination) : Combination := Eval cbn -[lit reverse] in to_tree
  (star "q" (Val 'snd @@ (Val (lit A C g) @@ ((Val (reverse A) @@ (Val 'fst @@ Ref "q")) ''* (Val 'snd @@ Ref "q"))))).

Ltac by_run := apply (runp_sound 40); vm_done.

Definition one := succ zero.
Definition two := succ one.
Definition l12 := cons Nat one (cons Nat two (nil Nat)).
Definition l0 := cons Nat zero (nil Nat).

(** ** Inversions of the declaration programs *)

Local Opaque lg_prog le_prog.

Lemma lg_inv : forall r C, 'wait[lg_prog, r] @ C ==> 'K ->
  exists A, decode r = Some A /\ (C = 'fst \/ C = 'S2['snd, 'K1 (A '* 'label[Fk list_nm r])]).
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent lg_prog. unfold lg_prog in H. Local Opaque lg_prog.
  pose proof (decode_p_eval r) as Hd.
  destruct (decode r) as [A|]; cbn [opt] in Hd; [|crunch].
  exists A; split; [reflexivity|].
  pose proof (equal_bt C 'fst) as E1; pose proof (equal_bt C ('S2['snd, 'K1 (A '* 'label[Fk list_nm r])])) as E2.
  inv_out E1; inv_out E2; dedup.
  destruct (combination_eq_dec C 'fst); [left; assumption|].
  destruct (combination_eq_dec C ('S2['snd, 'K1 (A '* 'label[Fk list_nm r])])); [right; assumption|].
  cbn [bt] in *; crunch.
Qed.

Lemma lg_hit : forall A C, C = 'fst \/ C = 'S2['snd, 'K1 (A '* 'label[Fk list_nm (code A)])] ->
  'wait[lg_prog, code A] @ C ==> 'K.
Proof.
  intros A C HC; apply wait_eval. Local Transparent lg_prog. unfold lg_prog. Local Opaque lg_prog.
  pose proof (decode_p_code A) as Hd.
  destruct HC as [->| ->].
  - pose proof (equal_eq 'fst) as He.
    assert (Hn : 'fst <> 'S2['snd, 'K1 (A '* 'label[Fk list_nm (code A)])]) by discriminate.
    pose proof (equal_neq _ _ Hn) as He2; ev2.
  - assert (Hn : 'S2['snd, 'K1 (A '* 'label[Fk list_nm (code A)])] <> 'fst) by discriminate.
    pose proof (equal_neq _ _ Hn) as He; pose proof (equal_eq ('S2['snd, 'K1 (A '* 'label[Fk list_nm (code A)])])) as He2; ev2.
Qed.

Lemma le_inv : forall r n a U V, 'wait[le_prog, r] @ n @r a @r U ==> Sm V ->
  exists A S, decode r = Some A /\ U = V '* S /\ a @ S @r (A '* 'label[Fk list_nm r]) ==> Sm V.
Proof.
  intros r n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent le_prog. unfold le_prog in Hp1. Local Opaque le_prog.
  pose proof (decode_p_eval r) as Hd.
  destruct (decode r) as [A|]; cbn [opt] in Hd; crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs; try discriminate.
  eq_case2; crunch; use_specs; try discriminate.
  all: match goal with E : ?U = _ |- _ => is_var U; rewrite E end.
  all: do 2 eexists; split; [reflexivity|split; [reflexivity|eapply eval_appl; eassumption]].
Qed.

Lemma carrier_snd_inv : forall O c P, infer O @ c ==> Sm ('S2['snd, 'K1 P]) ->
  exists p, c = 'S2['snd, 'K1 p] /\ infer O @ p ==> Sm P.
Proof.
  intros O c P H.
  destruct (type_Fk_inv O _ _ _ H) as [[m E]|[x [y [-> [_ [Hx [Hy _]]]]]]]; [discriminate|].
  destruct (type_Sm_inv O _ _ Hx) as [x' [-> Hx']].
  apply (concrete_type_forces O) in Hx'; [subst x'|reflexivity].
  destruct (type_Fk_inv O _ _ _ Hy) as [[m E]|[y1 [p [-> [_ [Hy1 [Hp _]]]]]]]; [discriminate|].
  pose proof (type_Lf_inv O _ Hy1) as ->.
  exists p; auto.
Qed.

(** The list declaration is sound by values, for every ontology and code. *)
Theorem list_decl_sound : forall O r, decl_sound O (list_tag r) (D_list r).
Proof.
  intros O r k C U V c v w HC HE Hc Hv Hk Hw.
  destruct (app2_inv _ _ _ _ HC) as [g [Hg HC']].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  destruct (lg_inv _ _ HC') as [A [HA [->| ->]]];
  apply elim_of_inv in HE; unfold list_elim in HE;
  apply name_elim_iff, le_inv in HE; cbn [right_of list_tag] in HE; destruct HE as [A' [S [HA' [-> HS]]]];
  rewrite HA in HA'; inversion HA'; subst A'.
  - apply (concrete_type_forces O) in Hc; [subst c|reflexivity].
    destruct (pair_type_inv O v V S Hv) as [b [s [-> [Hb Hs]]]].
    apply evaln_eval in Hw; pose proof (eval_deterministic _ _ Hw _ (fst_pair b s)) as ->; exact Hb.
  - destruct (carrier_snd_inv O c _ Hc) as [p [-> Hp]].
    destruct (pair_type_inv O v V S Hv) as [b [s [-> [Hb Hs]]]].
    destruct (evaln_S2_inv _ _ _ _ _ Hw) as [j [p1 [p2 [Hj [H1 [H2 H3]]]]]].
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H1) _ (snd_pair b s)) as ->.
    assert (E2 : ('K1 p) @ (b '* s) ==> p) by evaluate.
    pose proof (eval_deterministic _ _ (evaln_eval _ _ _ H2) _ E2) as ->.
    eapply Hk; [|exact H3|exact Hs|exact Hp|exact HS]; lia.
Qed.

(** ** The family entries *)

Lemma list_entry_inv : forall n a D, list_entry @ n @r a ==> Sm D -> exists r, n = list_tag r /\ D = D_list r.
Proof.
  intros n a D H; unfold list_entry in H.
  pose proof (get_par_spec list_nm n) as Hp.
  destruct (par_of list_nm n) as [r|] eqn:E; cbn [opt] in Hp; crunch.
  eexists; split; [apply par_of_some; eassumption|reflexivity].
Qed.

Lemma list_entry_hit : forall r a, list_entry @ list_tag r @r a ==> Sm (D_list r).
Proof.
  intros r a; unfold list_entry.
  pose proof (get_par_spec list_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec list_nm list_nm); [|contradiction]; cbn [opt] in Hp. ev2.
Qed.

Lemma list_entry_partial : forall n, exists p, list_entry @ n ==> p.
Proof.
  intros n; pose proof (get_par_spec list_nm n) as Hp.
  destruct (par_of list_nm n); cbn [opt] in Hp; unfold list_entry; eexists; ev2.
Qed.

Lemma list_entry_miss : forall n a, par_of list_nm n = None -> list_entry @ n @r a ==> Lf.
Proof.
  intros n a E; unfold list_entry; pose proof (get_par_spec list_nm n) as Hp; rewrite E in Hp; cbn [opt] in Hp; ev2.
Qed.

Lemma mkcons_entry_inv : forall n a D, mkcons_entry @ n @r a ==> Sm D ->
  exists r, n = Fk mkcons_nm r /\ concreteb r = true /\ D = D_mkcons r.
Proof.
  intros n a D H; unfold mkcons_entry in H.
  pose proof (get_par_spec mkcons_nm n) as Hp.
  destruct (par_of mkcons_nm n) as [r|] eqn:E; cbn [opt] in Hp.
  - pose proof (is_concrete_bt r) as Hc.
    destruct (concreteb r) eqn:Ec; cbn [bt] in Hc; crunch;
      eexists; split; [apply par_of_some; eassumption|split; [eassumption|reflexivity]].
  - crunch.
Qed.

Lemma mku_entry_miss : forall n a, n <> mku_nm -> mku_entry @ n @r a ==> Lf.
Proof. intros n a Hn; unfold mku_entry; pose proof (equal_neq _ _ Hn) as He; ev2. Qed.

Lemma upd_fam_miss : forall n a, n <> update_nm -> n <> mku_nm -> upd_fam @ n @r a ==> Lf.
Proof.
  intros n a H1 H2; unfold upd_fam.
  apply alt_none; [apply upd_entry_miss; exact H1|].
  apply alt_none; [apply mku_entry_miss; exact H2|]. unfold no_rows; evaluate.
Qed.

Lemma alt_partial : forall p q n, (exists r, p @ n ==> r) -> exists r, alt p q @ n ==> r.
Proof.
  intros p q n [r Hr]; unfold alt; eexists; apply wait2_eval; unfold alt_prog; ev2.
Qed.

Lemma L_fam_inv : forall n a D, L_fam @ n @r a ==> Sm D ->
  (n = update_nm /\ D = D_upd update_nm a) \/ (n = mku_nm /\ D = D_mku a) \/
  (exists r, n = list_tag r /\ D = D_list r) \/
  (exists r, n = Fk mkcons_nm r /\ concreteb r = true /\ D = D_mkcons r).
Proof.
  intros n a D H; unfold L_fam in H.
  destruct (alt_inv _ _ _ _ _ H) as [[D' [H1 E]]|[[H1 H2]|[x [y [_ E]]]]]; [|..|discriminate].
  - inversion E; subst; destruct (upd_fam_inv _ _ _ H1) as [[-> ->]|[-> ->]]; auto.
  - destruct (alt_inv _ _ _ _ _ H2) as [[D' [H3 E]]|[[H3 H4]|[x [y [_ E]]]]]; [|..|discriminate].
    + inversion E; subst; right; right; left; eapply list_entry_inv; exact H3.
    + destruct (alt_inv _ _ _ _ _ H4) as [[D' [H5 E]]|[[H5 H6]|[x [y [_ E]]]]]; [|..|discriminate].
      * inversion E; subst; right; right; right; eapply mkcons_entry_inv; exact H5.
      * apply no_rows_inv in H6; discriminate.
Qed.

Lemma O_list_inv : forall n D, O_list @ n @r tp O_list ==> Sm D ->
  lookup L_rows n = Some D \/
  (n = update_nm /\ D = D_upd update_nm (tp O_list)) \/ (n = mku_nm /\ D = D_mku (tp O_list)) \/
  (exists r, n = list_tag r /\ D = D_list r) \/
  (exists r, n = Fk mkcons_nm r /\ concreteb r = true /\ D = D_mkcons r).
Proof.
  intros n D H; destruct (rows_f_inv _ _ _ _ _ H) as [[D' [HL E]]|[_ HF]].
  - inversion E; subst; left; exact HL.
  - right; apply L_fam_inv; exact HF.
Qed.

Lemma L_fam_partial : forall n, exists p, L_fam @ n ==> p.
Proof. intros n; apply alt_partial, upd_fam_partial. Qed.

Lemma O_list_static : forall n D, lookup L_rows n = Some D -> O_list @ n @r tp O_list ==> Sm D.
Proof.
  intros n D H; destruct (L_fam_partial n) as [p Hp]; unfold O_list; eapply rows_f_hit; eassumption.
Qed.

Lemma O_list_update : O_list @ update_nm @r tp O_list ==> Sm (D_upd update_nm (tp O_list)).
Proof.
  unfold O_list; apply rows_f_miss; [reflexivity|]. unfold L_fam; apply alt_some; [apply upd_fam_update|].
  apply alt_partial, list_entry_partial.
Qed.

Lemma O_list_list : forall r, O_list @ list_tag r @r tp O_list ==> Sm (D_list r).
Proof.
  intros r; unfold O_list; apply rows_f_miss; [reflexivity|]. unfold L_fam.
  apply alt_none; [apply upd_fam_miss; discriminate|].
  apply alt_some; [apply list_entry_hit|]. apply alt_partial.
  pose proof (get_par_spec mkcons_nm (list_tag r)) as Hp; cbn [par_of list_tag] in Hp.
  destruct (combination_eq_dec mkcons_nm list_nm) as [E|]; [discriminate|]; cbn [opt] in Hp.
  unfold mkcons_entry; eexists; ev2.
Qed.

Theorem O_list_sound : ontology_sound O_list.
Proof.
  intros n D H.
  destruct (O_list_inv n D H) as [HL|[[-> ->]|[[-> ->]|[[r [-> ->]]|[r [-> [Hc ->]]]]]]].
  - unfold L_rows, O_rows in HL; cbn [lookup app] in HL.
    repeat (destruct (combination_eq_dec _ n) as [<-|]; [inversion HL; subst|]); try discriminate.
    + apply bool_decl_sound.
    + apply nat_decl_sound.
    + eapply ctor_decl_sound; [reflexivity|apply O_list_static; reflexivity|apply guard_of_pair].
    + eapply ctor_decl_sound; [reflexivity|apply O_list_static; reflexivity|apply guard_of_pair].
  - apply upd_decl_sound_g, O_list_update.
  - apply mku_decl_sound_g, O_list_update.
  - apply list_decl_sound.
  - eapply ctor_decl_sound; [cbn; exact Hc|apply O_list_list|apply guard_of_pair].
Qed.

Corollary O_list_typing_sound : typing_sound O_list.
Proof. apply evaluation_preserves_typing, O_list_sound. Qed.

(** ** Typings of nil and cons *)

Local Notation "t ':' T" := (infer O_list @ t ==> Sm T) (at level 70).

Lemma list_tag_concrete : forall A, names_concrete A -> concreteb (list_tag (code A)) = true.
Proof.
  intros A HA; unfold list_tag; cbn [concreteb]; rewrite (code_concrete A HA).
  assert (E : label_pair list_nm (code A) = false) by reflexivity. rewrite E; reflexivity.
Qed.

Theorem nil_typed : forall A, names_concrete A -> nil A : List A.
Proof.
  intros A HA; eapply infer_tag; [apply list_tag_concrete, HA| |apply O_list_list|].
  - apply concrete_is_self_typed; reflexivity.
  - eapply app2; [apply guard_of_pair|apply lg_hit; auto].
Qed.

Theorem cons_typed : forall A x xs, names_concrete A -> x : A -> xs : List A -> cons A x xs : List A.
Proof.
  intros A x xs HA Hx Hxs; eapply infer_tag; [apply list_tag_concrete, HA| |apply O_list_list|].
  - apply infer_fork; [reflexivity|apply concrete_is_self_typed; reflexivity| |reflexivity].
    apply infer_fork; [reflexivity|apply infer_leaf|apply pair_typed; [exact Hx|exact Hxs]|reflexivity].
  - eapply app2; [apply guard_of_pair|apply lg_hit; right; reflexivity].
Qed.

(** ** Examples, by computation *)

Definition l210 := cons Nat two (cons Nat one (cons Nat zero (nil Nat))).
Definition l120 := cons Nat one (cons Nat two (cons Nat zero (nil Nat))).
Definition l21 := cons Nat two (cons Nat one (nil Nat)).
Definition lb := cons Bool tt (cons Bool ff (cons Bool tt (nil Bool))).
Definition ltt := cons Bool tt (cons Bool tt (nil Bool)).

Example nil_Nat : nil Nat : List Nat. Proof. by_run. Qed.
Example l12_typed : l12 : List Nat. Proof. by_run. Qed.
Example cons_wrong : infer O_list @ cons Nat tt (nil Nat) ==> Lf. Proof. by_run. Qed.
Example mk_update_typed : mk_update : 'label[mku_nm]. Proof. by_run. Qed.
Example cons_fn_typed : infer_expression O_list @ (cons_fn Nat @ (zero '* nil Nat)) ==> Sm (List Nat). Proof. by_run. Qed.
Example cons_fn_eval : cons_fn Nat @ (zero '* nil Nat) ==> l0. Proof. by_run. Qed.

Example lit_typed : lit Nat (List Nat) (cons_fn Nat) : Update. Proof. by_run. Qed.
Example rev_append_eval : rev_append Nat @ (l12 '* l0) ==> l210. Proof. by_run. Qed.
Example rev_append_typed : infer_expression O_list @ (rev_append Nat @ (l12 '* l0)) ==> Sm (List Nat). Proof. by_run. Qed.
Example reverse_eval : reverse Nat @ l12 ==> l21. Proof. by_run. Qed.
Example reverse_typed : infer_expression O_list @ (reverse Nat @ l12) ==> Sm (List Nat). Proof. by_run. Qed.
Example append_eval : append Nat @ (l12 '* l0) ==> l120. Proof. by_run. Qed.
Example append_typed : infer_expression O_list @ (append Nat @ (l12 '* l0)) ==> Sm (List Nat). Proof. by_run. Qed.
Example length_eval : length Nat @ l120 ==> succ two. Proof. by_run. Qed.
Example length_typed : infer_expression O_list @ (length Nat @ l120) ==> Sm Nat. Proof. by_run. Qed.
Example filter_eval : filter Bool 'I @ lb ==> ltt. Proof. by_run. Qed.
Example filter_typed : infer_expression O_list @ (filter Bool 'I @ lb) ==> Sm (List Bool). Proof. by_run. Qed.
Example map_eval : map Nat Nat succ_fn @ l0 ==> cons Nat one (nil Nat). Proof. by_run. Qed.
Example map_typed : infer_expression O_list @ (map Nat Nat succ_fn @ l12) ==> Sm (List Nat). Proof. by_run. Qed.
Example foldright_eval : foldright Nat (List Nat) (cons_fn Nat) @ (l12 '* l0) ==> l120. Proof. by_run. Qed.
Example foldright_typed : infer_expression O_list @ (foldright Nat (List Nat) (cons_fn Nat) @ (l12 '* l0)) ==> Sm (List Nat).
Proof. by_run. Qed.

(** Data of a state-like type: append on a list whose elements are pairs
    of lists.  The step acts only at the top (the default branch is the
    identity), and the element type differs from the state type
    [List A * List A], so the elements are carried unchanged. *)
Definition LP := List Nat '* List Nat.
Definition pe := l12 '* l0.
Definition lpe := cons LP pe (nil LP).
Example append_pairs_eval : append LP @ (lpe '* lpe) ==> cons LP pe (cons LP pe (nil LP)). Proof. by_run. Qed.
Example append_pairs_typed : infer_expression O_list @ (append LP @ (lpe '* lpe)) ==> Sm (List LP). Proof. by_run. Qed.

(** A state passed as data: the iteration at [List Nat * List Nat] applied
    to a value of that type fires, as it should; a non-state is left alone. *)
Example lit_on_nonstate : lit Nat (List Nat) (cons_fn Nat) @ l12 ==> l12. Proof. by_run. Qed.
