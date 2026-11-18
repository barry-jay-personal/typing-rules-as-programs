(** * Step 82, stage 4, part 2: queries with codes (part 1 of 3 since stage 6: definitions and guard inversions).

    [Query[B] = label[query_tag[code B]]], [query_tag[c] = Fk query_nm c].
    The declaration at [query_tag[r]] (B = decode r):

      elim   Query[B] # U = Sm B      for every U
      guard  admits (any of)
             K1 B                                    constant queries   K1 b, b : B
             S2[Query[F], Query[V]]  with F # V ==> Sm B          applicative queries
             wait3[sp_body, code T, F, Query[B]]  with F # T ==> Sm B   specialised queries
             S2[Query[Query[B]], I]                  diagonal queries   (Step 89)

    Step 89: there is no recursive (fixfunction) clause.  A recursive
    query is built from a recursive update ([rec_query], below).

    A specialised query [special_query[T,f,d]] applies [f] to an argument of
    type T and the query [d] to any other.  The declaration is sound by
    values. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.

Definition query_nm : Combination := Nat.iter 22 Sm Lf.
Definition query_tag (c : Combination) : Combination := Fk query_nm c.
Definition Query (B : Combination) : Combination := 'label[query_tag (code B)].

Definition QN (r : Term) : Term := Val Lf @@ Val query_nm @@ r.
Definition QL (r : Term) : Term := lab (QN r).

(** constant: [C = K1 B] *)
Definition qK_prog : Combination := Eval cbn -[equal decode_p] in to_tree
  (star "r" (star "C" (''onStem1 (star "B" (op equal @@ Ref "C" @@ (Val 'K @@ Ref "B"))) @@ (op decode_p @@ Ref "r")))).

(** applicative: [C = S2[Query[F], Query[V]]] with [F # V ==> Sm B] *)
Definition PF (C : Term) := pr (pr (pr (ps (pl C)))).
Definition PV (C : Term) := pr (pr (pr (pr C))).
Definition qS_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s query_nm] in to_tree
  (star "r" (star "a" (star "C"
    (op equal @@ Ref "C" @@ ''S2[QL (PF (Ref "C")), QL (PV (Ref "C"))]
       @@ star "C2" (''onStem1 (star "F" (''onStem1 (star "V" (''onStem1 (star "B"
                  (''onStem1 (star "R" (op equal @@ Ref "R" @@ Ref "B")) @@ (Ref "a" @@ Ref "F" @@ Ref "V")))
                @@ (op decode_p @@ Ref "r")))
              @@ (op decode_p @@ PV (Ref "C2"))))
            @@ (op decode_p @@ PF (Ref "C2")))
       @@ Val ('K1 'KI) @@ Ref "C")))).

(** specialised: [C = wait3[sp_body, cT, F, Query[B]]] with [F # T ==> Sm B] *)
Definition qsp_prog : Combination := Eval cbn -[equal decode_p get_l get_r get_s query_nm] in to_tree
  (star "r" (star "a" (star "C"
    (op equal @@ Ref "C" @@ w3 (P3 (Ref "C")) (P2 (Ref "C")) (P1 (Ref "C"))
       @@ star "C2" (''onStem1 (star "T" (''onStem1 (star "B"
             (op equal @@ P1 (Ref "C2") @@ QL (Ref "r")
                @@ star "C3" (''onStem1 (star "R" (op equal @@ Ref "R" @@ Ref "B"))
                               @@ (Ref "a" @@ P2 (Ref "C3") @@ Ref "T"))
                @@ Val ('K1 'KI) @@ Ref "C2"))
               @@ (op decode_p @@ Ref "r")))
           @@ (op decode_p @@ P3 (Ref "C2")))
       @@ Val ('K1 'KI) @@ Ref "C")))).

(** triage: [C = wait3[tq_body, B, Query[B], Query[Query[B]] * Query[Query[B]]]],
    the last component the fork of the fork case [g] and the tag case [t].
    The carrier [tq_body b s (Fk g t)] passes a tagged value [tagged[c,n]]
    its carrier and its name, [t @ c @ n]; it never passes the bare label.
    Names are concrete, hence typed.  A separate tag case is needed: every
    pair of typed values is the pair of children of an untagged fork, so a
    tag passed to the fork case would be confused with some fork. *)
Definition tq_body : Combination := Eval cbn -[get_tagged get_l get_r] in to_tree
  (star "b" (star "s" (star "gt" (star "x"
    (''triage[star "x2" (''triage[Ref "b", Ref "s", op get_l @@ Ref "gt"] @@ Ref "x2"),
              star "p" (star "x2" (op get_r @@ Ref "gt" @@ (op get_l @@ Ref "p") @@ (op get_r @@ Ref "p"))),
              Val ('K1 ('K1 ('K1 Lf)))]
       @@ (op get_tagged @@ Ref "x") @@ Ref "x"))))).

Definition W3 (M N x y : Term) : Term := ''S2[''S2[''S2[''S2[''K1 M, ''K1 N], ''K1 x], ''K1 y], ''I].
Definition QQN (r : Term) : Term := Val Lf @@ Val query_nm @@ (Val Lf @@ Val (Fk Lf Lf) @@ QN r).

Definition gtq_prog : Combination := Eval cbn -[equal decode_p query_nm tq_body] in to_tree
  (star "r" (star "C"
    (''onStem1 (star "B" (op equal @@ Ref "C" @@ W3 (Val tq_body) (Ref "B") (QL (Ref "r"))
                                     (Val Lf @@ lab (QQN (Ref "r")) @@ lab (QQN (Ref "r")))))
       @@ (op decode_p @@ Ref "r")))).

(** diagonal (Step 89): [C = S2[Query[Query[B]], I]].  A diagonal query
    [Sq[B, g, I]] with [g : Query[Query[B]]] applies the query [g @ x] to [x]. *)
Definition gdq_prog : Combination := Eval cbn -[equal query_nm] in to_tree
  (star "r" (star "C" (op equal @@ Ref "C" @@ ''S2[lab (QQN (Ref "r")), Val 'I]))).

Definition qe_prog : Combination := Eval cbn -[decode_p] in to_tree
  (star "r" (star "n" (star "a" (star "U" (op decode_p @@ Ref "r"))))).

Definition query_guard (r a : Combination) : Combination :=
  or_g ('wait[qK_prog, r]) (or_g ('wait2[qS_prog, r, a]) (or_g ('wait2[qsp_prog, r, a])
    (or_g ('wait[gdq_prog, r]) ('wait[gtq_prog, r])))).
Definition query_elim : Combination := name_elim qe_prog.
Definition D_query (r a : Combination) : Combination := query_guard r a '* query_elim.

Definition query_entry : Combination := Eval cbn -[get_par query_nm is_concrete query_elim] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (op is_concrete @@ Ref "r" @@ (Val Lf @@
       (''wait2[Val or_prog, ''wait[Val qK_prog, Ref "r"],
          ''wait2[Val or_prog, ''wait2[Val qS_prog, Ref "r", Ref "a"],
            ''wait2[Val or_prog, ''wait2[Val qsp_prog, Ref "r", Ref "a"],
                                 ''wait2[Val or_prog, ''wait[Val gdq_prog, Ref "r"],
                                                      ''wait[Val gtq_prog, Ref "r"]]]]]
        ''* Val query_elim)) @@ Val Lf))
       @@ (op (get_par query_nm) @@ Ref "n")))).

(** The query constructor at [Fk mkq_nm r], [r] concrete:
    [mk_query[B] @ c = tagged[c, query_tag[code B]]] when the query guard admits the type of [c]. *)
Definition mkq_nm : Combination := Nat.iter 23 Sm Lf.
Definition D_mkq (r a : Combination) : Combination :=
  guard1 ('tagger[query_tag r]) '* ctor_elim (query_guard r a) (query_tag r).
Definition mkq_entry : Combination := Eval cbn -[get_par query_nm mkq_nm is_concrete] in to_tree
  (star "n" (star "a"
    (''onStem1 (star "r" (op is_concrete @@ Ref "r" @@ (Val Lf @@
       (''wait[Val equal, tagger_t (QN (Ref "r"))]
        ''* ''wait2[Val ctor_prog,
             ''wait2[Val or_prog, ''wait[Val qK_prog, Ref "r"],
              ''wait2[Val or_prog, ''wait2[Val qS_prog, Ref "r", Ref "a"],
                ''wait2[Val or_prog, ''wait2[Val qsp_prog, Ref "r", Ref "a"],
                                 ''wait2[Val or_prog, ''wait[Val gdq_prog, Ref "r"],
                                                      ''wait[Val gtq_prog, Ref "r"]]]]],
             QN (Ref "r")])) @@ Val Lf))
       @@ (op (get_par mkq_nm) @@ Ref "n")))).
Definition mk_query (B : Combination) : Combination := 'tagged['tagger[query_tag (code B)], Fk mkq_nm (code B)].

Definition Q_fam : Combination := alt L_fam (alt query_entry (alt mkq_entry no_rows)).
Definition O_q : Combination := rows_f G_rows Q_fam.

(** Constructors *)
Definition Kq (B b : Combination) := 'tagged['K1 b, query_tag (code B)].
Definition Sq (B g f : Combination) := 'tagged['S2[g, f], query_tag (code B)].
Definition special_query (B T f d : Combination) := 'tagged['wait3[sp_body, code T, f, d], query_tag (code B)].
(** Recursive queries (Step 89), by a recursive update with a seed [s : Query[B]]:
      rq_body[B,f] @ r ==> special_type[Query[B], step[r], identity_update]
      step[r] @ q      ==> f @ D[r,q]
      D[r,q]           =   Sq[B, Sq[Query[B], Kq[Update, r], Kq[Query[B], q]], I]
      rq_fix[B,f]      =   fix_update[rq_body[B,f]]
      rec_query[B,f,s] =   D[rq_fix[B,f], s]
    so [rec_query[B,f,s] @ x] evaluates [(rq_fix[B,f] @ s) @ x], that is
    [f @ rec_query[B,f,s] @r x].  The queries of [D[r,q]] are built at run
    time by the query generators, the specialised update by [mk_update]. *)
Definition Dq (B r q : Combination) : Combination :=
  Sq B (Sq (Query B) (Kq Update r) (Kq (Query B) q)) 'I.
Definition D_t (B : Combination) (r q : Term) : Term :=
  op (mk_query B) @@ ''S2[op (mk_query (Query B)) @@ ''S2[op (mk_query Update) @@ (''K @@ r),
                                                     op (mk_query (Query B)) @@ (''K @@ q)], Val 'I].
Definition step_t (B f : Combination) (r : Term) : Term := star "q" (Val f @@ D_t B r (Ref "q")).
Definition rq_body (B f : Combination) : Combination := Eval cbn -[mk_update mk_query code identity_update Query Update] in
  to_tree (star "r" (op mk_update @@ w3 (Val (code (Query B))) (step_t B f (Ref "r")) (Val identity_update))).
Definition rq_fix (B f : Combination) : Combination := fix_update (rq_body B f).
Definition rec_query (B f s : Combination) : Combination := Dq B (rq_fix B f) s.
Definition triageq (B b s g t : Combination) := 'tagged['wait3[tq_body, b, s, Fk g t], query_tag (code B)].

(** ** The department queries *)
Definition count_fn : Combination := Eval cbn -[mk_nat lengthR] in to_tree
  (star "d" (Ref "d" @@ star "p" (op mk_nat @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ (op lengthR @@ (Val (code Employee) ''* (Val 'snd @@ Ref "p")))))))).
Definition employee_count : Combination := special_query Nat Department count_fn (Kq Nat zero).

(** ** Inversions *)

Local Opaque qK_prog qS_prog qsp_prog qe_prog gdq_prog or_prog gtq_prog.

Lemma qK_inv : forall r C, 'wait[qK_prog, r] @ C ==> 'K -> exists B, decode r = Some B /\ C = 'K1 B.
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent qK_prog. unfold qK_prog in H. Local Opaque qK_prog.
  pose proof (decode_p_eval r) as Hd; destruct (decode r) as [B|]; cbn [opt] in Hd; crunch.
  all: eq_case2; crunch; try discriminate.
  all: eexists; split; [reflexivity|assumption].
Qed.

Lemma qS_inv : forall r a C, 'wait2[qS_prog, r, a] @ C ==> 'K ->
  exists cF cV F V B, C = 'S2['label[Fk query_nm cF], 'label[Fk query_nm cV]] /\ decode cF = Some F /\
    decode cV = Some V /\ decode r = Some B /\ a @ F @r V ==> Sm B.
Proof.
  intros r a C H; apply wait2_eval_inv in H. Local Transparent qS_prog. unfold qS_prog in H. Local Opaque qS_prog.
  crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs; try discriminate.
  all: repeat dec_step; crunch; try discriminate.
  all: try (eq_case2; crunch); try discriminate.
  all: try subst; do 5 eexists; split; [eassumption|split; [eassumption|split; [eassumption|split; [eassumption|]]]].
  all: eapply eval_appl; eassumption.
Qed.

Lemma qsp_inv : forall r a C, 'wait2[qsp_prog, r, a] @ C ==> 'K ->
  exists cT F T B, C = 'wait3[sp_body, cT, F, 'label[Fk query_nm r]] /\ decode cT = Some T /\
    decode r = Some B /\ a @ F @r T ==> Sm B.
Proof.
  intros r a C H; apply wait2_eval_inv in H. Local Transparent qsp_prog. unfold qsp_prog in H. Local Opaque qsp_prog.
  crunch; use_specs; crunch; use_specs.
  eq_case2; crunch; use_specs; try discriminate.
  all: repeat dec_step; crunch; try discriminate.
  all: try (eq_case2; crunch); try discriminate.
  all: try (eq_case2; crunch); try discriminate.
  all: use_specs; subst.
  all: match goal with E0 : right_of (right_of (stem_of (left_of ?C))) = 'label[_], E : ?C = _ |- _ =>
         rewrite E0 in E end.
  all: try subst; do 4 eexists; split; [eassumption|split; [eassumption|split; [eassumption|]]].
  all: eapply eval_appl; eassumption.
Qed.

Lemma qe_inv0 : forall r n a U V, 'wait[qe_prog, r] @ n @r a @r U ==> Sm V -> decode r = Some V.
Proof.
  intros r n a U V H.
  destruct (appl_inv _ _ _ _ H) as [p [Hp Hq]]; clear H.
  destruct (app2_inv _ _ _ _ Hp) as [p1 [Hp1 Hq1]]; clear Hp.
  apply wait_eval_inv in Hp1. Local Transparent qe_prog. unfold qe_prog in Hp1. Local Opaque qe_prog.
  pose proof (decode_p_eval r) as Hd; destruct (decode r) as [B|]; cbn [opt] in Hd; crunch; reflexivity.
Qed.

Lemma qe_fwd0 : forall r B n a U, decode r = Some B -> 'wait[qe_prog, r] @ n @r a @r U ==> Sm B.
Proof.
  intros r B n a U HB; pose proof (decode_p_eval r) as Hd; rewrite HB in Hd; cbn [opt] in Hd.
  eapply eval_appl; [eapply eval_appl; [apply wait_eval|]|]. Local Transparent qe_prog. unfold qe_prog. Local Opaque qe_prog.
  all: ev2.
Qed.

Lemma qe_inv : forall r a U V, query_elim @ query_tag r @r a @r U ==> Sm V -> decode r = Some V.
Proof. intros r a U V H; unfold query_elim in H; apply name_elim_iff, qe_inv0 in H; exact H. Qed.

Lemma qe_fwd : forall r B a U, decode r = Some B -> query_elim @ query_tag r @r a @r U ==> Sm B.
Proof. intros r B a U H; unfold query_elim; apply name_elim_iff, qe_fwd0; exact H. Qed.

Definition QQl (r : Combination) : Combination := 'label[Fk query_nm (Fk (Fk Lf Lf) (Fk query_nm r))].

Lemma gtq_inv : forall r C, 'wait[gtq_prog, r] @ C ==> 'K -> exists B, decode r = Some B /\
  C = 'wait3[tq_body, B, 'label[Fk query_nm r], Fk (QQl r) (QQl r)].
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent gtq_prog. unfold gtq_prog in H. Local Opaque gtq_prog.
  pose proof (decode_p_eval r) as Hd; destruct (decode r) as [B|]; cbn [opt] in Hd; crunch.
  all: eq_case2; crunch; try discriminate.
  all: eexists; split; [reflexivity|assumption].
Qed.

Lemma gdq_inv : forall r C, 'wait[gdq_prog, r] @ C ==> 'K -> C = 'S2[QQl r, 'I].
Proof.
  intros r C H; apply wait_eval_inv in H. Local Transparent gdq_prog. unfold gdq_prog in H. Local Opaque gdq_prog.
  crunch. all: eq_case2; crunch; try discriminate. all: reflexivity.
Qed.

Lemma query_guard_inv : forall r a C, guard_of @ D_query r a @r C ==> 'K ->
  (exists B, decode r = Some B /\ C = 'K1 B) \/
  (exists cF cV F V B, C = 'S2['label[Fk query_nm cF], 'label[Fk query_nm cV]] /\ decode cF = Some F /\
     decode cV = Some V /\ decode r = Some B /\ a @ F @r V ==> Sm B) \/
  (exists cT F T B, C = 'wait3[sp_body, cT, F, 'label[Fk query_nm r]] /\ decode cT = Some T /\
     decode r = Some B /\ a @ F @r T ==> Sm B) \/
  (C = 'S2[QQl r, 'I]) \/
  (exists B, decode r = Some B /\ C = 'wait3[tq_body, B, 'label[Fk query_nm r], Fk (QQl r) (QQl r)]).
Proof.
  intros r a C H; destruct (app2_inv _ _ _ _ H) as [g [Hg HC]].
  pose proof (eval_deterministic _ _ Hg _ (guard_of_pair _ _)) as ->.
  unfold query_guard in HC.
  destruct (or_g_inv _ _ _ HC) as [H1|H1]; [left; apply qK_inv; exact H1|].
  destruct (or_g_inv _ _ _ H1) as [H2|H2]; [right; left; apply qS_inv; exact H2|].
  destruct (or_g_inv _ _ _ H2) as [H3|H3]; [right; right; left; apply qsp_inv; exact H3|].
  destruct (or_g_inv _ _ _ H3) as [H4|H4]; [right; right; right; left; apply gdq_inv; exact H4|].
  right; right; right; right; apply gtq_inv; exact H4.
Qed.

