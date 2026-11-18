(** * Step 82 (stage 1): typing rules as programs, with labels as abstract types.

    Self-typing: a concrete (label-free) value [c] has type [c].  The
    abstract type named by a concrete name [n] is the label
    [label[n] = S2[K, K1 n]]; a typed value is a tag
    [tagged[f,n] = f o label[n]], whose type is [label[n]] when the
    ontology's guard at [n] admits the type of [f].  A bare label has no
    type.

    Programs answer [Sm R] on success and [Lf] on failure.

    - The ontology is a program [O]: [O @ n @r tp ==> Sm D] declares
      [n], with guard [guard_of @ D] (it answers [K] on an admitted
      carrier type) and eliminator [elim_of @ D], applied as
      [elim_of @ D @r n @r tp @r U].
    - Type application [tp O = Z (tp_body O)], clause by clause:

        label[n] # U  = let Sm D = O @ n @ tp in elim_of D @ n @ tp @ U
        Lf # U        = Sm U
        Sm G # U      = if Fk G U is a label then Lf else Sm (Fk G U)
        Fk X Y # U    = Lf                      (X a tag or a label)
        K1 Y # U      = Sm Y
        S2[G,H] # U   = let Sm V = G # U in let Sm W = H # U in V # W
        triage[F0,F1,F2] # U =
                        match U with
                        | label[_] => Lf
                        | Lf => Sm F0
                        | Sm X => F1 # X
                        | Fk X Y => let Sm G = F2 # X in G # Y

    - Value inference [infer O = Z (infer_body O)]:

        Lf            => Sm Lf
        Sm u          => let Sm U = infer u in Sm (Sm U)
        tagged[f,n]   => if n is concrete then
                           let Sm F = infer f in
                           let Sm D = O @ n @ tp in
                           if guard_of D @ F == K then Sm label[n] else Lf
                         else Lf
        Fk u1 u2      => let Sm U1 = infer u1 in let Sm U2 = infer u2 in
                         (Sm U1) # U2

    - Expression inference [infer_expression O]:

        Lf            => Lf
        Sm u          => infer u
        Fk e1 e2      => let Sm T1 = ie e1 in let Sm T2 = ie e2 in T1 # T2
*)

From BigStep Require Import tree.
From Stdlib Require Import String Bool Arith Lia.
Open Scope string_scope.
Set Default Proof Using "Type".

(** ** Helpers *)

(** Split two-argument evaluations in the context into their two steps,
    then build evaluations syntactically, closing the residual steps from
    the context. *)
Ltac dedup := repeat match goal with
  | H1 : ?e ==> ?a, H2 : ?e ==> ?b |- _ =>
      let E := fresh in pose proof (eval_deterministic _ _ H1 _ H2) as E; clear H2;
      inversion E; clear E; subst
  end.
Ltac split2 := repeat match goal with H : eval (Fk (Fk (Sm _) (Sm _)) (Sm _)) _ |- _ => inv_out H end; dedup.
Ltac ev := split2; evaluate2; first [eassumption | evaluate2].

(** [op c] hides the constant [c] behind an identity composition, so that
    [star] and [to_tree] never inspect [c]. *)
Definition op (c : Combination) : Term := Val ('I 'C c).

Definition bt (b : bool) : Combination := if b then 'K else 'KI.

Lemma bt_select : forall b x y, bt b @ x @r y ==> (if b then x else y).
Proof. intros [] x y; cbn; evaluate. Qed.

Definition opt (o : option Combination) : Combination :=
  match o with Some t => Sm t | None => Lf end.

(** A fuel evaluator; a computed [run k e = Some v] proves [e ==> v]. *)
Fixpoint run (k : nat) (e : Combination) : option Combination :=
  match k with
  | 0 => None
  | S k' =>
      match e with
      | Sm v => Some v
      | Fk (Fk e11 e12) e2 =>
          match run k' (Fk e11 e12) with
          | Some v1 => run k' (Fk (Sm v1) e2)
          | None => None
          end
      | Fk (Sm v1) (Fk e21 e22) =>
          match run k' (Fk e21 e22) with
          | Some v2 => run k' (Fk (Sm v1) (Sm v2))
          | None => None
          end
      | Fk (Sm Lf) (Sm v2) => Some (Sm v2)
      | Fk (Sm (Sm v1)) (Sm v2) => Some (Fk v1 v2)
      | Fk (Sm (Fk Lf v1)) (Sm _) => Some v1
      | Fk (Sm (Fk (Sm g) f)) (Sm v2) => run k' (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2)))
      | Fk (Sm (Fk (Fk f0 _) _)) (Sm Lf) => Some f0
      | Fk (Sm (Fk (Fk _ f1) _)) (Sm (Sm v2)) => run k' (Fk (Sm f1) (Sm v2))
      | Fk (Sm (Fk (Fk _ _ ) f2)) (Sm (Fk v21 v22)) =>
          run k' (Fk (Fk (Sm f2) (Sm v21)) (Sm v22))
      | _ => None
      end
  end.

Theorem run_sound : forall k e v, run k e = Some v -> e ==> v.
Proof.
  induction k as [|k IH]; intros e v H; [discriminate|].
  cbn in H.
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ =>
             lazymatch x with run _ _ => fail | _ => destruct x end
         end;
    try discriminate;
    repeat match goal with
           | H : context [match run ?k ?e with _ => _ end] |- _ =>
               let E := fresh "E" in destruct (run k e) eqn:E; [|discriminate]
           end;
    try (injection H as <-; constructor; fail);
    econstructor; apply IH; eassumption.
Qed.

(** A lazily fuelled evaluator.  [run k] matches on a unary [k], which the
    virtual machine builds in full before it starts; for the large budgets of
    the examples that dominated the build.  [runp d] has budget [2^d] layers
    but never builds a number: each layer is unfolded only when it is called. *)
Definition run_layer (F : Combination -> option Combination) (e : Combination) : option Combination :=
  match e with
  | Sm v => Some v
  | Fk (Fk e11 e12) e2 =>
      match F (Fk e11 e12) with Some v1 => F (Fk (Sm v1) e2) | None => None end
  | Fk (Sm v1) (Fk e21 e22) =>
      match F (Fk e21 e22) with Some v2 => F (Fk (Sm v1) (Sm v2)) | None => None end
  | Fk (Sm Lf) (Sm v2) => Some (Sm v2)
  | Fk (Sm (Sm v1)) (Sm v2) => Some (Fk v1 v2)
  | Fk (Sm (Fk Lf v1)) (Sm _) => Some v1
  | Fk (Sm (Fk (Sm g) f)) (Sm v2) => F (Fk (Fk (Sm g) (Sm v2)) (Fk (Sm f) (Sm v2)))
  | Fk (Sm (Fk (Fk f0 _) _)) (Sm Lf) => Some f0
  | Fk (Sm (Fk (Fk _ f1) _)) (Sm (Sm v2)) => F (Fk (Sm f1) (Sm v2))
  | Fk (Sm (Fk (Fk _ _ ) f2)) (Sm (Fk v21 v22)) => F (Fk (Fk (Sm f2) (Sm v21)) (Sm v22))
  | _ => None
  end.

Fixpoint runG (d : nat) (F : Combination -> option Combination) : Combination -> option Combination :=
  match d with 0 => run_layer F | S d' => runG d' (fun e => runG d' F e) end.

Definition runp (d : nat) : Combination -> option Combination := runG d (fun _ => None).

Definition run_ok (F : Combination -> option Combination) : Prop :=
  forall e v, F e = Some v -> e ==> v.

Lemma run_layer_ok : forall F, run_ok F -> run_ok (run_layer F).
Proof.
  intros F IH e v H; unfold run_layer in H.
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ =>
             lazymatch x with F _ => fail | _ => destruct x end
         end;
    try discriminate;
    repeat match goal with
           | H : context [match F ?e with _ => _ end] |- _ =>
               let E := fresh "E" in destruct (F e) eqn:E; [|discriminate]
           end;
    try (injection H as <-; constructor; fail);
    econstructor; apply IH; eassumption.
Qed.

Lemma runG_ok : forall d F, run_ok F -> run_ok (runG d F).
Proof.
  induction d as [|d IH]; intros F HF; cbn; [apply run_layer_ok, HF|].
  apply IH; intros e v H; exact (IH F HF e v H).
Qed.

Theorem runp_sound : forall d e v, runp d e = Some v -> e ==> v.
Proof. intros d; apply runG_ok; intros e v H; discriminate. Qed.

(** Close a goal [runp d e = r] by one computation, checked by the kernel at
    [Qed] only ([vm_compute; reflexivity] would compute it twice). *)
Ltac vm_done := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

(** *** Labels *)

Definition label_of (t : Combination) : option Combination :=
  match t with
  | Fk (Sm (Sm Lf)) (Fk Lf n) => Some n
  | _ => None
  end.

Lemma label_of_label : forall n, label_of ('label[n]) = Some n.
Proof. reflexivity. Qed.

Lemma label_of_some : forall t n, label_of t = Some n -> t = 'label[n].
Proof.
  intros t n H; destruct t as [| |a b]; try discriminate;
    destruct a as [|[|[| |]|]|]; try discriminate;
    destruct b as [| |[| |] m]; try discriminate; inversion H; reflexivity.
Qed.

Lemma label_of_none : forall t, label_of t = None -> forall n, t <> 'label[n].
Proof. intros t H n ->; discriminate. Qed.

Lemma label_pair_of : forall u v, label_pair u v = match label_of (Fk u v) with Some _ => true | None => false end.
Proof.
  intros u v; destruct u as [|[|[|x|x y]|x y]|x y]; try reflexivity;
    destruct v as [| |[| |] m]; reflexivity.
Qed.

(** [get_label @ t ==> opt (label_of t)]. *)
Definition get_label : Combination :=
  'triage[Lf, 'K1 Lf,
    'triage['K1 Lf,
      'triage['K1 Lf,
        'triage['triage[Lf, 'K1 Lf, 'triage[Lf, 'K1 ('K1 Lf), 'K1 ('K1 ('K1 Lf))]],
                'K1 ('K1 Lf), 'K1 ('K1 ('K1 Lf))],
        'K1 ('K1 ('K1 Lf))],
      'K1 ('K1 ('K1 Lf))]].

Lemma get_label_spec : forall t, get_label @ t ==> opt (label_of t).
Proof.
  intros t; unfold get_label.
  destruct t as [|t|a b]; [evaluate|evaluate|].
  destruct a as [|a|a1 a2]; [evaluate|..|evaluate].
  destruct a as [|a|a1 a2]; [evaluate|..|evaluate].
  destruct a as [|a|a1 a2]; [..|evaluate|evaluate].
  destruct b as [|b|b n]; [evaluate|evaluate|].
  destruct b as [|b|b1 b2]; cbn; evaluate.
Qed.

(** *** Reserved left branches: tags and labels *)

Definition tag_of (t : Combination) : option (Combination * Combination) :=
  match t with
  | Fk (Sm (Fk Lf f)) (Fk (Sm (Sm Lf)) (Fk Lf n)) => Some (f, n)
  | _ => None
  end.

Lemma tag_of_tagged : forall f n, tag_of ('tagged[f,n]) = Some (f, n).
Proof. reflexivity. Qed.

Lemma tag_of_some : forall t f n, tag_of t = Some (f, n) -> t = 'tagged[f,n].
Proof.
  intros t f n H; unfold tag_of in H;
    repeat match goal with
           | H : context [match ?x with _ => _ end] |- _ => destruct x; try discriminate H
           end;
    inversion H; reflexivity.
Qed.

Lemma tag_of_none : forall t, tag_of t = None -> forall f n, t <> 'tagged[f,n].
Proof. intros t H f n ->; discriminate. Qed.

Lemma get_tagged_spec : forall t,
  get_tagged @ t ==> match tag_of t with Some (f, n) => Sm (Fk f n) | None => Lf end.
Proof.
  intros t; destruct (tag_of t) as [[f n]|] eqn:E.
  - apply tag_of_some in E; subst; apply get_tagged_some.
  - apply get_tagged_none; apply tag_of_none; exact E.
Qed.

Definition reservedb (t : Combination) : bool :=
  match tag_of t, label_of t with
  | None, None => false
  | _, _ => true
  end.

(** [resv @ X ==> Lf] exactly when [X] is neither a tag nor a label. *)
Definition resv : Combination := extend get_tagged get_label.

Lemma resv_spec : forall X, exists r, resv @ X ==> r /\ (r = Lf <-> reservedb X = false).
Proof.
  intros X; unfold resv, reservedb.
  pose proof (get_tagged_spec X) as Ht; pose proof (get_label_spec X) as Hl.
  destruct (tag_of X) as [[f n]|] eqn:Et.
  - exists (Fk f n); split; [apply extend_some; exact Ht|split; discriminate].
  - destruct (label_of X) as [n|] eqn:El; cbn in Hl.
    + exists (Sm n); split; [apply extend_none_value; [exact Ht|exact Hl]|split; discriminate].
    + exists Lf; split; [apply extend_none_value; [exact Ht|exact Hl]|tauto].
Qed.

(** *** The label test on a pair, and the test for [K] *)

Definition label_tst : Combination := 'label_test.

Lemma label_tst_spec : forall u v, label_tst @ u @r v ==> bt (label_pair u v).
Proof. intros; unfold label_tst, bt; apply label_test_spec. Qed.

Definition isK : Combination := 'triage['KI, 'triage['K, 'K1 'KI, 'K1 ('K1 'KI)], 'K1 ('K1 'KI)].

Definition is_Kb (r : Combination) : bool :=
  match r with Sm Lf => true | _ => false end.

Lemma isK_spec : forall r, isK @ r ==> bt (is_Kb r).
Proof. intros [|[|x|x y]|x y]; unfold isK; cbn; evaluate. Qed.

Lemma is_Kb_true : forall r, is_Kb r = true -> r = 'K.
Proof. intros [|[| |]|] H; try discriminate; reflexivity. Qed.

(** The guard and the eliminator of a declaration [D]. *)
Definition guard_of : Combination := 'fst.
Definition elim_of : Combination := 'snd.

Lemma guard_of_pair : forall g e, guard_of @ (g '* e) ==> g.
Proof. intros; unfold guard_of; apply fst_pair. Qed.
Lemma elim_of_pair : forall g e, elim_of @ (g '* e) ==> e.
Proof. intros; unfold elim_of; apply snd_pair. Qed.

Lemma is_concrete_bt : forall n, is_concrete @ n ==> bt (concreteb n).
Proof. intros; unfold bt; apply is_concrete_spec. Qed.

(** ** The programs *)

Section Programs.
Variable O : Combination.

(** Lf # U = Sm U *)
Definition leaf_cl : Combination := Eval cbv in to_tree
  (star "U" (Val Lf @@ (Val Lf @@ Ref "U"))).

(** Sm G # U = if Fk G U is a label then Lf else Sm (Fk G U) *)
Definition stem_cl : Combination := Eval cbn -[label_tst] in to_tree
  (star "G" (star "U" (op label_tst @@ Ref "G" @@ Ref "U" @@ Val Lf
     @@ (Val Lf @@ (Val Lf @@ Ref "G" @@ Ref "U"))))).

(** S2[G,H] # U = let Sm V = G # U in let Sm W = H # U in V # W *)
Definition s_cl : Combination := Eval cbv in to_tree
  (star "rec" (star "G" (star "H" (star "U"
    (''onStem1 (star "V" (''onStem1 (star "W" (Ref "rec" @@ Ref "V" @@ Ref "W"))
                          @@ (Ref "rec" @@ Ref "H" @@ Ref "U")))
     @@ (Ref "rec" @@ Ref "G" @@ Ref "U")))))).

(** triage[F0,F1,F2] # U *)
Definition tri_shape : Term :=
  star "U2" (''triage[Val Lf @@ Ref "F0",
                      star "X" (Ref "rec" @@ Ref "F1" @@ Ref "X"),
                      star "X" (star "Y" (''onStem1 (star "G" (Ref "rec" @@ Ref "G" @@ Ref "Y"))
                                          @@ (Ref "rec" @@ Ref "F2" @@ Ref "X")))]
             @@ Ref "U2").

Definition tri_cl : Combination := Eval cbn -[get_label] in to_tree
  (star "rec" (star "F0" (star "F1" (star "F2" (star "U"
    (''triage[tri_shape, Val ('K1 ('K1 Lf)), Val ('K1 ('K1 ('K1 Lf)))]
       @@ (op get_label @@ Ref "U") @@ Ref "U")))))).

(** Fk X Y # U, by the left branch X (after refusing a reserved X). *)
Definition fk_cl : Combination := Eval cbn -[resv s_cl tri_cl] in to_tree
  (star "rec" (star "X" (star "Y"
    (''triage[''triage[''K1 (Val Lf @@ Ref "Y"),
                       star "G" (op s_cl @@ Ref "rec" @@ Ref "G" @@ Ref "Y"),
                       star "F0" (star "F1" (op tri_cl @@ Ref "rec" @@ Ref "F0" @@ Ref "F1" @@ Ref "Y"))]
                @@ Ref "X",
              Val ('K1 ('K1 Lf)),
              Val ('K1 ('K1 ('K1 Lf)))]
       @@ (op resv @@ Ref "X"))))).

(** The ordinary clauses, by the shape of F. *)
Definition ord_cl : Combination := Eval cbn -[leaf_cl stem_cl fk_cl] in to_tree
  (star "rec" (star "F"
    (''triage[Val leaf_cl, Val stem_cl,
              star "X" (star "Y" (op fk_cl @@ Ref "rec" @@ Ref "X" @@ Ref "Y"))]
       @@ Ref "F"))).

(** label[n] # U = let Sm D = O @ n @ tp in elim_of D @ n @ tp @ U *)
Definition abs_cl : Combination := Eval cbn -[elim_of] in to_tree
  (star "rec" (star "n" (star "U"
    (''onStem1 (star "D" (op elim_of @@ Ref "D" @@ Ref "n" @@ Ref "rec" @@ Ref "U"))
       @@ (op O @@ Ref "n" @@ Ref "rec"))))).

Definition tp_body : Combination := Eval cbn -[get_label ord_cl abs_cl] in to_tree
  (star "rec" (star "F"
    (''triage[op ord_cl @@ Ref "rec",
              star "n" (star "F2" (op abs_cl @@ Ref "rec" @@ Ref "n")),
              Val ('K1 ('K1 ('K1 Lf)))]
       @@ (op get_label @@ Ref "F") @@ Ref "F"))).

Definition tp : Combination := Z tp_body.

(** The tag clause of inference, given the parts [f] and [n] of the tag. *)
Definition tag_cl : Combination := Eval cbn -[is_concrete isK guard_of tp] in to_tree
  (star "f" (star "n" (star "r"
    (op is_concrete @@ Ref "n"
       @@ star "r2" (''onStem1 (star "F" (''onStem1 (star "D"
               (op isK @@ (op guard_of @@ Ref "D" @@ Ref "F")
                  @@ (Val Lf @@ (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "n")))
                  @@ Val Lf))
             @@ (op O @@ Ref "n" @@ Val tp)))
          @@ (Ref "r2" @@ Ref "f"))
       @@ Val ('K1 Lf)
       @@ Ref "r")))).

(** The plain fork clause of inference. *)
Definition plain_cl : Combination := Eval cbn -[tp] in to_tree
  (star "u1" (star "u2" (star "r"
    (''onStem1 (star "U1" (''onStem1 (star "U2" (op tp @@ (Val Lf @@ Ref "U1") @@ Ref "U2"))
                           @@ (Ref "r" @@ Ref "u2")))
       @@ (Ref "r" @@ Ref "u1"))))).

Definition infer_body : Combination := Eval cbn -[get_tagged tag_cl plain_cl] in to_tree
  (star "rec" (star "t"
    (''triage[Val (Sm Lf),
              star "u" (''onStem1 (star "U" (Val Lf @@ (Val Lf @@ Ref "U"))) @@ (Ref "rec" @@ Ref "u")),
              star "u1" (star "u2"
                (''triage[op plain_cl @@ Ref "u1" @@ Ref "u2",
                          star "p" (''triage[Val Lf, Val Lf, op tag_cl] @@ Ref "p"),
                          Val ('K1 ('K1 Lf))]
                   @@ (op get_tagged @@ (Val Lf @@ Ref "u1" @@ Ref "u2"))
                   @@ Ref "rec"))]
       @@ Ref "t"))).

Definition infer : Combination := Z infer_body.

Definition ie_body : Combination := Eval cbn -[infer tp] in to_tree
  (star "rec" (star "e"
    (''triage[Val Lf,
              star "u" (op infer @@ Ref "u"),
              star "e1" (star "e2"
                (''onStem1 (star "T1" (''onStem1 (star "T2" (op tp @@ Ref "T1" @@ Ref "T2"))
                                        @@ (Ref "rec" @@ Ref "e2")))
                   @@ (Ref "rec" @@ Ref "e1")))]
       @@ Ref "e"))).

Definition infer_expression : Combination := Z ie_body.

End Programs.

(** ** Inversion and forward lemmas

    [crunch] inverts evaluations as far as their syntax allows and
    identifies repeated evaluations; [fin] closes goals made of
    disjunctions, conjunctions, existentials and evaluations from the
    context. *)

Ltac fin := match goal with
 | |- _ \/ _ => first [left; fin | right; fin]
 | |- exists _, _ => eexists; fin
 | |- _ /\ _ => split; fin
 | |- eval (Fk (Fk _ _) _) _ => first [eassumption | eapply eval_appl; [fin|fin]]
 | |- _ => solve [reflexivity | eassumption | auto ]
end.
Ltac crunch := invert_eval; dedup; try (invert_eval; dedup); try (invert_eval; dedup); try (invert_eval; dedup).

Lemma app2 : forall f x y a v, f @ x ==> a -> a @ y ==> v -> f @ x @r y ==> v.
Proof. intros; eapply eval_appl; eassumption. Qed.

Lemma app2_inv : forall f x y v, f @ x @r y ==> v -> exists a, f @ x ==> a /\ a @ y ==> v.
Proof. intros f x y v H; inv_out H; eauto. Qed.

Lemma appl_inv : forall a b c v, Fk (Fk a b) c ==> v -> exists w, Fk a b ==> w /\ Fk (Sm w) c ==> v.
Proof. intros a b c v H; inv_out H; eauto. Qed.

Section Inversion.
Variable O : Combination.
Local Opaque get_label ord_cl abs_cl leaf_cl stem_cl fk_cl s_cl tri_cl resv label_tst elim_of
  guard_of isK is_concrete get_tagged tag_cl plain_cl tp infer.

(** *** Type application *)

Lemma tp_body_inv : forall rec F p, tp_body O @ rec @r F ==> p ->
  (label_of F = None /\ ord_cl @ rec @r F ==> p) \/
  (exists n, F = 'label[n] /\ abs_cl O @ rec @r n ==> p).
Proof.
  intros rec F p H.
  pose proof (get_label_spec F) as HL.
  destruct (label_of F) as [n|] eqn:EL; cbn [opt] in HL; unfold tp_body in H.
  - right; exists n; split; [apply label_of_some; exact EL|].
    invert_eval; dedup; fin.
  - left; split; [reflexivity|]. invert_eval; dedup; fin.
Qed.

Lemma ord_inv : forall rec F U v, ord_cl @ rec @r F @r U ==> v ->
   (F = Lf /\ leaf_cl @ U ==> v) \/ (exists G, F = Sm G /\ stem_cl @ G @r U ==> v) \/
   (exists X Y, F = Fk X Y /\ fk_cl @ rec @r X @r Y @r U ==> v).
Proof.
  intros rec F U v H. Local Transparent ord_cl. unfold ord_cl in H. Local Opaque ord_cl.
  invert_eval; dedup; fin.
Qed.

Lemma leaf_inv : forall U v, leaf_cl @ U ==> v -> v = Sm (Sm U).
Proof. intros U v H. Local Transparent leaf_cl. unfold leaf_cl in H. Local Opaque leaf_cl. invert_eval. Qed.

Lemma stem_inv : forall G U v, stem_cl @ G @r U ==> v -> v = (if label_pair G U then Lf else Sm (Fk G U)).
Proof.
  intros G U v H. Local Transparent stem_cl. unfold stem_cl in H. Local Opaque stem_cl.
  pose proof (label_tst_spec G U) as HL; inv_out HL.
  destruct (label_pair G U); cbn [bt] in *; crunch.
Qed.

Lemma abs_inv : forall rec n U v, abs_cl O @ rec @r n @r U ==> v ->
  exists d, O @ n @r rec ==> d /\ ((d = Lf /\ v = Lf) \/ (exists D, d = Sm D /\ elim_of @ D @r n @r rec @r U ==> v) \/ (exists a b, d = Fk a b /\ v = Lf)).
Proof.
  intros rec n U v H. Local Transparent abs_cl. unfold abs_cl in H. Local Opaque abs_cl.
  crunch; fin.
Qed.

Lemma fk_inv : forall rec X Y U v, fk_cl @ rec @r X @r Y @r U ==> v ->
  (reservedb X = true /\ v = Lf) \/
  (reservedb X = false /\ (
     (X = Lf /\ v = Sm Y) \/
     (exists G, X = Sm G /\ s_cl @ rec @r G @r Y @r U ==> v) \/
     (exists F0 F1, X = Fk F0 F1 /\ tri_cl @ rec @r F0 @r F1 @r Y @r U ==> v))).
Proof.
  intros rec X Y U v H. Local Transparent fk_cl. unfold fk_cl in H. Local Opaque fk_cl.
  destruct (resv_spec X) as [r [Hr Hiff]].
  destruct (reservedb X).
  - left; split; [reflexivity|].
    destruct r as [|r|r1 r2]; [destruct Hiff as [H1 _]; specialize (H1 eq_refl); discriminate|..];
    crunch.
  - right; split; [reflexivity|].
    destruct Hiff as [_ H1]; specialize (H1 eq_refl); subst r.
    crunch; fin.
Qed.

Lemma s_inv : forall rec G H U v, s_cl @ rec @r G @r H @r U ==> Sm v ->
  exists V W, rec @ G @r U ==> Sm V /\ rec @ H @r U ==> Sm W /\ rec @ V @r W ==> Sm v.
Proof.
  intros rec G H U v E. Local Transparent s_cl. unfold s_cl in E. Local Opaque s_cl.
  crunch; fin.
Qed.

Lemma tri_inv : forall rec F0 F1 F2 U v, tri_cl @ rec @r F0 @r F1 @r F2 @r U ==> Sm v ->
  label_of U = None /\
  ((U = Lf /\ v = F0) \/
   (exists X, U = Sm X /\ rec @ F1 @r X ==> Sm v) \/
   (exists X Y G, U = Fk X Y /\ rec @ F2 @r X ==> Sm G /\ rec @ G @r Y ==> Sm v)).
Proof.
  intros rec F0 F1 F2 U v E. Local Transparent tri_cl. unfold tri_cl in E. Local Opaque tri_cl.
  pose proof (get_label_spec U) as HL.
  destruct (label_of U) as [n|] eqn:EL; cbn [opt] in HL.
  - crunch.
  - split; [reflexivity|]. crunch; fin.
Qed.

(** Type application, clause by clause: [TA F U R] when [F # U] may
    give [Sm R]; the recursive calls are evaluations of [tp O]. *)
Definition app (F U R : Combination) : Prop := tp O @ F @r U ==> Sm R.

Inductive TA : Combination -> Combination -> Combination -> Prop :=
| TA_abs : forall n U D R, O @ n @r tp O ==> Sm D -> elim_of @ D @r n @r tp O @r U ==> Sm R ->
    TA ('label[n]) U R
| TA_leaf : forall U, TA Lf U (Sm U)
| TA_stem : forall G U, label_pair G U = false -> TA (Sm G) U (Fk G U)
| TA_K : forall Y U, TA ('K1 Y) U Y
| TA_S : forall G H U V W R, label_of ('S2[G,H]) = None ->
    app G U V -> app H U W -> app V W R -> TA ('S2[G,H]) U R
| TA_tri_leaf : forall F0 F1 F2, reservedb (Fk F0 F1) = false -> TA ('triage[F0,F1,F2]) Lf F0
| TA_tri_stem : forall F0 F1 F2 X R, reservedb (Fk F0 F1) = false -> app F1 X R ->
    TA ('triage[F0,F1,F2]) (Sm X) R
| TA_tri_fork : forall F0 F1 F2 X Y G R, reservedb (Fk F0 F1) = false -> label_of (Fk X Y) = None ->
    app F2 X G -> app G Y R -> TA ('triage[F0,F1,F2]) (Fk X Y) R.

Lemma tp_unfold_inv : forall F U v, tp O @ F @r U ==> v ->
  exists p, tp_body O @ tp O @r F ==> p /\ p @ U ==> v.
Proof.
  intros F U v H; destruct (app2_inv _ _ _ _ H) as [p [H1 H2]].
  exists p; split; [|exact H2].
  Local Transparent tp. unfold tp in *. Local Opaque tp. apply Z_unfold_inv; exact H1.
Qed.

Theorem tp_inv : forall F U R, tp O @ F @r U ==> Sm R -> TA F U R.
Proof.
  intros F U R H.
  destruct (tp_unfold_inv _ _ _ H) as [p [Hp HU]]; clear H.
  destruct (tp_body_inv _ _ _ Hp) as [[HL Ho]|[n [-> Ha]]].
  - destruct (ord_inv _ _ _ _ (eval_appl _ _ _ _ _ Ho HU)) as [[-> Hl]|[[G [-> Hs]]|[X [Y [-> Hf]]]]].
    + apply leaf_inv in Hl; inversion Hl; constructor.
    + apply stem_inv in Hs; destruct (label_pair G U) eqn:E; inversion Hs; constructor; exact E.
    + destruct (fk_inv _ _ _ _ _ Hf) as [[_ E]|[HX [[-> E]|[[G [-> Hs]]|[F0 [F1 [-> Ht]]]]]]];
        try discriminate.
      * inversion E; constructor.
      * destruct (s_inv _ _ _ _ _ Hs) as [V [W [H1 [H2 H3]]]].
        econstructor; [exact HL|exact H1|exact H2|exact H3].
      * destruct (tri_inv _ _ _ _ _ _ Ht) as [HU' [[-> ->]|[[X [-> H1]]|[X1 [X2 [G [-> [H1 H2]]]]]]]].
        -- constructor; exact HX.
        -- constructor; [exact HX|exact H1].
        -- econstructor; [exact HX|exact HU'|exact H1|exact H2].
  - destruct (abs_inv _ _ _ _ (eval_appl _ _ _ _ _ Ha HU)) as [d [Hd [[_ E]|[[D [-> HE]]|[a [b [_ E]]]]]]];
      try discriminate.
    econstructor; [exact Hd|exact HE].
Qed.

(** *** Value inference *)

Lemma infer_body_inv : forall rec t T, infer_body O @ rec @r t ==> Sm T ->
   (t = Lf /\ T = Lf)
 \/ (exists u U, t = Sm u /\ rec @ u ==> Sm U /\ T = Sm U)
 \/ (exists f n, t = 'tagged[f,n] /\ tag_cl O @ f @r n @r rec ==> Sm T)
 \/ (exists u1 u2, t = Fk u1 u2 /\ tag_of (Fk u1 u2) = None /\ plain_cl O @ u1 @r u2 @r rec ==> Sm T).
Proof.
  intros rec t T H; unfold infer_body in H.
  destruct t as [|u|u1 u2].
  - crunch; fin.
  - crunch; fin.
  - pose proof (get_tagged_spec (Fk u1 u2)) as HG.
    destruct (tag_of (Fk u1 u2)) as [[f n]|] eqn:E.
    + apply tag_of_some in E; rewrite E in *.
      right; right; left; exists f, n; split; [reflexivity|].
      crunch; fin.
    + right; right; right; exists u1, u2; split; [reflexivity|split; [exact E|]].
      crunch; fin.
Qed.

Lemma tag_cl_inv : forall f n r T, tag_cl O @ f @r n @r r ==> Sm T ->
  concreteb n = true /\ T = 'label[n] /\
  exists F D, r @ f ==> Sm F /\ O @ n @r tp O ==> Sm D /\ guard_of @ D @r F ==> 'K.
Proof.
  intros f n r T H. Local Transparent tag_cl. unfold tag_cl in H. Local Opaque tag_cl.
  pose proof (is_concrete_bt n) as Hc.
  destruct (concreteb n); cbn [bt] in Hc.
  - split; [reflexivity|].
    crunch.
    match goal with H : isK @ ?x ==> _ |- _ => pose proof (isK_spec x) as HK;
      destruct (is_Kb x) eqn:EK; cbn [bt] in HK end; crunch.
    apply is_Kb_true in EK; subst.
    split; [reflexivity|]. fin.
  - crunch.
Qed.

Lemma plain_cl_inv : forall u1 u2 r T, plain_cl O @ u1 @r u2 @r r ==> Sm T ->
  exists U1 U2, r @ u1 ==> Sm U1 /\ r @ u2 ==> Sm U2 /\ tp O @ Sm U1 @r U2 ==> Sm T.
Proof.
  intros u1 u2 r T H. Local Transparent plain_cl. unfold plain_cl in H. Local Opaque plain_cl.
  crunch; fin.
Qed.

Inductive INF : Combination -> Combination -> Prop :=
| INF_leaf : INF Lf Lf
| INF_stem : forall u U, infer O @ u ==> Sm U -> INF (Sm u) (Sm U)
| INF_tag : forall f n F D, concreteb n = true -> infer O @ f ==> Sm F ->
    O @ n @r tp O ==> Sm D -> guard_of @ D @r F ==> 'K -> INF ('tagged[f,n]) ('label[n])
| INF_fork : forall u1 u2 U1 U2, tag_of (Fk u1 u2) = None -> infer O @ u1 ==> Sm U1 ->
    infer O @ u2 ==> Sm U2 -> label_pair U1 U2 = false -> INF (Fk u1 u2) (Fk U1 U2).

Lemma tp_stem_inv : forall G U R, tp O @ Sm G @r U ==> Sm R -> label_pair G U = false /\ R = Fk G U.
Proof. intros G U R H; apply tp_inv in H; inversion H; subst; auto. Qed.

Theorem infer_inv : forall t T, infer O @ t ==> Sm T -> INF t T.
Proof.
  intros t T H.
  Local Transparent infer. unfold infer in H. Local Opaque infer.
  apply Z_unfold_inv in H; change (Z (infer_body O)) with (infer O) in H.
  destruct (infer_body_inv _ _ _ H) as [[-> ->]|[[u [U [-> [Hu ->]]]]|[[f [n [-> Ht]]]|[u1 [u2 [-> [Ht Hp]]]]]]].
  - constructor.
  - constructor; exact Hu.
  - destruct (tag_cl_inv _ _ _ _ Ht) as [Hc [-> [F [D [HF [HD HG]]]]]].
    econstructor; eassumption.
  - destruct (plain_cl_inv _ _ _ _ Hp) as [U1 [U2 [H1 [H2 H3]]]].
    destruct (tp_stem_inv _ _ _ H3) as [HL ->].
    constructor; assumption.
Qed.

(** *** Expression inference *)

Theorem ie_inv : forall e T, infer_expression O @ e ==> Sm T ->
  (exists u, e = Sm u /\ infer O @ u ==> Sm T) \/
  (exists e1 e2 T1 T2, e = Fk e1 e2 /\ infer_expression O @ e1 ==> Sm T1 /\
     infer_expression O @ e2 ==> Sm T2 /\ tp O @ T1 @r T2 ==> Sm T).
Proof.
  intros e T H.
  Local Transparent infer_expression. unfold infer_expression in H.
  apply Z_unfold_inv in H; change (Z (ie_body O)) with (infer_expression O) in H. Local Opaque infer_expression.
  unfold ie_body in H.
  destruct e as [|u|e1 e2]; crunch; fin.
Qed.

(** *** Forward lemmas *)

Local Ltac fwd := split2; evaluate2; repeat first [eassumption | progress evaluate2].

Local Transparent fk_cl abs_cl s_cl tri_cl.
Lemma s_partial : forall rec, exists p, s_cl @ rec ==> p.
Proof. intros; unfold s_cl; eexists; evaluate. Qed.
Lemma tri_partial : forall rec, exists p, tri_cl @ rec ==> p.
Proof. intros; unfold tri_cl; eexists; evaluate. Qed.
Lemma fk_partial : forall rec, exists p, fk_cl @ rec ==> p.
Proof.
  intros; destruct (s_partial rec) as [a Ha]; destruct (tri_partial rec) as [b Hb].
  unfold fk_cl; eexists; evaluate.
Qed.
Lemma abs_partial : forall rec, exists p, abs_cl O @ rec ==> p.
Proof. intros; unfold abs_cl; eexists; evaluate. Qed.
Local Opaque fk_cl abs_cl s_cl tri_cl.

Local Transparent stem_cl.
Lemma stem_fwd : forall G U, label_pair G U = false -> stem_cl @ G @r U ==> Sm (Fk G U).
Proof.
  intros G U HL.
  pose proof (label_tst_spec G U) as Ht; rewrite HL in Ht; cbn [bt] in Ht.
  unfold stem_cl. fwd.
Qed.
Local Opaque stem_cl.

Local Transparent tp ord_cl.
Lemma tp_stem_head : forall G p, stem_cl @ G ==> p -> tp O @ Sm G ==> p.
Proof.
  intros G p Hp.
  pose proof (get_label_spec (Sm G)) as Hg; cbn in Hg.
  destruct (fk_partial (tp O)) as [p1 H1]; destruct (abs_partial (tp O)) as [p2 H2].
  unfold tp in *; apply Z_unfold. unfold tp_body, ord_cl. fwd.
Qed.
Local Opaque tp ord_cl.

Lemma tp_stem : forall G U, label_pair G U = false -> tp O @ Sm G @r U ==> Sm (Fk G U).
Proof.
  intros G U HL; destruct (app2_inv _ _ _ _ (stem_fwd G U HL)) as [p [H1 H2]].
  eapply app2; [apply tp_stem_head; exact H1|exact H2].
Qed.

Local Transparent plain_cl tag_cl.
Lemma plain_partial : forall u1 u2, exists p, plain_cl O @ u1 @r u2 ==> p.
Proof. intros; unfold plain_cl; eexists; evaluate. Qed.

Lemma plain_fwd : forall u1 u2 r U1 U2, r @ u1 ==> Sm U1 -> r @ u2 ==> Sm U2 ->
  label_pair U1 U2 = false -> plain_cl O @ u1 @r u2 @r r ==> Sm (Fk U1 U2).
Proof.
  intros u1 u2 r U1 U2 H1 H2 HL; pose proof (tp_stem U1 U2 HL) as Ht.
  unfold plain_cl; fwd.
Qed.

Lemma tag_fwd : forall f n r F D, concreteb n = true -> r @ f ==> Sm F ->
  O @ n @r tp O ==> Sm D -> guard_of @ D @r F ==> 'K ->
  tag_cl O @ f @r n @r r ==> Sm ('label[n]).
Proof.
  intros f n r F D Hc Hf HD HG.
  pose proof (is_concrete_bt n) as Hn; rewrite Hc in Hn; cbn [bt] in Hn.
  pose proof (isK_spec 'K) as HK; cbn in HK.
  unfold tag_cl; fwd.
Qed.
Local Opaque plain_cl tag_cl.

Local Transparent infer.
Lemma infer_head : forall t v, infer_body O @ infer O @r t ==> v -> infer O @ t ==> v.
Proof. intros; unfold infer; apply Z_unfold; exact H. Qed.
Local Opaque infer.

Lemma infer_leaf : infer O @ Lf ==> Sm Lf.
Proof. apply infer_head; unfold infer_body; evaluate. Qed.

Lemma infer_stem : forall u U, infer O @ u ==> Sm U -> infer O @ Sm u ==> Sm (Sm U).
Proof. intros u U H; apply infer_head; unfold infer_body; fwd. Qed.

Lemma infer_fork : forall u1 u2 U1 U2, tag_of (Fk u1 u2) = None ->
  infer O @ u1 ==> Sm U1 -> infer O @ u2 ==> Sm U2 -> label_pair U1 U2 = false ->
  infer O @ Fk u1 u2 ==> Sm (Fk U1 U2).
Proof.
  intros u1 u2 U1 U2 Ht H1 H2 HL.
  pose proof (get_tagged_spec (Fk u1 u2)) as HG; rewrite Ht in HG.
  destruct (appl_inv _ _ _ _ (plain_fwd u1 u2 (infer O) U1 U2 H1 H2 HL)) as [p [Hp Hq]].
  apply infer_head; unfold infer_body; fwd.
Qed.

Lemma infer_tag : forall f n F D, concreteb n = true -> infer O @ f ==> Sm F ->
  O @ n @r tp O ==> Sm D -> guard_of @ D @r F ==> 'K ->
  infer O @ 'tagged[f,n] ==> Sm ('label[n]).
Proof.
  intros f n F D Hc Hf HD HG.
  pose proof (get_tagged_some f n) as Hgt.
  destruct (appl_inv _ _ _ _ (tag_fwd f n (infer O) F D Hc Hf HD HG)) as [p [Hp Hq]].
  destruct (plain_partial (Sm ('K1 f)) ('label[n])) as [p1 Hp1].
  apply infer_head; unfold infer_body; fwd.
Qed.

Lemma ie_stem : forall u T, infer O @ u ==> Sm T -> infer_expression O @ Sm u ==> Sm T.
Proof.
  intros u T H. Local Transparent infer_expression. unfold infer_expression. apply Z_unfold.
  unfold ie_body; fwd.
Qed.

Lemma ie_fork : forall e1 e2 T1 T2 T, infer_expression O @ e1 ==> Sm T1 ->
  infer_expression O @ e2 ==> Sm T2 -> tp O @ T1 @r T2 ==> Sm T ->
  infer_expression O @ Fk e1 e2 ==> Sm T.
Proof.
  intros e1 e2 T1 T2 T H1 H2 H3. unfold infer_expression in *. apply Z_unfold.
  unfold ie_body; fwd.
Qed.
Local Opaque infer_expression.
End Inversion.

(** ** Basic properties of value typing *)

Section Properties.
Variable O : Combination.
Local Notation "t ':' T" := (infer O @ t ==> Sm T) (at level 70).

Lemma concrete_Fk : forall u v, concreteb (Fk u v) = true ->
  label_pair u v = false /\ concreteb u = true /\ concreteb v = true.
Proof.
  intros u v H; cbn in H; apply andb_prop in H as [H Hv]; apply andb_prop in H as [Hp Hu].
  destruct (label_pair u v); [discriminate|auto].
Qed.

Lemma concrete_no_tag : forall u v, concreteb (Fk u v) = true -> tag_of (Fk u v) = None.
Proof.
  intros u v H; destruct (tag_of (Fk u v)) as [[f n]|] eqn:E; [|reflexivity].
  apply tag_of_some in E; rewrite E in H; cbn in H.
  rewrite Bool.andb_false_r in H; discriminate.
Qed.

(** Self-typing: a concrete value is its own type. *)
Theorem concrete_is_self_typed : forall c, concreteb c = true -> c : c.
Proof.
  induction c as [|u IH|u IHu v IHv]; intro H.
  - apply infer_leaf.
  - apply infer_stem, IH; exact H.
  - destruct (concrete_Fk u v H) as [HL [Hu Hv]].
    apply infer_fork; auto. apply concrete_no_tag; exact H.
Qed.

Corollary concrete_is_self_typed_p : forall c, concrete c -> c : c.
Proof. intros c H; apply concrete_is_self_typed, concreteb_spec, H. Qed.

(** A label is not concrete. *)
Lemma label_not_concrete : forall n, concreteb ('label[n]) = false.
Proof. intros; reflexivity. Qed.

(** No junk: a value of an abstract type [label[n]] is a tag
    [tagged[f,n]] whose carrier type is admitted by the guard at [n]. *)
Theorem no_junk : forall v n, v : 'label[n] ->
  exists f F D, v = 'tagged[f,n] /\ concreteb n = true /\ f : F /\
    O @ n @r tp O ==> Sm D /\ guard_of @ D @r F ==> 'K.
Proof.
  intros v n H; apply infer_inv in H; inversion H; subst.
  - exists f, F, D; repeat split; assumption.
  - match goal with H : label_pair _ _ = false |- _ => cbn in H; discriminate end.
Qed.

(** Bare labels: [label[n]] has no type. *)
Theorem bare_label_untyped : forall n T, ~ ('label[n] : T).
Proof.
  intros n T H. apply infer_inv in H. inversion H as [ | | | u1 u2 U1 U2 Ht H1 H2 HL]; subst.
  apply infer_inv in H1; inversion H1 as [ |u U Hu | | ]; subst.
  apply infer_inv in Hu; inversion Hu as [ |u' U' Hu' | | ]; subst.
  apply infer_inv in Hu'; inversion Hu'; subst.
  apply infer_inv in H2; inversion H2 as [ | | | a b A B Ht2 HA HB HAB]; subst.
  apply infer_inv in HA; inversion HA; subst.
  cbn in HL; discriminate.
Qed.

(** The types of values by shape. *)
Lemma type_Lf_inv : forall v, v : Lf -> v = Lf.
Proof. intros v H; apply infer_inv in H; inversion H; auto. Qed.

Lemma type_Sm_inv : forall v U, v : Sm U -> exists u, v = Sm u /\ u : U.
Proof. intros v U H; apply infer_inv in H; inversion H; subst; eauto. Qed.

Lemma type_Fk_inv : forall v U1 U2, v : Fk U1 U2 ->
  (exists n, Fk U1 U2 = 'label[n]) \/
  (exists u1 u2, v = Fk u1 u2 /\ tag_of (Fk u1 u2) = None /\ u1 : U1 /\ u2 : U2 /\ label_pair U1 U2 = false).
Proof.
  intros v U1 U2 H; apply infer_inv in H; inversion H; subst.
  - left; eauto.
  - right; exists u1, u2; auto.
Qed.

(** A value of a concrete type is that type. *)
Theorem concrete_type_forces : forall C v, concreteb C = true -> v : C -> v = C.
Proof.
  induction C as [|C IH|C1 IH1 C2 IH2]; intros v Hc H.
  - apply type_Lf_inv; exact H.
  - destruct (type_Sm_inv _ _ H) as [u [-> Hu]]; f_equal; apply IH; assumption.
  - destruct (concrete_Fk _ _ Hc) as [HL [H1 H2]].
    destruct (type_Fk_inv _ _ _ H) as [[n E]|[u1 [u2 [-> [_ [Hu1 [Hu2 _]]]]]]].
    + rewrite E in Hc; discriminate.
    + f_equal; [apply IH1|apply IH2]; assumption.
Qed.

(** A concrete type has exactly one value, itself. *)
Corollary concrete_singleton : forall C v, concreteb C = true -> (v : C <-> v = C).
Proof.
  intros C v Hc; split; [apply concrete_type_forces; exact Hc|intros ->; apply concrete_is_self_typed; exact Hc].
Qed.
End Properties.
