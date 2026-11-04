(** * Array types and array append (paper: Arrays, "Array types", "Array append").

    Arrays indexed by tree-valued lengths, the first-class append program
    [array_append] and its typing ([infer_array_append_application]), and
    the uniqueness of unary indices.  The array support used by the
    matrices is in array_traversals.v. *)


(** Consumer arrays with a fixed name and a length-bearing eliminator.

    An array of n elements supplies them, in order, to a curried consumer.
    E[A,Lf] F = Sm F; E[A,Sm n] (A --> G) = E[A,n] G.
    Empty arrays retain an element witness; prepend a xs f = xs (f a).

    Arrays form a family (families.v): the abstractor [array_abstractor]
    maps each carrier to an eliminator
    [array_eliminator A n = 'wait[array_elim, A '* n]] (element type [A],
    length index [n]).  It recognises three carriers: empty ['wait['KI,A]]
    (eliminator [array_eliminator A Lf]), prepend [Array A n 'C swap A]
    ([array_eliminator A (Sm n)]) and append [Array A m 'C Array A n]
    ([array_eliminator A (index_sum n m)]).  It reads the components
    with accessors, rebuilds the carrier and compares with [equal]; append
    joins the two eliminators with [array_splice], which adds the indices.

    The file proceeds from the family program and empty/prepend/append
    carriers, through the soundness of the abstractor, to a
    first-class append program. Its inference theorem types the actual two
    runtime applications; it is not merely a theorem about their evaluated
    output. Small local declarations support examples; paper_ontology.v
    declares arrays with the other abstract families. Lengths are tree
    values, not Rocq naturals. No new core typing rule is needed. *)
From Stdlib Require Import String Lia Arith.Wf_nat List.
From TreeTyping Require Import tree typing soundness families booleans.
From TreeTyping Require Import functions data_types booleans.
Import ListNotations.
Open Scope string_scope.
Set Default Proof Using "Type".

Lemma funty_injective : forall U V U' V',
  (U --> V) = (U' --> V') -> U = U' /\ V = V'.
Proof.
  intros U V U' V' H.
  unfold funty, fun_nm in H.
  injection H; auto.
Qed.


(** Canonical length indices are self-typing unary trees. Operationally a
    fork counts as a stem over its right child; the left child is ignored.
    Unary indices by rules: a proof device only; [unary_index] below is
    defined by the program [index_check], and [unary_index_iff_rules]
    relates the two. *)
Inductive unary_index_rules : Combination -> Prop :=
| unary_rules_leaf : unary_index_rules Lf
| unary_rules_stem : forall n, unary_index_rules n -> unary_index_rules (Sm n).
Fixpoint index_sum n m :=
  match n with Lf => m | Sm k | Fk _ k => Sm (index_sum k m) end.
Inductive index_less : Combination -> Combination -> Prop :=
| index_less_zero : forall n, index_less Lf (Sm n)
| index_less_step : forall k n, index_less k n -> index_less (Sm k) (Sm n).


(** ** The array family

    An array type has the parameter [A '* n]: its element type [A] and
    its length index [n].  The eliminator program [array_elim] is
    recursive: on the parameter [A '* Lf] it returns the consumer type
    unchanged (the leaf [Lf] maps [U] to [Sm U]); on [A '* Sm k] it checks
    one argument of type [A] and continues with the eliminator at
    [A '* k].  The components are read by the accessors [acc_arg] and
    [acc_pB], so the program is total: a missing component reads as [Lf],
    and, as in [index_sum] and [consumer_type], a fork [Fk j k] in the
    index position counts as a successor of [k]. *)

Lemma is_index_spec_rules : forall n, is_index n = true <-> unary_index_rules n.
Proof.
  induction n as [|k IH|j _ k _]; cbn; split; intro H.
  - constructor.
  - reflexivity.
  - constructor; apply IH; exact H.
  - inversion H; subst; apply IH; assumption.
  - discriminate.
  - inversion H.
Qed.

(** Unary indices: the trees on which the program [index_check] says yes. *)
Definition unary_index (n : Combination) : Prop := index_check @ n ==> 'K.

Lemma is_index_spec : forall n, is_index n = true <-> unary_index n.
Proof.
  intro n; unfold unary_index; pose proof (index_check_eval n) as H; split.
  - intro E; rewrite E in H; exact H.
  - intro Hrun; pose proof (eval_deterministic _ _ Hrun _ H) as He.
    destruct (is_index n); [reflexivity|discriminate].
Qed.

(** The program agrees with the rules. *)
Lemma unary_index_iff_rules : forall n, unary_index n <-> unary_index_rules n.
Proof. intro n; rewrite <- is_index_spec, is_index_spec_rules; reflexivity. Qed.

Lemma unary_leaf : unary_index Lf.
Proof. apply unary_index_iff_rules; constructor. Qed.

Lemma unary_stem : forall n, unary_index n -> unary_index (Sm n).
Proof. intros n H; apply unary_index_iff_rules; constructor; apply unary_index_iff_rules; exact H. Qed.

(** Induction and case analysis on unary indices, by the rules. *)
Lemma unary_index_ind : forall P : Combination -> Prop,
  P Lf -> (forall n, unary_index n -> P n -> P (Sm n)) ->
  forall n, unary_index n -> P n.
Proof.
  intros P H0 HS n Hn; apply unary_index_iff_rules in Hn.
  induction Hn as [|n Hn IH]; [exact H0|].
  apply HS; [apply unary_index_iff_rules; exact Hn|exact IH].
Qed.


(** A literal unary index is recognised by running the program. *)
Ltac unary_tac := apply (proj1 (is_index_spec _)); reflexivity.

Lemma index_tag_free : forall n, unary_index n -> tag_free n = true.
Proof. intros n H; induction H using unary_index_ind; cbn; auto. Qed.
Lemma infer_index : forall AI n, unary_index n -> infer AI @ n ==> Sm n.
Proof. intros; apply infer_tag_free; apply index_tag_free; assumption. Qed.

(** The sum of indices, as a program. *)
Definition index_sum_body := Eval cbv in to_tree
  (star "self" (star "n" (star "m"
    (''triage[Ref "m", star "k" (Val Lf @@ (Ref "self" @@ Ref "k" @@ Ref "m")),
       star "j" (star "k" (Val Lf @@ (Ref "self" @@ Ref "k" @@ Ref "m")))] @@ Ref "n")))).
Definition index_sum_prog := Z index_sum_body.
Lemma index_sum_prog_eval : forall n m, index_sum_prog @ n @r m ==> index_sum n m.
Proof.
  induction n as [|k IH|j _ k IH]; intro m; cbn [index_sum].
  - eapply eval_appl; [apply Z_unfold; unfold index_sum_body; evaluate|evaluate].
  - pose proof (IH m) as H; inv_out H.
    eapply eval_appl; [apply Z_unfold; unfold index_sum_body; evaluate|].
    evaluate.
  - pose proof (IH m) as H; inv_out H.
    eapply eval_appl; [apply Z_unfold; unfold index_sum_body; evaluate|].
    evaluate.
Qed.


Definition array_nm := Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf)))))))))).
Definition array_elim_body := Eval cbv -[acc_arg acc_pB payload_elim] in to_tree
  (star "self" (star "X" (star "a"
    ((star "q" (''triage[Val Lf, Ref "q", ''K1 (Ref "q")]))
       @@ (star "k" ((''onStem1 (''wait2[Ref "self", (op acc_arg @@ Ref "X") ''* Ref "k", Ref "a"]))
                   ''C (''wait2[Val payload_elim, op acc_arg @@ Ref "X", Ref "a"])))
     @@ (op acc_pB @@ Ref "X"))))).
Definition array_elim := Z array_elim_body.
Definition array_eliminator A n := 'wait[array_elim, A '* n].
Definition Array A n := 'tagged[array_eliminator A n,array_nm].
(** The eliminator at a fixed type application. *)
Definition array_unary A a n := 'wait2[array_elim, A '* n, a].
Definition array_zero A := array_eliminator A Lf.
Definition arrow_wait A a := 'wait2[payload_elim, A, a].
Lemma arrow_wait_eval : forall A a F V, a @ F @r A ==> V -> arrow_wait A a @ F ==> V.
Proof.
  intros A a F V H; pose proof (payload_eliminator_some _ _ _ _ H) as H1.
  destruct (eval_app_r_inv _ _ _ H1) as [w [Hw Hv]]; apply wait_eval_inv in Hw.
  apply wait2_eval; eapply eval_appl; eassumption.
Qed.
Lemma arrow_wait_inv : forall A a F V, arrow_wait A a @ F ==> V -> a @ F @r A ==> V.
Proof.
  intros A a F V H; apply wait2_eval_inv in H.
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]].
  apply payload_eliminator_inv; eapply eval_appl; [apply wait_eval; exact Hw|exact Hv].
Qed.
Definition array_step A a E := ('onStem1 E) 'C arrow_wait A a.

(** One unfolding of the eliminator program. *)
Definition array_core X a :=
  match path_fn path_pB X with
  | Lf => Lf
  | Sm k | Fk _ k => array_step (path_fn path_arg X) a (array_unary (path_fn path_arg X) a k)
  end.
Local Opaque acc_arg acc_pB payload_elim.
Lemma array_elim_eval : forall X a, array_elim @ X @r a ==> array_core X a.
Proof.
  intros X a; pose proof (acc_arg_eval X) as H1; pose proof (acc_pB_eval X) as H2.
  unfold array_core; destruct (path_fn path_pB X) as [|k|j k];
  (eapply eval_appl; [unfold array_elim at 1; apply Z_unfold; unfold array_elim_body; d_eval|]);
  unfold array_step, array_unary, arrow_wait; d_eval.
Qed.
Local Opaque arrow_wait.
Lemma array_elim_app : forall X a U V,
  array_elim @ X @r a @r U ==> V <-> array_core X a @ U ==> V.
Proof.
  intros X a U V; split; intro H.
  - destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hwu]]]]; inversion Hu; subst u.
    pose proof (eval_deterministic _ _ Hw _ (array_elim_eval X a)); subst w; exact Hwu.
  - eapply eval_appl; [apply array_elim_eval | exact H].
Qed.
Lemma array_unary_app : forall A a n U V,
  array_unary A a n @ U ==> V <->
  (match n with Lf => Lf | Sm k | Fk _ k => array_step A a (array_unary A a k) end) @ U ==> V.
Proof.
  intros A a n U V; unfold array_unary at 1; split; intro H.
  - apply wait2_eval_inv, array_elim_app in H; exact H.
  - apply wait2_eval, array_elim_app; exact H.
Qed.
Lemma array_eliminator_unary : forall A n a U V,
  array_eliminator A n @ a @r U ==> V <-> array_unary A a n @ U ==> V.
Proof.
  intros A n a U V; unfold array_eliminator, array_unary; split; intro H.
  - destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]]; apply wait_eval_inv in Hw.
    apply wait2_eval; eapply eval_appl; eassumption.
  - apply wait2_eval_inv in H.
    destruct (eval_app_r_inv _ _ _ H) as [w [Hw Hv]].
    eapply eval_appl; [apply wait_eval; exact Hw|exact Hv].
Qed.

Lemma array_zero_eval : forall A a U, array_zero A @ a @r U ==> Sm U.
Proof. intros; apply array_eliminator_unary, array_unary_app; evaluate. Qed.
Lemma array_step_eval : forall A a E F G R,
  a @ F @r A ==> Sm G -> E @ G ==> Sm R -> array_step A a E @ F ==> Sm R.
Proof.
  intros A a E F G R H1 H2; unfold array_step; pose proof (arrow_wait_eval _ _ _ _ H1); evaluate.
Qed.

Lemma array_step_inv : forall A a E U R,
  array_step A a E @ U ==> Sm R ->
  exists G, a @ U @r A ==> Sm G /\ E @ G ==> Sm R.
Proof.
  intros A a E U R H; unfold array_step in H; invert_eval.
  match goal with HP : arrow_wait A a @ U ==> Sm ?V |- _ =>
    apply arrow_wait_inv in HP; exists V; auto end.
Qed.

(** An array of length [n] feeds its elements to a consumer: each element
    takes one step of type application, from [U] to [R]. *)
Fixpoint array_takes a A n U R : Prop :=
  match n with
  | Lf => U = R
  | Sm k | Fk _ k => exists G, a @ U @r A ==> Sm G /\ array_takes a A k G R
  end.
Lemma array_unary_eval : forall a A n U R,
  array_takes a A n U R -> array_unary A a n @ U ==> Sm R.
Proof.
  intros a A n; induction n as [|k IH|j _ k IH]; intros U R H; apply array_unary_app; cbn in *.
  - subst R; evaluate.
  - destruct H as [G [H1 H2]]; eapply array_step_eval; [exact H1|apply IH; exact H2].
  - destruct H as [G [H1 H2]]; eapply array_step_eval; [exact H1|apply IH; exact H2].
Qed.
Fixpoint consumer_type A n U :=
  match n with Lf => U | Sm k | Fk _ k => A --> consumer_type A k U end.
Lemma array_takes_consumer : forall AI A n U,
  array_takes (type_app AI) A n (consumer_type A n U) U.
Proof.
  intros AI A n U; induction n as [|k IH|j _ k IH]; cbn; [reflexivity| |];
    eexists; (split; [apply type_app_abstract; apply funty_eliminator_eval|exact IH]).
Qed.
Lemma array_eliminator_eval : forall AI A n U,
  array_eliminator A n @ type_app AI @r consumer_type A n U ==> Sm U.
Proof. intros; apply array_eliminator_unary, array_unary_eval, array_takes_consumer. Qed.
Lemma type_app_Array : forall AI A n U,
  type_app AI @ Array A n @r consumer_type A n U ==> Sm U.
Proof. intros; apply type_app_abstract; apply array_eliminator_eval. Qed.


Definition empty w := 'tagged['wait['KI,w],array_nm].
Definition prepend a xs := 'tagged[xs 'C swap a,array_nm].
Lemma empty_eval : forall w f, empty w @ f ==> f.
Proof. intros; apply tagged_eval; apply wait_eval; evaluate. Qed.
Lemma prepend_eval : forall a xs f g r,
  f @ a ==> g -> xs @ g ==> r -> prepend a xs @ f ==> r.
Proof. intros; apply tagged_eval; unfold swap; evaluate. Qed.

(** ** Carriers and their eliminators

    The abstractor reads the components of a carrier with accessors,
    rebuilds the carrier from them and compares it with [equal]: the
    carrier of an empty array is ['wait['KI,A]] (eliminator
    [array_eliminator A Lf]); of a prepend, [Array A n 'C swap A]
    ([array_eliminator A (Sm n)]); of an append, [Array A m 'C Array A n]
    ([array_eliminator A (index_sum n m)]).  Each
    clause is total and its result is described by a Rocq function. *)

(** [path_left] reaches [g] in [g 'C f] and [f] in ['tagged[f,t]];
    [path_right] reaches [f] in [g 'C f]. *)
Definition path_left := [dir_l; dir_s; dir_r].
Definition path_right := [dir_r].
Definition acc_left := path_prog path_left.
Definition acc_right := path_prog path_right.
Lemma acc_left_eval : forall t, acc_left @ t ==> path_fn path_left t.
Proof. intros; apply path_eval. Qed.
Lemma acc_right_eval : forall t, acc_right @ t ==> path_fn path_right t.
Proof. intros; apply path_eval. Qed.
Local Opaque acc_left acc_right equal equal1 index_sum_prog array_elim.

Local Ltac arr_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval
            | apply acc_arg_eval | apply acc_pB_eval
            | apply acc_left_eval | apply acc_right_eval ]
  end.
Local Ltac arr_eval :=
  first [ arr_atom | evaluate_expr_core arr_eval arr_head | idtac ]
with arr_head :=
  first [ arr_atom | evaluate_head_core arr_eval | idtac ].

(** [eq_case p q] splits on [p = q], rewriting [ceqb p q] and recording
    the value of [equal1 p @ q]. *)
Local Ltac eq_case p q :=
  let Hd := fresh "Hd" in let Hc := fresh "Hc" in let He := fresh "He" in
  destruct (equal1_bt_case p q) as [[Hd [Hc He]]|[Hd [Hc He]]]; try rewrite Hc.

(** The empty carrier. *)
Definition array_empty_case := Eval cbv -[equal acc_arg array_elim] in to_tree
  (star "C" (op equal @@ Ref "C" @@ ''wait[Val 'KI, op acc_arg @@ Ref "C"]
     @@ (Val Lf @@ (Val Lf @@ ''wait[Val array_elim, (op acc_arg @@ Ref "C") ''* Val Lf]))
     @@ Val Lf)).
Definition empty_fn C :=
  if ceqb C ('wait['KI, path_fn path_arg C])
  then Sm (Sm (array_eliminator (path_fn path_arg C) Lf)) else Lf.
Lemma array_empty_case_eval : forall C, array_empty_case @ C ==> empty_fn C.
Proof.
  intro C; unfold empty_fn, array_empty_case, array_eliminator.
  eq_case C ('wait['KI, path_fn path_arg C]); arr_eval.
Qed.

(** The prepend carrier: the element type is read from [swap A] and the
    index from the parameter of the tail's eliminator; the comparison
    checks the tail's element type. *)
Definition prepend_elem C := path_fn path_pB (path_fn path_right C).
Definition prepend_index C :=
  path_fn path_pB (path_fn path_arg (path_fn path_left (path_fn path_left C))).
Definition array_prepend_case :=
  Eval cbv -[equal acc_arg acc_pB acc_left acc_right array_elim] in to_tree
  (star "C" ((star "e" (op equal @@ Ref "C"
     @@ ((Val ('tagger[array_nm]) @@ ''wait[Ref "e",
            (op acc_pB @@ (op acc_right @@ Ref "C")) ''*
            (op acc_pB @@ (op acc_arg @@ (op acc_left @@ (op acc_left @@ Ref "C"))))])
         ''C ''S2[Val 'I, ''K1 (op acc_pB @@ (op acc_right @@ Ref "C"))])
     @@ (Val Lf @@ (Val Lf @@ ''wait[Ref "e", (op acc_pB @@ (op acc_right @@ Ref "C")) ''*
           (Val Lf @@ (op acc_pB @@ (op acc_arg @@ (op acc_left @@ (op acc_left @@ Ref "C")))))]))
     @@ Val Lf)) @@ Val array_elim)).
Definition prepend_fn C :=
  if ceqb C (Array (prepend_elem C) (prepend_index C) 'C swap (prepend_elem C))
  then Sm (Sm (array_eliminator (prepend_elem C) (Sm (prepend_index C)))) else Lf.
Lemma array_prepend_case_eval : forall C, array_prepend_case @ C ==> prepend_fn C.
Proof.
  intro C; unfold prepend_fn, array_prepend_case, prepend_elem, prepend_index.
  eq_case C (Array (path_fn path_pB (path_fn path_right C))
    (path_fn path_pB (path_fn path_arg (path_fn path_left (path_fn path_left C)))) 'C
    swap (path_fn path_pB (path_fn path_right C))); unfold Array, array_eliminator, swap; arr_eval.
Qed.

(** Splice joins the eliminators [E] and [D] of two arrays with element
    type [B]: it checks both against [B], reading their indices with
    accessors, and builds the eliminator whose index is the sum. *)
Definition elim_index E := path_fn path_pB (path_fn path_arg E).
Definition array_splice :=
  Eval cbv -[equal acc_arg acc_pB index_sum_prog array_elim] in to_tree
  (star "E" (star "D" (star "B"
    ((star "e" (op equal @@ Ref "E"
       @@ ''wait[Ref "e", Ref "B" ''* (op acc_pB @@ (op acc_arg @@ Ref "E"))]
     @@ (op equal @@ Ref "D"
           @@ ''wait[Ref "e", Ref "B" ''* (op acc_pB @@ (op acc_arg @@ Ref "D"))]
         @@ (Val Lf @@ ''wait[Ref "e", Ref "B" ''*
               (op index_sum_prog @@ (op acc_pB @@ (op acc_arg @@ Ref "E"))
                  @@ (op acc_pB @@ (op acc_arg @@ Ref "D")))])
         @@ Val Lf)
     @@ Val Lf)) @@ Val array_elim)))).
Definition splice_fn E D B :=
  if ceqb E (array_eliminator B (elim_index E)) then
    if ceqb D (array_eliminator B (elim_index D)) then
      Sm (array_eliminator B (index_sum (elim_index E) (elim_index D)))
    else Lf
  else Lf.
Lemma array_splice_eval : forall E D B, array_splice @ E @r D @r B ==> splice_fn E D B.
Proof.
  intros E D B; unfold splice_fn, elim_index.
  pose proof (index_sum_prog_eval (path_fn path_pB (path_fn path_arg E))
    (path_fn path_pB (path_fn path_arg D))) as HS; inv_out HS.
  eq_case E (array_eliminator B (path_fn path_pB (path_fn path_arg E)));
  eq_case D (array_eliminator B (path_fn path_pB (path_fn path_arg D)));
  unfold array_splice, array_eliminator; arr_eval.
Qed.
(** Joining eliminators adds the lengths. *)
Lemma array_splice_canonical : forall A n m,
  array_splice @ array_eliminator A n @r array_eliminator A m @r A
    ==> Sm (array_eliminator A (index_sum n m)).
Proof.
  intros A n m; pose proof (array_splice_eval (array_eliminator A n) (array_eliminator A m) A) as H.
  unfold splice_fn in H.
  assert (H1 : elim_index (array_eliminator A n) = n) by reflexivity.
  assert (H2 : elim_index (array_eliminator A m) = m) by reflexivity.
  rewrite H1, H2, !ceqb_refl in H; exact H.
Qed.

(** The append carrier: the two eliminators are read from the carrier,
    which must compose two array types; their element type is read from
    the right-hand array, and splice checks both and adds the indices. *)
Definition append_left C := path_fn path_left (path_fn path_left C).
Definition append_right C := path_fn path_left (path_fn path_right C).
Definition append_elem C := path_fn path_arg (path_fn path_arg (append_left C)).
Local Opaque array_splice.
Definition array_append_case :=
  Eval cbv -[equal acc_arg acc_pB acc_left acc_right array_splice] in to_tree
  (star "C" (op equal @@ Ref "C"
     @@ ((Val ('tagger[array_nm]) @@ (op acc_left @@ (op acc_left @@ Ref "C"))) ''C
         (Val ('tagger[array_nm]) @@ (op acc_left @@ (op acc_right @@ Ref "C"))))
     @@ (''onStem1 (star "R" (Val Lf @@ (Val Lf @@ Ref "R")))
          @@ (op array_splice @@ (op acc_left @@ (op acc_right @@ Ref "C"))
                @@ (op acc_left @@ (op acc_left @@ Ref "C"))
                @@ (op acc_arg @@ (op acc_arg @@ (op acc_left @@ (op acc_left @@ Ref "C"))))))
     @@ Val Lf)).
Definition append_fn C :=
  if ceqb C ('tagged[append_left C, array_nm] 'C 'tagged[append_right C, array_nm]) then
    match splice_fn (append_right C) (append_left C) (append_elem C) with
    | Sm R => Sm (Sm R)
    | _ => Lf
    end
  else Lf.
Lemma array_append_case_eval : forall C, array_append_case @ C ==> append_fn C.
Proof.
  intro C; unfold append_fn, array_append_case, append_elem, append_left, append_right.
  remember (path_fn path_left (path_fn path_right C)) as En eqn:HEn.
  remember (path_fn path_left (path_fn path_left C)) as Em eqn:HEm.
  remember (path_fn path_arg (path_fn path_arg Em)) as B eqn:HB.
  pose proof (array_splice_eval En Em B) as HS.
  destruct (eval_pair_inv _ _ _ HS) as [f2 [b2 [H2 [Hb2 H2']]]];
    inversion Hb2; subst b2; clear Hb2.
  destruct (eval_pair_inv _ _ _ H2) as [f1 [d1 [H1 [Hd1 H1']]]];
    inversion Hd1; subst d1; clear Hd1.
  pose proof (acc_left_eval (path_fn path_right C)) as A1; rewrite <- HEn in A1.
  pose proof (acc_left_eval (path_fn path_left C)) as A2; rewrite <- HEm in A2.
  pose proof (acc_arg_eval (path_fn path_arg Em)) as A3; rewrite <- HB in A3.
  pose proof (acc_arg_eval Em) as A4.
  pose proof (acc_left_eval C) as A5; pose proof (acc_right_eval C) as A6.
  clear HS H2.
  remember (splice_fn En Em B) as sp eqn:Hsp; clear Hsp.
  destruct sp as [|R|a b];
  eq_case C ('tagged[Em, array_nm] 'C 'tagged[En, array_nm]); arr_eval.
Qed.

(** The abstractor tries the three carriers in turn. *)
Definition array_abstractor :=
  extend array_empty_case (extend array_prepend_case (extend array_append_case ('K1 Lf))).
Definition case_value r := match r with Sm v => v | _ => Lf end.
Definition array_abstraction C :=
  match empty_fn C with
  | Sm v => v
  | _ => match prepend_fn C with
         | Sm v => v
         | _ => case_value (append_fn C)
         end
  end.
Lemma array_abstractor_eval : forall C, array_abstractor @ C ==> array_abstraction C.
Proof.
  intro C; unfold array_abstractor, array_abstraction.
  pose proof (array_empty_case_eval C) as H1.
  pose proof (array_prepend_case_eval C) as H2.
  pose proof (array_append_case_eval C) as H3.
  remember (empty_fn C) as r1 eqn:E1; destruct r1 as [|v|a b].
  2: apply extend_some; exact H1.
  2: exfalso; unfold empty_fn in E1; destruct (ceqb _ _); discriminate.
  apply extend_none_value; [exact H1|].
  remember (prepend_fn C) as r2 eqn:E2; destruct r2 as [|v|a b].
  2: apply extend_some; exact H2.
  2: exfalso; unfold prepend_fn in E2; destruct (ceqb _ _); discriminate.
  apply extend_none_value; [exact H2|].
  remember (append_fn C) as r3 eqn:E3; destruct r3 as [|v|a b]; cbn [case_value].
  2: apply extend_some; exact H3.
  - apply extend_none_value; [exact H3|evaluate].
  - exfalso; unfold append_fn in E3; destruct (ceqb _ _); [|discriminate].
    destruct (splice_fn _ _ _); discriminate.
Qed.

Lemma array_abstractor_zero : forall A,
  array_abstractor @ ('wait['KI,A]) ==> Sm (array_zero A).
Proof.
  intro A; pose proof (array_abstractor_eval ('wait['KI,A])) as H.
  unfold array_abstraction, empty_fn in H; cbn [path_fn dir_fn path_arg] in H.
  rewrite ceqb_refl in H; exact H.
Qed.

Lemma array_abstractor_step : forall A n,
  array_abstractor @ (Array A n 'C swap A) ==> Sm (array_eliminator A (Sm n)).
Proof.
  intros A n; pose proof (array_abstractor_eval (Array A n 'C swap A)) as H.
  assert (H1 : prepend_elem (Array A n 'C swap A) = A) by reflexivity.
  assert (H2 : prepend_index (Array A n 'C swap A) = n) by reflexivity.
  unfold array_abstraction, empty_fn, prepend_fn in H; rewrite H1, H2, ceqb_refl in H.
  rewrite ceqb_false in H; [exact H|intro HE; unfold Array in HE; discriminate HE].
Qed.

Lemma array_abstractor_append : forall A n m,
  array_abstractor @ (Array A m 'C Array A n) ==>
    Sm (array_eliminator A (index_sum n m)).
Proof.
  intros A n m; pose proof (array_abstractor_eval (Array A m 'C Array A n)) as H.
  assert (H1 : append_left (Array A m 'C Array A n) = array_eliminator A m) by reflexivity.
  assert (H2 : append_right (Array A m 'C Array A n) = array_eliminator A n) by reflexivity.
  assert (H3 : append_elem (Array A m 'C Array A n) = A) by reflexivity.
  pose proof (array_splice_eval (array_eliminator A n) (array_eliminator A m) A) as HS.
  pose proof (eval_deterministic _ _ HS _ (array_splice_canonical A n m)) as HSp.
  unfold array_abstraction, empty_fn, prepend_fn, append_fn in H.
  rewrite H1, H2, H3, HSp in H.
  rewrite (ceqb_false (Array A m 'C Array A n)) in H
    by (intro HE; unfold Array in HE; discriminate HE).
  rewrite (ceqb_false (Array A m 'C Array A n)) in H
    by (intro HE; unfold Array in HE; discriminate HE).
  rewrite ceqb_refl in H; exact H.
Qed.

(** The abstractor accepts exactly the three carriers. *)
Lemma array_abstractor_inv : forall C X, array_abstractor @ C ==> Sm X ->
  (exists A, C = 'wait['KI,A] /\ X = array_eliminator A Lf) \/
  (exists A n, C = Array A n 'C swap A /\ X = array_eliminator A (Sm n)) \/
  (exists A n m, C = Array A m 'C Array A n /\ X = array_eliminator A (index_sum n m)).
Proof.
  intros C X H; pose proof (eval_deterministic _ _ H _ (array_abstractor_eval C)) as HX.
  clear H; unfold array_abstraction in HX.
  remember (empty_fn C) as r1 eqn:E1; unfold empty_fn in E1.
  destruct (ceqb C ('wait['KI, path_fn path_arg C])) eqn:Hc1.
  { apply ceqb_true in Hc1; subst r1; inversion HX; subst X.
    left; exists (path_fn path_arg C); split; [exact Hc1|reflexivity]. }
  subst r1; remember (prepend_fn C) as r2 eqn:E2; unfold prepend_fn in E2.
  destruct (ceqb C _) eqn:Hc2 in E2.
  { apply ceqb_true in Hc2; subst r2; inversion HX; subst X.
    right; left; do 2 eexists; split; [exact Hc2|reflexivity]. }
  subst r2; unfold case_value, append_fn in HX.
  destruct (ceqb C _) eqn:Hc3 in HX; [|discriminate].
  apply ceqb_true in Hc3.
  unfold splice_fn in HX.
  destruct (ceqb (append_right C) _) eqn:Hc4 in HX; [|discriminate].
  destruct (ceqb (append_left C) _) eqn:Hc5 in HX; [|discriminate].
  apply ceqb_true in Hc4; apply ceqb_true in Hc5; inversion HX; subst X.
  right; right; do 3 eexists; split; [|reflexivity].
  rewrite Hc3 at 1; rewrite Hc4 at 1; rewrite Hc5 at 1; reflexivity.
Qed.


Local Opaque index_check.


(** Elimination determines the consumer type. *)
Lemma array_unary_exact : forall a A n U R,
  array_unary A a n @ U ==> Sm R -> array_takes a A n U R.
Proof.
  intros a A n; induction n as [|k IH|j _ k IH]; intros U R H; apply array_unary_app in H; cbn.
  - inversion H; reflexivity.
  - destruct (array_step_inv _ _ _ _ _ H) as [V [HV HE]]; exists V; split; [exact HV|apply IH; exact HE].
  - destruct (array_step_inv _ _ _ _ _ H) as [V [HV HE]]; exists V; split; [exact HV|apply IH; exact HE].
Qed.

Lemma array_eliminator_exact : forall A n a U R,
  array_eliminator A n @ a @r U ==> Sm R -> array_takes a A n U R.
Proof. intros A n a U R H; apply array_eliminator_unary in H; exact (array_unary_exact _ _ _ _ _ H). Qed.

Lemma array_wrong_domain : forall AI A B n U R,
  A <> B -> ~ type_app AI @ Array A (Sm n) @r (B --> U) ==> Sm R.
Proof.
  intros AI A B n U R Hneq H; apply app_abstract_inv in H.
  apply array_eliminator_exact in H; cbn [array_takes] in H.
  destruct H as [G [H _]]; apply app_abstract_inv in H.
  apply funty_eliminator_inv in H; destruct H; congruence.
Qed.

(** The following theorem types application of the array program itself,
    not merely a separately evaluated result. *)
Lemma infer_array_application : forall AI xs A n f U,
  infer AI @ xs ==> Sm (Array A n) ->
  infer AI @ f ==> Sm (consumer_type A n U) ->
  infer_expression AI @ (xs @ f) ==> Sm U.
Proof.
  intros; eapply infer_expression_fork;
    [apply infer_expression_stem; eassumption|
     apply infer_expression_stem; eassumption|apply type_app_Array].
Qed.

Definition append_carrier xs ys := ys 'C xs.

Lemma append_carrier_eval : forall xs ys f g r,
  xs @ f ==> g -> ys @ g ==> r -> append_carrier xs ys @ f ==> r.
Proof. intros; unfold append_carrier; evaluate. Qed.

Lemma array_takes_add : forall a A n m U R,
  array_takes a A (index_sum n m) U R ->
  exists G, array_takes a A n U G /\ array_takes a A m G R.
Proof.
  intros a A n; induction n as [|k IH|j _ k IH]; intros m U R H; cbn in *.
  - exists U; split; [reflexivity|exact H].
  - destruct H as [G [H1 H2]]; destruct (IH _ _ _ H2) as [Q [H3 H4]].
    exists Q; split; [exists G; auto|exact H4].
  - destruct H as [G [H1 H2]]; destruct (IH _ _ _ H2) as [Q [H3 H4]].
    exists Q; split; [exists G; auto|exact H4].
Qed.

Lemma consumer_type_add : forall A n m U,
  consumer_type A (index_sum n m) U = consumer_type A n (consumer_type A m U).
Proof. intros A n; induction n; intros; cbn; [reflexivity|rewrite IHn; reflexivity|rewrite IHn2; reflexivity]. Qed.

Lemma infer_append_carrier : forall AI xs ys A n m,
  infer AI @ xs ==> Sm (Array A n) ->
  infer AI @ ys ==> Sm (Array A m) ->
  infer AI @ append_carrier xs ys ==> Sm (Array A m 'C Array A n).
Proof. intros; unfold append_carrier; infer_tac. Qed.

Lemma type_app_append_carrier : forall AI A n m U,
  type_app AI @ (Array A m 'C Array A n) @r
    consumer_type A (index_sum n m) U ==> Sm U.
Proof.
  intros; rewrite consumer_type_add.
  eapply type_app_compose; [solve [reject_name]| | |]; [intros; discriminate|apply type_app_Array|apply type_app_Array].
Qed.

Lemma infer_append_carrier_application : forall AI xs ys A n m f U,
  infer AI @ xs ==> Sm (Array A n) ->
  infer AI @ ys ==> Sm (Array A m) ->
  infer AI @ f ==> Sm (consumer_type A (index_sum n m) U) ->
  infer_expression AI @ (append_carrier xs ys @ f) ==> Sm U.
Proof.
  intros; eapply infer_expression_fork.
  - apply infer_expression_stem; eapply infer_append_carrier; eassumption.
  - apply infer_expression_stem; eassumption.
  - apply type_app_append_carrier.
Qed.

Lemma append_carrier_empty_left : forall w ys f r,
  ys @ f ==> r -> append_carrier (empty w) ys @ f ==> r.
Proof. intros; eapply append_carrier_eval; [apply empty_eval|eassumption]. Qed.

Lemma append_carrier_empty_right : forall xs w f r,
  xs @ f ==> r -> append_carrier xs (empty w) @ f ==> r.
Proof. intros; eapply append_carrier_eval; [eassumption|apply empty_eval]. Qed.

(** ** The declaration of arrays

    The abstractor [array_abstractor] is sound for every typing
    declarations ([array_abstractor_sound]). *)
Definition supports_arrays AI := AI @ array_nm ==> ('K1 (array_abstractor)).


(** Elimination agrees with type application to the carrier. *)
Lemma array_abstractor_sound : forall AI C E U V,
  array_abstractor @ C ==> Sm E -> E @ type_app AI @r U ==> Sm V ->
  type_app AI @ C @r U ==> Sm V.
Proof.
  intros AI C E U V HL HE.
  destruct (array_abstractor_inv _ _ HL) as [[A [-> ->]]|[[A [n [-> ->]]]|[A [n [m [-> ->]]]]]];
    apply array_eliminator_exact in HE; cbn [array_takes] in HE.
  - subst U; apply type_app_wait with (V := 'I); [apply type_app_K_ev|apply type_app_I].
  - destruct HE as [G [H1 H2]].
    eapply type_app_compose with (VF := G); [solve [reject_name]| | |].
    + intros; discriminate.
    + apply type_app_swap2; exact H1.
    + apply type_app_abstract; apply array_eliminator_unary, array_unary_eval; exact H2.
  - destruct (array_takes_add _ _ _ _ _ _ HE) as [G [H1 H2]].
    eapply type_app_compose with (VF := G); [solve [reject_name]| | |].
    + intros; discriminate.
    + apply type_app_abstract; apply array_eliminator_unary, array_unary_eval; exact H1.
    + apply type_app_abstract; apply array_eliminator_unary, array_unary_eval; exact H2.
Qed.


(** Prepending checks the element type; appending checks that the element
    types agree. *)
Lemma array_prepend_wrong_domain : forall A B n,
  A <> B -> array_abstractor @ (Array B n 'C swap A) ==> Lf.
Proof.
  intros A B n Hneq.
  pose proof (array_abstractor_eval (Array B n 'C swap A)) as H.
  assert (H1 : prepend_elem (Array B n 'C swap A) = A) by reflexivity.
  assert (H2 : prepend_index (Array B n 'C swap A) = n) by reflexivity.
  unfold array_abstraction, empty_fn, prepend_fn, append_fn in H; rewrite H1, H2 in H.
  rewrite (ceqb_false (Array B n 'C swap A)) in H
    by (intro HE; unfold Array in HE; discriminate HE).
  rewrite (ceqb_false (Array B n 'C swap A)) in H
    by (intro HE; unfold Array, array_eliminator in HE; injection HE; intros; congruence).
  rewrite (ceqb_false (Array B n 'C swap A)) in H
    by (intro HE; unfold Array, swap in HE; discriminate HE).
  exact H.
Qed.
Lemma array_abstractor_wrong_domain : forall A B n m,
  A <> B -> array_abstractor @ (Array B m 'C Array A n) ==> Lf.
Proof.
  intros A B n m Hneq.
  pose proof (array_abstractor_eval (Array B m 'C Array A n)) as H.
  assert (H1 : append_left (Array B m 'C Array A n) = array_eliminator B m) by reflexivity.
  assert (H2 : append_right (Array B m 'C Array A n) = array_eliminator A n) by reflexivity.
  assert (H3 : append_elem (Array B m 'C Array A n) = B) by reflexivity.
  assert (H4 : elim_index (array_eliminator A n) = n) by reflexivity.
  unfold array_abstraction, empty_fn, prepend_fn, append_fn, splice_fn in H.
  rewrite H1, H2, H3, H4 in H.
  rewrite (ceqb_false (array_eliminator A n)) in H
    by (intro HE; unfold array_eliminator in HE; injection HE; intros; congruence).
  rewrite (ceqb_false (Array B m 'C Array A n)) in H
    by (intro HE; unfold Array in HE; discriminate HE).
  rewrite (ceqb_false (Array B m 'C Array A n)) in H
    by (intro HE; unfold Array in HE; discriminate HE).
  destruct (ceqb _ _) in H; exact H.
Qed.

(** The array clause of declarations. *)
Definition array_case_package :
  { t : Combination | to_tree (tcase (Val array_nm) (Val ('K1 array_abstractor))) = t }.
Proof. eexists; simpl; reflexivity. Defined.
Definition array_case := Eval cbn in proj1_sig array_case_package.
Lemma array_case_compilation :
  to_tree (tcase (Val array_nm) (Val ('K1 array_abstractor))) = array_case.
Proof. unfold array_case; exact (proj2_sig array_case_package). Qed.
Lemma array_case_some :
  array_case @ array_nm ==> Sm ('K1 array_abstractor).
Proof. rewrite <- array_case_compilation; apply tcase_eq. Qed.
Lemma array_case_none : forall N,
  N <> array_nm -> array_case @ N ==> Lf.
Proof.
  intros N Hneq; rewrite <- array_case_compilation.
  apply tcase_neq; intros Heq; apply Hneq; symmetry; exact Heq.
Qed.
Lemma array_case_registers :
  clause_registers array_case array_nm ('K1 array_abstractor).
Proof. rewrite <- array_case_compilation; apply tcase_registers. Qed.


Definition append_value xs ys := 'tagged[append_carrier xs ys,array_nm].
Lemma append_value_eval : forall xs ys f g r,
  xs @ f ==> g -> ys @ g ==> r -> append_value xs ys @ f ==> r.
Proof. intros; apply tagged_eval; eapply append_carrier_eval; eassumption. Qed.
Lemma infer_append_value : forall AI xs ys A n m,
  supports_arrays AI ->
  infer AI @ xs ==> Sm (Array A n) -> infer AI @ ys ==> Sm (Array A m) ->
  infer AI @ append_value xs ys ==> Sm (Array A (index_sum n m)).
Proof.
  intros AI xs ys A n m HS HX HY.
  apply infer_tagged with (F := Array A m 'C Array A n).
  - apply infer_append_carrier; assumption.
  - apply infer_tag_free; reflexivity.
  - eapply declaration_apply; [exact HS|apply array_abstractor_append].
Qed.
Lemma infer_empty : forall AI w A,
  supports_arrays AI -> infer AI @ w ==> Sm A ->
  infer AI @ empty w ==> Sm (Array A Lf).
Proof.
  intros AI w A HS Hw; apply infer_tagged with (F := 'wait['KI,A]).
  - infer_tac.
  - apply infer_tag_free; reflexivity.
  - eapply declaration_apply; [exact HS|apply array_abstractor_zero].
Qed.
Lemma infer_prepend : forall AI a xs A n,
  supports_arrays AI ->
  infer AI @ a ==> Sm A -> infer AI @ xs ==> Sm (Array A n) ->
  infer AI @ prepend a xs ==> Sm (Array A (Sm n)).
Proof.
  intros AI a xs A n HS Ha Hxs; apply infer_tagged with (F := Array A n 'C swap A).
  - unfold swap; infer_tac.
  - apply infer_tag_free; reflexivity.
  - eapply declaration_apply; [exact HS|apply array_abstractor_step].
Qed.

Definition array_ontology :=
  extend array_case (extend list_case ordinary_ontology).
Lemma array_ontology_row : array_ontology @ fun_nm ==> function_abstractor.
Proof.
  unfold array_ontology.
  apply extend_none_value; [apply array_case_none; unfold array_nm, fun_nm; discriminate|].
  apply extend_none_value; [apply list_case_none; unfold list_nm, fun_nm; discriminate|].
  exact (functions_declared ordinary_decl).
Qed.
Canonical Structure array_decl := mkDecl array_ontology array_ontology_row.
Lemma array_ontology_support : supports_arrays array_ontology.
Proof. apply extend_some; apply array_case_some. Qed.


Lemma array_ontology_supports_list : supports_list array_ontology.
Proof.
 unfold supports_list, array_ontology; apply extend_none_value;
 [apply array_case_none; discriminate|apply extend_some; apply list_case_some].
Qed.
Lemma array_ontology_supports_number : supports_number array_ontology.
Proof.
 unfold supports_number, array_ontology; apply extend_none_value;
 [apply array_case_none; discriminate|].
 apply extend_none_value; [apply list_case_none; discriminate|].
 apply ordinary_ontology_supports_number.
Qed.
Lemma array_ontology_supports_booleans : supports_booleans array_ontology.
Proof.
 unfold supports_booleans, array_ontology; apply extend_none_value;
 [apply array_case_none; discriminate|].
 apply extend_none_value; [apply list_case_none; discriminate|].
 apply ordinary_ontology_supports_booleans.
Qed.

Definition second_leaf := lam ('K1 (lam 'I Lf)) Lf.
Definition appended_leaves :=
  append_value (prepend Lf (empty Lf)) (prepend Lf (empty Lf)).
Example infer_appended_leaves :
  infer array_ontology @ appended_leaves ==> Sm (Array Lf (Sm (Sm Lf))).
Proof.
  unfold appended_leaves; eapply infer_append_value with (n := Sm Lf) (m := Sm Lf);
    repeat first [apply array_ontology_support|apply infer_prepend|
      apply infer_empty|apply infer_leaf].
Qed.
Example infer_prepend_to_appended_leaves :
  infer array_ontology @ prepend Lf appended_leaves ==> Sm (Array Lf (Sm (Sm (Sm Lf)))).
Proof.
  apply infer_prepend;
    [apply array_ontology_support|apply infer_leaf|apply infer_appended_leaves].
Qed.
Example appended_leaves_eval : appended_leaves @ second_leaf ==> Lf.
Proof.
  unfold appended_leaves; eapply append_value_eval.
  - eapply prepend_eval.
    + unfold second_leaf, lam; apply tagged_eval; evaluate.
    + apply empty_eval.
  - eapply prepend_eval.
    + unfold lam; apply tagged_eval; evaluate.
    + apply empty_eval.
Qed.
Example infer_appended_leaves_application : 
  infer_expression array_ontology @ (appended_leaves @ second_leaf) ==> Sm Lf.
Proof.
  eapply infer_array_application; [apply infer_appended_leaves|].
  unfold second_leaf; eapply infer_lam.

  - apply infer_K1; eapply infer_lam;
      [apply infer_I|apply infer_leaf|apply type_app_I].
  - apply infer_leaf.
  - apply type_app_K_ev.
Qed.

(** First-class array append [array_append]. Both inputs arrive in one pair; the program
    constructs the same tagged composition checked by the constructor above.
    The lengths and element type occur only in the typing theorem. *)
Definition array_append := Eval cbn in to_tree
  (star "p" (Val ('tagger[array_nm]) @@
    ((Val 'snd @@ Ref "p") ''C (Val 'fst @@ Ref "p")))).
Lemma array_append_eval : forall xs ys,
  array_append @ (xs '* ys) ==> append_value xs ys.
Proof. intros; unfold array_append, append_value, append_carrier; cbn; evaluate. Qed.
Lemma array_append_tag_free : tag_free array_append = true.
Proof. unfold array_append, array_nm; tag_free_tac. Qed.
Lemma infer_array_append : forall AI,
  infer AI @ array_append ==> Sm array_append.
Proof. intro AI; apply infer_tag_free; apply array_append_tag_free. Qed.
Lemma type_app_array_append : forall AI A n m,
  supports_arrays AI ->
  type_app AI @ array_append @r (Array A n '* Array A m) ==> Sm (Array A (index_sum n m)).
Proof.
  intros AI A n m HS; unfold array_append; type_app_tac.
  apply type_app_stem_ev; apply type_app_stem_tagged.
  eapply declaration_apply; [exact HS|apply array_abstractor_append].
Qed.

(** [array_append] is its own type, and its type
    application computes the length of the result. *)
Theorem array_append_polymorphic : forall AI, supports_arrays AI ->
  infer AI @ array_append ==> Sm array_append /\
  forall A n m, type_app AI @ array_append @r (Array A n '* Array A m) ==>
    Sm (Array A (index_sum n m)).
Proof.
  intros AI HS; split; [apply infer_array_append|].
  intros A n m; exact (type_app_array_append AI A n m HS).
Qed.

Theorem infer_array_append_application : forall AI xs ys A n m,
  supports_arrays AI ->
  infer AI @ xs ==> Sm (Array A n) -> infer AI @ ys ==> Sm (Array A m) ->
  infer_expression AI @ (array_append @ (xs '* ys)) ==> Sm (Array A (index_sum n m)).
Proof.
  intros AI xs ys A n m HS HX HY; eapply infer_expression_fork.
  - apply infer_expression_stem; apply infer_array_append.
  - apply infer_expression_stem; apply infer_product_value; eassumption.
  - apply type_app_array_append; exact HS.
Qed.

Example append_two_singletons :
  array_append @ (prepend Lf (empty Lf) '* prepend Lf (empty Lf))
    ==> appended_leaves.
Proof. apply array_append_eval. Qed.
Example infer_append_two_singletons :
  infer_expression array_ontology @
    (array_append @ (prepend Lf (empty Lf) '* prepend Lf (empty Lf)))
      ==> Sm (Array Lf (Sm (Sm Lf))).
Proof.
  eapply infer_array_append_application with (n := Sm Lf) (m := Sm Lf);
    repeat first [apply array_ontology_support|apply infer_prepend|
      apply infer_empty|apply infer_leaf].
Qed.
Example append_consumer_eval :
  array_append @ (prepend Lf (empty Lf) '* prepend Lf (empty Lf)) @r second_leaf ==> Lf.
Proof.
  eapply eval_appl; [apply append_two_singletons|apply appended_leaves_eval].
Qed.
Example infer_append_consumer : 
  infer_expression array_ontology @
    (array_append @ (prepend Lf (empty Lf) '* prepend Lf (empty Lf)) @r second_leaf)
      ==> Sm Lf.
Proof.
  eapply infer_expression_fork.
  - apply infer_append_two_singletons.
  - apply infer_expression_stem.
    unfold second_leaf; eapply infer_lam.

    + apply infer_K1; eapply infer_lam;
        [apply infer_I|apply infer_leaf|apply type_app_I].
    + apply infer_leaf.
    + apply type_app_K_ev.
  - apply (type_app_Array array_ontology Lf (Sm (Sm Lf)) Lf).
Qed.

(** * Uniqueness of indices

    The index is a component of the parameter of the eliminator, so equal
    eliminators (and equal array types) have equal indices. *)
Lemma array_eliminator_index_injective : forall n,
  unary_index n -> forall m A B, unary_index m ->
  array_eliminator A n = array_eliminator B m -> n = m.
Proof. intros n _ m A B _ HE; unfold array_eliminator in HE; injection HE; auto. Qed.
Lemma Array_index_injective : forall A B n m,
  unary_index n -> unary_index m -> Array A n = Array B m -> n = m.
Proof.
  intros A B n m Hn Hm HE; unfold Array in HE.
  assert (HE' : array_eliminator A n = array_eliminator B m) by congruence.
  eapply array_eliminator_index_injective; eassumption.
Qed.

(** One-round soundness of the declarations. *)
Lemma plain_array_cond2 : forall AI, abstractor_sound_by_typing AI array_abstractor.
Proof. intros AI; exact (array_abstractor_sound AI). Qed.

Lemma array_ontology_plain_sound_for : forall (AI : Decl),
  supports_booleans AI -> supports_list AI ->
  plain_intro_sound_for array_ontology AI.
Proof.
  intros AI HB HL; unfold array_ontology.
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ array_case_compilation)
    |eapply plain_declared_sound_for; [apply array_case_registers|apply plain_array_cond2]|].
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ list_case_compilation)
    |eapply plain_declared_sound_for; [apply list_case_registers|apply plain_list_cond2]|].
  unfold ordinary_ontology.
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ sum_case_compilation)
    |eapply plain_declared_sound_for; [apply sum_case_registers|apply plain_sum_cond2]|].
  unfold option_ontology.
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ option_case_compilation)
    |eapply plain_declared_sound_for; [apply option_case_registers|apply plain_option_cond2]|].
  unfold nat_ontology.
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ nat_case_compilation)
    |eapply plain_declared_sound_for; [apply nat_case_registers|apply plain_nat_cond2]|].
  unfold bool_ontology.
  apply plain_extend_intro_sound_for;
    [apply (compiled_tcase_never_fork _ _ _ bool_case_compilation)
    |eapply plain_declared_sound_for; [apply bool_case_registers|apply plain_bool_cond2]|].
  unfold function_ontology.
  apply plain_extend_intro_sound_for;
    [apply function_case_never_fork|apply plain_function_declared_sound_for|].
  apply plain_empty_ontology_sound_for.
Qed.

Lemma array_ontology_EPT : forall e v T,
  e ==> v -> infer_expression array_ontology @ e ==> Sm T ->
  infer array_ontology @ v ==> Sm T.
Proof.
  intros e v T He Ht.
  assert (Hs : plain_intro_sound array_ontology).
  { intros C N E U V HI HE.
    exact (array_ontology_plain_sound_for array_decl
      array_ontology_supports_booleans array_ontology_supports_list C N E U V HI HE). }
  exact (plain_evaluation_preserves_typing array_ontology e v Hs He T Ht).
Qed.
