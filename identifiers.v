(** * Step 82 (stage 1): codes of types, [code] and [decode].

    A type parameter is passed as a concrete code [code[A]]:

      code label[n]   = Fk (Fk Lf Lf) n
      code Lf         = Lf
      code (Sm u)     = Sm (code u)
      code (Fk u v)   = Fk (Sm (code u)) (code v)      (Fk u v not a label)

    [decode] is its syntactic inverse.  This is the quotation [q] of probe
    81 with a clause for labels in front ([absty n = Fk (Fk Lf Lf) n]
    there).  When every label in [A] has a concrete name, [code A] is
    concrete, so it is its own type ([code_self_typed]). *)

From BigStep Require Import tree typing.
From Stdlib Require Import String Bool Lia.
Open Scope string_scope.
Set Default Proof Using "Type".

Fixpoint code (t : Combination) : Combination :=
  match t with
  | Lf => Lf
  | Sm u => Sm (code u)
  | Fk u v =>
      match label_of (Fk u v) with
      | Some n => Fk (Fk Lf Lf) n
      | None => Fk (Sm (code u)) (code v)
      end
  end.

Fixpoint decode (T : Combination) : option Combination :=
  match T with
  | Lf => Some Lf
  | Sm U => option_map Sm (decode U)
  | Fk (Fk Lf Lf) n => Some ('label[n])
  | Fk (Sm A) B =>
      match decode A, decode B with
      | Some a, Some b =>
          match label_of (Fk a b) with Some _ => None | None => Some (Fk a b) end
      | _, _ => None
      end
  | _ => None
  end.

(** Every label in [A] has a concrete name. *)
Fixpoint names_concrete (t : Combination) : Prop :=
  match t with
  | Lf => True
  | Sm u => names_concrete u
  | Fk u v =>
      match label_of (Fk u v) with
      | Some n => concreteb n = true
      | None => names_concrete u /\ names_concrete v
      end
  end.

Lemma code_label : forall n, code ('label[n]) = Fk (Fk Lf Lf) n.
Proof. reflexivity. Qed.

Lemma code_plain : forall u v, label_of (Fk u v) = None -> code (Fk u v) = Fk (Sm (code u)) (code v).
Proof. intros u v H; cbn [code]; rewrite H; reflexivity. Qed.

(** [decode] inverts [code]. *)
Theorem decode_code : forall A, decode (code A) = Some A.
Proof.
  induction A as [|u IH|u IHu v IHv]; cbn [code]; [reflexivity|cbn; rewrite IH; reflexivity|].
  destruct (label_of (Fk u v)) as [n|] eqn:E.
  - apply label_of_some in E; rewrite E; reflexivity.
  - cbn [decode]; rewrite IHu, IHv, E; reflexivity.
Qed.

Theorem code_inj : forall A B, code A = code B -> A = B.
Proof.
  intros A B H; assert (E : Some A = Some B) by (rewrite <- (decode_code A), <- (decode_code B), H; reflexivity).
  inversion E; reflexivity.
Qed.

(** [code] inverts [decode] where [decode] succeeds. *)
Theorem code_decode : forall T A, decode T = Some A -> code A = T.
Proof.
  induction T as [|U IH|X IHX B IHB]; intros A H; cbn [decode] in H.
  - inversion H; reflexivity.
  - destruct (decode U) as [u|] eqn:E; inversion H; subst; cbn; f_equal; apply IH; reflexivity.
  - destruct X as [|A'|X1 X2]; try discriminate.
    + destruct (decode A') as [a|] eqn:EA; [|discriminate].
      destruct (decode B) as [b|] eqn:EB; [|discriminate].
      destruct (label_of (Fk a b)) eqn:EL; inversion H; subst.
      rewrite code_plain by exact EL. f_equal; [f_equal|apply IHB; reflexivity].
      assert (HX := IHX (Sm a)); cbn in HX; rewrite EA in HX; specialize (HX eq_refl); injection HX; auto.
    + destruct X1; try discriminate; destruct X2; try discriminate.
      inversion H; subst; reflexivity.
Qed.

(** Codes contain no labels: [code A] is concrete when the names in [A] are. *)
Lemma code_not_K1 : forall t n, code t <> Fk Lf n.
Proof.
  intros [|u|u v] n H; cbn [code] in H; try discriminate.
  destruct (label_of (Fk u v)); discriminate.
Qed.

Lemma label_pair_K1 : forall x y, label_pair x y = true -> exists m, y = Fk Lf m.
Proof. intros [|[|[| |]|]|] [| |[| |] m] H; try discriminate; eauto. Qed.

Theorem code_concrete : forall A, names_concrete A -> concreteb (code A) = true.
Proof.
  induction A as [|u IH|u IHu v IHv]; intro H; cbn [names_concrete] in H; [reflexivity|exact (IH H)|].
  cbn [code]; destruct (label_of (Fk u v)) as [n|] eqn:E.
  - cbn. exact H.
  - destruct H as [Hu Hv].
    change (negb (label_pair (Sm (code u)) (code v)) && concreteb (code u) && concreteb (code v) = true).
    rewrite (IHu Hu), (IHv Hv).
    destruct (label_pair (Sm (code u)) (code v)) eqn:EL; [|reflexivity].
    exfalso; destruct (label_pair_K1 _ _ EL) as [m Ev].
    exact (code_not_K1 v m Ev).
Qed.

(** Codes are self-typed. *)
Theorem code_self_typed : forall O A, names_concrete A -> infer O @ code A ==> Sm (code A).
Proof. intros O A H; apply concrete_is_self_typed, code_concrete, H. Qed.

(** ** [code] and [decode] as programs *)

Local Opaque get_label label_tst.

Definition code_body : Combination := Eval cbn -[get_label] in to_tree
  (star "rec" (star "t"
    (''triage[Val Lf,
              star "u" (Val Lf @@ (Ref "rec" @@ Ref "u")),
              star "u" (star "v"
                (''triage[Val Lf @@ (Val Lf @@ (Ref "rec" @@ Ref "u")) @@ (Ref "rec" @@ Ref "v"),
                          star "n" (Val Lf @@ Val (Fk Lf Lf) @@ Ref "n"),
                          Val ('K1 ('K1 Lf))]
                   @@ (op get_label @@ (Val Lf @@ Ref "u" @@ Ref "v"))))]
       @@ Ref "t"))).

Definition code_p : Combination := Z code_body.

Theorem code_p_eval : forall t, code_p @ t ==> code t.
Proof.
  induction t as [|u IH|u IHu v IHv]; unfold code_p in *; apply Z_unfold; unfold code_body.
  - evaluate.
  - cbn [code]; evaluate2; first [exact IH|evaluate2].
  - pose proof (get_label_spec (Fk u v)) as HL; cbn [code].
    destruct (label_of (Fk u v)); cbn [opt] in HL; evaluate2; first [exact IHu|exact IHv|exact HL|evaluate2].
Qed.

Definition decode_body : Combination := Eval cbn -[label_tst] in to_tree
  (star "rec" (star "T"
    (''triage[Val (Sm Lf),
              star "U" (''onStem1 (star "u" (Val Lf @@ (Val Lf @@ Ref "u"))) @@ (Ref "rec" @@ Ref "U")),
              star "A" (star "B"
                (''triage[Val Lf,
                          star "A1" (''onStem1 (star "a" (''onStem1 (star "b"
                                (op label_tst @@ Ref "a" @@ Ref "b" @@ Val Lf
                                   @@ (Val Lf @@ (Val Lf @@ Ref "a" @@ Ref "b"))))
                              @@ (Ref "rec" @@ Ref "B")))
                            @@ (Ref "rec" @@ Ref "A1")),
                          star "X1" (star "X2"
                            (''triage[''triage[Val Lf @@ (Val Lf @@ (Val Lf @@ Val 'K) @@ (Val 'K @@ Ref "B")),
                                               Val ('K1 Lf), Val ('K1 ('K1 Lf))],
                                      Val ('K1 ('K1 Lf)), Val ('K1 ('K1 ('K1 Lf)))]
                               @@ Ref "X1" @@ Ref "X2"))]
                   @@ Ref "A"))]
       @@ Ref "T"))).

Definition decode_p : Combination := Z decode_body.

Lemma decode_Fk_Sm : forall A B, decode (Fk (Sm A) B) =
  match decode A, decode B with
  | Some a, Some b => match label_of (Fk a b) with Some _ => None | None => Some (Fk a b) end
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma decode_p_eval_size : forall k T, tree_size T <= k -> decode_p @ T ==> opt (decode T).
Proof.
  induction k as [|k IH]; intros T Hk; [destruct T; cbn in Hk; lia|].
  unfold decode_p; apply Z_unfold; fold decode_p; unfold decode_body.
  destruct T as [|U|A B]; cbn [tree_size] in Hk.
  - evaluate.
  - assert (HU : decode_p @ U ==> opt (decode U)) by (apply IH; lia).
    cbn [decode]; destruct (decode U) as [u|]; cbn [opt option_map] in *;
      evaluate2; first [exact HU|evaluate2].
  - assert (HB : decode_p @ B ==> opt (decode B)) by (apply IH; lia).
    destruct A as [|A1|X1 X2].
    + cbn [decode]; evaluate2; first [exact HB|evaluate2].
    + cbn [tree_size] in Hk.
      assert (HA : decode_p @ A1 ==> opt (decode A1)) by (apply IH; lia).
      rewrite decode_Fk_Sm.
      destruct (decode A1) as [a|]; destruct (decode B) as [b|]; cbn [opt] in *;
        [pose proof (label_tst_spec a b) as HL; rewrite label_pair_of in HL;
         destruct (label_of (Fk a b)); cbn [bt opt] in *
        |destruct (label_test_spec2 a Lf) as [w [Hw _]]| |];
        split2; evaluate2; repeat first [eassumption | progress evaluate2].
    + destruct X1 as [|x|x1 x2]; [destruct X2 as [|x|x1 x2]|..]; cbn [decode];
        evaluate2; first [exact HB|evaluate2].
Qed.

Theorem decode_p_eval : forall T, decode_p @ T ==> opt (decode T).
Proof. intros T; apply (decode_p_eval_size (tree_size T)); constructor. Qed.

(** Round trip through the programs. *)
Corollary decode_p_code : forall A, decode_p @ code A ==> Sm A.
Proof. intros A; pose proof (decode_p_eval (code A)) as H; rewrite decode_code in H; exact H. Qed.
