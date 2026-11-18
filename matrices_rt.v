(** * Step 82, stage 7, part 1: matrices.

    [Matrix m n = Array (Array Nat n) m].  Multiplication receives [xs * ys]:
    - [heads ys] is the first column of [ys];
    - [zeros v] is a row of zeros as long as [v];
    - [axpy (x * (y * a))] is [x * y + a], entry by entry;
    - [row_times (r * (ys * z))] is the row [r] times [ys], from the zero row [z];
    - [mrows (xs * (ys * (z * e)))] multiplies each row of [xs]; the rows are
      prepended at the code of [Array Nat p], built at run time from the
      length [p] of [z] ([array_length]), and the result ends in the empty
      array [e] at the end of [ys] ([array_last_empty]);
    - [width_check (xs * ys) = zero @ (r * K1 c)] for the first row [r] of
      [xs] and the first column [c] of [ys]: type application of [Nat] at
      [R * K1 C] needs [C = R];
    - [matrix_mult t = K @ (matrix_product @ t) @ (width_check @ t)].
    Every typing unfolds along a length; [row_times] is typed for rows and
    matrices of any lengths, so that the refusal of mismatched dimensions
    comes from the width check alone. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology fun_ontology size_queries poly scott_arithmetic array_family array_poly.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

(** ** Forward rules for refusal *)

Section Refusal.
Variable O : Combination.
Local Opaque get_label resv label_tst elim_of.

Lemma s_fwd_any : forall G H U V W v, tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Sm W ->
  tp O @ V @r W ==> v -> s_cl @ tp O @r G @r H @r U ==> v.
Proof. intros G H U V W v H1 H2 H3; unfold s_cl; ev3. Qed.

Lemma s_refuse_H : forall G H U V p, tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Lf -> tp O @ V ==> p ->
  s_cl @ tp O @r G @r H @r U ==> Lf.
Proof. intros G H U V p H1 H2 H3; unfold s_cl; ev3. Qed.

Lemma tp_K1_partial : forall Y, tp O @ ('K1 Y) ==> ('K1 (Sm Y)).
Proof. intros Y; apply tp_head_ord; [reflexivity|apply ord_fork, fk_K1]. Qed.

Theorem tp_S2_any : forall G H U V W v, label_of ('S2[G,H]) = None ->
  tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Sm W -> tp O @ V @r W ==> v ->
  tp O @ 'S2[G,H] @r U ==> v.
Proof.
  intros G H U V W v HL H1 H2 H3.
  destruct (appl_inv _ _ _ _ (s_fwd_any G H U V W v H1 H2 H3)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [exact HL|apply ord_fork, fk_S2; exact Hq]|exact Hq'].
Qed.

Theorem tp_S2_refuse_H : forall G H U V p, label_of ('S2[G,H]) = None ->
  tp O @ G @r U ==> Sm V -> tp O @ H @r U ==> Lf -> tp O @ V ==> p -> tp O @ 'S2[G,H] @r U ==> Lf.
Proof.
  intros G H U V p HL H1 H2 H3.
  destruct (appl_inv _ _ _ _ (s_refuse_H G H U V p H1 H2 H3)) as [q [Hq Hq']].
  eapply eval_appl; [apply tp_head_ord; [exact HL|apply ord_fork, fk_S2; exact Hq]|exact Hq'].
Qed.
End Refusal.

Lemma nat_eliminator_refuse : forall n a B S C, a @ S @r 'label[n] ==> Sm C -> C <> B ->
  nat_eliminator @ n @r a @r (B '* S) ==> Lf.
Proof.
  intros n a B S C H HC; unfold nat_eliminator.
  pose proof (get_pn_spec (B '* S)) as H1; pose proof (get_rr_spec (B '* S)) as H2; cbn in H1, H2.
  pose proof (equal_eq (B '* S)) as He; pose proof (equal_neq _ _ HC) as He2.
  split2; evaluate2; repeat first [eassumption | progress evaluate2].
Qed.

Lemma type_app_NatA : forall B S, tp PO @ S @r Nat ==> Sm B -> tp PO @ Nat @r (B '* S) ==> Sm B.
Proof.
  intros B S H; eapply tp_abs; [apply PO_static; reflexivity|].
  apply elim_of_fwd, nat_eliminator_eval; exact H.
Qed.

Theorem type_app_Nat_refuse : forall B S C, tp PO @ S @r Nat ==> Sm C -> C <> B ->
  tp PO @ Nat @r (B '* S) ==> Lf.
Proof.
  intros B S C H HC; eapply tp_abs; [apply PO_static; reflexivity|].
  apply elim_of_fwd; eapply nat_eliminator_refuse; eassumption.
Qed.

(** ** The programs *)

Definition array_uncons : Combination := swap (Lf '* 'I).
(** [gen_empty @ code Nat], applied through [K1 (code Nat) @ x] so that the application is not closed. *)
Definition E_t (x : Term) : Term := op gen_empty @@ (Val ('K1 (code Nat)) @@ x).
Definition pre_t (c x xs : Term) : Term := op gen_prepend @@ (c ''* (x ''* xs)).
Definition fst_t' (x : Term) : Term := Val 'fst @@ x.
Definition snd_t' (x : Term) : Term := Val 'snd @@ x.

Definition array_length_body : Combination := Eval cbn in to_tree
  (star "self" (star "xs" (Ref "xs" @@ (Val Lf ''* (star "p" (Val Lf @@ (Ref "self" @@ snd_t' (Ref "p")))))))).
Definition array_length : Combination := Z array_length_body.
Definition array_last_empty_body : Combination := Eval cbn in to_tree
  (star "self" (star "xs" (Ref "xs" @@ (Ref "xs" ''* (star "p" (Ref "self" @@ snd_t' (Ref "p"))))))).
Definition array_last_empty : Combination := Z array_last_empty_body.

Definition zeros_body : Combination := Eval cbn -[gen_empty gen_prepend zero] in to_tree
  (star "self" (star "v" (Ref "v" @@ (E_t (Ref "v") ''* (star "p"
     (pre_t (Val (code Nat)) (Val zero) (Ref "self" @@ snd_t' (Ref "p")))))))).
Definition zeros : Combination := Z zeros_body.

Definition axpy_body : Combination := Eval cbn -[gen_empty gen_prepend add mul] in to_tree
  (let t := Ref "t" in let x := fst_t' t in let y := fst_t' (snd_t' t) in let a := snd_t' (snd_t' t) in
   let p := Ref "p" in let q := Ref "q" in
   star "self" (star "t" (y @@ (E_t t ''* (star "p" (a @@ (E_t t ''* (star "q"
     (pre_t (Val (code Nat)) (op add @@ ((op mul @@ (x ''* fst_t' p)) ''* fst_t' q))
        (Ref "self" @@ (x ''* (snd_t' p ''* snd_t' q)))))))))))).
Definition axpy : Combination := Z axpy_body.

Definition row_times_body : Combination := Eval cbn -[axpy] in to_tree
  (let t := Ref "t" in let r := fst_t' t in let ys := fst_t' (snd_t' t) in let z := snd_t' (snd_t' t) in
   let p := Ref "p" in let q := Ref "q" in
   star "self" (star "t" (r @@ (z ''* (star "p" (ys @@ (z ''* (star "q"
     (op axpy @@ (fst_t' p ''* (fst_t' q ''* (Ref "self" @@ (snd_t' p ''* (snd_t' q ''* z)))))))))))))).
Definition row_times : Combination := Z row_times_body.

(** The code of [Array Nat q], built at run time from a row of length [q]. *)
Definition row_code_t (z : Term) : Term :=
  Val Lf @@ (Val Lf @@ Val Lf @@ Val Lf) @@ (Val Lf @@ Val array_nm @@ (Val Lf @@ Val (code Nat) @@ (op array_length @@ z))).

Definition rows_body : Combination := Eval cbn -[row_times array_length gen_prepend array_nm] in to_tree
  (let t := Ref "t" in let xs := fst_t' t in let ys := fst_t' (snd_t' t) in
   let z := fst_t' (snd_t' (snd_t' t)) in let e := snd_t' (snd_t' (snd_t' t)) in
   let p := Ref "p" in
   star "self" (star "t" (xs @@ (e ''* (star "p"
     (pre_t (row_code_t z) (op row_times @@ (fst_t' p ''* (ys ''* z)))
        (Ref "self" @@ (snd_t' p ''* (ys ''* (z ''* e)))))))))).
Definition mrows : Combination := Z rows_body.

Definition heads_body : Combination := Eval cbn -[gen_empty gen_prepend array_uncons] in to_tree
  (star "self" (star "ys" (Ref "ys" @@ (E_t (Ref "ys") ''* (star "p"
     (pre_t (Val (code Nat)) (fst_t' (op array_uncons @@ fst_t' (Ref "p"))) (Ref "self" @@ snd_t' (Ref "p")))))))).
Definition heads : Combination := Z heads_body.

Definition width_check : Combination := Eval cbn -[zero array_uncons heads] in to_tree
  (star "t" (Val zero @@ (fst_t' (op array_uncons @@ fst_t' (Ref "t")) ''* (Val 'K @@ (op heads @@ snd_t' (Ref "t")))))).

Definition matrix_product : Combination := Eval cbn -[mrows zeros array_uncons array_last_empty] in to_tree
  (star "t" (op mrows @@ (fst_t' (Ref "t") ''* (snd_t' (Ref "t") ''*
     ((op zeros @@ fst_t' (op array_uncons @@ snd_t' (Ref "t"))) ''* (op array_last_empty @@ snd_t' (Ref "t"))))))).

Definition matrix_mult : Combination := Eval cbn -[matrix_product width_check] in to_tree
  (star "t" (Val 'K @@ (Val matrix_product @@ Ref "t") @@ (Val width_check @@ Ref "t"))).

Definition Matrix (m n : Combination) : Combination := Array (Array Nat n) m.

(** ** Types, by computation *)

Definition T_addA := Eval vm_compute in tyA add.
Definition T_mulA := Eval vm_compute in tyA mul.
Definition T_z := Eval vm_compute in tyA zeros.
Definition T_axpy := Eval vm_compute in tyA axpy.
Definition T_rt := Eval vm_compute in tyA row_times.
Definition T_mrows := Eval vm_compute in tyA mrows.
Definition T_heads := Eval vm_compute in tyA heads.
Definition T_wc := Eval vm_compute in tyA width_check.
Definition T_mp := Eval vm_compute in tyA matrix_product.
Definition T_mm := Eval vm_compute in tyA matrix_mult.

Lemma infer_matrix_mult : infer PO @ matrix_mult ==> Sm T_mm. Proof. by_runAr. Qed.
Lemma type_app_add_A : tp PO @ T_addA @r (Nat '* Nat) ==> Sm Nat. Proof. by_runAr. Qed.
Lemma type_app_mul_A : tp PO @ T_mulA @r (Nat '* Nat) ==> Sm Nat. Proof. by_runAr. Qed.

Lemma array_length_concrete : concreteb array_length = true. Proof. vm_compute; reflexivity. Qed.
Lemma array_last_empty_concrete : concreteb array_last_empty = true. Proof. vm_compute; reflexivity. Qed.
Lemma array_uncons_concrete : concreteb array_uncons = true. Proof. vm_compute; reflexivity. Qed.

Lemma Array_names : forall A k, names_concrete A -> names_concrete (Array A (idx k)).
Proof. intros A k HA; cbn [names_concrete Array]; exact (Array_tag_concrete A k HA). Qed.
Lemma Nat_names : names_concrete Nat. Proof. reflexivity. Qed.

(** ** Type application of the parts *)

Lemma tp_gen_empty_Nat : tp PO @ 'label[gen_empty_nm] @r code Nat ==> Sm (Array Nat Lf).
Proof. apply (type_app_gen_empty PO PO_gemp), Nat_names. Qed.
Lemma tp_gen_prepend_Nat : forall k, tp PO @ 'label[gen_prepend_nm] @r (code Nat '* (Nat '* Array Nat k)) ==> Sm (Array Nat (Sm k)).
Proof. intros k; apply (type_app_gen_prepend PO PO_gpre), Nat_names. Qed.
Lemma tp_gen_prepend_row : forall p k,
  tp PO @ 'label[gen_prepend_nm] @r (Fk (Fk Lf Lf) (array_tag (code Nat) (idx p)) '* (Array Nat (idx p) '* Array (Array Nat (idx p)) k))
    ==> Sm (Array (Array Nat (idx p)) (Sm k)).
Proof.
  intros p k; change (Fk (Fk Lf Lf) (array_tag (code Nat) (idx p))) with (code (Array Nat (idx p))).
  apply (type_app_gen_prepend PO PO_gpre), Array_names, Nat_names.
Qed.

Ltac tpsM := repeat first
  [ eassumption
  | apply tp_gen_empty_Nat | apply tp_gen_prepend_Nat | apply tp_gen_prepend_row | apply type_app_NatA
  | (apply (type_app_gen_prepend PO PO_gpre); assumption)
  | (apply (type_app_gen_empty PO PO_gemp); assumption)
  | apply (type_app_Array_leaf PO PO_array)
  | eapply (type_app_Array_succ PO PO_array)
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].

Lemma type_app_array_uncons : forall A k, tp PO @ array_uncons @r Array A (Sm k) ==> Sm (A '* Array A k).
Proof. intros A k; unfold array_uncons, swap; tpsA. Qed.

Lemma type_app_array_length : forall A k, tp PO @ array_length @r Array A (idx k) ==> Sm (idx k).
Proof. intros A k; induction k as [|k IH]; cbn [idx] in *; unfold array_length in *; tpsA. Qed.

Lemma type_app_array_last_empty : forall A k, tp PO @ array_last_empty @r Array A (idx k) ==> Sm (Array A Lf).
Proof. intros A k; induction k as [|k IH]; cbn [idx] in *; unfold array_last_empty in *; tpsA. Qed.

Lemma type_app_zeros : forall A k, tp PO @ T_z @r Array A (idx k) ==> Sm (Array Nat (idx k)).
Proof.
  intros A k; induction k as [|k IH]; cbn [idx] in *; unfold T_z in *; tpsM.
Qed.

Lemma type_app_axpy : forall k,
  tp PO @ T_axpy @r (Nat '* (Array Nat (idx k) '* Array Nat (idx k))) ==> Sm (Array Nat (idx k)).
Proof.
  intros k; pose proof type_app_add_A as Ha; pose proof type_app_mul_A as Hm.
  induction k as [|k IH]; cbn [idx] in *; unfold T_axpy in *; tpsM.
Qed.

(** [row_times] at a row of length [n] and a matrix of [k] rows, for all [n] and [k]. *)
Lemma type_app_row_times : forall n k p,
  tp PO @ T_rt @r (Array Nat (idx n) '* (Array (Array Nat (idx p)) (idx k) '* Array Nat (idx p))) ==> Sm (Array Nat (idx p)).
Proof.
  induction n as [|n IH]; intros k p; pose proof (type_app_axpy p) as Hx.
  - cbn [idx]; unfold T_rt; tpsM.
  - destruct k as [|k]; cbn [idx] in *; [unfold T_rt; tpsM|].
    specialize (IH k p); unfold T_rt in *; tpsM.
Qed.

Lemma type_app_mrows : forall m n k p,
  tp PO @ T_mrows @r (Array (Array Nat (idx n)) (idx m) '* (Array (Array Nat (idx p)) (idx k) '*
                       (Array Nat (idx p) '* Array (Array Nat (idx p)) Lf)))
    ==> Sm (Array (Array Nat (idx p)) (idx m)).
Proof.
  intros m n k p; pose proof (type_app_row_times n k p) as Hr; pose proof (type_app_array_length Nat p) as Hl.
  induction m as [|m IH]; cbn [idx] in *; unfold T_mrows in *; tpsM.
Qed.

Lemma type_app_heads : forall k p,
  tp PO @ T_heads @r Array (Array Nat (idx (S p))) (idx k) ==> Sm (Array Nat (idx k)).
Proof.
  intros k p; pose proof (type_app_array_uncons Nat (idx p)) as Hu.
  induction k as [|k IH]; cbn [idx] in *; unfold T_heads in *; tpsM.
Qed.

Lemma type_app_matrix_product : forall m n k p,
  tp PO @ T_mp @r (Array (Array Nat (idx n)) (idx m) '* Array (Array Nat (idx p)) (idx (S k)))
    ==> Sm (Array (Array Nat (idx p)) (idx m)).
Proof.
  intros m n k p.
  pose proof (type_app_mrows m n (S k) p) as Hr; pose proof (type_app_zeros Nat p) as Hz.
  pose proof (type_app_array_last_empty (Array Nat (idx p)) (S k)) as He.
  pose proof (type_app_array_uncons (Array Nat (idx p)) (idx k)) as Hu.
  cbn [idx] in *; unfold T_mp; tpsM.
Qed.

Lemma type_app_width_check : forall m n p,
  tp PO @ T_wc @r (Array (Array Nat (idx (S n))) (idx (S m)) '* Array (Array Nat (idx (S p))) (idx (S n)))
    ==> Sm (Array Nat (idx (S n))).
Proof.
  intros m n p; pose proof (type_app_heads (S n) p) as Hh.
  pose proof (type_app_array_uncons (Array Nat (idx (S n))) (idx m)) as Hu.
  cbn [idx] in *; unfold T_wc; tpsM.
Qed.

Lemma idx_inj : forall n k, idx n = idx k -> n = k.
Proof. induction n as [|n IH]; intros [|k] H; cbn in H; try discriminate; [reflexivity|]. f_equal; apply IH; inversion H; reflexivity. Qed.

Lemma type_app_width_check_refuse : forall m n k p, n <> k ->
  tp PO @ T_wc @r (Array (Array Nat (idx (S n))) (idx (S m)) '* Array (Array Nat (idx (S p))) (idx (S k))) ==> Lf.
Proof.
  intros m n k p Hnk; pose proof (type_app_heads (S k) p) as Hh.
  pose proof (type_app_array_uncons (Array Nat (idx (S n))) (idx m)) as Hu.
  cbn [idx] in *; unfold T_wc.
  eapply tp_S2_any; [reflexivity|tpsM|tpsM|].
  eapply type_app_Nat_refuse; [apply tp_K1_fwd|].
  intros E; injection E; intros E2; apply Hnk; apply idx_inj; symmetry; exact E2.
Qed.

Definition Matrix0 (m n : nat) : Combination := Matrix (idx (S m)) (idx (S n)).

Lemma type_app_matrix_mult : forall m n p,
  tp PO @ T_mm @r (Matrix0 m n '* Matrix0 n p) ==> Sm (Matrix0 m p).
Proof.
  intros m n p; unfold Matrix0, Matrix.
  pose proof (type_app_matrix_product (S m) (S n) n (S p)) as H1.
  pose proof (type_app_width_check m n p) as H2.
  unfold T_mm; tpsM.
Qed.

Lemma type_app_matrix_mult_refuse : forall m n k p, n <> k ->
  tp PO @ T_mm @r (Matrix0 m n '* Matrix0 k p) ==> Lf.
Proof.
  intros m n k p Hnk; unfold Matrix0, Matrix.
  pose proof (type_app_matrix_product (S m) (S n) k (S p)) as H1.
  pose proof (type_app_width_check_refuse m n k p Hnk) as H2.
  unfold T_mm; eapply tp_S2_refuse_H; [reflexivity|tpsM|exact H2|apply tp_K1_partial].
Qed.

(** ** The paper's theorems.  Rocq's [Matrix0 m n] is the paper's [Matrix[m+1, n+1]]. *)

Theorem infer_matrix_mult_application : forall m n p xs ys,
  infer PO @ xs ==> Sm (Matrix0 m n) -> infer PO @ ys ==> Sm (Matrix0 n p) ->
  infer_expression PO @ (matrix_mult @ (xs '* ys)) ==> Sm (Matrix0 m p).
Proof.
  intros m n p xs ys Hx Hy.
  eapply ie_fork; [apply ie_stem, infer_matrix_mult|apply ie_stem, pair_typed; eassumption|apply type_app_matrix_mult].
Qed.

Theorem matrix_mult_refused : forall m n k p V, n <> k ->
  ~ (tp PO @ T_mm @r (Matrix0 m n '* Matrix0 k p) ==> Sm V).
Proof.
  intros m n k p V Hnk H.
  pose proof (eval_deterministic _ _ H _ (type_app_matrix_mult_refuse m n k p Hnk)); discriminate.
Qed.

(** So no application of [matrix_mult] to matrices with mismatched inner dimensions has a type. *)
Corollary matrix_mult_application_refused : forall m n k p xs ys T, n <> k ->
  infer PO @ xs ==> Sm (Matrix0 m n) -> infer PO @ ys ==> Sm (Matrix0 k p) ->
  ~ (infer_expression PO @ (matrix_mult @ (xs '* ys)) ==> Sm T).
Proof.
  intros m n k p xs ys T Hnk Hx Hy H.
  destruct (ie_inv _ _ _ H) as [[u [E _]]|[e1 [e2 [T1 [T2 [E [H1 [H2 H3]]]]]]]]; [discriminate|].
  inversion E; subst.
  destruct (ie_inv _ _ _ H1) as [[u [E1 Hu]]|[a [b [_ [_ [E1 _]]]]]]; [|discriminate].
  destruct (ie_inv _ _ _ H2) as [[u2 [E2 Hu2]]|[a [b [_ [_ [E2 _]]]]]]; [|discriminate].
  inversion E1; inversion E2; subst.
  pose proof (eval_deterministic _ _ Hu _ infer_matrix_mult) as E3; inversion E3; subst.
  pose proof (eval_deterministic _ _ Hu2 _ (pair_typed _ _ _ _ _ Hx Hy)) as E4; inversion E4; subst.
  exact (matrix_mult_refused m n k p T Hnk H3).
Qed.

(** ** The example: [[1,2],[3,4]] times [[5,6],[7,8]] *)

Fixpoint arrv (A : Combination) (l : list Combination) : Combination :=
  match l with [] => empty A | x :: l' => prepend A (idx (List.length l')) x (arrv A l') end.
Definition nrow (l : list nat) : Combination := arrv Nat (List.map numeral l).
Definition nmat (p : nat) (rws : list (list nat)) : Combination := arrv (Array Nat (idx p)) (List.map nrow rws).
Definition mm_left := nmat 2 [[1;2];[3;4]].
Definition mm_right := nmat 2 [[5;6];[7;8]].
Definition mm_result := nmat 2 [[19;22];[43;50]].
Definition mm_wide := nmat 3 [[1;2;3];[4;5;6]].

Example mm_left_typed : infer PO @ mm_left ==> Sm (Matrix0 1 1). Proof. by_runAr. Qed.
Example matrix_mult_example : matrix_mult @ (mm_left '* mm_right) ==> mm_result. Proof. by_runAr. Qed.
Example matrix_mult_example_typed : infer_expression PO @ (matrix_mult @ (mm_left '* mm_right)) ==> Sm (Matrix0 1 1).
Proof. by_runAr. Qed.
Example matrix_mult_wide : infer_expression PO @ (matrix_mult @ (mm_wide '* mm_right)) ==> Lf. Proof. by_runAr. Qed.

(** ** Reading an array, arrays to lists, the last empty array (stage 8, ROCQ_DELTA P4) *)
Fixpoint array_value (A : Combination) (l : list Combination) : Combination :=
  match l with [] => empty A | x :: l' => prepend A (idx (List.length l')) x (array_value A l') end.

Definition array_reading_body : Combination := Eval cbn in to_tree
  (star "self" (star "q"
     (snd_t' (snd_t' (Ref "q")) @@ (fst_t' (snd_t' (Ref "q")) ''* (star "p"
        (Ref "self" @@ (fst_t' (Ref "q") ''* ((fst_t' (Ref "q") @@ (fst_t' (snd_t' (Ref "q")) ''* fst_t' (Ref "p"))) ''* snd_t' (Ref "p"))))))))).
Definition array_reading : Combination := Z array_reading_body.
Lemma array_reading_concrete : concreteb array_reading = true. Proof. vm_compute; reflexivity. Qed.

Lemma array_reading_eval : forall f (ff : Combination -> Combination -> Combination) A l s,
  (forall a x, f @ (a '* x) ==> ff a x) ->
  array_reading @ (f '* (s '* array_value A l)) ==> List.fold_left ff l s.
Proof.
  intros f ff A l; induction l as [|x l IH]; intros s Hf; cbn [array_value List.fold_left].
  - apply Z_unfold; unfold array_reading_body, empty; ev2.
  - pose proof (Hf s x) as H1; pose proof (IH (ff s x) Hf) as H2.
    unfold array_reading at 1; apply Z_unfold; unfold array_reading_body at 1; unfold prepend; ev2.
Qed.

Ltac tpsR := repeat first
  [ eassumption
  | (apply (type_app_gen_prepend PO PO_gpre); assumption)
  | (apply (type_app_gen_empty PO PO_gemp); assumption)
  | (apply type_app_gen_cons; assumption)
  | (apply type_app_gen_nil; assumption)
  | apply (type_app_Array_leaf PO PO_array)
  | eapply (type_app_Array_succ PO PO_array)
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].

Lemma type_app_array_reading : forall A F S k, tp PO @ F @r (S '* A) ==> Sm S ->
  tp PO @ array_reading @r (F '* (S '* Array A (idx k))) ==> Sm S.
Proof.
  intros A F S k HF; induction k as [|k IH]; cbn [idx] in *; unfold array_reading in *; tpsR.
Qed.

Definition array_to_list_body : Combination := Eval cbn -[gen_nil gen_cons] in to_tree
  (star "self" (star "q"
     (snd_t' (Ref "q") @@ ((op gen_nil @@ fst_t' (Ref "q")) ''* (star "p"
        (op gen_cons @@ (fst_t' (Ref "q") ''* (fst_t' (Ref "p") ''* (Ref "self" @@ (fst_t' (Ref "q") ''* snd_t' (Ref "p"))))))))))).
Definition array_to_list : Combination := Z array_to_list_body.
Definition T_al : Combination := Eval vm_compute in tyA array_to_list.
Lemma infer_array_to_list : infer PO @ array_to_list ==> Sm T_al. Proof. by_runAr. Qed.

Lemma type_app_array_to_list : forall A k, names_concrete A ->
  tp PO @ T_al @r (code A '* Array A (idx k)) ==> Sm (List A).
Proof. intros A k HA; induction k as [|k IH]; cbn [idx] in *; unfold T_al in *; tpsR. Qed.

Fixpoint list_value (A : Combination) (l : list Combination) : Combination :=
  match l with [] => nil A | x :: l' => cons A x (list_value A l') end.

Lemma gen_cons_apply : forall A x xs, gen_cons @ (code A '* (x '* xs)) ==> cons A x xs.
Proof. intros; unfold gen_cons, cons, list_tag; apply tagged_eval, gcons_eval. Qed.
Lemma gen_nil_apply : forall A, gen_nil @ code A ==> nil A.
Proof. intros; unfold gen_nil, nil, list_tag; apply tagged_eval, gnil_eval. Qed.

Lemma array_to_list_eval : forall A l, array_to_list @ (code A '* array_value A l) ==> list_value A l.
Proof.
  intros A l; induction l as [|x l IH]; cbn [array_value list_value].
  - pose proof (gen_nil_apply A) as H0.
    unfold array_to_list at 1; apply Z_unfold; unfold array_to_list_body at 1; unfold empty; ev2.
  - pose proof (gen_nil_apply A) as H0; pose proof (gen_cons_apply A x (list_value A l)) as H1.
    unfold array_to_list at 1; apply Z_unfold; unfold array_to_list_body at 1; unfold prepend; ev2.
Qed.

Lemma array_last_empty_eval : forall A l, array_last_empty @ array_value A l ==> empty A.
Proof.
  intros A l; induction l as [|x l IH]; cbn [array_value].
  - unfold array_last_empty at 1; apply Z_unfold; unfold array_last_empty_body at 1; unfold empty; ev2.
  - unfold array_last_empty at 1; apply Z_unfold; unfold array_last_empty_body at 1; unfold prepend; ev2.
Qed.

Theorem infer_array_to_list_application : forall A k xs,
  infer PO @ xs ==> Sm (Array A (idx k)) ->
  infer_expression PO @ (array_to_list @ (code A '* xs)) ==> Sm (List A).
Proof.
  intros A k xs Hx; pose proof (array_type_names _ _ _ _ Hx) as HA.
  assert (Hq : infer PO @ (code A '* xs) ==> Sm (code A '* Array A (idx k)))
    by (apply pair_typed; [apply code_self_typed, HA|exact Hx]).
  eapply ie_fork; [apply ie_stem, infer_array_to_list|apply ie_stem, Hq|apply type_app_array_to_list, HA].
Qed.
