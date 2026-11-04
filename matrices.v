(** * Matrices (paper: Arrays, "Matrices").

    Matrices as arrays of rows: mapping, transpose, dot product and matrix
    multiplication, with their typing. *)


(** Matrices are arrays of rows, with tree indices for both dimensions.
    Matrix A m n is Array (Array A n) m. Row append adds the row indices
    and requires identical row types. Canonical unary indices distinguish
    different column counts, so the array constructor rejects a width
    mismatch. Row witnesses retain the column type even with zero rows.
    The development proceeds through mapping, transposition (including
    transpose twice), and multiplication. The dimensions of mapping and
    transposition are runtime tree values; multiplication takes none.
    Concrete examples share [array_ontology] with arrays; they do not depend
    on Salary, Company, Query or Update introduction. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types arrays array_traversals.

Open Scope string_scope.
Set Default Proof Using "Type".

Definition Matrix A m n := Array (Array A n) m.
Lemma infer_empty_matrix : forall AI row A n,
  supports_arrays AI -> infer AI @ row ==> Sm (Array A n) ->
  infer AI @ arrays.empty row ==> Sm (Matrix A Lf n).
Proof. intros; apply infer_empty; assumption. Qed.
Lemma infer_prepend_row : forall AI row rows A m n,
  supports_arrays AI -> infer AI @ row ==> Sm (Array A n) ->
  infer AI @ rows ==> Sm (Matrix A m n) ->
  infer AI @ arrays.prepend row rows ==> Sm (Matrix A (Sm m) n).
Proof. intros; apply infer_prepend; assumption. Qed.
Lemma type_app_append_rows : forall AI A m p n,
  supports_arrays AI ->
  type_app AI @ array_append @r (Matrix A m n '* Matrix A p n) ==>
    Sm (Matrix A (index_sum m p) n).
Proof. intros; apply type_app_array_append; assumption. Qed.

Lemma infer_append_rows : forall AI xs ys A m p n,
  supports_arrays AI -> infer AI @ xs ==> Sm (Matrix A m n) ->
  infer AI @ ys ==> Sm (Matrix A p n) ->
  infer_expression AI @ (array_append @ (xs '* ys)) ==>
    Sm (Matrix A (index_sum m p) n).
Proof. intros; apply infer_array_append_application; assumption. Qed.
Lemma append_rows_wrong_width : forall A n q m p,
  unary_index n -> unary_index q -> n <> q ->
  array_abstractor @ (Matrix A p q 'C Matrix A m n) ==> Lf.
Proof.
  intros; apply array_abstractor_wrong_domain.
  intro HE; apply H1; eapply Array_index_injective; eassumption.
Qed.

Definition matrix_value ar a (rows : List.list (List.list Combination)) :=
  array_value ar (List.map (array_value a) rows).
Lemma infer_matrix_value : forall AI ar a A n rows,
  supports_arrays AI -> infer AI @ a ==> Sm A ->
  infer AI @ ar ==> Sm (Array A n) ->
  Forall (fun row => sequence_index row = n /\
    Forall (fun x => infer AI @ x ==> Sm A) row) rows ->
  infer AI @ matrix_value ar a rows ==>
    Sm (Matrix A (sequence_index (List.map (array_value a) rows)) n).
Proof.
  intros AI ar a A n rows HA Ha Har Hrows; unfold matrix_value, Matrix.
  apply array_value_typed; [exact HA|exact Har|].
  induction Hrows; cbn; constructor; auto.
  destruct H as [HE Htyped]; rewrite <- HE; apply array_value_typed; assumption.
Qed.


(** * Matrix mapping

    Matrix mapping generates the row action from the column index,
    then maps that action over the outer array using the row index.
    The program receives both indices at runtime. Explicit row witnesses
    ar : Array A n and br : Array B n retain the column type when there
    are no rows. Its inferred application preserves both dimensions;
    its operational theorem preserves order while applying f to each entry.
    This uses the array/list interfaces, with no new matrix typing rule. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types arrays array_traversals.

Open Scope string_scope.
Set Default Proof Using "Type".

Definition map_matrix ar br a b f := Eval cbn in to_tree
  (star "m" (star "n"
    (Val (map_array_with ar br) @@ (Val (map_array a b f) @@ Ref "n") @@ Ref "m"))).
Lemma map_matrix_eval : forall ar br a b f m n,
  map_matrix ar br a b f @ m @r n ==>
    array_mapper ar br (array_mapper a b f n) m.
Proof.
  intros; pose proof (map_array_eval a b f n).
  pose proof (map_array_with_eval ar br (array_mapper a b f n) m) as HM; inv_out HM.
  unfold map_matrix; evaluate.
Qed.

Section MatrixTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Definition infer_map_matrix ar br a b f A B F n
  (Har : infer AI @ ar ==> Sm (Array A n))
  (Hbr : infer AI @ br ==> Sm (Array B n))
  (Ha : infer AI @ a ==> Sm A) (Hb : infer AI @ b ==> Sm B)
  (Hf : infer AI @ f ==> Sm F) (HFA : type_app AI @ F @r A ==> Sm B) :
  { M : Combination | infer AI @ map_matrix ar br a b f ==> Sm M /\
    forall m, unary_index m -> unary_index n ->
    exists T, type_app AI @ M @r m ==> Sm T /\
      type_app AI @ T @r n ==> Sm (Matrix A m n --> Matrix B m n) }.
Proof using AI HL HA.
  pose proof (proj2_sig (infer_map_array AI HL HA a b f A B F Ha Hb Hf HFA))
    as [HR HRT].
  pose proof (proj2_sig (infer_map_array_with AI HL HA ar br
    (Array A n) (Array B n) Har Hbr)) as [HO HOT].
  eexists; split.
  - unfold map_matrix; infer_tac.
  - intros m Hm Hn.
    pose proof (HRT n Hn).
    assert (Hrow : type_app AI @ (Array A n --> Array B n) @r
      Array A n ==> Sm (Array B n)).
    { apply type_app_abstract; apply funty_eliminator_eval. }
    destruct (HOT _ Hrow) as [T [HT HTm]]; pose proof (HTm m Hm).
    eexists; split; type_app_tac.
Defined.
Lemma infer_matrix_map_specialisation : forall ar br a b f A B F m n,
  infer AI @ ar ==> Sm (Array A n) -> infer AI @ br ==> Sm (Array B n) ->
  infer AI @ a ==> Sm A -> infer AI @ b ==> Sm B ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r A ==> Sm B ->
  unary_index m -> unary_index n ->
  infer_expression AI @ (map_matrix ar br a b f @ m @r n) ==>
    Sm (Matrix A m n --> Matrix B m n).
Proof using AI HL HA.
  intros ar br a b f A B F m n Har Hbr Ha Hb Hf HFA Hm Hn.
  destruct (infer_map_matrix ar br a b f A B F n Har Hbr Ha Hb Hf HFA)
    as [M [HM HMT]].
  destruct (HMT m Hm Hn) as [T [HT HTn]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork.
    + apply infer_expression_stem; exact HM.
    + apply infer_expression_stem; apply infer_index; exact Hm.
    + exact HT.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - exact HTn.
Qed.
Lemma infer_matrix_map_application : forall ar br a b f A B F m n xs,
  infer AI @ ar ==> Sm (Array A n) -> infer AI @ br ==> Sm (Array B n) ->
  infer AI @ a ==> Sm A -> infer AI @ b ==> Sm B ->
  infer AI @ f ==> Sm F -> type_app AI @ F @r A ==> Sm B ->
  unary_index m -> unary_index n -> infer AI @ xs ==> Sm (Matrix A m n) ->
  infer_expression AI @ (map_matrix ar br a b f @ m @r n @r xs) ==>
    Sm (Matrix B m n).
Proof using AI HL HA.
  intros ar br a b f A B F m n xs Har Hbr Ha Hb Hf HFA Hm Hn HX.
  eapply infer_expression_fork.
  - eapply infer_matrix_map_specialisation; eassumption.
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End MatrixTyping.

Lemma map_matrix_exact : forall ar br a b f n rows result_rows,
  Forall (fun row => sequence_index row = n) rows ->
  Forall2 (Forall2 (fun x y => f @ x ==> y)) rows result_rows ->
  map_matrix ar br a b f @ sequence_index (List.map (array_value a) rows) @r n @r
    matrix_value ar a rows ==> matrix_value br b result_rows.
Proof.
  intros ar br a b f n rows result_rows Hwidth Hmap.
  eapply eval_appl; [apply map_matrix_eval|].
  unfold matrix_value; apply array_mapper_exact.
  induction Hmap; cbn; constructor.
  - inversion Hwidth; subst; apply array_mapper_exact; assumption.
  - apply IHHmap; inversion Hwidth; assumption.
Qed.


(** * Transposition

    Transpose with runtime tree dimensions and computed witnesses.

    transpose a @ m @r n is intended to have type
      Matrix A m n --> Matrix A n m, for a : A.

    Read the matrix as lists of rows. At each column step, map head over
    those rows, build that column as an array of length m, then continue
    with their tails. A fold over n assembles the n columns. Its element
    type (Array A m) stays fixed throughout this fold.

    Both the row witness and column witness are generated from the supplied
    indices. At n=Lf the result retains its length-m column witness even
    though there are no columns. At m=Lf, every generated column is empty.
    Rectangular inputs use no padding, so no ghost of a row is read.
    This construction adds no core typing rules or abstract constructors. *)
From Stdlib Require Import String List.
From TreeTyping Require Import tree typing soundness booleans.
From TreeTyping Require Import functions data_types arrays array_traversals.

Open Scope string_scope.
Unset Default Proof Using.
Section FunctionEnabledExamples.
Definition row_heads a := map_value (head_or a) a.
Definition row_tails a := map_value list_tail (nil_value a).
Definition columns_step2 a build :=
  star "r" (lam2
    (star "rows" (''tagged[
      (Ref "r" @@ (Val (row_tails a) @@ Ref "rows")) ''C
      ''S2[Val 'I,''K1 (build @@ (Val (row_heads a) @@ Ref "rows"))],Val array_nm]))
    (Val (nil_value (nil_value a)))).
Definition columns_step a build := Eval cbn in to_tree (columns_step2 a (Val build)).
Definition columns a build b :=
  unary_fold (lam ('K1 (arrays.empty b)) (nil_value (nil_value a))) (columns_step a build).
Definition columns_program a := Eval cbn in to_tree
  (star "build" (star "b" (unary_fold2
    (lam2 (''K1 (empty2 (Ref "b"))) (Val (nil_value (nil_value a))))
    (columns_step2 a (Ref "build"))))).
Lemma columns_specialises : forall a build b,
  columns_program a @ build @r b ==> columns a build b.
Proof.
  intros; unfold columns_program, columns, columns_step, columns_step2,
    unary_fold2, unary_fold, unary_fold_body, empty2, lam2, lam,
    arrays.empty, Z2, Z; cbn; evaluate.
Qed.
Fixpoint columns_consumer a build b n :=
  match n with
  | Lf => lam ('K1 (arrays.empty b)) (nil_value (nil_value a))
  | Sm k | Fk _ k => lam
      (to_tree (star "rows" (''tagged[
        (Val (columns_consumer a build b k) @@ (Val (row_tails a) @@ Ref "rows")) ''C
        ''S2[Val 'I,''K1 (Val build @@ (Val (row_heads a) @@ Ref "rows"))],Val array_nm])))
      (nil_value (nil_value a))
  end.
Lemma columns_eval : forall a build b n,
  columns a build b @ n ==> columns_consumer a build b n.
Proof.
  intros a build b n; induction n; cbn [columns_consumer]; unfold columns in *.
  - apply unary_fold_leaf.
  - eapply unary_fold_stem; [exact IHn|].
    unfold columns_step, columns_step2, lam2, lam; cbn; evaluate.
  - eapply unary_fold_fork; [exact IHn2|].
    unfold columns_step, columns_step2, lam2, lam; cbn; evaluate.
Qed.

Local Opaque columns_program map_with take_array_program read_array_program.
Definition transpose a := Eval cbn in to_tree
  (star "m" (star "n"
    ((star "row"
      ((star "build"
        ((star "column" (lam2
          ((''wait2[Val (columns_program a),Ref "build",Ref "column"] @@ Ref "n") ''C
            ((op map_with @@
              (Val (read_array a) @@ Ref "n") @@ Val (nil_value a)) ''C
             (op read_array_program @@ Ref "row" @@ Ref "m")))
          (op take_array_program @@ Ref "row" @@ Ref "m" @@ nil2 (Ref "row")))) @@
          (Ref "build" @@ Val (nil_value a)))) @@
        (Val (take_array a) @@ Ref "m"))) @@
      (Val (take_array a) @@ Ref "n" @@ Val (nil_value a))))).
Definition transpose_value a m n :=
  let row := array_value a (array_elements a n List.nil) in
  let column := array_value a (array_elements a m List.nil) in
  lam (columns_consumer a (array_builder a m) column n 'C
    (map_value (array_reader a n) (nil_value a) 'C array_reader row m))
    (array_value row (array_elements row m List.nil)).
Lemma transpose_eval : forall a m n,
  transpose a @ m @r n ==> transpose_value a m n.
Proof.
  intros a m n.
  set (row := array_value a (array_elements a n List.nil)).
  set (column := array_value a (array_elements a m List.nil)).
  pose proof (take_array_eval a m); pose proof (take_array_eval a n).
  pose proof (array_builder_list n a a List.nil) as Hrow.
  pose proof (array_builder_list m a a List.nil) as Hcolumn.
  pose proof (take_array_program_list row m row List.nil) as Hmatrix.
  pose proof (read_array_eval a n); pose proof (read_array_program_eval row m) as Hread.
  destruct (eval_app_r_inv _ _ _ (map_with_specialises (array_reader a n) (nil_value a))) as [mw [Hmap Hmap2]].
  pose proof (columns_specialises a (array_builder a m) column) as Hcols.
  pose proof (columns_eval a (array_builder a m) column n).
  pose proof (take_array_specialises row).
  pose proof (take_array_eval row m).
  pose proof (array_builder_list m row row List.nil) as Houter.
  pose proof (read_array_specialises row).
  pose proof (read_array_eval row m).
  inv_out Hcols.
  cbn [list_value] in Hrow, Hcolumn, Houter.
  unfold transpose, transpose_value, lam2, nil2, nil_value, lam;
    fold row column; cbn; evaluate.

Qed.

Section TransposeTyping.
Variable AI : Decl.
Hypothesis HL : supports_list AI.
Hypothesis HA : supports_arrays AI.
Local Ltac transpose_app := first
  [apply funty_eliminator_eval | eassumption
  | lazymatch goal with
    | |- type_app _ @ ?T @r _ ==> _ =>
      first [is_evar T; fail 1|idtac];
      first [eapply type_app_I
        | new_S; [solve [intros; discriminate]| | |]
        | eapply type_app_K_ev | eapply type_app_leaf_ev
        | eapply type_app_abstract | eapply type_app_stem_ev]
    | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
      first [apply type_app_stem_function
        | apply type_app_stem_tagged; eapply declaration_apply; [exact HA|apply array_abstractor_step]
        | apply type_app_stem_tagged; eapply declaration_apply; [exact HA|apply array_abstractor_zero]
        | apply type_app_stem_structural; intros; discriminate
        | apply type_app_stem_tagged; apply list_abstractor_supported; [exact HL|apply list_abstractor_nil]
        | apply type_app_stem_structural; solve [intros; discriminate]]
    end].
Definition RowHeads A := foldright_value (map_step_value (head_or A)) ('List[A]).
Definition RowTails A := foldright_value (map_step_value list_tail) ('List['List[A]]).
Lemma infer_row_heads : forall a A, infer AI @ a ==> Sm A ->
  infer AI @ row_heads a ==> Sm (RowHeads A).
Proof using AI HL.
  intros; apply infer_map_value; [exact HL|apply infer_head_or; assumption|assumption].
Qed.
Lemma infer_row_tails : forall a A, infer AI @ a ==> Sm A ->
  infer AI @ row_tails a ==> Sm (RowTails A).
Proof using AI HL.
  intros; apply infer_map_value;
    [exact HL|apply infer_list_tail|apply infer_nil_value; assumption].
Qed.
Lemma type_app_row_heads : forall A,
  type_app AI @ RowHeads A @r 'List['List[A]] ==> Sm ('List[A]).
Proof using AI HL. intros; apply type_app_map_value; [exact HL|apply type_app_head_or_list]. Qed.
Lemma type_app_row_tails : forall A,
  type_app AI @ RowTails A @r 'List['List[A]] ==> Sm ('List['List[A]]).
Proof using AI HL. intros; apply type_app_map_value; [exact HL|apply type_app_list_tail; exact HL]. Qed.
Local Transparent columns_program.
Definition infer_columns_program a A (Ha : infer AI @ a ==> Sm A) :
  { T : Combination | infer AI @ columns_program a ==> Sm T /\
    forall B, exists F S,
      type_app AI @ T @r ('List[A] --> B) ==> Sm F /\
      type_app AI @ F @r B ==> Sm (Z (unary_fold_body ('List['List[A]] --> Array B Lf) S)) /\
      forall n, unary_index n ->
      type_app AI @ Z (unary_fold_body ('List['List[A]] --> Array B Lf) S) @r n ==>
        Sm ('List['List[A]] --> Array B n) }.
Proof using AI HL HA.
  pose proof (infer_row_heads a A Ha). pose proof (infer_row_tails a A Ha).
  pose proof (type_app_row_heads A). pose proof (type_app_row_tails A).
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  pose proof (infer_nil_value AI (nil_value a) ('List[A]) HL Hnil).
  eexists; split.
  - unfold columns_program, columns_step2, unary_fold2, empty2, lam2, Z2, Z; cbn.
    repeat first [progress infer_tac|transpose_app].
  - intro B; do 2 eexists; split.
    + repeat transpose_app.
    + split; [repeat transpose_app|].
      intros n Hn; eapply arrow_fold_application with
        (P := fun n => 'List['List[A]] --> Array B n);
        [reflexivity| |exact Hn].
      intro k; repeat transpose_app.
Defined.

Local Opaque columns_program.
Definition infer_transpose a A (Ha : infer AI @ a ==> Sm A) :
  { T : Combination | infer AI @ transpose a ==> Sm T /\
    forall m, unary_index m -> exists F,
      type_app AI @ T @r m ==> Sm F /\
      forall n, unary_index n -> type_app AI @ F @r n ==>
        Sm (Matrix A m n --> Matrix A n m) }.
Proof using AI HL HA.
  pose proof (infer_take_array AI HL HA a A Ha) as HT.
  pose proof (proj2_sig (infer_read_array AI HL HA a A Ha)) as [HR HRA].
  pose proof (proj2_sig (infer_take_array_program AI HL HA )) as [HTP HTPA].
  pose proof (proj2_sig (infer_read_array_program AI HL HA )) as [HRP HRPA].
  pose proof (proj2_sig (infer_columns_program a A Ha)) as [HC HCA].
  pose proof (infer_map_with AI) as HM.
  pose proof (infer_nil_value AI a A HL Ha) as Hnil.
  eexists; split.
  - unfold transpose, lam2, nil2; cbn.
    repeat first [progress infer_tac|transpose_app].
  - intros m Hm.
    pose proof (take_array_type_application AI a A HL HA Ha m Hm).
    eexists; split; [repeat transpose_app|].
    intros n Hn.
    pose proof (take_array_type_application AI a A HL HA Ha n Hn).
    pose proof (HRA n Hn).
    destruct (HTPA (Array A n)) as [S [HS HSn]]; pose proof (HSn m Hm).
    destruct (HRPA (Array A n)) as [R [HRR HRm]]; pose proof (HRm m Hm).
    destruct (HCA (Array A m)) as [F [C [HCF [HFC HCn]]]]; pose proof (HCn n Hn).
    assert (Harrow : type_app AI @ (Array A n --> 'List[A]) @r Array A n ==> Sm ('List[A])).
    { apply type_app_abstract; apply funty_eliminator_eval. }
    destruct (type_app_map_with AI HL (Array A n --> 'List[A]) ('List[A])) as [R0 [HMA HMA2]].
    pose proof (type_app_map_value AI HL _ _ _ Harrow) as HMB.
    unfold Matrix; repeat transpose_app.
Defined.
Lemma infer_transpose_specialisation : forall a A m n,
  infer AI @ a ==> Sm A -> unary_index m -> unary_index n ->
  infer_expression AI @ (transpose a @ m @r n) ==> Sm (Matrix A m n --> Matrix A n m).
Proof using AI HL HA.
  intros a A m n Ha Hm Hn; destruct (infer_transpose a A Ha) as [T [HT HMT]].
  destruct (HMT m Hm) as [F [HFm HFn]].
  eapply infer_expression_fork.
  - eapply infer_expression_fork.
    + apply infer_expression_stem; exact HT.
    + apply infer_expression_stem; apply infer_index; exact Hm.
    + exact HFm.
  - apply infer_expression_stem; apply infer_index; exact Hn.
  - apply HFn; exact Hn.
Qed.
Lemma infer_transpose_application : forall a A m n xs,
  infer AI @ a ==> Sm A -> unary_index m -> unary_index n ->
  infer AI @ xs ==> Sm (Matrix A m n) ->
  infer_expression AI @ (transpose a @ m @r n @r xs) ==> Sm (Matrix A n m).
Proof using AI HL HA.
  intros a A m n xs Ha Hm Hn HX; eapply infer_expression_fork.
  - eapply infer_transpose_specialisation; eassumption.
  - apply infer_expression_stem; exact HX.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.
End TransposeTyping.

(** The following list specification describes observable entries, not the
    runtime representation or a separate implementation of type inference.
    The number of column steps is still the supplied tree index. *)
Fixpoint transpose_rows a n (rows : List.list (List.list Combination)) :=
  match n with
  | Lf => List.nil
  | Sm k | Fk _ k => List.map (List.hd a) rows ::
      transpose_rows a k (List.map (@List.tl Combination) rows)
  end.
Lemma sequence_index_map_same : forall X (f g : X -> Combination) xs,
  sequence_index (List.map f xs) = sequence_index (List.map g xs).
Proof. intros X f g xs; induction xs; cbn; congruence. Qed.
(** Rectangularity ensures that no row is empty at a column step, so the
    ghost of an empty row is never read.  Each step removes one element per
    row; the rows carry whatever ghost the last tail left them. *)
Lemma rectangular_step : forall n rows,
  Forall (fun row => sequence_index row = Sm n) rows ->
  Forall (fun row => row <> List.nil) rows /\
  Forall (fun row => sequence_index row = n) (List.map (@List.tl Combination) rows).
Proof.
  intros n rows H; induction H; cbn; [split; constructor|].
  destruct IHForall as [HN HT]; destruct x as [|x xs]; [discriminate|].
  cbn in H; injection H as H; split; constructor; auto; discriminate.
Qed.

Definition rows_repr rows vs :=
  Forall2 (fun row v => exists g, v = list_value g row) rows vs.
Lemma rows_repr_list : forall a rows, rows_repr rows (List.map (list_value a) rows).
Proof. intros a; induction rows; constructor; eauto. Qed.

Lemma row_heads_eval : forall a rows vs d, rows_repr rows vs ->
  Forall (fun row => row <> List.nil) rows ->
  row_heads a @ list_value d vs ==> list_value a (List.map (List.hd a) rows).
Proof.
  intros a rows vs d Hr Hn; unfold row_heads; apply map_value_list.
  induction Hr as [|row v rows vs [g ->] _ IH]; cbn; constructor.
  - inversion Hn; subst; destruct row; [contradiction|]; cbn; apply head_or_list.
  - apply IH; inversion Hn; assumption.
Qed.
Lemma tails_repr : forall rows vs, rows_repr rows vs ->
  Forall (fun row => row <> List.nil) rows ->
  exists ws, rows_repr (List.map (@List.tl Combination) rows) ws /\
    Forall2 (fun v w => list_tail @ v ==> w) vs ws.
Proof.
  intros rows vs Hr Hn; induction Hr as [|row v rows vs [g ->] _ IH].
  - exists List.nil; split; constructor.
  - inversion Hn as [|? ? Hx Hrest]; subst; destruct (IH Hrest) as [ws [H1 H2]].
    destruct row as [|x l]; [contradiction|].
    exists (list_value x l :: ws); split; constructor; [eauto|exact H1|apply list_tail_cons|exact H2].
Qed.
Lemma columns_consumer_zero : forall a build b rows,
  columns_consumer a build b Lf @ rows ==> arrays.empty b.
Proof. intros; cbn [columns_consumer]; unfold lam; evaluate. Qed.
Lemma columns_consumer_step : forall a build b k rows heads tails column rest,
  row_heads a @ rows ==> heads -> row_tails a @ rows ==> tails ->
  build @ heads ==> column -> columns_consumer a build b k @ tails ==> rest ->
  columns_consumer a build b (Sm k) @ rows ==> arrays.prepend column rest.
Proof. intros; cbn [columns_consumer]; unfold arrays.prepend, lam; cbn; evaluate. Qed.
Lemma columns_consumer_exact : forall a b n,
  unary_index n -> forall rows vs d m, rows_repr rows vs ->
  Forall (fun row => sequence_index row = n) rows ->
  m = sequence_index (List.map (List.hd a) rows) ->
  columns_consumer a (array_builder a m) b n @ list_value d vs ==>
    array_value b (List.map (array_value a) (transpose_rows a n rows)).
Proof.
  intros a b n Hn; induction Hn as [|n ? IHHn] using unary_index_ind;
    intros rows vs d m Hr Hrect Hm.
  - apply columns_consumer_zero.
  - destruct (rectangular_step n rows Hrect) as [Hne Hrect'].
    pose proof (row_heads_eval a rows vs d Hr Hne) as He.
    destruct (tails_repr rows vs Hr Hne) as [ws [Hws Hmap]].
    cbn [transpose_rows List.map array_value].
    eapply columns_consumer_step.
    + exact He.
    + unfold row_tails; exact (map_value_list list_tail (nil_value a) d vs ws Hmap).
    + rewrite Hm; apply array_builder_exact.
    + apply IHHn; try assumption.
      rewrite List.map_map; rewrite Hm; apply sequence_index_map_same.
Qed.
Lemma array_reader_rows : forall a d n rows,
  Forall (fun row => sequence_index row = n) rows ->
  map_value (array_reader a n) (nil_value a) @ list_value d (List.map (array_value a) rows) ==>
    list_value (nil_value a) (List.map (list_value a) rows).
Proof.
  intros a d n rows Hrows; apply map_value_list.
  induction Hrows; cbn; constructor; auto.
  rewrite <- H; apply array_reader_eval; apply array_value_supplies; apply reader_consumer_sequence.
Qed.
Lemma sequence_index_elements : forall a n, unary_index n ->
  sequence_index (array_elements a n List.nil) = n.
Proof.
  intros a n Hn; induction Hn as [|n ? IH] using unary_index_ind; cbn; congruence.
Qed.
Lemma transpose_exact : forall a d m n rows,
  unary_index n -> m = sequence_index (List.map (array_value a) rows) ->
  Forall (fun row => sequence_index row = n) rows ->
  transpose a @ m @r n @r matrix_value d a rows ==>
    matrix_value (array_value a (array_elements a m List.nil)) a (transpose_rows a n rows).
Proof.
  intros a d m n rows Hn Hm Hrows.
  eapply eval_appl; [apply transpose_eval|].
  set (row := array_value a (array_elements a n List.nil)).
  set (column := array_value a (array_elements a m List.nil)).
  assert (HR : array_reader row m @ matrix_value d a rows ==>
    list_value row (List.map (array_value a) rows)).
  { rewrite Hm; apply array_reader_eval; apply array_value_supplies; apply reader_consumer_sequence. }
  pose proof (array_reader_rows a row n rows Hrows) as HM.
  assert (HC : columns_consumer a (array_builder a m) column n @
    list_value (nil_value a) (List.map (list_value a) rows) ==>
    matrix_value column a (transpose_rows a n rows)).
  { unfold matrix_value; apply columns_consumer_exact;
      [exact Hn|apply rows_repr_list|exact Hrows|].
    rewrite Hm; apply sequence_index_map_same. }
  unfold transpose_value, lam; fold row column; evaluate.
Qed.

Lemma transpose_rows_dimensions : forall a n,
  unary_index n -> forall rows,
  sequence_index (List.map (array_value a) (transpose_rows a n rows)) = n /\
  Forall (fun col => sequence_index col = sequence_index (List.map (List.hd a) rows))
    (transpose_rows a n rows).
Proof.
  intros a n Hn; induction Hn as [|? ? IHHn] using unary_index_ind; intro rows; cbn [transpose_rows List.map sequence_index].
  - split; [reflexivity|constructor].
  - destruct (IHHn (List.map (@List.tl Combination) rows)) as [HI HC].
    split; [rewrite HI; reflexivity|constructor; [reflexivity|]].
    rewrite List.map_map in HC.
    rewrite (sequence_index_map_same _ (fun x => List.hd a (List.tl x)) (List.hd a) rows) in HC.
    exact HC.
Qed.

(** The involution law concerns entries. The runtime retains the supplied
    dimensions even when one dimension is zero. In particular transposing
    [] with n columns produces n empty rows, so the reverse transpose still
    knows the original number of rows. *)
Lemma transpose_rows_tails : forall a n row rows,
  List.map (@List.tl Combination) (transpose_rows a n (row :: rows)) =
    transpose_rows a n rows.
Proof.
  intros a n; induction n; intros row rows; cbn [transpose_rows List.map List.tl];
    [reflexivity|rewrite IHn|rewrite IHn2]; reflexivity.
Qed.
Lemma transpose_rows_heads : forall a row rows,
  List.map (List.hd a) (transpose_rows a (sequence_index row) (row :: rows)) = row.
Proof.
  intros a row; induction row as [|x xs IH]; intro rows;
    cbn [sequence_index transpose_rows List.map List.hd List.tl];
    [reflexivity|rewrite IH; reflexivity].
Qed.
Lemma transpose_rows_involutive : forall a n rows,
  Forall (fun row => sequence_index row = n) rows ->
  transpose_rows a (sequence_index (List.map (array_value a) rows))
    (transpose_rows a n rows) = rows.
Proof.
  intros a n rows H; induction H; [reflexivity|].
  change (List.map (List.hd a) (transpose_rows a n (x :: l)) ::
    transpose_rows a (sequence_index (List.map (array_value a) l))
      (List.map (@List.tl Combination) (transpose_rows a n (x :: l))) = x :: l).
  rewrite transpose_rows_tails, IHForall.
  f_equal; rewrite <- H; apply transpose_rows_heads.
Qed.

(** Two evaluations restore the entries. Their outer witness is rebuilt
    canonically, rather than copied from the input. Consequently this is
    not a claim of syntactic identity for arbitrary array representations. *)
Lemma transpose_twice : forall a d m n rows,
  unary_index n -> m = sequence_index (List.map (array_value a) rows) ->
  Forall (fun row => sequence_index row = n) rows ->
  exists middle,
    transpose a @ m @r n @r matrix_value d a rows ==> middle /\
    transpose a @ n @r m @r middle ==>
      matrix_value (array_value a (array_elements a n List.nil)) a rows.
Proof.
  intros a d m n rows Hn Hm Hrows.
  exists (matrix_value (array_value a (array_elements a m List.nil)) a (transpose_rows a n rows)).
  split; [apply transpose_exact; assumption|].
  pose proof (transpose_rows_dimensions a n Hn rows) as [HD HC].
  pose proof (transpose_exact a (array_value a (array_elements a m List.nil))
    n m (transpose_rows a n rows)) as HE.
  rewrite Hm in *.
  rewrite (sequence_index_map_same _ (List.hd a) (array_value a) rows) in HC.
  specialize (HE (sequence_index_unary _) (eq_sym HD) HC).
  rewrite transpose_rows_involutive in HE; [exact HE|exact Hrows].
Qed.
Lemma transpose_composed : forall a d m n rows,
  unary_index n -> m = sequence_index (List.map (array_value a) rows) ->
  Forall (fun row => sequence_index row = n) rows ->
  Fk (transpose a @ n @r m) (transpose a @ m @r n @r matrix_value d a rows) ==>
    matrix_value (array_value a (array_elements a n List.nil)) a rows.
Proof.
  intros a d m n rows Hn Hm HR.
  destruct (transpose_twice a d m n rows Hn Hm HR) as [middle [H1 H2]].
  destruct (eval_pair_inv _ _ _ H2) as [f [v [HF [HV HA]]]].
  inversion HV; subst; eapply eval_pair; eassumption.
Qed.
Lemma transpose_canonical_identity : forall a m n rows,
  unary_index n -> m = sequence_index (List.map (array_value a) rows) ->
  Forall (fun row => sequence_index row = n) rows ->
  let original := matrix_value (array_value a (array_elements a n List.nil)) a rows in
  Fk (transpose a @ n @r m) (transpose a @ m @r n @r original) ==> original.
Proof. intros; apply transpose_composed; assumption. Qed.

(** Small behavioural and live-declarations checks. Numerals are entries;
    every dimension below is a self-typing tree value. *)
Example transpose_two_by_three : forall a d x11 x12 x13 x21 x22 x23,
  transpose a @ Sm (Sm Lf) @r Sm (Sm (Sm Lf)) @r
    matrix_value d a ((x11 :: x12 :: x13 :: List.nil) ::
                     (x21 :: x22 :: x23 :: List.nil) :: List.nil) ==>
    matrix_value (array_value a (a :: a :: List.nil)) a
      ((x11 :: x21 :: List.nil) :: (x12 :: x22 :: List.nil) ::
       (x13 :: x23 :: List.nil) :: List.nil).
Proof. intros; apply transpose_exact; [first [unary_tac|repeat constructor]|reflexivity|first [unary_tac|repeat constructor]]. Qed.
Example transpose_zero_rows : forall a d,
  transpose a @ Lf @r Sm (Sm Lf) @r matrix_value d a List.nil ==>
    matrix_value (arrays.empty a) a (List.nil :: List.nil :: List.nil).
Proof. intros; apply transpose_exact; [first [unary_tac|repeat constructor]|reflexivity|first [unary_tac|constructor]]. Qed.
Example transpose_zero_columns : forall a d,
  transpose a @ Sm (Sm Lf) @r Lf @r matrix_value d a (List.nil :: List.nil :: List.nil) ==>
    arrays.empty (array_value a (a :: a :: List.nil)).
Proof. intros; apply transpose_exact; [unary_tac|reflexivity|repeat constructor]. Qed.

Definition transpose_example_rows :=
  (numeral 1 :: numeral 2 :: numeral 3 :: List.nil) ::
  (numeral 4 :: numeral 5 :: numeral 6 :: List.nil) :: List.nil.
Definition transpose_example_input :=
  matrix_value (array_value zero (zero :: zero :: zero :: List.nil)) zero transpose_example_rows.
Definition transpose_example_output :=
  matrix_value (array_value zero (zero :: zero :: List.nil)) zero
    ((numeral 1 :: numeral 4 :: List.nil) :: (numeral 2 :: numeral 5 :: List.nil) ::
     (numeral 3 :: numeral 6 :: List.nil) :: List.nil).
Lemma transpose_example_input_typed : infer array_ontology @ transpose_example_input ==>
  Sm (Matrix ('Nat) (Sm (Sm Lf)) (Sm (Sm (Sm Lf)))).
Proof.
  unfold transpose_example_input; change (infer array_ontology @
    matrix_value (array_value zero (zero :: zero :: zero :: List.nil)) zero transpose_example_rows ==>
    Sm (Matrix ('Nat) (sequence_index (List.map (array_value zero) transpose_example_rows))
      (Sm (Sm (Sm Lf))))).
  apply infer_matrix_value.
  - apply array_ontology_support.
  - apply infer_zero; apply array_ontology_supports_number.
  - change (infer array_ontology @ array_value zero (zero :: zero :: zero :: List.nil) ==>
      Sm (Array ('Nat) (sequence_index (zero :: zero :: zero :: List.nil)))).
    apply array_value_typed.
    + apply array_ontology_support.
    + apply infer_zero; apply array_ontology_supports_number.
    + repeat first [apply Forall_cons|apply Forall_nil];
        apply infer_zero; apply array_ontology_supports_number.
  - unfold transpose_example_rows;
      repeat first [apply Forall_cons|apply Forall_nil|apply conj|reflexivity];
      apply numeral_typed; apply array_ontology_supports_number.
Qed.
Example transpose_example_typed : infer_expression array_ontology @
    (transpose zero @ Sm (Sm Lf) @r Sm (Sm (Sm Lf)) @r transpose_example_input) ==>
    Sm (Matrix ('Nat) (Sm (Sm (Sm Lf))) (Sm (Sm Lf))).
Proof.
   apply infer_transpose_application.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.

  - apply infer_zero; apply array_ontology_supports_number.
  - first [unary_tac|repeat constructor].
  - first [unary_tac|repeat constructor].
  - apply transpose_example_input_typed.
Qed.
Example transpose_example_eval :
  transpose zero @ Sm (Sm Lf) @r Sm (Sm (Sm Lf)) @r transpose_example_input ==>
    transpose_example_output.
Proof. apply transpose_two_by_three. Qed.
Example transpose_example_preserved :
  infer array_ontology @ transpose_example_output ==>
    Sm (Matrix ('Nat) (Sm (Sm (Sm Lf))) (Sm (Sm Lf))).
Proof.
   eapply array_ontology_EPT.

  - apply transpose_example_eval.
  - apply transpose_example_typed.
Qed.
Example transpose_example_twice :
  Fk (transpose zero @ Sm (Sm (Sm Lf)) @r Sm (Sm Lf))
    (transpose zero @ Sm (Sm Lf) @r Sm (Sm (Sm Lf)) @r transpose_example_input) ==>
    transpose_example_input.
Proof.
  apply transpose_canonical_identity; [first [unary_tac|repeat constructor]|reflexivity|repeat constructor].
Qed.

End FunctionEnabledExamples.


(** * Mapping examples and rejected widths *)
Unset Default Proof Using.
Definition leaf_row := array_value Lf (Lf :: Lf :: List.nil).
Definition number_rows :=
  (numeral 1 :: numeral 2 :: List.nil) :: (numeral 3 :: numeral 4 :: List.nil) :: List.nil.
Definition leaf_rows := (Lf :: Lf :: List.nil) :: (Lf :: Lf :: List.nil) :: List.nil.
Definition number_matrix := matrix_value number_row zero number_rows.
Definition leaf_matrix := matrix_value leaf_row Lf leaf_rows.

Lemma leaf_row_typed : infer array_ontology @ leaf_row ==> Sm (Array Lf two_index).
Proof.
  unfold leaf_row; change (infer array_ontology @ array_value Lf (Lf :: Lf :: List.nil) ==>
    Sm (Array Lf (sequence_index (Lf :: Lf :: List.nil)))).
  apply array_value_typed; [apply array_ontology_support|apply infer_leaf|].
  repeat first [apply Forall_cons|apply Forall_nil]; apply infer_leaf.
Qed.
Lemma number_matrix_typed : infer array_ontology @ number_matrix ==>
  Sm (Matrix ('Nat) two_index two_index).
Proof.
  unfold number_matrix; change (infer array_ontology @ matrix_value number_row zero number_rows ==>
    Sm (Matrix ('Nat) (sequence_index (List.map (array_value zero) number_rows)) two_index)).
  apply infer_matrix_value.
  - apply array_ontology_support.
  - apply infer_zero; apply array_ontology_supports_number.
  - apply number_row_typed.
  - unfold number_rows; repeat first [apply Forall_cons|apply Forall_nil|apply conj|reflexivity]; apply numeral_typed; apply array_ontology_supports_number.
Qed.
Example matrix_map_changes_element_type : infer_expression array_ontology @
    (map_matrix number_row leaf_row zero Lf ('K1 Lf) @ two_index @r two_index @r number_matrix) ==>
    Sm (Matrix Lf two_index two_index).
Proof.
   eapply infer_matrix_map_application.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.

  - apply number_row_typed.
  - apply leaf_row_typed.
  - apply infer_zero; apply array_ontology_supports_number.
  - apply infer_leaf.
  - apply infer_K1; apply infer_leaf.
  - apply type_app_K_ev.
  - first [unary_tac|repeat constructor].
  - first [unary_tac|repeat constructor].
  - apply number_matrix_typed.
Qed.
Example matrix_map_changes_element_type_eval :
  map_matrix number_row leaf_row zero Lf ('K1 Lf) @ two_index @r two_index @r number_matrix ==>
    leaf_matrix.
Proof.
  unfold number_matrix, leaf_matrix.
  change (map_matrix number_row leaf_row zero Lf ('K1 Lf) @
    sequence_index (List.map (array_value zero) number_rows) @r two_index @r
    matrix_value number_row zero number_rows ==> matrix_value leaf_row Lf leaf_rows).
  apply map_matrix_exact.
  - unfold number_rows; repeat constructor.
  - unfold number_rows, leaf_rows.
    repeat first [apply Forall2_cons|apply Forall2_nil|progress evaluate].
Qed.

Example matrix_map_zero_rows : infer_expression array_ontology @
    (map_matrix number_row leaf_row zero Lf ('K1 Lf) @ Lf @r two_index @r arrays.empty number_row) ==>
    Sm (Matrix Lf Lf two_index).
Proof.
   eapply infer_matrix_map_application.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.

  - apply number_row_typed.
  - apply leaf_row_typed.
  - apply infer_zero; apply array_ontology_supports_number.
  - apply infer_leaf.
  - apply infer_K1; apply infer_leaf.
  - apply type_app_K_ev.
  - first [unary_tac|constructor].
  - first [unary_tac|repeat constructor].
  - apply infer_empty_matrix; [apply array_ontology_support|apply number_row_typed].
Qed.

Definition zero_column_matrix := array_value (arrays.empty zero)
  (arrays.empty zero :: arrays.empty zero :: List.nil).
Lemma zero_column_matrix_typed : infer array_ontology @ zero_column_matrix ==>
  Sm (Matrix ('Nat) two_index Lf).
Proof.
  unfold zero_column_matrix.
  change (infer array_ontology @ array_value (arrays.empty zero)
    (arrays.empty zero :: arrays.empty zero :: List.nil) ==>
    Sm (Array (Array ('Nat) Lf)
      (sequence_index (arrays.empty zero :: arrays.empty zero :: List.nil)))).
  apply array_value_typed; [apply array_ontology_support| |].
  - apply infer_empty; [apply array_ontology_support|apply infer_zero; apply array_ontology_supports_number].
  - repeat first [apply Forall_cons|apply Forall_nil].
    all: apply infer_empty;
      [apply array_ontology_support|apply infer_zero; apply array_ontology_supports_number].
Qed.
Example matrix_map_zero_columns : infer_expression array_ontology @
    (map_matrix (arrays.empty zero) (arrays.empty Lf) zero Lf ('K1 Lf) @ two_index @r Lf @r zero_column_matrix) ==>
    Sm (Matrix Lf two_index Lf).
Proof.
   eapply infer_matrix_map_application.

  - apply array_ontology_supports_list.
  - apply array_ontology_support.

  - apply infer_empty; [apply array_ontology_support|apply infer_zero; apply array_ontology_supports_number].
  - apply infer_empty; [apply array_ontology_support|apply infer_leaf].
  - apply infer_zero; apply array_ontology_supports_number.
  - apply infer_leaf.
  - apply infer_K1; apply infer_leaf.
  - apply type_app_K_ev.
  - first [unary_tac|repeat constructor].
  - first [unary_tac|constructor].
  - apply zero_column_matrix_typed.
Qed.

Example different_column_counts_rejected :
  array_abstractor @ (Matrix ('Nat) (Sm Lf) (Sm Lf) 'C
    Matrix ('Nat) (Sm Lf) two_index) ==> Lf.
Proof. apply append_rows_wrong_width; try (repeat (first [unary_tac|constructor])); discriminate. Qed.

Example mapped_matrix_preserved : infer array_ontology @ leaf_matrix ==> Sm (Matrix Lf two_index two_index).
Proof.
   eapply array_ontology_EPT.

  - apply matrix_map_changes_element_type_eval.
  - apply matrix_map_changes_element_type.
Qed.


(** * Matrix multiplication

    [Matrix0 m n] is a matrix with [m+1] rows and [n+1] columns, so a zero
    dimension cannot be written.  [matrix_mult @ (xs * ys)] takes no index.
    The rows of [xs] and of [ys] are read by consumers, and the length of the
    rows of the result comes from the first row of [ys], which always exists.

    A row [r] of [xs] is read in lock step with the rows of [ys], and the row
    of the result is the sum of [x * y] over the pairs, starting from a row
    of zeros of the length of the first row of [ys].  The inner dimension is checked once, by
    the type of a value: [checked_rows] joins [xs] to the empty array whose
    witness is a row with one entry per row of [ys].  The abstractor of
    append compares the element types, so a disagreement is refused at every
    number of rows, including none ([matrix_mult_refused]).  *)
From Stdlib Require Import String List Arith Lia.
Local Open Scope string_scope.

(** ** Dot product: [dot @ (xs * ys)] reads [xs] in lock step with [ys]. *)
Definition dot_step := Eval cbn -[add mul] in to_tree
  (star "p" (Val add @@ ((Val 'fst @@ Ref "p") ''* (Val mul @@ (Val 'snd @@ Ref "p"))))).
Definition dot := Eval cbn -[array_lock dot_step mk_zero] in to_tree
  (star "t" (Val array_lock @@ (Val dot_step ''* ((Val mk_zero @@ Ref "t") ''* Ref "t")))).
Lemma dot_tag_free : tag_free dot = true.
Proof. vm_compute; reflexivity. Qed.
Lemma infer_dot : forall AI, infer AI @ dot ==> Sm dot.
Proof. intros; apply infer_tag_free; exact dot_tag_free. Qed.

(** ** Multiplication *)
Definition axpy := Eval cbn -[add mul] in to_tree
  (star "x" (star "p" (Val add @@ ((Val 'fst @@ Ref "p") ''*
     (Val mul @@ (Ref "x" ''* (Val 'snd @@ Ref "p"))))))).
Definition row_step := Eval cbn -[array_zip axpy mk_zero] in to_tree
  (star "p" (Val array_zip @@ (''wait[Val axpy, Val 'fst @@ (Val 'snd @@ Ref "p")] ''*
     ((Val mk_zero @@ Ref "p") ''* ((Val 'fst @@ Ref "p") ''* (Val 'snd @@ (Val 'snd @@ Ref "p"))))))).
Definition row_action := Eval cbn -[array_lock row_step] in to_tree
  (star "c" (star "r" (Val array_lock @@ (Val row_step ''*
     ((Val 'fst @@ Ref "c") ''* (Ref "r" ''* (Val 'snd @@ Ref "c"))))))).
Definition Matrix0 m n := Matrix ('Nat) (Sm m) (Sm n).
Definition checked_rows := Eval cbn -[array_map array_append mk_zero] in to_tree
  (star "t" (Val array_append @@
     (empty_t (Val array_map @@ (Val mk_zero ''* ((Val mk_zero @@ Ref "t") ''* (Val 'snd @@ Ref "t"))))
      ''* (Val 'fst @@ Ref "t")))).
Definition first_zeros := Eval cbn -[array_map array_uncons mk_zero] in to_tree
  (star "t" (Val array_map @@ (Val mk_zero ''* ((Val mk_zero @@ Ref "t") ''*
     (Val 'fst @@ (Val array_uncons @@ (Val 'snd @@ Ref "t"))))))).
Definition matrix_mult := Eval cbn -[array_map checked_rows first_zeros row_action] in to_tree
  (star "t" ((star "r" ((star "z" (Val array_map @@
      (''wait[Val row_action, Ref "z" ''* (Val 'snd @@ Ref "t")] ''* (Ref "z" ''* Ref "r"))))
      @@ (Val first_zeros @@ Ref "t")))
    @@ (Val checked_rows @@ Ref "t"))).

Lemma matrix_mult_tag_free : tag_free matrix_mult = true.
Proof. vm_compute; reflexivity. Qed.

Section MatrixTyping.
Variable AI : Combination.
Hypothesis HA : supports_arrays AI.
Hypothesis HN : supports_number AI.
Local Ltac ty_onto_more ::= eapply declaration_apply; [exact HA|first [apply array_abstractor_zero|apply array_abstractor_step]].

Lemma type_app_mk_zero : forall U, type_app AI @ mk_zero @r U ==> Sm ('Nat).
Proof. intro U; repeat ty. Qed.

Lemma type_app_dot_step :
  type_app AI @ dot_step @r ('Nat '* ('Nat '* 'Nat)) ==> Sm ('Nat).
Proof.
  pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_add AI HN) as H1; pose proof (type_app_mul AI HN) as H2.
  unfold dot_step; repeat ty.
Qed.
Lemma type_app_dot : forall n, unary_index n ->
  type_app AI @ dot @r (Array ('Nat) n '* Array ('Nat) n) ==> Sm ('Nat).
Proof.
  intros n Hn; pose proof type_app_mk_zero as H0.
  pose proof (type_app_array_lock AI HA (fun _ => 'Nat) dot_step ('Nat) ('Nat) n Hn
    (fun _ => type_app_dot_step)) as H1.
  cbv beta in H1.
  unfold dot; repeat ty.
Qed.

Lemma type_app_axpy : type_app AI @ 'wait[axpy, 'Nat] @r ('Nat '* 'Nat) ==> Sm ('Nat).
Proof.
  pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_add AI HN) as H1; pose proof (type_app_mul AI HN) as H2.
  eapply type_app_wait; unfold axpy; repeat ty.
Qed.
Lemma type_app_row_step : forall p, unary_index p ->
  type_app AI @ row_step @r (Array ('Nat) p '* ('Nat '* Array ('Nat) p)) ==> Sm (Array ('Nat) p).
Proof.
  intros p Hp; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_mk_zero) as H0.
  pose proof (type_app_array_zip AI HA _ _ _ _ p Hp type_app_axpy) as H1.
  unfold row_step; repeat ty.
Qed.
Local Opaque array_lock array_map array_append mk_zero row_step.
Lemma type_app_row_action : forall p n, unary_index p -> unary_index n ->
  type_app AI @ 'wait[row_action, Array ('Nat) p '* Array (Array ('Nat) p) n] @r Array ('Nat) n
    ==> Sm (Array ('Nat) p).
Proof.
  intros p n Hp Hn; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof (type_app_array_lock AI HA (fun _ => Array ('Nat) p) row_step ('Nat) (Array ('Nat) p) n Hn
    (fun _ => type_app_row_step p Hp)) as H1.
  cbv beta in H1.
  eapply type_app_wait; unfold row_action; repeat ty.
Qed.
Local Opaque row_action array_uncons.
Lemma type_app_first_zeros : forall A n p, unary_index n -> unary_index p ->
  type_app AI @ first_zeros @r (A '* Array (Array ('Nat) p) (Sm n)) ==> Sm (Array ('Nat) p).
Proof.
  intros A n p Hn Hp; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof type_app_mk_zero as H0.
  pose proof (type_app_array_map AI HA _ _ _ _ Hp (H0 ('Nat))) as H3.
  pose proof (type_app_array_uncons AI HA (Array ('Nat) p) n Hn) as H1.
  unfold first_zeros; repeat ty; apply H0.
Qed.
Lemma type_app_matrix_mult : forall m n p, unary_index m -> unary_index n -> unary_index p ->
  type_app AI @ matrix_mult @r (Matrix0 m n '* Matrix0 n p) ==> Sm (Matrix0 m p).
Proof.
  intros m n p Hm Hn Hp; pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
  pose proof type_app_mk_zero as H0.
  pose proof (unary_stem _ Hm) as Hm'; pose proof (unary_stem _ Hn) as Hn'; pose proof (unary_stem _ Hp) as Hp'.
  pose proof (type_app_row_action (Sm p) (Sm n) Hp' Hn') as H2.
  pose proof (type_app_array_map AI HA _ _ _ _ Hn' (H0 (Array ('Nat) (Sm p)))) as H4.
  pose proof (type_app_array_map AI HA _ _ _ _ Hm' H2) as H5.
  pose proof (type_app_array_append AI (Array ('Nat) (Sm n)) Lf (Sm m) HA) as H6.
  cbn [index_sum] in H6.
  pose proof (type_app_first_zeros (Matrix0 m n) n (Sm p) Hn Hp') as Hz.
  unfold matrix_mult, checked_rows, Matrix0, Matrix in *; repeat ty; apply H0.
Qed.
End MatrixTyping.

(** Refusal *)
Local Ltac ty_onto_more ::= eapply declaration_apply; [eassumption|first [apply array_abstractor_zero|apply array_abstractor_step]].

Local Lemma S_success_inv : forall (AI : Decl) G F U V,
 (forall E N, 'S2[G,F] <> 'tagged[E,N]) ->
 get_name_test @ ('S2[G,F]) ==> Lf ->
 type_app AI @ ('S2[G,F]) @r U ==> Sm V ->
 exists A B, type_app AI @ G @r U ==> Sm A /\
 type_app AI @ F @r U ==> Sm B /\ type_app AI @ A @r B ==> Sm V.
Proof.
 intros AI G F U V HP HN H.
 Local Transparent abstract_case.
 assert (HA : abstract_case @ ('S2[G,F]) ==> Lf)
   by (unfold abstract_case; apply type_app_abstract_case_S_none; exact HP).
 Local Opaque abstract_case.
 eapply default_S_inv; exact (app_plain_inv _ _ _ _ HA H).
Qed.

Local Ltac invert_S H a b H1 H2 H3 :=
  match type of H with
  | type_app ?ai @ ('S2[?g,?f]) @r ?u ==> Sm ?v =>
    let Hn := fresh "Hn" in
    assert (Hn : forall E N, 'S2[g,f] <> 'tagged[E,N]) by (intros; discriminate);
    destruct (S_success_inv ai g f u v Hn ltac:(reject_name) H) as [a [b [H1 [H2 H3]]]];
    clear Hn
  end.

Lemma type_app_tagger_inv : forall (AI : Decl) n C V,
  type_app AI @ 'tagger[n] @r C ==> Sm V ->
  exists E, AI @ n @r type_app AI @r C ==> Sm E.
Proof.
  intros AI n C V H.
  destruct (S_success_inv AI 'tag_head ('S2['K1 'make_label, 'K1 n]) C V ltac:(intros; discriminate) ltac:(reject_name) H) as [a [b [H1 [H2 H3]]]].
  assert (Ha : type_app AI @ 'tag_head @r C ==> Sm (Sm (Sm ('K1 C)))).
  { new_S; [discriminate|apply type_app_K_ev| |].
    + new_S; [discriminate|apply type_app_K_ev|apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate|].
      apply type_app_leaf_ev.
    + apply type_app_leaf_ev. }
  assert (Hb : type_app AI @ 'S2['K1 'make_label, 'K1 n] @r C ==> Sm ('S2['K,'K1 n])).
  { new_S; [discriminate|apply type_app_K_ev|apply type_app_K_ev|].
    new_S; [discriminate| | |].
    + apply type_app_K_ev.
    + apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate.
    + apply type_app_stem_ev; apply type_app_stem_structural; intros; discriminate. }
  pose proof (eval_deterministic _ _ H1 _ Ha) as E1; inversion E1; subst a.
  pose proof (eval_deterministic _ _ H2 _ Hb) as E2; inversion E2; subst b.
  apply type_app_stem_inv in H3.
  apply type_app_stem_tagged_success_inv in H3.
  destruct H3 as [E [HE _]]; exists E; exact HE.
Qed.

Lemma array_append_refused : forall (AI : Decl) A B n m V,
  supports_arrays AI -> A <> B ->
  ~ type_app AI @ array_append @r (Array A n '* Array B m) ==> Sm V.
Proof.
  intros AI A B n m V HA Hne H.
  unfold array_append in H; cbn in H.
  invert_S H a b H1 H2 H3.
  pose proof (eval_deterministic _ _ H1 _ (type_app_K_ev AI _ _)) as E1; inversion E1; subst a.
  assert (Hb : type_app AI @ 'S2 [Lf 'C (Lf 'C ('K 'C 'snd)), 'fst] @r (Array A n '* Array B m)
      ==> Sm (Array B m 'C Array A n)).
  { pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
    repeat ty. }
  pose proof (eval_deterministic _ _ H2 _ Hb) as E2; inversion E2; subst b.
  destruct (type_app_tagger_inv AI _ _ _ H3) as [E HE].
  destruct (declaration_apply_inv _ _ _ _ _ HE) as [R [D [H4 [H5 H6]]]].
  pose proof (eval_deterministic _ _ H4 _ HA) as E3; subst R.
  assert (H7 : ('K1 array_abstractor) @ type_app AI ==> array_abstractor) by evaluate.
  pose proof (eval_deterministic _ _ H5 _ H7) as E4; subst D.
  pose proof (eval_deterministic _ _ H6 _ (array_abstractor_wrong_domain A B n m Hne)) as E5.
  discriminate E5.
Qed.

Theorem matrix_mult_refused : forall (AI : Decl) m n k p V,
  supports_arrays AI -> supports_number AI -> unary_index n -> unary_index k -> n <> k ->
  ~ type_app AI @ matrix_mult @r (Matrix0 m n '* Matrix0 k p) ==> Sm V.
Proof.
  intros AI m n k p V HA HN Hn Hk Hne H.
  unfold matrix_mult in H.
  invert_S H a b H1 H2 H3.
  clear H1 H3.
  unfold checked_rows in H2.
  invert_S H2 a2 b2 H4 H5 H6.
  pose proof (eval_deterministic _ _ H4 _ (type_app_K_ev AI _ _)) as E1; inversion E1; subst a2.
  pose proof (unary_stem _ Hk) as Hk'.
  eapply (array_append_refused AI (Array ('Nat) (Sm k)) (Array ('Nat) (Sm n)) Lf (Sm m) b HA); [|].
  - intro HE; apply Hne.
    pose proof (Array_index_injective _ _ _ _ Hk' (unary_stem _ Hn) HE) as HI.
    injection HI; intro; symmetry; assumption.
  - pose proof (type_app_fst_product AI) as Hf; pose proof (type_app_snd_product AI) as Hs.
    pose proof (type_app_mk_zero AI HN) as H0.
    pose proof (type_app_array_map AI HA _ _ _ _ Hk' (H0 (Array ('Nat) (Sm p)))) as HW.
    assert (Hb : Sm b2 = Sm (Array (Array ('Nat) (Sm k)) Lf '* Array (Array ('Nat) (Sm n)) (Sm m))).
    { eapply eval_deterministic; [exact H5|].
      unfold Matrix0, Matrix in *; repeat ty; apply H0. }
    inversion Hb; subst b2; exact H6.
Qed.

(** Evaluation *)
Local Opaque array_zip array_lock array_map array_append.
Lemma axpy_eval : forall x a b, 'wait[axpy, numeral x] @ (numeral a '* numeral b) ==> numeral (a + x * b).
Proof.
  intros x a b; pose proof (mul_numerals x b) as H1; pose proof (add_numerals a (x * b)) as H2.
  apply wait_eval; unfold axpy; cbn -[add mul numeral]; d_eval.
Qed.
Fixpoint axpy_spec x (v y : list nat) := match v, y with
  | a :: v', b :: y' => (a + x * b) :: axpy_spec x v' y'
  | _, _ => nil end.
Fixpoint row_spec (v r : list nat) (Y : list (list nat)) := match r, Y with
  | x :: r', y :: Y' => row_spec (axpy_spec x v y) r' Y'
  | _, _ => v end.
Definition enc e ns := array_value e (List.map numeral ns).
Lemma zips_axpy : forall x v y, length v = length y ->
  zips ('wait[axpy, numeral x]) (List.map numeral v) (List.map numeral y)
    (List.map numeral (axpy_spec x v y)).
Proof.
  intros x v; induction v as [|a v IH]; intros [|b y] H; try discriminate; cbn; constructor.
  - apply axpy_eval.
  - apply IH; injection H; auto.
Qed.
Lemma length_axpy : forall x v y, length v = length y -> length (axpy_spec x v y) = length v.
Proof.
  intros x v; induction v as [|a v IH]; intros [|b y] H; try discriminate; cbn; [reflexivity|].
  injection H as H; rewrite IH; auto.
Qed.
Definition pointwise_products (xs ys : list nat) :=
  List.map (fun p => Nat.mul (fst p) (snd p)) (List.combine xs ys).
Definition dot_spec xs ys := List.fold_right Nat.add 0 (pointwise_products xs ys).
Lemma dot_step_eval : forall s x y,
  dot_step @ (numeral s '* (numeral x '* numeral y)) ==> numeral (s + x * y).
Proof.
  intros s x y; pose proof (mul_numerals x y) as H1; pose proof (add_numerals s (x * y)) as H2.
  unfold dot_step; cbn -[add mul numeral]; d_eval.
Qed.
Lemma folds2_dot : forall xs ys s, length xs = length ys ->
  folds2 dot_step (numeral s) (List.map numeral xs) (List.map numeral ys)
    (numeral (s + dot_spec xs ys)).
Proof.
  intro xs; induction xs as [|x xs IH]; intros [|y ys] s H; try discriminate; cbn [List.map].
  - replace (s + dot_spec List.nil List.nil) with s by (cbn; lia); constructor.
  - econstructor; [apply dot_step_eval|].
    replace (s + dot_spec (x :: xs) (y :: ys)) with ((s + x * y) + dot_spec xs ys)
      by (unfold dot_spec, pointwise_products; cbn; lia).
    apply IH; injection H; auto.
Qed.
Lemma dot_numerals : forall xs ys d e, length xs = length ys ->
  dot @ (array_value d (List.map numeral xs) '* array_value e (List.map numeral ys)) ==>
    numeral (dot_spec xs ys).
Proof.
  intros xs ys d e H.
  set (t := array_value d (List.map numeral xs) '* array_value e (List.map numeral ys)).
  pose proof (array_lock_eval _ _ _ _ _ _ _ (array_value_reads d _) (array_value_reads e _)
    (folds2_dot xs ys 0 H)) as H1.
  pose proof (mk_zero_eval t) as H2.
  cbn [Nat.add] in H1.
  unfold dot, t; cbn -[array_lock dot_step mk_zero numeral]; fold t; d_eval.
Qed.

Lemma row_step_eval : forall x v y d e, length v = length y ->
  row_step @ (enc d v '* (numeral x '* enc e y)) ==> enc zero (axpy_spec x v y).
Proof.
  intros x v y d e H.
  pose proof (array_zip_eval _ zero _ _ _ _ _ (array_value_reads d _) (array_value_reads e _) (zips_axpy x v y H)) as H1.
  pose proof (mk_zero_eval (enc d v '* (numeral x '* enc e y))) as H2.
  unfold row_step, enc; cbn -[array_zip axpy mk_zero numeral]. d_eval.
Qed.
Lemma folds2_rows : forall r Y v e, length r = length Y ->
  List.Forall (fun y => length y = length v) Y ->
  folds2 row_step (enc zero v) (List.map numeral r) (List.map (enc e) Y) (enc zero (row_spec v r Y)).
Proof.
  intro r; induction r as [|x r IH]; intros [|y Y] v e HL HY; try discriminate; cbn.
  - constructor.
  - inversion HY; subst.
    assert (HL2 : length v = length y) by auto.
    econstructor; [apply row_step_eval; exact HL2|].
    apply IH; [injection HL; auto|rewrite length_axpy by exact HL2; exact H2].
Qed.

Lemma row_action_eval : forall v0 c r Yl rl v, reads r rl -> reads c Yl ->
  folds2 row_step v0 rl Yl v -> 'wait[row_action, v0 '* c] @ r ==> v.
Proof.
  intros v0 c r Yl rl v Hr Hc H.
  pose proof (array_lock_eval _ _ _ _ _ _ _ Hr Hc H) as H1.
  apply wait_eval; unfold row_action; cbn -[array_lock row_step]; d_eval.
Qed.

Lemma reads_append_empty : forall w a xs, reads a xs -> reads (append_value (arrays.empty w) a) xs.
Proof.
  intros w a xs Ha f v H; eapply append_value_eval; [apply empty_eval|apply Ha; exact H].
Qed.

Lemma zeros_eval : forall a xs, reads a xs ->
  array_map @ (mk_zero '* (zero '* a)) ==> array_value zero (List.map (fun _ => zero) xs).
Proof.
  intros a xs Ha; eapply array_map_eval; [exact Ha|].
  clear Ha; induction xs as [|x xs IH]; cbn; [constructor|constructor; [apply mk_zero_eval|exact IH]].
Qed.

Lemma checked_rows_eval : forall xs ys yl, reads ys yl ->
  checked_rows @ (xs '* ys) ==>
    append_value (arrays.empty (array_value zero (List.map (fun _ => zero) yl))) xs.
Proof.
  intros xs ys yl Hy.
  pose proof (zeros_eval _ _ Hy) as H1.
  pose proof (mk_zero_eval (xs '* ys)) as H2.
  pose proof (array_append_eval (arrays.empty (array_value zero (List.map (fun _ => zero) yl))) xs) as H3.
  unfold arrays.empty in H3 |- *.
  unfold checked_rows; cbn -[array_map array_append mk_zero]; d_eval.
Qed.

Lemma first_zeros_eval : forall xs ys y yl zs, reads ys (y :: yl) -> reads y zs ->
  first_zeros @ (xs '* ys) ==> array_value zero (List.map (fun _ => zero) zs).
Proof.
  intros xs ys y yl zs Hy Hz.
  pose proof (zeros_eval _ _ Hz) as H1.
  pose proof (mk_zero_eval (xs '* ys)) as H2.
  pose proof (array_uncons_eval _ _ _ Hy) as H3.
  unfold first_zeros; cbn -[array_map array_uncons mk_zero]; d_eval.
Qed.

Lemma matrix_mult_eval : forall xs ys xl y yl zs vs,
  reads xs xl -> reads ys (y :: yl) -> reads y zs ->
  List.Forall2 (fun r v => 'wait[row_action,
     array_value zero (List.map (fun _ => zero) zs) '* ys] @ r ==> v) xl vs ->
  matrix_mult @ (xs '* ys) ==> array_value (array_value zero (List.map (fun _ => zero) zs)) vs.
Proof.
  intros xs ys xl y yl zs vs Hx Hy Hz H.
  pose proof (checked_rows_eval xs ys (y :: yl) Hy) as H1.
  pose proof (first_zeros_eval xs ys y yl zs Hy Hz) as H2.
  pose proof (array_map_eval _ (array_value zero (List.map (fun _ => zero) zs)) _ _ _
     (reads_append_empty (array_value zero (List.map (fun _ => zero) (y :: yl))) _ _ Hx) H) as H4.
  unfold matrix_mult; cbn -[array_map checked_rows first_zeros row_action]; d_eval.
Qed.

Local Open Scope nat_scope.
Definition zeros (zs : list Combination) := List.map (fun _ => 0) zs.
Lemma enc_zeros : forall zs, enc zero (zeros zs) = array_value zero (List.map (fun _ => zero) zs).
Proof. intros zs; unfold enc, zeros; rewrite List.map_map; reflexivity. Qed.
Lemma matrix_mult_numerals : forall zs dx dy ex ey X y Y,
  reads (enc ey y) zs ->
  List.Forall (fun r => length r = length (y :: Y)) X ->
  List.Forall (fun y' => length y' = length zs) (y :: Y) ->
  matrix_mult @ (array_value dx (List.map (enc ex) X) '* array_value dy (List.map (enc ey) (y :: Y))) ==>
    array_value (enc zero (zeros zs)) (List.map (fun r => enc zero (row_spec (zeros zs) r (y :: Y))) X).
Proof.
  intros zs dx dy ex ey X y Y Hz HX HY.
  rewrite enc_zeros.
  eapply matrix_mult_eval with (y := enc ey y) (yl := List.map (enc ey) Y);
    [apply array_value_reads|apply array_value_reads|exact Hz|].
  rewrite <- enc_zeros.
  revert HX HY; generalize (y :: Y) as Ys; intros Ys HX HY.
  induction HX as [|r X Hr _ IH]; cbn [List.map]; [constructor|]; constructor; [|exact IH].
  eapply row_action_eval; [apply array_value_reads|apply array_value_reads|].
  apply folds2_rows; [rewrite Hr; rewrite ?List.length_map; reflexivity|].
  unfold zeros; rewrite List.length_map; exact HY.
Qed.

Section ApplicationTyping.
Variable AI : Decl.
Hypothesis HA : supports_arrays AI.
Hypothesis HN : supports_number AI.
Lemma infer_matrix_mult : infer AI @ matrix_mult ==> Sm matrix_mult.
Proof using. apply infer_tag_free; exact matrix_mult_tag_free. Qed.
Theorem infer_matrix_mult_application : forall m n p xs ys,
 unary_index m -> unary_index n -> unary_index p ->
 infer AI @ xs ==> Sm (Matrix0 m n) ->
 infer AI @ ys ==> Sm (Matrix0 n p) ->
 infer_expression AI @ (matrix_mult @ (xs '* ys)) ==> Sm (Matrix0 m p).
Proof using AI HA HN.
 intros m n p xs ys Hm Hn Hp HX HY.
 assert (HT : infer AI @ (xs '* ys) ==> Sm (Matrix0 m n '* Matrix0 n p))
   by (apply infer_product_value; assumption).
 eapply infer_application;
   [apply infer_matrix_mult|exact HT|apply type_app_matrix_mult; assumption].
Qed.
End ApplicationTyping.

Lemma infer_dot_application : forall (AI : Decl) n xs ys,
  supports_arrays AI -> supports_number AI -> unary_index n ->
  infer AI @ xs ==> Sm (Array ('Nat) n) -> infer AI @ ys ==> Sm (Array ('Nat) n) ->
  infer_expression AI @ (dot @ (xs '* ys)) ==> Sm ('Nat).
Proof.
  intros AI n xs ys HA HN Hn HX HY; eapply infer_application;
    [apply infer_dot|apply infer_product_value; eassumption|apply type_app_dot; assumption].
Qed.
Definition dot_example_left := array_value zero (List.map numeral (1 :: 2 :: 3 :: List.nil)).
Definition dot_example_right := array_value zero (List.map numeral (4 :: 5 :: 6 :: List.nil)).
Lemma numeral_array_typed : forall ns,
  infer array_ontology @ array_value zero (List.map numeral ns) ==>
    Sm (Array ('Nat) (sequence_index (List.map numeral ns))).
Proof.
  intro ns; apply array_value_typed.
  - apply array_ontology_support.
  - apply infer_zero; apply array_ontology_supports_number.
  - induction ns; cbn [List.map]; constructor; [|exact IHns].
    apply numeral_typed; apply array_ontology_supports_number.
Qed.
Example dot_example_typed : infer_expression array_ontology @
    (dot @ (dot_example_left '* dot_example_right)) ==> Sm ('Nat).
Proof.
  apply infer_dot_application with (n := Sm (Sm (Sm Lf))).
  - apply array_ontology_support.
  - apply array_ontology_supports_number.
  - first [unary_tac|repeat constructor].
  - apply (numeral_array_typed (1 :: 2 :: 3 :: List.nil)).
  - apply (numeral_array_typed (4 :: 5 :: 6 :: List.nil)).
Qed.
Example dot_example_eval :
  dot @ (dot_example_left '* dot_example_right) ==> numeral 32.
Proof. exact (dot_numerals (1 :: 2 :: 3 :: List.nil) (4 :: 5 :: 6 :: List.nil) zero zero eq_refl). Qed.
Example dot_empty_eval : dot @ (arrays.empty zero '* arrays.empty zero) ==> zero.
Proof. exact (dot_numerals List.nil List.nil zero zero eq_refl). Qed.
Example dot_example_preserved :
  infer array_ontology @ numeral 32 ==> Sm ('Nat).
Proof.
   eapply array_ontology_EPT.
  - apply dot_example_eval.
  - apply dot_example_typed.
Qed.

(** Multiply [1,2,3; 4,5,6] by [1,4; 2,5; 3,6]. *)
Definition two_zeros := array_value zero (zero :: zero :: List.nil).
Definition matrix_mult_example_rows := (1 :: 2 :: 3 :: List.nil) :: (4 :: 5 :: 6 :: List.nil) :: List.nil.
Definition matrix_mult_example_columns :=
  (1 :: 4 :: List.nil) :: (2 :: 5 :: List.nil) :: (3 :: 6 :: List.nil) :: List.nil.
Definition matrix_product_example_result :=
  matrix_value two_zeros zero
    ((numeral 14 :: numeral 32 :: List.nil) ::
     (numeral 32 :: numeral 77 :: List.nil) :: List.nil).
Example matrix_mult_example_eval :
 matrix_mult @ (transpose_example_input '* transpose_example_output) ==>
   matrix_product_example_result.
Proof.
  exact (matrix_mult_numerals (numeral 1 :: numeral 4 :: List.nil) _ _ zero zero
    matrix_mult_example_rows (1 :: 4 :: List.nil)
    ((2 :: 5 :: List.nil) :: (3 :: 6 :: List.nil) :: List.nil)
    (array_value_reads _ _) ltac:(repeat constructor) ltac:(repeat constructor)).
Qed.
Example matrix_mult_example_typed :
 infer_expression array_ontology @ (matrix_mult @ (transpose_example_input '* transpose_example_output)) ==>
 Sm (Matrix0 (Sm Lf) (Sm Lf)).
Proof.
  apply infer_matrix_mult_application with (n := Sm (Sm Lf)).
  - apply array_ontology_support.
  - apply array_ontology_supports_number.
  - first [unary_tac|repeat constructor].
  - first [unary_tac|repeat constructor].
  - first [unary_tac|repeat constructor].
  - apply transpose_example_input_typed.
  - apply transpose_example_preserved.
Qed.
Example matrix_mult_example_preserved :
 infer array_ontology @ matrix_product_example_result ==>
 Sm (Matrix ('Nat) (Sm (Sm Lf)) (Sm (Sm Lf))).
Proof.
  eapply array_ontology_EPT.
 - apply matrix_mult_example_eval.
 - apply matrix_mult_example_typed.
Qed.
(** Paper notation: [Matrix[m,n]]. *)
Notation "'Matrix [ m , n ]" := (Matrix ('Nat) m n) (at level 0, only parsing).
Notation "'Matrix0 [ m , n ]" := (Matrix0 m n) (at level 0, only parsing).

(** The size of the program, as Appendix B reports it. *)
Lemma matrix_mult_size : tree_size matrix_mult = 16662.
Proof. vm_compute; reflexivity. Qed.
