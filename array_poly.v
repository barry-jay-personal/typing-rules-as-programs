(** * Step 82, stage 7, part 1: array append and map, for every element type.

    The programs receive the codes of their element types and build their
    results with the generic constructors:

      array_append @ (c * (xs * ys)) =
        xs @ (ys * \p. gen_prepend @ (c * (fst p * array_append @ (c * (snd p * ys)))))
      array_map @ (f * (cb * xs)) =
        xs @ (gen_empty @ cb * \p. gen_prepend @ (cb * (f @ fst p * array_map @ (f * (cb * snd p)))))

    Both are recursions by [Z] alone.  Type application unfolds them along
    the length of the first array: at length [Sm k] the eliminator takes the
    prepend branch at [Array A k], at [Lf] it takes the base.  The proofs are
    by induction on the length, for every element type [A] (with concrete
    names) and every pair of lengths: each step is the symbolic type
    application of one unfolding ([tpsA]), with the induction hypothesis at
    the recursive call. *)

From Stdlib Require Import String List Bool Lia.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists department lists_rt queries self_typing sums paper_ontology fun_ontology size_queries poly array_family.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation PO := paper_ontology.

(** The type that inference computes, at paper_ontology. *)
Definition tyA (t : Combination) : Combination :=
  match runp 40 (infer PO @ t) with Some (Sm A) => A | _ => Lf end.

Ltac by_runAr := apply (runp_sound 40); match goal with |- _ = ?r => tryif has_evar r then (vm_compute; reflexivity) else vm_done end.

(** Symbolic type application at paper_ontology. *)
Ltac tpsA := repeat first
  [ eassumption
  | (apply (type_app_gen_prepend PO PO_gpre); assumption)
  | (apply (type_app_gen_empty PO PO_gemp); assumption)
  | apply (type_app_Array_leaf PO PO_array)
  | eapply (type_app_Array_succ PO PO_array)
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd ].

(** ** The programs *)

Definition array_append_term : Term :=
  let q := Ref "q" in
  let c := Val 'fst @@ q in
  let xs := Val 'fst @@ (Val 'snd @@ q) in
  let ys := Val 'snd @@ (Val 'snd @@ q) in
  let p := Ref "p" in
  star "self" (star "q"
    (xs @@ (ys ''* (star "p"
       (op gen_prepend @@ (c ''* ((Val 'fst @@ p) ''* (Ref "self" @@ (c ''* ((Val 'snd @@ p) ''* ys)))))))))).
Definition array_append_body : Combination := Eval cbn -[gen_prepend] in to_tree array_append_term.
Definition array_append : Combination := Z array_append_body.

Definition array_map_term : Term :=
  let t := Ref "t" in
  let f := Val 'fst @@ t in
  let cb := Val 'fst @@ (Val 'snd @@ t) in
  let xs := Val 'snd @@ (Val 'snd @@ t) in
  let p := Ref "p" in
  star "self" (star "t"
    (xs @@ ((op gen_empty @@ cb) ''* (star "p"
       (op gen_prepend @@ (cb ''* ((f @@ (Val 'fst @@ p)) ''* (Ref "self" @@ (f ''* (cb ''* (Val 'snd @@ p))))))))))).
Definition array_map_body : Combination := Eval cbn -[gen_prepend gen_empty] in to_tree array_map_term.
Definition array_map : Combination := Z array_map_body.

Definition T_aa : Combination := Eval vm_compute in tyA array_append.
Definition T_am : Combination := Eval vm_compute in tyA array_map.

Lemma infer_array_append : infer PO @ array_append ==> Sm T_aa. Proof. by_runAr. Qed.
Lemma infer_array_map : infer PO @ array_map ==> Sm T_am. Proof. by_runAr. Qed.

(** ** Type application, by induction on the length *)

Lemma type_app_array_append : forall A n m, names_concrete A ->
  tp PO @ T_aa @r (code A '* (Array A (idx n) '* Array A (idx m))) ==> Sm (Array A (idx (n + m))).
Proof.
  intros A n m HA; induction n as [|n IH]; cbn [idx Nat.add] in *; unfold T_aa in *; tpsA.
Qed.

Lemma type_app_array_map : forall A B F n, names_concrete B -> tp PO @ F @r A ==> Sm B ->
  tp PO @ T_am @r (F '* (code B '* Array A (idx n))) ==> Sm (Array B (idx n)).
Proof.
  intros A B F n HB HF; induction n as [|n IH]; cbn [idx] in *; unfold T_am in *; tpsA.
Qed.

(** ** The paper's theorems *)

Theorem array_append_polymorphic :
  infer PO @ array_append ==> Sm T_aa /\
  forall A n m, names_concrete A ->
    tp PO @ T_aa @r (code A '* (Array A (idx n) '* Array A (idx m))) ==> Sm (Array A (idx (n + m))).
Proof. split; [exact infer_array_append|exact type_app_array_append]. Qed.

(** The element type of a typed array has concrete names. *)
Lemma array_type_names : forall O xs A k, infer O @ xs ==> Sm (Array A k) -> names_concrete A.
Proof.
  intros O xs A k H; apply code_concrete_inv. unfold Array in H.
  destruct (no_junk O xs _ H) as [f [F [D [_ [Hn _]]]]].
  unfold array_tag in Hn; destruct (concrete_Fk _ _ Hn) as [_ [_ Hn2]];
  destruct (concrete_Fk _ _ Hn2) as [_ [Hc _]]; exact Hc.
Qed.

Theorem infer_array_append_application : forall A n m xs ys,
  infer PO @ xs ==> Sm (Array A (idx n)) -> infer PO @ ys ==> Sm (Array A (idx m)) ->
  infer_expression PO @ (array_append @ (code A '* (xs '* ys))) ==> Sm (Array A (idx (n + m))).
Proof.
  intros A n m xs ys Hx Hy; pose proof (array_type_names _ _ _ _ Hx) as HA.
  assert (Hq : infer PO @ (code A '* (xs '* ys)) ==> Sm (code A '* (Array A (idx n) '* Array A (idx m))))
    by (apply pair_typed; [apply code_self_typed, HA|apply pair_typed; assumption]).
  eapply ie_fork; [apply ie_stem, infer_array_append|apply ie_stem, Hq|apply type_app_array_append, HA].
Qed.

Theorem array_map_polymorphic :
  infer PO @ array_map ==> Sm T_am /\
  forall A B F n, names_concrete B -> tp PO @ F @r A ==> Sm B ->
    tp PO @ T_am @r (F '* (code B '* Array A (idx n))) ==> Sm (Array B (idx n)).
Proof. split; [exact infer_array_map|exact type_app_array_map]. Qed.

Theorem infer_array_map_application : forall A B f F n xs, names_concrete B ->
  infer PO @ f ==> Sm F -> tp PO @ F @r A ==> Sm B -> infer PO @ xs ==> Sm (Array A (idx n)) ->
  infer_expression PO @ (array_map @ (f '* (code B '* xs))) ==> Sm (Array B (idx n)).
Proof.
  intros A B f F n xs HB Hf HF Hx.
  assert (Hq : infer PO @ (f '* (code B '* xs)) ==> Sm (F '* (code B '* Array A (idx n))))
    by (apply pair_typed; [exact Hf|apply pair_typed; [apply code_self_typed, HB|exact Hx]]).
  eapply ie_fork; [apply ie_stem, infer_array_map|apply ie_stem, Hq|apply type_app_array_map; assumption].
Qed.

(** ** Examples, by computation *)

Definition a12 := prepend Nat (idx 1) one (prepend Nat (idx 0) two (empty Nat)).
Definition a0 := prepend Nat (idx 0) zero (empty Nat).
Definition a120 := prepend Nat (idx 2) one (prepend Nat (idx 1) two (prepend Nat (idx 0) zero (empty Nat))).
Definition a23 := prepend Nat (idx 1) two (prepend Nat (idx 0) (succ two) (empty Nat)).

Example a12_typed : infer PO @ a12 ==> Sm (Array Nat (idx 2)). Proof. by_runAr. Qed.
Example gen_prepend_typed : infer_expression PO @ (gen_prepend @ (code Nat '* (zero '* empty Nat))) ==> Sm (Array Nat (idx 1)).
Proof. by_runAr. Qed.
Example gen_prepend_wrong : infer_expression PO @ (gen_prepend @ (code Nat '* (tt '* empty Nat))) ==> Lf. Proof. by_runAr. Qed.
Example array_append_eval : array_append @ (code Nat '* (a12 '* a0)) ==> a120. Proof. by_runAr. Qed.
Example array_append_typed : infer_expression PO @ (array_append @ (code Nat '* (a12 '* a0))) ==> Sm (Array Nat (idx 3)).
Proof. by_runAr. Qed.
Example array_map_eval : array_map @ (succ_fn '* (code Nat '* a12)) ==> a23. Proof. by_runAr. Qed.
Example array_map_typed : infer_expression PO @ (array_map @ (succ_fn '* (code Nat '* a12))) ==> Sm (Array Nat (idx 2)).
Proof. by_runAr. Qed.
