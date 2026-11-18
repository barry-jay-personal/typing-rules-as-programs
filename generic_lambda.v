(** * Step 82, stage 6, part 4: polymorphic lambda programs that take codes at run time.

      id_F @ c          = gen_lam @ (c * (c * I))                      (= lam[I, A, A] at c = code A)
      K_F @ cA @ cB     = gen_lam @ (cA * (code[B -> A] * k))            (= lam[k, A, B -> A])
        where code[B -> A] is built from cB and cA, and
              k @ a     = gen_lam @ (cB * (cA * K1 a))                  (= lam[K1 a, B, A])

    For all types whose names are concrete,
      id_F # code[A] ==> Sm (A -> A)           (id_F_polymorphic)
      K_F # code[A] # code[B] ==> Sm (A -> (B -> A))  (K_F_polymorphic)
    the roles of the paper's id_polymorphic and K_polymorphic. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists sums glam department lists_rt queries self_typing paper_ontology fun_ontology logic_paper logic_typing.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation FO := fun_ontology.

Definition GenLam : Combination := 'label[gen_lam_nm].

Theorem infer_gen_lam : infer FO @ gen_lam ==> Sm GenLam.
Proof.
  eapply infer_tag; [reflexivity|apply concrete_is_self_typed; vm_compute; reflexivity|apply FO_glam|].
  eapply app2; [apply guard_of_pair|]. pose proof (guard1_spec glam_carrier glam_carrier) as G.
  destruct combination_eq_dec; [exact G|contradiction].
Qed.

Theorem type_app_gen_lam : forall A B F, names_concrete A -> names_concrete B -> tp FO @ F @r A ==> Sm B ->
  tp FO @ GenLam @r (code A '* (code B '* F)) ==> Sm (Fun A B).
Proof.
  intros A B F HA HB H; eapply tp_abs; [apply FO_glam|]. apply elim_of_fwd, glm_fwd; assumption.
Qed.

Corollary type_app_gen_lam_label : forall A n F, names_concrete A -> names_concrete ('label[n]) ->
  tp FO @ F @r A ==> Sm ('label[n]) ->
  tp FO @ GenLam @r (code A '* (Fk (Fk Lf Lf) n '* F)) ==> Sm (Fun A ('label[n])).
Proof. intros A n F HA Hn H; exact (type_app_gen_lam A ('label[n]) F HA Hn H). Qed.

(** The code [code[B -> A]] built from the codes of [B] and [A]. *)
Definition fun_code_t (cB cA : Term) : Term :=
  Val Lf @@ (Val Lf @@ Val Lf @@ Val Lf) @@ (Val Lf @@ Val fun_nm @@ (Val Lf @@ cB @@ cA)).
Lemma code_Fun : forall A B, code (Fun B A) = Fk (Fk Lf Lf) (Fk fun_nm (Fk (code B) (code A))).
Proof. reflexivity. Qed.

Definition id_F : Combination := Eval cbn -[gen_lam] in to_tree
  (star "c" (op gen_lam @@ (Ref "c" ''* (Ref "c" ''* Val 'I)))).
Definition K_F : Combination := Eval cbn -[gen_lam fun_nm] in to_tree
  (star "cA" (star "cB" (op gen_lam @@
     (Ref "cA" ''* (fun_code_t (Ref "cB") (Ref "cA") ''*
        star "a" (op gen_lam @@ (Ref "cB" ''* (Ref "cA" ''* (Val 'K @@ Ref "a"))))))))).

Ltac buildG := first
  [ eassumption
  | apply infer_leaf
  | (apply infer_stem; buildG)
  | apply infer_gen_lam
  | (apply concrete_is_self_typed; vm_compute; reflexivity)
  | (eapply infer_fork; [reflexivity|buildG|buildG|first [reflexivity|lp_false]]) ].

Definition IdFT : Combination := Eval vm_compute in
  match runp 40 (infer FO @ id_F) with Some (Sm T) => T | _ => Lf end.
Definition KFT : Combination := Eval vm_compute in
  match runp 40 (infer FO @ K_F) with Some (Sm T) => T | _ => Lf end.

Theorem infer_id_F : infer FO @ id_F ==> Sm IdFT. Proof. apply (runp_sound 40); vm_done. Qed.
Theorem infer_K_F : infer FO @ K_F ==> Sm KFT. Proof. apply (runp_sound 40); vm_done. Qed.

Ltac tpsG := repeat first
  [ eassumption
  | (apply type_app_gen_lam; [assumption|assumption|])
  | (apply type_app_Fun; assumption)
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd
  | apply app_I ].

Section Poly.
Variables A B : Combination.
Hypothesis HA : names_concrete A.
Hypothesis HB : names_concrete B.

Theorem id_F_polymorphic : tp FO @ IdFT @r code A ==> Sm (Fun A A).
Proof using HA. unfold IdFT; cbn. tpsG. Qed.

Theorem K_F_polymorphic : exists T, tp FO @ KFT @r code A ==> Sm T /\ tp FO @ T @r code B ==> Sm (Fun A (Fun B A)).
Proof using HA HB.
  pose proof (names_concrete_Fun B A HB HA) as HBA.
  eexists; split; unfold KFT; [tpsG|].
  tpsG. apply (type_app_gen_lam_label A); [exact HA|exact HBA|]. tpsG.
Qed.
End Poly.


(** Examples, by computation. *)
Example id_F_Nat_eval : id_F @ code Nat @r zero ==> zero. Proof. apply (runp_sound 40); vm_done. Qed.
Example id_F_Nat_typed : infer_expression FO @ (id_F @ code Nat) ==> Sm (Fun Nat Nat). Proof. apply (runp_sound 40); vm_done. Qed.
Example K_F_eval : K_F @ code Nat @r code Bool @r zero @r tt ==> zero. Proof. apply (runp_sound 40); vm_done. Qed.
Example K_F_typed : infer_expression FO @ (K_F @ code Nat @r code Bool) ==> Sm (Fun Nat (Fun Bool Nat)). Proof. apply (runp_sound 40); vm_done. Qed.
Example K_F_applied : infer_expression FO @ (K_F @ code Nat @r code Bool @r zero @r tt) ==> Sm Nat. Proof. apply (runp_sound 40); vm_done. Qed.
Example K_F_refuses : infer_expression FO @ (K_F @ code Nat @r code Bool @r tt) ==> Lf. Proof. apply (runp_sound 40); vm_done. Qed.
