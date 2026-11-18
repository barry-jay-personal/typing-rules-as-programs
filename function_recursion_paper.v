(** * Step 82, stage 6, part 4: recursive functions as updates of a function type.

      fu_body[U,V,f] @ r      = special_type[U -> V, act_r, identity_update]     (built by mk_update)
        where act_r @ w       = f @ lam[wait[r, w], U, V]                       (built by mk_fun[U,V])
      fu_update[U,V,f]        = fix_update[fu_body[U,V,f]]
      fix_function_upd[U,V,f,g0] = lam[wait[fu_update[U,V,f], g0], U, V]

    If the ontology supports updates and function types (here
    [fun_ontology]), [f : (U -> V) -> (U -> V)] and [g0 : U -> V], then
    [fix_function_upd[U,V,f,g0] : U -> V] ([infer_fix_function_upd]). *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists sums glam department lists_rt queries self_typing paper_ontology fun_ontology logic_paper logic_typing size_queries poly.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation FO := fun_ontology.

Definition fu_body (U V f : Combination) : Combination := Eval cbn -[mk_update mk_fun code identity_update Fun] in to_tree
  (star "r" (op mk_update @@ w3 (Val (code (Fun U V)))
     (star "w" (Val f @@ (op (mk_fun U V) @@ ''wait[Ref "r", Ref "w"]))) (Val identity_update))).
Definition fu_update (U V f : Combination) : Combination := fix_update (fu_body U V f).
Definition fix_function_upd (U V f g0 : Combination) : Combination := lam ('wait[fu_update U V f, g0]) U V.

Lemma FO_identity_update : infer FO @ identity_update ==> Sm Update.
Proof.
  eapply infer_tag; [reflexivity|apply concrete_is_self_typed; reflexivity|apply FO_update|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard. apply or_g_l.
  pose proof (guard1_spec 'I 'I) as G; destruct combination_eq_dec; [exact G|contradiction].
Qed.

Lemma FO_type_app_Update : forall X, tp FO @ Update @r X ==> Sm X.
Proof. apply Update_app_g, FO_update. Qed.

Ltac buildU := first
  [ eassumption
  | apply infer_leaf
  | (apply infer_stem; buildU)
  | (apply infer_mk_fun; assumption)
  | apply (mk_update_typed_g FO FO_mku)
  | apply FO_identity_update
  | (apply code_self_typed; assumption)
  | (apply concrete_is_self_typed; vm_compute; reflexivity)
  | (eapply infer_fork; [reflexivity|buildU|buildU|first [reflexivity|lp_false]]) ].

Ltac tpsU := repeat first
  [ eassumption
  | (apply type_app_mk_fun; [assumption|assumption|])
  | (apply type_app_Fun; assumption)
  | apply FO_type_app_Update
  | (apply (mku_app FO FO_mku); unfold upd_guard;
       eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|];
       eapply or_g_r; [apply gch_miss; discriminate|reflexivity|]; apply or_g_l;
       eapply gsp_hit_code; [apply decode_code|])
  | apply tp_K1_fwd
  | (eapply tp_S2_fwd; [first [reflexivity|lo_none]| | |])
  | (apply tp_stem; first [reflexivity|lp_false])
  | apply tp_leaf_fwd
  | apply app_I ].

Section FixFun.
Variables U V f g0 : Combination.
Hypothesis HU : names_concrete U.
Hypothesis HV : names_concrete V.
Hypothesis Hf : infer FO @ f ==> Sm (Fun (Fun U V) (Fun U V)).
Hypothesis Hg : infer FO @ g0 ==> Sm (Fun U V).
Let HUV := names_concrete_Fun U V HU HV.

Theorem infer_fu_update : infer FO @ fu_update U V f ==> Sm Update.
Proof using HU HV Hf.
  evar (B : Combination).
  assert (Hb : infer FO @ fu_body U V f ==> Sm B) by (unfold fu_body, B; buildU).
  assert (HB : tp FO @ B @r Update ==> Sm Update) by (unfold B; tpsU).
  unfold fu_update, fix_update.
  assert (Hc : infer FO @ Z (fu_body U V f 'C 'tagger[update_nm]) ==> Sm (Z (B 'C 'tagger[update_nm])))
    by (unfold Z, self_apply, wait1; buildU).
  eapply infer_tag; [reflexivity|exact Hc|apply FO_update|].
  eapply app2; [apply guard_of_pair|]. unfold upd_guard.
  eapply or_g_r; [apply guard1_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gch_miss; discriminate|reflexivity|].
  eapply or_g_r; [apply gsp_miss_Z|reflexivity|apply gfx_hit; exact HB].
Qed.

Theorem infer_fix_function_upd : infer FO @ fix_function_upd U V f g0 ==> Sm (Fun U V).
Proof using HU HV Hf Hg.
  pose proof infer_fu_update as Hu.
  unfold fix_function_upd; eapply infer_lam; [exact HU|exact HV| |].
  - buildU.
  - tpsU.
Qed.
End FixFun.
