(** * Step 82, stage 6, part 2: propositional logic at [fun_ontology].

    Propositions denote types:
      [[P_i]] = Atom i     [[top]] = Lf       [[bot]] = Empty
      [[p /\ q]] = [[p]] * [[q]]   [[p \/ q]] = Sum[[[p]],[[q]]]   [[p -> q]] = Fun [[p]] [[q]].
    The axiom programs are lambda programs built from [lam] and the
    constructors [mk_fun] and [mk_sum], which carry the codes of their
    types; [Lf] proves [top] and [absurd] proves [bot -> p].  Derivations
    are those of a Hilbert system with modus ponens, interpreted as
    application.

    Consistency is by realizability: each axiom program realizes its
    scheme and modus ponens preserves realizing, so every derivable
    proposition has an expression whose value realizes it; and nothing
    realizes [bot] or an atom. *)

From Stdlib Require Import String List Bool Lia Arith.
Import ListNotations.
From BigStep Require Import tree typing soundness rows identifiers booleans functions updates data_types lists sums department lists_rt queries self_typing paper_ontology fun_ontology.
Open Scope string_scope.
Set Default Proof Using "Type".

Local Opaque equal decode_p get_l get_r get_s get_par is_concrete isK.
Local Notation FO := fun_ontology.

Inductive form : Type :=
| Atm : nat -> form
| Top : form
| Bot : form
| And : form -> form -> form
| Or : form -> form -> form
| Imp : form -> form -> form.

Fixpoint denote (p : form) : Combination :=
  match p with
  | Atm i => Atom i
  | Top => Lf
  | Bot => Empty
  | And p q => denote p '* denote q
  | Or p q => Sum (denote p) (denote q)
  | Imp p q => Fun (denote p) (denote q)
  end.

(** ** The axiom programs *)

Definition axK_body (A B : Combination) : Combination := Eval cbn -[mk_fun] in to_tree
  (star "a" (op (mk_fun B A) @@ (Val 'K @@ Ref "a"))).
Definition ax_K (A B : Combination) : Combination := lam (axK_body A B) A (Fun B A).

Definition axS_body (A B C : Combination) : Combination := Eval cbn -[mk_fun Fun] in to_tree
  (star "f" (op (mk_fun (Fun A B) (Fun A C)) @@
     star "g" (op (mk_fun A C) @@ star "x" (Ref "f" @@ Ref "x" @@ (Ref "g" @@ Ref "x"))))).
Definition ax_S (A B C : Combination) : Combination :=
  lam (axS_body A B C) (Fun A (Fun B C)) (Fun (Fun A B) (Fun A C)).

Definition axpair_body (A B : Combination) : Combination := Eval cbn -[mk_fun] in to_tree
  (star "a" (op (mk_fun B (A '* B)) @@ star "b" (Ref "a" ''* Ref "b"))).
Definition ax_pair (A B : Combination) : Combination := lam (axpair_body A B) A (Fun B (A '* B)).
Definition ax_fst (A B : Combination) : Combination := lam 'fst (A '* B) A.
Definition ax_snd (A B : Combination) : Combination := lam 'snd (A '* B) B.

Definition axleft_body (A B : Combination) : Combination := Eval cbn -[mk_sum] in to_tree
  (star "a" (op (mk_sum A B) @@ (Val (Sm (Sm 'fst)) @@ (Val 'K @@ Ref "a")))).
Definition ax_left (A B : Combination) : Combination := lam (axleft_body A B) A (Sum A B).
Definition axright_body (A B : Combination) : Combination := Eval cbn -[mk_sum] in to_tree
  (star "b" (op (mk_sum A B) @@ (Val (Sm (Sm 'snd)) @@ (Val 'K @@ Ref "b")))).
Definition ax_right (A B : Combination) : Combination := lam (axright_body A B) B (Sum A B).

Definition axcase_body (A B C : Combination) : Combination := Eval cbn -[mk_fun Fun Sum] in to_tree
  (star "f" (op (mk_fun (Fun B C) (Fun (Sum A B) C)) @@
     star "g" (op (mk_fun (Sum A B) C) @@ star "s" (Ref "s" @@ (Ref "f" ''* Ref "g"))))).
Definition ax_case (A B C : Combination) : Combination :=
  lam (axcase_body A B C) (Fun A C) (Fun (Fun B C) (Fun (Sum A B) C)).

(** ** Derivations *)

Inductive derivable : form -> Prop :=
| d_K : forall p q, derivable (Imp p (Imp q p))
| d_S : forall p q r, derivable (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r)))
| d_pair : forall p q, derivable (Imp p (Imp q (And p q)))
| d_fst : forall p q, derivable (Imp (And p q) p)
| d_snd : forall p q, derivable (Imp (And p q) q)
| d_left : forall p q, derivable (Imp p (Or p q))
| d_right : forall p q, derivable (Imp q (Or p q))
| d_case : forall p q r, derivable (Imp (Imp p r) (Imp (Imp q r) (Imp (Or p q) r)))
| d_top : derivable Top
| d_absurd : forall p, derivable (Imp Bot p)
| d_mp : forall p q, derivable (Imp p q) -> derivable p -> derivable q.

(** ** Realizability *)

Fixpoint realizes (p : form) (v : Combination) : Prop :=
  match p with
  | Atm _ => False
  | Bot => False
  | Top => v = Lf
  | And p q => exists a b, v = a '* b /\ realizes p a /\ realizes q b
  | Or p q => (exists a, v = inleft (denote p) (denote q) a /\ realizes p a) \/
              (exists b, v = inright (denote p) (denote q) b /\ realizes q b)
  | Imp p q => forall u, realizes p u -> exists w, v @ u ==> w /\ realizes q w
  end.

Lemma mk_fun_eval : forall A B c, mk_fun A B @ c ==> lam c A B.
Proof. intros; apply tagged_eval, tagger_eval. Qed.
Lemma lam_eval : forall f A B u v, f @ u ==> v -> lam f A B @ u ==> v.
Proof. intros; apply tagged_eval; assumption. Qed.

Local Opaque mk_fun mk_sum Fun Sum.
Ltac evf := split2; evaluate2; repeat first [eassumption | apply mk_fun_eval | apply mk_sum_eval | progress evaluate2].

Theorem realizes_K : forall p q, realizes (Imp p (Imp q p)) (ax_K (denote p) (denote q)).
Proof.
  intros p q u Hu; eexists; split.
  - apply lam_eval; unfold axK_body; evf.
  - intros u' _; exists u; split; [apply lam_eval; evaluate|exact Hu].
Qed.

Theorem realizes_S : forall p q r,
  realizes (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))) (ax_S (denote p) (denote q) (denote r)).
Proof.
  intros p q r f Hf; eexists; split; [apply lam_eval; unfold axS_body; evf|].
  intros g Hg; eexists; split; [apply lam_eval; evf|].
  intros x Hx.
  destruct (Hf x Hx) as [h [Hh Hhr]]; destruct (Hg x Hx) as [b [Hb Hbr]]; destruct (Hhr b Hbr) as [c [Hc Hcr]].
  exists c; split; [apply lam_eval; evf|exact Hcr].
Qed.

Theorem realizes_pair : forall p q, realizes (Imp p (Imp q (And p q))) (ax_pair (denote p) (denote q)).
Proof.
  intros p q a Ha; eexists; split; [apply lam_eval; unfold axpair_body; evf|].
  intros b Hb; exists (a '* b); split; [apply lam_eval; evf|exists a, b; auto].
Qed.

Theorem realizes_fst : forall p q, realizes (Imp (And p q) p) (ax_fst (denote p) (denote q)).
Proof. intros p q v [a [b [-> [Ha _]]]]; exists a; split; [apply lam_eval, fst_pair|exact Ha]. Qed.
Theorem realizes_snd : forall p q, realizes (Imp (And p q) q) (ax_snd (denote p) (denote q)).
Proof. intros p q v [a [b [-> [_ Hb]]]]; exists b; split; [apply lam_eval, snd_pair|exact Hb]. Qed.

Theorem realizes_left : forall p q, realizes (Imp p (Or p q)) (ax_left (denote p) (denote q)).
Proof.
  intros p q a Ha; exists (inleft (denote p) (denote q) a); split; [apply lam_eval; unfold axleft_body, inleft; evf|].
  left; exists a; auto.
Qed.
Theorem realizes_right : forall p q, realizes (Imp q (Or p q)) (ax_right (denote p) (denote q)).
Proof.
  intros p q b Hb; exists (inright (denote p) (denote q) b); split; [apply lam_eval; unfold axright_body, inright; evf|].
  right; exists b; auto.
Qed.

Theorem realizes_case : forall p q r,
  realizes (Imp (Imp p r) (Imp (Imp q r) (Imp (Or p q) r))) (ax_case (denote p) (denote q) (denote r)).
Proof.
  intros p q r f Hf; eexists; split; [apply lam_eval; unfold axcase_body; evf|].
  intros g Hg; eexists; split; [apply lam_eval; evf|].
  intros s [[a [-> Ha]]|[b [-> Hb]]].
  - destruct (Hf a Ha) as [c [Hc Hcr]]; exists c; split; [|exact Hcr].
    apply lam_eval; unfold inleft; evf.
  - destruct (Hg b Hb) as [c [Hc Hcr]]; exists c; split; [|exact Hcr].
    apply lam_eval; unfold inright; evf.
Qed.

Theorem realizes_top : realizes Top Lf.
Proof. reflexivity. Qed.
Theorem realizes_exfalso : forall p, realizes (Imp Bot p) (absurd (denote p)).
Proof. intros p u []. Qed.
Theorem realizes_mp : forall p q f a, realizes (Imp p q) f -> realizes p a -> exists w, f @ a ==> w /\ realizes q w.
Proof. intros p q f a Hf Ha; exact (Hf a Ha). Qed.

(** The program of an axiom instance; modus ponens is application. *)
Theorem derivation_realizes : forall p, derivable p -> exists e v, e ==> v /\ realizes p v.
Proof.
  intros p D; induction D.
  - exists (Sm (ax_K (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_K].
  - exists (Sm (ax_S (denote p) (denote q) (denote r))); eexists; split; [apply eval_val|apply realizes_S].
  - exists (Sm (ax_pair (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_pair].
  - exists (Sm (ax_fst (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_fst].
  - exists (Sm (ax_snd (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_snd].
  - exists (Sm (ax_left (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_left].
  - exists (Sm (ax_right (denote p) (denote q))); eexists; split; [apply eval_val|apply realizes_right].
  - exists (Sm (ax_case (denote p) (denote q) (denote r))); eexists; split; [apply eval_val|apply realizes_case].
  - exists (Sm Lf), Lf; split; [apply eval_val|apply realizes_top].
  - exists (Sm (absurd (denote p))); eexists; split; [apply eval_val|apply realizes_exfalso].
  - destruct IHD1 as [e1 [f [He1 Hf]]]; destruct IHD2 as [e2 [a [He2 Ha]]].
    destruct (Hf a Ha) as [w [Hw Hwr]].
    exists (Fk e1 e2), w; split; [eapply eval_pair; eassumption|exact Hwr].
Qed.

Theorem no_realizer_atom_bot : forall v, ~ realizes Bot v /\ forall i, ~ realizes (Atm i) v.
Proof. intros v; split; [intros []|intros i []]. Qed.

Theorem bot_not_derivable : ~ derivable Bot.
Proof. intros D; destruct (derivation_realizes Bot D) as [e [v [_ []]]]. Qed.

Theorem atom_not_derivable : forall i, ~ derivable (Atm i).
Proof. intros i D; destruct (derivation_realizes (Atm i) D) as [e [v [_ []]]]. Qed.
