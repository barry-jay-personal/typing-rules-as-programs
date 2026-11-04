(** * Typing rules as programs (paper: Typing Rules as Programs).

    The typing program and its properties, in build order:
    - clause notation for writing the typing programs;
    - the hardwired auxiliary programs;
    - type application [type_app];
    - inference of value types and of expression types;
    - the paper's type-application figure, type application clause by clause. *)


(** * Clause notation for the typing programs

    The typing programs of the paper are first-match case programs.  This
    module supplies a small surface syntax, the custom entry [clause],
    written between [<{] and [}>], in which those programs can be written
    clause by clause.  Every construct is a notation: it expands to the
    existing second-level [Term] constructions ([star], [tcase], [extend2],
    [''onStem1], [''onFork1], [success2], [''wait], [''triage], ...), so a
    definition written in clause syntax compiles to exactly the same tree as
    before.  No new combinator is introduced.

    Variables of the clause language are string literals: the coercion
    [Ref] turns ["x"] into a variable, and the coercion [Val] turns a closed
    combination (such as a named precompiled component) into a quoted
    value.  Term-valued Coq variables may be used directly.

    Summary (in the order the paper uses them):
    - [fun "x" "y" => e]                      : [star "x" (star "y" e)]
    - [e1 @ e2]                               : application [e1 @@ e2]
    - [(Sm e)], [(Fk e1 e2)]                  : stem and fork construction
    - ['K1 e], ['S2[g,f]], ['triage[a,b,c]], ['tagged[e,n]], ['label[n]],
      ['name_test[n]], ['wait[m,n]], ['wait2[m,n,x]], [g 'C f]
                                              : the [''] constructions
    - [let Sm "x" = e1 in e2]                 : [''onStem1 (\"x" e2) @@ e1]
      (sequential: [e1] is evaluated, a stem continues, anything else
      gives [Lf])
      (nested lets [let Sm "x" = e1 in let Sm "y" = e2 in e3] compile so
      that [e2], when it does not mention "x", is evaluated together with
      [e1]: [star "x"] lifts it out as [K1 e2])
    - [fun Sm "x" , Sm "y" => e]               : [success2] with continuation
                                                [e] compiled in place, as a
                                                function of the two results
    - [if c then a else b]                    : [c @@ a @@ b], [c] a selector
    - [shape | Lf => a | Sm "x" => b | Fk "y" "z" => c end]
                                              : [''triage[a, \"x" b, \"y" \"z" c]]
    - [shape | Lf => a | Sm "x" => b | 'K1 "y" => c
             | 'S2["g","f"] => d | 'triage["f0","f1","f2"] => e end]
                                              : curried dispatch on a function type,
                                                the fork split by its left branch
                                                into K1 / S2 / triage; each branch
                                                is a function of the argument type
    - [function | p => s end]                 : [tcase p s] (one pattern clause)
    - [first_match | c1 | ... | cn | otherwise => r end]
                                              : [extend2 c1 (... (extend2 cn r))]
    - [match u with | 'tagged["c","n"] => b | _ => a end]
                                              : guard "u is tagged[c,n]" (by get_tagged)
    - [match u with | 'tagged => Lf | _ => f @ a @ b end]
                                              : reject a tagged u
    - [tag_case | 'tagged => b | _ => a end]  : the same test, point-free

    Because [star] eta-contracts ([\"x" (t @@ "x") = t] when ["x"] is not
    free in [t]), a clause that names its arguments and passes them to a
    precompiled component compiles to the bare component.  This is how the
    composite programs keep their named, separately verified components
    while still listing the clauses with their arguments.

    The notations live in the module [ClauseNotation], so that their
    keywords ([first_match], [otherwise], [shape], [function], [tag_case]) are
    active only in files that import it. *)

From TreeTyping Require Import tree.
From Stdlib Require Import String.
Open Scope string_scope.

Declare Custom Entry clause.
(** [otherwise] must be a keyword (not an atom) where a clause could also
    start; the dummy entry [clause_keyword] makes it one. *)
Declare Custom Entry clause_keyword.

Module ClauseNotation.

Coercion Ref : string >-> Term.
Coercion Val : Combination >-> Term.

Notation "'otherwise'" := tt (in custom clause_keyword at level 0).

Notation "<{ e }>" := e (e custom clause at level 200).

(** Atoms. *)
Notation "( e )" := e (in custom clause at level 0, e custom clause at level 200).
Notation "{ c }" := c (in custom clause at level 0, c constr at level 200).
Notation "x" := x (in custom clause at level 0, x constr at level 0).

(** Tree constructions. *)
Notation "( 'Sm' x )" := (Val Lf @@ x)
  (in custom clause at level 0, x custom clause at level 9).
Notation "( 'Fk' x y )" := (Val Lf @@ x @@ y)
  (in custom clause at level 0, x custom clause at level 9, y custom clause at level 9).
Notation "'K1 x" := (''K1 x)
  (in custom clause at level 9, x custom clause at level 9).
Notation "'S2 [ g , f ]" := (''S2 [ g, f ])
  (in custom clause at level 0, g custom clause at level 200, f custom clause at level 200).
Notation "'triage [ a , b , c ]" := (''triage [ a, b, c ])
  (in custom clause at level 0, a custom clause at level 200, b custom clause at level 200,
   c custom clause at level 200).
Notation "'tagged [ e , n ]" := (''tagged [ e, n ])
  (in custom clause at level 0, e custom clause at level 200, n custom clause at level 200).
Notation "'label [ n ]" := (''S2 [ ''K, ''K1 n ])
  (in custom clause at level 0, n custom clause at level 200).
Notation "'wait [ m , n ]" := (''wait [ m, n ])
  (in custom clause at level 0, m custom clause at level 200, n custom clause at level 200).
Notation "'wait2 [ m , n , x ]" := (''wait2 [ m, n, x ])
  (in custom clause at level 0, m custom clause at level 200, n custom clause at level 200,
   x custom clause at level 200).
Notation "'name_test [ n ]" := ((''wait [ Val equal, Val Lf @@ n ]) ''C Val get_tagname)
  (in custom clause at level 0, n custom clause at level 200).
Notation "'tagged_by [ n ]" := (''K1 (Val Lf ''C ((''wait [ Val equal, Val Lf @@ n ]) ''C Val get_tagname)))
  (in custom clause at level 0, n custom clause at level 200).
Notation "g 'C f" := (g ''C f)
  (in custom clause at level 9, f custom clause at level 9).

(** Application. *)
Notation "x @ y" := (App x y)
  (in custom clause at level 10, left associativity).

(** Abstraction. *)
Notation "'fun' x .. y => e" := (star x .. (star y e) ..)
  (in custom clause at level 200, x constr at level 0, y constr at level 0,
   e custom clause at level 200).

(** Success binding. *)
Notation "'let' 'Sm' x = e1 'in' e2" := (''onStem1 (star x e2) @@ e1)
  (in custom clause at level 200, x constr at level 0, e1 custom clause at level 100,
   e2 custom clause at level 200).

(** A two-argument function of two results that proceeds only when both
    are stems: [success2] with its continuation compiled in place. *)
Notation "'fun' 'Sm' x , 'Sm' y => e" :=
  (''triage [ Val ('K1 Lf),
              star x (''triage [ Val Lf, star y e, Val ('K1 ('K1 Lf)) ]),
              Val ('K1 ('K1 ('K1 Lf))) ])
  (in custom clause at level 200, x constr at level 0, y constr at level 0,
   e custom clause at level 200).

(** Selection by a selector [K] / [K1 I]. *)
Notation "'if' c 'then' a 'else' b" := (c @@ a @@ b)
  (in custom clause at level 200, c custom clause at level 100,
   a custom clause at level 100, b custom clause at level 200).

(** Dispatch on the shape of the argument (raw triage). *)
Notation "'shape' | 'Lf' => a | 'Sm' x => b | 'Fk' y z => c 'end'" :=
  (''triage [ a, star x b, star y (star z c) ])
  (in custom clause at level 0, a custom clause at level 200,
   b custom clause at level 200, c custom clause at level 200,
   x constr at level 0, y constr at level 0, z constr at level 0).
Notation "'shape' | 'Lf' => a | 'Sm' => b | 'Fk' => c 'end'" :=
  (''triage [ a, b, c ])
  (in custom clause at level 0, a custom clause at level 200,
   b custom clause at level 200, c custom clause at level 200).
(** Curried dispatch on a function type [F]: leaf, stem, and the three
    kinds of fork ([K1], [S2], [triage]), split by the fork's left branch.
    Each branch is the function of the argument type [U] that the clause
    returns, typically written [fun "U" => ...]. *)
Notation "'shape' | 'Lf' => a | 'Sm' x => b | 'K1 y => c | 'S2 [ g , f ] => d | 'triage [ f0 , f1 , f2 ] => e 'end'" :=
  (''triage [ a, star x b,
     ''triage [ star y c, star g (star f d), star f0 (star f1 (star f2 e)) ] ])
  (in custom clause at level 0, a custom clause at level 200,
   b custom clause at level 200, c custom clause at level 200,
   d custom clause at level 200, e custom clause at level 200,
   x constr at level 0, y constr at level 0, g constr at level 0, f constr at level 0,
   f0 constr at level 0, f1 constr at level 0, f2 constr at level 0).

(** One pattern clause: [Sm s] on a match, [Lf] otherwise. *)
Notation "'function' | p => s 'end'" := (tcase p s)
  (in custom clause at level 0, p custom clause at level 100,
   s custom clause at level 200).

(** First match: try each clause in order; the first [Sm v] gives [v]. *)
(* Spelled out for one to four clauses: a recursive notation cannot end
   with a clause introduced by its own separator. *)
Notation "'first_match' | c1 | 'otherwise' => r 'end'" :=
  (extend2 c1 r)
  (in custom clause at level 0, c1 custom clause at level 200,
   r custom clause at level 200).
Notation "'first_match' | c1 | c2 | 'otherwise' => r 'end'" :=
  (extend2 c1 (extend2 c2 r))
  (in custom clause at level 0, c1 custom clause at level 200,
   c2 custom clause at level 200, r custom clause at level 200).
Notation "'first_match' | c1 | c2 | c3 | 'otherwise' => r 'end'" :=
  (extend2 c1 (extend2 c2 (extend2 c3 r)))
  (in custom clause at level 0, c1 custom clause at level 200,
   c2 custom clause at level 200, c3 custom clause at level 200,
   r custom clause at level 200).
Notation "'first_match' | c1 | c2 | c3 | c4 | 'otherwise' => r 'end'" :=
  (extend2 c1 (extend2 c2 (extend2 c3 (extend2 c4 r))))
  (in custom clause at level 0, c1 custom clause at level 200,
   c2 custom clause at level 200, c3 custom clause at level 200,
   c4 custom clause at level 200, r custom clause at level 200).

(** Guards on the tag of a value, decided by [get_tagged] (which returns
    [Sm (Fk c n)] on [tagged[c,n]] and [Lf] otherwise). *)
Notation "'match' u 'with' | 'tagged [ c , n ] => b | '_' => a 'end'" :=
  (''triage [ a, ''onFork1 (star c (star n b)), Val ('K1 ('K1 Lf)) ]
     @@ (Val get_tagged @@ u))
  (in custom clause at level 0, u custom clause at level 9,
   c constr at level 0, n constr at level 0,
   b custom clause at level 200, a custom clause at level 200).
(* reject a tagged [u]; otherwise [f @ a @ b] *)
Notation "'match' u 'with' | 'tagged => 'Lf' | '_' => f @ a @ b 'end'" :=
  (''triage [ f, Val ('K1 ('K1 ('K1 Lf))), Val ('K1 ('K1 ('K1 ('K1 Lf)))) ]
     @@ (Val get_tagged @@ u) @@ a @@ b)
  (in custom clause at level 0, u custom clause at level 9,
   f custom clause at level 9, a custom clause at level 9, b custom clause at level 9).
(* the same test, point-free: a function of the value to be tested *)
Notation "'tag_case' | 'tagged => b | '_' => a 'end'" :=
  ((''triage [ a, ''K1 b, Val ('K1 ('K1 ('K1 Lf))) ]) ''C Val get_tagged)
  (in custom clause at level 0, a custom clause at level 200,
   b custom clause at level 200).

(** Combination-level first match, for programs stored with [extend]. *)
Notation "'first_match' | c1 | 'otherwise' => r 'end'" :=
  (extend c1 r)
  (at level 0, c1 at level 100, r at level 100).
Notation "'first_match' | c1 | c2 | 'otherwise' => r 'end'" :=
  (extend c1 (extend c2 r))
  (at level 0, c1 at level 100, c2 at level 100, r at level 100).
Notation "'first_match' | c1 | c2 | c3 | 'otherwise' => r 'end'" :=
  (extend c1 (extend c2 (extend c3 r)))
  (at level 0, c1 at level 100, c2 at level 100, c3 at level 100, r at level 100).

End ClauseNotation.


Unset Default Proof Using.

(** Auxiliary programs required by the type-application rules of the paper's type-application figure:
    the query-triage check, immediate-child reconstruction,
    function-introduction check and tag-name test. Function introduction
    requires recognition of arrow certificates; the abstract function
    constructors and their soundness proofs come later.

    Registered-wrapper lookup supplies the exact type predicate for
    conditionals; its operational definitions and lemmas also live here. *)
From TreeTyping Require Import tree.
Import ClauseNotation.
From Stdlib Require Import String Bool.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque equal.
Local Notation "'onFork1 f" := (Fk ('K1 ('K1 Lf)) f) (at level 10).

(** Every eliminator is a delay ['wait[e,X]] of a program [e] of the
    parameter [X], type application and the argument type.  [ignores e]
    is the eliminator program of a family whose elimination does not call
    type application: it discards the argument, as [K1] does. *)
Definition ignores (e : Combination) : Combination := 'K 'C e.

Lemma ignores_wait_eval : forall e X a U v,
  e @ X @r U ==> v -> 'wait[ignores e, X] @ a @r U ==> v.
Proof.
  intros e X a U v H.
  destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hv]]]]; inv_out Hu.
  eapply eval_appl; [apply wait_eval; unfold ignores; repeat first [eassumption | progress evaluate]|exact Hv].
Qed.

Lemma ignores_wait_inv : forall e X a U v,
  'wait[ignores e, X] @ a @r U ==> v -> e @ X @r U ==> v.
Proof.
  intros e X a U v H.
  destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hv]]]]; inv_out Hu.
  apply wait_eval_inv in Hw; unfold ignores in Hw; invert_eval.
  eapply eval_appl; eassumption.
Qed.

(** Query-triage recognition. *)
Definition query_nm : Combination := Sm Lf.

(** The Query family program: at the parameter [B] it yields the constant
    eliminator [K1 (Sm B)], so [query_eliminator B @ U ==> Sm B] for every
    [U].  The eliminator of [Query[B]] is the delay of this program at the
    parameter [B]. *)
Definition query_elim0 : Combination := 'S2['K1 'K, Lf].
Definition query_elim : Combination := ignores query_elim0.

Definition query_eliminator (B : Combination) : Combination :=
  'wait[query_elim, B].

Notation "'Query [ B ]" :=
  ('tagged[query_eliminator B, query_nm]) (at level 0).
Notation "''Query [ B ]" :=
  (''tagged[''wait[Val query_elim, B], Val query_nm]) (at level 0).

Lemma query_elim_eval : forall B, query_elim0 @ B ==> ('K1 (Sm B)).
Proof. intros; unfold query_elim0; evaluate. Qed.

Lemma query_eliminator_eval : forall B a U, query_eliminator B @ a @r U ==> Sm B.
Proof.
  intros; unfold query_eliminator, query_elim; apply ignores_wait_eval.
  eapply eval_appl; [apply query_elim_eval|evaluate].
Qed.

(** The query triage at element type [B]: one level of a query traversal,
    triage[B, Query[B], Query[Query[B]]]
    (query_one_level[B] # U = Sm B).  [''query_one_level] is its Term form. *)
Definition query_one_level (B : Combination) : Combination :=
  'triage[B, 'Query[B], 'Query['Query[B]]].
Notation "''query_one_level [ B ]" :=
  (''triage[B, ''Query[B], ''Query[''Query[B]]]) (at level 0).

(** Given the three fields of a triage and its immaterial argument type,
    certify the query shape by returning the triage itself.  [type_app]
    turns that certificate into the result [Sm F0]. *)
Definition query_handler_package :
  { t : Combination |
    to_tree
      (\"F0" (\"F1" (\"F2" (''K1
        (''wait[Val 'I, Val equal]
          @@ (Val ('tagger[query_nm]) @@ ''wait[Val query_elim, Ref "F0"])
          @@ Ref "F1"
          @@ (''wait[Val 'I, Val equal]
                @@ (Val ('tagger[query_nm]) @@ ''wait[Val query_elim, Ref "F1"])
                @@ Ref "F2"
                @@ (Val Lf @@
                      ''triage[Ref "F0", Ref "F1", Ref "F2"])
                @@ Val Lf)
          @@ Val Lf))))) = t }.
Proof.
  eexists.
  unfold star at 3; eqb_tac.
  unfold equal at 1; unfold Z.
  unfold star at 2; eqb_tac.
  unfold equal at 1; unfold Z.
  unfold star at 1; eqb_tac.
  unfold to_tree.
  replace ('wait [dup_z, equal_body 'C bz]) with equal by auto.
  reflexivity.
Defined.

Definition query_handler : Combination :=
  Eval cbn in proj1_sig query_handler_package.

Lemma query_handler_eval : forall F0 U,
  query_handler @ F0 @r ('Query[F0]) @r ('Query['Query[F0]]) @r U ==>
    Sm (query_one_level F0).
Proof.
  intros F0 U; unfold query_handler, query_one_level; cbn.
  repeat first
    [ eapply equal_eval
    | eapply equal1_eq
    | progress evaluate
    ].
Qed.


(** Immediate-child reconstruction:
    update_one_level[r] = triage[Lf, Lf o r, update_fork[r]] rebuilds a tree
    with [r] applied to each immediate child. *)
Definition update_nm : Combination := Sm (Sm Lf).
(** The Update eliminator stores the parameter [Lf]. Its program
    [update_elim] ignores the parameter and returns the argument
    type, so [update_eliminator @ U ==> Sm U]. *)
Definition update_elim0 : Combination := 'K1 Lf.
Definition update_elim : Combination := ignores update_elim0.
Definition update_eliminator : Combination := 'wait[update_elim, Lf].
Notation "'Update" := ('tagged[update_eliminator,update_nm]) (at level 0).

Lemma update_eliminator_eval : forall a U,
  update_eliminator @ a @r U ==> Sm U.
Proof.
  intros; unfold update_eliminator, update_elim; apply ignores_wait_eval.
  unfold update_elim0; evaluate.
Qed.

(** ** The IsNamed family

    The IsNamed test [is_named[n]] is the name test [name_test n]
    tagged at [is_named_nm].  The IsNamed family has parameter [N] (the name);
    its eliminator [tagged_by N = K1 (Lf 'C name_test N)] ignores its
    first argument and runs the name test on the argument type:
    [tagged_by N @ a @r U ==> Sm (name_test N @ U)].  Its type
    [IsNamed[N]] mentions no declarations. *)
Definition is_named_nm : Combination :=
  Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm (Sm Lf)))))))))))).
Definition tagged_by N : Combination := 'K1 (Lf 'C name_test N).
Definition IsNamed N : Combination := 'tagged[tagged_by N, is_named_nm].
Definition is_named n : Combination := 'tagged[name_test n, is_named_nm].

Lemma tagged_by_eval : forall N a U B,
  name_test N @ U ==> B -> tagged_by N @ a @r U ==> Sm B.
Proof.
  intros N a U B H; unfold tagged_by.
  repeat first [eassumption | progress evaluate].
Qed.
Lemma tagged_by_inv : forall N a U V,
  tagged_by N @ a @r U ==> Sm V -> name_test N @ U ==> V.
Proof.
  intros N a U V H.
  destruct (name_test_total N U) as [b Hb].
  pose proof (eval_deterministic _ _ H _ (tagged_by_eval N a _ _ Hb)) as HE.
  inversion HE; subst; exact Hb.
Qed.
Lemma is_named_eval : forall n u b,
  name_test n @ u ==> b -> is_named n @ u ==> b.
Proof. intros; unfold is_named; apply tagged_eval; assumption. Qed.

Definition update_fork r := Eval cbn in to_tree
  (star "x" (star "y"
    (Val Lf @@ (Val r @@ Ref "x") @@ (Val r @@ Ref "y")))).
Definition update_one_level r :=
  'triage[Lf, Lf 'C r, update_fork r].


(** ** Accessors

    Total programs that walk a fixed path into a tree, answering [Lf] when
    the tree has the wrong shape.  They recover the components of delays,
    declarations and Church pairs by programs. *)
Inductive dir : Set := dir_l | dir_r | dir_s.

Definition dir_prog d :=
  match d with
  | dir_l => 'triage[Lf, 'K1 Lf, 'K]
  | dir_r => 'triage[Lf, 'K1 Lf, 'K1 'I]
  | dir_s => 'triage[Lf, 'I, 'K1 ('K1 Lf)]
  end.

Definition dir_fn d t :=
  match d, t with
  | dir_l, Fk a _ => a
  | dir_r, Fk _ b => b
  | dir_s, Sm a => a
  | _, _ => Lf
  end.

Fixpoint path_prog (ds : list dir) :=
  match ds with
  | nil => 'I
  | cons d ds' => path_prog ds' 'C dir_prog d
  end.

Fixpoint path_fn (ds : list dir) t :=
  match ds with
  | nil => t
  | cons d ds' => path_fn ds' (dir_fn d t)
  end.

Lemma dir_eval : forall d t, dir_prog d @ t ==> dir_fn d t.
Proof. intros [] []; cbn; evaluate. Qed.

Lemma path_eval : forall ds t, path_prog ds @ t ==> path_fn ds t.
Proof.
  induction ds as [|d ds IH]; intro t; cbn [path_prog path_fn].
  - apply I_eval.
  - apply eval_c; eapply eval_arg_value; [apply dir_eval | apply IH].
Qed.


(** [path_arg] reaches the argument [X] of ['wait[E,X]] and the first
    component [A] of the Church pair [A '* B]; [path_pB] reaches [B]. *)
Definition path_arg := cons dir_l (cons dir_s (cons dir_r (cons dir_r nil))).
Definition path_pB := cons dir_r (cons dir_r nil).
Definition acc_arg := path_prog path_arg.
Definition acc_pB := path_prog path_pB.

Lemma acc_arg_eval : forall t, acc_arg @ t ==> path_fn path_arg t.
Proof. intros; apply path_eval. Qed.
Lemma acc_pB_eval : forall t, acc_pB @ t ==> path_fn path_pB t.
Proof. intros; apply path_eval. Qed.

(** [op c] hides the constant [c] behind an identity composition, so that
    abstraction does not inspect it. *)
Definition op (c : Combination) : Term := Val ('I 'C c).

(** Boolean values and the equality test on trees. *)
Definition bt (b : bool) := if b then 'K else 'KI.

(** The test for unary indices, as a program. *)
Fixpoint is_index n := match n with Lf => true | Sm k => is_index k | Fk _ _ => false end.
Definition index_check_body := Eval cbv in to_tree
  (star "self" (''triage[Val 'K, Ref "self", ''K1 (''K1 (Val 'KI))])).
Definition index_check := Z index_check_body.
Lemma index_check_eval : forall n, index_check @ n ==> bt (is_index n).
Proof.
  induction n as [|k IH|j _ k _]; unfold index_check; apply Z_unfold;
    unfold index_check_body; cbn [is_index]; evaluate.
Qed.

Definition ceqb p q := if combination_eq_dec p q then true else false.

Lemma ceqb_true : forall p q, ceqb p q = true <-> p = q.
Proof.
  intros p q; unfold ceqb; destruct (combination_eq_dec p q); split;
    intro; congruence.
Qed.

Lemma ceqb_refl : forall p, ceqb p p = true.
Proof. intro p; apply ceqb_true; reflexivity. Qed.

Lemma equal1_bt : forall p q, equal1 p @ q ==> bt (ceqb p q).
Proof.
  intros p q; unfold ceqb; destruct (combination_eq_dec p q) as [->|Hne];
    cbn [bt]; [apply equal1_eq | apply equal1_neq; exact Hne].
Qed.

Lemma ceqb_false : forall p q, p <> q -> ceqb p q = false.
Proof. intros p q H; unfold ceqb; destruct (combination_eq_dec p q); congruence. Qed.

(** The two outcomes of a comparison, with the matching value of
    [equal1 p @ q]. *)
Lemma equal1_bt_case : forall p q,
  (p = q /\ ceqb p q = true /\ equal1 p @ q ==> 'K) \/
  (p <> q /\ ceqb p q = false /\ equal1 p @ q ==> 'KI).
Proof.
  intros p q; destruct (combination_eq_dec p q) as [H|H].
  - left; subst; repeat split; [apply ceqb_refl|apply equal1_eq].
  - right; repeat split; [exact H|apply ceqb_false; exact H|apply equal1_neq; exact H].
Qed.

Local Ltac acc_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval | apply acc_arg_eval | apply acc_pB_eval ]
  end.
Local Ltac acc_eval :=
  first [ acc_atom | evaluate_expr_core acc_eval acc_head | idtac ]
with acc_head :=
  first [ acc_atom | evaluate_head_core acc_eval | idtac ].

(** ** The function family

    Function types form a family with the parameter [U '* V] (default
    tupling).  Its eliminator program [funty_elim] compares the domain
    [U] with the argument type and returns [Sm V] or [Lf]; the eliminator
    of [U --> V] is the delay of this program at [U '* V].  Only function
    introduction is hardwired (no declaration). *)
Definition funty_elim0 := Eval cbv -[equal] in to_tree
  (star "P" (star "X"
    (op equal @@ (Ref "P" @@ Val 'K) @@ Ref "X"
       @@ (Val Lf @@ (Ref "P" @@ Val 'KI)) @@ Val Lf))).
Definition funty_elim := ignores funty_elim0.

Lemma funty_elim_eval : forall U V X,
  funty_elim0 @ (U '* V) @r X ==> (if ceqb U X then Sm V else Lf).
Proof.
  intros U V X.
  assert ((U '* V) @ 'K ==> U) by evaluate.
  assert ((U '* V) @ 'KI ==> V) by evaluate.
  destruct (equal1_bt_case U X) as [[Hd [Hc He]]|[Hd [Hc He]]];
    rewrite Hc; unfold funty_elim0; acc_eval.
Qed.


(** Function introduction: build the arrow eliminator for direct functions,
    and recognise the arrow certificate on a recursive body. *)
Definition funty_eliminator2 (U V : Term) : Term :=
  ''wait[Val funty_elim, U ''* V].

(** The function nametag is the leaf. *)
Definition fun_nm : Combination := Lf.

Definition check_function_direct_package :
  { t : Combination |
    to_tree
      (''onStem1
        (''onFork1
          (star "F" (star "U"
            (Val Lf @@
              (star "type_app0"
                (''onStem1
                  (star "V"
                    (Val Lf @@ funty_eliminator2 (Ref "U") (Ref "V")))
                 @@ (Ref "type_app0" @@ Ref "F" @@ Ref "U")))))))
       ''C Val get_decorate) = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition check_function_direct : Combination :=
  Eval cbn in proj1_sig check_function_direct_package.

(** [get_funty] reads the parameter [U '* V] of a function type by
    position and compares nothing, so it does not establish that its
    argument is a function type.  A caller that needs this compares the
    argument with the type it rebuilds from the parameter. *)
Definition path_tag_body : list dir := dir_l :: dir_s :: dir_r :: List.nil.
Definition get_funty : Combination := path_prog (path_tag_body ++ path_arg)%list.

(** The run-time form of a function type, for use under a binder: the
    function tag is attached by [tagger[fun_nm]] when the program runs, so
    the compiled program contains no label.  (Under [star], [U] or [V] must
    mention a bound variable; a closed application would not compile.) *)
Definition funty_rt (U V : Term) : Term :=
  Val ('tagger[fun_nm]) @@ funty_eliminator2 U V.


(** The function retagger builds its label at run time. *)
Definition tagged_fun : Combination := 'tagger[fun_nm].

(** The recursive certificate is read and rebuilt: the parameter of the
    function type sits at a fixed path, and the fixed point built from it
    is compared with the carrier.  The outer function type takes its
    eliminator program from the inner one. *)
Definition path_rec : list dir :=
  (path_arg ++ path_tag_body ++ path_tag_body ++ path_tag_body ++ path_arg ++ path_arg ++ path_tag_body ++ path_arg)%list.
Definition acc_rec := path_prog path_rec.
Definition path_wait_prog : list dir := dir_l :: dir_s :: dir_l :: dir_s :: dir_r :: List.nil.
Definition acc_wait_prog := path_prog path_wait_prog.

Definition check_function_recursive : Combination :=
  Eval cbn -[equal acc_rec acc_wait_prog acc_arg acc_pB tagged_fun funty_elim] in to_tree
  (star "C"
    ((star "P"
      ((star "E"
        ((star "T" (op equal @@ Ref "C"
            @@ Z2 ((Val tagged_fun
                 @@ ''wait[Val acc_wait_prog @@ Ref "E", Ref "T" ''* Ref "T"]) ''C Val tagged_fun)
            @@ (Val Lf @@ ''K1 (Val Lf @@ Ref "E"))
            @@ Val Lf))
         @@ (Val tagged_fun @@ Ref "E")))
       @@ funty_eliminator2 (Val acc_arg @@ Ref "P") (Val acc_pB @@ Ref "P")))
     @@ (Val acc_rec @@ Ref "C"))).

(** Function introduction tries the direct certificate, then the
    recursive one. *)
Definition function_abstractor_core : Combination :=
  first_match
  | check_function_direct
  | check_function_recursive
  | otherwise => 'K1 ('K1 Lf)
  end.

(** Function type introduction takes type application first, so that
    [function_abstractor @ type_app] is a program waiting for the carrier type. *)
Definition function_abstractor := Eval cbn -[function_abstractor_core] in
  to_tree (star "a" (star "C" (Val function_abstractor_core @@ Ref "C" @@ Ref "a"))).

Lemma function_abstractor_eval : forall a C v,
  function_abstractor_core @ C @r a ==> v -> function_abstractor @ a @r C ==> v.
Proof.
  intros a C v H; destruct (eval_pair_inv _ _ _ H) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  unfold function_abstractor; repeat first [eassumption | progress evaluate].
Qed.

Lemma function_abstractor_partial : forall a,
  function_abstractor @ a ==> 'S2[function_abstractor_core, 'K1 a].
Proof. intros; unfold function_abstractor; evaluate. Qed.

Lemma function_abstractor_eval_inv : forall a C v,
  function_abstractor @ a @r C ==> v -> function_abstractor_core @ C @r a ==> v.
Proof. intros a C v H; unfold function_abstractor in H; invert_eval; eapply eval_appl; eassumption. Qed.

(** ** Declarations as programs

    [declarations @ N] answers the declaration at [N]: a single program,
    an abstractor, that maps a carrier type [C] to [Sm E], an eliminator,
    or to [Lf].  Type application applies it to [C].  The refusal is the
    abstractor that refuses every carrier, ['K1 Lf]. *)
Definition refusal := 'K1 ('K1 Lf).

Lemma declaration_apply : forall AI N R a C v,
  AI @ N ==> ('K1 R) -> R @ C ==> v -> AI @ N @r a @r C ==> v.
Proof. intros; repeat (eapply eval_appl; [eassumption || evaluate|]); try eassumption; evaluate. Qed.

Lemma declaration_apply_gen : forall AI N R a v,
  AI @ N ==> R -> R @ a ==> v -> AI @ N @r a ==> v.
Proof. intros; eapply eval_appl; eassumption. Qed.

Lemma declaration_K1_inv : forall AI N D a C v,
  AI @ N ==> ('K1 D) -> AI @ N @r a @r C ==> v -> D @ C ==> v.
Proof.
  intros AI N D a C v HD H.
  destruct (eval_pair_inv _ _ _ H) as [D' [c [HD' [Hc Hv]]]]; inv_out Hc.
  destruct (eval_pair_inv _ _ _ HD') as [R [c' [HR [Hc' Ha]]]]; inv_out Hc'.
  pose proof (eval_deterministic _ _ HR _ HD) as ->.
  pose proof (eval_deterministic _ _ Ha _ (eval_k _ _)) as ->; exact Hv.
Qed.

Lemma declaration_apply_inv : forall AI N a C v,
  AI @ N @r a @r C ==> v -> exists R D, AI @ N ==> R /\ R @ a ==> D /\ D @ C ==> v.
Proof.
  intros AI N a C v H; destruct (eval_pair_inv _ _ _ H) as [D [c [HD [Hc Hv]]]]; inv_out Hc.
  destruct (eval_pair_inv _ _ _ HD) as [R [c' [HR [Hc' Ha]]]]; inv_out Hc'.
  exists R, D; repeat split; assumption.
Qed.

(** Function types are one row of the declarations: at [fun_nm] they
    answer [function_abstractor], the abstractor that uses type application.
    [Decl] is declarations with this row; a statement about function types
    quantifies over it. *)
Record Decl := mkDecl
  { dtree :> Combination; functions_declared : dtree @ fun_nm ==> function_abstractor }.

Definition funty_eliminator (U V : Combination) : Combination :=
  'wait[funty_elim, U '* V].

Definition funty (U V : Combination) : Combination :=
  'tagged[funty_eliminator U V,fun_nm].

Notation "U --> V" := (funty U V) (at level 65).

Lemma check_function_direct_some_inv : forall C continuation,
  check_function_direct @ C ==> Sm continuation ->
  exists F U, C = 'decorate[F,U].
Proof.
  intros C continuation H; unfold check_function_direct in H; cbn in H.
  invert_eval; eauto.
  apply get_decorate_inv in H4; eauto.
Qed.

Lemma check_function_direct_eval_inv :
  forall type_app0 F U continuation E,
  check_function_direct @ 'decorate[F,U] ==> Sm continuation ->
  continuation @ type_app0 ==> Sm E ->
  exists V,
    type_app0 @ F @r U ==> Sm V /\
    E = funty_eliminator U V.
Proof.
  intros type_app0 F U continuation E H Happly.
  unfold check_function_direct in H; cbn in H.
  invert_eval; eauto.
  apply get_decorate_inv in H4; inversion H4; subst v5 v3.
  exists v4; split.
  - eapply eval_appl; eauto.
  - reflexivity.
Qed.

Lemma get_tagged_success_inv : forall T P,
  get_tagged @ T ==> Sm P ->
  exists E N, T = 'tagged[E,N] /\ P = Fk E N.
Proof.
  intros T P H.
  destruct (tagged_decide T) as [[E [N ->]] | Hnot].
  - exists E, N; split; [reflexivity |].
    pose proof (get_tagged_some E N) as Hsome.
    unify_evals; inversion H0; reflexivity.
  - destruct T as [| T | left right].
    + unfold get_tagged in H; inv_out H; invert_eval.
    + unfold get_tagged in H; inv_out H; invert_eval.
    + pose proof (get_tagged_fork_none left right Hnot) as Hnone.
      unify_evals; discriminate.
Qed.

Lemma funty_eliminator_app : forall U V a X,
  funty_eliminator U V @ a @r X ==> (if ceqb U X then Sm V else Lf).
Proof.
  intros; unfold funty_eliminator, funty_elim; apply ignores_wait_eval; apply funty_elim_eval.
Qed.

Lemma get_funty_some : forall U V, get_funty @ (U --> V) ==> (U '* V).
Proof. intros; exact (path_eval (path_tag_body ++ path_arg)%list _). Qed.

(** What is read from [X] when [V] is taken from [get_funty @ X]. *)
Lemma funty_cod_some : forall U V, acc_pB @ (U '* V) ==> V.
Proof. intros; exact (acc_pB_eval (U '* V)). Qed.

Lemma tagged_fun_is_retag : tagged_fun = retag.
Proof. unfold tagged_fun, retag, fun_nm; reflexivity. Qed.

Lemma tagged_fun_app : forall x, tagged_fun @ x ==> 'tagged[x,fun_nm].
Proof. intros; unfold tagged_fun; evaluate. Qed.

Lemma acc_wait_prog_wait : forall M N, acc_wait_prog @ 'wait[M,N] ==> M.
Proof. intros; exact (path_eval path_wait_prog _). Qed.

Definition rec_Z U V := Z (((U --> V) --> (U --> V)) 'C tagged_fun).
Definition rec_cert_fn C :=
  let P := path_fn path_rec C in
  let U := path_fn path_arg P in
  let V := path_fn path_pB P in
  if ceqb C (rec_Z U V) then Sm ('K1 (Sm (funty_eliminator U V))) else Lf.

Local Ltac rc_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval | apply tagged_fun_app | apply acc_wait_prog_wait ]
  end.
Local Ltac rc_eval :=
  first [ rc_atom | evaluate_expr_core rc_eval rc_head | idtac ]
with rc_head :=
  first [ rc_atom | evaluate_head_core rc_eval | idtac ].

Lemma check_function_recursive_eval : forall C,
  check_function_recursive @ C ==> rec_cert_fn C.
Proof.
  intros C; pose proof (path_eval path_rec C) as Ha; fold acc_rec in Ha.
  unfold rec_cert_fn; cbv zeta.
  set (P := path_fn path_rec C) in *.
  pose proof (acc_arg_eval P) as HU; pose proof (acc_pB_eval P) as HV.
  set (U := path_fn path_arg P) in *; set (V := path_fn path_pB P) in *.
  destruct (equal1_bt_case C (rec_Z U V)) as [[Hd [Hc He]]|[Hd [Hc He]]];
    rewrite Hc; unfold rec_Z, funty, funty_eliminator in *; unfold check_function_recursive;
    rc_eval.
Qed.

Lemma check_function_recursive_eval_inv :
  forall type_app0 C continuation E,
  check_function_recursive @ C ==> Sm continuation ->
  continuation @ type_app0 ==> Sm E ->
  exists U V,
    C = Z (((U --> V) --> (U --> V)) 'C tagged_fun) /\
    E = funty_eliminator U V.
Proof.
  intros type_app0 C continuation E H Happly.
  pose proof (eval_deterministic _ _ H _ (check_function_recursive_eval C)) as Heq.
  unfold rec_cert_fn in Heq; cbv zeta in Heq.
  destruct (ceqb C _) eqn:Hc; [|discriminate].
  apply ceqb_true in Hc; inversion Heq; subst continuation.
  eexists _, _; split; [exact Hc|]; inv_out Happly; reflexivity.
Qed.

Local Transparent function_abstractor_core.
Lemma function_abstractor_default_impossible :
  forall (C continuation A E : Combination),
  (('K1 ('K1 Lf)) @ C ==> continuation) ->
  (continuation @ A ==> Sm E) -> False.
Proof.
  intros C continuation A E Hdefault Happly.
  assert (Hcanonical : ('K1 ('K1 Lf)) @ C ==> ('K1 Lf)) by evaluate.
  assert (Heq : continuation = 'K1 Lf)
    by (eapply eval_deterministic; [exact Hdefault | exact Hcanonical]).
  subst continuation.
  assert (Hfail : ('K1 Lf) @ A ==> Lf) by evaluate.
  pose proof (eval_deterministic _ _ Happly _ Hfail) as Hbad.
  discriminate Hbad.
Qed.

Lemma check_function_recursive_never_fork : forall C left right,
  check_function_recursive @ C ==> Fk left right -> False.
Proof.
  intros C left right H.
  pose proof (eval_deterministic _ _ H _ (check_function_recursive_eval C)) as Heq.
  unfold rec_cert_fn in Heq; cbv zeta in Heq.
  destruct (ceqb _ _); discriminate.
Qed.

Lemma check_function_direct_never_fork : forall C left right,
  check_function_direct @ C ==> Fk left right -> False.
Proof.
  intros C left right H; unfold check_function_direct in H; cbn in H.
  invert_eval.
Qed.

Lemma function_abstractor_success_inv : forall C type_app0 E,
  function_abstractor_core @ C @r type_app0 ==> Sm E ->
  (exists F U V,
      C = 'decorate[F,U] /\
      type_app0 @ F @r U ==> Sm V /\
      E = funty_eliminator U V) \/
  (exists U V,
      C = Z (((U --> V) --> (U --> V)) 'C tagged_fun) /\
      E = funty_eliminator U V).
Proof.
  intros C type_app0 E H.
  assert (exists W,
      function_abstractor_core @ C ==> W /\ W @ type_app0 ==> Sm E)
    by (inv_out H; eauto).
  clear H; destruct H0 as [W [Hcheck Happly]].
  unfold function_abstractor_core in Hcheck.
  destruct (extend_inv _ _ _ _ Hcheck)
    as [[continuation [Hdirect ->]] |
        [[Hdirect_none Hfallback] |
         [left [right [Hdirect_fork ->]]]]]; clear Hcheck.
  - destruct (check_function_direct_some_inv C continuation Hdirect)
      as [F [U ->]].
    destruct (check_function_direct_eval_inv
      type_app0 F U continuation E Hdirect Happly)
      as [V [Htype ->]].
    left; exists F, U, V; auto.
  - destruct (extend_inv _ _ _ _ Hfallback)
      as [[continuation [Hrecursive ->]] |
          [[Hrecursive_none Hdefault] |
           [left [right [Hrecursive_fork ->]]]]]; clear Hfallback.
    + destruct (check_function_recursive_eval_inv
        type_app0 C continuation E Hrecursive Happly)
        as [U [V [-> ->]]].
      right; exists U, V; auto.
    + exfalso; eapply function_abstractor_default_impossible; eauto.
    + exfalso; eapply check_function_recursive_never_fork; eauto.
  - exfalso; eapply check_function_direct_never_fork; eauto.
Qed.


Local Opaque equal1.

Local Opaque function_abstractor_core.

(** Successful recognition of the recursive function certificate. *)
Local Transparent equal1 function_abstractor_core.
Lemma funty_eliminator_eval : forall U V a,
  funty_eliminator U V @ a @r U ==> Sm V.
Proof.
  intros U V a; pose proof (funty_eliminator_app U V a U) as H.
  rewrite ceqb_refl in H; exact H.
Qed.


Lemma check_function_direct_recursive_none : forall U V,
  check_function_direct @
    Z (((U --> V) --> (U --> V)) 'C tagged_fun) ==> Lf.
Proof.
  intros U V; unfold check_function_direct; cbn; cbv -[equal1].
  repeat first
    [ eapply equal1_neq; discriminate
    | progress evaluate2
    | progress evaluate
    ].
Qed.

Lemma check_function_recursive_some : forall U V,
  check_function_recursive @
    Z (((U --> V) --> (U --> V)) 'C tagged_fun) ==>
    Sm ('K1 (Sm (funty_eliminator U V))).
Proof.
  intros U V; pose proof (check_function_recursive_eval (rec_Z U V)) as H.
  unfold rec_cert_fn in H; cbv zeta in H.
  change (path_fn path_rec (rec_Z U V)) with (U '* V) in H.
  change (path_fn path_arg (U '* V)) with U in H.
  change (path_fn path_pB (U '* V)) with V in H.
  rewrite ceqb_refl in H; exact H.
Qed.

Lemma function_abstractor_recursive_eval : forall type_app0 U V,
  function_abstractor_core @
    Z (((U --> V) --> (U --> V)) 'C tagged_fun) @r type_app0 ==>
    Sm (funty_eliminator U V).
Proof.
  intros type_app0 U V; unfold function_abstractor_core.
  eapply extend_none.
  - apply check_function_direct_recursive_none.
  - eapply eval_appl.
    + eapply extend_some; apply check_function_recursive_some.
    + evaluate.
Qed.

Lemma function_declared : forall (AI : Decl) app C E,
  function_abstractor_core @ C @r app ==> E -> AI @ fun_nm @r app @r C ==> E.
Proof.
  intros AI app C E H.
  pose proof (function_abstractor_eval app C E H) as Hf.
  destruct (eval_pair_inv _ _ _ Hf) as [w [c [Hw [Hc Hw2]]]]; inv_out Hc.
  repeat (eapply eval_appl; [|eassumption]); exact (functions_declared AI).
Qed.

Lemma function_row_inv : forall AI app C r,
  AI @ fun_nm ==> function_abstractor ->
  AI @ fun_nm @r app @r C ==> r -> function_abstractor_core @ C @r app ==> r.
Proof.
  intros AI app C r HF H.
  destruct (eval_pair_inv _ _ _ H) as [D [c [HD [Hc Hv]]]]; inv_out Hc.
  destruct (eval_pair_inv _ _ _ HD) as [R [c' [HR [Hc' Ha]]]]; inv_out Hc'.
  pose proof (eval_deterministic _ _ HR _ HF) as ->.
  apply function_abstractor_eval_inv; eapply eval_appl; eassumption.
Qed.

Lemma function_declared_inv : forall (AI : Decl) app C r,
  AI @ fun_nm @r app @r C ==> r -> function_abstractor_core @ C @r app ==> r.
Proof. intros AI app C r H; exact (function_row_inv _ _ _ _ (functions_declared AI) H). Qed.

Local Opaque equal1 function_abstractor_core.

(** Elimination and ordinary-name inversion used in soundness. *)
Local Opaque equal equal1 function_abstractor_core.
Lemma funty_eliminator_inv : forall U V a X R,
  funty_eliminator U V @ a @r X ==> Sm R ->
  X = U /\ R = V.
Proof.
  intros U V a X R H; pose proof (eval_deterministic _ _ H _ (funty_eliminator_app U V a X)) as Heq.
  destruct (ceqb U X) eqn:Hc; [|discriminate].
  apply ceqb_true in Hc; inversion Heq; subst; auto.
Qed.

(** Registered wrapper types: lookup fixes the complete type tested by
    specialisation. Abstract construction and its typing proofs come later. *)
Local Opaque get_funty equal.

(** A wrapper stores its payload domain A in this unary eliminator.
    Elimination by an action of type F is the type application F @ A. *)
Definition payload_elim := Eval cbn in to_tree
  (star "A" (star "a" (star "F" (Ref "a" @@ Ref "F" @@ Ref "A")))).
Definition payload_eliminator A := 'wait[payload_elim,A].
Definition payload_eliminator2 A := ''wait[Val payload_elim,A].
Lemma payload_eliminator_head : forall A a,
  exists w, payload_eliminator A @ a ==> w /\
    (forall F V, w @ F ==> V <-> a @ F @r A ==> V).
Proof.
  intros A a; eexists; split.
  - apply wait_eval; unfold payload_elim; evaluate.
  - intros F V; split; intro H.
    + invert_eval; repeat (eapply eval_appl; eauto).
    + inv_out H; evaluate; eauto.
Qed.
Lemma payload_eliminator_some : forall A a F V,
  a @ F @r A ==> V -> payload_eliminator A @ a @r F ==> V.
Proof.
  intros A a F V H; destruct (payload_eliminator_head A a) as [w [Hw Hi]].
  eapply eval_appl; [exact Hw|apply Hi; exact H].
Qed.
Lemma payload_eliminator_inv : forall A a X V,
  payload_eliminator A @ a @r X ==> V -> a @ X @r A ==> V.
Proof.
  intros A a X V H; destruct (payload_eliminator_head A a) as [w [Hw Hi]].
  destruct (eval_pair_inv _ _ _ H) as [w' [u [Hw' [Hu Hv]]]]; inv_out Hu.
  pose proof (eval_deterministic _ _ Hw' _ Hw) as ->; apply Hi; exact Hv.
Qed.


Definition swap u := 'S2['I,'K1 u].
(** [swap[p]] passes its stored payload to its argument. *)
Definition wrap_eliminator := payload_eliminator.
Definition wrap_type T N := 'tagged[wrap_eliminator T,N].
(** Wrapper declarations and their lookup [get_wrap_payload_type] are
    below; the wrapper lemmas are in soundness.v. *)


Unset Default Proof Using.
Transparent equal function_abstractor_core equal1 get_funty get_wait.

(** Type application.  Every abstract type is introduced by its row of the
    declarations and eliminated by its own eliminator. *)
From TreeTyping Require Import tree.
Import ClauseNotation.
From Stdlib Require Import String Bool.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque equal equal1 get_tagname get_tagged is_concrete.
(** The programs below are written in the clause syntax above.
    [rec] is type application itself, so
    [rec @ F @ U] is the paper's [F # U]. *)

(** Structural application clauses, corresponding to the concrete rules
    in the paper's type-application figure. These are local components of the checker.

    triage[F0,F1,F2], tagged[E,N] => Lf
    triage[F0,F1,F2], Fk X Y      => let Sm G = F2 # X in G # Y          *)
Definition structural_fork2 rec F2 := <{
  fun "X" "Y" =>
    let Sm "G" = (match (Fk "X" "Y") with
                  | 'tagged => Lf
                  | _ => rec @ F2 @ "X"
                  end)
    in rec @ "G" @ "Y" }>.

(** Plain triage on U (the "otherwise" clause of a triage F):
    triage[F0,F1,F2] => \U. match U with
                           | Lf          => Sm F0
                           | Sm X        => F1 # X
                           | tagged[C,M] => Lf          (in structural_fork2)
                           | Fk X Y      => let Sm G = F2 # X in G # Y      *)
Definition structural_triage2 rec F0 F1 F2 := <{
  shape | Lf => (Sm F0) | Sm => 'wait[rec, F1]
        | Fk => {structural_fork2 rec F2} end }>.

(** Lf => \U. Sm (Sm U) *)
Definition type_app_leaf := Eval cbn in to_tree <{ fun "U" => (Sm (Sm "U")) }>.

(** Sm F => \U. match Fk F U with
               | tagged[C,N] => let Sm E = intro @ N @r C in Sm tagged[E,N]
               | X           => Sm X                                       *)
Definition type_app_stem_package (AI : Combination) :
  { t |
    to_tree <{
      fun "rec" "F" "U" =>
        match (Fk "F" "U") with
        | 'tagged["C", "N"] =>
            let Sm "E" = 'wait2[{AI}, "N", "rec"] @ "C"
            in (Sm 'tagged["E", "N"])
        | _ => (Sm (Fk "F" "U"))
        end }> = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition type_app_stem (AI : Combination) :=
  Eval cbn in proj1_sig (type_app_stem_package AI).

(** K1 F => \U. Sm F *)
Definition type_app_K := Eval cbn in to_tree <{ fun "F" "U" => (Sm "F") }>.

(** The paper's [F # U] inside the type-application clauses.  The section
    only scopes the notation, so that later sections can give [x # y]
    other meanings without overriding it. *)
Section TypeAppSClause.
Local Notation "x # y" := (Ref "rec" @@ x @@ y)
  (in custom clause at level 20, left associativity).

(** S2[G,F] => \U. let Sm V = G # U in let Sm W = F # U in V # W
    Sequential: [F # U] is evaluated only when [G # U] succeeds. *)
Definition type_app_S := Eval cbv in to_tree <{
  fun "rec" "G" "F" "U" =>
    let Sm "V" = "G" # "U" in let Sm "W" = "F" # "U" in "V" # "W" }>.
End TypeAppSClause.


Lemma eval_app_r_inv : forall e x v,
  Fk e (Sm x) ==> v -> exists w, e ==> w /\ w @ x ==> v.
Proof.
  intros e x v H; destruct (eval_pair_inv _ _ _ H) as [w [u [Hw [Hu Hv]]]].
  inversion Hu; subst u; eauto.
Qed.


Local Transparent equal1.
Lemma type_app_abstract_case_S_none : forall G F,
  (forall E N, 'S2[G,F] <> 'tagged[E,N]) ->
  (to_tree (tcase (''tagged[Ref "E", Ref "N"])
    (Ref "E")) @ 'S2[G,F]) ==> Lf.
Proof.
  intros G F Hnot.
  assert (Hgeneric : forall T,
    (forall E N, T <> 'tagged[E,N]) ->
    (to_tree (tcase (''tagged[Ref "E", Ref "N"])
      (Ref "E")) @ T) ==> Lf).
  {
    intros T Hplain.
    destruct T as [|T|X Y]; try (cbv; evaluate; fail).
    destruct X as [|X|X1 X2]; try (cbv; evaluate; fail).
    destruct X as [|X|X1 X2]; try (cbv; evaluate; fail).
    destruct X1 as [|X1|X11 X12]; try (cbv; evaluate; fail).
    destruct Y as [|Y|Y1 Y2]; try (destruct X2; cbv; evaluate; fail).
    destruct Y1 as [|Y1|Y11 Y12]; try (destruct X2; cbv; evaluate; fail).
    destruct Y1 as [|Y1|Y11 Y12]; try (destruct X2; cbv; evaluate; fail).
    destruct Y1 as [|Y1|Y11 Y12]; try (destruct X2; cbv; evaluate; fail).
    destruct Y2 as [|Y2|Y21 Y22]; try (destruct X2; cbv; evaluate; fail).
    destruct Y21 as [|Y21|Y211 Y212]; try (destruct X2; cbv; evaluate; fail).
    exfalso; eapply Hplain; eauto.
  }
  apply Hgeneric; exact Hnot.
Qed.

Local Opaque equal1.
Lemma type_app_stem_head : forall AI rec,
  exists handler, type_app_stem AI @ rec ==> handler.
Proof.
  intros; pose proof (function_abstractor_partial rec).
  eexists; unfold type_app_stem; cbn; repeat first [eassumption | progress evaluate].
Qed.

Lemma type_app_stem_tagged_result : forall AI app C N result,
  AI @ N @r app @r C ==> result ->
  type_app_stem AI @ app @r (Sm ('K1 C)) @r ('S2['K,'K1 N]) ==>
    match result with Sm E => Sm ('tagged[E,N]) | _ => Lf end.
Proof.
  intros AI app C N result H.
  pose proof (wait2_eval _ _ _ _ _ H) as Hw.
  pose proof (get_tagged_some C N) as Htag.
  destruct result; unfold type_app_stem; cbn.
  all: repeat first [eassumption | progress evaluate].
Qed.

Lemma type_app_stem_tagged : forall AI app C N E,
  AI @ N @r app @r C ==> Sm E ->
  type_app_stem AI @ app @r (Sm ('K1 C)) @r ('S2['K,'K1 N]) ==>
    Sm ('tagged[E,N]).
Proof. intros AI app C N E H; exact (type_app_stem_tagged_result AI app C N (Sm E) H). Qed.

Lemma type_app_stem_structural : forall AI app F U,
  (forall C N, Fk F U <> 'tagged[C,N]) ->
  type_app_stem AI @ app @r F @r U ==> Sm (Fk F U).
Proof.
  intros AI app F U Htag.
  pose proof (get_tagged_fork_none F U Htag) as Hget.
  pose proof (function_abstractor_partial app).
  unfold type_app_stem; cbn.
  repeat first [eassumption | progress evaluate].
Qed.

Definition structural_fork rec F2 := Eval cbn in
  to_tree (structural_fork2 (Val rec) (Val F2)).

Definition plain_triage rec F0 F1 F2 :=
  'triage[Sm F0,'wait[rec,F1],structural_fork rec F2].
(** The error clause's function of U: \U. Lf, which always fails. *)
Definition error_triage := 'K1 Lf.
(** The specification of the structural clauses used by the inversion
    lemmas: the error clause when Fk F0 F1 is tagged, plain triage
    otherwise (the program before the guard was lifted to F level). *)
Definition structural_triage rec F0 F1 F2 :=
  'wait[
    ('triage[plain_triage rec F0 F1 F2,
      'K1 error_triage,
      'K1 ('K1 ('K1 Lf))]) 'C get_tagged,
    Fk F0 F1].

Lemma structural_triage_plain : forall rec F0 F1 F2 U R,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  (structural_triage rec F0 F1 F2 @ U ==> R <-> plain_triage rec F0 F1 F2 @ U ==> R).
Proof.
  intros rec F0 F1 F2 U R HP.
  pose proof (get_tagged_none _ HP) as HG.
  assert (HS : ('triage[plain_triage rec F0 F1 F2, 'K1 error_triage,
      'K1 ('K1 ('K1 Lf))]) 'C get_tagged @ Fk F0 F1 ==> plain_triage rec F0 F1 F2)
    by (unfold plain_triage, error_triage; evaluate).
  unfold structural_triage; split; intro H.
  - apply wait_eval_inv in H; inv_out H.
    match goal with H1 : _ @ Fk F0 F1 ==> ?v |- _ =>
      pose proof (eval_deterministic _ _ H1 _ HS) as ->; assumption end.
  - apply wait_eval; eapply eval_appl; [exact HS|exact H].
Qed.
Lemma structural_triage_error : forall rec F0 F1 F2 E N U R,
  Fk F0 F1 = 'tagged[E,N] ->
  (structural_triage rec F0 F1 F2 @ U ==> R <-> error_triage @ U ==> R).
Proof.
  intros rec F0 F1 F2 E N U R HT.
  pose proof (get_tagged_some E N) as HG; rewrite <- HT in HG.
  assert (HS : ('triage[plain_triage rec F0 F1 F2, 'K1 error_triage,
      'K1 ('K1 ('K1 Lf))]) 'C get_tagged @ Fk F0 F1 ==> error_triage)
    by (unfold plain_triage, error_triage; evaluate).
  unfold structural_triage; split; intro H.
  - apply wait_eval_inv in H; inv_out H.
    match goal with H1 : _ @ Fk F0 F1 ==> ?v |- _ =>
      pose proof (eval_deterministic _ _ H1 _ HS) as ->; assumption end.
  - apply wait_eval; eapply eval_appl; [exact HS|exact H].
Qed.
Lemma error_triage_fails : forall U, error_triage @ U ==> Lf.
Proof. intros; unfold error_triage; evaluate. Qed.
Lemma error_triage_not_some : forall U V, ~ (error_triage @ U ==> Sm V).
Proof.
  intros U V H; pose proof (eval_deterministic _ _ H _ (error_triage_fails U)); discriminate.
Qed.

Local Ltac split_apps_local :=
  repeat match goal with H : Fk (Fk ?a ?b) ?c ==> _ |- _ => inv_out H end.
Local Ltac run_check :=
  first [eassumption | apply equal_eval | apply equal1_eq |
    evaluate_expr_core run_check run_check_head | idtac]
with run_check_head :=
  first [eassumption | apply equal_eval | apply equal1_eq |
    evaluate_head_core run_check | idtac].
Local Transparent query_handler.
(** Application of a triage F = triage[F0,F1,F2]: the clauses are tried on
    F alone, error test first (it always fails, at every U), then plain
    triage; each returns a function of U, which is then applied to U.  The
    stored program tries the operator-refusal (error) clause on every fork
    ([default_body]), so [triage_case] is the proof view of the clauses at
    a triage ([default_triage_iff]).
      triage[Sm (K1 E), label[N], F2]    => \U. Lf        (Fk F0 F1 tagged: error)
      triage[F0,F1,F2]                   => structural_triage2 (plain, on U)
    *)
Definition triage_clauses : Term := <{
  fun "rec" "F0" "F1" "F2" =>
    (first_match
     | (fun "F" => match (Fk "F0" "F1") with
                   | 'tagged["E", "N"] => (Sm (fun "U" => Lf))
                   | _ => Lf
                   end)
     | otherwise => (fun "F" => {structural_triage2 "rec" "F0" "F1" "F2"})
     end) @ 'triage["F0", "F1", "F2"] }>.
Definition triage_case := Eval lazy in to_tree triage_clauses.

(** The four F-level outcomes. *)

Lemma triage_case_error : forall rec E N F2,
  triage_case @ rec @r Sm ('K1 E) @r ('S2['K,'K1 N]) @r F2 ==> error_triage.
Proof.
  Local Transparent structural_fork.
  intros rec E N F2.
  pose proof (get_tagged_some E N) as HG.
  split_apps_local.
  unfold triage_case, extend_program, error_triage, structural_fork; run_check.
Local Opaque structural_fork.
Qed.
Lemma triage_case_plain : forall rec F0 F1 F2,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  triage_case @ rec @r F0 @r F1 @r F2 ==> plain_triage rec F0 F1 F2.
Proof.
  Local Transparent structural_fork.
  intros rec F0 F1 F2 HP.
  pose proof (get_tagged_none _ HP) as HG.
  split_apps_local.
  unfold triage_case, extend_program, plain_triage, structural_fork; run_check.
Local Opaque structural_fork.
Qed.


(** Plain triage on U (the last clause), as a closed component of
    [rec], F0, F1 and F2. *)
Definition plain_case := Eval cbn in to_tree <{
  fun "rec" "F0" "F1" "F2" => {structural_triage2 "rec" "F0" "F1" "F2"} }>.

(** The ordinary clauses: every clause except the F-level clause
    [tagged[E,N]], in the order of the paper's type-application figure.
    F is dispatched on its shape: a leaf and a stem have their own
    clauses; a fork Fk X Y tries the operator refusal
    [Fk (tagged[E,N]) _] (X tagged), and is otherwise split by
    its left branch X into [triage[F0,F1,F2]], [K1 G] and [S2[G,H]] (a
    three-way dispatch on X).  Each
    clause returns a function of U: the named component above, applied to
    the clause's pattern variables (and to [rec] where it recurses). *)
Definition ordinary_clauses (AI : Combination) : Term := <{
  fun "rec" =>
    shape
    | Lf => type_app_leaf
    | Sm "G" => {type_app_stem AI} @ "rec" @ "G"
    | Fk "X" "Y" =>
        (first_match
         | (fun "F" => match "X" with
                       | 'tagged["E", "N"] => (Sm (fun "U" => Lf))
                       | _ => Lf
                       end)
         | otherwise => (fun "F" =>
             'triage[(fun "G" => type_app_K @ "G"),
                     (fun "G" "H" => type_app_S @ "rec" @ "G" @ "H"),
                     (fun "F0" "F1" "F2" =>
                        'wait[plain_case, "rec"] @ "F0" @ "F1" @ "F2")]
             @ "X" @ "Y")
         end) @ (Fk "X" "Y")
    end }>.
Definition default_body AI := Eval cbn -[type_app_leaf type_app_stem type_app_K
  type_app_S plain_case] in to_tree (ordinary_clauses AI).
(** tagged[E,N] => E *)


Definition abstract_case := Eval cbn in to_tree
  (tcase (''tagged[Ref "E", Ref "N"])
    (Ref "E")).
(** [get_name_test] reads the name, rebuilds the test and compares, so
    that [equal] and [get_tagname] are not compiled into a pattern. *)
Definition path_name_test : list dir :=
  dir_l :: dir_s :: dir_r :: (path_arg ++ dir_s :: List.nil)%list.
Definition acc_name_test := path_prog path_name_test.
Definition get_name_test := Eval cbn -[equal get_tagname acc_name_test] in to_tree
  (star "C" ((star "e" (star "N"
      (Ref "e" @@ Ref "C"
        @@ ((''wait[Ref "e", Val Lf @@ Ref "N"]) ''C Val get_tagname)
        @@ (Val Lf @@ Ref "N") @@ Val Lf)))
    @@ Val equal @@ (Val acc_name_test @@ Ref "C"))).
Lemma get_name_test_spec : forall C, exists v, get_name_test @ C ==> v /\
  ((C = name_test (path_fn path_name_test C) /\ v = Sm (path_fn path_name_test C)) \/
   (C <> name_test (path_fn path_name_test C) /\ v = Lf)).
Proof.
  intros C; pose proof (path_eval path_name_test C) as Hr; fold acc_name_test in Hr.
  pose proof (equal_eval C) as He.
  destruct (combination_eq_dec C (name_test (path_fn path_name_test C))) as [E|E].
  - assert (Hk2 : forall a b, a = b -> equal1 a @ b ==> 'K)
      by (intros a b ->; apply equal1_eq).
    pose proof (Hk2 _ _ E) as Hk; clear Hk2.
    exists (Sm (path_fn path_name_test C)); split; [|left; auto].
    unfold name_test in Hk; unfold get_name_test; evaluate.
  - pose proof (equal1_neq C _ E) as Hk; exists Lf; split; [|right; auto].
    unfold name_test in Hk; unfold get_name_test; evaluate.
Qed.
Lemma get_name_test_some : forall nm, get_name_test @ name_test nm ==> Sm nm.
Proof.
  intros nm; destruct (get_name_test_spec (name_test nm)) as [v [H [[_ ->]|[E _]]]].
  - exact H.
  - contradiction E; reflexivity.
Qed.
Lemma get_name_test_none : forall C, (forall N, C <> name_test N) -> get_name_test @ C ==> Lf.
Proof.
  intros C H; destruct (get_name_test_spec C) as [v [Hv [[E _]|[_ ->]]]].
  - contradiction (H _ E).
  - exact Hv.
Qed.
Lemma get_name_test_inv : forall C nm,
 get_name_test @ C ==> Sm nm -> C = name_test nm.
Proof.
  intros C nm H; destruct (get_name_test_spec C) as [v [Hv [[E ->]|[_ ->]]]].
  - pose proof (eval_deterministic _ _ H _ Hv) as HE; inversion HE; subst nm; exact E.
  - pose proof (eval_deterministic _ _ H _ Hv); discriminate.
Qed.
Ltac name_failure := apply get_name_test_none;
  let N := fresh "N" in let HE := fresh "HE" in
  intros N HE; unfold name_test in HE; first [discriminate HE | inversion HE].

(** The branches are functions: select first, then apply to U. *)
Local Ltac run := first [eassumption|apply equal_eval|apply equal1_eq|
 evaluate_expr_core run run_head|idtac]
with run_head := first [eassumption|apply equal_eval|apply equal1_eq|evaluate_head_core run|idtac].
Local Ltac split_apps := repeat match goal with H : Fk (Fk ?a ?b) ?c ==> _ |- _ => inv_out H end.
Local Opaque payload_eliminator.
(** ** Wrapper lookup *)
(** The abstractor of the wrapper with payload program [p]: when
    [p @ Lf ==> Sm T] it maps the carrier [swap T] to the eliminator
    [wrap_eliminator T] and refuses every other carrier. *)
Definition wrap_abstractor_body := Eval cbn -[equal equal1 get_wait] in to_tree
 (star "p" (star "C"
  (''onStem1 (star "T"
   (Val equal @@ ''S2[Val 'I,''K1 (Ref "T")] @@ Ref "C"
    @@ (Val Lf @@ payload_eliminator2 (Ref "T")) @@ Val Lf))
   @@ (Ref "p" @@ Val Lf)))).
Definition computed_wrap_abstractor p := 'wait[wrap_abstractor_body,p].
(** A fixed payload type [T] is computed by [fixed_payload T]. *)
Definition fixed_payload T := 'K1 (Sm T).
Definition wrap_abstractor T := computed_wrap_abstractor (fixed_payload T).
(* A wrapper's abstractor is 'wait[wrap_abstractor_body, p], so its
   payload program p sits at path_arg. *)
Definition path_payload := (dir_r :: path_arg)%list.
Definition get_payload_program := path_prog path_payload.
Definition computed_wrap_builder := Eval cbn -[equal equal1 get_wait] in to_tree
  (star "p" (''K1 (''wait[Val wrap_abstractor_body, Ref "p"]))).
Definition get_computed_payload :=
  'S2['S2['S2['S2[equal, computed_wrap_builder 'C get_payload_program],
    get_payload_program], 'K1 ('K1 Lf)], 'K1 Lf].
Definition wrapper_lookup AI := get_computed_payload 'C AI.
Definition get_wrap_payload_type AI := wrapper_lookup AI.

Local Opaque get_wrap_payload_type.
Local Opaque payload_eliminator.

(** ** The IsNamed family

    The abstractor maps the carrier type [name_test N] at a concrete name
    [N] to the eliminator [tagged_by N].  It consults no
    declarations. *)
Definition is_named_abstractor := Eval cbn -[is_concrete get_name_test] in to_tree <{
  fun "C" => let Sm "N" = get_name_test @ "C" in
    if is_concrete @ "N" then (Sm 'tagged_by["N"]) else Lf }>.
Definition supports_is_named (AI : Combination) : Prop := AI @ is_named_nm ==> ('K1 is_named_abstractor).

Lemma is_named_abstractor_some : forall N,
  concrete N -> is_named_abstractor @ name_test N ==> Sm (tagged_by N).
Proof.
  intros N HN; pose proof (get_name_test_some N); unfold concrete in HN.
  unfold is_named_abstractor, tagged_by; cbn; run.
Qed.

Local Opaque get_name_test default_body abstract_case.
(** One fixed application policy, in the clause order of the
    the paper's type-application figure: leaf, stem, then for a fork the
    F-level clause abstract elimination, then the remaining fork clauses
    (operator refusal, and the split into triage, K1 and S2) in that
    order.
    (The paper's name-test, one-level query and one-level update clauses
    are gone: those programs are tagged values of ordinary families.)

    The ordinary clauses [default_body] are computed once from [rec]; a
    leaf or stem is passed straight to them (they dispatch it to its own
    clause), while a fork first meets the F-level clause.  [triage_case]
    remains as a proof view of the fork clauses at a triage.
    No flag selects or disables a rule.

    type_app = let ordinary = default_body @ rec in
               shape
               | Lf       => ordinary @ Lf
               | Sm G     => ordinary @ (Sm G)
               | Fk X Y   => first_match
                             | tagged[E,N]  => E @ rec         (abstract_wait)
                             | otherwise    => ordinary        (default_body)
                             end @ (Fk X Y) *)
Definition abstract_wait := Eval cbn -[abstract_case] in to_tree
  (star "rec" (star "F"
    (''onStem1 (star "E" (Val Lf @@ ''wait[Ref "E", Ref "rec"]))
       @@ (Val abstract_case @@ Ref "F")))).

Definition body AI := Eval cbn -[abstract_wait default_body] in
 to_tree <{
   fun "rec" =>
     (fun "ordinary" =>
        shape
        | Lf => "ordinary" @ Lf
        | Sm "G" => "ordinary" @ (Sm "G")
        | Fk "X" "Y" =>
            {extend_w2 (''wait[Val abstract_wait, Ref "rec"]) (Ref "ordinary")} @ (Fk "X" "Y")
        end) @ ({default_body AI} @ "rec") }>.
(** The component view of [body], for controlled inversion. *)
Lemma body_components : forall AI, body AI = to_tree
 (star "rec" (star "ordinary"
   (''triage[Ref "ordinary" @@ Val Lf,
     star "G" (Ref "ordinary" @@ (Val Lf @@ Ref "G")),
     star "X" (star "Y" (extend_w2 (''wait[Val abstract_wait, Ref "rec"]) (Ref "ordinary")
       @@ (Val Lf @@ Ref "X" @@ Ref "Y")))])
   @@ (Val (default_body AI) @@ Ref "rec"))).
Proof. intros; reflexivity. Qed.
Definition type_app AI := Z (body AI).
Abbreviation app := type_app.

(** ** The ordinary clauses, shape by shape

    Forward evaluation of [default_body] at each shape of F.  At a triage
    the ordinary clauses select exactly the function of U selected by the
    proof view [triage_case] ([default_triage_iff]). *)

Lemma plain_case_eval : forall rec F0 F1 F2,
  plain_case @ rec @r F0 @r F1 @r F2 ==> plain_triage rec F0 F1 F2.
Proof.
  Local Transparent structural_fork.
  intros; unfold plain_case, plain_triage, structural_fork; cbn; evaluate.
  Local Opaque structural_fork.
Qed.
Local Opaque plain_case.

Local Ltac ord_run := first [eassumption | apply equal1_eq |
  apply equal1_neq; discriminate |
  evaluate_expr_core ord_run ord_run_head | idtac]
with ord_run_head := first [eassumption | apply equal1_eq |
  apply equal1_neq; discriminate | evaluate_head_core ord_run | idtac].
Local Ltac ord_prep AI rec :=
  let Hs := fresh "Hs" in let Ht := fresh "Ht" in
  destruct (type_app_stem_head AI rec) as [? Hs];
  assert (Ht : exists t, type_app_S @ rec ==> t)
    by (eexists; unfold type_app_S; cbn; evaluate);
  destruct Ht as [? Ht].
Local Ltac prune_evals := repeat match goal with
  | H1 : ?e ==> ?a, H2 : ?e ==> ?b |- _ =>
      let E := fresh "E" in
      pose proof (eval_deterministic _ _ H1 _ H2) as E; clear H1;
      inversion E; subst; try clear E
  end.
Local Ltac extend_chain := match goal with
  | H1 : extend_program @ ?p ==> ?a, H2 : ?a @ ?r ==> ?b, H3 : ?b @ ?x ==> ?w |- _ =>
    let HE := fresh "HE" in
    assert (HE : extend p r @ x ==> w) by (apply wait2_eval; eauto using eval_appl);
    clear H1 H2 H3;
    let v := fresh "v" in let HS := fresh "HS" in let HF := fresh "HF" in
    let l := fresh "l" in let q := fresh "q" in let EE := fresh "EE" in
    destruct (extend_inv _ _ _ _ HE) as [[v [HS EE]]|[[HS HF]|[l [q [HS EE]]]]]; clear HE
  end.
Local Ltac not_update_one_level :=
  let HE := fresh "HE" in intro HE; unfold update_one_level in HE; discriminate.
Local Transparent default_body.

Lemma default_leaf : forall AI rec,
  default_body AI @ rec @r Lf ==> type_app_leaf.
Proof. intros; ord_prep AI rec; unfold default_body, extend_program; ord_run. Qed.

Lemma default_stem : forall AI rec G v,
  type_app_stem AI @ rec @r G ==> v -> default_body AI @ rec @r Sm G ==> v.
Proof.
  intros AI rec G v H.
  destruct (eval_app_r_inv _ _ _ H) as [s [Hs Hv]].
  assert (Ht : exists t, type_app_S @ rec ==> t)
    by (eexists; unfold type_app_S; cbn; evaluate).
  destruct Ht as [t Ht].
  unfold default_body, extend_program; ord_run.
Qed.

Lemma default_K : forall AI rec G v,
  type_app_K @ G ==> v -> default_body AI @ rec @r ('K1 G) ==> v.
Proof.
  intros AI rec G v H; ord_prep AI rec.
  pose proof (get_tagged_none Lf ltac:(intros; discriminate)) as HG.
  unfold default_body, extend_program; ord_run.
Qed.

Lemma default_S : forall AI rec G H v,
  type_app_S @ rec @r G @r H ==> v -> default_body AI @ rec @r ('S2[G,H]) ==> v.
Proof.
  intros AI rec G H v Hv.
  destruct (type_app_stem_head AI rec) as [s Hs].
  destruct (eval_app_r_inv _ _ _ Hv) as [t1 [Ht1 Hv1]].
  destruct (eval_app_r_inv _ _ _ Ht1) as [t [Ht Ht2]].
  pose proof (get_tagged_none (Sm G) ltac:(intros; discriminate)) as HG.
  unfold default_body, extend_program; ord_run.
Qed.

Lemma default_S_app : forall AI rec G H U R,
  type_app_S @ rec @r G @r H @r U ==> R -> default_body AI @ rec @r ('S2[G,H]) @r U ==> R.
Proof.
  intros AI rec G H U R HR.
  destruct (eval_app_r_inv _ _ _ HR) as [w [Hw HR']].
  eapply eval_appl; [apply default_S; exact Hw|exact HR'].
Qed.


Lemma default_error : forall AI rec E N F2,
  default_body AI @ rec @r 'triage[Sm ('K1 E), 'S2['K,'K1 N], F2] ==> error_triage.
Proof.
  intros AI rec E N F2; ord_prep AI rec.
  pose proof (get_tagged_some E N) as HG.
  pose proof (plain_case_eval rec (Sm ('K1 E)) ('S2['K,'K1 N]) F2) as HPl.
  split_apps_local.
  unfold default_body, extend_program, error_triage; ord_run.
Qed.

Lemma default_plain : forall AI rec F0 F1 F2,
  (forall E N, Fk F0 F1 <> 'tagged[E,N]) ->
  default_body AI @ rec @r 'triage[F0,F1,F2] ==> plain_triage rec F0 F1 F2.
Proof.
  intros AI rec F0 F1 F2 HP; ord_prep AI rec.
  pose proof (get_tagged_none _ HP) as HG.
  pose proof (plain_case_eval rec F0 F1 F2) as HPl.
  split_apps_local.
  unfold default_body, extend_program; ord_run.
Qed.

(** The F-level selection: applied to the branches of F, the triage
    clauses yield the refusal or the structural clauses, before any
    argument type is seen. *)
Lemma triage_case_head : forall rec F0 F1 F2 w,
 triage_case @ rec @r F0 @r F1 @r F2 ==> w ->
 ((exists E N, Fk F0 F1 = 'tagged[E,N]) /\ w = error_triage) \/
 ((forall E N, Fk F0 F1 <> 'tagged[E,N]) /\ w = plain_triage rec F0 F1 F2).
Proof.
 intros rec F0 F1 F2 w H.
 destruct (tagged_decide (Fk F0 F1)) as [[E [N HE]]|HP].
 - left; split; [exists E, N; exact HE|].
   inversion HE; subst F0 F1.
   exact (eval_deterministic _ _ H _ (triage_case_error rec E N F2)).
 - right; split; [exact HP|].
   exact (eval_deterministic _ _ H _ (triage_case_plain rec _ _ _ HP)).
Qed.

(** At a triage, the ordinary clauses and [triage_case] select the same
    function of U. *)
Lemma default_triage_agree : forall AI rec F0 F1 F2,
  exists w, triage_case @ rec @r F0 @r F1 @r F2 ==> w /\
            default_body AI @ rec @r 'triage[F0,F1,F2] ==> w.
Proof.
 intros AI rec F0 F1 F2.
 destruct (tagged_decide (Fk F0 F1)) as [[E [N HE]]|HP].
 - inversion HE; subst F0 F1.
   eexists; split; [apply triage_case_error|apply default_error].
 - eexists; split; [apply triage_case_plain; exact HP|apply default_plain; exact HP].
Qed.

Lemma default_triage_iff : forall AI rec F0 F1 F2 w,
  default_body AI @ rec @r 'triage[F0,F1,F2] ==> w <->
  triage_case @ rec @r F0 @r F1 @r F2 ==> w.
Proof.
 intros AI rec F0 F1 F2 w.
 destruct (default_triage_agree AI rec F0 F1 F2) as [w0 [HT HD]].
 split; intro H.
 - rewrite (eval_deterministic _ _ H _ HD); exact HT.
 - rewrite (eval_deterministic _ _ H _ HT); exact HD.
Qed.

Lemma default_stem_inv : forall AI rec G w,
  default_body AI @ rec @r Sm G ==> w -> type_app_stem AI @ rec @r G ==> w.
Proof.
  intros AI rec G w H.
  assert (Hv : exists v, type_app_stem AI @ rec @r G ==> v)
    by (pose proof (function_abstractor_partial rec); eexists; unfold type_app_stem; cbn; repeat first [eassumption | progress evaluate]).
  destruct Hv as [v Hv].
  rewrite (eval_deterministic _ _ H _ (default_stem AI rec G v Hv)); exact Hv.
Qed.

Lemma default_S_head_inv : forall AI rec G H w,
  default_body AI @ rec @r ('S2[G,H]) ==> w -> type_app_S @ rec @r G @r H ==> w.
Proof.
  intros AI rec G H w Hw.
  pose proof (get_tagged_none (Sm G) ltac:(intros; discriminate)) as HG.
  unfold default_body in Hw; invert_eval; prune_evals.
  all: repeat (extend_chain; invert_eval; prune_evals).
  all: eauto using eval_appl.
Qed.

Local Opaque default_body.

(** ** Type application on F: the two F-level clauses, then the ordinary ones *)
Lemma abstract_case_plain : forall T,
 (forall E N, T <> 'tagged[E,N]) -> abstract_case @ T ==> Lf.
Proof.
  Local Transparent abstract_case.
  intros T Hplain; unfold abstract_case.
  destruct T as [|T|X Y]; try (cbv; evaluate; fail).
  destruct X as [|X|X1 X2]; try (cbv; evaluate; fail).
  exact (type_app_abstract_case_S_none X Y Hplain).
  Local Opaque abstract_case.
Qed.
Lemma abstract_case_tagged : forall E N, abstract_case @ 'tagged[E,N] ==> Sm E.
Proof.
  Local Transparent abstract_case.
  intros E N; unfold abstract_case; cbn; run.
  Local Opaque abstract_case.
Qed.
Local Transparent abstract_wait.
Lemma abstract_wait_tagged : forall rec E N,
  abstract_wait @ rec @r 'tagged[E,N] ==> Sm ('wait[E,rec]).
Proof.
  intros rec E N; pose proof (abstract_case_tagged E N) as HA.
  unfold abstract_wait; cbn; run.
Qed.
Lemma abstract_wait_none : forall rec F,
  abstract_case @ F ==> Lf -> abstract_wait @ rec @r F ==> Lf.
Proof.
  intros rec F HA; unfold abstract_wait; cbn; run.
Qed.
Lemma abstract_wait_plain : forall rec F,
  (forall E N, F <> 'tagged[E,N]) -> abstract_wait @ rec @r F ==> Lf.
Proof. intros; apply abstract_wait_none, abstract_case_plain; assumption. Qed.
Local Opaque abstract_wait.
Lemma wait_abstract_wait_plain : forall rec F,
  (forall E N, F <> 'tagged[E,N]) -> 'wait[abstract_wait, rec] @ F ==> Lf.
Proof. intros; apply wait_eval, abstract_wait_plain; assumption. Qed.
Lemma wait_abstract_wait_none : forall rec F,
  abstract_case @ F ==> Lf -> 'wait[abstract_wait, rec] @ F ==> Lf.
Proof. intros; apply wait_eval, abstract_wait_none; assumption. Qed.
Lemma wait_abstract_wait_tagged : forall rec E N,
  'wait[abstract_wait, rec] @ 'tagged[E,N] ==> Sm ('wait[E,rec]).
Proof. intros; apply wait_eval, abstract_wait_tagged. Qed.

Lemma get_name_test_leaf : get_name_test @ Lf ==> Lf.
Proof. apply get_name_test_none; intros N HE; discriminate HE. Qed.
Lemma get_name_test_stem : forall G, get_name_test @ Sm G ==> Lf.
Proof. intros; apply get_name_test_none; intros N HE; discriminate HE. Qed.

Lemma default_head : forall AI rec,
  exists d, default_body AI @ rec ==> d /\ d @ Lf ==> type_app_leaf.
Proof.
  intros AI rec.
  destruct (eval_app_r_inv _ _ _ (default_leaf AI rec)) as [d [Hd H]]; eauto.
Qed.

(** Forward: off the F-level clause, [body] is the ordinary clauses. *)
Lemma body_default : forall AI rec F w,
  abstract_case @ F ==> Lf -> get_name_test @ F ==> Lf ->
  default_body AI @ rec @r F ==> w -> body AI @ rec @r F ==> w.
Proof.
  intros AI rec F w HA0 HG H.
  pose proof (wait_abstract_wait_none rec F HA0) as HA.
  destruct (default_head AI rec) as [d [Hd HL]].
  destruct (eval_app_r_inv _ _ _ H) as [d' [Hd' Hw]].
  rewrite (eval_deterministic _ _ Hd' _ Hd) in Hw; clear Hd'.
  destruct F as [|G|X Y].
  - rewrite (eval_deterministic _ _ Hw _ HL); clear Hw.
    unfold body; run.
  - unfold body; run.
  - unfold body, extend_program; run.
Qed.

Lemma body_abstract : forall AI rec E N,
  body AI @ rec @r 'tagged[E,N] ==> 'wait[E,rec].
Proof.
  intros AI rec E N.
  pose proof (wait_abstract_wait_tagged rec E N) as HA.
  destruct (default_head AI rec) as [d [Hd HL]].
  unfold body, extend_program; run.
Qed.


Local Transparent extend_program.
(** Inversion: the F-level value of [body] at F. *)
Lemma body_inv : forall AI rec F w,
  body AI @ rec @r F ==> w ->
  (exists E N, F = 'tagged[E,N] /\ w = 'wait[E,rec]) \/
  ((forall E N, F <> 'tagged[E,N]) /\
   default_body AI @ rec @r F ==> w).
Proof.
  intros AI rec F w H.
  destruct (tagged_decide F) as [[E [N ->]]|HP].
  { left; exists E, N; split; [reflexivity|].
    exact (eval_deterministic _ _ H _ (body_abstract AI rec E N)). }
  right.
  unfold body in H; invert_eval.
  1,2: split; [exact HP|eauto 6 using eval_appl].
  pose proof (wait_abstract_wait_plain rec _ HP) as HA.
  match goal with
  | H1 : extend_program @ ?p ==> ?v0,
    H2 : ?v0 @ ?d ==> ?v1,
    H3 : ?v1 @ (Fk ?x ?y) ==> w |- _ =>
    assert (HE : extend_w p d @ Fk x y ==> w)
      by (apply wait2_eval; eauto using eval_appl)
  end.
  destruct (extend_w_inv _ _ _ _ HE) as [[v [HS _]]|[[_ HE2]|[l [q [HS _]]]]].
  1,3: pose proof (eval_deterministic _ _ HS _ HA); discriminate.
  split; [exact HP|eauto 6 using eval_appl].
Qed.


Lemma body_default_name : forall AI rec F w,
  abstract_case @ F ==> Lf ->
  default_body AI @ rec @r F ==> w -> body AI @ rec @r F ==> w.
Proof.
  intros AI rec F w HA0 H.
  pose proof (wait_abstract_wait_none rec F HA0) as HA.
  destruct (default_head AI rec) as [d [Hd HL]].
  destruct (eval_app_r_inv _ _ _ H) as [d' [Hd' Hw]].
  rewrite (eval_deterministic _ _ Hd' _ Hd) in Hw; clear Hd'.
  destruct F as [|G|X Y].
  - rewrite (eval_deterministic _ _ Hw _ HL); clear Hw.
    unfold body; run.
  - unfold body; run.
  - unfold body, extend_program; run.
Qed.


Lemma default_application : forall AI F U R,
 abstract_case @ F ==> Lf -> get_name_test @ F ==> Lf ->
 default_body AI @ app AI @r F @r U ==> R -> app AI @ F @r U ==> R.
Proof.
 intros AI F U R HA HG HC.
 destruct (eval_app_r_inv _ _ _ HC) as [w [Hw HR]].
 eapply eval_appl; [apply Z_unfold; apply body_default; eassumption|exact HR].
Qed.


(** A raw name test [name_test N] is typed by the S2 clause; the IsNamed
    test [is_named n] by the IsNamed family. *)


Lemma app_S : forall AI G F U VG VF R,
 (forall E N,'S2[G,F] <> 'tagged[E,N]) ->
 get_name_test @ ('S2[G,F]) ==> Lf ->
 app AI @ G @r U ==> Sm VG -> app AI @ F @r U ==> Sm VF ->
 app AI @ VG @r VF ==> R -> app AI @ ('S2[G,F]) @r U ==> R.
Proof.
  Local Transparent type_app_S.
 intros AI G F U VG VF R HP HM HG HF HR;apply default_application.
 - apply abstract_case_plain;exact HP.
 - exact HM.
 - apply default_S_app;split_apps;unfold type_app_S;cbn;run.
Local Opaque type_app_S.
Qed.
Local Ltac reject_name_local := name_failure.

Lemma app_abstract : forall AI E N U R,
 E @ app AI @r U ==> R -> app AI @ 'tagged[E,N] @r U ==> R.
Proof.
 intros AI E N U R HE.
 eapply eval_appl;[apply Z_unfold;apply body_abstract|apply wait_eval;exact HE].
Qed.
Lemma app_stem : forall AI F U R,
 type_app_stem AI @ app AI @r F @r U ==> R -> app AI @ Sm F @r U ==> R.
Proof.
 intros AI F U R H;apply default_application.
 - apply abstract_case_plain;intros;discriminate.
 - apply get_name_test_stem.
 - destruct (eval_app_r_inv _ _ _ H) as [w [Hw HR]].
   eapply eval_appl;[apply default_stem;exact Hw|exact HR].
Qed.

Lemma app_K : forall AI F U,app AI @ ('K1 F) @r U ==> Sm F.
Proof.
  Local Transparent get_name_test.
 intros;apply default_application.
 - apply abstract_case_plain;intros;discriminate.
 - reject_name_local.
 - eapply eval_appl;[apply default_K;unfold type_app_K;evaluate|evaluate].
Local Opaque get_name_test.
Qed.
Lemma app_I : forall AI U,app AI @ ('I) @r U ==> Sm U.
Proof.
  Local Transparent get_name_test.
 intros;change (app AI @ ('S2['K,'K]) @r U ==> Sm U).
 eapply app_S;[intros;discriminate|reject_name_local| | |apply app_K].
 all: apply app_stem;apply type_app_stem_structural;intros;discriminate.
Local Opaque get_name_test.
Qed.
Lemma app_true : forall AI U,app AI @ ('K) @r U ==> Sm ('K1 U).
Proof. intros;apply app_stem;apply type_app_stem_structural;intros;discriminate. Qed.

(** An ordinary composition used by the following derived rules;
    it is not a clause of the checker. *)
(** The conditional [if_named] tests with the IsNamed test
    [is_named nm], a tagged value; its type is [IfNamed]. *)
Definition if_named nm s d := 'S2['S2['S2[is_named nm,'K1 s],'K1 d],'I].
Definition IfNamed N S D := 'S2['S2['S2[IsNamed N,'K1 S],'K1 D],'I].

(** Elimination of [IsNamed N] by [tagged_by N] runs the name test on the argument type. *)
Lemma app_IsNamed : forall AI N U B,
  name_test N @ U ==> B -> app AI @ IsNamed N @r U ==> Sm B.
Proof.
  intros; unfold IsNamed; apply app_abstract.
  apply tagged_by_eval; assumption.
Qed.

Lemma if_named_selected : forall AI nm S D U test branch selected V,
 app AI @ IsNamed nm @r U ==> Sm test ->
 app AI @ test @r S ==> Sm branch ->
 app AI @ branch @r D ==> Sm selected ->
 app AI @ selected @r U ==> Sm V ->
 app AI @ IfNamed nm S D @r U ==> Sm V.
Proof.
  Local Transparent get_name_test.
 intros AI nm S D U test branch selected V HM HT HB HV;unfold IfNamed.
 eapply app_S;[intros;discriminate|unfold IsNamed;reject_name_local| |apply app_I|exact HV].
 eapply app_S;[intros;discriminate|unfold IsNamed;reject_name_local| |apply app_K|exact HB].
 eapply app_S;[intros;discriminate|unfold IsNamed;reject_name_local|exact HM|apply app_K|exact HT].
Local Opaque get_name_test.
Qed.


Definition app_default := default_application.
Lemma get_name_test_triage_none : forall F0 F1 F2,
  get_name_test @ 'triage[F0,F1,F2] ==> Lf.
Proof. intros; apply get_name_test_none; intros N HE; discriminate HE. Qed.
Lemma abstract_case_triage_none : forall F0 F1 F2,
  abstract_case @ 'triage[F0,F1,F2] ==> Lf.
Proof.
  Local Transparent abstract_case. intros; unfold abstract_case, extend_program; cbn; repeat first [apply equal1_eq | progress evaluate]. Local Opaque abstract_case.
Qed.

Lemma default_triage : forall AI rec F0 F1 F2 U R,
  triage_case @ rec @r F0 @r F1 @r F2 @r U ==> R ->
  default_body AI @ rec @r 'triage[F0,F1,F2] @r U ==> R.
Proof.
  intros AI rec F0 F1 F2 U R H.
  destruct (eval_app_r_inv _ _ _ H) as [w [Hw HR]].
  eapply eval_appl; [apply (proj2 (default_triage_iff AI rec F0 F1 F2 w)); exact Hw|exact HR].
Qed.


Lemma app_leaf : forall AI U, app AI @ Lf @r U ==> Sm (Sm U).
Proof.
  intros; apply app_default.
  - apply abstract_case_plain; intros; discriminate.
  - apply get_name_test_leaf.
  - eapply eval_appl; [apply default_leaf|unfold type_app_leaf; evaluate].
Qed.

Lemma app_compose : forall AI G F U VF R,
 get_name_test @ (G 'C F) ==> Lf ->
 (forall E N,G 'C F <> 'tagged[E,N]) ->
 app AI @ F @r U ==> Sm VF -> app AI @ G @r VF ==> R ->
 app AI @ (G 'C F) @r U ==> R.
Proof. intros;eapply app_S;[eassumption|eassumption|apply app_K|eassumption|eassumption]. Qed.
Lemma triage_structural : forall rec F0 F1 F2 U R,
  structural_triage rec F0 F1 F2 @ U ==> R ->
  triage_case @ rec @r F0 @r F1 @r F2 @r U ==> R.
Proof.
  intros rec F0 F1 F2 U R HS.
  destruct (tagged_decide (Fk F0 F1)) as [[E [N HE]]|HP].
  - apply (structural_triage_error rec F0 F1 F2 E N U R HE) in HS.
    inversion HE; subst F0 F1.
    eapply eval_appl; [apply triage_case_error|exact HS].
  - apply (structural_triage_plain rec F0 F1 F2 U R HP) in HS.
    eapply eval_appl; [apply triage_case_plain; assumption|exact HS].
Qed.
Local Opaque app.
Lemma app_Z : forall AI F U V1 V,
  app AI @ F @r Z F ==> Sm V1 -> app AI @ V1 @r U ==> Sm V ->
  app AI @ Z F @r U ==> Sm V.
Proof.
  Local Transparent get_name_test.
  intros AI F U V1 V HF HV; unfold Z.
  Ltac step := first
    [ match goal with
      | |- type_app_stem _ @ _ @r _ @r _ ==> _ =>
        apply type_app_stem_structural; intros; discriminate
      | |- app _ @ ?T @r _ ==> _ =>
        tryif is_evar T then fail 1 else first
        [ eapply app_S; [intros; discriminate|
            solve [name_failure]| | |]
        | apply app_K | apply app_stem | apply app_leaf ]
      end ].
  repeat step.
  Unshelve.
  all: repeat step.
  - fold Z; exact HF.
  - exact HV.
Local Opaque get_name_test.
Qed.

(** update_one_level[Update] => \U. Sm U, for every U. *)


(** Inverting stem application, needed by value-inference inversion. *)
Local Opaque app equal equal1 type_app_stem type_app_S
  abstract_case default_body triage_case.
Lemma app_stem_inv : forall AI F U R,
  app AI @ Sm F @r U ==> R ->
  type_app_stem AI @ app AI @r F @r U ==> R.
Proof.
  intros AI F U R H.
  destruct (eval_app_r_inv _ _ _ H) as [s [Hs Ha]].
  pose proof (Z_unfold_inv _ _ _ Hs) as Hb.
  destruct (body_inv _ _ _ _ Hb) as [[E [N [HE _]]]|[_ HD]].
  - discriminate.
  - apply default_stem_inv in HD; eapply eval_appl; [exact HD|exact Ha].
Qed.

Definition type_app_stem_inv := app_stem_inv.

Local Transparent type_app_stem extend_program.
Lemma type_app_stem_tagged_success_inv : forall AI app C N R,
  type_app_stem AI @ app @r (Sm ('K1 C)) @r ('S2['K,'K1 N]) ==> Sm R ->
  exists E, AI @ N @r app @r C ==> Sm E /\ R = 'tagged[E,N].
Proof.
  intros AI app C N R H.
  unfold type_app_stem in H; cbn in H; unfold extend_program in H.
  repeat first
    [ match goal with
      | HH : get_tagged @ ('tagged[C,N]) ==> ?v |- _ =>
          is_var v;
          pose proof (eval_deterministic _ _ HH _ (get_tagged_some C N)) as HE;
          subst v; clear HH
      end
    | progress invert_eval1 ].
  match goal with
  | H1 : ?ai @ ?n ==> ?f, H2 : ?f @ ?a ==> ?g, H3 : ?g @ ?c ==> Sm ?r |- _ =>
      exists r; split; [eapply eval_appl; [eapply eval_appl; eassumption|eassumption]|reflexivity]
  end.
Qed.

Lemma type_app_stem_structural_inv : forall AI app F U R,
  (forall C N, Fk F U <> 'tagged[C,N]) ->
  type_app_stem AI @ app @r F @r U ==> Sm R -> R = Fk F U.
Proof.
  intros AI app F U R Htag H.
  pose proof (type_app_stem_structural AI app F U Htag) as Hstruct.
  pose proof (eval_deterministic _ _ H _ Hstruct); congruence.
Qed.

Local Opaque type_app_stem extend_program.
Lemma type_app_stem_fork_success_shape : forall AI app F U R,
  type_app_stem AI @ app @r F @r U ==> Sm R -> exists R1 R2, R = Fk R1 R2.
Proof.
  intros AI app F U R H.
  destruct (tagged_decide (Fk F U)) as [[C [N Heq]]|Hplain].
  - inversion Heq; subst F U.
    destruct (type_app_stem_tagged_success_inv AI _ _ _ _ H) as [E [_ ->]].
    repeat eexists.
  - pose proof (type_app_stem_structural_inv AI _ _ _ _ Hplain H) as ->; eauto.
Qed.

Lemma type_app_stem_triage_success_inv : forall AI app F0 F1 F2 R,
  type_app_stem AI @ app @r (Fk F0 F1) @r F2 ==> Sm R ->
  R = 'triage[F0,F1,F2].
Proof. intros; eapply type_app_stem_structural_inv; [intros; discriminate|eauto]. Qed.

Definition type_app_leaf_ev := app_leaf.
Definition type_app_stem_ev := app_stem.
Definition type_app_K_ev := app_K.
Definition type_app_S_ev := app_S.
Definition type_app_abstract := app_abstract.
Definition type_app_I := app_I.
Definition type_app_compose := app_compose.
Definition type_app_Z := app_Z.


Ltac new_S := eapply app_S;[|solve [name_failure]| | |].

(** Application inversion for preservation of typing. *)
Local Opaque app equal equal1 get_tagname get_tagged abstract_case default_body type_app_stem type_app_S.
Lemma get_name_test_S_right : forall G F,
 F <> get_tagname -> get_name_test @ ('S2[G,F]) ==> Lf.
Proof.
  intros G F H; apply get_name_test_none; intros N HE; apply H.
  unfold name_test in HE; inversion HE; reflexivity.
Qed.

(** F-level type application always terminates: the clauses select a
    function of U without running any recursive call. *)
(** At S2[G,H] the ordinary clauses already form [rec @ G] and [rec @ H]
    ([star] lifts these U-free applications out of the clause). *)
Lemma default_total : forall AI rec F,
  (forall G H, F = 'S2[G,H] -> (exists f, rec @ G ==> f) /\ (exists f, rec @ H ==> f)) ->
  exists w, default_body AI @ rec @r F ==> w.
Proof.
 Local Transparent type_app_stem type_app_S.
 intros AI rec F Hrec; destruct F as [|G|[|G|F0 F1] H].
 - eexists; apply default_leaf.
 - assert (Hv : exists v, type_app_stem AI @ rec @r G ==> v)
     by (pose proof (function_abstractor_partial rec); eexists; unfold type_app_stem; cbn; repeat first [eassumption | progress evaluate]).
   destruct Hv as [v Hv]; eexists; apply default_stem; exact Hv.
 - assert (Hv : exists v, type_app_K @ H ==> v) by (eexists; unfold type_app_K; evaluate).
   destruct Hv as [v Hv]; eexists; apply default_K; exact Hv.
 - destruct (Hrec G H eq_refl) as [[fg Hg] [fh Hh]].
   assert (Hv : exists v, type_app_S @ rec @r G @r H ==> v)
     by (eexists; unfold type_app_S; cbn; repeat first [eassumption|progress evaluate]).
   destruct Hv as [v Hv]; eexists; apply default_S; exact Hv.
 - destruct (default_triage_agree AI rec F0 F1 H) as [w [_ Hw]]; eexists; exact Hw.
 Local Opaque type_app_stem type_app_S.
Qed.

Lemma app_head_from : forall AI F,
  (forall G H, F = 'S2[G,H] ->
     (exists f, app AI @ G ==> f) /\ (exists f, app AI @ H ==> f)) ->
  exists f, app AI @ F ==> f.
Proof.
 Local Transparent type_app.
 intros AI F Hrec; unfold type_app in *.
 destruct (tagged_decide F) as [[E [N ->]]|HP].
 - eexists; apply Z_unfold; apply body_abstract.
 - destruct (default_total AI (Z (body AI)) F Hrec) as [w Hw].
   eexists; apply Z_unfold; apply body_default_name;
     [apply abstract_case_plain; exact HP|exact Hw].
 Local Opaque type_app.
Qed.

Lemma app_head_total : forall AI F, exists f, app AI @ F ==> f.
Proof.
 intros AI F.
 assert (HQ : (exists f, app AI @ F ==> f) /\ (forall G, F = Sm G -> exists f, app AI @ G ==> f)).
 { induction F as [|G IHG|X IHX Y IHY].
   - split; [apply app_head_from; intros; discriminate|intros; discriminate].
   - split; [apply app_head_from; intros; discriminate|].
     intros G' E; inversion E; subst; exact (proj1 IHG).
   - split; [|intros; discriminate].
     apply app_head_from; intros G H E; inversion E; subst.
     split; [exact (proj2 IHX G eq_refl)|exact (proj1 IHY)]. }
 exact (proj1 HQ).
Qed.


Ltac reject_name := first [apply get_name_test_S_right;discriminate | solve [name_failure]].
Ltac new_S ::= eapply app_S;[|reject_name| | |].

Lemma type_app_wait : forall AI M N U V R,
 typing.type_app AI @ M @r N ==> Sm V -> typing.type_app AI @ V @r U ==> R ->
 typing.type_app AI @ ('wait[M,N]) @r U ==> R.
Proof.
 intros;new_S;[discriminate| |apply app_I|eassumption].
 new_S;[discriminate|apply app_K|apply app_K|eassumption].
Qed.


Local Ltac case_run := first [eassumption | apply equal1_eq |
 evaluate_expr_core case_run case_run_head | idtac]
with case_run_head := first [eassumption | apply equal1_eq | evaluate_head_core case_run | idtac].
Lemma app_abstract_head : forall AI E N,
 app AI @ 'tagged[E,N] ==> 'wait[E, app AI].
Proof.
 Local Transparent app.
 intros AI E N; apply Z_unfold; apply body_abstract.
 Local Opaque app.
Qed.

Lemma app_abstract_inv : forall AI E N U R,
 app AI @ 'tagged[E,N] @r U ==> R -> E @ app AI @r U ==> R.
Proof.
 intros AI E N U R H.
 destruct (eval_app_r_inv _ _ _ H) as [f [Hf Hr]].
 pose proof (eval_deterministic _ _ Hf _ (app_abstract_head AI E N)) as ->.
 apply wait_eval_inv; exact Hr.
Qed.

Local Opaque get_tagname get_tagged type_app_stem.
Local Opaque extend_program.
Lemma app_plain_inv : forall AI C U V,
 abstract_case @ C ==> Lf -> app AI @ C @r U ==> Sm V ->
 default_body AI @ app AI @r C @r U ==> Sm V.
Proof.
 intros AI C U V HA H.
 destruct (eval_app_r_inv _ _ _ H) as [s [Hs Ha]].
 pose proof (Z_unfold_inv _ _ _ Hs) as Hb; clear H Hs.
 destruct (body_inv _ _ _ _ Hb) as [[E [N [-> ->]]]|[_ HD]].
 - pose proof (eval_deterministic _ _ HA _ (abstract_case_tagged E N)); discriminate.
 - eapply eval_appl; [exact HD|exact Ha].
Qed.

(** The head of an application of type application to a function type
    that is not tagged is the partial application of the default clauses.
    Used by the height-indexed inversions of soundness.v. *)


Lemma default_triage_inv : forall AI rec F0 F1 F2 U V,
 default_body AI @ rec @r ('triage[F0,F1,F2]) @r U ==> Sm V ->
 triage_case @ rec @r F0 @r F1 @r F2 @r U ==> Sm V.
Proof.
 intros AI rec F0 F1 F2 U V H.
 destruct (eval_app_r_inv _ _ _ H) as [w [Hw HR]].
 eapply eval_appl; [apply (proj1 (default_triage_iff AI rec F0 F1 F2 w)); exact Hw|exact HR].
Qed.


Lemma triage_case_inv : forall rec F0 F1 F2 U V,
 triage_case @ rec @r F0 @r F1 @r F2 @r U ==> Sm V ->
 structural_triage rec F0 F1 F2 @ U ==> Sm V.
Proof.
 intros rec F0 F1 F2 U V H.
 destruct (eval_pair_inv _ _ _ H) as [h [u [HH [HU HR]]]]; inversion HU; subst u; clear HU.
 destruct (triage_case_head _ _ _ _ _ HH)
   as [[[E [N HE]] ->]|[HP ->]].
 - exfalso; exact (error_triage_not_some _ _ HR).
 - exact (proj2 (structural_triage_plain rec F0 F1 F2 U _ HP) HR).
Qed.

Local Transparent structural_fork.
Lemma structural_fork_inv : forall rec F2 X Y V,
  structural_fork rec F2 @ X @r Y ==> Sm V ->
  (forall E N, Fk X Y <> 'tagged[E,N]) /\
  exists G, rec @ F2 @r X ==> Sm G /\ rec @ G @r Y ==> Sm V.
Proof.
  intros rec F2 X Y V H.
  destruct (tagged_decide (Fk X Y)) as [[E [N HE]]|Hplain].
  - assert (HF : structural_fork rec F2 @ X @r Y ==> Lf).
    { pose proof (get_tagged_some E N) as HG; rewrite <- HE in HG.
      unfold structural_fork; evaluate. }
    pose proof (eval_deterministic _ _ H _ HF); discriminate.
  - pose proof (get_tagged_none _ Hplain) as HG.
    split; [exact Hplain|].
    unfold structural_fork in H; invert_eval.
    all: match goal with HX : get_tagged @ _ ==> _ |- _ =>
      pose proof (eval_deterministic _ _ HX _ HG); clear HX; subst end.
    all: invert_eval.
    eexists; split; eauto using eval_appl.
Qed.

Local Opaque structural_fork.
Lemma structural_triage_inv : forall rec F0 F1 F2 U V,
  structural_triage rec F0 F1 F2 @ U ==> Sm V ->
  ((forall E N, Fk F0 F1 <> 'tagged[E,N]) /\
    ((U = Lf /\ V = F0) \/
     (exists N, U = Sm N /\ rec @ F1 @r N ==> Sm V))) \/
  (exists X Y G, U = Fk X Y /\
    (forall E N, Fk X Y <> 'tagged[E,N]) /\
    rec @ F2 @r X ==> Sm G /\ rec @ G @r Y ==> Sm V).
Proof.
  intros rec F0 F1 F2 U V H.
  destruct (tagged_decide (Fk F0 F1)) as [[E [N HE]]|Hplain].
  - exfalso; apply (structural_triage_error rec F0 F1 F2 E N U _ HE) in H.
    exact (error_triage_not_some _ _ H).
  - destruct U as [|N|X Y]; unfold structural_triage, plain_triage, error_triage in H; invert_eval.
    all: repeat match goal with HX : get_tagged @ _ ==> _ |- _ =>
      let HH := fresh "HH" in
      pose proof (eval_deterministic _ _ HX _ (get_tagged_none _ Hplain)) as HH;
      clear HX; inversion HH; subst; clear HH end.
    all: invert_eval.
    all: try solve [left; split; [exact Hplain|left; split;reflexivity]].
    all: try solve [left; split; [exact Hplain|right; eexists; split; [reflexivity|eauto using eval_appl]]].
    all: right.
    all: assert (HF : structural_fork rec F2 @ X @r Y ==> Sm V)
      by (eauto using eval_appl).
    all: destruct (structural_fork_inv _ _ _ _ _ HF) as [HP [G [HL HR]]].
    all: exists X,Y,G; repeat split; assumption || reflexivity.
Qed.


(** Remaining name-test and child-reconstruction application facts. *)
Lemma default_S_inv : forall AI rec G F U V,
 default_body AI @ rec @r ('S2[G,F]) @r U ==> Sm V ->
 exists VG VF, rec @ G @r U ==> Sm VG /\
   rec @ F @r U ==> Sm VF /\ rec @ VG @r VF ==> Sm V.
Proof.
 intros AI rec G F U V H.
 destruct (eval_app_r_inv _ _ _ H) as [w [Hw HR]].
 apply default_S_head_inv in Hw.
 pose proof (eval_appl _ _ _ _ _ Hw HR) as H'; clear H Hw HR.
 Local Transparent type_app_S.
 unfold type_app_S in H'; cbn in H'; invert_eval.
 Local Opaque type_app_S.
 do 2 eexists; repeat split; eauto 8 using eval_appl.
Qed.


Lemma app_Update : forall AI U, app AI @ ('Update) @r U ==> Sm U.
Proof. intros; apply typing.app_abstract; apply update_eliminator_eval. Qed.

Lemma app_update_stem : forall AI X,
 app AI @ (Lf 'C ('Update)) @r X ==> Sm (Sm X).
Proof.
 intros; eapply typing.app_compose;[solve [reject_name]|discriminate|apply app_Update|apply typing.app_leaf].
Qed.

Lemma app_update_fork_first : forall AI X,
 app AI @ update_fork ('Update) @r X ==> Sm ('S2['K1 (Sm X),'Update]).
Proof.
 intros; unfold update_fork.
 repeat first [apply app_Update | new_S; [solve[intros;discriminate]| | |] |
 apply typing.app_K | apply typing.app_leaf | apply typing.app_stem; apply type_app_stem_structural; intros; discriminate].
Qed.

Lemma app_update_fork_second : forall AI X Y U,
 app AI @ Sm X @r Y ==> Sm U ->
 app AI @ ('S2['K1 (Sm X),'Update]) @r Y ==> Sm U.
Proof.
 intros; new_S; [discriminate|apply typing.app_K|apply app_Update|assumption].
Qed.


(** Structural typing of a triage: whenever the structural clauses give a
    result, type application gives the same result. *)
Lemma app_triage_structural : forall AI F0 F1 F2 U V,
  structural_triage (app AI) F0 F1 F2 @ U ==> Sm V ->
  app AI @ 'triage[F0,F1,F2] @r U ==> Sm V.
Proof.
  intros AI F0 F1 F2 U V H.
  apply app_default; [apply abstract_case_triage_none|apply get_name_test_triage_none|].
  apply default_triage; apply triage_structural; exact H.
Qed.

(** A one-level query type is an ordinary triage type, which gives [B] at
    every argument type that is not tagged; at a tagged (abstract)
    argument type plain triage refuses.  The one-level query is a value of
    the Query family, sound for values ([query_one_level_value_typing]). *)
Lemma installed_traversal : forall AI B U,
  (forall E N, U <> 'tagged[E,N]) ->
  app AI @ query_one_level B @r U ==> Sm B.
Proof.
  intros AI B U HU; unfold query_one_level; apply app_triage_structural.
  assert (HP : forall E N, Fk B ('Query[B]) <> 'tagged[E,N]) by (intros; discriminate).
  apply (proj2 (structural_triage_plain _ _ _ _ _ _ HP)).
  assert (HQ : forall N, app AI @ ('Query[B]) @r N ==> Sm B)
    by (intros; apply app_abstract; apply query_eliminator_eval).
  assert (HQQ : forall N, app AI @ ('Query['Query[B]]) @r N ==> Sm ('Query[B]))
    by (intros; apply app_abstract; apply query_eliminator_eval).
  Local Transparent structural_fork.
  destruct U as [|X|X Y]; unfold plain_triage.
  - evaluate.
  - destruct (eval_app_r_inv _ _ _ (HQ X)) as [h [Hh HX]].
    repeat first [eassumption | apply wait_eval | progress evaluate].
  - pose proof (get_tagged_none _ HU) as HG.
    destruct (eval_app_r_inv _ _ _ (HQQ X)) as [h1 [Hh1 HX1]].
    destruct (eval_app_r_inv _ _ _ (HQ Y)) as [h2 [Hh2 HX2]].
    unfold structural_fork; repeat first [eassumption | apply wait_eval | progress evaluate].
  Local Opaque structural_fork.
Qed.


Unset Default Proof Using.
Transparent equal function_abstractor_core equal1 get_funty get_wait get_tagname get_tagged is_concrete query_handler structural_fork payload_eliminator get_wrap_payload_type get_name_test default_body abstract_case app extend_program type_app_stem type_app_S triage_case.

(**********************************************************************)
(* Copyright 2026 Barry Jay                                           *)
(*                                                                    *)
(* Permission is hereby granted, free of charge, to any person        *)
(* obtaining a copy of this software and associated documentation     *)
(* files (the "Software"), to deal in the Software without            *)
(* restriction, including without limitation the rights to use, copy, *)
(* modify, merge, publish, distribute, sublicense, and/or sell copies *)
(* of the Software, and to permit persons to whom the Software is     *)
(* furnished to do so, subject to the following conditions:           *)
(*                                                                    *)
(* The above copyright notice and this permission notice shall be     *)
(* included in all copies or substantial portions of the Software.    *)
(*                                                                    *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    *)
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *)
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *)
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        *)
(* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       *)
(* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, *)
(* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      *)
(* DEALINGS IN THE SOFTWARE.                                          *)
(**********************************************************************)

(**********************************************************************)
(*                        Type Systems                                *)
(*                                                                    *)
(*                         Barry Jay                                  *)
(**********************************************************************)

(** Value inference recursively mirrors tree structure and uses [type_app]
    at every fork. An explicit tag is checked by the stem branch after
    its carrier and name have themselves been inferred. Tag proposals are
    dispatched to the core function checker or the callback-free [AI]. *)

From Stdlib Require Import Bool String.
From Stdlib Require Import Program.Equality.
From TreeTyping Require Import tree.
Import ClauseNotation.

Set Default Proof Using "Type".
Open Scope nat_scope.
Open Scope string_scope.


(** * Tag-free combinations

    A combination is tag-free when no subtree has the reserved shape of an
    ordinary tag.  This hereditary semantic criterion includes raw analysis
    programs and replaces the earlier, narrower inductive grammar. *)

(** Fix the declarations within this file. Section discharge restores the
    exported parameters; local notation specialises imported definitions. *)
Section ValueInference.
Variable AI : Combination.
Local Abbreviation type_app := (typing.type_app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).

(** 2. Type inference for programs and expressions
    Soundness of type inference will require
    soundness of AI when typing tagged terms only. 
 *) 

(** Combine the inferred types of a value fork's immediate children.
    Successful results [Sm U] and [Sm V] are combined by [Sm U # V].
    The stem is constructed on the type; inference never recurses on an
    artificially constructed [Sm u]. Non-stem results give failure. *)
Local Notation "x # y" := (Val type_app @@ x @@ y)
  (in custom clause at level 20, left associativity).
(** let Sm U1 = _ and Sm U2 = _ in (Sm U1) # U2, as a function of the two
    results ([success2] compiled in place). *)
Definition infer_fork_results_package :
  { t : Combination |
    to_tree <{ fun Sm "U1" , Sm "U2" => (Sm "U1") # "U2" }> = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition infer_fork_results : Combination :=
  Eval cbn in proj1_sig infer_fork_results_package.

(** This specification includes failures and arbitrary application results. *)
Lemma infer_fork_results_spec : forall a b R,
  infer_fork_results @ a @r b ==> R <->
  match a, b with
  | Sm U, Sm V => type_app @ Sm U @r V ==> R
  | _, _ => R = Lf
  end.
Proof.
  intros a b R.
  destruct a as [|U|a1 a2].
  - unfold infer_fork_results; cbn; split; intros; subst; invert_eval; evaluate.
  - assert (Hprobe : type_app @ Sm U @r Lf ==> Sm (Fk U Lf)).
    { apply typing.type_app_stem_ev; apply type_app_stem_structural.
      intros C N H; discriminate H. }
    inv_out Hprobe.
    destruct b as [|V|b1 b2]; unfold infer_fork_results; cbn;
      split; intros; subst; invert_eval; evaluate.
  - unfold infer_fork_results; cbn; split; intros; subst; invert_eval; evaluate.
Qed.

(** infer = | Lf       => Sm Lf
            | Sm u     => let Sm U = infer @ u in Sm (Sm U)
            | Fk u1 u2 => let Sm U1 = infer @ u1 in
                          let Sm U2 = infer @ u2 in (Sm U1) # U2
    As compiled, [infer @ u2] does not mention U1, so [star] lifts it out
    of the first let: both children are inferred before either result is
    tested; then [type_app @ Sm U1] is formed and, if U2 is a success,
    applied to U2. *)
Definition infer_body_package :
  { t |
    to_tree <{
      fun "infer" =>
        shape
        | Lf => (Sm Lf)
        | Sm "u" => let Sm "U" = "infer" @ "u" in (Sm (Sm "U"))
        | Fk "u1" "u2" =>
            let Sm "U1" = "infer" @ "u1" in
            let Sm "U2" = "infer" @ "u2" in (Sm "U1") # "U2"
        end }> = t}.
 Proof. eexists; simpl; reflexivity. Defined.

 Definition infer_body :=
  Eval cbn in proj1_sig infer_body_package.

Definition infer  :=  Z infer_body.


Local Notation "F # U" := (type_app @ F @r U)
                      (at level 45, left associativity).

(* type inference for programs *) 

Lemma infer_leaf : infer @ Lf ==> Sm Lf.
Proof. eapply Z_unfold; unfold infer_body at 1; evaluate. Qed.

Lemma infer_stem :
  forall u U,
    infer @ u ==> Sm U ->
    infer @ Sm u ==> Sm (Sm U).
Proof.
  intros u U Hu.
  assert (Lf # U ==> Sm (Sm U))
    by eapply typing.type_app_leaf_ev.
  change (Z infer_body @ Sm u ==> Sm (Sm U)).
  eapply Z_unfold.
  unfold infer_body; evaluate2; evaluate.
Qed.


Lemma infer_fork_gen_inv : forall u1 u2 R,
  infer @ Fk u1 u2 ==> R ->
  exists a b, infer @ u1 ==> a /\ infer @ u2 ==> b /\ infer_fork_results @ a @r b ==> R.
Proof.
  intros u1 u2 R H; apply Z_unfold_inv in H; unfold infer_body in H; invert_eval.
  all: do 2 eexists; split; [eauto using eval_appl|split; [eauto using eval_appl|]].
  all: apply infer_fork_results_spec; cbn; first [reflexivity|eauto using eval_appl].
Qed.
Lemma infer_fork_gen : forall u1 u2 a b R,
  infer @ u1 ==> a -> infer @ u2 ==> b -> infer_fork_results @ a @r b ==> R ->
  infer @ Fk u1 u2 ==> R.
Proof.
  intros u1 u2 a b R Ha Hb HR; apply infer_fork_results_spec in HR.
  apply Z_unfold; unfold infer_body at 1.
  destruct a as [|U1|a1 a2]; [subst R|destruct (app_head_total AI (Sm U1)) as [f Hf]|subst R].
  1,3: repeat first [eassumption|progress evaluate].
  destruct b as [|U2|b1 b2]; [subst R| |subst R].
  1,3: repeat first [eassumption|progress evaluate].
  destruct (eval_app_r_inv _ _ _ HR) as [f' [Hf' HR']]; clear Hf.
  repeat first [eassumption|progress evaluate].
Qed.


Lemma infer_fork :
  forall u1 u2 U1 U2 R,
    infer @ u1 ==> Sm U1 ->
    infer @ u2 ==> Sm U2 ->
    Sm U1 # U2 ==> R ->
    infer @ Fk u1 u2 ==> R.
Proof.
  intros u1 u2 U1 U2 R H1 H2 HR.
  eapply infer_fork_gen; [exact H1|exact H2|].
  apply infer_fork_results_spec; exact HR.
Qed.

Local Lemma infer_fork_results_inv :
  forall v1 v2 T,
    infer_fork_results @ v1 @r v2 ==> Sm T ->
    exists U1 U2,
      v1 = Sm U1 /\
      v2 = Sm U2 /\
      type_app @ Sm U1 @r U2 ==> Sm T.
Proof.
  intros v1 v2 T H.
  destruct v1 as [|U1|u11 u12];
    destruct v2 as [|U2|u21 u22];
    try (unfold infer_fork_results in H; cbn in H; invert_eval).
  exists U1, U2; repeat split; try reflexivity.
  evaluate.   
Qed.

Lemma infer_stem_inv :
  forall u T,
    infer @ Sm u ==> Sm T ->
    exists U, T = Sm U /\ infer @ u ==> Sm U.
Proof.
  intros u T H.
  assert (infer_body @ infer @r Sm u ==> Sm T)
    by (eapply Z_unfold_inv; exact H).
  invert_eval; inv_out H5; invert_eval; evaluate; eauto.
Qed.

Lemma infer_fork_inv :
  forall u1 u2 T,
    infer @ Fk u1 u2 ==> Sm T ->
    exists U1 U2,
      infer @ u1 ==> Sm U1 /\
      infer @ u2 ==> Sm U2 /\
      type_app @ Sm U1 @r U2 ==> Sm T.
Proof.
  intros u1 u2 T H.
  destruct (infer_fork_gen_inv _ _ _ H) as [v2 [v4 [H1 [H2 Hsuccess]]]].
  destruct (infer_fork_results_inv _ _ _ Hsuccess)
    as [U1 [U2 [-> [-> Htype_app]]]].
  exists U1, U2; repeat split; auto.
Qed.


Lemma infer_K1 :
  forall u U,
    infer @ u ==> Sm U ->
    infer @ ('K1 u) ==> Sm ('K1 U).
Proof.
  intros u U Hu.
  eapply infer_fork.
  - eapply infer_leaf.
  - exact Hu.
  - eapply typing.type_app_stem_ev; eapply type_app_stem_structural;
      intros; discriminate.
Qed.

Lemma infer_tag_free :
  forall c,
    tag_free c = true ->
    infer @ c ==> Sm c.
Proof.
  intros c; induction c as [|u IH|u IHu v IHv]; cbn; intro H.
  - apply infer_leaf.
  - apply infer_stem; auto.
  - apply andb_true_iff in H; destruct H as [Huv Hv].
    apply andb_true_iff in Huv; destruct Huv as [Hnot Hu].
    eapply infer_fork; [apply IHu; exact Hu|apply IHv; exact Hv|].
    apply typing.type_app_stem_ev; apply type_app_stem_structural.
    intros E N Heq.
    change (negb (reserved_tagb (Fk u v)) = true) in Hnot.
    rewrite Heq, reserved_tagb_tagged in Hnot; discriminate.
Qed.


(** Explicit tags are inferred through the same stem branch used by
    fork introduction.  The source payload and name are inferred first; the
    prospective tagged type is then submitted to [AI]. *)
Lemma infer_tagged :
  forall f F n N T,
    infer @ f ==> Sm F ->
    infer @ n ==> Sm N ->
    AI @ N @r type_app @r F ==> Sm T ->
    infer @ 'tagged[f,n] ==> Sm ('tagged[T,N]).
Proof.
  intros f F n N T Hf Hn Hadapt.
  eapply infer_fork.
  - eapply infer_stem.
    eapply infer_K1; exact Hf.
  - eapply infer_fork.
    + eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    + eapply infer_K1; exact Hn.
    + eapply typing.type_app_stem_ev; eapply type_app_stem_structural;
        intros; discriminate.
  - eapply typing.type_app_stem_ev.
    eapply type_app_stem_tagged; eauto.
Qed.

(** Inversion of inference for a tagged value of any abstract family. *)
Lemma infer_tagged_inv : forall f n E N,
  infer @ 'tagged[f,n] ==> Sm ('tagged[E,N]) ->
  exists F,
    infer @ f ==> Sm F /\
    infer @ n ==> Sm N /\
    AI @ N @r type_app @r F ==> Sm E.
Proof.
  intros f n E N Htagged.
  destruct (infer_fork_inv _ _ _ Htagged)
    as [left_ty [right_ty [Hleft [Hright Houter]]]].
  destruct (infer_stem_inv _ _ Hleft)
    as [fun_ty [Hleft_ty Hfun]]; subst left_ty.
  destruct (infer_fork_inv _ _ _ Hfun)
    as [leaf_ty [F [Hleaf [Hf Hfun_app]]]].
  assert (Hfun_canonical :
    infer @ ('K1 f) ==> Sm ('K1 F))
    by (eapply infer_K1; exact Hf).
  pose proof
    (eval_deterministic _ _ Hfun _ Hfun_canonical) as Hfun_eq.
  inversion Hfun_eq; subst fun_ty.
  destruct (infer_fork_inv _ _ _ Hright)
    as [K_ty [kn_ty [HK [Hkn Hright_app]]]].
  destruct (infer_fork_inv _ _ _ Hkn)
    as [leaf_ty' [N0 [Hleaf' [Hn Hkn_app]]]].
  assert (Hright_canonical :
    infer @ ('S2['K,'K1 n]) ==> Sm ('S2['K,'K1 N0])).
  { eapply infer_fork.
    - eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    - eapply infer_K1; exact Hn.
    - eapply typing.type_app_stem_ev; eapply type_app_stem_structural; discriminate. }
  pose proof
    (eval_deterministic _ _ Hright _ Hright_canonical) as Hright_eq.
  inversion Hright_eq; subst right_ty.
  assert (Hadapt :
    type_app_stem @ type_app @r (Sm ('K1 (F))) @r ('S2['K,'K1 (N0)]) ==>
      Sm ('tagged[E,N]))
    by (eapply typing.type_app_stem_inv; exact Houter).
  assert (Hname : N0 = N).
  { destruct (type_app_stem_tagged_success_inv AI type_app F N0
      ('tagged[E,N]) Hadapt) as [Eshape [_ Hshape]].
    inversion Hshape; reflexivity. }
  subst N0.
  destruct (type_app_stem_tagged_success_inv
    AI type_app F N ('tagged[E,N]) Hadapt)
    as [E1 [Hintro Heq]].
  inversion Heq; subst E1.
  exists F; split; [exact Hf |].
  split; [exact Hn | exact Hintro].
Qed.

(** Paper-facing: every typable abstract program (one tagged at the head)
    has an abstract type carrying the type of the program's nametag. *)
Lemma abstract_has_abstract_type : forall f n T,
  infer @ 'tagged[f,n] ==> Sm T ->
  exists E N, T = 'tagged[E,N] /\ infer @ n ==> Sm N.
Proof.
  intros f n T Htagged.
  destruct (infer_fork_inv _ _ _ Htagged)
    as [left_ty [right_ty [Hleft [Hright Houter]]]].
  destruct (infer_stem_inv _ _ Hleft)
    as [fun_ty [Hleft_ty Hfun]]; subst left_ty.
  destruct (infer_fork_inv _ _ _ Hfun)
    as [leaf_ty [F [Hleaf [Hf Hfun_app]]]].
  pose proof (eval_deterministic _ _ Hfun _ (infer_K1 _ _ Hf)) as Hfun_eq.
  inversion Hfun_eq; subst fun_ty.
  destruct (infer_fork_inv _ _ _ Hright)
    as [K_ty [kn_ty [HK [Hkn Hright_app]]]].
  destruct (infer_fork_inv _ _ _ Hkn)
    as [leaf_ty' [N [Hleaf' [Hn Hkn_app]]]].
  assert (Hright_canonical :
    infer @ ('S2['K,'K1 n]) ==> Sm ('S2['K,'K1 N])).
  { eapply infer_fork.
    - eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    - eapply infer_K1; exact Hn.
    - eapply typing.type_app_stem_ev; eapply type_app_stem_structural; discriminate. }
  pose proof
    (eval_deterministic _ _ Hright _ Hright_canonical) as Hright_eq.
  inversion Hright_eq; subst right_ty.
  assert (Hadapt :
    type_app_stem @ type_app @r (Sm ('K1 F)) @r ('S2['K,'K1 N]) ==> Sm T)
    by (eapply typing.type_app_stem_inv; exact Houter).
  destruct (type_app_stem_tagged_success_inv AI type_app F N T Hadapt)
    as [E [_ ->]].
  exists E, N; split; [reflexivity | exact Hn].
Qed.

Lemma infer_tag_free_inv : forall u c,
  infer @ u ==> Sm c ->
  tag_free c = true ->
  u = c.
Proof.
  induction u as [|u IHu|u1 IHu1 u2 IHu2]; intros c Hinfer Htag_free.
  - assert (Heq : Sm c = Sm Lf)
      by (eapply eval_deterministic; [exact Hinfer | apply infer_leaf]).
    inversion Heq; reflexivity.
  - destruct (infer_stem_inv _ _ Hinfer) as [U [-> Hu]].
    cbn in Htag_free.
    f_equal; eapply IHu; eauto.
  - destruct (infer_fork_inv _ _ _ Hinfer)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt :
      type_app_stem @ type_app @r U1 @r U2 ==> Sm c)
      by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk U1 U2))
      as [[E [N Htagged]] | Hnot_tagged].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E N c Hadapt)
        as [E' [_ ->]].
      vm_compute in Htag_free; discriminate.
    + assert (Heq : c = Fk U1 U2).
      { eapply (type_app_stem_structural_inv AI type_app); eauto. }
      subst c; cbn in Htag_free.
      apply andb_true_iff in Htag_free; destruct Htag_free as [Hleft Hu2c].
      apply andb_true_iff in Hleft; destruct Hleft as [_ Hu1c].
      f_equal.
      * eapply IHu1; eauto.
      * eapply IHu2; eauto.
Qed.


Lemma infer_stem_result_inv : forall u T,
  infer @ u ==> Sm (Sm T) ->
  exists t, u = Sm t /\ infer @ t ==> Sm T.
Proof.
  intros [|t|u1 u2] T H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf) as Heq.
    discriminate Heq.
  - destruct (infer_stem_inv _ _ H) as [U [Heq Hu]].
    inversion Heq; subst U; eauto.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt : type_app_stem @ type_app @r U1 @r U2 ==> Sm (Sm T))
      by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk U1 U2))
      as [[E [N Htagged]] | Hplain].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E N (Sm T) Hadapt)
        as [E' [_ Heq]]; discriminate Heq.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 (Sm T) Hplain Hadapt) as Heq.
      discriminate Heq.
Qed.

Lemma infer_K1_inv : forall u F,
  infer @ u ==> Sm ('K1 F) ->
  exists f, u = 'K1 f /\ infer @ f ==> Sm F.
Proof.
  intros [|t|u1 u2] F H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf) as Heq.
    discriminate Heq.
  - destruct (infer_stem_inv _ _ H) as [U [Heq _]].
    discriminate Heq.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt : type_app_stem @ type_app @r U1 @r U2 ==> Sm ('K1 F))
      by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk U1 U2))
      as [[E [N Htagged]] | Hplain].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E N ('K1 F) Hadapt)
        as [E' [_ Heq]]; discriminate Heq.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 ('K1 F) Hplain Hadapt) as Heq.
      inversion Heq; subst U1 U2.
      assert (Hu1_shape : u1 = Lf)
        by (eapply infer_tag_free_inv; [exact Hu1 | tag_free_tac]).
      subst u1; exists u2; split; [reflexivity | exact Hu2].
Qed.

(** Source-directed inversion also discovers the result type.  This form is
    useful when a constructor occurs inside a larger typed computation and
    its component types are not known in advance. *)
Lemma infer_K1_result_inv : forall u T,
  infer @ ('K1 u) ==> Sm T ->
  exists U,
    T = 'K1 U /\
    infer @ u ==> Sm U.
Proof.
  intros u T H.
  destruct (infer_fork_inv _ _ _ H)
    as [U1 [U [Hleaf [Hu Happ]]]].
  assert (HU1 : U1 = Lf).
  { pose proof (eval_deterministic _ _ Hleaf _ infer_leaf) as Heq.
    inversion Heq; reflexivity. }
  subst U1.
  assert (Hadapt :
    type_app_stem @ type_app @r Lf @r U ==> Sm T).
  { eapply typing.type_app_stem_inv; exact Happ. }
  assert (Hplain : forall E N, 'K1 U <> 'tagged[E,N])
    by (intros; discriminate).
  pose proof
    ((type_app_stem_structural_inv AI type_app) Lf U T Hplain Hadapt) as Heq.
  exists U; split; [exact Heq | exact Hu].
Qed.

Lemma infer_tag_right_inv : forall u N,
  infer @ u ==> Sm ('S2['K,'K1 N]) ->
  exists n, u = 'S2['K,'K1 n] /\ infer @ n ==> Sm N.
Proof.
  intros [|t|u1 u2] N H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf) as Heq.
    discriminate Heq.
  - destruct (infer_stem_inv _ _ H) as [U [Heq _]].
    discriminate Heq.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt :
      type_app_stem @ type_app @r U1 @r U2 ==>
        Sm ('S2['K,'K1 N]))
      by (eapply typing.type_app_stem_inv; exact Happ).
    assert (Htarget_plain :
      forall E name, 'S2['K,'K1 N] <> 'tagged[E,name])
      by (intros; discriminate).
    destruct (tagged_decide (Fk U1 U2))
      as [[E [name Htagged]] | Hplain].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E name
        ('S2['K,'K1 N]) Hadapt) as [E' [_ Heq]].
      exfalso; eapply Htarget_plain; exact Heq.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 ('S2['K,'K1 N]) Hplain Hadapt)
          as Heq.
      inversion Heq; subst U1 U2.
      assert (Hu1_shape : u1 = Sm 'K).
      { eapply infer_tag_free_inv; [exact Hu1 | tag_free_tac]. }
      subst u1.
      destruct (infer_K1_inv u2 N Hu2) as [n [-> Hn]].
      exists n; split; [reflexivity | exact Hn].
Qed.

Lemma infer_S2_K1_inv : forall u g N,
  tag_free g = true ->
  (forall E, g <> 'K1 E) ->
  infer @ u ==> Sm ('S2[g,'K1 N]) ->
  exists n, u = 'S2[g,'K1 n] /\ infer @ n ==> Sm N.
Proof.
  intros [|t|u1 u2] g N Hg HnotK H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf) as Heq.
    discriminate Heq.
  - destruct (infer_stem_inv _ _ H) as [U [Heq _]].
    discriminate Heq.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt : type_app_stem @ type_app @r U1 @r U2 ==>
      Sm ('S2[g,'K1 N]))
      by (eapply typing.type_app_stem_inv; exact Happ).
    assert (Htarget_plain :
      forall E name, 'S2[g,'K1 N] <> 'tagged[E,name]).
    { intros; discriminate. }
    destruct (tagged_decide (Fk U1 U2))
      as [[E [name Htagged]] | Hplain].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E name
        ('S2[g,'K1 N]) Hadapt) as [E' [_ Heq]].
      exfalso; eapply Htarget_plain; exact Heq.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 ('S2[g,'K1 N]) Hplain Hadapt)
          as Heq.
      inversion Heq; subst U1 U2.
      assert (Hu1_shape : u1 = Sm g).
      { eapply infer_tag_free_inv; [exact Hu1 | cbn; exact Hg]. }
      subst u1.
      destruct (infer_K1_inv u2 N Hu2) as [n [-> Hn]].
      exists n; split; [reflexivity | exact Hn].
Qed.

(** Syntax-directed inversion for an ordinary [S2] type.  The side
    condition excludes the [S2] shape reserved for abstract types. *)
Lemma infer_S2_inv : forall u G F,
  (forall E N, 'S2[G,F] <> 'tagged[E,N]) ->
  infer @ u ==> Sm ('S2[G,F]) ->
  exists g f,
    u = 'S2[g,f] /\
    infer @ g ==> Sm G /\
    infer @ f ==> Sm F.
Proof.
  intros [|t|u1 u2] G F Hnot_tagged H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf); discriminate.
  - destruct (infer_stem_inv _ _ H) as [U [Heq _]]; discriminate Heq.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt : type_app_stem @ type_app @r U1 @r U2 ==>
      Sm ('S2[G,F])) by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk U1 U2))
      as [[E [N Htagged]] | Hplain].
    + inversion Htagged; subst U1 U2.
      destruct (type_app_stem_tagged_success_inv AI type_app E N
        ('S2[G,F]) Hadapt) as [E' [_ Heq]].
      exfalso; eapply Hnot_tagged; exact Heq.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 ('S2[G,F]) Hplain Hadapt) as Heq.
      inversion Heq; subst U1 U2.
      destruct (infer_stem_result_inv u1 G Hu1) as [g [-> Hg]].
      exists g, u2; repeat split; assumption.
Qed.

Lemma infer_decorate_inv : forall u F U,
  infer @ u ==> Sm ('decorate[F,U]) ->
  exists f d,
    u = 'decorate[f,d] /\
    infer @ f ==> Sm F /\
    infer @ d ==> Sm U.
Proof.
  intros u F U H.
  destruct (infer_S2_inv u
    ('S2['K1 ('K1 F),'K1 U]) 'I ltac:(intros; discriminate) H)
    as [g [i [-> [Hg Hi]]]].
  assert (i = 'I).
  { eapply infer_tag_free_inv; [exact Hi | tag_free_tac]. }
  subst i.
  destruct (infer_S2_inv g ('K1 ('K1 F)) ('K1 U)
    ltac:(intros; discriminate) Hg)
    as [kf [ku [-> [Hkf Hku]]]].
  destruct (infer_K1_inv kf ('K1 F) Hkf) as [kf0 [-> Hkf0]].
  destruct (infer_K1_inv kf0 F Hkf0) as [f [-> Hf]].
  destruct (infer_K1_inv ku U Hku) as [d [-> Hd]].
  exists f, d; repeat split; assumption.
Qed.

(** Source-directed decoration inversion discovers both component types and
    the necessarily decorated result type. *)
Lemma infer_decorate_result_inv : forall f d T,
  infer @ 'decorate[f,d] ==> Sm T ->
  exists F U,
    T = 'decorate[F,U] /\
    infer @ f ==> Sm F /\
    infer @ d ==> Sm U.
Proof.
  intros f d T H.
  destruct (infer_fork_inv _ _ _ H)
    as [G [Ity [Hgstem [Hi Happ]]]].
  destruct (infer_stem_inv _ _ Hgstem) as [G0 [-> Hg]].
  assert (HIty : Ity = 'I).
  { assert (HI : infer @ 'I ==> Sm 'I).
    { eapply infer_tag_free; tag_free_tac. }
    pose proof (eval_deterministic _ _ Hi _ HI) as Heq.
    inversion Heq; reflexivity. }
  subst Ity.
  assert (Houter :
    type_app_stem @ type_app @r (Sm G0) @r 'I ==> Sm T).
  { eapply typing.type_app_stem_inv; exact Happ. }
  assert (Houter_plain : forall E N, 'S2[G0,'I] <> 'tagged[E,N])
    by (intros; discriminate).
  pose proof
    ((type_app_stem_structural_inv AI type_app) (Sm G0) 'I T Houter_plain Houter)
      as HT.
  destruct (infer_fork_inv _ _ _ Hg)
    as [KF [KU [Hkfstem [Hku Hinner_app]]]].
  destruct (infer_stem_inv _ _ Hkfstem) as [KF0 [-> Hkf]].
  destruct (infer_K1_result_inv _ _ Hkf) as [KF1 [-> Hkf1]].
  destruct (infer_K1_result_inv _ _ Hkf1) as [F [-> Hf]].
  destruct (infer_K1_result_inv _ _ Hku) as [U [-> Hd]].
  assert (Hinner :
    type_app_stem @ type_app @r (Sm ('K1 ('K1 F))) @r ('K1 U) ==> Sm G0).
  { eapply typing.type_app_stem_inv; exact Hinner_app. }
  assert (Hinner_plain :
    forall E N, 'S2['K1 ('K1 F),'K1 U] <> 'tagged[E,N])
    by (intros; discriminate).
  pose proof
    ((type_app_stem_structural_inv AI type_app)
      (Sm ('K1 ('K1 F))) ('K1 U) G0 Hinner_plain Hinner) as HG.
  subst G0.
  exists F, U; repeat split; assumption.
Qed.

Lemma infer_tagged_result_inv : forall u E N,
  infer @ u ==> Sm ('tagged[E,N]) ->
  exists f n F,
    u = 'tagged[f,n] /\
    infer @ f ==> Sm F /\
    infer @ n ==> Sm N /\
    AI @ N @r type_app @r F ==> Sm E.
Proof.
  intros [|t|u1 u2] E N H.
  - pose proof (eval_deterministic _ _ H _ infer_leaf) as Heq.
    discriminate Heq.
  - destruct (infer_stem_inv _ _ H) as [U [Heq _]].
    discriminate Heq.
  - destruct (infer_fork_inv _ _ _ H)
      as [U1 [U2 [Hu1 [Hu2 Happ]]]].
    assert (Hadapt :
      type_app_stem @ type_app @r U1 @r U2 ==> Sm ('tagged[E,N]))
      by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk U1 U2))
      as [[F [N0 Hproposal]] | Hplain].
    + inversion Hproposal; subst U1 U2.
      destruct (infer_stem_result_inv u1 ('K1 F) Hu1)
        as [kf [-> Hkf]].
      destruct (infer_K1_inv kf F Hkf) as [f [-> Hf]].
      destruct (infer_tag_right_inv u2 N0 Hu2) as [n [-> Hn]].
      assert (Hname : N0 = N).
      { destruct (type_app_stem_tagged_success_inv AI type_app F N0
          ('tagged[E,N]) Hadapt) as [E0 [_ Hshape]].
        inversion Hshape; reflexivity. }
      subst N0.
      destruct (infer_tagged_inv f n E N H)
        as [F0 [Hf0 [Hn0 Hintro]]].
      exists f, n, F0; repeat split; assumption.
    + pose proof
        ((type_app_stem_structural_inv AI type_app) U1 U2 ('tagged[E,N]) Hplain Hadapt)
          as Heq.
      inversion Heq; subst U1 U2.
      exfalso; eapply (Hplain E N); reflexivity.
Qed.

Lemma infer_I : infer @ 'I ==> Sm 'I.
Proof.
  eapply infer_tag_free; tag_free_tac.
Qed.


End ValueInference.

(** Routine inference for concrete applicative syntax. *)
Ltac infer_tac :=
  repeat first
  [ match goal with Hf : _ |- _ => exact Hf end
  | match goal with Hd : _ |- _ => exact Hd end
  | eapply infer_fork
  | eapply infer_stem
  | eapply infer_leaf
  | eapply infer_I
  | eapply typing.type_app_I
  | eapply typing.type_app_K_ev
  | eapply typing.type_app_stem_ev; eapply type_app_stem_structural;
    intros; discriminate
  | new_S; [intros; discriminate |]
  ].

(** Routine type application for the concrete S/K encodings generated by
    packages. *)
Ltac type_app_tac :=
  repeat first
  [ eassumption
  | eapply typing.type_app_I
  | new_S; [solve [intros; discriminate] | | |]
  | eapply typing.type_app_K_ev
  | eapply typing.type_app_stem_ev;
      eapply type_app_stem_structural; intros; discriminate
  | eapply typing.type_app_leaf_ev
  | eapply typing.type_app_abstract
  ].


(** Tactics above are exported outside sections. Resume the same fixed
    declarations for the remaining inference facts. *)
(** Concrete declarations are not themselves a label, so [Lf 'C AI] is plain. *)
Lemma concrete_ontology_plain : forall AI,
  concrete AI -> reserved_tagb (Lf 'C AI) = false.
Proof.
  intros AI HL.
  destruct (tagged_decide (Lf 'C AI)) as [[E [N HE]]|HN].
  - inversion HE; subst.
    apply concrete_iff_rules in HL.
    destruct HL as [Hb _]; exfalso; apply Hb; split; [reflexivity|eexists; reflexivity].
  - unfold reserved_tagb.
    repeat match goal with
    | |- context [match ?x with Lf => _ | Sm _ => _ | Fk _ _ => _ end] => destruct x
    end; try reflexivity; exfalso; eapply HN; reflexivity.
Qed.

Section ValueInferenceFacts.
Variable AI : Combination.
Local Abbreviation type_app := (typing.type_app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (infer AI).

(** Decorations are ordinary value-level structure. *)
Lemma infer_decorate : forall f F d U,
  infer @ f ==> Sm F ->
  infer @ d ==> Sm U ->
  infer @ 'decorate[f,d] ==> Sm ('decorate[F,U]).
Proof.
  intros f F d U Hf Hd.
  infer_tac.
Qed.

Lemma infer_Z :
  forall f F,
    infer @ f ==> Sm F ->
    infer @ Z f ==> Sm (Z F).
Proof.
  intros f F Hf.
  unfold Z.
  infer_tac.
Qed.


(** Raw equality and type inference themselves satisfy the semantic
    tag-freeness criterion. *)

Lemma equal_tag_free : tag_free equal = true.
Proof.
  Local Transparent equal Z. vm_compute; reflexivity. Local Opaque equal Z.
Qed.


Lemma infer_program_tag_free : tag_free AI = true -> reserved_tagb (Lf 'C AI) = false ->
  tag_free infer = true.
Proof.
  Local Transparent equal Z.
  intros HAI Hplain;
  unfold infer, infer_body, infer_fork_results, type_app, app,
    body, default_body, triage_case;
  unfold type_app_stem;
  vm_compute in HAI, Hplain |- *; repeat rewrite HAI; try rewrite Hplain; reflexivity.
Local Opaque equal Z.
Qed.


(** Used by [infer_self_typed] (self_typing.v). *)
Lemma infer_concrete_self_typed : concrete AI ->
  infer @ infer ==> Sm infer.
Proof.
  intros HL; apply infer_tag_free.
  apply infer_program_tag_free;
    [apply concrete_tag_free; exact HL|apply concrete_ontology_plain; exact HL].
Qed.


Set Default Proof Using "Type".
Lemma infer_tagged_source_inv : forall f n R,
  infer @ 'tagged[f,n] ==> Sm R ->
  exists C N E, R = 'tagged[E,N] /\
    infer @ f ==> Sm C /\ infer @ n ==> Sm N /\
    AI @ N @r type_app @r C ==> Sm E.
Proof.
  intros f n R Htagged.
  destruct (infer_fork_inv AI _ _ _ Htagged)
    as [left_ty [right_ty [Hleft [Hright Houter]]]].
  destruct (infer_stem_inv AI _ _ Hleft)
    as [fun_ty [Hleft_ty Hfun]]; subst left_ty.
  destruct (infer_fork_inv AI _ _ _ Hfun)
    as [leaf_ty [F [Hleaf [Hf Hfun_app]]]].
  assert (Hfun_canonical :
    infer @ ('K1 f) ==> Sm ('K1 F))
    by (eapply infer_K1; exact Hf).
  pose proof
    (eval_deterministic _ _ Hfun _ Hfun_canonical) as Hfun_eq.
  inversion Hfun_eq; subst fun_ty.
  destruct (infer_fork_inv AI _ _ _ Hright)
    as [K_ty [kn_ty [HK [Hkn Hright_app]]]].
  destruct (infer_fork_inv AI _ _ _ Hkn)
    as [leaf_ty' [N0 [Hleaf' [Hn Hkn_app]]]].
  assert (Hright_canonical :
    infer @ ('S2['K,'K1 n]) ==> Sm ('S2['K,'K1 N0])).
  { eapply infer_fork.
    - eapply infer_stem.
      eapply infer_tag_free; tag_free_tac.
    - eapply infer_K1; exact Hn.
    - eapply typing.type_app_stem_ev; eapply type_app_stem_structural; discriminate. }
  pose proof
    (eval_deterministic _ _ Hright _ Hright_canonical) as Hright_eq.
  inversion Hright_eq; subst right_ty.
  assert (Hadapt :
    type_app_stem @ type_app @r (Sm ('K1 (F))) @r ('S2['K,'K1 (N0)]) ==>
      Sm R)
    by (eapply typing.type_app_stem_inv; exact Houter).
  destruct (type_app_stem_tagged_success_inv AI type_app F N0 R Hadapt)
    as [E [Hintro ->]].
  exists F,N0,E; repeat split; assumption.
Qed.

Lemma infer_plain_fork_inv : forall u L R,
  (forall E N, Fk L R <> 'tagged[E,N]) ->
  infer @ u ==> Sm (Fk L R) ->
  exists l r, u = Fk l r /\ infer @ l ==> Sm L /\ infer @ r ==> Sm R.
Proof.
  intros [|t|l r] L R Hnot H.
  - pose proof (eval_deterministic _ _ H _ (infer_leaf AI)); discriminate.
  - destruct (infer_stem_inv AI _ _ H) as [U [HE _]]; discriminate.
  - destruct (infer_fork_inv AI _ _ _ H) as [X [Y [Hl [Hr Happ]]]].
    assert (HS : type_app_stem @ type_app @r X @r Y ==> Sm (Fk L R))
      by (eapply typing.type_app_stem_inv; exact Happ).
    destruct (tagged_decide (Fk X Y)) as [[C [N HE]]|Hplain].
    + inversion HE; subst X Y.
      destruct (type_app_stem_tagged_success_inv AI type_app C N _ HS)
        as [E [_ HE']]; exfalso; eapply Hnot; exact HE'.
    + pose proof (type_app_stem_structural_inv AI type_app X Y _ Hplain HS)
        as HE; inversion HE; subst X Y.
      exists l,r; repeat split; assumption.
Qed.


Lemma infer_update_one_level : forall r,
  infer @ r ==> Sm ('Update) ->
  infer @ update_one_level r ==> Sm (update_one_level ('Update)).
Proof. intros; unfold update_one_level, update_fork; infer_tac. Qed.


End ValueInferenceFacts.


(** Keep the established external declarations-argument names. *)
Arguments infer_fork_results_package declarations : rename.
Arguments infer_fork_results declarations : rename.
Arguments infer_body_package declarations : rename.
Arguments infer_body declarations : rename.
Arguments infer declarations : rename.

(** Short names used in the decomposed preservation proofs. *)
Abbreviation inf := infer.
Definition inf_leaf := infer_leaf.
Definition inf_stem := infer_stem.
Definition inf_fork := infer_fork.
Definition inf_K1 := infer_K1.
Definition inf_tag_free := infer_tag_free.
Definition inf_tagged := infer_tagged.
Definition inf_I := infer_I.
Definition inf_Z := infer_Z.
Ltac inf_tac := repeat first
  [eassumption | apply inf_leaf | apply inf_stem | apply inf_K1
  | eapply inf_fork
  | apply typing.app_stem; apply type_app_stem_structural; intros; discriminate].
(** The IsNamed test [is_named N] has type [IsNamed N], in declarations that support
    the IsNamed family. *)
Lemma inf_is_named : forall AI N,
  concrete N -> supports_is_named AI -> inf AI @ is_named N ==> Sm (IsNamed N).
Proof.
  intros AI N HN HT.
  assert (inf AI @ N ==> Sm N) by (apply inf_tag_free, concrete_tag_free; assumption).
  assert (inf AI @ equal ==> Sm equal) by (apply inf_tag_free; apply equal_tag_free).
  assert (inf AI @ get_tagname ==> Sm get_tagname)
    by (apply inf_tag_free; vm_compute; reflexivity).
  assert (Ht : inf AI @ name_test N ==> Sm (name_test N)) by (unfold name_test; cbn; inf_tac).
  unfold is_named, IsNamed; eapply inf_tagged;
    [exact Ht|apply inf_tag_free; reflexivity|].
  eapply declaration_apply; [exact HT|apply is_named_abstractor_some; exact HN].
Qed.

(** The conditional [if_named] has the type built the same way from
    [IsNamed N]. *)
Lemma inf_if_named : forall AI N f F d D,
  concrete N -> supports_is_named AI -> inf AI @ f ==> Sm F -> inf AI @ d ==> Sm D ->
  inf AI @ if_named N f d ==> Sm (IfNamed N F D).
Proof.
  intros AI N f F d D HN HT Hf Hd.
  pose proof (inf_is_named AI N HN HT) as HW.
  unfold if_named, IfNamed; inf_tac.
Qed.


Unset Default Proof Using.
Transparent equal function_abstractor_core equal1 get_funty get_wait get_tagname get_tagged is_concrete query_handler structural_fork payload_eliminator get_wrap_payload_type get_name_test default_body abstract_case app extend_program type_app_stem type_app_S triage_case.

From TreeTyping Require Import tree.
Import ClauseNotation.
From Stdlib Require Import String.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque app inf type_app_stem.
Section Expressions.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (inf AI).
Local Abbreviation type_app_stem_inv := (typing.app_stem_inv AI).
Local Notation "x # y" := (Val type_app @@ x @@ y)
  (in custom clause at level 20, left associativity).
(** let Sm T1 = _ and Sm T2 = _ in T1 # T2, as a function of the two
    results ([success2] compiled in place). *)
Definition expression_success2_type_app_package :
  { t : Combination |
    to_tree <{ fun Sm "T1" , Sm "T2" => "T1" # "T2" }> = t }.
Proof. eexists; simpl; reflexivity. Defined.

Definition expression_success2_type_app :=
  Eval cbn in proj1_sig
    expression_success2_type_app_package.

(** infer_expression = | Lf       => Lf
                       | Sm u     => infer @ u
                       | Fk e1 e2 => let Sm T1 = infer_expression @ e1 in
                                     let Sm T2 = infer_expression @ e2 in T1 # T2
    As compiled, both subexpressions are inferred before either result is
    tested ([star] lifts the T1-free [infer_expression @ e2]); then
    [type_app @ T1] is formed and, if T2 is a success, applied to T2. *)
Definition infer_expression_body_package :
  { t | to_tree <{
      fun "infer_expression" =>
        shape
        | Lf => Lf
        | Sm "u" => infer @ "u"
        | Fk "e1" "e2" =>
            let Sm "T1" = "infer_expression" @ "e1" in
            let Sm "T2" = "infer_expression" @ "e2" in "T1" # "T2"
        end }> = t}.
Proof.  eexists; simpl; reflexivity.  Defined. 

 Definition infer_expression_body :=
  Eval cbn in proj1_sig infer_expression_body_package.

Definition infer_expression := 
  Z infer_expression_body.


Local Notation "F # U" := (type_app @ F @r U)
                      (at level 45, left associativity).


(** type inference for expressions *)

Lemma infer_expression_leaf : infer_expression @ Lf ==> Lf.
Proof. unfold infer_expression; eapply Z_unfold; cbv -[type_app infer]; evaluate. Qed.

Lemma infer_expression_stem :
  forall u T,
    infer @ u ==> Sm T ->
    infer_expression @ Sm u ==> Sm T.
Proof. intros u T Hu; eapply Z_unfold; cbv -[type_app infer]; evaluate. Qed.

Lemma infer_expression_fork :
  forall e1 e2 T1 T2 R,
    infer_expression @ e1 ==> Sm T1 ->
    infer_expression @ e2 ==> Sm T2 ->
    type_app @ T1 @r T2 ==> R ->
    infer_expression @ Fk e1 e2 ==> R.
Proof. intros; invert_eval; eapply Z_unfold; cbv -[type_app infer]; evaluate. Qed.

Local Lemma expression_success2_type_app_inv :
  forall v1 v2 T,
    expression_success2_type_app @ v1 @r v2 ==> Sm T ->
    exists T1 T2,
      v1 = Sm T1 /\
      v2 = Sm T2 /\
      type_app @ T1 @r T2 ==> Sm T.
Proof.
  intros v1 v2 T H.
  destruct v1 as [|T1|v11 v12];
    destruct v2 as [|T2|v21 v22];
    try (unfold expression_success2_type_app in H; cbn in H; invert_eval).
  exists T1, T2; repeat split; try reflexivity.
  evaluate.
Qed.

Lemma infer_expression_fork_gen_inv : forall e1 e2 R,
  infer_expression @ Fk e1 e2 ==> R ->
  exists a b, infer_expression @ e1 ==> a /\ infer_expression @ e2 ==> b /\
    expression_success2_type_app @ a @r b ==> R.
Proof.
  intros e1 e2 R H; apply Z_unfold_inv in H; unfold infer_expression_body in H; invert_eval.
  all: do 2 eexists; split; [eauto using eval_appl|split; [eauto using eval_appl|]].
  all: unfold expression_success2_type_app; cbn; repeat first [eassumption|progress evaluate].
Qed.


Lemma infer_expression_stem_inv :
  forall u T,
    infer_expression @ Sm u ==> T ->
    infer @ u ==> T.
Proof.
  intros u T H.
  assert (infer_expression_body @ infer_expression @r Sm u ==> T)
    by (eapply Z_unfold_inv; exact H).
  inv_out H0; inv_out H5; invert_eval.
Qed.

Lemma infer_expression_fork_inv :
  forall e1 e2 T,
    infer_expression @ Fk e1 e2 ==> Sm T ->
    exists T1 T2,
      infer_expression @ e1 ==> Sm T1 /\
      infer_expression @ e2 ==> Sm T2 /\
      type_app @ T1 @r T2 ==> Sm T.
Proof.
  intros e1 e2 T H.
  destruct (infer_expression_fork_gen_inv _ _ _ H) as [v2 [v4 [H1 [H2 Hsuccess]]]].
  destruct (expression_success2_type_app_inv _ _ _ Hsuccess)
    as [T1 [T2 [-> [-> Htype_app]]]].
  exists T1, T2; repeat split; auto.
Qed.

(** Immediate reduct typing for [K] fork elimination. *)
Lemma K_redex_typing :
  forall v1 v2 T,
    infer_expression @ (('K1 v1) @ v2) ==> Sm T ->
    infer @ v1 ==> Sm T.
Proof.
  intros v1 v2 T Htyping.
  destruct (infer_expression_fork_inv _ _ _ Htyping)
    as [function_ty [argument_ty
      [Hfunction_expr [Hargument_expr Hfinal_app]]]].
  pose proof
    (infer_expression_stem_inv _ _ Hfunction_expr) as Hfunction.
  destruct (infer_fork_inv _ _ _ _ Hfunction)
    as [leaf_ty [v1_ty [Hleaf [Hv1 Hconstructor_app]]]].
  pose proof
      (eval_deterministic _ _ Hleaf _ (inf_leaf AI)) as Hleaf_ty.
  inversion Hleaf_ty; subst leaf_ty.
  assert(type_app_stem @ type_app @r Lf @r v1_ty ==> Sm function_ty).
  eapply type_app_stem_inv; eauto.
  assert(type_app_stem @ type_app @r Lf @r v1_ty ==> Sm ('K1 v1_ty)) by
    (eapply type_app_stem_structural; intros; discriminate).
  assert(Sm function_ty = Sm ('K1 v1_ty)).
  eapply eval_deterministic; eauto. inv_out H1.
  assert(('K1 v1_ty) # argument_ty ==> Sm v1_ty)
    by eapply typing.app_K.
  assert(Sm T = Sm v1_ty) by (eapply eval_deterministic; eauto).
  inv_out H2; auto.
Qed.

(** Once the inferred triage has query shape, inversion recovers the types
    of all three fields.  Query shape is imposed by [type_app], not by
    construction of the triage itself. *)
Lemma infer_triage_shape : forall f0 f1 f2 Q,
  infer @ 'triage[f0,f1,f2] ==> Sm Q ->
  exists F0 F1 F2, Q = 'triage[F0,F1,F2].
Proof.
  intros f0 f1 f2 Q Htriage.
  destruct (infer_fork_inv _ _ _ _ Htriage)
    as [L [F2 [Hleft [Hf2 Houter_app]]]].
  destruct (infer_fork_inv _ _ _ _ Hleft)
    as [A [B [Hf0 [Hf1 Hinner_app]]]].
  pose proof (type_app_stem_inv _ _ _ Hinner_app) as Hinner_adapt.
  pose proof (type_app_stem_inv _ _ _ Houter_app) as Houter_adapt.
  destruct (type_app_stem_fork_success_shape _ _ _ _ _ Hinner_adapt)
    as [F0 [F1 ->]].
  pose proof (type_app_stem_triage_success_inv _ _ _ _ _ _ Houter_adapt) as ->.
  repeat eexists.
Qed.

Lemma infer_triage_inv : forall f0 f1 f2 B,
  infer @ 'triage[f0,f1,f2] ==>
    Sm (query_one_level B) ->
  infer @ f0 ==> Sm B /\
  infer @ f1 ==> Sm ('Query[B]) /\
  infer @ f2 ==> Sm ('Query['Query[B]]).
Proof.
  intros f0 f1 f2 B Htriage.
  destruct (infer_fork_inv _ _ _ _ Htriage)
    as [L [F2 [Hleft [Hf2 Houter_app]]]].
  destruct (infer_fork_inv _ _ _ _ Hleft)
    as [F0 [F1 [Hf0 [Hf1 Hinner_app]]]].
  pose proof (type_app_stem_inv _ _ _ Hinner_app) as Hinner_adapt.
  pose proof (type_app_stem_inv _ _ _ Houter_app) as Houter_adapt.
  destruct (type_app_stem_fork_success_shape _ _ _ _ _ Hinner_adapt)
    as [A [B1 HL]].
  subst L.
  pose proof (type_app_stem_triage_success_inv _ _ _ _ _ _ Houter_adapt) as HQ.
  inversion HQ; subst A B1 F2.
  destruct (tagged_decide (Fk F0 F1))
    as [[E [N Htagged]] | Hplain].
  - inversion Htagged; subst F0 F1.
    destruct (type_app_stem_tagged_success_inv _ _ E N (Fk B ('Query[B]))
      Hinner_adapt) as [E' [_ Heq]].
    discriminate Heq.
  - pose proof (type_app_stem_structural_inv _ _ F0 F1
      (Fk B ('Query[B])) Hplain Hinner_adapt) as Heq.
    inversion Heq; subst F0 F1.
  repeat split; assumption.
Qed.


Lemma infer_expression_program_tag_free : tag_free AI = true -> reserved_tagb (Lf 'C AI) = false ->
  tag_free infer_expression = true.
Proof.
  Local Transparent inf app typing.type_app_stem.
  intros HAI Hplain;
  unfold infer_expression, infer_expression_body, expression_success2_type_app,
    infer, infer_body, infer_fork_results, typing.type_app, app,
    body, default_body, triage_case;
  unfold type_app_stem;
  vm_compute in HAI, Hplain |- *; repeat rewrite HAI; try rewrite Hplain; reflexivity.
Local Opaque inf app typing.type_app_stem.
Qed.


Lemma infer_expression_self_typed : concrete AI ->
  infer @ infer_expression ==> Sm infer_expression.
Proof.
  intros HL; apply infer_tag_free.
  apply infer_expression_program_tag_free;
    [apply concrete_tag_free; exact HL|apply concrete_ontology_plain; exact HL].
Qed.


End Expressions.


Unset Default Proof Using.
Transparent equal function_abstractor_core equal1 get_funty get_wait get_tagname get_tagged is_concrete query_handler structural_fork payload_eliminator get_wrap_payload_type get_name_test default_body abstract_case app extend_program type_app_stem type_app_S triage_case inf.

(** * Type application, clause by clause as in the paper

    This file restates the stored program [typing.body] in a notation
    that follows the paper's type-application figure clause for clause:

      fun "type_app" "F" "U" => match "F" with
      | Lf                      => ...
      | Sm G                    => ...
      | tagged[E,N]             => ...
      | Fk (tagged[E,N]) _      => ...
      | triage[F0,F1,F2]        => ...
      | K1 G                    => ...
      | S2[G,H]                 => ...
      end

    Every clause body is a function of "U" (compiled by [star "U"]), so
    [E @ "U"] compiles to [E], [(Sm G)] to [K1 (Sm G)] and [(Sm "U")] to
    [Lf].  The notation only arranges the clauses; it expands
    ([type_app_clauses] below) into the stored staging of [body], which tries the
    clauses in the order of the figure:

    - the ordinary clauses (all but the F-level clause tagged) are
      compiled into one component ([default_body]), which is applied once
      to "type_app";
    - F is dispatched on its shape: a leaf or a stem goes straight to the
      ordinary clauses, which give it its own clause; a fork Fk X Y first
      tries the F-level clause [tagged[E,N]] ([abstract_case]) and then the
      ordinary clauses;
    - in the ordinary clauses a fork Fk X Y tries the operator refusal
      [Fk (tagged[E,N]) _] (X tagged), and is otherwise split
      by its left branch X into [triage[F0,F1,F2]], [K1 G] and [S2[G,H]]
      (a three-way dispatch on X: these three are pairwise disjoint,
      [K_not_triage], [S_not_triage]).

    Each clause body is compiled, as in the stored program, to a closed
    component applied to its pattern variables (and to [type_app] where it
    recurses).  The view is proved equal to the stored tree
    ([type_app_figure_body]); the stored definitions are not changed. *)

From TreeTyping Require Import tree.
Import ClauseNotation.
From Stdlib Require Import String.
Open Scope string_scope.
Set Default Proof Using "Type".

(** The staging of [body], as a function of the clauses' binders and
    bodies.  [rec] is the recursion variable ("type_app"). *)
Definition type_app_clauses
  (leaf : Term)
  (G1 : string) (stem : Term)
  (E N : string) (abs : Term)
  (E2 N2 : string) (err : Term)
  (F0 F1 F2 : string) (tri : Term)
  (G2 : string) (kc : Term)
  (G3 H3 : string) (sc : Term) : Term :=
  let rec := "type_app" in
  let V t := Val (to_tree t) in
  let FXY := Val Lf @@ Ref "X" @@ Ref "Y" in
  (* Fk (tagged[E2,N2]) _ => err, a function of F = Fk X Y *)
  let err_clause :=
    star "F" (''triage[Val Lf,
       ''onFork1 (star E2 (star N2 (Val Lf @@ star "U" err))),
       Val ('K1 ('K1 Lf))]
       @@ (Val get_tagged @@ Ref "X")) in
  (* otherwise, by the left branch X (a three-way dispatch, so the order
     of these clauses is immaterial): triage[F0,F1,F2] => tri,
     K1 G2 => kc, S2[G3,H3] => sc *)
  let split_clause :=
    star "F" (''triage[
        star G2 (V (star G2 (star "U" kc)) @@ Ref G2),
        star G3 (star H3
          (V (star rec (star G3 (star H3 (star "U" sc))))
             @@ Ref rec @@ Ref G3 @@ Ref H3)),
        star F0 (star F1 (star F2
          (''wait[V (star rec (star F0 (star F1 (star F2 (star "U" tri))))),
                  Ref rec]
           @@ Ref F0 @@ Ref F1 @@ Ref F2)))]
       @@ Ref "X" @@ Ref "Y") in
  (* the ordinary clauses, by the shape of F *)
  let ordinary :=
    V (star rec (''triage[
        V (star "U" leaf),
        star G1 (V (star rec (star G1 (star "U" stem))) @@ Ref rec @@ Ref G1),
        star "X" (star "Y"
          (extend2 err_clause split_clause
           @@ FXY))])) in
  (* tagged[E,N] => abs *)
  let abstract_clause :=
    ''wait[V (star rec (star "F"
             (''onStem1 (star E (Val Lf @@ star "U" abs))
                @@ (V (tcase (''tagged[Ref E, Ref N]) (Ref E)) @@ Ref "F")))),
           Ref rec] in
  (* a leaf or a stem goes to the ordinary clauses; a fork first tries
     tagged and name_test *)
  star "ordinary" (''triage[
      Ref "ordinary" @@ Val Lf,
      star "G" (Ref "ordinary" @@ (Val Lf @@ Ref "G")),
      star "X" (star "Y"
        (extend_w2 abstract_clause (Ref "ordinary")
         @@ FXY))])
  @@ (ordinary @@ Ref rec).

(** The section only scopes the notations of the figure (it has no
    variables), so that [InferFigures] below can give [x # y] another
    meaning without overriding it. *)
Section TypeAppFigure.

(** [x # y] is type application, the recursion variable "type_app". *)
Local Notation "x # y" := (Ref "type_app" @@ x @@ y)
  (in custom clause at level 20, left associativity).

(** Type application on F (the paper's type-application figure); the selected clause is a function of
    U, which is then applied to "U". *)
Local Notation "'match' u 'with' | 'Lf' => c | 'Sm' g1 => d | 'tagged [ e , n ] => a | 'Fk' ( 'tagged [ e2 , n2 ] ) '_' => er | 'triage [ f0 , f1 , f2 ] => t | 'K1 g2 => k | 'S2 [ g3 , h3 ] => s 'end'" :=
  (type_app_clauses c g1 d e n a e2 n2 er f0 f1 f2 t g2 k g3 h3 s @@ u @@ Ref "U")
  (in custom clause at level 0, u custom clause at level 9,
   c custom clause at level 200,
   g1 constr at level 0, d custom clause at level 200,
   e constr at level 0, n constr at level 0, a custom clause at level 200,
   e2 constr at level 0, n2 constr at level 0, er custom clause at level 200,
   g2 constr at level 0, k custom clause at level 200,
   g3 constr at level 0, h3 constr at level 0, s custom clause at level 200,
   f0 constr at level 0, f1 constr at level 0, f2 constr at level 0,
   t custom clause at level 200).

(** Plain triage on U (the triage clause of the paper's type-application figure).  The argument refusal [tagged[_,_] => Lf] comes first, as
    in the figure; since a tagged U is a fork, it is
    decided inside the fork branch of the triage on U, before [F2 # X] is
    computed, which tries it before [Fk X Y] and leaves the leaf and stem
    branches unchanged. *)
Local Notation "'match' u 'with' | 'tagged [ '_' , '_' ] => 'Lf' | 'Lf' => a | 'Sm' x => b | 'Fk' y z => 'let' 'Sm' g = f # y2 'in' e 'end'" :=
  (''triage[a, star x b, star y (star z
     (''onStem1 (star g e) @@
       (''triage[Ref "type_app", Val ('K1 ('K1 ('K1 Lf))),
                 Val ('K1 ('K1 ('K1 ('K1 Lf))))]
         @@ (Val get_tagged @@ (Val Lf @@ Ref y @@ Ref z)) @@ f @@ y2)))]
   @@ u)
  (in custom clause at level 0, u custom clause at level 9,
   a custom clause at level 200, x constr at level 0, b custom clause at level 200,
   y constr at level 0, z constr at level 0, g constr at level 0,
   f custom clause at level 0, y2 custom clause at level 0,
   e custom clause at level 200).


(** The view.  Differences from the figure: [E @ type_app @ U] and
    [F1 # X] in plain triage are the delayed [wait[E, type_app] @ U] and
    [wait[type_app, F1] @ X]; the tagged-U case of plain triage
    is decided inside the fork clause; nested matches are parenthesised.
    Writing [F1 # X] inline compiles to a different tree. *)
Definition type_app_figure (AI : Combination) : Term := <{
  fun "type_app" "F" "U" => match "F" with
  | Lf => (Sm (Sm "U"))
  | Sm "G" => (match (Fk "G" "U") with
              | 'tagged["C", "N"] =>
                  let Sm "E" = 'wait2[{AI}, "N", "type_app"] @ "C"
                  in (Sm 'tagged["E", "N"])
              | _ => (Sm (Fk "G" "U"))
              end)
  | 'tagged["E", "N"] => 'wait["E", "type_app"] @ "U"
  | Fk ('tagged["E", "N"]) _ => Lf
  | 'triage["F0", "F1", "F2"] => (match "U" with
              | 'tagged[_, _] => Lf
              | Lf => (Sm "F0")
              | Sm "X" => 'wait["type_app", "F1"] @ "X"
              | Fk "X" "Y" => let Sm "G" = "F2" # "X" in "G" # "Y"
              end)
  | 'K1 "G" => (Sm "G")
  | 'S2["G", "H"] => let Sm "V" = "G" # "U" in let Sm "W" = "H" # "U" in "V" # "W"
  end }>.

(** The view compiles to the stored body of type application. *)
Lemma type_app_figure_body : forall AI, to_tree (type_app_figure AI) = body AI.
Proof. intros; reflexivity. Qed.

Lemma type_app_figure_Z : forall AI, Z (to_tree (type_app_figure AI)) = type_app AI.
Proof. intros; rewrite type_app_figure_body; reflexivity. Qed.

End TypeAppFigure.

(** * Value and expression inference, clause by clause as in the figure

    The same check for the other two programs of the figure: written as
    [match] on the argument with nested lets, they compile to the stored
    bodies [infer_body] and [infer_expression_body].  [x # y] is the
    stored type application, [type_app AI @ x @ y]. *)
Section InferFigures.
Variable AI : Combination.
Local Notation "x # y" := (Val (type_app AI) @@ x @@ y)
  (in custom clause at level 20, left associativity).
Local Notation "'match' t 'with' | 'Lf' => a | 'Sm' x => b | 'Fk' y z => c 'end'" :=
  (''triage [ a, star x b, star y (star z c) ] @@ t)
  (in custom clause at level 0, t custom clause at level 9,
   a custom clause at level 200, x constr at level 0, b custom clause at level 200,
   y constr at level 0, z constr at level 0, c custom clause at level 200).

Definition infer_figure : Term := <{
  fun "infer" "t" => match "t" with
  | Lf => (Sm Lf)
  | Sm "u" => let Sm "U" = "infer" @ "u" in (Sm (Sm "U"))
  | Fk "u1" "u2" =>
      let Sm "U1" = "infer" @ "u1" in
      let Sm "U2" = "infer" @ "u2" in (Sm "U1") # "U2"
  end }>.

(** The view compiles to the stored body of value inference. *)
Lemma infer_figure_body : to_tree infer_figure = infer_body AI.
Proof. reflexivity. Qed.

Definition infer_expression_figure : Term := <{
  fun "infer_expression" "e" => match "e" with
  | Lf => Lf
  | Sm "u" => {infer AI} @ "u"
  | Fk "e1" "e2" =>
      let Sm "T1" = "infer_expression" @ "e1" in
      let Sm "T2" = "infer_expression" @ "e2" in "T1" # "T2"
  end }>.

(** The view compiles to the stored body of expression inference. *)
Lemma infer_expression_figure_body :
  to_tree infer_expression_figure = infer_expression_body AI.
Proof. reflexivity. Qed.
End InferFigures.
