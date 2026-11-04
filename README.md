# Typing Rules Become Programs in Tree Calculus: Rocq development

This is the Rocq development that accompanies the research report
*Typing Rules Become Programs in Tree Calculus* by Barry Jay (2026).

Tree calculus can analyse programs, so its typing rules can be
programs: type inference (`infer`) and type application (`type_app`) are
programs of tree calculus. Type application computes the type of an
application from the types of operator and argument, and in doing so
displaces function types, type variables and quantifiers. The soundness
and expressive power of the system are determined by an ontology of
abstract types. The development proves that evaluation preserves typing,
types booleans, numbers, options, sums, lists, arrays, queries, updates
and general recursion, and shows that `infer` has type `infer`.

## Building

The development builds with [Rocq](https://rocq-prover.org) 9.3 and its
standard library, and has no other dependencies.

```sh
./build.sh
```

This generates a `Makefile` from `_CoqProject` and runs `make`. The
logical library name is `TreeTyping`; `From TreeTyping Require Import
TreeTyping.` loads the core (tree calculus, typing, soundness and
booleans).

## Checking

The development has no `Admitted` proofs and no axioms. `Assumptions.v`,
the last file built, runs `Print Assumptions` on every Theorem; each
reports "Closed under the global context".

Every Theorem of the paper is a Rocq Theorem of the same name, stated in
the paper as proved here. Not every Rocq Theorem appears in the paper.
Other results that the paper relies on are Lemmas, cited by name in the
paper.

## Files

In build order, with the part of the paper each supports:

| File | Paper |
|---|---|
| `tree.v` | Tree Calculus |
| `typing.v` | Typing Rules as Programs: type inference and type application |
| `soundness.v` | Typing Rules as Programs: soundness by typing and by values |
| `families.v` | Support: from abstractor soundness to the conditions on each clause |
| `booleans.v` | Abstract Types: booleans |
| `TreeTyping.v` | Umbrella module for the core |
| `functions.v` | Functions |
| `data_types.v` | Abstract Types: numbers, options, sums, lists |
| `arrays.v` | Arrays: array types, array append |
| `array_traversals.v` | Arrays: reading an array |
| `matrices.v` | Arrays: matrices |
| `recursion.v` | Support: recursive number programs and structural recursion |
| `search.v` | Lazy searches; not described in the paper |
| `conditionals.v` | Type-Directed Conditionals; wrapped types and a department |
| `queries.v` | Queries |
| `updates.v` | Updates |
| `dither_minimisation.v` | Updates: minimisation; Queries: dither |
| `paper_ontology.v` | A Sound Ontology |
| `self_typing.v` | Concrete Types: self-typing, including `infer : infer` |
| `customisation.v` | Querying a department; raising salaries |
| `patching.v` | Patching a query program; patching expressions |
| `optimisation.v` | Towards Typed Tooling: typed optimisation |
| `steps.v` | Towards Typed Tooling: snapshots of evaluation |
| `divergence.v` | Support: divergence and the truth-teller |
| `specialise_equal.v` | Towards Typed Tooling: specialising equality, sizes |
| `typed_mu.v` | Typed partial recursion on numbers |
| `nat_search.v` | Introduction (Figure 1) and Updates: `nat_search` |
| `Assumptions.v` | `Print Assumptions` for every Theorem |

## Theorems of the paper

| Paper | Rocq Theorem | File |
|---|---|---|
| Theorem 1 | `eval_deterministic` | `tree.v` |
| Theorem 2 | `infer_application` | `functions.v` |
| Theorem 3 | `ept_by_typing` | `soundness.v` |
| Theorem 4 | `eval_iff_bounded` | `soundness.v` |
| Theorem 5 | `evaluation_preserves_typing` | `soundness.v` |
| Theorem 6 | `concrete_is_self_typed` | `self_typing.v` |
| Theorem 7 | `concrete_type_unique_value` | `self_typing.v` |
| Theorem 8 | `identity_polymorphic` | `self_typing.v` |
| Theorem 9 | `normal_combinators_are_concrete` | `self_typing.v` |
| Theorem 10 | `Z_preserves_concrete` | `self_typing.v` |
| Theorem 11 | `concrete_is_Turing_complete` | `self_typing.v` |
| Theorem 12 | `infer_self_typed` | `self_typing.v` |
| Theorem 13 | `infer_expression_cdither_no_value` | `divergence.v` |
| Theorem 14 | `add_typed` | `data_types.v` |
| Theorem 15 | `mul_typed` | `data_types.v` |
| Theorem 16 | `type_app_zdither_no_value` | `divergence.v` |
| Theorem 17 | `append_polymorphic` | `data_types.v` |
| Theorem 18 | `infer_append_application` | `data_types.v` |
| Theorem 19 | `map_polymorphic` | `data_types.v` |
| Theorem 20 | `salary_here_polymorphic` | `conditionals.v` |
| Theorem 21 | `array_append_polymorphic` | `arrays.v` |
| Theorem 22 | `infer_array_append_application` | `arrays.v` |
| Theorem 23 | `array_map_polymorphic` | `array_traversals.v` |
| Theorem 24 | `infer_matrix_mult_application` | `matrices.v` |
| Theorem 25 | `matrix_mult_refused` | `matrices.v` |
| Theorem 26 | `generic_query_application` | `queries.v` |
| Theorem 27 | `infer_size` | `queries.v` |
| Theorem 28 | `typed_equal_eval` | `queries.v` |
| Theorem 29 | `typed_equal_polymorphic` | `queries.v` |
| Theorem 30 | `dither_typed_no_value` | `dither_minimisation.v` |
| Theorem 31 | `count_employees_department_example` | `customisation.v` |
| Theorem 32 | `salary_bill_department_2025` | `customisation.v` |
| Theorem 33 | `paid_over_typed` | `customisation.v` |
| Theorem 34 | `paid_over_57_original` | `customisation.v` |
| Theorem 35 | `abstract_update_preserves_typing` | `updates.v` |
| Theorem 36 | `infer_update_salary` | `customisation.v` |
| Theorem 37 | `salary_update_department_2025` | `customisation.v` |
| Theorem 38 | `salary_update_polymorphic` | `patching.v` |
| Theorem 39 | `minimisation_polymorphic` | `dither_minimisation.v` |
| Theorem 40 | `minimise_is_odd` | `dither_minimisation.v` |
| Theorem 41 | `nat_search_polymorphic` | `nat_search.v` |
| Theorem 42 | `typed_mu_complete` | `typed_mu.v` |
| Theorem 43 | `infer_lam` | `functions.v` |
| Theorem 44 | `salary_update_paid_at_least_57` | `patching.v` |
| Theorem 45 | `infer_fix_function` | `functions.v` |
| Theorem 46 | `function_abstractor_sound` | `soundness.v` |
| Theorem 47 | `infer_minimisation_fn` | `recursion.v` |
| Theorem 48 | `paper_evaluation_preserves_typing` | `paper_ontology.v` |
| Theorem 49 | `paper_infer_self_typed` | `self_typing.v` |
| Theorem 50 | `update_preserves_expression_typing` | `patching.v` |
| Theorem 51 | `patch_commutes_with_evaluation` | `patching.v` |
| Theorem 52 | `optimise_preserves_evaluation` | `optimisation.v` |
| Theorem 53 | `optimise_typed` | `optimisation.v` |
| Theorem 54 | `size_table` | `specialise_equal.v` |
| Theorem 55 | `tester_agrees` | `specialise_equal.v` |
| Theorem 56 | `specialise_typed` | `specialise_equal.v` |
| Theorem 57 | `size_on_expressions` | `steps.v` |

## Licence

MIT; see `LICENSE`.
