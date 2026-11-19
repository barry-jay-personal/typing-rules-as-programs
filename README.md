# Typing Rules Become Programs in Tree Calculus: Rocq development (v2.0)

This is the Rocq development that accompanies the research report
*Typing Rules Become Programs in Tree Calculus* by Barry Jay (2026),
included here as [`paper/typing-rules-become-programs.pdf`](paper/typing-rules-become-programs.pdf).
Version 1.0 (tag `v1.0`) accompanies the first version of the report.

Tree calculus can analyse programs, so its typing rules can be
programs: type inference (`infer`) and type application (`type_app`) are
programs of tree calculus. Concrete programs are their own types. Abstract
types are labels whose names are declared by an ontology, and type
parameters are passed as their codes. The development proves that
evaluation preserves typing for a sound ontology; types booleans, numbers,
options, sums and the empty type, lists, arrays, queries, updates and
general recursion; shows that `infer` has type `infer`; types patching,
measuring and optimising as programs on expressions; and gives
intuitionistic propositional logic a consistent model, with function types
as abstract types that record their domains.

## Changes since version 1.0

This version adds a goal, to support propositional logic, the first step of
a larger project to treat all of logic within type theory. Its
consideration forced three changes.

- Falsity is an empty type.
- Version 1.0 passed a type parameter by a *ghost*, a value of that type,
  which an empty type does not have, so ghosts are eliminated.
- Types are represented by names and passed as codes, and generators build
  the constructors of empty lists and arrays at run time.

Function types are abstract types that record a domain, possibly
uninhabited. In version 1.0, function types and query types each had a
constructor for fixfunctions. Both are gone: recursive functions and
recursive queries are now built from updates, so every recursion stops at
the update type. So `paper_ontology`, which types everything before the
logic, has no function types, and that development is self-contained.
Type-directed conditionals, once a section of their own, are now limited
to updates and queries.

## Building

The development builds with [Rocq](https://rocq-prover.org) 9.3 and its
standard library, and has no other dependencies.

```sh
./build.sh
```

This generates a `Makefile` from `_CoqProject` and runs `make`. The
logical library name is `BigStep`. A full build takes about 17 minutes.

## Checking

The development has no `Admitted` proofs and no axioms. `Assumptions.v`,
the last file built, runs `Print Assumptions` on every Theorem of the
paper; each reports "Closed under the global context".

Every Theorem of the paper is a Rocq Theorem of the same name. Not every
Rocq Theorem appears in the paper. Other results that the paper relies on
are Lemmas, cited by name in the paper. The paper writes a program with
parameters in brackets, `f[x]`, where Rocq often builds it as
`'wait[f_body, x]`; the paper's `code[A]` is `code A`.

## Files

`_CoqProject` lists the 59 files in build order.

## Sections of the paper and the files they cite most

| Section | Title | Files |
|---|---|---|
| 1 | Introduction | `logic_typing.v`, `poly.v`, `matrices_rt.v`, `updates.v`, `salary_query_paper.v`, `updates_paper.v` |
| 2 | Tree Calculus | `tree.v`, `department.v`, `booleans.v` |
| 3 | Typing Rules as Programs | `typing.v`, `identifiers.v`, `booleans.v`, `updates.v`, `soundness.v`, `functions.v` |
| 4 | Concrete Types | `self_typing.v`, `system_f.v`, `divergence.v`, `typing.v`, `plain_translation.v`, `tree.v` |
| 5 | Abstract Types | `sums.v`, `booleans.v`, `department.v`, `data_types.v`, `lists.v`, `functions.v` |
| 6 | Updates | `updates.v`, `department.v`, `generic_typings.v`, `cites_queries.v`, `functions.v`, `updates_paper.v` |
| 7 | Recursion | `scott_arithmetic.v`, `poly.v`, `typed_mu_rt.v`, `numbers_rt.v`, `cites_functions.v`, `lists.v` |
| 8 | Queries | `queries_core.v`, `dither_queries.v`, `size_queries.v`, `updates_paper.v`, `queries.v`, `cites_queries.v` |
| 9 | Arrays | `matrices_rt.v`, `array_family.v`, `array_poly.v`, `rows.v` |
| 10 | A Sound Ontology | `paper_ontology.v`, `cites_queries.v`, `fun_ontology.v`, `paper_names.v` |
| 11 | Towards Typed Tooling | `size_queries.v`, `cites_queries.v`, `optimisation_rt.v` |
| 12 | Functions | `functions.v`, `cites_functions.v`, `function_recursion_paper.v`, `function_types_paper.v`, `generic_lambda.v`, `fun_ontology.v` |
| 13 | Propositional Logic | `logic_paper.v`, `logic_typing.v`, `paper_ontology.v`, `fun_ontology.v`, `functions.v` |
| A | The Leibniz Project | `cites_data.v` |

## Theorems of the paper

| Section | Theorem | File |
|---|---|---|
| 2.1 | `eval_deterministic` | `tree.v` |
| 3.1 | `infer_application` | `paper_names.v` |
| 3.4 | `ept_by_typing` | `soundness.v` |
| 3.5 | `eval_iff_bounded` | `updates_paper.v` |
| 3.5 | `evaluation_preserves_typing` | `soundness.v` |
| 4.1 | `concrete_is_self_typed` | `typing.v` |
| 4.1 | `concrete_type_unique_value` | `self_typing.v` |
| 4.1 | `identity_polymorphic` | `self_typing.v` |
| 4.2 | `plain_translation_concrete` | `plain_translation.v` |
| 4.2 | `sysF_normal_concrete` | `system_f.v` |
| 4.2 | `Z_preserves_concrete` | `self_typing.v` |
| 4.2 | `concrete_is_Turing_complete` | `self_typing.v` |
| 4.2 | `infer_self_typed` | `self_typing.v` |
| 4.3 | `infer_expression_cdither_no_value` | `divergence.v` |
| 6 | `abstract_update_preserves_typing` | `updates_paper.v` |
| 6 | `infer_update_salary` | `updates_paper.v` |
| 6 | `salary_update_department_2025` | `department.v` |
| 7.1 | `minimisation_polymorphic` | `poly.v` |
| 7.2 | `add_typed` | `poly.v` |
| 7.2 | `mul_typed` | `poly.v` |
| 7.2 | `minimise_is_odd` | `poly.v` |
| 7.2 | `typed_mu_complete` | `typed_mu_rt.v` |
| 7.3 | `append_polymorphic` | `poly.v` |
| 7.3 | `infer_append_application` | `poly.v` |
| 7.3 | `map_polymorphic` | `poly.v` |
| 8.1 | `generic_query_application` | `size_queries.v` |
| 8.2 | `rec_query_generic` | `size_queries.v` |
| 8.3 | `infer_size` | `size_queries.v` |
| 8.3 | `typed_equal_eval` | `equality_queries.v` |
| 8.3 | `typed_equal_polymorphic` | `equality_queries.v` |
| 8.4 | `type_app_zdither_no_value` | `dither_queries.v` |
| 8.4 | `dither_typed_no_value` | `dither_queries.v` |
| 8.5 | `count_employees_department_example` | `paper_names.v` |
| 8.5 | `salary_bill_department_2025` | `paper_names.v` |
| 8.5 | `paid_over_typed` | `updates_paper.v` |
| 8.5 | `paid_over_57_original` | `updates_paper.v` |
| 8.6 | `salary_update_polymorphic` | `salary_query_paper.v` |
| 9.2 | `array_append_polymorphic` | `array_poly.v` |
| 9.2 | `infer_array_append_application` | `array_poly.v` |
| 9.3 | `array_map_polymorphic` | `array_poly.v` |
| 9.4 | `infer_matrix_mult_application` | `matrices_rt.v` |
| 9.4 | `matrix_mult_refused` | `matrices_rt.v` |
| 10 | `paper_evaluation_preserves_typing` | `paper_names.v` |
| 10 | `paper_infer_self_typed` | `paper_ontology.v` |
| 11.1 | `update_preserves_expression_typing` | `updates_paper.v` |
| 11.1 | `patch_commutes_with_evaluation` | `patching_paper.v` |
| 11.2 | `optimise_preserves_evaluation` | `optimisation_rt.v` |
| 11.2 | `optimise_typed` | `optimisation_rt.v` |
| 11.3 | `tester_agrees` | `specialise_check.v` |
| 11.3 | `specialise_typed` | `specialise_rt.v` |
| 11.4 | `size_on_paper_expressions` | `size_queries.v` |
| 12.1 | `fun_ontology_sound` | `fun_ontology.v` |
| 12.1 | `infer_lam` | `logic_typing.v` |
| 12.1 | `function_declaration_sound` | `paper_names.v` |
| 12.1 | `salary_update_paid_at_least_57` | `salary_lambda_paper.v` |
| 12.2 | `infer_fix_function_upd` | `function_recursion_paper.v` |
| 12.2 | `infer_minimisation_fn` | `function_types_paper.v` |
| 13.1 | `infer_contrapositive` | `logic_typing.v` |
| 13.2 | `derivation_evaluates` | `logic_typing.v` |
| 13.2 | `bot_not_derivable` | `logic_paper.v` |
| 13.2 | `atom_not_derivable` | `logic_paper.v` |

