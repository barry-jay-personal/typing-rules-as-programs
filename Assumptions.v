(** * Assumptions of every Theorem.

    Each [Print Assumptions] below should report
    "Closed under the global context": no axiom, no admitted proof. *)

From TreeTyping Require tree typing soundness families booleans TreeTyping functions data_types arrays array_traversals matrices recursion search conditionals queries updates dither_minimisation paper_ontology self_typing customisation patching optimisation steps divergence specialise_equal typed_mu nat_search.

Print Assumptions TreeTyping.tree.eval_deterministic.
Print Assumptions TreeTyping.soundness.function_abstractor_sound.
Print Assumptions TreeTyping.soundness.eval_iff_bounded.
Print Assumptions TreeTyping.soundness.evaluation_preserves_typing.
Print Assumptions TreeTyping.soundness.ept_by_typing.
Print Assumptions TreeTyping.functions.infer_lam.
Print Assumptions TreeTyping.functions.infer_fix_function.
Print Assumptions TreeTyping.functions.infer_application.
Print Assumptions TreeTyping.functions.dither_fn_typed_no_value.
Print Assumptions TreeTyping.data_types.add_typed.
Print Assumptions TreeTyping.data_types.mul_typed.
Print Assumptions TreeTyping.data_types.append_polymorphic.
Print Assumptions TreeTyping.data_types.infer_append_application.
Print Assumptions TreeTyping.data_types.map_polymorphic.
Print Assumptions TreeTyping.arrays.array_append_polymorphic.
Print Assumptions TreeTyping.arrays.infer_array_append_application.
Print Assumptions TreeTyping.array_traversals.array_map_polymorphic.
Print Assumptions TreeTyping.matrices.matrix_mult_refused.
Print Assumptions TreeTyping.matrices.infer_matrix_mult_application.
Print Assumptions TreeTyping.recursion.infer_minimisation_fn.
Print Assumptions TreeTyping.search.infer_minimise_is_odd_fn.
Print Assumptions TreeTyping.conditionals.salary_here_polymorphic.
Print Assumptions TreeTyping.queries.generic_query_application.
Print Assumptions TreeTyping.queries.infer_size.
Print Assumptions TreeTyping.queries.typed_equal_polymorphic.
Print Assumptions TreeTyping.queries.typed_equal_eval.
Print Assumptions TreeTyping.updates.abstract_update_preserves_typing.
Print Assumptions TreeTyping.dither_minimisation.minimisation_polymorphic.
Print Assumptions TreeTyping.dither_minimisation.minimise_is_odd.
Print Assumptions TreeTyping.dither_minimisation.dither_typed_no_value.
Print Assumptions TreeTyping.paper_ontology.paper_evaluation_preserves_typing.
Print Assumptions TreeTyping.self_typing.concrete_is_self_typed.
Print Assumptions TreeTyping.self_typing.concrete_type_unique_value.
Print Assumptions TreeTyping.self_typing.identity_polymorphic.
Print Assumptions TreeTyping.self_typing.normal_combinators_are_concrete.
Print Assumptions TreeTyping.self_typing.Z_preserves_concrete.
Print Assumptions TreeTyping.self_typing.concrete_is_Turing_complete.
Print Assumptions TreeTyping.self_typing.infer_self_typed.
Print Assumptions TreeTyping.self_typing.paper_infer_self_typed.
Print Assumptions TreeTyping.customisation.infer_update_salary.
Print Assumptions TreeTyping.customisation.paid_over_typed.
Print Assumptions TreeTyping.customisation.paid_over_57_original.
Print Assumptions TreeTyping.customisation.count_employees_department_example.
Print Assumptions TreeTyping.customisation.salary_bill_department_2025.
Print Assumptions TreeTyping.customisation.salary_update_department_2025.
Print Assumptions TreeTyping.patching.salary_update_polymorphic.
Print Assumptions TreeTyping.patching.salary_update_paid_at_least_57.
Print Assumptions TreeTyping.patching.salary_update_pending_query_typed.
Print Assumptions TreeTyping.patching.update_preserves_expression_typing.
Print Assumptions TreeTyping.patching.patch_commutes_with_evaluation.
Print Assumptions TreeTyping.optimisation.optimise_preserves_evaluation.
Print Assumptions TreeTyping.optimisation.optimise_typed.
Print Assumptions TreeTyping.steps.size_on_expressions.
Print Assumptions TreeTyping.divergence.infer_expression_cdither_no_value.
Print Assumptions TreeTyping.divergence.type_app_zdither_no_value.
Print Assumptions TreeTyping.specialise_equal.tester_agrees.
Print Assumptions TreeTyping.specialise_equal.specialise_concrete.
Print Assumptions TreeTyping.specialise_equal.specialise_typed.
Print Assumptions TreeTyping.specialise_equal.specialised_infer_self_typed.
Print Assumptions TreeTyping.specialise_equal.unchanged_from_support.
Print Assumptions TreeTyping.specialise_equal.size_table.
Print Assumptions TreeTyping.typed_mu.typed_mu_complete_at.
Print Assumptions TreeTyping.typed_mu.typed_mu_complete.
Print Assumptions TreeTyping.typed_mu.typed_mu_values_are_numbers.
Print Assumptions TreeTyping.nat_search.nat_search_polymorphic.
Print Assumptions TreeTyping.nat_search.nat_search_is_odd.
