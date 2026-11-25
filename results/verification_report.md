# Verification report

Seed 20261121. 35 tests, 0 failed.

| Test | Status | Seconds | Key numbers |
|---|---|---:|---|
| `lemma1_closed_form_equals_series` | PASS | 1.2 | {"evaluations": 7830} |
| `lemma1_normalization_integers_sandwich` | PASS | 0.35 | {"points": 10095} |
| `lemma1_plateau_ramps_error_set` | PASS | 0.28 | {"ramps": ["early_saturation", "late_start"], "points": 2240, "old_error_set_equality_counterexamples": 149, "superadditivity_pairs": 6250} |
| `lemma1_monotone_superadditive` | PASS | 5.31 | {"pairs": 75000} |
| `lemma1_averaging_identity_linear_exact` | PASS | 0.12 | {"points": 2440} |
| `lemma1_averaging_identity_smooth_float` | PASS | 0.16 | {"max_abs_error": 0.0009374993750004279, "note": "Stieltjes sums on 2001 nodes"} |
| `lemma1_cut_validity_integer_points` | PASS | 3.5 | {"instances": 600, "cuts": 12000} |
| `domain_symmetric_smooth_floor_not_superadditive_float` | PASS | 0.11 | {"symmetric_violation_fraction_on_R": 0.4592896127821491, "delayed_violation_fraction_on_R+": 0.0} |
| `domain_normalization_needed_example_float` | PASS | 0.19 | {"min_superadditivity_gap": 0.3504954104660811, "analytic_lower_bound": 0.25} |
| `thm1_certificate_random_and_boundary` | PASS | 8.74 | {"cases": 60008, "by_case": {"direct": 29707, "rescaled": 15049, "with_fixings": 15252}, "max_certificate_rows": 7, "bound_n_plus_1_holds": true} |
| `thm1_smooth_mixture_certificate_compression` | PASS | 0.15 | {"rational_smooth_cuts": 360, "nontrivial_compressions": 45, "maximum_compressed_rows": 4, "bound_n_plus_1_holds": true} |
| `thm1_three_row_certificate` | PASS | 26.11 | {"shifted_rows": 60000, "shifted_by_rows": {"1": 44650, "2": 15350}, "smooth_rows": 45000, "smooth_by_distinct_rows": {"1": 29874, "2": 6636, "3": 8490}, "max_rows_after_compression": 3, "rescaling_identity_checks": 1800} |
| `thm1_certificate_bounds_attained` | PASS | 17.89 | {"smooth_row_times_256": [11, 256, 593, 296], "cg_rows_checked_up_to_rhs": 200, "reduced_without_x3_needs_two": true, "on_P_two_added_cuts_suffice": true, "pairs_checked": 20100, "smooth_needs_three": true, "shifted_needs_two": true} |
| `thm1_exact_recovery_all_ramps` | PASS | 13.18 | {"value_lists": 30000, "ramps": ["linear", "smoothstep", "smootherstep"]} |
| `thm1_closure_equality_on_instances` | PASS | 2.92 | {"instances": 120, "instances_with_C_strictly_inside_P": 109, "random_smooth_cuts_checked_against_C": 7200, "closure_rows_recovered_exactly": 256} |
| `oracle_cross_check_grid_and_hull` | PASS | 1.28 | {"instances_grid_equals_oracle": 60, "rank2_example_grid_D": 8} |
| `oracle_separate_support_arithmetic_and_guards` | PASS | 0.26 | {"separate_support_oracle_matches": 20, "invalid_inputs_rejected": 4, "weakened_rhs_mutation_detected": true} |
| `thm1_fixed_width_counterexample` | PASS | 0.75 | {"min_cut_bound_over_grid": "131431/87319", "C(P)": "[0,1]", "smoothstep_max_|S(r)-r|": 0.096225043794, "needs_<_0.2": true} |
| `thm2_soundness_random_networks` | PASS | 20.41 | {"instances": 40, "networks": 320, "neuron_cuts_checked": 1380, "neuron_rows_by_depth": {"1": 671, "2": 465, "3": 244}, "cuts_using_their_full_depth": 224, "full_depth_cuts_by_actual_depth": {"1": 224}, "full_depth_cuts_of_depth_at_least_2": 0} |
| `thm2_recovery_builds_Ck_exactly` | PASS | 6.65 | {"instances": 40, "neurons_simulated_exactly": 254, "closure_levels_histogram": {"1": 4, "2": 32, "3": 4}, "one_common_width_per_network": true, "ramps_replayed": ["linear", "smoothstep", "smootherstep"]} |
| `thm2_explicit_rank2_example` | PASS | 0.59 | {"features": [["0", "1", "1"], ["2", "3", "4"], ["1", "2", "2"]], "depth2_cut": "x + 2y <= 2", "min_depth1_slack_at_(1/2,1)": "0"} |
| `cor3_closure_value_identity` | PASS | 6.2 | {"instances": 60, "(instance,k)_pairs_exact_equality": 177, "pairs_by_k": {"0": 60, "1": 60, "2": 54, "3": 3}, "actual_compiled_network_evaluated": true} |
| `example_3x4y_table` | PASS | 0.09 | {"hull_rank": {"0": 0, "1": 1, "2": 1, "3": 1, "4": 1, "5": 1, "6": 2, "7": 1, "8": 1, "9": 1, "10": 2, "11": 1, "12": 0}, "objective_rank": {"0": 0, "1": 1, "2": 1, "3": 0, "4": 1, "5": 1, "6": 0, "7": 1, "8": 1, "9": 0, "10": 1, "11": 1, "12": 0}, "min_value_function_depth": 1, "max_hull_rank": 2, "fixed_smooth_neuron_exact_on_all_13_rhs": true} |
| `cor4_fixed_branch_min_pool_on_finite_rhs` | PASS | 0.23 | {"fixed_branches": 26, "cross_anchor_rhs_evaluations": 338, "max_objective_rank_by_cost": {"(1, 1)": 1, "(1, 2)": 2}, "min_pool_exact_at_every_rhs": true} |
| `objective_rank_vs_hull_rank_random` | PASS | 2.7 | {"families": 40, "families_with_max_obj_rank_<_max_hull_rank": 18} |
| `complementation_scope` | PASS | 17.72 | {"covering_closure_equals_pulled_back_packing_closure": true, "rank2_also_checked": true, "closure_vertices": [["0", "2"], ["2", "0"], ["3", "0"], ["3", "2"]], "covering_to_packing_integer_points_match": 9, "transformed_closure_rows": 4, "conflicting_sign_choices_available": 0, "signed_input_counterexample": "zero-extension of F: 2x1 - 2x2 <= 0 -> x1 <= 0 cuts (1,1)"} |
| `lifting_remark_mixed_sign_rank1` | PASS | 28.47 | {"instances": 8, "instances_with_C(P)_strictly_inside_P": 7, "includes_conflicting_sign_example": "x1 = x2 on [0,1]^2", "note": "rank 1 only; C(P) by grid multipliers (denominators <= 4)"} |
| `lifting_remark_rank2_and_empty_slice` | PASS | 1.09 | {"strict_lifted_rounds": 2, "slice_vertex_counts": [3, 3, 2], "lifted_closure_rows": [4, 6, 2], "replayed_neurons": 8, "network_depth": 2, "common_width": "1/20", "ramps": 3, "empty_slice_ranks": [1, 2], "packing_closures_remain_nonempty": true, "fractional_linking_penalty": ["0", "1/2"], "rounded_linking_penalty": [0, 1]} |
| `prop4_frontier_exact` | PASS | 0.93 | {"1": {"L1_error_per_unit": "1/2", "independent_admissible_PL_minorants": 200, "too_steep_mutation_detected": true}, "2": {"L1_error_per_unit": "1/4", "independent_admissible_PL_minorants": 200, "too_steep_mutation_detected": true}, "3": {"L1_error_per_unit": "1/6", "independent_admissible_PL_minorants": 200, "too_steep_mutation_detected": true}, "4": {"L1_error_per_unit": "1/8", "independent_admissible_PL_minorants": 200, "too_steep_mutation_detected": true}, "10": {"L1_error_per_unit": "1/20", |
| `mik_generator_bound` | PASS | 1.4 | {"formula_checked_n_1_to_40": true, "bound_100x200": 0.00024040504597284612, "bound_10x20": 31.960323224461845, "bound_1000x2000": 1.3170080803048775e-73, "monte_carlo_100x200_collapsed": "200/200", "monte_carlo_10x20_with_multi_item_solution": "200/200"} |
| `mutation_tests_detect_errors` | PASS | 3.31 | {"M1_round_to_nearest_invalid_cuts_found": 19, "M2_no_fixing_rows_domination_failures": 769, "M3_eps0_integer_mismatches": 19, "M4_basis_only_oracle_disagreements": 36, "M5_negative_weight_invalid_cuts_found": 121, "M6_single_row_instances": 60, "M6_full_oracle_agrees": 60, "M6_mutant_nontrivial": 51, "M6_mutant_disagreements": 7, "M6_aggregation_witness_detected": true} |
| `thm1_certificate_at_t_equals_one` | PASS | 3.68 | {"cases": 20003, "rescaled_or_fixed": 18341} |
| `fixed_width_no_universal_width` | PASS | 13.1 | {"cases": 40, "min_ratio_overall": 1.5121, "interior_plateau_counterexample_to_saturation_only_bound": true, "examples": {"linear/delta=1": "eta=1/2, min ratio 1.5417", "linear/delta=1/2": "eta=1/4, min ratio 1.7500", "linear/delta=1/3": "eta=1/6, min ratio 1.7500", "linear/delta=1/7": "eta=1/14, min ratio 1.7500", "linear/delta=1/100": "eta=1/200, min ratio 1.7500"}} |
| `recovery_points_have_zero_gradient` | PASS | 15.33 | {"evaluations_with_zero_slope": 402168, "width_derivatives_zero": true, "nondifferentiable_endpoint_checked": true, "same_multiplier_cut_order_counterexample": true} |
| `thm2_recovery_higher_rank_instances` | PASS | 17.51 | {"instances_with_rank_at_least_2": 20, "sampled": 306, "strict_rounds_histogram": {"2": 20}, "neurons_simulated_exactly": 180} |
