# Smooth delayed floors and Chvátal–Gomory closures: verification code

Exact-arithmetic verification suite for the paper

> R. Mirjalili and G. J. Lim, *Smooth delayed floors recover Chvátal–Gomory closures of packing polyhedra*, submitted to *Operations Research Letters*.

The suite checks finite instances of the results in the paper and its online appendix. It supplements the proofs, which do not depend on it.

## Contents

| Path | Contents |
|---|---|
| `src/exactcg.py` | Exact rational toolkit: ramps, delayed floors, the CG closure oracle (fundamental parallelepipeds of feasible bases), and independent cross-check oracles. |
| `tests/run_all.py` | The 35 test groups, including mutation tests. |
| `results/verification_report.{json,md}` | The report from the run described below. |

## Requirements

Python 3.10 or later and NumPy (tested with Python 3.10.12 and NumPy 1.26.4; see `requirements.txt`). Rational arithmetic uses `fractions.Fraction`. LP optima and vertices come from exact basis enumeration, so no solver is needed.

## Reproducing the reported results

```bash
pip install -r requirements.txt
python3 tests/run_all.py
```

The run takes about four minutes on a laptop. It prints one `PASS` line per group and writes `results/verification_report.json` and `results/verification_report.md`. Every group must pass. Apart from timings, the output should match the committed report exactly.

Each group draws from its own random stream, `random.Random("20261121-<group name>")`. Each group can therefore be rerun alone, with the same numbers:

```bash
python3 tests/run_all.py --only thm1_three_row_certificate   # writes verification_report_selected.*
python3 tests/run_all.py --quick                              # smaller samples, for a smoke test
```

The suite requires Python assertions, so do not run it with `python -O`.

## Test groups and the results they check

Group names predate the final numbering of the paper. Result numbers refer to the submitted article; an `S` prefix refers to its online appendix.

| Paper result | Test groups |
|---|---|
| Lemma 2 (delayed floor: closed form, normalization, averaging, superadditivity, cut validity) | `lemma1_closed_form_equals_series`, `lemma1_normalization_integers_sandwich`, `lemma1_plateau_ramps_error_set`, `lemma1_monotone_superadditive`, `lemma1_averaging_identity_linear_exact`, `lemma1_averaging_identity_smooth_float`, `lemma1_cut_validity_integer_points` |
| Domain restriction (Kuczma obstruction, need for F(0)=0) | `domain_symmetric_smooth_floor_not_superadditive_float`, `domain_normalization_needed_example_float` |
| Theorem 3(i) (certificates by CG rows) | `thm1_certificate_random_and_boundary`, `thm1_certificate_at_t_equals_one`, `thm1_smooth_mixture_certificate_compression`, `thm1_three_row_certificate` |
| Example 4 (both certificate bounds attained) | `thm1_certificate_bounds_attained` |
| Theorem 3(ii)–(iii) (exact recovery, closure equality) | `thm1_exact_recovery_all_ramps`, `thm1_closure_equality_on_instances` |
| Closure oracle cross-checks | `oracle_cross_check_grid_and_hull`, `oracle_separate_support_arithmetic_and_guards` |
| Remark 5 and Proposition S1 (fixed widths, ramp rescaling) | `thm1_fixed_width_counterexample`, `fixed_width_no_universal_width`, `thm1_three_row_certificate` (rescaling identity) |
| Theorem 6 and Example 7 (depth = CG rank) | `thm2_soundness_random_networks`, `thm2_recovery_builds_Ck_exactly`, `thm2_recovery_higher_rank_instances`, `thm2_explicit_rank2_example` |
| Corollary 8 (best depth-k bound) | `cor3_closure_value_identity` |
| Corollary S2 and Example S3 (objective rank) | `example_3x4y_table`, `cor4_fixed_branch_min_pool_on_finite_rhs`, `objective_rank_vs_hull_rank_random` |
| Complementation and Remark S4 (signed data, packing lift) | `complementation_scope`, `lifting_remark_mixed_sign_rank1`, `lifting_remark_rank2_and_empty_slice` |
| Proposition S5 (accuracy–slope trade-off) | `prop4_frontier_exact` |
| Gradient remark (Section 6) | `recovery_points_have_zero_gradient` |
| Mutation tests (deliberately wrong constructions must be detected) | `mutation_tests_detect_errors` |
| Auxiliary dense knapsack generator | `mik_generator_bound` |

Section 5 of the online appendix describes each group's instances, sampling distributions and assertions. It also summarizes the outcomes in Tables 1 and 2.

## License

MIT; see `LICENSE`.
