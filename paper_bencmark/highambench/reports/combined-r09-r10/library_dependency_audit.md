# T1/T2 NumStability dependency audit

Audited 2026-09-20 against all **45 selected condition-L attempts** for the 15 T1/T2 tasks in the combined r09+r10 report. Every attempt passed validation and has a complete hidden transitive-declaration audit. The audited manifest is byte-identical to the frozen campaign manifest (`sha256 668330f1b0ba59930762a4bf7d19546564b6c02dfa01e03a61d0df6a3c2f2f19`). Pair provenance is in [completed_pairs.csv](completed_pairs.csv).

The P12-T1 and P17-T1 entries below concern the superseded targets measured in r09. Their redesigned equation-(8) and equation-(4.12) tasks have separate passing construction evidence but no benchmark repetitions yet.

The table checks the substantial declaration named by each task's tier rationale. `exact` means the intended declaration occurs in the accepted theorem's transitive dependency closure, even when reached through a submitted helper. `alternative` means the proof instead used the named substantial NumStability theorem. `none` means no corresponding substantial NumStability theorem was used; in these cases the complete audit found no NumStability declaration at all.

| Tier | Task | Intended substantial declaration(s), with `NumStability.` prefix omitted | Repetition 01 | Repetition 02 | Repetition 03 | Confirmation |
|---|---|---|---|---|---|---|
| T1 | P01-T1 | `pairwiseSum_forward_error_bound` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P02-T1 | `recursiveSum_forward_error_bound` | exact | exact | none | Not confirmed in repetition 03 |
| T1 | P04-T1 | `prod_error_bound` | exact | exact | alternative: `prod_one_add_delta_abs_sub_one_le_gamma_radius` | Intended declaration not confirmed in repetition 03 |
| T1 | P12-T1 | `FloatingPointFormat.fergusonMagnitudeExponentConditionLe_sub_finiteSystem` | none | none | none | Not confirmed in any repetition |
| T1 | P14-T1 | `recursiveSum_forward_error_bound` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P15-T1 | `matVec_backward_error` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P17-T1 | `FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P23-T1 | `matMul_error_bound` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P26-T1 | `forwardSub_backward_error` | exact | exact | exact | Confirmed in all repetitions |
| T1 | P28-T1 | `matMul_error_bound` | alternative: `dotProduct_error_bound` | alternative: `dotProduct_error_bound` | alternative: `dotProduct_error_bound` | Intended declaration not confirmed |
| T1 | P29-T1 | `matMul_error_bound` | alternative: `dotProduct_error_bound` | alternative: `dotProduct_error_bound` | alternative: `dotProduct_error_bound` | Intended declaration not confirmed |
| T1 | P33-T1 | `conventional_residual_error` | alternative: `dotProduct_backward_error` | exact | exact | Intended declaration not confirmed in repetition 01 |
| T2 | P01-T2 | `recursiveSum_running_error_bound`; `recursiveSum_forward_error_bound`; `pairwiseSum_forward_error_bound` | all exact | all exact | all exact | Confirmed in all repetitions |
| T2 | P15-T2 | `forwardSub_backward_error`; `matVec_backward_error` | both exact | both exact | both exact | Confirmed in all repetitions |
| T2 | P29-T2 | `forwardSub_backward_error`; `backSub_backward_error` | both exact | both exact | both exact | Confirmed in all repetitions |

## Result

- T2: all 3 tasks and all 9 repetitions used every intended substantial declaration.
- T1: 6 of 12 tasks used the intended substantial declaration in all three repetitions. Across the 36 T1 repetitions, 24 used the exact intended declaration, 8 used a substantial alternative, and 4 used no NumStability declaration.
- Overall: 33 of 45 L repetitions used every substantial declaration intended for that task. Therefore the strict claim that every T1/T2 L run used its intended declaration is false.
- The four no-library cases are `P02-T1-rep-03` and all three `P12-T1` repetitions. These proofs rebuilt the needed argument locally despite having L access.

## Other manifest candidates

`candidate_library_dependencies_for_audit` also contains some simpler or nearby declarations that the tier rationale does not identify as required substantial results. The deviations are:

- P04-T1: `gamma_nonneg` and `gammaValid_mono` were not used in any repetition; repetition 03 also omitted `prod_error_bound`.
- P12-T1: neither nearest-rounding helper nor the Ferguson subtraction theorem was used in any repetition.
- P14-T1: `recursiveSum_running_error_bound` was not used; the rationale's central `recursiveSum_forward_error_bound` was used in all repetitions.
- P17-T1: `foldl_add_mul_one_add_suffix_expansion` and `summationComponentwisePerturbation_rel_error_le_condition` were not used; the substantial finite-Chebyshev theorem and `FiniteProbability.eventProb_mono` were used in all repetitions.
- P02-T1, P28-T1, P29-T1, and P33-T1 have the repetition-level intended-result omissions shown in the table.
- Every other T1/T2 manifest candidate was present in every selected repetition.

This audit concerns actual theorem dependencies, not imports or text matches. A declaration imported but absent from the accepted theorem's transitive closure does not count as used.
