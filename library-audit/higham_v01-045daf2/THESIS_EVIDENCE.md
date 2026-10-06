# Thesis-ready evidence dossier

## Citation scope and reading rule

This dossier distils the read-only audit of `NumStability` at the exact commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`. It is intended to support careful
academic claims, not to replace the complete methods and limitations in the
linked reports.

The elaborated declaration graph always uses the orientation
**consumer -> dependency**:

```text
A -> B means that declaration A directly references declaration B
in its elaborated type or in its body/proof.
```

The current graph schema is `numstability-elaborated-architecture/2.1.0`.
Unless stated otherwise, “confirmed source-written public” is the audit's
conservative operational class: a non-reserved, environment-public declaration
with a direct Lean selection range whose exact selected source token agrees
with the terminal declaration-name component or a namespace-qualified suffix.
This is source-origin evidence, not proof that a human rather than a macro
wrote every part of the declaration. Generated and unresolved declarations
remain separate.

For the 27 incoming-use and cross-boundary percentages, the authoritative
citation surface is
[`incoming_and_cross_boundary_coverage_contract.csv`](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv),
schema `numstability-coverage-metric-contract/1.0.0`. Each row carries the
formula, exact universe predicate, exact metric predicate, all-project
consumer/dependency universe, materialized columns, conservative authorship
classifier, and underlying raw artifacts/columns. The older coverage table is
the materialized numerical source, but the contract is the citable definition.

The isolated same-commit cached `lake build` exited 0. A genuinely fresh full
build did **not** complete: one attempt stopped on `ENOSPC`, and the next was
capacity-stopped before filling the disk. Therefore no clean full-build time is
available. Exact Phase 10A tooling was recovered, but historical comparison is
valid only for aggregate fields replayed with that byte-identical schema; the
historical raw declaration/edge stream was not recovered.

Primary reports:

- [architecture review](./ARCHITECTURE_REVIEW.md)
- [dependency-chain evidence](./DEPENDENCY_CHAINS.md)
- [public API consumability](./PUBLIC_API_CONSUMABILITY.md)
- [historical comparison](./HISTORICAL_COMPARISON.md)
- [timings and proof hygiene](./TIMINGS_AND_PROOF_HYGIENE.md)
- [build and environment provenance](./provenance/BUILD_AND_ENVIRONMENT.md)
- [reproduction instructions](./REPRODUCE.md)
- [limitations](./LIMITATIONS.md)

## Claim-to-evidence table

| ID | Conservative thesis-safe formulation | Direct evidence | Boundary of the claim |
|---|---|---|---|
| T1 | The compiled project is structurally integrated: within the confirmed-source-written public universe, 35,889 of 47,890 declarations have an incoming project reference, and 46,811 participate in a directional chain of at least two edges upstream or downstream. | Metrics M1 and M6 below; [authoritative coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv). | Incoming use and chain membership prove formal composition in this Lean environment, not source faithfulness, semantic importance, or API quality. |
| T2 | Reuse crosses ownership boundaries: 12,584 of 47,890 confirmed-source-written public declarations are consumed from another module; 5,962 are consumed from another architectural layer; 9,260 have consumers in multiple modules; and 5,126 have consumers in multiple audit-classified domains. | Metrics M2–M5; [authoritative coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv); [direct dependency rows](./current_graph/metrics/direct_project_dependencies.csv.gz). | Module, layer, and domain classifications are audit classifications. A file split can change cross-module status without changing the logical declaration pair. |
| T3 | The source-facing layer is substantially connected to reusable mathematics: 22,062 of 30,289 confirmed-source-written public declarations owned by `Source` directly reference at least one confirmed-source-written public declaration in `Algorithms`, `Analysis`, or `FloatingPoint`. | Metric M9 and the filtered edge join described in the [architecture review](./ARCHITECTURE_REVIEW.md#source-wrappers-and-delegation). | This does not show that every Source declaration is a thin wrapper, nor that any wrapper is faithful to Higham. |
| T4 | A high-level QR-solve theorem is compositionally checked through a verified 14-edge, seven-module proof spine reaching the primitive square-root rounding model, with an additional direct branch for the right-hand-side/back-substitution argument. | Chain C05 in [dependency chains](./DEPENDENCY_CHAINS.md#c05-qr-solve-bound-descends-through-factorization-householder-norm-and-square-root-analyses); exact rows in [chain edges](./current_graph/chains/representative_chain_edges.csv) and [branch edges](./current_graph/chains/representative_chain_branch_edges.csv). | This is one selected proof spine. It does not establish completeness, numerical sharpness, source fidelity, or ease of discovery by a user. |
| T5 | The rechecked Chapter 9/12 LU-solver composition exists through a deliberately `CrossChapter`-owned theorem: it has a branch into the Chapter 9 Doolittle closure and a separate type/body branch to the Chapter 12 solver-bound predicate. | Chain C06 in [dependency chains](./DEPENDENCY_CHAINS.md#c06-crosschapter-lu-solver-bridge-connects-chapter-12-semantics-to-chapter-9-doolittle-bounds); [machine re-check](./current_graph/chains/chapter09_chapter12_path_recheck.json); [declaration-level figure](./figures/crosschapter_lu_solver_chain.svg). | The exhaustive re-check found zero paths from the 96 Chapter12-owned declarations to any of the 6,081 Chapter09-owned declarations. It is therefore incorrect to describe this as a Chapter12-owned -> Chapter09-owned dependency. The bridge is owned by `Source.Higham.CrossChapter.LUSolverWeights`. |
| T6 | The gamma calculus is reused broadly inside the project: `NumStability.gamma_mul` has 81 direct consumer declarations and 4,739 transitive downstream consumers in 362 modules, reaching all 22 audit-classified domains. | Row `NumStability.gamma_mul` in [declaration metrics](./current_graph/metrics/declaration_metrics.csv.gz), columns `direct_project_consumer_count`, `transitive_downstream_consumer_count`, `transitive_downstream_module_count`, and `transitive_downstream_domain_count`. | High fan-in is evidence of internal consumption, not automatically of a good public interface or faithful mathematical formalization. |
| T7 | Representative canonical APIs are practically consumable when their narrow owner modules are known: all 15 predeclared probes passed both an independent `#check` and a separately compiled minimal client theorem; their narrow import closures reached no `Source` module, and all 49 selected direct type edges targeted public, non-Source, non-compatibility declarations. | Metric M12; [probe report](./PUBLIC_API_CONSUMABILITY.md); [results](./probes/results.csv); [type-edge rows](./probes/selected_api_direct_project_type_dependencies.csv). | This is a purposeful 15-API case study, not a library-wide success rate. Most clients are thin forwarding corollaries; success proves usability only for the recorded import and theorem. |
| T8 | The completed reorganization materially changed module ownership and navigation: the exact historical scanner reports 957 modules at effective Phase 10A commit `d21a4ed5...` and 2,839 at the audited commit, while normalized source bytes changed from 69,590,164 to 69,455,337. All 28 `Source.Higham.ChapterNN` roots exist, and 1,405 of 1,414 Source modules follow that hierarchy; all 393 source/chapter-labelled paths remaining under canonical `Algorithms` or `Analysis` are statically declaration-free. | Metric M11; [static architecture report](./ARCHITECTURE_REVIEW.md#actual-hierarchy-and-ownership-after-reorganization); [historical source replay](./historical/PHASE10A_SOURCE_REPLAY.json); [static module rows](./static_architecture/modules.csv). | Static declaration starters are lexical evidence, not an elaborated authorship inventory. More modules/imports demonstrate finer boundaries, not more mathematics. |
| T9 | The intended layer direction is substantially but not perfectly respected: 15,306 of 359,542 direct declaration pairs whose two endpoints are confirmed-source-written public run against `Examples -> Source -> Algorithms -> Analysis -> FloatingPoint`. | Metric M10; [layer matrix](./current_graph/metrics/layer_dependency_matrix.csv); [layer diagram](./figures/layer_dependency_diagram.svg). | A direction-opposing edge is a review signal, not automatically an architectural defect. Some cases may indicate a classification or ownership mismatch. |
| T10 | Proof-hygiene checks found no source `sorry`, `admit`, `sorryAx`, explicit axiom command, or `unsafe` command in 2,839 library files; the compiled graph has no direct edge to `sorryAx`, no unsafe declaration, and no unrecognized project-owned axiom. | [proof-hygiene report](./TIMINGS_AND_PROOF_HYGIENE.md); [source occurrences](./hygiene/source_proof_hygiene_code_occurrences.csv); [compiled evidence](./hygiene/proof_hygiene_results.csv). | Six `native_decide`-generated internal axiom helpers remain part of the trusted-code story, and sampled endpoint axiom reports also use ordinary Lean principles such as choice. Absence of proof holes does not establish source faithfulness. |
| T11 | Under the exact historical Phase 10A schema, incoming-reference coverage of environment-public declarations is nearly unchanged, while cross-module utilization is higher under the reorganized ownership boundaries. | Metrics M13–M15; [historical comparison](./HISTORICAL_COMPARISON.md#exact-declaration-graph-comparison). | The cross-module increase is strongly boundary-confounded. Because historical raw names/edges are missing, stable-edge, rename/move, and named-chain before/after comparisons are unavailable. |
| T12 | The recorded source snapshot is accepted by the exact Lean/Lake environment through a same-commit cached full-build verification; fresh compilation attempts reached no Lean elaboration error before storage termination. | [build provenance](./provenance/BUILD_AND_ENVIRONMENT.md) and [build-attempt table](./build/build_attempts.csv). | This is not a successful clean full build, and 2.80 seconds is not a clean or incremental compilation time. Compilation acceptance does not establish correspondence with Higham. |
| T13 | Direct public-type exposure is measurable rather than inferred: 650/47,890 confirmed-source-written public declarations (1.357277%) directly expose at least one environment-nonpublic project target in their elaborated type. The reserved-target stratum has zero sources and zero pairs. In the canonical Algorithms/Analysis/FloatingPoint subset, the union of all retained exposure-review signals is 743/17,547 declarations (4.234342%) and 1,304 unique pairs. | Metrics M16–M18; [public-type summary](./current_graph/metrics/public_type_exposure_summary.json); [declaration rows](./current_graph/metrics/public_type_exposure_declarations.csv); [edge rows](./current_graph/metrics/public_type_exposure_edges.csv). | Signals overlap and are not defects or an API-quality score. Internal proof helpers can be benign; the analysis does not pretty-print signatures, unfold transitive definitions, or test external clients. |
| T14 | On the induced graph of all 49,573 conservatively confirmed-source-written declarations, including public and nonpublic names, 48,066 (96.960039%) lie in the largest of 319 weak components; all 49,573 induced strong components are singletons. | Metric M19; [component summary](./current_graph/metrics/source_written_components_summary.json); [size distribution](./current_graph/metrics/source_written_component_size_distribution.csv). | Weak connectedness forgets direction and does not establish reuse, usefulness, or API quality. An induced singleton can still connect through excluded generated or unresolved names. |
| T15 | Aggregate reachability is now enumerated for every public entry point: the authoritative table has 479 entry modules × three declaration universes = 1,437 rows, using compiled closures for 439 entries and validated static fallbacks for 40 declaration-free entries. | [Complete entry-point exposure](./current_graph/metrics/public_entrypoint_exposure_all.csv); validation fields in the [public-type summary](./current_graph/metrics/public_type_exposure_summary.json). | The earlier table's 117 unobserved zero rows are superseded. Module-ownership reachability is not practical consumability; the 15 compiled clients remain the stronger user-facing case study. |
| T16 | Reuse leaders can be inspected without mixing declaration universes: four universes × eight metrics × the top 100 produce 3,200 ranked rows. The derived product is exactly `transitive_downstream_consumer_count * (1 + downstream_depth_scc_condensation)`. | [Reuse-leader table](./current_graph/metrics/reuse_leaders_by_universe.csv); [definitions and validation](./current_graph/metrics/reuse_leaders_by_universe_summary.json). | The product is a per-declaration heuristic, not a cohesion score and not aggregable; it conflates reach and depth and is dominated by large reach values. All consumers are drawn from the all-project universe. |

## Quantitative metric ledger

This ledger supplies the numerator, denominator, exact universe, filters, and
raw artifact/columns for every percentage used in this dossier. For M1–M6 and
M8, the authoritative 27-row definition surface is
[`incoming_and_cross_boundary_coverage_contract.csv`](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv),
columns `universe,metric,numerator,denominator,percent,percentage_formula,
exact_universe_filter,exact_metric_filter,consumer_and_dependency_universe,
materialized_artifact,materialized_columns,authorship_artifact,
authorship_columns,underlying_raw_artifacts,underlying_raw_columns`. Its
confirmed-source-written universe is joined from
[`declaration_origins_and_authorship.csv`](./current_graph/metrics/declaration_origins_and_authorship.csv),
columns `name,module,is_public,is_internal,is_private,is_reserved_name,
has_direct_selection_range,selection_source_token,authorship_class,
classifier_evidence`.

| Metric | Numerator / denominator | Result | Exact universe and filters | Raw artifact and columns |
|---|---:|---:|---|---|
| M1. Incoming project-reference coverage | 35,889 / 47,890 | 74.940489% | Target satisfies `is_public=true AND authorship_class=confirmed_source_written`; consumer may be any project declaration; `direct_project_consumer_count >= 1`. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,at_least_one_incoming_project_reference`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M2. Cross-module use | 12,584 / 47,890 | 26.276885% | Same target universe/classifier as M1; `used_by_different_module=true`, meaning at least one direct all-project consumer has a different owner module. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,used_by_at_least_one_different_module`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M3. Cross-layer use | 5,962 / 47,890 | 12.449363% | Same target universe/classifier as M1; `used_by_different_layer=true`, meaning at least one direct all-project consumer has a different path-derived layer. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,used_by_at_least_one_different_layer`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M4. Multiple consumer modules | 9,260 / 47,890 | 19.335978% | Same target universe/classifier as M1; `used_by_multiple_modules=true`, meaning direct all-project consumers occupy at least two owner modules. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,used_by_multiple_consumer_modules`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M5. Multiple consumer domains | 5,126 / 47,890 | 10.703696% | Same target universe/classifier as M1; `used_by_multiple_domains=true`, meaning direct all-project consumers occupy at least two deterministic audit-classified domains. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,used_by_multiple_consumer_domains`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M6. Participation in a nontrivial multi-step chain | 46,811 / 47,890 | 97.746920% | Same target universe/classifier as M1; `dependency_depth_scc_condensation >= 2 OR downstream_depth_scc_condensation >= 2`, with all project declarations eligible along paths. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,participates_in_nontrivial_multistep_chain`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M7. Largest weak-component coverage | 46,445 / 47,890 | 96.982669% | Induced undirected graph on declarations satisfying `is_public=true AND authorship_class=confirmed_source_written`; largest weak component. Edge direction is deliberately forgotten only for this metric. | [Components](./current_graph/metrics/components.csv), columns `universe,component_kind,size`, row class `confirmed_source_written_public,weak_induced`; denominator from [declaration inventory](./current_graph/metrics/declaration_inventory.csv), `universe,universe_denominator`; exact universe/classifier evidence in the [coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), `exact_universe_filter,authorship_artifact,authorship_columns`, and [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M8. Project-graph isolates | 143 / 47,890 | 0.298601% | Same target universe/classifier as M1; `isolated_in_project_graph=true`, meaning neither an incoming nor outgoing direct all-project pair. External dependencies are excluded. | [Coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `confirmed_source_written_public,neither_incoming_nor_outgoing_project_edge`, exact contract columns listed above; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), exact columns listed above. |
| M9. Source declarations directly consuming lower reusable layers | 22,062 / 30,289 | 72.8383% | Consumer is confirmed-source-written public and owned by `Source`; at least one direct edge targets a confirmed-source-written public declaration owned by `Algorithms`, `Analysis`, or `FloatingPoint`. | Join [direct project dependencies](./current_graph/metrics/direct_project_dependencies.csv.gz), columns `source,target,source_layer,target_layer`, with [origins/authorship](./current_graph/metrics/declaration_origins_and_authorship.csv), columns `name,module,is_public,authorship_class`; numerator is distinct `source`, denominator is all Source declarations passing the same visibility/authorship filter. |
| M10. Direction-opposing logical pairs | 15,306 / 359,542 | 4.2571% | Unique direct pairs for which **both** endpoints are confirmed-source-written public; numerator has `against_intended_layer_direction=true` relative to `Examples > Source > Algorithms > Analysis > FloatingPoint`. | Join [direct project dependencies](./current_graph/metrics/direct_project_dependencies.csv.gz), columns `source,target,source_layer,target_layer,against_intended_layer_direction`, with [origins/authorship](./current_graph/metrics/declaration_origins_and_authorship.csv), columns `name,is_public,authorship_class`. |
| M11. Uniform Source/Higham path coverage | 1,405 / 1,414 | 99.3635% | All physical Source-layer modules in `NumStability.lean` plus `NumStability/**/*.lean`; numerator matches exact `NumStability.Source.Higham.ChapterNN...`; the nine other Source modules are the Source/Higham root and coherent CrossChapter paths. | [static modules](./static_architecture/modules.csv), columns `module,source_path,physical_layer`; filter `physical_layer=Source`, then exact module-path pattern. Chapter-root presence is separately in [chapter hierarchy](./static_architecture/chapter_hierarchy.csv), columns `chapter,canonical_aggregate_module_present`. |
| M12. Practical client-probe success | 15 / 15 | 100% | The predeclared stratified sample only; declarations exclude Source/Higham, private/internal, generated, and static compatibility candidates. A success requires a separately compiled minimal client theorem with a fresh target output and cached exact-commit imports. | [Probe results](./probes/results.csv), columns `probe_id,declaration,client_status,client_exit_status,client_fresh_output,client_source,client_source_sha256,client_olean_sha256`; the retained `client_source` files show the selected declarations used in the client theorems. Sample definition: [manifest](./probes/PREDECLARED_SAMPLE.csv). The separate visibility percentage is also 15/15 from `check_status`; narrow Source-free closure is 15/15 from [closure CSV](./probes/narrow_import_closure.csv), `reachable_source_modules`. |
| M13. Phase 10A public incoming coverage | 40,963 / 56,187 | 72.905% | Historical root-module environment; Phase 10A “public” means neither `isPrivateName` nor `Name.isInternalDetail`; generated/reserved names were not excluded; unique type/body-union pair incoming to target. | [historical baseline JSON](./historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json), columns `declarations.visibility_counts.public`, `declarations.graph_metrics.public_referenced_somewhere`; contract in [recovery JSON](./historical/PHASE10A_RECOVERY.json), `headline_metrics`. |
| M14. Current incoming coverage under the exact Phase 10A schema | 37,997 / 52,332 | 72.608% | Same exact historical root-module, visibility, generated-name, ownership, and union-edge filters as M13, replayed unchanged on the audited commit. This is **not** the v2 public universe of 58,120. | [Current exact-schema summary](./historical/phase10a_exact_current_summary.json), flat paths `visibility_counts.public`, `graph_metrics.public_referenced_somewhere`; raw [exact current stream](./raw/phase10a_exact_current.tsv.gz), `DECL,SIGDEP,BODYDEP` records. |
| M15. Cross-module public use under the exact Phase 10A schema | historical 8,371 / 56,187; current 12,795 / 52,332 | 14.898%; 24.450% | Same exact Phase 10A public universe as M13/M14; target has an incoming unique union pair whose consumer is owned by another module. The difference is boundary-sensitive. | Historical [baseline JSON](./historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json), nested path `declarations.graph_metrics.public_referenced_from_another_module`; current [exact-schema summary](./historical/phase10a_exact_current_summary.json), flat path `graph_metrics.public_referenced_from_another_module`; definitions in [recovery JSON](./historical/PHASE10A_RECOVERY.json). |
| M16. Environment-public sources with a nonpublic type target | 2,259 / 58,120 | 3.886786% | Source is any project declaration with `is_public=true` (generated/unresolved retained); numerator has at least one unique direct project pair with `occurs_in_type=true` and target `is_internal=true OR is_private=true`. | [Exhaustive environment-public edge rows](./current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv), distinct `source` over columns `source,source_module,source_authorship_class,target,target_module,target_is_internal,target_is_private,target_is_reserved_name,target_authorship_class,occurs_in_body_also`; denominator from [origins/authorship](./current_graph/metrics/declaration_origins_and_authorship.csv), `name,is_public`; formula and validation in [public-type summary](./current_graph/metrics/public_type_exposure_summary.json), `environment_public_source_universe,review_signals`. |
| M17. Confirmed-source-written public sources with a nonpublic type target | 650 / 47,890 | 1.357277% | Source satisfies `is_public=true AND authorship_class=confirmed_source_written`; numerator has at least one unique direct project pair with `occurs_in_type=true` and environment-nonpublic target. | [Public-type declaration rows](./current_graph/metrics/public_type_exposure_declarations.csv), distinct `source` where `nonpublic_target_edges>0`, columns `source,source_layer,nonpublic_target_edges,candidate_reasons`; pair evidence in [edge rows](./current_graph/metrics/public_type_exposure_edges.csv), `source,target,exposure_nonpublic_target`; denominator/classifier in [origins/authorship](./current_graph/metrics/declaration_origins_and_authorship.csv), `name,is_public,authorship_class`; summary fields `source_universe,review_signals`. |
| M18. Canonical public type-exposure review-signal union | 743 / 17,547 | 4.234342% | Source satisfies `is_public=true AND authorship_class=confirmed_source_written` and effective layer is Algorithms, Analysis, or FloatingPoint; numerator is the distinct-source union of the overlapping nonpublic, generated/authorship-unresolved, Source-layer, compatibility, Examples, and reserved-target direct-type signals. | [Public-type declaration rows](./current_graph/metrics/public_type_exposure_declarations.csv), `source,source_layer,nonpublic_target_edges,generated_or_authorship_unresolved_target_edges,reserved_target_edges,canonical_to_source_edges,static_compatibility_candidate_edges,examples_candidate_edges,candidate_reasons`; [edge union](./current_graph/metrics/public_type_exposure_edges.csv), `source,target,exposure_nonpublic_target,exposure_generated_or_authorship_unresolved_target,exposure_reserved_target,exposure_canonical_to_source,exposure_to_static_compatibility_candidate,exposure_to_examples_candidate`; exact 743-source/1,304-pair union and 17,547 denominator in [summary](./current_graph/metrics/public_type_exposure_summary.json), `canonical_source_written_public_universe,review_signals`. |
| M19. Largest all-source-written induced weak component | 48,066 / 49,573 | 96.960039% | Universe is every declaration with `authorship_class=confirmed_source_written`, public and nonpublic retained; graph contains only direct project pairs whose two endpoints are in that universe, then forgets direction for WCCs. | [Size distribution](./current_graph/metrics/source_written_component_size_distribution.csv), row `confirmed_source_written,weak_induced,48066`, columns `universe,universe_declarations,component_kind,component_size,component_count,declarations_covered,percent_of_universe,edge_filter,raw_artifacts,raw_columns`; [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv), `name,is_public,authorship_class`; [summary](./current_graph/metrics/source_written_components_summary.json), `universe,weak_components`. |

### Counts that should be cited without inventing a percentage

- The current compiled universe has 77,246 NumStability-owned environment
  declarations and 458,414 unique direct project-to-project declaration pairs.
  Type edges number 283,049; body/proof edges 406,528; 231,163 occur in both;
  268,231 pairs cross owner modules. Source: [graph summary](./current_graph/metrics/summary.json),
  fields `declaration_inventory.all_environment_declarations` and
  `direct_project_graph.*`.
- The correct graph has 77,245 SCCs over 77,246 nodes; its only nontrivial SCC
  has two generated internal partial-recursion helpers. The SCC-condensation
  maximum depth and retained longest path are 65 edges. Source: the same
  [graph summary](./current_graph/metrics/summary.json), `component_and_depth`,
  and [longest path](./current_graph/metrics/longest_dependency_path.csv).
- `NumStability.gamma_mul` has 81 direct consumers and 4,739 transitive
  downstream consumers in 362 modules and 22 audit-classified domains.
  Source: [declaration metrics](./current_graph/metrics/declaration_metrics.csv.gz),
  exact row name and columns listed in T6.
- The separated reuse-leader table contains 3,200 rows: the top 100 for each
  of eight metrics in each of four declaration universes. All consumer counts
  use the all-project universe. `NumStability.FPModel` ranks first for the
  derived product in all four universes with
  `13,992 * (1 + 51) = 727,584`. Source:
  [reuse-leader rows](./current_graph/metrics/reuse_leaders_by_universe.csv),
  columns `universe,consumer_universe,rank_metric,rank,value,name,
  transitive_downstream_consumers,downstream_depth`, and
  [summary](./current_graph/metrics/reuse_leaders_by_universe_summary.json).
  This is a ranking heuristic, not a cohesion score.
- The complete entry-point table has 1,437 rows (479 entry modules × three
  declaration universes): 439 entries use compiled import closures and 40
  declaration-free entries use validated static fallbacks. It supersedes 117
  previously unobserved zero rows. Source:
  [entry-point exposure](./current_graph/metrics/public_entrypoint_exposure_all.csv),
  columns `entry_module,closure_basis,universe,reachable_declarations,
  universe_declarations,percent,coverage_status`, and validation fields in the
  [public-type summary](./current_graph/metrics/public_type_exposure_summary.json).
- The source tree contains 2,839 Lean modules/files and 1,183,374 code-bearing
  lines under the static lexical definition. Source: [static summary](./static_architecture/summary.json),
  `totals.lean_source_files`, `totals.code_bearing_lines`; distribution by
  module is in [modules.csv](./static_architecture/modules.csv).
- The source scan found zero code occurrences of `sorry`, `admit`, `sorryAx`,
  explicit axiom declarations, or `unsafe` commands in those 2,839 files. The
  compiled scan found zero `sorryAx` edges among 3,963,823 all-scope direct
  dependency rows, zero unsafe declarations among 77,246 declarations, and six
  generated internal `native_decide` axiom helpers. Source:
  [proof-hygiene results](./hygiene/proof_hygiene_results.csv) and
  [summary](./hygiene/proof_hygiene_summary.json).

## Short Greek replacement paragraph

Στην ακριβή έκδοση
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`, η βιβλιοθήκη NumStability
παρουσιάζει μετρήσιμη εσωτερική συνοχή και επαναχρησιμοποίηση: 35.889 από τις
47.890 δημόσιες δηλώσεις που επιβεβαιώνονται συντηρητικά από το αντίστοιχο
όνομα στον πηγαίο κώδικα έχουν τουλάχιστον μία εισερχόμενη αναφορά από δήλωση
του έργου (74,940489%, M1), ενώ 12.584/47.890 χρησιμοποιούνται από διαφορετικό
module (26,276885%, M2) και 46.811/47.890 συμμετέχουν σε κατευθυντική αλυσίδα
τουλάχιστον δύο βημάτων (97,746920%, M6). Η σύνθεση δεν περιορίζεται σε
συγκεντρωτικά ποσοστά: ένα θεώρημα οπισθόδρομου σφάλματος για επίλυση μέσω QR
επαναχρησιμοποιεί, σε επαληθευμένη αλυσίδα 14 άμεσων ακμών και επτά modules,
αποτελέσματα παραγοντοποίησης Householder, κατασκευής ανακλαστήρων, νόρμας και
τελικά τον νόμο του μοντέλου στρογγύλευσης για την τετραγωνική ρίζα. Στο
induced γράφημα όλων των 49.573 source-token-confirmed δηλώσεων, 48.066 ανήκουν
στη μεγαλύτερη ασθενώς συνεκτική συνιστώσα (96,960039%, M19), ενώ ο χωριστός
έλεγχος της δημόσιας επιφάνειας τύπων βρήκε ότι 650/47.890 τέτοιες δημόσιες
δηλώσεις εκθέτουν άμεσα τουλάχιστον έναν environment-nonpublic project στόχο
(1,357277%, M17). Το πρώτο είναι συνδεσιμότητα, όχι επαναχρησιμοποίηση, και το
δεύτερο είναι σήμα ανασκόπησης, όχι αυτομάτως ελάττωμα API. Επιπλέον, και τα 15
προκαθορισμένα εξωτερικά probes πέτυχαν τόσο σε ανεξάρτητο `#check` όσο και σε
ελάχιστο client theorem (15/15 = 100%, M12) με στενά imports. Τα στοιχεία αυτά
τεκμηριώνουν τυπική σύνθεση και πρακτική χρηστικότητα για το συγκεκριμένο
δείγμα· δεν αποδεικνύουν από μόνα τους πιστότητα προς το βιβλίο του Higham,
καθολική ευχρηστία ή επιτυχημένο καθαρό full build.

Every percentage in this paragraph uses the exact universes, filters, raw
artifacts, and columns defined in M1, M2, M6, M12, M17, and M19 above.

## Longer Greek subsection: concrete compositional chains

### Επαληθεύσιμη σύνθεση αποτελεσμάτων

Στα ακόλουθα παραδείγματα η φορά της ακμής είναι πάντοτε «καταναλωτής ->
εξάρτηση». Επομένως, κάθε διαδοχικό βέλος δηλώνει ότι ο αριστερός όρος
αναφέρεται άμεσα στον δεξιό όρο μέσα στον elaborated τύπο ή στο σώμα/την
απόδειξή του. Οι ακμές δεν προέρχονται από απλή αναζήτηση κειμένου ή από κοινά
imports: αντιστοιχούν μία προς μία στις γραμμές του compiled graph στο
[`representative_chain_raw_compiled_rows.csv`](./current_graph/chains/representative_chain_raw_compiled_rows.csv).

Το ισχυρότερο παράδειγμα σύνθεσης υψηλού επιπέδου είναι η αλυσίδα C05. Το
θεώρημα
`NumStability.fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid`
στο `Algorithms/LinearSystems/QR/QRSolve.lean:5470` εξαρτάται από το
`NumStability.fl_householderQR_R_frobNorm_le_gammaHigham_of_global_gammaValid`
και κατόπιν από μια ακολουθία αποτελεσμάτων για το σφάλμα της παραγοντοποίησης
Householder, το βήμα εφαρμογής ενός ανακλαστήρα, την κατασκευή του διανύσματος
Householder και τον υπολογισμό της Ευκλείδειας νόρμας. Μετά από 14 άμεσες
ακμές, η αλυσίδα καταλήγει στο
`NumStability.FPModel.model_sqrt` του
`FloatingPoint/Model.lean:93`. Συνολικά διασχίζει 15 δηλώσεις, επτά modules,
τις περιοχές QR, Norms και FloatingPoint, και τα layers Algorithms και
FloatingPoint. Το ίδιο αρχικό θεώρημα έχει ξεχωριστή άμεση body-edge προς το
`NumStability.fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid`,
δηλαδή συνδυάζει τον κλάδο σφάλματος της παραγοντοποίησης με ανεξάρτητο κλάδο
για το δεξιό μέλος και την οπισθοαντικατάσταση. Αυτή είναι ισχυρή ένδειξη ότι
ένα αλγοριθμικό endpoint συναρμολογείται από χαμηλότερα, επαναχρησιμοποιήσιμα
αποτελέσματα. Παραμένει, ωστόσο, ένα επιλεγμένο proof spine: δεν καταγράφει
κάθε υπόθεση ή κλάδο, ούτε αποδεικνύει πληρότητα του QR development ή πιστότητα
στην έντυπη πηγή.

Η αλυσίδα C06 διορθώνει με ιδιαίτερη ακρίβεια την παλαιότερη περιγραφή της
σχέσης μεταξύ των Κεφαλαίων 9 και 12. Το θεώρημα
`NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source`, που
ανήκει στο
`Source.Higham.CrossChapter.LUSolverWeights.Doolittle` και όχι στο Chapter12,
έχει άμεση body-edge προς το
`NumStability.higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source`
του Chapter09. Από εκεί ακολουθεί επαληθευμένη αλυσίδα επτά ακμών μέσα από το
Doolittle closure μέχρι το `NumStability.gamma_mul`. Παράλληλα, το αρχικό
CrossChapter θεώρημα έχει ακμή τόσο στον τύπο όσο και στο σώμα προς το
`NumStability.higham12_1_SolverWBound`, δηλαδή προς το κατηγορήμα ορίου του
Chapter12. Έτσι, η τυπική σύνθεση των δύο κεφαλαίων είναι πραγματική αλλά
εντοπίζεται σκόπιμα σε CrossChapter ownership. Η εξαντλητική αναζήτηση με
αφετηρία και τις 96 Chapter12-owned δηλώσεις και στόχο οποιαδήποτε από τις
6.081 Chapter09-owned δηλώσεις βρήκε μηδενικές άμεσες ή μεταβατικές διαδρομές.
Δεν πρέπει, συνεπώς, να διατυπωθεί ότι ένα θεώρημα που ανήκει στο Chapter12
εξαρτάται από θεώρημα που ανήκει στο Chapter09. Το σωστό συμπέρασμα είναι ότι
ένα ρητά cross-chapter endpoint συνθέτει χωριστά την παραγοντοποίηση του
Κεφαλαίου 9 και τη σημασιολογία του ορίου επίλυσης του Κεφαλαίου 12.

Η C03 παρέχει ένα μικρότερο αλλά καθαρό διαστρωματικό παράδειγμα:

```text
NumStability.matMul_error_bound
  -> NumStability.matVec_error_bound
  -> NumStability.dotProduct_error_bound
  -> NumStability.fl_sum_error_init
  -> NumStability.FPModel.model_add
```

Οι τέσσερις body-edges περνούν από πέντε modules και συνδέουν διαδοχικά
πολλαπλασιασμό μητρών, γινόμενο μήτρας-διανύσματος, εσωτερικό γινόμενο,
ανάλυση αθροίσματος και το βασικό μοντέλο στρογγύλευσης της πρόσθεσης. Σε
συνδυασμό με την C05 και την C06, το παράδειγμα αποτρέπει την επιλεκτική
στήριξη σε μία μόνο ευνοϊκή οικογένεια θεωρημάτων. Οι δώδεκα συνολικά
στρωματοποιημένες αλυσίδες καλύπτουν επίσης τριγωνικές λύσεις, αντιστροφή
μητρών, πολυωνυμική παραγώγιση, Cholesky, ελάχιστα τετράγωνα, εκτίμηση
κατάστασης, νόρμες και FFT. Το κοινό συμπέρασμα είναι τυπική
επαναχρησιμοποίηση και συνθετικός typechecking, όχι ανεξάρτητη πιστοποίηση της
μαθηματικής μετάφρασης.

Οι πλήρεις ιδιοκτήτες, γραμμές πηγαίου κώδικα, είδη δηλώσεων, ταξινομήσεις
layer/domain/chapter, statement excerpts, τύποι ακμών και ακριβή raw-row keys
βρίσκονται στα
[`representative_dependency_chains.csv`](./current_graph/chains/representative_dependency_chains.csv),
[`representative_chain_nodes.csv`](./current_graph/chains/representative_chain_nodes.csv),
[`representative_chain_edges.csv`](./current_graph/chains/representative_chain_edges.csv)
και
[`representative_chain_branch_edges.csv`](./current_graph/chains/representative_chain_branch_edges.csv).

Η συστηματική κατάταξη ενισχύει την αναπαραγωγιμότητα της επιλογής
παραδειγμάτων χωρίς να δημιουργεί έναν τεχνητό «δείκτη συνοχής». Το
[`reuse_leaders_by_universe.csv`](./current_graph/metrics/reuse_leaders_by_universe.csv)
χωρίζει τέσσερα σύμπαντα δηλώσεων και ορίζει ρητά το βοηθητικό γινόμενο
`transitive_downstream_consumer_count * (1 + downstream_depth_scc_condensation)`.
Για παράδειγμα, το `NumStability.FPModel` έχει 13.992 μεταβατικούς consumers
και downstream depth 51, άρα τιμή 727.584. Η τιμή αυτή είναι μόνο ευρετική
σειρά προτεραιότητας: συγχέει εμβέλεια και βάθος, κυριαρχείται από την
εμβέλεια και δεν αποδεικνύει ποιότητα API ή πιστότητα πηγής. Αντίστοιχα, η
μεγάλη ασθενώς συνεκτική συνιστώσα των 48.066/49.573 confirmed-source-written
δηλώσεων (M19) τεκμηριώνει συνδεσιμότητα μετά την αφαίρεση της φοράς, όχι ότι
όλες οι δηλώσεις επαναχρησιμοποιούνται.

## Compact Greek headline-metrics table

| Μετρική | Αποτέλεσμα | Ακριβές σύμπαν / φίλτρο | Raw τεκμήριο / στήλες |
|---|---:|---|---|
| Δημόσιες, source-token-confirmed δηλώσεις με εισερχόμενη project αναφορά | 35.889/47.890 = 74,940489% | Στόχος στο `confirmed_source_written_public`, οποιοσδήποτε project consumer, τουλάχιστον μία άμεση ακμή | M1: [coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv), row `at_least_one_incoming_project_reference`, ακριβείς contract/authorship/raw στήλες |
| Ίδιο σύμπαν, χρήση από άλλο module | 12.584/47.890 = 26,276885% | Όπως M1, με διαφορετικό owner module consumer/target | M2: ίδιο contract, row `used_by_at_least_one_different_module`, και [authorship classifier](./current_graph/metrics/declaration_origins_and_authorship.csv) |
| Ίδιο σύμπαν, χρήση από άλλο layer | 5.962/47.890 = 12,449363% | Όπως M1, με διαφορετικό path-derived layer | M3: ίδιο contract, row `used_by_at_least_one_different_layer`, και ίδιος classifier |
| Ίδιο σύμπαν, συμμετοχή σε πολυβηματική αλυσίδα | 46.811/47.890 = 97,746920% | SCC-condensation dependency depth >= 2 ή downstream depth >= 2 | M6: ίδιο contract, exact metric filter/materialized/raw/authorship columns |
| Μεγαλύτερη ασθενώς συνεκτική συνιστώσα δημόσιων source-token-confirmed | 46.445/47.890 = 96,982669% | Induced undirected graph μόνο στο ίδιο σύμπαν | M7: [components](./current_graph/metrics/components.csv), `universe,component_kind,size`; universe predicate/classifier από το coverage contract και το origins/authorship artifact |
| Μεγαλύτερη ασθενώς συνεκτική συνιστώσα όλων των source-token-confirmed | 48.066/49.573 = 96,960039% | Public και nonpublic· induced ακμές με δύο confirmed-source-written endpoints | M19: [size distribution](./current_graph/metrics/source_written_component_size_distribution.csv), ακριβείς universe/size/percent/edge/raw στήλες |
| Δημόσια source-token-confirmed επιφάνεια τύπων προς nonpublic στόχο | 650/47.890 = 1,357277% | Direct elaborated type pairs· source confirmed-source-written public, target environment-nonpublic | M17: [declaration rows](./current_graph/metrics/public_type_exposure_declarations.csv), [edge rows](./current_graph/metrics/public_type_exposure_edges.csv), και classifier |
| Union σημάτων τύπου στο canonical υποσύνολο | 743/17.547 = 4,234342% | Confirmed-source-written public source στα Algorithms/Analysis/FloatingPoint· union επικαλυπτόμενων σημάτων | M18: ίδια public-type artifacts και [summary](./current_graph/metrics/public_type_exposure_summary.json), `canonical_source_written_public_universe,review_signals` |
| Source δηλώσεις που καταναλώνουν κατώτερο reusable layer | 22.062/30.289 = 72,8383% | Source consumer και lower-layer target, και τα δύο confirmed-source-written public | M9: join dependency `source,target,source_layer,target_layer` με origin `name,is_public,authorship_class` |
| Ακμές αντίθετα από την επιδιωκόμενη φορά | 15.306/359.542 = 4,2571% | Direct pairs με δύο confirmed-source-written public endpoints | M10: ίδιο join, `against_intended_layer_direction` |
| Πρακτικά client probes | 15/15 = 100% | Μόνο το προκαθορισμένο στρωματοποιημένο δείγμα· fresh probe outputs, cached exact-commit imports | M12: [results](./probes/results.csv), `declaration,client_status,client_exit_status,client_fresh_output,client_source,client_source_sha256,client_olean_sha256` |

These percentages are not independent estimates of one latent “cohesion
score”; no such aggregate score is defined or used.

## Proposed figure captions

1. **Layer dependency diagram — Greek thesis caption.** «Ακμές άμεσης
   εξάρτησης μεταξύ αρχιτεκτονικών layers της NumStability στο commit
   `045daf2`. Η φορά είναι καταναλωτής -> εξάρτηση. Οι τιμές μετρούν μοναδικά
   ζεύγη δηλώσεων στο πλήρες environment-owned σύμπαν· οι επισημασμένες
   αντίστροφες ακμές αποτελούν υποψήφια σημεία αρχιτεκτονικής ανασκόπησης και
   όχι αυτομάτως σφάλματα.» [SVG](./figures/layer_dependency_diagram.svg) ·
   [PNG](./figures/layer_dependency_diagram.png)

2. **Domain heatmap — Greek thesis caption.** «Θερμικός χάρτης άμεσων
   elaborated εξαρτήσεων ανά μαθηματικό domain στο commit `045daf2`, με
   λογαριθμική χρωματική κλίμακα για να παραμένουν ορατές τόσο οι πυκνές όσο
   και οι αραιές συνδέσεις. Οι γραμμές είναι domains καταναλωτών και οι στήλες
   domains εξαρτήσεων. Τα domains προκύπτουν από τον καταγεγραμμένο
   ντετερμινιστικό ταξινομητή paths/names και δεν αποτελούν kernel facts.»
   [SVG](./figures/domain_dependency_heatmap.svg) ·
   [PNG](./figures/domain_dependency_heatmap.png)

3. **Cross-chapter LU/solver chain — Greek thesis caption.** «Επαληθευμένη
   αλυσίδα δηλώσεων για τη σύνθεση του Doolittle backward-error αποτελέσματος
   του Κεφαλαίου 9 με το `SolverWBound` του Κεφαλαίου 12. Το endpoint ανήκει
   ρητά στο `Source.Higham.CrossChapter.LUSolverWeights`: ο κύριος κλάδος
   καταλήγει μέσω επτά body-edges στο `gamma_mul`, ενώ ξεχωριστή type/body-edge
   οδηγεί στο κατηγόρημα του Κεφαλαίου 12. Η φορά είναι καταναλωτής ->
   εξάρτηση.» [SVG](./figures/crosschapter_lu_solver_chain.svg) ·
   [PNG](./figures/crosschapter_lu_solver_chain.png)

The exact matrix values behind captions 1 and 2 are in
[layer_dependency_matrix.csv](./current_graph/metrics/layer_dependency_matrix.csv)
and
[domain_dependency_matrix.csv](./current_graph/metrics/domain_dependency_matrix.csv).
The exact compiled rows behind caption 3 are in
[representative_chain_raw_compiled_rows.csv](./current_graph/chains/representative_chain_raw_compiled_rows.csv).

## Statements that must not be made from this evidence

1. Do not say that the library completed a clean full build, or that it clean-
   built in 2.80 seconds. The only completed full-build verification reused
   exact same-commit cached outputs; fresh attempts were storage-limited.
2. Do not say that successful compilation or an elaborated dependency proves
   fidelity to Higham. It proves acceptance and formal reference in the
   recorded Lean environment.
3. Do not say that 96.982669% weak-component coverage means that 96.982669% of
   declarations are reused or useful. The exact fraction is 46,445/47,890 in
   the confirmed-source-written public induced undirected graph (M7); weak
   connectivity forgets edge direction.
4. Do not call the 12,001 confirmed-source-written public declarations with no
   incoming project edge “unused” or “redundant”. They are 12,001/47,890 =
   25.059511% in the exact M1 universe/filter, from the [coverage contract](./current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv)
   row `confirmed_source_written_public,no_incoming_project_edge`; any may be an
   intended external endpoint.
5. Do not call generated/reserved environment declarations handwritten public
   API. Environment visibility and source-token confirmation are separate
   fields in [origins/authorship](./current_graph/metrics/declaration_origins_and_authorship.csv),
   columns `is_public,is_reserved_name,authorship_class`.
6. Do not conflate a direct edge with transitive reach. Cite an exact direct
   row for each adjacent arrow and a retained path for transitive claims.
7. Do not infer that an import without a logical declaration edge is removable.
   It may supply notation, tactics, macros, attributes, or typeclass instances.
8. Do not infer redundancy from exact elaborated statement equality. Equal
   propositions may be intentional source labels, compatibility names, or
   independent proof endpoints.
9. Do not interpret high fan-in as proof of public-interface quality. It is an
   internal-consumption measure.
10. Do not generalize the 15/15 probe result to all public declarations. The
    denominator is the predeclared, nonrandom, stratified 15-API sample defined
    in M12.
11. Do not say that a Chapter12-owned declaration depends on a Chapter09-owned
    declaration. The exhaustive C06 re-check found zero such paths; the
    verified bridge is CrossChapter-owned.
12. Do not describe the current architecture as perfectly layered. In the
    strict two-endpoint public/source-token-confirmed universe, 15,306/359,542
    direct pairs (4.2571%, M10) oppose the intended layer direction.
13. Do not say that proof hygiene is “axiom-free” without qualification. Six
    internal helpers are generated by `native_decide`; representative theorem
    probes report ordinary Lean foundational principles.
14. Do not describe the historical 14.898% -> 24.450% cross-module change as a
    corresponding increase in mathematical reuse. Both fractions use the
    Phase 10A environment-public filter (M15), and module splitting strongly
    changes the boundary measurement.
15. Do not claim detailed before/after preservation, addition, removal, move,
    rename, or chain survival. The historical raw declaration/edge stream is
    missing, so only exact-schema aggregate comparison is justified.
16. Do not describe direct nonpublic, generated/unresolved, Source,
    compatibility, Examples, or reserved type targets as API defects solely
    from the exposure scan. They are overlapping review signals; benign proof
    helpers and intentional source-facing dependencies are possible.
17. Do not add the canonical type-signal rows. The 75 nonpublic-source cases
    and 133 generated/unresolved-source cases overlap on 70 declarations; the
    exact union with the disjoint 605-source Source-layer signal is
    743/17,547, not an arithmetic sum. This union is not a quality score.
18. Do not treat the 48,066/49,573 all-source-written largest-WCC fraction as
    directional reuse. Weak connectedness forgets direction, and an induced
    singleton may connect through an excluded generated or unresolved name.
19. Do not interpret entry-module reachability as practical API usability, and
    do not cite zero exposure from the superseded
    `public_entrypoint_exposure.csv`. Its 117 unobserved zero rows were replaced
    by validated static fallbacks in `public_entrypoint_exposure_all.csv`.
20. Do not call the reuse-depth product a cohesion score or aggregate it. It is
    a per-declaration ordering heuristic with the exact formula stated in T16;
    it conflates reverse reach with depth and is dominated by large reach.

## Footnote-ready provenance and exact paths

### Commit and tool revisions

| Label | Exact value |
|---|---|
| Audited Git commit (`origin/higham_v01`, local branch and remote-tracking ref agreed at audit) | `045daf28056a6e4358d5de7c22c7a9d7acc2e80e` |
| Audit reference-resolution timestamp | `2026-09-03T11:07:13+03:00` (`Europe/Athens`; EEST) |
| Effective Phase 10A source commit | `d21a4ed5b91008a8a5bc60741765f27fcdf86edf` |
| Literal Phase 10A candidate `HEAD` recorded in its snapshot | `899003baca0fdca2714344a69c10eef4b2d3c306` |
| Clean Phase 10A reproduction-evidence commit | `21e130ac8355de8ec1a74f22a73bf103e00bc48f` |
| Recovered later audit-tool untracked-tree commit (not the Phase 10A metric source) | `8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d` |
| Lean | `4.29.0-rc3`, revision `5d86aa4032284a5242470e95fbe25f1ff506763d` |
| Mathlib | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Exact Phase 10A extractor SHA-256 | `30186d3470320983e2ada2e61fce7efaa7e6230c71348c5d37a9801526be2acd` |
| Exact Phase 10A generator SHA-256 | `fc5863b2ca4e8f2dd03d2f012c40df9f26666849073a4e5b1babc65a671d6a94` |
| Corrected current analyzer SHA-256 | `543159b9dd6645a19c736a27cda585701b66fe6134d457b4eb891dd26c842d45` |
| Coverage-contract builder SHA-256 | `1967659d5b85cd5114bfbc7dc87d41e8c09269e8cae4991d82b829f3e9de6e1a` |
| Public-type exposure analyzer SHA-256 | `1fb91f07610320ed420698e0ddd9c89bc16307c3fe81796885beed9ec7fbaf60` |
| Confirmed-source-written component analyzer SHA-256 | `df53e2de72028c1797fc5e0a68613e5bfe3f5bd1b8fbf43aa23932971f6dc05f` |
| Universe-separated reuse-leader builder SHA-256 | `a7c171d48b8c8c8295c2116866ee1a29c8f32737a53eb4867ffb8678a01abd26` |
| Current raw declarations SHA-256 | `235238fd68eb6ac31bdf30fe344e1d60755377d49ba5701efbd52f53e298f03f` |
| Current raw dependencies SHA-256 | `cf64609f72a23ad4df78a6ac30f04db78449bcb4d5b0b6ba9721f820d108c240` |

### Absolute artifact paths

Audit root:

```text
<library-repo>/tmp/library_audit/higham_v01-045daf2
```

Footnote-ready primary artifacts:

```text
<library-repo>/tmp/library_audit/higham_v01-045daf2/REPORT.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/metrics.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/ARCHITECTURE_REVIEW.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/THESIS_EVIDENCE.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/DEPENDENCY_CHAINS.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/PUBLIC_API_CONSUMABILITY.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/HISTORICAL_COMPARISON.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/TIMINGS_AND_PROOF_HYGIENE.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/provenance/BUILD_AND_ENVIRONMENT.md
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/summary.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/direct_project_dependencies.csv.gz
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/declaration_origins_and_authorship.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/public_type_exposure_summary.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/public_type_exposure_declarations.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/public_type_exposure_edges.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/environment_public_type_nonpublic_exposure_edges.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/public_entrypoint_exposure_all.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/source_written_components_summary.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/source_written_component_memberships.csv.gz
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/source_written_component_size_distribution.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/reuse_leaders_by_universe.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/metrics/reuse_leaders_by_universe_summary.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/current_graph/chains/representative_chain_raw_compiled_rows.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/probes/results.csv
<library-repo>/tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json
<library-repo>/tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json
```

## Citation safeguards

Successful compilation proves acceptance by the recorded Lean environment; it
does not prove faithfulness to the original mathematical source. A later
declaration depending on an earlier declaration proves formal reuse and
compositional typechecking, but not the independent correctness of either
translation. Error propagation through dependencies demonstrates integration,
not source fidelity. Weak connectedness, import reachability, direct logical
dependence, transitive logical dependence, public visibility, source-token
confirmation, and external client usability are different measurements and
must remain separate. Exact-statement equality is only a review signal. A
declaration with no internal consumer can still be an intentional external API
endpoint. A successful probe establishes usability for that probe, not
universal ease of use. Direct public-type exposures are overlapping review
signals, not an API-quality score; entry-module reachability is not practical
usability; and the reuse-depth product is a per-declaration ordering heuristic,
not a cohesion score.
