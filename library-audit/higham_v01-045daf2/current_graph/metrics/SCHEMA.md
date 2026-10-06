# Current elaborated graph schema

Schema: `numstability-elaborated-architecture/2.1.0`. Source commit:
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.

Edge orientation: `consumer -> dependency; A -> B means A directly references B in its elaborated type or body/proof`.

The raw dependency extractor emits one row per ordered source/target pair and
two overlapping Boolean flags, `occurs_in_type` and `occurs_in_body`.  The
analyzer validates uniqueness.  `type + body - both = all project pairs`.

Percentages are materialized in `incoming_and_cross_boundary_coverage.csv`;
the authoritative citable definitions are in
`incoming_and_cross_boundary_coverage_contract.csv`, with numerator,
denominator, formula, exact universe and predicate, authorship evidence,
materialized columns, and underlying raw artifacts/columns. Public means
environment-public (`is_internal=false` and
`is_private=false`).  Confirmed source-written is the conservative classifier
recorded in `summary.json`; likely and unresolved names are excluded.

Transitive downstream counts are exact distinct reverse-reachable project
declarations after SCC condensation.  Dependency depths are exact on that
condensation DAG.  Weak components for public/source-written universes are
computed on induced subgraphs.

Explicit declaration-to-component membership is recorded in
`weak_component_memberships.csv.gz` and
`strong_component_memberships.csv.gz`. Apparent module-level logical SCC
edges are preserved in `logical_module_scc_edge_evidence.csv` and must be
interpreted separately from the compiled import graph.

An import lacking a direct logical pair is only a review candidate.  No
incoming declaration is called unused.  Exact graph evidence does not establish
source faithfulness or universal API ease.

## Coverage metric contract

`incoming_and_cross_boundary_coverage_contract.csv`, schema
`numstability-coverage-metric-contract/1.0.0`, is the authoritative citation
surface for all 27 coverage percentages (three declaration universes times
nine predicates). It reproduces every numerical row of
`incoming_and_cross_boundary_coverage.csv` and adds:

- `percentage_formula = 100 * numerator / denominator`;
- the exact declaration-universe and metric predicates;
- the consumer/dependency universe;
- materialized and underlying raw artifact paths and exact columns; and
- the authorship-classifier artifact, columns, and evidence rule.

The universes are: all project-owned environment declarations;
environment-public declarations (`is_public=true`, equivalently
`is_internal=false AND is_private=false`); and confirmed-source-written public
declarations (`is_public=true AND
authorship_class=confirmed_source_written`). The confirmed class requires a
nonreserved name, direct Lean selection range, and an exact selected source
token matching the terminal declaration name or a namespace-qualified suffix.
That is conservative source-origin evidence, not proof of human authorship.

The nine predicates are materialized directly in
`declaration_metrics.csv.gz`: at least one incoming project reference;
different-module use; different-layer use; multiple consumer modules;
multiple consumer domains; no incoming edge; no outgoing edge; neither edge;
and nontrivial multi-step-chain participation. The last means
`dependency_depth_scc_condensation >= 2 OR
downstream_depth_scc_condensation >= 2`. The generating tool is
`current_graph/build_coverage_metric_contract.py`, SHA-256
`1967659d5b85cd5114bfbc7dc87d41e8c09269e8cae4991d82b829f3e9de6e1a`;
all 27 rows recompute exactly, as recorded in
`incoming_and_cross_boundary_coverage_contract_summary.json`.

## Confirmed-source-written induced components

`source_written_component_memberships.csv.gz` and
`source_written_component_size_distribution.csv`, schema
`numstability-source-written-components/1.0.0`, use the 49,573 declarations
with `authorship_class=confirmed_source_written`; public and nonpublic names
are both retained. An induced edge is a direct project pair whose two endpoints
belong to this universe. The 368,602 induced pairs produce 319 weak components,
with 48,066/49,573 declarations (96.960039%) in the largest and 168 singleton
weak components. They produce 49,573 singleton strong components and no
directed cycle. The percentage's numerator, denominator, edge filter, raw
artifacts, and columns are explicit in the size-distribution CSV.
Weak connectedness forgets edge direction and is not reuse, usefulness, or
public-interface evidence; a singleton in this induced graph may connect to an
excluded generated/unresolved declaration. The generating tool is
`current_graph/analyze_source_written_components.py`, SHA-256
`df53e2de72028c1797fc5e0a68613e5bfe3f5bd1b8fbf43aa23932971f6dc05f`.

## Reuse leaders separated by declaration universe

`reuse_leaders_by_universe.csv`, schema
`numstability-reuse-leaders/1.0.0`, ranks declarations separately in four
universes: all project environment, environment-public, confirmed
source-written, and confirmed source-written public. It retains the top 100
for each of eight metrics: direct fan-in; transitive downstream consumers;
downstream consumer modules, layers, domains, and chapters; downstream depth;
and the explicitly derived `reused_low_in_hierarchy_product`.

All direct and transitive consumer counts use the all-project declaration
consumer universe even when ranked declarations are filtered. The product is
defined exactly as:

```text
transitive_downstream_consumer_count
  * (1 + downstream_depth_scc_condensation)
```

It is a ranking heuristic combining reverse reach and reverse-consumer path
depth. It is **not a cohesion score**, must not be aggregated across the
library, conflates different properties, and is dominated by large reach
values. Layer and domain do not enter its formula. The tool is
`current_graph/build_reuse_leaders_by_universe.py`, SHA-256
`a7c171d48b8c8c8295c2116866ee1a29c8f32737a53eb4867ffb8678a01abd26`;
the summary records three toy/tie-break validations and exact reproduction of
the 500 applicable legacy all-project ranking rows.

## Direct public type exposure

The `numstability-public-type-exposure/1.0.0` analysis uses unique direct
project pairs with `occurs_in_type=true`. Its primary source universe contains
47,890 declarations satisfying `is_public=true AND
authorship_class=confirmed_source_written`; the parallel exhaustive
environment-public check retains all 58,120 public declarations, including
generated and authorship-unresolved names. The canonical subset is the 17,547
confirmed-source-written public declarations whose effective layer is
Algorithms, Analysis, or FloatingPoint.

The review signals are defined as follows:

- `nonpublic_target`: the target is environment-private or
  environment-internal under the v2 visibility fields;
- `generated_or_authorship_unresolved_target`: the target, of any visibility,
  is outside the confirmed-source-written class—this is not proof of
  generation;
- `generated_or_unresolved_nonpublic_target`: both preceding conditions;
- `confirmed_source_written_nonpublic_target`: a nonpublic target that passes
  the conservative source-origin classifier;
- `canonical_to_source`: a source declaration in Algorithms, Analysis, or
  FloatingPoint directly exposes a Source-layer target;
- `static_compatibility_candidate`: the target owner is marked
  `compatibility_candidate_static=true` by the static classifier;
- `reserved_target`: `Environment.isReservedName=true`, kept separate from the
  broader generated/unresolved signal; and
- `to_examples_candidate`: a non-Examples source targets the Examples layer.

Signals overlap. In the canonical universe, 75/17,547 declarations (87 pairs)
have a nonpublic target, 133/17,547 (149 pairs) have a generated/unresolved
target, and 605/17,547 (1,150 pairs) have a Source target. Nonpublic and
generated/unresolved overlap on 70 declarations and 82 pairs; the Source
signal is disjoint. The exact union is therefore 743/17,547 declarations and
1,304 pairs. Compatibility, Examples, and reserved-target counts are all zero.
These are review strata, not an API-quality or cohesion score.

`public_type_exposure_declarations.csv` contains distinct source declarations
with at least one signal;
`public_type_exposure_edges.csv` contains the unique signal-pair union; and
`environment_public_type_nonpublic_exposure_edges.csv` contains every
environment-public-to-nonpublic type edge. The analysis does not pretty-print
user-facing signatures, unfold transitive definitions, measure namespace
discoverability, or observe external clients. The tool is
`current_graph/analyze_public_type_exposure.py`, SHA-256
`1fb91f07610320ed420698e0ddd9c89bc16307c3fe81796885beed9ec7fbaf60`.

## Complete entry-point exposure

`public_entrypoint_exposure_all.csv` supersedes
`public_entrypoint_exposure.csv`. It has 479 entry modules times three
declaration universes, or 1,437 rows. For 439 entry modules it uses compiled
transitive project-module import closure plus the entry module. For 40
declaration-free entries not observed in the root-loaded compiled module graph,
it uses validated static source-import closure and joins reached modules to
compiled declaration ownership. Static and compiled closures agree for all
439 observed entries, and every declaration-bearing fallback-closure module
has compiled ownership data.

The prior table's 117 unobserved zero rows are superseded and must not be
interpreted as zero declaration exposure. Entry-point reachability remains a
module-ownership exposure measure, not proof of practical usability; the
independent compiled client probes answer the latter question for their
predeclared sample.
