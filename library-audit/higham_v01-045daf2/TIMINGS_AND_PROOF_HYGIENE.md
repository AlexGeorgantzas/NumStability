# Fresh-output module timings and proof-hygiene audit

Audited commit: `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.

This report covers two bounded parts of the larger read-only audit: a
predeclared fresh-target-output compilation sample, and source plus
compiled-environment proof-hygiene checks. It does not replace the full-build
result or the declaration-graph analysis.

## Fresh-output module compilation

All 30 modules in the predeclared stratified sample compiled successfully; no
module failed or timed out. Each invocation wrote a unique, initially absent
`.olean` and `.ilean` pair beneath the ignored audit directory. Imports used
the exact-commit cached artifacts in the isolated worktree. The output sizes
and hashes were recorded and the temporary target outputs were then removed.
Thus these are **fresh target-output timings with cached imports**, not clean
whole-library compilation times.

The sample deliberately covers public roots, each architectural layer,
important numerical domains, chapter entry points, and known large source
files. It is not random and includes only 30 of 2,839 modules. Every percentile
below therefore describes this sample only.

| Measure | Numerator / denominator | Result |
|---|---:|---:|
| Successful fresh-target compilations | 30 / 30 sampled modules | 100% |
| Failed | 0 / 30 | 0% |
| Timed out (900 s bound) | 0 / 30 | 0% |
| Above the skill's review threshold | 6 / 30 | >20 s |
| Above the skill's priority threshold | 4 / 30 | >40 s |
| Sample median | 30 successful observations | 9.265 s |
| Sample p90 | 30 successful observations | 46.484 s |
| Sample p95 | 30 successful observations | 54.218 s |
| Sample maximum | 30 successful observations | 56.840 s |

Percentiles use R-7 linear interpolation, `h = (n - 1)p`, over successful
effective observations and the `/usr/bin/time -p` `real` column.

### Sampled timing review candidates

| Module | Layer | Code-bearing lines | Fresh-target real time | Threshold |
|---|---|---:|---:|---|
| `NumStability.Source.Higham.Chapter09.Section11` | Source | 37,178 | 56.84 s | priority |
| `NumStability.Source.Higham.Chapter11.Section01.Tridiagonal` | Source | 51,482 | 55.95 s | priority |
| `NumStability.Source.Higham.Chapter20.Theorem03.QRSolve` | Source | 22,416 | 52.10 s | priority |
| `NumStability.Source.Higham.Chapter19.Core` | Source | 36,307 | 45.86 s | priority |
| `NumStability` | Root | 1 | 28.24 s | review |
| `NumStability.Analysis.Perturbation.LeastSquares.Basic` | Analysis | 21,598 | 27.23 s | review |

The four slow source modules are concrete compilation-hotspot candidates under
the skill contract. A threshold crossing is a review signal, not evidence that
a file must be split or that its mathematics is poorly organized. The root
module's time is dominated by loading its broad imported environment, not its
single source line. It was also the first timed module, so cold operating-system
page caches may inflate it relative to later aggregate modules.

The largest sampled emitted `.olean` was the Chapter 20 QR source module
(14,617,712 bytes); the Chapter 11 tridiagonal source module emitted a
9,645,184-byte `.olean` and a 10,557,350-byte `.ilean`. These sizes are evidence
of large target artifacts in this build, but do not alone diagnose the cause or
authorize a module split.

An unrelated Python scan overlapped two first attempts. Rows 25 and 26 were
rerun after a quiet period with identical commands. The first attempts remain
in the raw CSV and are excluded; `fresh_module_timings_effective.csv` is the
only timing input used above. See `timings/INTERFERENCE_NOTE.md` for the exact
window and one diagnostic-log retention limitation.

## Source-level proof hygiene

The lexical pass covered all 2,839 NumStability Lean source files. It maintains
nested block-comment and string state, and records code, comment, and string
matches separately.

| Source check | Numerator / denominator | Finding |
|---|---:|---|
| `sorry` in code | 0 / 2,839 files | none found |
| `admit` in code | 0 / 2,839 files | none found |
| `sorryAx` in code | 0 / 2,839 files | none found |
| `axiom`/`axioms` declaration commands | 0 / 2,839 files | none found |
| `unsafe` in code | 0 / 2,839 files | none found |
| `native_decide` in code | 6 occurrences / 2,839 files | two Chapter 2 modules |
| `#print axioms` diagnostics | 5 occurrences / 2,839 files | diagnostics, not declarations |

There are 40 comment occurrences each of the words `sorry` and `admit`, 94
comment occurrences of `axiom`/`axioms`, and other comment-only warnings. They
are not proof commands. The raw table retains them so the zero code result is
auditable rather than based on an undifferentiated text search.

Four public structures in
`NumStability.Algorithms.FastMatMul.Internal.LegacyBounds` are explicitly
described by their own documentation as legacy placeholders:
`StrassenErrorBound`, `WinogradInnerProductError`,
`BilinearAlgorithmError`, and `ThreeMMethodError`. They are well-formed Prop
interfaces with fields, not missing Lean proofs, `sorry`, or axioms. The module
itself says it is an unsupported compatibility surface. This is a public-API
and content-maturity concern, and the four are conservatively reported in
`placeholder_like_source_declarations.csv`. The historical abbreviation
`WinogradStrassenErrorBound` is related compatibility surface but is not added
to the four-declaration numerator because its individual documentation does not
call it a placeholder.

No source `opaque` command was found by this pass. More importantly, opacity is
not treated as evidence of a placeholder; compiled reducibility metadata and
proof completeness are distinct properties.

## Compiled-environment hygiene

The compiled universe contains 77,246 environment declarations attributed to
NumStability modules. The elaborated graph contains 3,963,823 direct edges from
those declarations to project or external declarations.

| Compiled check | Numerator / denominator | Finding |
|---|---:|---|
| Direct elaborated edges to `sorryAx` | 0 / 3,963,823 edges | none found |
| `DeclarationInfo.isUnsafe = true` | 0 / 77,246 declarations | none found |
| Unrecognized project-owned axiom declarations | 0 / 77,246 | none found |
| Lean-generated `native_decide` axiom helpers | 6 / 77,246 | present and isolated below |
| Unexpected declarations without bodies | 0 / 77,246 | none after kind classification |
| Generated internal partial-recursion helpers | 126 / 77,246 | all named `._unsafe_rec` |
| Other partial declarations requiring review | 0 / 77,246 | none found |

Exactly 1,689 compiled declarations have no value/proof body: 711 constructors,
486 recursors, 486 inductive declarations, and six internal
`native_decide`-generated axiom helpers. The first 1,683 are expected
environment kinds. Each generated axiom helper has one direct incoming
proof-body edge, from the source theorem whose `native_decide` invocation
generated it. No other project-owned `axiom`-kind declaration was found.

All 126 declarations carrying the compiled `is_partial` flag are internal
definitions with generated names ending in `._unsafe_rec`; they span 60
modules, have bodies, and `is_unsafe` is false in the recorded declaration
metadata. Three are additionally private. They are classified as generated
recursion implementation helpers, not source-written public partial APIs and
not proof placeholders. The apparently alarming suffix is reported exactly,
but not conflated with the `isUnsafe` field.

## Representative theorem assumption sets

A temporary, external `#print axioms` probe compiled successfully for twelve
predeclared declarations. Six high-level endpoints—LU solve, QR solve, Chapter
12 iterative refinement, matrix multiplication, dot product, and least-squares
analysis—each reported exactly the ordinary trio `propext`,
`Classical.choice`, and `Quot.sound`. None of those six reported a
project-specific axiom, a `native_decide` helper, or a placeholder assumption.

The six theorems proved with `native_decide` each reported the same ordinary
trio plus its own generated internal helper. The helper names and direct proof
edges are preserved in `compiled_project_axioms.csv`,
`compiled_project_axiom_dependency_edges.csv`, and
`representative_endpoint_axioms.csv`. These helpers are trusted-code evidence
introduced by Lean's native decision procedure; they are not explicit
source-level mathematical assumptions and not incomplete proofs. They should
nevertheless be disclosed when describing the trusted base.

## What these results establish—and do not establish

The successful sampled compiles establish that those exact modules elaborate
and emit fresh target artifacts against the recorded cached imports. They do
not establish a clean-library build time or the timing distribution of all
modules. The absence of source proof holes, compiled `sorryAx` dependencies,
unsafe declarations, and unrecognized project axioms is strong proof-hygiene
evidence for this compiled snapshot. It does not establish fidelity to Higham,
the mathematical truth of specifications relative to their intended source,
or universal axiom cleanliness for every theorem's transitive external
dependencies.

The six endpoint `#print axioms` probes are stronger than lexical inspection
for those particular proof terms, but they are a stratified sample, not all
62,152 compiled theorems. Direct graph edges suffice to inventory every
project-owned axiom consumer, while transitive external foundational-assumption
sets would require a library-wide `#print axioms`-equivalent traversal to make
an exhaustive claim.

Sequential timings retain exact cached Lean artifacts but do not control the
operating-system page cache, thermal state, or unrelated machine activity. The
two known interference overlaps were rerun; no universal performance claim is
made from a single host run.

## Primary artifacts

- `timings/timing_sample_predeclared.csv`: frozen sample and strata.
- `timings/fresh_module_timings.csv`: all original attempts.
- `timings/fresh_module_timing_reruns.csv`: two quiet reruns.
- `timings/fresh_module_timings_effective.csv`: authoritative 30 rows.
- `timings/fresh_module_timing_percentiles.csv`: formula-labelled percentiles.
- `timings/fresh_module_timing_hotspots.csv`: skill-threshold review rows.
- `hygiene/source_proof_hygiene_occurrences.csv`: code/comment/string lexical rows.
- `hygiene/proof_hygiene_results.csv`: formula and universe table.
- `hygiene/compiled_bodyless_declarations.csv`: all bodyless declarations with classifications.
- `hygiene/compiled_project_axioms.csv`: generated axiom inventory.
- `hygiene/compiled_project_axiom_dependency_edges.csv`: six exact body edges.
- `hygiene/compiled_sorryAx_dependency_edges.csv`: header-only zero-result artifact.
- `hygiene/compiled_unsafe_declarations.csv`: header-only zero-result artifact.
- `hygiene/compiled_partial_declarations.csv`: generated partial-helper inventory.
- `hygiene/placeholder_like_source_declarations.csv`: four documented legacy interfaces.
- `hygiene/representative_endpoint_axioms.csv`: parsed `#print axioms` results.
- `hygiene/representative_axioms.log`: unmodified Lean diagnostic output.
