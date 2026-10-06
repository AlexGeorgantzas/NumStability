# Phase 10A tooling and metric recovery

Recovery timestamp: `2026-09-03T11:16:50+03:00` (`Europe/Athens`; UTC
`2026-09-03T08:16:50+00:00`)

Target of the new audit: `origin/higham_v01` at
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.

## Outcome

The exact tooling that produced the four cited Phase 10A headline figures was
recovered from Git history. It is **not** the later, untracked
`tools/library_audit/` suite. Phase 10A used:

- `tools/architecture/declaration_dependencies.lean`, SHA-256
  `30186d3470320983e2ada2e61fce7efaa7e6230c71348c5d37a9801526be2acd`;
- `tools/architecture/generate_baseline.py`, SHA-256
  `fc5863b2ca4e8f2dd03d2f012c40df9f26666849073a4e5b1babc65a671d6a94`.

Those blobs are identical at the Phase 10A pre-edit ownership commit
`899003baca0fdca2714344a69c10eef4b2d3c306` and implementation commit
`d21a4ed5b91008a8a5bc60741765f27fcdf86edf`.

The committed JSON says it was captured from a dirty candidate worktree whose
`HEAD` was `899003b...`. The nine listed dirty NumStability paths are the Phase
10A implementation. Two independent facts bind the measurements to the clean
implementation commit `d21a4ed...`:

1. Re-running the exact source scanner over a `git archive` of `d21a4ed...`
   reproduced its source-tree SHA-256
   `cd5be41c56cf8f6dec940b89324298aa3bd5e3dd14853afecdd2017b08fb0cb1`
   and every recorded source/import total exactly.
2. The evidence-only commit
   `21e130ac8355de8ec1a74f22a73bf103e00bc48f` records a clean
   `d21a4ed...` worktree and a passing
   `generate_baseline.py --no-build --check`, including exact source, import,
   declaration, toolchain, and Mathlib reproduction.

Accordingly, `d21a4ed...` is the defensible effective Phase 10A source commit;
`899003b...` remains the literal `HEAD` stored in the first candidate capture.

The Phase 10A raw format-2 dependency TSV was **not recovered**. The generator
used a temporary file and deleted it by default unless
`--keep-dependency-tsv` was supplied. Searches of tracked and ignored files,
local worktrees, all refs/stashes, `/tmp`, and macOS temporary directories found
no retained Phase 10A TSV. The aggregate JSON, generated Markdown, exact tools,
source commit, and clean reproduction record were recovered.

The exact recovered extractor and the exact, unchanged
`summarize_declaration_tsv` function were subsequently replayed against the
presentation commit. This makes the aggregate fields emitted by that function
schema-compatible across the two commits. It does **not** recover the missing
historical declaration names or edge rows, and it does not make a
source-written-public comparison possible.

## Provenance chain

| Role | Commit/object | Evidence |
| --- | --- | --- |
| Immutable pre-edit ownership map and candidate `HEAD` | `899003baca0fdca2714344a69c10eef4b2d3c306` | Parent is execution base `227f41ce...`; exact Phase 10A tool blobs already present. |
| Effective Phase 10A implementation and committed snapshot | `d21a4ed5b91008a8a5bc60741765f27fcdf86edf` | Adds the Phase 10A JSON/Markdown/build record and contains the source tree whose normalized digest matches the snapshot. |
| Clean reproduction evidence | `21e130ac8355de8ec1a74f22a73bf103e00bc48f` | Changes only the build note; records clean `d21a4ed...` validation and exact `--check` reproduction. |
| New audit target | `045daf28056a6e4358d5de7c22c7a9d7acc2e80e` | Descends from `d21a4ed...`; same Lean and Mathlib revisions. |

The historical capture used Lean `v4.29.0-rc3`, Lean revision
`5d86aa4032284a5242470e95fbe25f1ff506763d`, and Mathlib revision
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`. These match the presentation
commit. The first capture reports `x86_64-w64-windows-gnu`; the recovery host is
macOS `26.5.2` on `arm64`.

Historical builds passed (`lake test`, 5,169 jobs; `lake build NumStability
NumStabilityTest`, 5,171 jobs), but the build note explicitly classifies these
as cache-preserving validation builds. They are not fresh-output timing
evidence.

## Recovered files

Exact Phase 10A files are under [`phase10a_exact/`](phase10a_exact/). The final
clean validation note is separately preserved under
[`phase10a_validation_21e/`](phase10a_validation_21e/), so the d21 archive is
not silently mixed with a later evidence-only commit.

The complete Git-blob/SHA-256 inventory is
[`PHASE10A_RECOVERY_CHECKSUMS.csv`](PHASE10A_RECOVERY_CHECKSUMS.csv). The
machine-readable conclusions and formulas are in
[`PHASE10A_RECOVERY.json`](PHASE10A_RECOVERY.json). The independent replay of
the exact Phase 10A source scanner is recorded in
[`PHASE10A_SOURCE_REPLAY.json`](PHASE10A_SOURCE_REPLAY.json).

## Exact declaration universe

The Phase 10A extractor imports the single root module `NumStability`, then
iterates compiled module metadata. Its node universe is:

> Every uniquely owned environment declaration whose owning module name is
> exactly `NumStability` or begins with `NumStability.` and is reachable in the
> environment formed by importing `NumStability`.

Ownership is assigned by `Environment.getModuleIdxFor?`; repeated declarations
in re-exporting module data are discarded. At Phase 10A the root re-exported
the complete tree. The source scanner separately counted `NumStability.lean`
and every `NumStability/**/*.lean` file, whether declaration-bearing or not.

Consequences:

- `NumStabilityTest` and external `examples/` files were excluded.
- `Source/Higham` modules reachable from the root were included.
- compatibility and aggregate modules were included in the source/module
  inventory, but declaration-free shims contributed no declaration nodes.
- there was no source-authorship filter.
- there was no `isReservedName` filter.
- generated constructors, recursors, equation lemmas, match/proof auxiliaries,
  and other generated names could be present.

The snapshot contains 81,950 nodes owned by 803 declaration-bearing modules,
while the source universe contains 957 Lean modules. The 154-module difference
must not be read as missing source: many aggregates and compatibility shims are
deliberately declaration-free.

## Exact edge semantics

`A -> B` means the elaborated type or body/proof of declaration `A` directly
contains project declaration constant `B`.

- Type references are `info.type.getUsedConstantsAsSet`.
- Definition, theorem, and opaque bodies use their stored values.
- Recursor bodies use the union of constants in recursor-rule right-hand sides.
- Other declaration kinds contribute no body set.
- Targets outside the project declaration universe are discarded.
- The extractor uses sets, and the Python summarizer stores sets of
  `(source,target)` pairs. Repeated textual occurrences do not create repeated
  edges.
- Type and body/proof sets are retained separately. Their union counts a pair
  once even when it occurs in both.
- All cited reuse and cross-module metrics are direct, not transitive.
- The Phase 10A code does not explicitly remove `A -> A`; therefore any
  elaborated self-reference, if present, is part of its exact schema.

The recorded edge accounting is internally consistent:

| Edge set | All | Cross-module |
| --- | ---: | ---: |
| Signature | 305,425 | 150,870 |
| Body/proof | 439,195 | 197,823 |
| Signature/body overlap | 253,063 | 126,374 (derived) |
| Body/proof only | 186,132 | 71,449 |
| Union | 491,557 | 222,319 |

Thus `222,319` is a count of unique cross-module declaration pairs in the
type/body union. It is not a raw constant-occurrence count, import count, or
transitive-edge count.

## Reconstruction of the four cited figures

All percentages use the JSON fields named below; no denominator is inferred
from source blocks.

| Claim | Numerator / denominator | Exact formula and filters | Raw/summary provenance |
| --- | ---: | --- | --- |
| Public declarations | 56,187 / 81,950 | Declaration name is neither `isPrivateName` nor `Name.isInternalDetail`. | Raw format-2 declaration row field 4 (`visibility`); JSON `declarations.visibility_counts.public`. |
| Public declarations with an incoming reference | 40,963 / 56,187 = 72.905% | Public target `B` has at least one incoming pair in `signature_edges union body_edges`; source visibility is unrestricted. | Raw declaration and edge rows; JSON `declarations.graph_metrics.public_referenced_somewhere`. |
| Public declarations used from another module | 8,371 / 56,187 = 14.898% | Public target `B` has at least one incoming union edge from `A` with `owner(A) != owner(B)`; source visibility is unrestricted. | Raw declaration and edge rows; JSON `declarations.graph_metrics.public_referenced_from_another_module`. |
| Cross-module declaration edges | 222,319 / 491,557 union edges = 45.228% | Cardinality of unique union pairs `(A,B)` whose unique owner modules differ. | Raw declaration and edge rows; JSON `declarations.edge_counts.cross_module_union`. |

The old reports did not state the 45.228% edge fraction as a headline; it is
shown only to make the denominator explicit for this audit.

## Exact-schema replay at `045daf2...`

The retained current raw extraction is
`../raw/phase10a_exact_current.tsv.gz`. Its compressed SHA-256 is
`bca79605b72534a4784a4a458008b6b283fb5a05e8336370abde6163cc3e5e84`;
the 124,996,640-byte decompressed TSV has SHA-256
`3d3d5dc5b329b4b48ea76d95b615967ee1c9f624cae0f508f99c4f95cd36eaa9`
and 770,151 rows. Those rows consist of one format marker, 77,246 declaration
rows, 283,049 signature-edge rows, and 409,855 body/proof-edge rows.

[`phase10a_exact_current_summary.json`](phase10a_exact_current_summary.json)
is the literal JSON result of passing that TSV through the recovered
`summarize_declaration_tsv` implementation without modifying the function. It
has SHA-256
`264b53838599b48f071f8122a5efb61bc38f23bde2a9f7c6aff2362cf401d701`.
The raw, decompressed-stream, summary, log, and timing hashes are collected in
[`PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv`](PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv).
The TSV was streamed from gzip through a FIFO, so no second uncompressed copy
was retained. The summarizer took 2.23 seconds wall time on this host. The
extractor timing record reports 95.11 seconds, but that is compiled-environment
extraction over already available outputs, **not** a fresh-output library build
or clean compilation timing.

The following aggregate comparison is apples-to-apples at the recovered Phase
10A schema. “Public” still means environment-public under
`not isPrivateName` and `not Name.isInternalDetail`, generated declarations are
still included, and every dependency count remains a unique direct declaration
pair.

| Exact Phase 10A field | `d21a4ed...` | `045daf2...` | Absolute delta | Relative delta |
| --- | ---: | ---: | ---: | ---: |
| Declaration nodes | 81,950 | 77,246 | -4,704 | -5.740% |
| Declaration-bearing modules | 803 | 1,649 | +846 | +105.355% |
| Environment-public nodes | 56,187 | 52,332 | -3,855 | -6.861% |
| Private nodes | 4,341 | 4,516 | +175 | +4.031% |
| Internal-detail nodes | 21,422 | 20,398 | -1,024 | -4.780% |
| Signature edges | 305,425 | 283,049 | -22,376 | -7.326% |
| Body/proof edges | 439,195 | 409,855 | -29,340 | -6.680% |
| Type/body union edges | 491,557 | 458,631 | -32,926 | -6.698% |
| Cross-module union edges | 222,319 | 268,228 | +45,909 | +20.650% |
| Public nodes with an incoming edge | 40,963 | 37,997 | -2,966 | -7.241% |
| Public nodes used from another module | 8,371 | 12,795 | +4,424 | +52.849% |
| Largest all-node weak component | 73,995 | 69,427 | -4,568 | -6.173% |
| Largest public-induced weak component | 54,301 | 50,410 | -3,891 | -7.166% |
| All-node isolates | 5,881 | 5,450 | -431 | -7.329% |
| Public-node isolates | 159 | 148 | -11 | -6.918% |

Several denominator-aware comparisons are more informative than the raw
counts:

- incoming-reference coverage of environment-public nodes is almost unchanged:
  40,963/56,187 = 72.905% historically and 37,997/52,332 = 72.608% now, a
  decrease of 0.297 percentage points;
- public cross-module utilization is 8,371/56,187 = 14.898% historically and
  12,795/52,332 = 24.450% now, an increase of 9.551 percentage points;
- the largest weak component covers 90.293% of all nodes historically and
  89.878% now, a decrease of 0.415 percentage points; the public-induced
  coverage changes from 96.643% to 96.327%, a decrease of 0.316 percentage
  points;
- cross-module pairs form 222,319/491,557 = 45.228% of union edges
  historically and 268,228/458,631 = 58.484% now, an increase of 13.257
  percentage points; and
- mean declarations per declaration-bearing module fall from 102.055 to
  46.844 while the module count more than doubles.

Percentage-point changes above are calculated from the unrounded ratios and
then rounded to three decimal places, not by subtracting displayed rounded
percentages.

The first, third, and isolate proportions show broadly stable graph-coverage
shape under this historical schema. The rise in cross-module counts is real as
a measurement of current ownership boundaries, but it is not evidence by
itself of more mathematical reuse: splitting and moving modules converts an
unchanged declaration edge from intra-module to cross-module. Indeed, total
union edges decrease by 6.698% while declaration-bearing modules increase by
105.355%. A defensible thesis formulation is therefore that the reorganized
presentation tree exposes substantially more dependencies across finer module
boundaries while retaining nearly the same incoming-reference and weak-component
coverage under the old environment-wide metric. Whether the stable logical
declaration graph gained or lost particular edges cannot be determined from
the missing historical raw TSV.

## What “public” did and did not mean

Phase 10A “public” meant environment-visible under a name heuristic. It did
**not** mean explicitly source-written. The extractor did not consult syntax,
source locations, declaration origins, or `isReservedName`.

The generated-name inclusion is not merely hypothetical:

- the JSON reports 734 constructors and 509 recursors in the total universe;
- the Phase 10A ownership record explicitly names the generated
  `RectRankFactorization.mk.congr_simp` theorem as a public owned constant;
- later July 27 changes to the architecture extractor were specifically titled
  “Stabilize declaration dependency ownership,” “Cover shifted simp auxiliary
  normalization,” and “Contract generated declaration auxiliaries.” Those
  later changes filtered/contracted reserved and compiler-generated details;
  they are not part of the Phase 10A schema.

`Name.isInternalDetail` removes many generated `eq_*`, `match_*`, `proof_*`,
numeric, and underscore-bearing names from the public category, but it does not
prove the remaining public names were handwritten. Constructors, recursors,
and generated names such as `congr_simp` may remain public. Phase 10A therefore
has no defensible source-written-public numerator or denominator.

## Relationship to the recovered `tools/library_audit/` suite

The requested later infrastructure was also recovered, byte-for-byte, under
[`recovered_library_audit/`](recovered_library_audit/). Its source is the
untracked-files commit
`8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d`, third parent of stash commit
`698c08e9897941ee4d5b19e944a7ad49836d2b67` (“preserve
codex/numstability-rename work before deletion,” 2026-07-24). The stash base is
release commit `2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`.

The same source bytes were later preserved again in untracked-files commit
`163a1134a6cadae7538fdb27859bfc25d9f00005` (2026-08-14). The only difference
between the two recovered directory trees is the incidental `.pyc` file present
in the July stash.

The ignored `tmp/library_audit/2bb76d0/` artifacts report commit `2bb76d0`, a
July 21 capture timestamp, clean NumStability sources, and `?? tools/`. Their
CSV schemas and metrics exactly match this recovered suite. This is strong
provenance evidence. It is not a cryptographic proof that the files had these
same hashes three days before they were stashed, because that older capture did
not record tool hashes.

The recovered known-example test passed on this host:

```text
Ran 1 test in 0.047s
OK
```

This suite did not generate the Phase 10A values. In particular, its metric
schema differs from Phase 10A:

| Topic | Phase 10A architecture tool | Recovered library-audit tool |
| --- | --- | --- |
| Internal-name predicate | `Name.isInternalDetail` | `Name.isInternal` |
| Generated/reserved declarations | included; visibility-labelled heuristically | included; `is_internal` uses the narrower predicate |
| Self edges | not explicitly erased | explicitly erased |
| Recursor body references | recursor-rule RHS included | omitted because `ConstantInfo.value? true` returns no recursor value |
| External edges | discarded by extractor | retained in raw CSV with scope, then filtered for project graph |
| Public weak-component figure | largest component in the public-induced graph | public nodes lying in the largest all-declaration component |

The first difference alone invalidates a direct comparison of their public
counts: Lean 4.29's `isInternalDetail` additionally recognizes numeric
components and generated `eq_*`, `match_*`, `proof_*`, and `omega_*` forms.

The recovered Lean extractor and graph analyzer can be invoked from the
external ignored recovery directory without changing their source. The
`capture_baseline.py` script derives the repository root as two parents above
its own path; to run that script unchanged, copy the exact recovered
`tools/library_audit` tree into `tools/library_audit` inside a disposable
worktree. A path-only wrapper/adaptation is otherwise required and must be
recorded.

## Historical comparison decision

The exact current replay has now satisfied the requirements for an
apples-to-apples **aggregate** comparison:

- it used the exact Phase 10A extractor and exact summarizer;
- `d21a4ed...` is an ancestor of `045daf2...`;
- both revisions use the same Lean and exact Mathlib commits;
- both root modules are `import NumStability` compatibility entry points that
  re-export `NumStability.All`; and
- the current raw TSV and summary have been retained and hashed.

Accordingly, fields common to the old aggregate JSON and the new exact summary
are numerically comparable under the Phase 10A declaration universe and
filters. This conclusion does not extend to a current result produced only by
the recovered `tools/library_audit` suite or a new enriched schema. It also does
not turn Phase 10A “public” into source-written public.

Detailed comparisons remain unavailable. The aggregate Phase 10A JSON does not
contain historical declaration names or edge rows, so it cannot support public
name additions/removals, statement-fingerprint moves/renames, stable logical
edge additions/removals, or preservation of named dependency chains. Those
require regenerating the raw Phase 10A format-2 TSV from clean commit
`d21a4ed...` with the exact extractor, then comparing both raw files under a
declared name/fingerprint reconciliation procedure. Cross-module utilization
and edge counts also remain mechanically sensitive to file moves and splits.

## Reproduction commands

To reproduce the old snapshot faithfully in a disposable worktree at
`d21a4ed...`, place the recovered exact architecture files at their historical
paths and run:

```bash
python3 tools/architecture/generate_baseline.py \
  --keep-dependency-tsv /absolute/ignored/path/phase10a-dependencies.tsv \
  --output-dir /absolute/ignored/path/reproduced \
  --name phase10a-reproduced
```

To preserve a clean-output distinction, delete or relocate only the disposable
worktree's NumStability build outputs before this invocation and record that
action. The historical command itself ran `lake build NumStability` without
guaranteeing fresh outputs.

For a current apples-to-apples extraction without modifying the presentation
worktree, the exact Lean extractor can be invoked from this recovery directory:

```bash
cd /absolute/path/to/clean-higham-v01-worktree
lake env lean --run \
  /absolute/path/to/historical/phase10a_exact/tools/architecture/declaration_dependencies.lean \
  /absolute/ignored/path/higham-v01-phase10-schema.tsv
```

Then call `summarize_declaration_tsv` from the exact recovered
`generate_baseline.py` (or place both exact tools at their historical paths and
use `--dependency-tsv`). Do not substitute the later library-audit summary and
retain the Phase 10A label.

All recovery/search commands actually executed are recorded in
[`PHASE10A_COMMANDS.md`](PHASE10A_COMMANDS.md), including two harmless failed
diagnostic/cleanup attempts.

## Publication-safe conclusion

It is safe to say that the Phase 10A snapshot measured 56,187
environment-public declarations, of which 40,963 had at least one incoming
direct project edge and 8,371 had an incoming direct edge from a different
owner module, under the exact recovered visibility and graph filters. It is
also safe to say that the graph contained 222,319 unique cross-module pairs in
the union of elaborated type and body/proof dependencies.

It is additionally safe to compare those aggregate fields with the exact-schema
replay at `045daf2...`: incoming-reference coverage remained close (72.905% to
72.608%), while the fraction of environment-public declarations consumed from
another module rose from 14.898% to 24.450%. The latter must be presented
together with the doubling of declaration-bearing modules (803 to 1,649),
because module splitting alone can reclassify stable edges as cross-module.

It is not safe to call the 56,187 declarations handwritten public API, to call
the 40,963 declarations source-faithful or externally consumable, to interpret
222,319 as independent mathematical reuse events, or to compare any of these
numbers directly with a differently filtered current snapshot. It is also not
safe, without regenerating the historical raw TSV, to attribute aggregate edge
changes to particular declarations, renames, moves, or new proof reuse.
