# Historical comparison with Phase 10A

## Decision

The exact Phase 10A architecture tooling was recovered. A numerical comparison
with `higham_v01` is valid **only for the aggregate source and declaration
fields replayed with that byte-identical tooling and its original filters**.
The missing historical raw declaration TSV prevents declaration-name, stable
edge, move/rename, statement-fingerprint, and named-chain comparisons. Results
from the later `tools/library_audit/` suite and from the enriched current audit
are separate snapshots and are not substituted into the Phase 10A series.

The compared revisions are:

- effective Phase 10A source commit:
  `d21a4ed5b91008a8a5bc60741765f27fcdf86edf`;
- literal pre-edit/candidate `HEAD` recorded in the original snapshot:
  `899003baca0fdca2714344a69c10eef4b2d3c306`;
- clean Phase 10A reproduction-evidence commit:
  `21e130ac8355de8ec1a74f22a73bf103e00bc48f`;
- presentation-branch audit commit:
  `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.

The first captured JSON records a dirty candidate worktree at `899003b...`.
Its nine dirty NumStability paths are the Phase 10A implementation later
committed by `d21a4ed...`. Replaying the exact source scanner on an archive of
`d21a4ed...` reproduced every recorded source/import total and the normalized
tree hash
`cd5be41c56cf8f6dec940b89324298aa3bd5e3dd14853afecdd2017b08fb0cb1`.
Commit `21e130a...` independently records a clean `d21a4ed...` worktree and a
passing exact `--check`. These facts make `d21a4ed...` the defensible effective
historical source commit while preserving `899003b...` as the literal stored
candidate `HEAD`.

## Tool provenance

The four previously quoted Phase 10A figures came from these files, not from
the later library-audit suite:

| Historical path | SHA-256 | Role |
| --- | --- | --- |
| `tools/architecture/declaration_dependencies.lean` | `30186d3470320983e2ada2e61fce7efaa7e6230c71348c5d37a9801526be2acd` | Extract compiled declaration ownership plus direct type and body/proof constants. |
| `tools/architecture/generate_baseline.py` | `fc5863b2ca4e8f2dd03d2f012c40df9f26666849073a4e5b1babc65a671d6a94` | Scan source/import structure and summarize the declaration TSV. |

The blobs are identical at `899003b...` and `d21a4ed...`. They are preserved
under [`historical/phase10a_exact/`](historical/phase10a_exact/); the Git-blob
inventory is [`historical/PHASE10A_RECOVERY_CHECKSUMS.csv`](historical/PHASE10A_RECOVERY_CHECKSUMS.csv).
The complete recovery argument is
[`historical/PHASE10A_RECOVERY.md`](historical/PHASE10A_RECOVERY.md), with a
machine-readable version in
[`historical/PHASE10A_RECOVERY.json`](historical/PHASE10A_RECOVERY.json).

The current source replay uses the recovered generator's `scan_sources`
function without changing that file. The external serialization wrapper is
[`tooling/phase10a_source_scan_replay.py`](tooling/phase10a_source_scan_replay.py),
schema `numstability-phase10a-source-scan-replay/v1`, SHA-256
`ffefca5ec3163c6ec5c2f4cb896e7534ade0d4c68156e37c9927db4a8bbf5eeb`.
The wrapper's only compatibility adjustment is registering the dynamically
loaded module in `sys.modules`, which Python 3.14 requires while processing the
historical script's dataclasses. It does not alter or reimplement
`scan_sources`. The command, output, and hashes are retained in:

- [`historical/PHASE10A_SOURCE_SCAN_CURRENT_COMMAND.log`](historical/PHASE10A_SOURCE_SCAN_CURRENT_COMMAND.log);
- [`historical/PHASE10A_SOURCE_SCAN_CURRENT_STDOUT.log`](historical/PHASE10A_SOURCE_SCAN_CURRENT_STDOUT.log);
- [`historical/PHASE10A_SOURCE_SCAN_CURRENT_SHA256SUMS`](historical/PHASE10A_SOURCE_SCAN_CURRENT_SHA256SUMS);
- [`historical/phase10a_exact_current_source_scan.json`](historical/phase10a_exact_current_source_scan.json);
- [`historical/phase10a_exact_current_source_modules.csv`](historical/phase10a_exact_current_source_modules.csv).

The first wrapper invocation failed before scanning because the dynamically
loaded module was not yet registered for Python 3.14 dataclass annotation
resolution. The recorded retry contains the compatibility fix above. No Lean
source changed, and the isolated worktree remained clean.

## Exact Phase 10A metric contract

The committed aggregate baseline declares `schema_version: 1`; the extractor's
tabular stream begins with `FORMAT\t2`. The source-only current replay envelope
uses `numstability-phase10a-source-scan-replay/v1` solely to record invocation,
hash, and serialization metadata around the unmodified historical
`scan_sources` function. The later enriched graph schema
`numstability-elaborated-architecture/2.1.0` is not part of the historical
series.

### Source universe

The source scanner includes `NumStability.lean` and every `*.lean` file below
`NumStability/`. It normalizes UTF-8 BOMs and CRLF/CR line endings to LF for
hashing. `line_count` is Python `splitlines()` count; `nonblank_line_count`
counts lines for which `line.strip()` is nonempty, including comment lines.
`byte_count` is the size of normalized UTF-8 text. These are not code-only LOC
metrics.

`direct_import_count` counts parsed import occurrences. An internal import is
deduplicated as an `(importer module, imported project module)` pair;
`external_direct_import_count` counts external import occurrences. The edge
orientation is importer/consumer to imported dependency. An import edge is not
an elaborated theorem dependency.

### Declaration universe

The extractor imports `NumStability`, iterates the resulting compiled module
metadata, and keeps every uniquely owned environment declaration whose owner
module is `NumStability` or starts with `NumStability.`. Ownership uses
`Environment.getModuleIdxFor?`; duplicate observations through re-exports are
discarded. Tests and external examples are outside this universe. Source,
aggregate, and compatibility modules are included when reachable, although
declaration-free modules add no nodes.

“Public” means neither `isPrivateName(name)` nor
`Name.isInternalDetail(name)`. It does **not** mean explicitly source-written.
There is no source-range or `isReservedName` filter. Constructors, recursors,
equation lemmas, congruence helpers, and other generated declarations can be
included. The historical snapshot itself contains 734 constructors and 509
recursors, and its migration record identifies a generated public-looking
`congr_simp` theorem.

### Declaration edges

For every declaration pair, `A -> B` means the elaborated type or body/proof
of consumer `A` directly contains the project constant `B`.

- Signature dependencies are `info.type.getUsedConstantsAsSet`.
- Definitions, theorems, and opaque declarations contribute stored body
  constants.
- Recursors contribute constants found in rule right-hand sides.
- External targets are removed.
- Repeated occurrences are deduplicated as declaration-name pairs.
- Type and body/proof sets are retained separately; their union counts a pair
  once even if it appears in both.
- All quoted reuse fields are direct, never transitive.
- Self edges are not explicitly removed in this historical schema.

The raw format is version 2. The old raw TSV was temporary by default and was
not recovered despite searches of tracked and ignored files, local worktrees,
refs, stashes, `/tmp`, and macOS temporary directories. The committed
aggregate JSON is therefore the only historical declaration-level result
available without rebuilding the historical commit.

## Exact source and import comparison

The current figures below are from the exact historical `scan_sources`
function, not the newer static analyzer. The numerator for each absolute delta
is `current - Phase 10A`; relative delta is `(current - historical) /
historical`. Raw current columns are under `source.<field>` in
[`historical/phase10a_exact_current_source_scan.json`](historical/phase10a_exact_current_source_scan.json);
historical columns are under `source.<field>` in
[`historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json`](historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json).

| Exact source field | Phase 10A | `045daf2...` | Absolute delta | Relative delta |
| --- | ---: | ---: | ---: | ---: |
| Lean source modules | 957 | 2,839 | +1,882 | +196.656% |
| Physical source lines | 1,467,997 | 3,660,946 | +2,192,949 | +149.384% |
| Nonblank source lines | 1,401,875 | 1,345,766 | -56,109 | -4.002% |
| Normalized source bytes | 69,590,164 | 69,455,337 | -134,827 | -0.194% |
| Direct import occurrences | 4,009 | 30,334 | +26,325 | +656.648% |
| Unique internal direct-import pairs | 2,642 | 18,818 | +16,176 | +612.263% |
| External direct-import occurrences | 1,367 | 11,516 | +10,149 | +742.429% |
| Unresolved NumStability imports | 0 | 0 | 0 | n/a |
| Modules with a module docstring | 735 / 957 (76.803%) | 2,839 / 2,839 (100%) | +2,104 modules; +23.197 pp | n/a |
| Cyclic source-import SCCs | 0 | 0 | 0 | n/a |

This is unusually strong structural evidence of a file/module split: module
count nearly tripled and internal import edges increased more than sevenfold,
while normalized bytes fell by 0.194% and nonblank lines fell by 4.002%.
Physical lines increased by 149.384%, reflecting extensive whitespace in the
presentation tree; neither physical nor nonblank lines alone measure proof
complexity. The import increase documents finer compilation/navigation
boundaries, not more mathematical dependencies. The continued absence of
source-import cycles supports an acyclic module order under the scanner's
parser.

The source-tree digest changed from
`cd5be41c56cf8f6dec940b89324298aa3bd5e3dd14853afecdd2017b08fb0cb1`
to
`6fd479228698609a447bab444439445cdd48bb299a746a7041279d30f15857d3`,
as expected for the reorganized source tree.

## Exact declaration-graph comparison

The exact historical extractor and the unmodified
`summarize_declaration_tsv` function were replayed against `045daf2...`.
The retained raw current stream is
[`raw/phase10a_exact_current.tsv.gz`](raw/phase10a_exact_current.tsv.gz):
770,151 rows comprising one format marker, 77,246 declaration rows, 283,049
signature rows, and 409,855 body/proof rows. Its compressed SHA-256 is
`bca79605b72534a4784a4a458008b6b283fb5a05e8336370abde6163cc3e5e84`;
the 124,996,640-byte decompressed stream hashes to
`3d3d5dc5b329b4b48ea76d95b615967ee1c9f624cae0f508f99c4f95cd36eaa9`.
The exact current summary is
[`historical/phase10a_exact_current_summary.json`](historical/phase10a_exact_current_summary.json),
SHA-256
`264b53838599b48f071f8122a5efb61bc38f23bde2a9f7c6aff2362cf401d701`.

| Exact Phase 10A field | Phase 10A | `045daf2...` | Absolute delta | Relative delta |
| --- | ---: | ---: | ---: | ---: |
| Declaration nodes | 81,950 | 77,246 | -4,704 | -5.740% |
| Declaration-bearing owner modules | 803 | 1,649 | +846 | +105.355% |
| Environment-public nodes | 56,187 | 52,332 | -3,855 | -6.861% |
| Private nodes | 4,341 | 4,516 | +175 | +4.031% |
| Internal-detail nodes | 21,422 | 20,398 | -1,024 | -4.780% |
| Signature pairs | 305,425 | 283,049 | -22,376 | -7.326% |
| Body/proof pairs | 439,195 | 409,855 | -29,340 | -6.680% |
| Type/body union pairs | 491,557 | 458,631 | -32,926 | -6.698% |
| Cross-module union pairs | 222,319 | 268,228 | +45,909 | +20.650% |
| Public nodes with an incoming project pair | 40,963 | 37,997 | -2,966 | -7.241% |
| Public nodes used by another owner module | 8,371 | 12,795 | +4,424 | +52.849% |
| Largest all-node weak component | 73,995 | 69,427 | -4,568 | -6.173% |
| Largest public-induced weak component | 54,301 | 50,410 | -3,891 | -7.166% |
| All-node isolates | 5,881 | 5,450 | -431 | -7.329% |
| Public-node isolates | 159 | 148 | -11 | -6.918% |

### Denominator-aware interpretation

| Metric | Phase 10A formula/result | `045daf2...` formula/result | Change |
| --- | --- | --- | ---: |
| Incoming-reference coverage, environment-public universe | 40,963 / 56,187 = 72.905% | 37,997 / 52,332 = 72.608% | -0.297 percentage points |
| Cross-module utilization, environment-public universe | 8,371 / 56,187 = 14.898% | 12,795 / 52,332 = 24.450% | +9.551 percentage points |
| Cross-module share of unique union pairs | 222,319 / 491,557 = 45.228% | 268,228 / 458,631 = 58.484% | +13.257 percentage points |
| Largest all-node weak-component coverage | 73,995 / 81,950 = 90.293% | 69,427 / 77,246 = 89.878% | -0.415 percentage points |
| Largest public-induced weak-component coverage | 54,301 / 56,187 = 96.643% | 50,410 / 52,332 = 96.327% | -0.316 percentage points |
| Mean declarations per declaration-bearing module | 81,950 / 803 = 102.055 | 77,246 / 1,649 = 46.844 | -55.211 (-54.100%) |

Percentage-point changes are computed from the unrounded numerator/denominator
ratios and only then rounded to three decimal places; they are not obtained by
subtracting the displayed three-decimal percentages.

The strongest defensible historical conclusion is two-part. First,
environment-public incoming-reference coverage and weak-component coverage are
nearly unchanged under the exact old schema. Second, dependencies are exposed
across many more, smaller owner modules: declaration-bearing module count more
than doubled while mean declarations per such module approximately halved.
The measured increases in cross-module pairs and declarations with
cross-module consumers are therefore real boundary measurements but are
strongly confounded by the reorganization. A file split can convert an
unchanged logical pair from intra-module to cross-module. It is not defensible
to call the 20.650% edge-count rise a 20.650% increase in mathematical reuse.

Weak connectedness has an additional strict limit: it shows undirected graph
connectivity after forgetting dependency direction. It does not show that
every declaration is consumed, useful, canonical, or source-faithful.

## Why the later recovered schema is not a Phase 10A comparator

The post-Phase10A `tools/library_audit/` tree was recovered from untracked-files
commit `8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d`, the third parent of stash
`698c08e9897941ee4d5b19e944a7ad49836d2b67` based at
`2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`. It is preserved under
[`historical/recovered_library_audit/`](historical/recovered_library_audit/).
Its known-example validation passed, and it was useful for a separate current
snapshot, but it did not produce the original Phase 10A values.

| Contract point | Exact Phase 10A tool | Recovered library-audit tool |
| --- | --- | --- |
| Internal-name predicate | `Name.isInternalDetail` | `Name.isInternal` |
| Reserved/generated names | Included; no reserved filter | Included, but labelled only by internal/private fields |
| Self references | Not explicitly erased | Erased |
| Recursor body references | Rule RHS constants included | Omitted because `ConstantInfo.value? true` gives no recursor value |
| External direct references | Removed during extraction | Retained with target scope; project graph filters later |
| Public weak component | Largest component of public-induced graph | Public nodes inside largest all-node component |

An additional validation check during this audit found that the recovered
analyzer's iterative DFS does not always compute a true finishing order when a
DAG has a cross-edge to a previously scheduled sibling. It can consequently
merge unrelated nodes into false SCCs and invalidate its SCC-condensed
transitive and depth metrics. Those fields are not used anywhere in the
Phase 10A comparison above. Raw extraction, direct-edge/incoming/cross-module
counts, and union-find weak components are unaffected. The enriched current
analyzer uses a corrected iterator-stack DFS with a sibling-cross-edge
regression test; its validation log is
[`current_graph/validation_tests.log`](current_graph/validation_tests.log).

For example, the recovered current summary calls 58,120 of 77,246 nodes
public, whereas the exact Phase 10A replay calls 52,332 public. The 5,788-node
difference is caused by the different visibility predicate, not by a branch
change. Its 458,414 project pairs and 268,231 cross-module pairs also differ
slightly from the exact Phase 10A replay's 458,631 and 268,228 because the edge
contracts differ. These results are valid within their own schema but cannot
be mixed into the table above.

## Comparisons that remain unavailable

The missing historical raw TSV means the recovered aggregate JSON cannot
support any of the following requested comparisons:

- exact public-name additions, removals, or preservation;
- public import-path additions, removals, or preservation;
- compatibility-module and compatibility-import additions, removals, or
  preservation, including whether an old path continued to forward to the same
  canonical owner;
- probable declaration moves or renames by statement fingerprint;
- owner-module changes for a named declaration;
- stable logical-pair additions and removals independent of file boundaries;
- preservation or creation of a named dependency chain;
- per-layer, per-domain, or per-chapter edge changes;
- source-wrapper-to-canonical delegation changes;
- exact-statement group additions/removals;
- a declaration-level before/after architecture diagram.

The exact additional evidence required is a clean disposable worktree at
`d21a4ed...`, the recovered exact tools restored at their historical paths,
and a new extraction run with `--keep-dependency-tsv` to retain the full
format-2 historical stream. A declared name/fingerprint reconciliation must
then compare that stream with the retained current stream, report stable pairs
separately from owner changes, and avoid turning equal expressions into
semantic redundancy claims.

Rebuilding `d21a4ed...` was outside this audit episode's storage-safe execution
envelope. The historical build records are passing cache-preserving builds,
not fresh-output timing evidence. The current full-build episode likewise has
separate build classifications in
[`provenance/BUILD_AND_ENVIRONMENT.md`](provenance/BUILD_AND_ENVIRONMENT.md).
No historical/current clean-time delta is claimed.

## Thesis-safe formulations

Safe:

> Replaying the byte-identical Phase 10A analyzer at the presentation commit
> showed that environment-public incoming-reference coverage remained almost
> unchanged (72.905% to 72.608%), while declaration ownership was distributed
> over 1,649 rather than 803 declaration-bearing modules. Cross-module
> utilization rose from 14.898% to 24.450%, but this boundary-sensitive change
> is reported as evidence of finer modularization, not as an independent
> increase in mathematical reuse.

> Under the exact historical source scanner, the reorganized tree grew from
> 957 to 2,839 modules while normalized source bytes slightly decreased
> (69,590,164 to 69,455,337) and the source-import graph remained acyclic. This
> is direct structural evidence of a much finer module decomposition.

Unsafe:

- “Phase 10A contained 56,187 handwritten public theorems.” Generated and
  reserved declarations were not excluded.
- “40,963 declarations were externally usable.” Incoming internal references
  do not test a client API.
- “Cross-module reuse improved by 20.650%.” That number is an edge-count delta
  under changed module boundaries.
- “Every declaration in the largest component is reused.” Weak connectedness
  forgets direction.
- “The reorganization preserved all declarations and logical edges.” The old
  raw names and pairs are unavailable.
- “Equal statements are duplicates.” Exact elaborated equality is a review
  signal; source and API roles can differ.
- “Compilation or dependency preservation proves fidelity to Higham.” Source
  faithfulness requires a separate PDF-first audit.

## Reproduction and audit trail

Full recovery/search/replay commands are in
[`historical/PHASE10A_COMMANDS.md`](historical/PHASE10A_COMMANDS.md) and the
source-scan command log linked above. The exact current dependency checksums
are in
[`historical/PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv`](historical/PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv).

The compact current source replay command is:

```bash
/opt/homebrew/bin/python3 \
  tooling/phase10a_source_scan_replay.py \
  --generator historical/phase10a_exact/tools/architecture/generate_baseline.py \
  --worktree _worktree \
  --commit 045daf28056a6e4358d5de7c22c7a9d7acc2e80e \
  --output-json historical/phase10a_exact_current_source_scan.json \
  --output-modules historical/phase10a_exact_current_source_modules.csv
```

All paths are relative to this audit directory. The wrapper records absolute
paths, its own hash, the recovered generator hash, the invoked function name,
and `function_source_modified=false` inside its JSON envelope.
