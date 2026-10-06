# Reproducing the `origin/higham_v01` library audit

This document reproduces the read-only NumStability architecture audit at
commit `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`. The measurement sources,
temporary Lean clients, recovered historical programs, logs, and reports live
under this ignored audit directory; none is part of the audited source tree.

The reproducibility conclusion has one important qualification: the retained
snapshot has a successful cached same-commit `lake build`, but no successful
clean full build. Two fresh-output attempts were constrained by the host's
free disk space. The first ended with `ENOSPC`; the second was stopped before
the same failure. Consequently, the recorded `2.80 s` run is **not** a clean
or incremental compilation time. The complete episode record is in
[BUILD_AND_ENVIRONMENT.md](provenance/BUILD_AND_ENVIRONMENT.md) and
[build_attempts.csv](build/build_attempts.csv).

## Immutable identity and environment

| Item | Recorded value |
|---|---|
| Audited ref | `origin/higham_v01` |
| Audited full commit | `045daf28056a6e4358d5de7c22c7a9d7acc2e80e` |
| Local `higham_v01` at capture | same full commit |
| Local/remote agreement | yes |
| Audit time zone | `Europe/Athens` (`EEST`, UTC+03:00) |
| Final environment capture | `2026-09-03T11:19:42+0300` |
| Final ref/source-cleanliness recheck | `2026-09-03T12:40:18+0300 EEST` |
| Host | macOS 26.5.2 build 25F84; Darwin 25.5.0; arm64 |
| CPU / memory | 8 logical and 8 physical cores; 17,179,869,184 bytes |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Lean | 4.29.0-rc3, `5d86aa4032284a5242470e95fbe25f1ff506763d` |
| Lake | `5.0.0-src+5d86aa4` |
| Mathlib | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Python used by audit scripts | CPython 3.14.6 |
| Current graph schema | `numstability-elaborated-architecture/2.1.0` |

All nine Lake package checkouts matched the committed manifest:

| Package | Revision |
|---|---|
| mathlib | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| plausible | `2b93f2523263a6df8a8fbbe3dd28b7f028087480` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `ea1e51a85f6bd53b6a84239b00593eebd03d522b` |
| proofwidgets | `212dc300449e436298804f09b264f624667106f8` |
| aesop | `6f8999a4e31701d2c905262d3788a8c0d21b3f1f` |
| Qq | `5bb0ac23f6e6c4c3ba1b084f2d65cb1bd2a9cf7a` |
| batteries | `ed250d06b33e67aa5dc5f2cc349a5a35e8b6b390` |
| Cli | `0c688ceba0d380f6e56f977009fc2bb2322af5a3` |

The authoritative machine-readable records are
[build_environment.json](provenance/build_environment.json) and
[package_revision_validation.csv](provenance/package_revision_validation.csv).
The later [final_ref_recheck.log](provenance/final_ref_recheck.log) confirms
that the local branch, remote-tracking ref, live `ls-remote` result, and
isolated worktree still resolved to the same commit, that the isolated source
remained clean, and that the caller still had only its pre-existing
`paper_bencmark/` untracked path.
The pinned input hashes are:

```text
fdf7ccfe204caff50fab1913b9f13a763be5384e87d14555c9fdcb2be2b9f7f8  lean-toolchain
a4c00f6534596883069d57bbe529adb6bb5b295019eb32b8d4c2fb6a34c021ce  lakefile.toml
ccfe8a72d6d227aebfe4e58575ddf2a2aef03b795052f97b770c36f684cc5774  lake-manifest.json
```

## Aggregate and root-module scope

Lake's default target is `NumStability`. The exact primary import chain is:

```text
NumStability
  -> NumStability.All
       -> NumStability.Algorithms
       -> NumStability.Analysis
       -> NumStability.FloatingPoint
       -> NumStability.Source
            -> NumStability.Source.Higham
```

These arrows are source imports, not declaration-dependency edges. The nine
explicit root-entry modules audited for exposure are `NumStability`,
`NumStability.All`, `NumStability.Core`, `NumStability.FloatingPoint`,
`NumStability.Analysis`, `NumStability.Algorithms`, `NumStability.Source`,
`NumStability.Source.Higham`, and the legacy compatibility aggregate
`NumStability.Higham`. The exact complete entry-point universe contains 479
rows: 9 root entries, 127 `All` aggregates, and 343 documented aggregates. It
is frozen in [entry_points.csv](static_architecture/entry_points.csv), SHA-256
`f1cf9bbc3f7d99962c6872ca200bf04ded09ce028ba6433e3b1c7836f1e4daf5`.

The source universe is `NumStability.lean` plus every `*.lean` file beneath
`NumStability/`, discovered with `rg --files -uu`: 2,839 project library files.

## Required software and capacity

Install Git, Elan, the pinned Lean toolchain, Lake, Python 3.14 or a compatible
Python 3 with the standard library, ripgrep (`rg`), `gzip`, `tar`, `jq`, and a
SHA-256 utility (`shasum -a 256` on macOS or `sha256sum` on GNU systems). The
measurement and figure programs use only their declared Python dependencies;
the graph, static, timing, probe-summary, hygiene, checksum, and link-checking
programs use the standard library.

The original host used BSD `/usr/bin/time` with `-l` or `-lp`. On GNU systems,
use `/usr/bin/time -v` and retain the different output format. Timing values
from different hosts or timing implementations are not directly comparable.

A fully independent worktree needs space for dependencies (observed about
6.7 GiB) and NumStability outputs (known same-commit tree about 8.2 GiB), plus
temporary artifacts. Reserve at least 16 GiB free. If dependencies are shared
or symlinked at their exact manifest revisions, reserve at least 9 GiB for
fresh project outputs. The 2026-09-03 host did not have this capacity.

## Clean branch isolation

Set paths without repurposing `HOME` or `CODEX_HOME`:

```bash
REPO=<library-repo>
AUDITED_COMMIT=045daf28056a6e4358d5de7c22c7a9d7acc2e80e
AUDIT_ROOT="$REPO/tmp/library_audit/higham_v01-045daf2"
WT="$AUDIT_ROOT/_worktree"
mkdir -p "$AUDIT_ROOT"
```

Resolve the remote again and retain both remote and local state before
creating a detached worktree. A moved remote ref does not invalidate this
snapshot, but it means a new audit must use a new commit-labelled directory.

```bash
git -C "$REPO" ls-remote origin refs/heads/higham_v01
git -C "$REPO" rev-parse --verify refs/remotes/origin/higham_v01
git -C "$REPO" rev-parse --verify refs/heads/higham_v01
git -C "$REPO" status --short --branch
git -C "$REPO" worktree list --porcelain
git -C "$REPO" check-ignore -v "$AUDIT_ROOT"
git -C "$REPO" cat-file -e "${AUDITED_COMMIT}^{commit}"
git -C "$REPO" worktree add --detach "$WT" "$AUDITED_COMMIT"
git -C "$WT" rev-parse HEAD
git -C "$WT" status --porcelain=v1 --untracked-files=all
```

The final command must print nothing. Do not switch the caller's checkout.
Before and after every measurement family, repeat the `rev-parse` and status
checks. The original isolated source tree was clean throughout. The caller's
pre-existing tracked and untracked files were not inputs and must not be
deleted or modified.

Capture the platform, versions, roots, and ignored-inclusive file list:

```bash
cd "$WT"
TZ=Europe/Athens date '+%Y-%m-%dT%H:%M:%S%z %Z'
date -u '+%Y-%m-%dT%H:%M:%SZ'
uname -a
uname -m
sw_vers
lake --version
lake env lean --version
elan --version
python3 --version
rg --files -uu | sort
rg --files -uu NumStability -g '*.lean' | sort
shasum -a 256 lean-toolchain lakefile.toml lake-manifest.json
jq -r '.packages[] | [.name, .rev] | @tsv' lake-manifest.json
```

The exhaustive original environment/build shell record is
[COMMANDS_BUILD_ENVIRONMENT.md](provenance/COMMANDS_BUILD_ENVIRONMENT.md).

## Tool recovery and hashes

The exact Phase 10A tool was recovered from commit
`d21a4ed5b91008a8a5bc60741765f27fcdf86edf`; the historical JSON recorded
candidate HEAD `899003baca0fdca2714344a69c10eef4b2d3c306`, where the two relevant
files are byte-identical. Clean-validation evidence was found at
`21e130ac8355de8ec1a74f22a73bf103e00bc48f`. The later, richer
`tools/library_audit` tree was recovered from untracked-files stash object
`8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d` (base commit
`2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`). It did **not** generate the
Phase 10A headline figures.

Key recovered/current tool hashes are:

| Tool | SHA-256 |
|---|---|
| Phase 10A `declaration_dependencies.lean` | `30186d3470320983e2ada2e61fce7efaa7e6230c71348c5d37a9801526be2acd` |
| Phase 10A `generate_baseline.py` | `fc5863b2ca4e8f2dd03d2f012c40df9f26666849073a4e5b1babc65a671d6a94` |
| recovered `DeclarationGraph.lean` | `ef2731b1b9270b5d6185c4a9a2caa611d113ca1ba19ca4e8785e004bbd25c8f1` |
| recovered `DeclarationFingerprints.lean` | `cd8f2a8e60fc65841a4b9bf551205688c44591ebbd7fb72185f7cde58cd66142` |
| recovered `analyze_graph.py` | `03811e8519bd000d6d00620eb8f2780f52e59e5a3812b416b2ea91137b51d7ac` |
| recovered `find_duplicate_candidates.py` | `3c79fd0a9fd51b8c0f64e5e70d426dc3fe7a059a6d8860cefc0d0988651c91f8` |
| skill `DeclarationOrigins.lean` | `61a38f911a8d0da2c28d082ceaa5d2345eb7e9498cfd2f0c3cbe670e37a777ea` |
| current `DeclarationMetadata.lean` | `8ad62709b4a031931414421b83cbe92787a49be0d4e3d4a337ce6b4cade7d628` |
| current graph analyzer | `543159b9dd6645a19c736a27cda585701b66fe6134d457b4eb891dd26c842d45` |
| current graph regression tests | `b9059413dc37bff39a2c38f5e52b091891aceaed2b53077e897b5dc92cb6b14a` |
| coverage-contract builder | `1967659d5b85cd5114bfbc7dc87d41e8c09269e8cae4991d82b829f3e9de6e1a` |
| public type/entry-point exposure analyzer | `1fb91f07610320ed420698e0ddd9c89bc16307c3fe81796885beed9ec7fbaf60` |
| universe-separated reuse-leader builder | `a7c171d48b8c8c8295c2116866ee1a29c8f32737a53eb4867ffb8678a01abd26` |
| source-written component analyzer | `df53e2de72028c1797fc5e0a68613e5bfe3f5bd1b8fbf43aa23932971f6dc05f` |
| static architecture analyzer | `dfba978902ba0bbc19453eede1e01c74c7b9a59cc4bcdd96bb4e89198b8d7efe` |
| Phase 10A source-scan replay wrapper | `ffefca5ec3163c6ec5c2f4cb896e7534ade0d4c68156e37c9927db4a8bbf5eeb` |
| public-probe runner | `0ce84d1c9f9d9e346da6eeac873dd710691cb95033914ed8a1040515c72f1668` |
| public-probe summarizer | `7096ae700138060b001509678f9bcd87e2ee23a0dec2405d3a209ab14ab038e3` |
| fresh-module timing runner | `10a4b7e0770e50291cb5da83e15a478fba9dd08daee3654cbc19824017c3b8c6` |
| timing summarizer | `0ead4c898f30364dab85fdce5ca85e0ffd48d03b64745f786c3e1392de1d63cd` |
| proof-hygiene analyzer | `88fed21fb61d4ba013d2a38ad87db0cc93d321dad2ac91ecef28b29bef1003f4` |
| representative-axiom parser | `805f9f21072128b519af0549dac2ac436f6bdbae2dc914f8edf6b0babc94b4e1` |
| skill priority-review builder | `0c7fc186aea208ec8c672dd63a43ca8a945c0ea20c2560da3b2998e867bb4094` |
| priority-review current-metrics adapter | `b56c1340f716c2851c489b45372d234312a3fbb3ab2e549ef38791c734ca5380` |
| representative-chain builder | `e3911db08f101e56cd7167aebdcb36344ed2e27598fcbc974dafd257778f3a5a` |
| deterministic SVG figure generator | `fb5e10f1102ff70358603dd4cd7122002bf2ff5569553e2be93ceac48da8ae65` |
| final artifact checksum writer/verifier | `500ca7cde9b81da74d57764498cabc888404b5be53cd2ae4898ffccf3a776be8` |
| current-report link validator | `35902f65d07c7152050d1a942f0fec3e0af6f5b3fb188903f9cac7bfbf41ebc4` |

The exact history searches and extraction commands, including `git archive`
commands, are in [PHASE10A_COMMANDS.md](historical/PHASE10A_COMMANDS.md). The
machine-readable provenance and complete recovered-file hash inventory are
[PHASE10A_RECOVERY.json](historical/PHASE10A_RECOVERY.json) and
[PHASE10A_RECOVERY_CHECKSUMS.csv](historical/PHASE10A_RECOVERY_CHECKSUMS.csv).
To re-extract the two core trees while the Git objects remain reachable:

```bash
mkdir -p "$AUDIT_ROOT/historical/phase10a_exact"
git -C "$REPO" archive d21a4ed5b91008a8a5bc60741765f27fcdf86edf \
  tools/architecture \
  docs/architecture/baselines/2026-07-24-organization-phase10a.json \
  docs/architecture/baselines/2026-07-24-organization-phase10a.md \
  docs/architecture/baselines/2026-07-24-organization-phase10a-build.md \
  docs/architecture/migrations/2026-07-24-higham-chapter14-section05-phase10.md \
  docs/architecture/tiers.json docs/architecture/layout-exceptions.json \
  | tar -x -C "$AUDIT_ROOT/historical/phase10a_exact"

mkdir -p "$AUDIT_ROOT/historical/recovered_library_audit"
git -C "$REPO" archive 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d \
  tools/library_audit \
  | tar -x -C "$AUDIT_ROOT/historical/recovered_library_audit"
```

No recovered tool was added to the presentation branch. The retained copies
beneath this audit directory remain the reproducible fallback if the stash
object is later garbage-collected.

## Build classifications and commands

| Episode | Output/cache class | Result | Timing interpretation |
|---|---|---|---|
| Fresh full build attempt 1 | fresh project outputs; freshly materialized pinned dependencies | exit 1, host `ENOSPC` | incomplete; no clean time |
| Fresh full build attempt 2 | fresh project outputs; exact cached/prebuilt pinned dependencies | exit 130, capacity-stopped | incomplete; no clean time |
| Full-build verification | complete APFS-cloned outputs from the same commit/toolchain/manifest | exit 0 | cached same-commit verification; 2.80 s is not compilation time |
| Phase 10A/current graph extraction | existing same-commit compiled environment | exit 0 | extraction time, not compilation time |
| 30-module timing sample | fresh target output; cached exact imported modules | 30/30 exit 0 | sample-only fresh-target times |
| 15 public API pairs | fresh probe output; cached exact imported modules | 30/30 exit 0 | probe elaboration times, not library times |

No successful incremental compilation time is reported as a clean time.

For a genuine clean-output full build, start from a new detached worktree with
no `.lake/build` and enough free storage:

```bash
cd "$WT"
test ! -e .lake/build
/usr/bin/time -l -o "$AUDIT_ROOT/build/reproduction_lake_update.time" \
  lake update \
  > "$AUDIT_ROOT/build/reproduction_lake_update.log" 2>&1
test ! -e .lake/build
/usr/bin/time -l -o "$AUDIT_ROOT/build/reproduction_full_build_clean.time" \
  lake build \
  > "$AUDIT_ROOT/build/reproduction_full_build_clean.log" 2>&1
```

This is the appropriate command for a future clean compilation time. The
original first fresh run reached filesystem error 28 (`ENOSPC`) after roughly
101 seconds and 61 project oleans; timing output itself could not be completed
after the disk filled. A second fresh-output run, with exact cached dependency
repositories and no project build outputs, was deliberately interrupted with
exit 130 after 17.49 seconds and 16 project oleans when another `ENOSPC` was
predictable. Neither partial duration is a clean-build timing, and neither run
exposed a Lean typechecking error before termination.

The successful audit verification used an APFS copy-on-write clone of a
complete `.lake/build` only after the source commit, toolchain, manifest, and
all dependency revisions were shown identical. Its command was:

```bash
cd "$WT"
/usr/bin/time -l -o "$AUDIT_ROOT/build/full_build_cached_same_commit_time.log" \
  lake build \
  > "$AUDIT_ROOT/build/full_build_cached_same_commit_stdout_stderr.log" 2>&1
```

It exited 0 in 2.80 seconds with 0 `Built`, 160 `Replayed`, and 0 error
records. It is **cached same-commit full-build verification**, not clean and
not an incremental compile benchmark. Do not use an output tree from a
different commit, toolchain, manifest, or package revision.

## Static source and import analysis

The static analyzer is deterministic and does not read oleans:

```bash
python3 "$AUDIT_ROOT/static_architecture/static_architecture.py" \
  --root "$WT" \
  --output "$AUDIT_ROOT/static_architecture"
```

It scans the complete `rg --files -uu` source universe, validates its nested
comment/string lexer on known examples, and emits source-file, line-count,
module, source-import, entry-point, compatibility, naming, layer, chapter,
domain, and hygiene tables. See [COMMANDS.md](static_architecture/COMMANDS.md),
[validation.json](static_architecture/validation.json), and
[summary.json](static_architecture/summary.json).

## Exact Phase 10A-schema replay

The historical extractor writes a path supplied as its only argument. The
following FIFO command is the exact reproduction command reconstructed from
that recovered interface and the retained compressed artifact. The verbatim
original shell wrapper was not preserved; this block must not be described as
its literal transcript.

```bash
PHASE_FIFO_DIR=$(mktemp -d <tmp>/numstability-phase10a-replay.XXXXXX)
PHASE_FIFO="$PHASE_FIFO_DIR/declarations.tsv"
mkfifo "$PHASE_FIFO"
gzip -9 -c "$PHASE_FIFO" > "$AUDIT_ROOT/raw/phase10a_exact_current.tsv.gz" &
PHASE_GZIP_PID=$!
cd "$WT"
/usr/bin/time -lp -o "$AUDIT_ROOT/raw/phase10a_exact_extraction.time" \
  lake env lean --run \
  "$AUDIT_ROOT/tooling/phase10a_exact/tools/architecture/declaration_dependencies.lean" \
  "$PHASE_FIFO" \
  > "$AUDIT_ROOT/raw/phase10a_exact_extraction.log" 2>&1
wait "$PHASE_GZIP_PID"
unlink "$PHASE_FIFO"
rmdir "$PHASE_FIFO_DIR"
gzip -t "$AUDIT_ROOT/raw/phase10a_exact_current.tsv.gz"
```

The retained run took 95.11 seconds and is compiled-environment extraction
over existing exact-commit outputs, not a library build. Its raw logical
stream is 124,996,640 bytes and 770,151 rows. Validate both retained and
logical-stream hashes using
[PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv](historical/PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv).

Summarize with the exact unmodified historical function while keeping the
large uncompressed stream off disk:

```bash
SUMMARY_DIR=$(mktemp -d <tmp>/numstability-phase10a-summary.XXXXXX)
SUMMARY_FIFO="$SUMMARY_DIR/current.tsv"
mkfifo "$SUMMARY_FIFO"
gzip -dc "$AUDIT_ROOT/raw/phase10a_exact_current.tsv.gz" > "$SUMMARY_FIFO" &
SUMMARY_GZIP_PID=$!
python3 -c 'import importlib.util,json,sys; from pathlib import Path; p=Path(sys.argv[1]); mpath=Path(sys.argv[2]); spec=importlib.util.spec_from_file_location("phase10a_exact_generate_baseline",mpath); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); print(json.dumps(m.summarize_declaration_tsv(p),indent=2,sort_keys=True))' \
  "$SUMMARY_FIFO" \
  "$AUDIT_ROOT/historical/phase10a_exact/tools/architecture/generate_baseline.py" \
  > "$AUDIT_ROOT/historical/phase10a_exact_current_summary.json"
wait "$SUMMARY_GZIP_PID"
unlink "$SUMMARY_FIFO"
rmdir "$SUMMARY_DIR"
```

Only aggregate fields generated by this same historical code are compared to
Phase 10A. The old raw TSV was not recovered, so declaration-name, move,
rename, and stable-edge diffs are unavailable.

Replay the exact historical `scan_sources` function against the current
worktree through the audit-only serialization wrapper:

```bash
python3 "$AUDIT_ROOT/tooling/phase10a_source_scan_replay.py" \
  --generator "$AUDIT_ROOT/historical/phase10a_exact/tools/architecture/generate_baseline.py" \
  --worktree "$WT" \
  --commit "$AUDITED_COMMIT" \
  --output-json "$AUDIT_ROOT/historical/phase10a_exact_current_source_scan.json" \
  --output-modules "$AUDIT_ROOT/historical/phase10a_exact_current_source_modules.csv" \
  > "$AUDIT_ROOT/historical/PHASE10A_SOURCE_SCAN_CURRENT_STDOUT.log"
```

The first wrapper attempt failed during Python 3.14 dynamic-module loading;
the wrapper was corrected to register the loaded module in `sys.modules`
before executing its dataclass definitions. The second command above exited
successfully. The recovered `scan_sources` implementation itself was not
modified. Exact command and output hashes are retained in
`historical/PHASE10A_SOURCE_SCAN_CURRENT_COMMAND.log` and
`historical/PHASE10A_SOURCE_SCAN_CURRENT_SHA256SUMS`.

## Current compiled declaration graph

The byte-recovered later extractor emits all direct targets, including
external ones, and overlapping type/body flags. Named FIFOs avoid retaining a
second multi-gigabyte plain-text copy:

```bash
FIFO_DIR="$AUDIT_ROOT/raw/library_audit_fifos"
mkdir -p "$FIFO_DIR"
mkfifo "$FIFO_DIR/declarations.csv" \
  "$FIFO_DIR/direct_dependencies.csv" \
  "$FIFO_DIR/module_imports.csv"
gzip -9 -c "$FIFO_DIR/declarations.csv" > "$AUDIT_ROOT/raw/declarations.csv.gz" &
DECL_GZIP_PID=$!
gzip -9 -c "$FIFO_DIR/direct_dependencies.csv" > "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" &
DEP_GZIP_PID=$!
gzip -9 -c "$FIFO_DIR/module_imports.csv" > "$AUDIT_ROOT/raw/module_imports.csv.gz" &
IMPORT_GZIP_PID=$!
cd "$WT"
NUMSTABILITY_AUDIT_OUT="$FIFO_DIR" /usr/bin/time -lp \
  lake env lean \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/DeclarationGraph.lean" \
  > "$AUDIT_ROOT/raw/library_audit_extraction.log" \
  2> "$AUDIT_ROOT/raw/library_audit_extraction.time"
wait "$DECL_GZIP_PID" "$DEP_GZIP_PID" "$IMPORT_GZIP_PID"
unlink "$FIFO_DIR/declarations.csv"
unlink "$FIFO_DIR/direct_dependencies.csv"
unlink "$FIFO_DIR/module_imports.csv"
rmdir "$FIFO_DIR"
```

Integrity and row accounting:

```bash
gzip -t "$AUDIT_ROOT/raw/declarations.csv.gz"
gzip -t "$AUDIT_ROOT/raw/direct_dependencies.csv.gz"
gzip -t "$AUDIT_ROOT/raw/module_imports.csv.gz"
gzip -dc "$AUDIT_ROOT/raw/declarations.csv.gz" | wc -l
gzip -dc "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" | wc -l
gzip -dc "$AUDIT_ROOT/raw/module_imports.csv.gz" | wc -l
```

Expected counts including headers are 77,247, 3,963,824, and 29,566,
respectively.

The original gzip wrappers did not request a normalized zero timestamp, and
Python's gzip writers likewise retain container metadata. A later extraction
can therefore have identical decompressed CSV/TSV bytes and different `.gz`
bytes. Use row counts and decompressed logical-stream hashes to compare a
regeneration; use `ARTIFACT_SHA256SUMS` to authenticate the exact retained
containers. The Phase 10A replay already records both compressed and
decompressed hashes explicitly.

Extract reserved-name/origin evidence with the exact skill program and richer
compiled metadata with the ignored audit-only program:

```bash
cd "$WT"
NUMSTABILITY_AUDIT_OUT="$AUDIT_ROOT/raw" /usr/bin/time -lp \
  lake env lean \
  "$AUDIT_ROOT/tooling/current_audit/DeclarationOrigins.lean" \
  > "$AUDIT_ROOT/raw/declaration_origins_extraction.log" \
  2> "$AUDIT_ROOT/raw/declaration_origins_extraction.time"

NUMSTABILITY_AUDIT_OUT="$AUDIT_ROOT/raw" /usr/bin/time -lp \
  lake env lean "$AUDIT_ROOT/tooling/current_audit/DeclarationMetadata.lean" \
  > "$AUDIT_ROOT/raw/declaration_metadata_extraction.log" \
  2> "$AUDIT_ROOT/raw/declaration_metadata_extraction.time"
```

The original run addressed the skill copy at
`<codex-home>/skills/numstability-library-reorganization/scripts/DeclarationOrigins.lean`.
`tooling/current_audit/DeclarationOrigins.lean` is a byte-identical retained
copy (`61a38f...77ea`) so reproduction does not depend on that installation
path.

The first metadata attempt used an invalid `env.isStructure` call and failed
before extraction. The retained extractor was corrected to use
`Lean.isStructure`, run again, and its successful replacement CSV is the only
metadata input. No Lean library source changed.

Extract exact elaborated-expression statement groups:

```bash
cd "$WT"
NUMSTABILITY_AUDIT_OUT="$AUDIT_ROOT/raw" /usr/bin/time -lp \
  lake env lean \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/DeclarationFingerprints.lean" \
  > "$AUDIT_ROOT/raw/declaration_fingerprints_extraction.log" \
  2> "$AUDIT_ROOT/raw/declaration_fingerprints_extraction.time"

python3 \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/find_duplicate_candidates.py" \
  "$AUDIT_ROOT/raw/statement_fingerprints.csv" \
  --output "$AUDIT_ROOT/metrics/exact_statement_groups/possible_duplicate_statements.csv"
```

Exact expression equality is only a review signal. It does not prove semantic
or API redundancy.

Build a narrow compatibility view from the valid current-schema metrics, then
run the skill's exact-statement/delegation and isolated-declaration
evidence-prioritization program. The adapter deliberately exposes only the
direct-edge fields required by the skill program. **Run the current graph
analyzer in the next section before executing this block.**

```bash
cd "$AUDIT_ROOT"
/usr/bin/time -l python3 current_graph/prepare_priority_metrics_adapter.py \
  --metrics current_graph/metrics/declaration_metrics.csv.gz \
  --edges current_graph/metrics/direct_project_dependencies.csv.gz \
  --source-commit "$AUDITED_COMMIT" \
  --output current_graph/priority_review_metrics_compat.csv \
  --provenance current_graph/priority_review_metrics_compat.provenance.json \
  > current_graph/priority_review_metrics_adapter_stdout.log \
  2> current_graph/priority_review_metrics_adapter_time_and_stderr.log

/usr/bin/time -l python3 \
  tooling/current_audit/prepare_priority_reviews.py \
  --duplicates metrics/exact_statement_groups/possible_duplicate_statements.csv \
  --metrics current_graph/priority_review_metrics_compat.csv \
  --dependencies <(gzip -dc raw/direct_dependencies.csv.gz) \
  --origins raw/declaration_origins.csv \
  --source-root _worktree/NumStability \
  --snapshot-commit "$AUDITED_COMMIT" \
  --output-dir current_graph/priority_reviews \
  > current_graph/priority_reviews_stdout.log \
  2> current_graph/priority_reviews_time_and_stderr.log
```

The exact invocation uses Bash process substitution because the skill program
expects a plain CSV. On a shell without process substitution, a named FIFO
drained by `gzip -dc` is equivalent. The adapter defines and records every
compatibility column in
`current_graph/priority_review_metrics_compat.provenance.json`; neither step
consumes recovered-analyzer SCC or transitive-count fields.
The original run addressed the installed skill script at
`<codex-home>/skills/numstability-library-reorganization/scripts/prepare_priority_reviews.py`;
the local path above is a byte-identical retained copy with the recorded
`0c7fc186...4094` hash.
The program prioritizes evidence only: it does not classify any declaration
as redundant or authorize deletion. If previously reviewed manual columns are
present in the selected output directory, the program deliberately preserves
them; use an empty output directory when validating the raw automatic result.

## Current graph analyzer and validation

The current analyzer was introduced because the historical/recovered tools do
not satisfy the expanded declaration-universe, authorship, boundary, depth,
and downstream-reach contract. Run its seven known-graph regression tests
first, including the sibling-cross-edge DAG that exposed the recovered
analyzer defect:

```bash
python3 -m unittest -v "$AUDIT_ROOT/current_graph/test_analyze_current_graph.py" \
  > "$AUDIT_ROOT/current_graph/validation_tests.log" 2>&1
```

Then analyze the retained raw graph:

```bash
cd "$AUDIT_ROOT"
/usr/bin/time -l python3 current_graph/analyze_current_graph.py \
  --declarations raw/declarations.csv.gz \
  --dependencies raw/direct_dependencies.csv.gz \
  --imports raw/module_imports.csv.gz \
  --metadata raw/declaration_metadata.csv \
  --origins raw/declaration_origins.csv \
  --modules static_architecture/modules.csv \
  --static-declarations static_architecture/static_declaration_starters.csv \
  --entry-points static_architecture/entry_points.csv \
  --worktree _worktree \
  --source-commit "$AUDITED_COMMIT" \
  --output current_graph/metrics \
  > current_graph/analyzer_stdout.log \
  2> current_graph/analyzer_time_and_stderr.log
```

The expected schema is documented in
[SCHEMA.md](current_graph/metrics/SCHEMA.md). The run must report zero raw
project-pair duplicates, zero missing project targets, exact equality of the
metadata/origin/declaration universes, agreement between two independent
reserved-name extractors, and the identity `type + body - both = all`.

## Contract-completion supplements

Run these four deterministic supplements from the audit root after the current
graph analyzer and static architecture pass. They take no command-line
arguments and resolve their inputs relative to their retained script paths:

```bash
cd "$AUDIT_ROOT"
python3 current_graph/build_coverage_metric_contract.py
python3 current_graph/analyze_public_type_exposure.py
python3 current_graph/build_reuse_leaders_by_universe.py
python3 current_graph/analyze_source_written_components.py
```

These are the exact commands recorded in their validation logs. The scripts
write the following versioned products:

| Script and tool SHA-256 | Schema | Outputs | Required validation result |
|---|---|---|---|
| `build_coverage_metric_contract.py`; `1967659d5b85cd5114bfbc7dc87d41e8c09269e8cae4991d82b829f3e9de6e1a` | `numstability-coverage-metric-contract/1.0.0` | `metrics/incoming_and_cross_boundary_coverage_contract.csv`, `metrics/incoming_and_cross_boundary_coverage_contract_summary.json`, and `current_graph/coverage_contract_validation.log` | all 27 rows recomputed exactly over 77,246 declarations; every numerator, denominator, and percentage agrees within `1e-6` percentage points |
| `analyze_public_type_exposure.py`; `1fb91f07610320ed420698e0ddd9c89bc16307c3fe81796885beed9ec7fbaf60` | `numstability-public-type-exposure/1.0.0` | `metrics/public_type_exposure_declarations.csv`, `metrics/public_type_exposure_edges.csv`, `metrics/environment_public_type_nonpublic_exposure_edges.csv`, `metrics/public_entrypoint_exposure_all.csv`, `metrics/public_type_exposure_summary.json`, and `current_graph/public_type_exposure_validation.log` | 8/8 toy cases; unique type pairs; complete endpoint metadata; expected 47,890-source universe; all old observed entry rows reproduced; 439 compiled closures agree with static closures and 40 declaration-free static fallbacks are validated; canonical Source signal disjointness verified |
| `build_reuse_leaders_by_universe.py`; `a7c171d48b8c8c8295c2116866ee1a29c8f32737a53eb4867ffb8678a01abd26` | `numstability-reuse-leaders/1.0.0` | `metrics/reuse_leaders_by_universe.csv`, `metrics/reuse_leaders_by_universe_summary.json`, and `current_graph/reuse_leaders_validation.log` | 3/3 toy ranking/tie cases; unique declaration rows; four universe sizes match inventory; all 500 overlapping legacy all-project ranking rows reproduced |
| `analyze_source_written_components.py`; `df53e2de72028c1797fc5e0a68613e5bfe3f5bd1b8fbf43aa23932971f6dc05f` | `numstability-source-written-components/1.0.0` | `metrics/source_written_component_memberships.csv.gz`, `metrics/source_written_component_size_distribution.csv`, `metrics/source_written_components_summary.json`, and `current_graph/source_written_components_validation.log` | toy weak/strong graphs pass; 49,573-member universe covered exactly; source-written-public weak distribution agrees with the main v2 analyzer |

All output paths in the table are relative to `current_graph/` unless already
prefixed with `current_graph/`. Each summary records the exact input artifact
hashes, output paths, metric definitions, filters, and the same tool hash shown
above. These supplements do not alter Lean sources or re-elaborate the
library. They refine reporting over the retained compiled graph and static
tables.

### Invalid fields in the recovered analyzer

For provenance, the byte-recovered `analyze_graph.py` was also tested and run
unchanged. Its included test passes, but a later sibling-cross-edge DAG
regression exposed an iterative DFS finishing-order defect. It can emit a
consumer before a dependency and can create false SCCs on its transpose pass.
Therefore **do not use** the recovered run's `strong_components`,
`strong_component_id`, `transitive_project_dependency_count`, or any depth or
condensation inference derived from them. The notice is
[INVALID_SCC_TRANSITIVE_NOTICE.md](metrics/recovered_library_audit_schema/INVALID_SCC_TRANSITIVE_NOTICE.md).

The unaffected inventory, unique direct-edge, direct fan-in/fan-out,
cross-module, weak-component, module-pair, apparent-leaf, and isolate fields
remain useful only as independent cross-checks. The primary SCC, transitive,
and depth results come from `numstability-elaborated-architecture/2.1.0`.

For completeness, the recovered invocation used gzip-fed FIFOs:

```bash
LEGACY_INPUT="$AUDIT_ROOT/metrics/_legacy_inputs"
LEGACY_OUT="$AUDIT_ROOT/metrics/recovered_library_audit_schema"
mkdir -p "$LEGACY_INPUT" "$LEGACY_OUT"
mkfifo "$LEGACY_INPUT/declarations.csv" \
  "$LEGACY_INPUT/direct_dependencies.csv" \
  "$LEGACY_INPUT/module_imports.csv"
gzip -dc "$AUDIT_ROOT/raw/declarations.csv.gz" > "$LEGACY_INPUT/declarations.csv" &
gzip -dc "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" > "$LEGACY_INPUT/direct_dependencies.csv" &
gzip -dc "$AUDIT_ROOT/raw/module_imports.csv.gz" > "$LEGACY_INPUT/module_imports.csv" &
python3 "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/test_analyze_graph.py"
/usr/bin/time -lp python3 \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/analyze_graph.py" \
  "$LEGACY_INPUT" --output "$LEGACY_OUT" \
  > "$AUDIT_ROOT/metrics/recovered_library_audit_analyze.log" \
  2> "$AUDIT_ROOT/metrics/recovered_library_audit_analyze.time"
unlink "$LEGACY_INPUT/declarations.csv"
unlink "$LEGACY_INPUT/direct_dependencies.csv"
unlink "$LEGACY_INPUT/module_imports.csv"
rmdir "$LEGACY_INPUT"
```

## Public API client probes

The predeclared 15-API stratified sample, exact declarations, source lines,
narrow imports, and intended client actions are in
[PREDECLARED_SAMPLE.csv](probes/PREDECLARED_SAMPLE.csv), SHA-256
`f7196f6b5813bc4d93c4196195db882a7efc73d2c65e2704da631e30797d623c`.
Every API has two independent external files: a visibility `#check` and a
minimal client theorem/example.

The exact 30 Lean command strings are frozen in
[run_commands.tsv](probes/run_commands.tsv). They follow this form:

```bash
/usr/bin/time -p -o <time-log> \
  lake env lean \
  -R "$AUDIT_ROOT/probes/src" \
  -o <initially-absent-probe-output>.olean \
  -i <initially-absent-probe-output>.ilean \
  <probe-source>.lean
```

Run the harness from the isolated worktree only when every target output path
is absent:

```bash
cd "$WT"
"$AUDIT_ROOT/probes/run_probes.sh"
python3 "$AUDIT_ROOT/probes/summarize_probes.py"
git status --porcelain=v1 --untracked-files=all
```

The final status command must be empty. These are fresh **probe target**
outputs with cached imported modules, not clean library compiles. A successful
`#check` proves visibility only; a successful client compile is stronger but
applies only to that exact probe. The known-good visibility and deliberately
ill-typed client controls are recorded in
[VALIDATION_COMMANDS.md](probes/VALIDATION_COMMANDS.md). See
[COMMANDS.md](probes/COMMANDS.md) for the complete procedure.

## Fresh-output module timing sample

The timing sample was frozen before measurement and contains 30 modules across
roots, layers, domains, chapter aggregates, and known large files. Run:

```bash
cd "$AUDIT_ROOT"
python3 timings/run_fresh_module_timings.py
python3 timings/rerun_interfered_timings.py
python3 timings/summarize_timings.py
```

Rows 25 and 26 were replaced by identical quiet reruns because their original
intervals overlapped a recorded unrelated-host workload. The authoritative
table is `timings/fresh_module_timings_effective.csv`. Each command emits a
unique initially absent target `.olean`/`.ilean`, records sizes and hashes,
and unlinks only those explicit temporary outputs. Imports remain cached.
These are fresh target-output timings with cached imports; percentiles describe
only this nonrandom 30-module sample. Details are in
[COMMANDS.md](timings/COMMANDS.md) and [SAMPLE_DESIGN.md](timings/SAMPLE_DESIGN.md).

## Proof hygiene and representative assumptions

Run the source lexer and compiled-environment classifier against the raw graph:

```bash
cd "$AUDIT_ROOT"
python3 hygiene/analyze_proof_hygiene.py
```

Run the predeclared external `#print axioms` probe and parse the unmodified
Lean diagnostic output:

```bash
cd "$WT"
/usr/bin/time -lp lake env lean \
  "$AUDIT_ROOT/hygiene/RepresentativeAxioms.lean" \
  > "$AUDIT_ROOT/hygiene/representative_axioms.log" \
  2> "$AUDIT_ROOT/hygiene/representative_axioms.time"
python3 "$AUDIT_ROOT/hygiene/parse_axiom_probe.py"
```

The source scan distinguishes code from comments and strings. The compiled
scan distinguishes constructors, inductives, recursors, generated
`native_decide` axioms, generated partial-recursion helpers, explicit unsafe
status, and direct `sorryAx` edges. `opaque` is never classified as a
placeholder merely because it is opaque. Exact formulas and inputs are in
[TIMINGS_AND_PROOF_HYGIENE.md](TIMINGS_AND_PROOF_HYGIENE.md).

## Dependency chains and figures

Representative chains must be regenerated from the current analyzer's unique
project edge tables, never from textual matches or shared imports. Every chain
edge is supported by the `source`, `target`, `occurs_in_type`, and
`occurs_in_body` columns of `current_graph/metrics/direct_project_dependencies.csv.gz`.
Run the frozen stratified selection and raw-row verifier from the audit root:

```bash
cd "$AUDIT_ROOT"
/usr/bin/time -l python3 current_graph/build_dependency_chains.py \
  --metrics current_graph/metrics/declaration_metrics.csv.gz \
  --edges current_graph/metrics/direct_project_dependencies.csv.gz \
  --compiled-raw-edges raw/direct_dependencies.csv.gz \
  --metadata raw/declaration_metadata.csv \
  --worktree _worktree \
  --source-commit "$AUDITED_COMMIT" \
  --output current_graph/chains \
  --top-level-report DEPENDENCY_CHAINS.md \
  > current_graph/chains_stdout.log \
  2> current_graph/chains_time_and_stderr.log
cmp -s DEPENDENCY_CHAINS.md current_graph/chains/DEPENDENCY_CHAINS.md
```

The script fails if a selected node or adjacent edge is absent, if any selected
processed edge differs from its exact compiled raw row, or if the commit is
not a full lowercase Git object ID. Its retained schema is
`numstability-representative-dependency-chains/1.1.0`; the final sample has 12
chains, 59 path edges, and 5 independent branch edges.

Generate the A4-readable vector figures from the layer/domain matrices and
verified chain tables:

```bash
cd "$AUDIT_ROOT"
python3 figures/generate_figures.py
shasum -a 256 -c figures/SHA256SUMS
```

Expected outputs are `figures/layer_dependency_diagram.svg`,
`figures/domain_dependency_heatmap.svg`, and
`figures/crosschapter_lu_solver_chain.svg`, plus the input/output hash manifest
`figures/manifest.json`. The generator is deterministic and uses only the
Python standard library. Full input hashes and rendering details are in
[README.md](figures/README.md).

The retained matching PNGs are convenience previews, not the canonical
figures. On macOS they were rendered from the SVGs with:

```bash
for figure in figures/*.svg; do
  sips -s format png "$figure" --out "${figure%.svg}.png"
done
```

PNG encoder metadata can vary across operating-system versions; validate the
canonical SVG hashes for cross-host reproduction.

The figure contract is: consumer-to-dependency edge orientation, explicit
arrow legend, no inference from imports, stable declaration names, readable
A4 dimensions, and matrices derived from unique elaborated declaration pairs.

## Validation sequence

Run these checks before accepting regenerated artifacts:

```bash
cd "$AUDIT_ROOT"

gzip -t raw/phase10a_exact_current.tsv.gz
gzip -t raw/declarations.csv.gz
gzip -t raw/direct_dependencies.csv.gz
gzip -t raw/module_imports.csv.gz
gzip -t current_graph/metrics/declaration_metrics.csv.gz
gzip -t current_graph/metrics/direct_project_dependencies.csv.gz
gzip -t current_graph/metrics/type_project_dependencies.csv.gz
gzip -t current_graph/metrics/body_project_dependencies.csv.gz
gzip -t current_graph/metrics/type_and_body_project_dependencies.csv.gz
gzip -t current_graph/metrics/weak_component_memberships.csv.gz
gzip -t current_graph/metrics/strong_component_memberships.csv.gz
gzip -t current_graph/metrics/source_written_component_memberships.csv.gz

python3 -m json.tool provenance/build_environment.json >/dev/null
python3 -m json.tool historical/PHASE10A_RECOVERY.json >/dev/null
python3 -m json.tool historical/phase10a_exact_current_summary.json >/dev/null
python3 -m json.tool static_architecture/summary.json >/dev/null
python3 -m json.tool current_graph/metrics/summary.json >/dev/null
python3 -m json.tool current_graph/metrics/incoming_and_cross_boundary_coverage_contract_summary.json >/dev/null
python3 -m json.tool current_graph/metrics/public_type_exposure_summary.json >/dev/null
python3 -m json.tool current_graph/metrics/reuse_leaders_by_universe_summary.json >/dev/null
python3 -m json.tool current_graph/metrics/source_written_components_summary.json >/dev/null
python3 -m json.tool current_graph/chains/summary.json >/dev/null
python3 -m json.tool current_graph/priority_review_metrics_compat.provenance.json >/dev/null
python3 -m json.tool current_graph/priority_reviews/summary.json >/dev/null
python3 -m json.tool probes/summary.json >/dev/null
python3 -m json.tool timings/timing_summary.json >/dev/null
python3 -m json.tool hygiene/proof_hygiene_summary.json >/dev/null
python3 -m json.tool figures/manifest.json >/dev/null

grep -H '^all_validations=PASS$' \
  current_graph/coverage_contract_validation.log \
  current_graph/public_type_exposure_validation.log \
  current_graph/reuse_leaders_validation.log \
  current_graph/source_written_components_validation.log

python3 -m unittest -v current_graph/test_analyze_current_graph.py
python3 tooling/current_audit/validate_markdown_links.py
git -C "$WT" rev-parse HEAD
git -C "$WT" status --porcelain=v1 --untracked-files=all
```

The graph test must pass seven tests. The link validator excludes only the
isolated worktree and exact recovered archival trees, ignores fenced code, and
must report zero unresolved current-report links. Its raw results are
`provenance/MARKDOWN_LINK_VALIDATION.csv` and
`provenance/MARKDOWN_LINK_VALIDATION.json`.

Validate the principal graph identities directly:

```bash
python3 - <<'PY'
import json
from pathlib import Path

s = json.loads(Path('current_graph/metrics/summary.json').read_text())
assert s['source_commit'] == '045daf28056a6e4358d5de7c22c7a9d7acc2e80e'
e = s['direct_project_graph']
assert e['type'] + e['body'] - e['both'] == e['all']
v = s['validation']
assert v['raw_project_pair_duplicates'] == 0
assert v['project_targets_missing_from_declaration_universe'] == 0
assert v['metadata_universe_exact_match'] is True
assert v['origin_universe_exact_match'] is True
assert v['two_reserved_extractors_agree'] is True
print('current_graph_invariants_ok=true')
PY
```

## Final deterministic checksums

Do not run this step while reports or figures are still being written. Once the
artifact tree is frozen, write and immediately verify its deterministic
manifest:

```bash
cd "$AUDIT_ROOT"
python3 tooling/current_audit/finalize_artifact_checksums.py write
python3 tooling/current_audit/finalize_artifact_checksums.py verify
```

The script hashes every regular non-symlink artifact in bytewise relative-path
order except:

- `_worktree/`;
- transient `probes/build/` and `probes/validation_output/` Lean objects;
- transient `timings/fresh_outputs/` objects;
- Python `__pycache__`/`.pyc` and `.DS_Store`; and
- `ARTIFACT_SHA256SUMS` plus its atomic temporary output, preventing recursive
  self-hashing.

An unexpected symlink outside the excluded tree is a hard error. Verification
detects missing, changed, and unlisted files. The final manifest should be
`ARTIFACT_SHA256SUMS`; it was intentionally not generated until all agents had
finished producing artifacts.

## Expected outputs

At minimum, a complete run contains:

- top-level `REPORT.md`, `metrics.json`, `DEPENDENCY_CHAINS.md`,
  `PUBLIC_API_CONSUMABILITY.md`, `ARCHITECTURE_REVIEW.md`,
  `HISTORICAL_COMPARISON.md`, `THESIS_EVIDENCE.md`, `REPRODUCE.md`, and
  `LIMITATIONS.md`;
- raw declarations, dependencies, type/body flags, imports, origins, metadata,
  and statement fingerprints under `raw/`;
- current declaration inventory, authorship, direct edge partitions,
  declaration/module metrics, components, coverage, matrices, reachability,
  leaves/isolates, depth/path, and reuse-leader tables under
  `current_graph/metrics/`;
- denominator-complete coverage-contract rows, complete 479-entry exposure,
  exhaustive direct public-type exposure, four-universe reuse rankings, and
  all-source-written weak/strong component artifacts plus their summaries and
  validation logs under `current_graph/`;
- exact-statement and direct-delegation review tables under
  `current_graph/priority_reviews/` and `metrics/exact_statement_groups/`;
- public client sources, logs, results, controls, and summary under `probes/`;
- fresh-target timing tables and logs under `timings/`;
- source/compiled proof-hygiene tables and representative axiom output under
  `hygiene/`;
- exact Phase 10A recovery, replay, hashes, and comparison inputs under
  `historical/`;
- a layer diagram, chapter/domain heatmap, and deep declaration-chain diagram
  under `figures/`; and
- `ARTIFACT_SHA256SUMS` after the tree is frozen.

The full command provenance is deliberately split by evidence family to keep
this file usable: build/environment commands are under `provenance/`, Phase
10A search/recovery commands under `historical/`, source/import commands under
`static_architecture/`, client commands under `probes/`, and timing/hygiene
commands under `timings/`. Together with this file and the per-row `command`
fields, they are the exhaustive command record.

## Interpretation boundary

Reproduction of these artifacts establishes only that the same programs over
the same source and compiled environment regenerate the recorded structural
evidence. Compilation establishes acceptance by the recorded Lean
environment, not faithfulness to Higham. A declaration edge establishes
formal reference and compositional typechecking, not mathematical-source
fidelity. Weak connectedness is not reuse. An import is not necessarily a
logical theorem dependency. A no-incoming declaration can be an intended
external endpoint. Generated declarations are not handwritten API. Direct and
transitive dependencies must remain separate, and successful sample clients
do not establish universal ease of use.
