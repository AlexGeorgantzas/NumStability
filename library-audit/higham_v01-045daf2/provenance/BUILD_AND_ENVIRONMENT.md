# Build and environment provenance

## Scope and classification

This file records the environment and full-build evidence for the read-only
audit of `origin/higham_v01`.  The audited source commit is
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`.

The build evidence has two distinct conclusions:

1. A genuinely fresh full compilation was attempted twice but did not
   complete because the host lacked enough free storage for a second complete
   NumStability output tree.  The first attempt ended with `ENOSPC`; the second
   was deliberately stopped before exhausting the volume.  Neither attempt
   exposed a Lean elaboration/typechecking error before termination.
2. A `lake build` verification over APFS-cloned, same-commit cached outputs
   completed successfully with exit status 0.  Its 2.80 s timing is **cached
   same-commit verification time**, not clean or incremental compilation time.

Accordingly, this audit may say that the same-commit cached full build is
accepted by Lake, but it must not report a successful fresh full-build time.

## Git state

- Isolated worktree HEAD: `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`
- Worktree state: detached HEAD
- Local `higham_v01`: `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`
- `origin/higham_v01`: `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`
- Local/remote agreement: yes
- Commit subject: `Fix final NumStability build failures`
- Commit author and committer timestamp: `2026-08-28T17:26:56+03:00`
- Source status before each build episode: clean (`git status --short --branch`
  printed only `## HEAD (no branch)`)
- Source status after each terminated/successful build episode: clean

The initial reference resolution was captured at
`2026-09-03T11:07:13+03:00`; the final environment/reference snapshot was
captured at `2026-09-03T11:19:42+03:00 EEST` (`Europe/Athens`).

## Toolchain and platform

- OS: macOS 26.5.2, build 25F84
- Kernel: Darwin 25.5.0
- Architecture: arm64
- CPU: 8 logical / 8 physical cores
- RAM: 17,179,869,184 bytes (16 GiB)
- Lean toolchain declaration: `leanprover/lean4:v4.29.0-rc3`
- Lean: 4.29.0-rc3, commit
  `5d86aa4032284a5242470e95fbe25f1ff506763d`,
  `arm64-apple-darwin24.6.0`, Release
- Lake: `5.0.0-src+5d86aa4` (Lean 4.29.0-rc3)
- Elan: 4.2.0, commit prefix `861dbdae2`
- Mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
  (`git describe`: `v4.29.0-rc3-80-ge8ea1afc32`)
- Mathlib commit timestamp: `2026-03-03T09:28:55+00:00`

Pinned input hashes:

| File | SHA-256 |
| --- | --- |
| `lean-toolchain` | `fdf7ccfe204caff50fab1913b9f13a763be5384e87d14555c9fdcb2be2b9f7f8` |
| `lakefile.toml` | `a4c00f6534596883069d57bbe529adb6bb5b295019eb32b8d4c2fb6a34c021ce` |
| `lake-manifest.json` | `ccfe8a72d6d227aebfe4e58575ddf2a2aef03b795052f97b770c36f684cc5774` |

All nine dependency repositories in `lake-manifest.json` were checked at
their exact pinned revisions, with zero mismatches. The machine-readable list
is `package_revision_validation.csv`; the original preflight is in
`recreated_worktree_preflight.log`.

## Aggregate/root modules

`lakefile.toml` declares `defaultTargets = ["NumStability"]`.  The exact
top-level import chain used by `lake build` is:

```text
NumStability                     (NumStability.lean)
  -> NumStability.All            (NumStability/All.lean)
       -> NumStability.Algorithms
       -> NumStability.Analysis
       -> NumStability.FloatingPoint
       -> NumStability.Source
```

The arrow above means source-module import, not a declaration dependency.
`NumStability.Source` imports `NumStability.Source.Higham`.
`NumStability.Higham` is a compatibility aggregate that also imports
`NumStability.Source.Higham`; it is not a direct import of `NumStability.All`.
`NumStability.Core` is a narrower reusable-foundations entry point and is not
the Lake default target.  The exact direct-import lists for all of these
aggregates are in `final_environment_and_refs.log` and
`environment_and_roots_raw.log`.

The source snapshot contains 2,838 `.lean` files under `NumStability/` plus
the root `NumStability.lean` file (2,839 total project library source files).

## Build episodes

### Dependency materialization for the first fresh attempt

The first isolated worktree began with no `.lake` directory.  `lake update`
was run once against the committed manifest.  It cloned/checkouted the pinned
dependencies and ran Mathlib's post-update cache hook (8,030 files
decompressed).  It exited 0 and left the project-specific `.lake/build`
absent and Git status clean.

- Start: `2026-09-03T08:07:51Z`
- End: `2026-09-03T08:11:56Z`
- `/usr/bin/time -l`: 245.71 s real, 82.76 s user, 37.45 s sys
- Maximum resident set size: 817,496,064 bytes

This setup time is network/cache materialization time, not NumStability
compilation time.  The task-created dependency copy was later removed only by
recreating the clean temporary worktree, after its 6.7 GiB size caused the
volume to fill.  No user source file was removed.

### Fresh attempt 1: terminated by `ENOSPC`

- Command: `lake build`
- Classification: fresh NumStability outputs; the project `.lake/build` was
  absent at start; dependencies had just been materialized from the pinned
  manifest/cache
- Start: `2026-09-03T08:12:21Z`
- End: `2026-09-03T08:14:02Z`
- Exit status: 1
- Terminal cause: host error 28, `no space left on device`, while writing
  `.olean`/`.ilean`/IR output files
- Partial outputs observed: 61 project `.olean` and 61 `.ilean` files
- Git status after failure: clean
- Timing: `/usr/bin/time` could not write its final record after the volume
  filled; the timestamp interval to failure was approximately 101 seconds and
  is not a compilation benchmark

At the failure snapshot the isolated `.lake` occupied 6.8 GiB: 6.7 GiB of
dependencies (6.4 GiB Mathlib) and 107 MiB of partial project output.  The data
volume had 184 MiB available.  Errors in the log are filesystem write errors,
not failed Lean goals.

### Fresh attempt 2: capacity-stopped

The worktree was recreated.  `.lake/packages` was a symlink to a preinstalled
dependency cache whose nine repository revisions match the committed manifest;
the project `.lake/build` was absent.

- Command: `lake build`
- Classification: fresh NumStability outputs with cached/prebuilt locked
  dependencies
- Start: `2026-09-03T08:17:06Z`
- End: `2026-09-03T08:17:23Z`
- Exit status: 130 (deliberately interrupted)
- Reason: a known same-commit output tree is approximately 8.2 GiB while only
  about 7.1 GiB was available; the run was stopped before another `ENOSPC`
- Partial outputs observed: 16 project `.olean` and 16 `.ilean` files
- `/usr/bin/time -l`: 17.49 s real, 30.97 s user, 21.68 s sys
- Maximum resident set size: 3,001,548,800 bytes
- Git status after interruption: clean

This is an incomplete run and its timing is not a clean compilation time.

### Cached same-commit full-build verification

The clean worktree was recreated again.  The caller's complete `.lake/build`
was APFS-cloned copy-on-write after the caller and isolated worktree were
verified at the same commit and toolchain/manifest.  This avoids using outputs
from another branch while consuming only a small amount of additional physical
storage.

- Command: `lake build`
- Classification: **cached same-commit full build**
- Start: `2026-09-03T08:18:35Z`
- End: `2026-09-03T08:18:37Z`
- Exit status: 0
- `/usr/bin/time -l`: 2.80 s real, 1.94 s user, 2.47 s sys
- Maximum resident set size: 741,163,008 bytes
- Build-log classification: 0 `Built` records, 160 `Replayed` warning records,
  0 error/failure records
- Available-space decrease during command: 644 KiB
- Output inventory after command: 2,866 `.olean` and 2,866 `.ilean` files
  under the NumStability build-output prefix (this inventory can include stale
  files not reached by the current root and is not a source-module count)
- Git status after build: clean

The replayed output consists of cached linter/information messages.  The exit-0
result is evidence that Lake regarded the same-commit target graph as complete
and current.  It is not an independently fresh re-elaboration of every module.

## Publication-safe interpretation

Safe statement: "At commit `045daf28056a6e4358d5de7c22c7a9d7acc2e80e`,
an isolated `lake build` over same-commit cached outputs completed successfully;
fresh rebuild attempts were infrastructure-limited by available disk space and
did not reach a Lean error before termination."

Unsafe statements include "the library clean-built in 2.80 seconds" and "the
fresh full build succeeded."  A successful compilation, cached or fresh,
establishes acceptance by the recorded Lean environment; it does not establish
faithfulness to Higham's source mathematics.

## Raw evidence

- `preflight_raw.log`: initial commit/ref/status/platform and manifest capture
- `environment_and_roots_raw.log`: version output, aggregate source, and
  `rg --files -uu` discovery
- `lake_update_{metadata,stdout_stderr,time}.log`: first dependency setup
- `disk_failure_snapshot.log`: `ENOSPC` capacity snapshot
- `storage_breakdown.log`: dependency/project output size evidence
- `build/full_build_{metadata,stdout_stderr,time}.log`: fresh attempt 1
- `build/full_build_fresh_cached_deps_*`: fresh attempt 2
- `cached_same_commit_preflight.log`: cached-run preflight
- `build/full_build_cached_same_commit_*`: successful cached verification
- `final_environment_and_refs.log`: final refs, versions, hashes, aggregate
  imports, and clean status
- `package_revision_validation.csv`: manifest-versus-checkout dependency
  revision validation (nine matches, zero mismatches)
