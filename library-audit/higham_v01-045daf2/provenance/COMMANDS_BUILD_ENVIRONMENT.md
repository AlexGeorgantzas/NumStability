# Commands used for build/environment evidence

Working variables used below:

```bash
AUDIT_ROOT=<library-repo>/tmp/library_audit/higham_v01-045daf2
WT="$AUDIT_ROOT/_worktree"
```

The following commands describe the semantic commands executed for this slice
of the audit. Logging wrappers added timestamps and redirected stdout/stderr to
the raw artifact names recorded in `BUILD_AND_ENVIRONMENT.md`.

## Skill contract reads

```bash
sed -n '1,240p' <codex-home>/skills/numstability-library-reorganization/SKILL.md
sed -n '1,320p' <codex-home>/skills/numstability-library-reorganization/references/metric-contract.md
```

## Directory and Git preflight

```bash
mkdir -p "$AUDIT_ROOT/build" "$AUDIT_ROOT/provenance"
git -C "$WT" rev-parse --show-toplevel
git -C "$WT" rev-parse HEAD
git -C "$WT" rev-parse --verify refs/remotes/origin/higham_v01
git -C "$WT" rev-parse refs/heads/higham_v01
git -C "$WT" symbolic-ref -q --short HEAD
git -C "$WT" status --short --branch
git -C "$WT" status --porcelain=v1
git -C "$WT" worktree list --porcelain
git -C "$WT" show -s --format='commit=%H%ncommit_author_date=%aI%ncommit_committer_date=%cI%ncommit_subject=%s' HEAD
```

## Platform and toolchain

```bash
date -u '+%Y-%m-%dT%H:%M:%SZ'
TZ=Europe/Athens date '+%Y-%m-%dT%H:%M:%S%z %Z'
readlink /etc/localtime
uname -a
uname -s
uname -m
sw_vers
sysctl -n hw.logicalcpu
sysctl -n hw.physicalcpu
sysctl -n hw.memsize
command -v lake
lake --version
command -v lean
lean --version
lake env lean --version
command -v elan
elan --version
git -C "$WT/.lake/packages/mathlib" rev-parse HEAD
git -C "$WT/.lake/packages/mathlib" describe --tags --always --dirty
git -C "$WT/.lake/packages/mathlib" show -s --format='mathlib_commit_date=%cI%nmathlib_subject=%s' HEAD
shasum -a 256 "$WT/lean-toolchain" "$WT/lakefile.toml" "$WT/lake-manifest.json"
```

All package revisions were checked with the following loop:

```bash
for pkg in mathlib plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli; do
  git -C "$WT/.lake/packages/$pkg" rev-parse HEAD
done
jq -r '.packages[] | [.name, .rev] | @tsv' "$WT/lake-manifest.json"
```

## Aggregate and all-file discovery

```bash
sed -n '1,80p' "$WT/lean-toolchain"
sed -n '1,240p' "$WT/lakefile.toml"
sed -n '1,260p' "$WT/lake-manifest.json"
cd "$WT" && rg --files -uu -g '*.lean' | sort
cd "$WT" && rg --files -uu NumStability -g '*.lean' | wc -l
rg '^import ' "$WT/NumStability.lean"
rg '^import ' "$WT/NumStability/All.lean"
rg '^import ' "$WT/NumStability/Core.lean"
rg '^import ' "$WT/NumStability/FloatingPoint.lean"
rg '^import ' "$WT/NumStability/Analysis.lean"
rg '^import ' "$WT/NumStability/Algorithms.lean"
rg '^import ' "$WT/NumStability/Source.lean"
rg '^import ' "$WT/NumStability/Higham.lean"
```

## Setup and build commands

The first worktree had no `.lake` directory. Dependency setup was measured as:

```bash
cd "$WT"
/usr/bin/time -l -o "$AUDIT_ROOT/provenance/lake_update_time.log" \
  lake update \
  > "$AUDIT_ROOT/provenance/lake_update_stdout_stderr.log" 2>&1
```

Each full-build episode ran the same Lake command. Distinct metadata, output,
and timing files prevent the episodes from being conflated:

```bash
cd "$WT"
/usr/bin/time -l -o "$AUDIT_ROOT/build/full_build_time.log" \
  lake build \
  > "$AUDIT_ROOT/build/full_build_stdout_stderr.log" 2>&1

/usr/bin/time -l -o "$AUDIT_ROOT/build/full_build_fresh_cached_deps_time.log" \
  lake build \
  > "$AUDIT_ROOT/build/full_build_fresh_cached_deps_stdout_stderr.log" 2>&1

/usr/bin/time -l -o "$AUDIT_ROOT/build/full_build_cached_same_commit_time.log" \
  lake build \
  > "$AUDIT_ROOT/build/full_build_cached_same_commit_stdout_stderr.log" 2>&1
```

The first command was a fresh-output attempt ending in `ENOSPC`; the second was
a fresh-output attempt deliberately interrupted for capacity; the third was a
successful cached same-commit verification. See `build/build_attempts.csv` for
classification and timestamps.

## Storage and output diagnostics

```bash
df -h "$WT"
df -k "$WT"
du -sh "$WT/.lake" "$WT/.lake/packages" "$WT/.lake/build"
du -sh "$WT/.lake/packages"/* | sort -h
du -sh "$WT/.lake/build"/* | sort -h
du -sh "$WT/.lake/packages/mathlib"/* "$WT/.lake/packages/mathlib"/.[!.]* | sort -h
du -sh "$WT/.lake/packages/mathlib/.lake/build"/* | sort -h
find "$WT/.lake/build/lib/lean/NumStability" -type f -name '*.olean' | wc -l
find "$WT/.lake/build/lib/lean/NumStability" -type f -name '*.ilean' | wc -l
find "$WT/.lake/build" -type f | wc -l
wc -l "$AUDIT_ROOT/build/full_build_stdout_stderr.log"
tail -140 "$AUDIT_ROOT/build/full_build_stdout_stderr.log"
tail -140 "$AUDIT_ROOT/build/full_build_cached_same_commit_stdout_stderr.log"
rg -c '^[^[:alnum:]]*\[[0-9]+/[0-9]+\] Built ' "$AUDIT_ROOT/build/full_build_cached_same_commit_stdout_stderr.log"
rg -c '^[^[:alnum:]]*\[[0-9]+/[0-9]+\] Replayed ' "$AUDIT_ROOT/build/full_build_cached_same_commit_stdout_stderr.log"
```

No module-level timing command was run in this slice.
