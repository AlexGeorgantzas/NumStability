# Static architecture audit command record

All paths below are absolute to remove ambiguity. These commands are read-only
with respect to the audited worktree. The analyzer writes only to the ignored
artifact directory outside the isolated worktree.

## Commit and environment checks

```bash
cd <library-repo>/tmp/library_audit/higham_v01-045daf2/_worktree
git rev-parse --show-toplevel
git rev-parse HEAD
git rev-parse 'HEAD^{tree}'
git rev-parse higham_v01
git rev-parse origin/higham_v01
git status --porcelain=v1
git status --short --branch
git branch -vv
git remote -v
date -Iseconds
uname -a
uname -m
sw_vers
python3 --version
```

## Ignored-inclusive discovery and static scope checks

```bash
cd <library-repo>/tmp/library_audit/higham_v01-045daf2/_worktree
rg --files -uu
rg --files -uu NumStability | rg '\.lean$'
git ls-files NumStability | rg '\.lean$'
find NumStability -type d | sort
find NumStability/Source/Higham -maxdepth 1 -type f -name 'Chapter*.lean' -print | sort
wc -l NumStability.lean $(find NumStability -type f -name '*.lean' | sort)
```

The tracked-file and ignored-inclusive lists each contained the same 2,838
files below `NumStability/`; adding `NumStability.lean` gives the 2,839-module
static universe. The broad `rg --files -uu` discovery was also used to locate
audit/history material, but no prior numerical results were inputs to this
snapshot.

## Final analyzer invocation

```bash
python3 \
  <library-repo>/tmp/library_audit/higham_v01-045daf2/static_architecture/static_architecture.py \
  --root <library-repo>/tmp/library_audit/higham_v01-045daf2/_worktree \
  --output <library-repo>/tmp/library_audit/higham_v01-045daf2/static_architecture
```

The final analyzer completed at `2026-09-03T11:29:27+03:00`. Its embedded
small-example validations are in `validation.json`. The command is idempotent:
it replaces the generated CSV/JSON files with measurements of the supplied
root and does not use `.olean` files or build caches.

## Evidence inspections used for the narrative

```bash
sed -n '1,190p' NumStability/Algorithms.lean
sed -n '1,160p' NumStability/Analysis.lean
sed -n '1,80p' NumStability/FloatingPoint.lean
sed -n '1,90p' NumStability/Source.lean
sed -n '1,100p' NumStability/Source/Higham.lean
sed -n '1,30p' NumStability/All.lean
sed -n '1,30p' NumStability.lean
rg -n '^import NumStability\.Source' NumStability/Algorithms.lean
rg -n '^import NumStability\.(Algorithms|Source)' NumStability/Analysis.lean
nl -ba NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/HessenbergSchur/All.lean
nl -ba NumStability/Source/Higham/Chapter04/Equation10/Neumaier/AdaptiveBound.lean
nl -ba NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AutomaticBounds/All.lean
```

All additional tabulations quoted in `STATIC_ARCHITECTURE.md` are sums,
counts, nearest-rank percentiles, or filtered rows computed by the analyzer and
stored in `summary.json` or the cited CSV. No textual import match is used as a
logical declaration-dependency claim.

## Hash checks

```bash
cd <library-repo>/tmp/library_audit/higham_v01-045daf2/static_architecture
sha256sum static_architecture.py summary.json validation.json modules.csv source_imports.csv
find . -maxdepth 1 -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum
```

