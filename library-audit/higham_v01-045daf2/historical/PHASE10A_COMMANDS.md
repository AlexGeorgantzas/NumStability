# Phase 10A recovery command log

These are the shell commands executed by the Phase 10A recovery sub-audit, in
chronological groups. Multi-command tool invocations are expanded here. All
commands were read-only except directory creation, exact `git archive`
extraction below the ignored audit directory, creation of the three recovery
notes with `apply_patch`, and deletion of this sub-audit's own temporary
`<tmp>/numstability-phase10a-verify.Mjn7AQ` archive.

## Skill and contract inspection

```bash
sed -n '1,260p' <codex-home>/skills/numstability-library-reorganization/SKILL.md

wc -l <codex-home>/skills/numstability-library-reorganization/references/metric-contract.md <codex-home>/skills/numstability-library-reorganization/references/book-ownership-contract.md <codex-home>/skills/numstability-library-reorganization/references/architecture-contract.md
sed -n '1,320p' <codex-home>/skills/numstability-library-reorganization/references/metric-contract.md
sed -n '1,300p' <codex-home>/skills/numstability-library-reorganization/references/book-ownership-contract.md
sed -n '1,320p' <codex-home>/skills/numstability-library-reorganization/references/architecture-contract.md
```

## Repository and ref preflight

```bash
pwd
git rev-parse --show-toplevel
git status --short --branch
git branch -avv --no-abbrev
git worktree list --porcelain
git rev-parse origin/higham_v01
git rev-parse higham_v01 2>/dev/null || true
git show -s --format='%H%n%P%n%an <%ae>%n%aI%n%cn <%ce>%n%cI%n%s' origin/higham_v01
rg --files -uu | sed -n '1,260p'
```

## Filesystem and history discovery

The following five searches ran concurrently:

```bash
rg -n -uu --glob '!**/.lake/**' --glob '!**/.git/**' --glob '!paper_bencmark/**' '(56[, ]?187|56187|40[, ]?963|40963|8[, ]?371|8371|222[, ]?319|222319|Phase 10A|Phase10A|10A)' .

rg --files -uu | rg '(^|/)(tools/library_audit|tmp/library_audit|LIBRARY_REORGANIZATION|library_audit|audit)' | sed -n '1,1200p'

git log --all --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- tools/library_audit docs/LIBRARY_REORGANIZATION_STANDARDS.md docs/library_reorganization tmp/library_audit | sed -n '1,500p'

for ref in $(git for-each-ref --format='%(refname)' refs/heads refs/remotes); do
  if git ls-tree -r --name-only "$ref" | rg -q '^(tools/library_audit/|docs/LIBRARY_REORGANIZATION_STANDARDS\.md$)'; then
    printf '%s\t%s\n' "$ref" "$(git rev-parse "$ref")"
  fi
done

for d in <workspace>/* <codex-home>/worktrees/*/*; do
  [ -d "$d/.git" ] || [ -f "$d/.git" ] || continue
  printf '\nWORKTREE %s\n' "$d"
  (cd "$d" && git rev-parse HEAD && rg -n -uu --glob '!**/.lake/**' --glob '!**/.git/**' '(56[, ]?187|56187|40[, ]?963|40963|8[, ]?371|8371|222[, ]?319|222319|Phase 10A|Phase10A)' . 2>/dev/null | sed -n '1,160p')
done
```

```bash
git log --all --reverse --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- docs/architecture/baselines/2026-07-24-organization-phase10a.md docs/architecture/baselines/2026-07-24-organization-phase10a.json docs/architecture/baselines/2026-07-24-organization-phase10a-build.md docs/architecture/migrations/2026-07-24-higham-chapter14-section05-phase10.md tools/library_audit | sed -n '1,500p'
git log --all --follow --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- docs/architecture/baselines/2026-07-24-organization-phase10a.json | sed -n '1,200p'
git log --all -S'222319' --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- docs tools | sed -n '1,300p'

git show --stat --summary --format=fuller d21a4ed5b91008a8a5bc60741765f27fcdf86edf
git show --stat --summary --format=fuller 21e130ac8355de8ec1a74f22a73bf103e00bc48f
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/baselines/2026-07-24-organization-phase10a.json
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/baselines/2026-07-24-organization-phase10a.md
git show 21e130ac8355de8ec1a74f22a73bf103e00bc48f:docs/architecture/baselines/2026-07-24-organization-phase10a-build.md
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/migrations/2026-07-24-higham-chapter14-section05-phase10.md
```

```bash
find tmp/library_audit -maxdepth 4 -type f -print 2>/dev/null | sort | sed -n '1,2000p'
find <codex-home>/worktrees -path '*<tmp>/library_audit/*' -type f -print 2>/dev/null | sort | sed -n '1,1000p'
git ls-tree -r --name-only d21a4ed5b91008a8a5bc60741765f27fcdf86edf tools/library_audit
git ls-tree -r --name-only 899003baca0fdca2714344a69c10eef4b2d3c306 tools/library_audit
git ls-tree -r --name-only 21e130ac8355de8ec1a74f22a73bf103e00bc48f tools/library_audit
git ls-tree -r --name-only origin/main tools/library_audit

git log --all --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- tools/library_audit | sed -n '1,500p'
git log --all --name-status --format='COMMIT %H %ad %s' --date=iso-strict -- tools/library_audit | sed -n '1,1200p'
git rev-list --all --objects | rg 'tools/library_audit|DeclarationGraph|generate_baseline|analyze_graph|capture_baseline' | sed -n '1,1200p'

git log --all --full-history --simplify-merges --date=iso-strict --format='%H%x09%ad%x09%D%x09%s' -- tools/library_audit/DeclarationGraph.lean
git log --all --full-history --raw -- tools/library_audit/DeclarationGraph.lean | sed -n '1,500p'
git cat-file -t 81c553dae8a991877f9d0ebac9b2ba3b42542cd5
git cat-file -s 81c553dae8a991877f9d0ebac9b2ba3b42542cd5
git branch -a --contains $(git rev-list --all --objects | awk '$2=="tools/library_audit/DeclarationGraph.lean"{print $1}') 2>&1 || true
```

The final `git branch --contains` command intentionally received a blob rather
than a commit and failed; the failure helped identify that the tool lived in an
untracked-files stash parent.

```bash
git ls-tree -r --name-only d21a4ed5b91008a8a5bc60741765f27fcdf86edf tools/architecture | sort
git ls-tree -r --name-only 21e130ac8355de8ec1a74f22a73bf103e00bc48f tools/architecture | sort
git ls-tree -r --name-only 899003baca0fdca2714344a69c10eef4b2d3c306 tools/architecture | sort
git ls-tree -r --name-only 227f41ce0018596c154d07a00631e9984d7b4c27 tools/architecture | sort
git ls-tree -r d21a4ed5b91008a8a5bc60741765f27fcdf86edf tools/architecture | sed -n '1,500p'

git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/README.md
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/declaration_dependencies.lean
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/generate_baseline.py
```

```bash
rg --files -uu <library-repo> <codex-home>/worktrees 2>/dev/null | rg '(phase10a|phase-10a|dependencies\.tsv$|dependency.*\.tsv$|declaration.*\.tsv$|library_audit)' | sed -n '1,2500p'
find <home> -type f \( -name '*phase10a*' -o -name 'dependencies.tsv' -o -name '*dependency*.tsv' \) 2>/dev/null | sed -n '1,2500p'
```

## Exact archive recovery and hashing

```bash
mkdir -p <library-repo>/tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact
git archive d21a4ed5b91008a8a5bc60741765f27fcdf86edf tools/architecture docs/architecture/baselines/2026-07-24-organization-phase10a.json docs/architecture/baselines/2026-07-24-organization-phase10a.md docs/architecture/baselines/2026-07-24-organization-phase10a-build.md docs/architecture/migrations/2026-07-24-higham-chapter14-section05-phase10.md docs/architecture/tiers.json docs/architecture/layout-exceptions.json | tar -x -C <library-repo>/tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact
find <library-repo>/tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact -type f -print | sort

find tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact -type f -print0 | sort -z | xargs -0 shasum -a 256
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/generate_baseline.py | shasum -a 256
git show 899003baca0fdca2714344a69c10eef4b2d3c306:tools/architecture/generate_baseline.py | shasum -a 256
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/declaration_dependencies.lean | shasum -a 256
git show 899003baca0fdca2714344a69c10eef4b2d3c306:tools/architecture/declaration_dependencies.lean | shasum -a 256
git diff --no-index <(git show 899003baca0fdca2714344a69c10eef4b2d3c306:tools/architecture/generate_baseline.py) <(git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/generate_baseline.py) || true
git diff --no-index <(git show 899003baca0fdca2714344a69c10eef4b2d3c306:tools/architecture/declaration_dependencies.lean) <(git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/declaration_dependencies.lean) || true
```

```bash
mkdir -p tmp/library_audit/higham_v01-045daf2/historical/later_library_audit_stash
git archive 163a1134a6cadae7538fdb27859bfc25d9f00005 tools/library_audit | tar -x -C tmp/library_audit/higham_v01-045daf2/historical/later_library_audit_stash
find tmp/library_audit/higham_v01-045daf2/historical/later_library_audit_stash -type f -print | sort
find tmp/library_audit/higham_v01-045daf2/historical/later_library_audit_stash -type f -print0 | sort -z | xargs -0 shasum -a 256
git show -s --format='%H%n%P%n%aI%n%cI%n%s' 163a1134a6cadae7538fdb27859bfc25d9f00005
git show -s --format='%H%n%P%n%aI%n%cI%n%s' c80d8cfee02c85a7a306d8447cc4a77dc973e168
git stash list --date=iso-strict

git reflog show --date=iso-strict --format='%H%x09%gd%x09%gs' refs/stash
for c in $(git reflog show --format='%H' refs/stash); do
  printf '\nSTASH %s\n' "$c"
  git show -s --format='%H %P %cI %s' "$c"
  git ls-tree -r --name-only "$c" | rg '(library_audit|architecture|phase10a|dependencies\.tsv|benchmark-results)' | sed -n '1,500p'
done

for c in 698c08e9897941ee4d5b19e944a7ad49836d2b67 9a76b402435ea6802901c77713fa9f0d5ae80517 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d; do
  printf '\nOBJECT %s\n' "$c"
  git show -s --format='%H %P %cI %s' "$c"
  git ls-tree -r --name-only "$c" | sed -n '1,1000p'
done
```

```bash
mkdir -p tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0
git archive 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d tools/library_audit docs/LIBRARY_REORGANIZATION_BASELINE.md docs/LIBRARY_REORGANIZATION_PILOT.md docs/LIBRARY_REORGANIZATION_PLAN.md docs/LIBRARY_REORGANIZATION_STANDARDS.md docs/Report.md docs/numstability-import-graph.html | tar -x -C tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0
find tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0 -type f -print | sort
find tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0 -type f -print0 | sort -z | xargs -0 shasum -a 256
diff -qr tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit tmp/library_audit/higham_v01-045daf2/historical/later_library_audit_stash/tools/library_audit || true

mkdir -p tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit
git archive 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d tools/library_audit | tar -x -C tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit
find tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit -type f -print0 | sort -z | xargs -0 shasum -a 256
diff -qr tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit/tools/library_audit tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit || true
git status --short --ignored=matching -- tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit | sed -n '1,80p'
```

## Code, artifact, and schema inspection

```bash
jq '.' tmp/library_audit/2bb76d0/metrics/summary.json
jq '{schema_version,captured_at,git_commit,git_branch,git_status,library_source_status,lean_version,lake_version,lean_toolchain,mathlib_revision,file_statistics,full_build,module_compilation_timings}' tmp/library_audit/2bb76d0/baseline/baseline.json
sed -n '1,260p' tmp/library_audit/2bb76d0/REPORT.md
git show -s --format='%H%n%P%n%D%n%aI%n%cI%n%s' 2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19
git merge-base --is-ancestor d21a4ed5b91008a8a5bc60741765f27fcdf86edf 2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19
printf 'ancestor_rc=%s\n' $?

nl -ba tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py | sed -n '1,280p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py | sed -n '281,620p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py | sed -n '621,980p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py | sed -n '445,648p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/declaration_dependencies.lean | sed -n '1,240p'

nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/DeclarationGraph.lean | sed -n '1,260p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/analyze_graph.py | sed -n '1,360p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/analyze_graph.py | sed -n '361,760p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/test_analyze_graph.py | sed -n '1,420p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/analyze_graph.py | sed -n '212,360p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/capture_baseline.py | sed -n '1,420p'
nl -ba tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/tools/library_audit/README.md | sed -n '1,320p'
```

```bash
git merge-base d21a4ed5b91008a8a5bc60741765f27fcdf86edf 045daf28056a6e4358d5de7c22c7a9d7acc2e80e
git merge-base 2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19 045daf28056a6e4358d5de7c22c7a9d7acc2e80e
git log --graph --oneline --decorate --all --boundary --simplify-by-decoration | sed -n '1,250p'
git diff --shortstat d21a4ed5b91008a8a5bc60741765f27fcdf86edf 045daf28056a6e4358d5de7c22c7a9d7acc2e80e -- NumStability NumStability.lean
printf 'phase10a modules='
git ls-tree -r --name-only d21a4ed5b91008a8a5bc60741765f27fcdf86edf NumStability NumStability.lean | rg '\.lean$' | wc -l
printf 'higham modules='
git ls-tree -r --name-only 045daf28056a6e4358d5de7c22c7a9d7acc2e80e NumStability NumStability.lean | rg '\.lean$' | wc -l
git diff --name-status d21a4ed5b91008a8a5bc60741765f27fcdf86edf 045daf28056a6e4358d5de7c22c7a9d7acc2e80e -- NumStability NumStability.lean | sed -n '1,300p'

git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:lean-toolchain
git show 045daf28056a6e4358d5de7c22c7a9d7acc2e80e:lean-toolchain
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:lake-manifest.json | jq -r '.packages[] | select(.name=="mathlib") | [.rev,.inputRev] | @tsv'
git show 045daf28056a6e4358d5de7c22c7a9d7acc2e80e:lake-manifest.json | jq -r '.packages[] | select(.name=="mathlib") | [.rev,.inputRev] | @tsv'
git show d21a4ed5b91008a8a5bc60741765f27fcdf86edf:NumStability.lean | sed -n '1,80p'
git show 045daf28056a6e4358d5de7c22c7a9d7acc2e80e:NumStability.lean | sed -n '1,80p'
```

```bash
lean_prefix=$(lake env lean --print-prefix)
printf 'lean_prefix=%s\n' "$lean_prefix"
rg -n 'def isInternalDetail|def isInternal\b|isInternalDetail' "$lean_prefix/src/lean" "$lean_prefix/src" 2>/dev/null | sed -n '1,240p'
rg -n 'def value\?|value\? \(' "$lean_prefix/src/lean/Lean" 2>/dev/null | sed -n '1,240p'

lean_prefix=$(lake env lean --print-prefix)
nl -ba "$lean_prefix/src/lean/Lean/Data/Name.lean" | sed -n '105,165p'
nl -ba "$lean_prefix/src/lean/Lean/Declaration.lean" | sed -n '430,500p'
```

```bash
jq '.source | {module_count,line_count,nonblank_line_count,byte_count,direct_import_count,internal_direct_import_count,external_direct_import_count,unresolved_project_import_count,module_docstring_count,modules_missing_module_docstring_count,source_tree_sha256,source_tree_sha256_normalization,import_graph:(.import_graph|{edge_count,strong_component_count,cyclic_strong_component_count}),tier_audit:(.tier_audit|{classified_module_count,unclassified_module_count,classification_coverage_percentage,module_counts_by_tier,classified_import_edge_count,reusable_to_source_edge_count,reusable_to_mixed_edge_count,reusable_to_source_reachability_count,reusable_to_mixed_reachability_count,classification_complete,tier_separation_complete,physical_source_target_gate_satisfied})}' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json
jq 'keys, .source|keys' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json
```

## Independent source-digest replay

```bash
phase10_verify_dir=$(mktemp -d <tmp>/numstability-phase10a-verify.XXXXXX)
git archive d21a4ed5b91008a8a5bc60741765f27fcdf86edf NumStability NumStability.lean | tar -x -C "$phase10_verify_dir"
python3 - "$phase10_verify_dir" tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py <<'PY'
import importlib.util, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
tool = pathlib.Path(sys.argv[2])
spec = importlib.util.spec_from_file_location('phase10_generator', tool)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
summary, modules = module.scan_sources(root)
print(json.dumps({k: summary[k] for k in ('module_count','source_tree_sha256','line_count','nonblank_line_count','byte_count','direct_import_count','internal_direct_import_count','external_direct_import_count','unresolved_project_import_count')}, indent=2, sort_keys=True))
PY
printf 'temporary_verification_tree=%s\n' "$phase10_verify_dir"
```

The first cleanup attempt below was rejected by the command safety layer before
execution:

```bash
test -d <tmp>/numstability-phase10a-verify.Mjn7AQ && test "$(realpath <tmp>/numstability-phase10a-verify.Mjn7AQ)" = <tmp>/numstability-phase10a-verify.Mjn7AQ && rm -rf -- <tmp>/numstability-phase10a-verify.Mjn7AQ
test ! -e <tmp>/numstability-phase10a-verify.Mjn7AQ
printf 'cleanup_rc=%s\n' $?
```

The exact temporary tree was then safely removed:

```bash
test -d <tmp>/numstability-phase10a-verify.Mjn7AQ && find <tmp>/numstability-phase10a-verify.Mjn7AQ -depth -delete
test ! -e <tmp>/numstability-phase10a-verify.Mjn7AQ
df -h /tmp
```

## Additional provenance and raw-artifact searches

```bash
git show --stat --oneline 77c11767a202432214213e9f5dc8fdc8ef0b7beb
git show --stat --oneline 7590f571c2ec3656739ca1ef07430d03f8e082ad
git show --stat --oneline 115c7a0ffbe7bb5a741e7ed957d23605ddbb9f32
git diff d21a4ed5b91008a8a5bc60741765f27fcdf86edf 77c11767a202432214213e9f5dc8fdc8ef0b7beb -- tools/architecture/declaration_dependencies.lean tools/architecture/generate_baseline.py | sed -n '1,500p'
git diff 77c11767a202432214213e9f5dc8fdc8ef0b7beb 7590f571c2ec3656739ca1ef07430d03f8e082ad -- tools/architecture/declaration_dependencies.lean tools/architecture/generate_baseline.py | sed -n '1,400p'
git diff 7590f571c2ec3656739ca1ef07430d03f8e082ad 115c7a0ffbe7bb5a741e7ed957d23605ddbb9f32 -- tools/architecture/declaration_dependencies.lean tools/architecture/generate_baseline.py | sed -n '1,500p'

find <library-repo> <codex-home>/worktrees -type f -name '*.tsv' -print 2>/dev/null | rg '(depend|architect|phase10|baseline|NumStability|library_audit)' | sed -n '1,2000p'
find /tmp <tmp> -type f -name 'numstability-dependencies-*.tsv' -print 2>/dev/null | sed -n '1,500p'
git rev-list --all --objects | rg '(dependencies\.tsv|phase10a.*\.(tsv|csv)|declaration_dependencies)'
```

```bash
rg -n -uu --glob '!**/.lake/**' --glob '!**/.git/**' --glob '!paper_bencmark/**' '(organization-phase10a|phase10a|Phase 10A|222,319|222319|dependencies\.tsv|keep-dependency-tsv|generate_baseline\.py --no-build --check)' docs tmp/library_audit 2>/dev/null | sed -n '1,2500p'
git grep -n -I -e '222319' -e '222,319' -e 'generate_baseline.py --no-build --check' -e 'keep-dependency-tsv' $(git rev-list --all | head -n 1) -- 2>/dev/null | sed -n '1,500p'
```

```bash
for c in 899003baca0fdca2714344a69c10eef4b2d3c306 d21a4ed5b91008a8a5bc60741765f27fcdf86edf 21e130ac8355de8ec1a74f22a73bf103e00bc48f; do
  printf '\nCOMMIT %s\n' "$c"
  git show -s --format='%H%n%P%n%aI%n%cI%n%s' "$c"
  git ls-tree -r "$c" tools/architecture/generate_baseline.py tools/architecture/declaration_dependencies.lean docs/architecture/baselines/2026-07-24-organization-phase10a.json docs/architecture/baselines/2026-07-24-organization-phase10a.md docs/architecture/baselines/2026-07-24-organization-phase10a-build.md
done
git diff --stat d21a4ed5b91008a8a5bc60741765f27fcdf86edf 21e130ac8355de8ec1a74f22a73bf103e00bc48f
git diff d21a4ed5b91008a8a5bc60741765f27fcdf86edf 21e130ac8355de8ec1a74f22a73bf103e00bc48f -- docs/architecture/baselines/2026-07-24-organization-phase10a-build.md | sed -n '1,300p'

git log --all --full-history --follow --date=iso-strict --format='%H%x09%ad%x09%s' -- tools/architecture/generate_baseline.py
git log --all --full-history --follow --date=iso-strict --format='%H%x09%ad%x09%s' -- tools/architecture/declaration_dependencies.lean
git log --all --full-history --follow --name-status --format='COMMIT %H %ad %s' --date=iso-strict -- tools/architecture/generate_baseline.py | sed -n '1,500p'
git cat-file -p 7dd991e1eae443556d860c9e8063ac516f6322f2 | shasum -a 256
git cat-file -p f13fc5f12a502f0b87544650f777bf7353223c9d | shasum -a 256
```

```bash
sed -n '1,320p' tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/docs/LIBRARY_REORGANIZATION_BASELINE.md
sed -n '1,360p' tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/docs/LIBRARY_REORGANIZATION_STANDARDS.md
sed -n '1,280p' tmp/library_audit/higham_v01-045daf2/historical/library_audit_2bb76d0/docs/LIBRARY_REORGANIZATION_PILOT.md
```

## Validation-note extraction, checksums, tests, and host metadata

The first attempt to create the clean-validation archive failed with `No space
left on device` before a file was written:

```bash
mkdir -p tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e
git archive 21e130ac8355de8ec1a74f22a73bf103e00bc48f docs/architecture/baselines/2026-07-24-organization-phase10a-build.md | tar -x -C tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e
find tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e -type f -print0 | xargs -0 shasum -a 256
```

Disk diagnostics and the successful retry were:

```bash
df -h . /tmp
du -sh tmp/library_audit/higham_v01-045daf2/* 2>/dev/null | sort -h
du -sh tmp/library_audit/higham_v01-045daf2/_worktree/.lake 2>/dev/null
du -sh <tmp>/numstability-phase10a-verify.Mjn7AQ 2>/dev/null || true

mkdir -p tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e
git archive 21e130ac8355de8ec1a74f22a73bf103e00bc48f docs/architecture/baselines/2026-07-24-organization-phase10a-build.md | tar -x -C tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e
find tmp/library_audit/higham_v01-045daf2/historical/phase10a_validation_21e -type f -print0 | xargs -0 shasum -a 256
df -h .
```

```bash
for spec in 'd21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/baselines/2026-07-24-organization-phase10a.json' 'd21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/baselines/2026-07-24-organization-phase10a.md' 'd21a4ed5b91008a8a5bc60741765f27fcdf86edf:docs/architecture/baselines/2026-07-24-organization-phase10a-build.md' '21e130ac8355de8ec1a74f22a73bf103e00bc48f:docs/architecture/baselines/2026-07-24-organization-phase10a-build.md' 'd21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/generate_baseline.py' 'd21a4ed5b91008a8a5bc60741765f27fcdf86edf:tools/architecture/declaration_dependencies.lean'; do
  printf '%s\t' "$spec"
  git show "$spec" | shasum -a 256 | awk '{print $1}'
done
git show 21e130ac8355de8ec1a74f22a73bf103e00bc48f:docs/architecture/baselines/2026-07-24-organization-phase10a-build.md | wc -c
```

```bash
printf 'PHASE10A\n'
git ls-tree -r d21a4ed5b91008a8a5bc60741765f27fcdf86edf tools/architecture docs/architecture/baselines/2026-07-24-organization-phase10a.json docs/architecture/baselines/2026-07-24-organization-phase10a.md docs/architecture/baselines/2026-07-24-organization-phase10a-build.md docs/architecture/migrations/2026-07-24-higham-chapter14-section05-phase10.md docs/architecture/tiers.json docs/architecture/layout-exceptions.json | sort -k4
printf 'CLEAN_VALIDATION\n'
git ls-tree -r 21e130ac8355de8ec1a74f22a73bf103e00bc48f docs/architecture/baselines/2026-07-24-organization-phase10a-build.md
printf 'LIBRARY_AUDIT_STASH\n'
git ls-tree -r 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d tools/library_audit | sort -k4
printf 'STANDARDS_STASH\n'
git ls-tree -r 8f9125c74f0cf3d3a5ed28f2f8b7774a84b6478d docs/LIBRARY_REORGANIZATION_BASELINE.md docs/LIBRARY_REORGANIZATION_PILOT.md docs/LIBRARY_REORGANIZATION_PLAN.md docs/LIBRARY_REORGANIZATION_STANDARDS.md | sort -k4

PYTHONDONTWRITEBYTECODE=1 python3 tmp/library_audit/higham_v01-045daf2/historical/recovered_library_audit/tools/library_audit/test_analyze_graph.py

python3 - <<'PY'
print(round(100*222319/491557, 3))
PY
jq empty tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json
printf 'jq_rc=%s\n' $?
```

The GNU-style date command was attempted first and failed on BSD/macOS `date`:

```bash
date --iso-8601=seconds
date -u --iso-8601=seconds
uname -a
git status --short --branch
git rev-parse HEAD
git rev-parse origin/higham_v01
git rev-parse higham_v01
```

The portable retry was:

```bash
date -Iseconds
date -u -Iseconds
/usr/bin/sw_vers
uname -m
```

Finally, the generated inventory was inspected with:

```bash
wc -l tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY_CHECKSUMS.csv
sed -n '1,6p' tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY_CHECKSUMS.csv
tail -n 6 tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY_CHECKSUMS.csv
```

The recorded SHA-256 inventory was then verified against every recovered file:

```bash
python3 - <<'PY'
import csv, hashlib, pathlib, sys
base=pathlib.Path('tmp/library_audit/higham_v01-045daf2/historical')
collection_root={
 'phase10a_exact':base/'phase10a_exact',
 'phase10a_clean_validation':base/'phase10a_validation_21e',
 'recovered_library_audit':base/'recovered_library_audit',
 'reorganization_docs':base/'library_audit_2bb76d0',
}
ok=True
with (base/'PHASE10A_RECOVERY_CHECKSUMS.csv').open(newline='') as f:
 for row in csv.DictReader(f):
  p=collection_root[row['collection']]/row['relative_path']
  if not p.is_file():
   print('MISSING',p); ok=False; continue
  actual=hashlib.sha256(p.read_bytes()).hexdigest()
  if actual != row['sha256']:
   print('MISMATCH',p,actual,row['sha256']); ok=False
print('checksum_inventory_ok=' + str(ok).lower())
sys.exit(0 if ok else 1)
PY
```

## Exact Phase 10A-schema replay summary for `045daf2...`

The current extractor was not rerun during this recovery step. The already
retained compressed raw TSV was first inspected and integrity-checked:

```bash
sed -n '1,260p' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py
sed -n '1,260p' tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.md
df -h . /tmp
ls -lh tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py

rg -n "def summarize_declaration_tsv|return \\{|declaration_tsv" tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py | head -40
sed -n '430,720p' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py
gzip -t tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz
shasum -a 256 tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py

sed -n '649,790p' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py
ls -lh tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.*
rg -n "phase10a_exact_current|summariz" tmp/library_audit/higham_v01-045daf2 -g '*.md' -g '*.json' -g '*.log'
```

The exact recovered `summarize_declaration_tsv` function was imported and
called without modification. A FIFO kept the 124,996,640-byte decompressed TSV
off disk. This timed run printed the literal summary to standard output:

```bash
set -euo pipefail
audit_stream_dir=$(mktemp -d <tmp>/phase10a-summary.XXXXXX)
audit_fifo="$audit_stream_dir/current.tsv"
mkfifo "$audit_fifo"
gzip -dc tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz > "$audit_fifo" &
audit_gzip_pid=$!
/usr/bin/time -p python3 -c 'import importlib.util,json,sys; from pathlib import Path; p=Path(sys.argv[1]); mpath=Path(sys.argv[2]); spec=importlib.util.spec_from_file_location("phase10a_exact_generate_baseline",mpath); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); print(json.dumps(m.summarize_declaration_tsv(p),indent=2,sort_keys=True))' "$audit_fifo" tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/tools/architecture/generate_baseline.py
wait "$audit_gzip_pid"
find "$audit_stream_dir" -depth -delete
```

The same block was run once more without `/usr/bin/time -p`; Codex captured its
standard output and materialized it byte-for-byte using `apply_patch` as
`historical/phase10a_exact_current_summary.json`. No summarizer or extractor
source was edited. The generated result was checked as follows:

```bash
python3 -m json.tool tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json >/dev/null
wc -c -l tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json
shasum -a 256 tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz
python3 - <<'PY'
import json
from pathlib import Path
p=Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json')
d=json.loads(p.read_text())
print(json.dumps({k:d[k] for k in ('declaration_count','module_count','visibility_counts','kind_counts','edge_counts','graph_metrics')},indent=2,sort_keys=True))
PY
```

Uncompressed integrity, row/byte accounting, nearby extraction evidence, and
denominator-aware ratios were obtained with:

```bash
gzip -dc tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz | shasum -a 256
gzip -dc tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz | wc -lc
find tmp/library_audit/higham_v01-045daf2/raw -maxdepth 1 -type f -name 'phase10a_exact_current*' -exec ls -lh {} \\;
find tmp/library_audit/higham_v01-045daf2/raw -maxdepth 1 -type f -name 'phase10a_exact_current*' -exec shasum -a 256 {} \\;
python3 - <<'PY'
import json
from pathlib import Path
op=Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json')
np=Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json')
o=json.loads(op.read_text())['declarations']; n=json.loads(np.read_text())
def pct(a,b): return 100*a/b
print('public share',pct(o['visibility_counts']['public'],o['declaration_count']),pct(n['visibility_counts']['public'],n['declaration_count']))
print('cross union fraction',pct(o['edge_counts']['cross_module_union'],o['edge_counts']['union']),pct(n['edge_counts']['cross_module_union'],n['edge_counts']['union']))
print('mean declarations/module',o['declaration_count']/o['module_count'],n['declaration_count']/n['module_count'])
for k in ['apparent_leaves_all','project_foundational_all','project_isolated_all']:
 print(k,pct(o['graph_metrics'][k],o['declaration_count']),pct(n['graph_metrics'][k],n['declaration_count']))
print('public isolate frac',pct(o['graph_metrics']['project_isolated_public'],o['visibility_counts']['public']),pct(n['graph_metrics']['project_isolated_public'],n['visibility_counts']['public']))
PY

ls -lah tmp/library_audit/higham_v01-045daf2/raw | sed -n '1,120p'
rg -n "phase10a|77246|283049|409855|045daf" tmp/library_audit/higham_v01-045daf2/raw -g '*.log' -g '*.txt' -g '*.time' -g '*.json'
sed -n '1,200p' tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_extraction.time
shasum -a 256 tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_extraction.log tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_extraction.time
stat -f '%N|%z bytes|mtime=%Sm' -t '%Y-%m-%dT%H:%M:%S%z' tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_current.tsv.gz tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_extraction.log tmp/library_audit/higham_v01-045daf2/raw/phase10a_exact_extraction.time tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json
```

The complete old object and exact deltas were inspected with two Python
read-only scripts; their substantive formulas and outputs are incorporated in
`PHASE10A_RECOVERY.md` and `PHASE10A_RECOVERY.json`:

```bash
find tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact -type f -maxdepth 6 -print | sort
find tmp/library_audit/higham_v01-045daf2/historical -maxdepth 2 -type f -name '*.json' -print | sort
rg -n '81950|56187|491557|222319' tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact -g '*.json' -g '*.md'
python3 - <<'PY'
import json
from pathlib import Path
old=json.loads(Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json').read_text())['declarations']
new=json.loads(Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json').read_text())
print(json.dumps(old, indent=2, sort_keys=True))
print('\nDELTA TABLE')
for group in ['visibility_counts','kind_counts','edge_counts','graph_metrics']:
  for k in sorted(set(old.get(group,{})) | set(new.get(group,{}))):
    ov=old.get(group,{}).get(k)
    nv=new.get(group,{}).get(k)
    if isinstance(ov,(int,float)) and isinstance(nv,(int,float)):
      delta=nv-ov
      pct=(delta/ov*100) if ov else None
      print(group,k,ov,nv,delta,None if pct is None else round(pct,3),sep='\t')
for k in ['declaration_count','module_count']:
  ov=old[k]; nv=new[k]; delta=nv-ov; pct=delta/ov*100
  print('top',k,ov,nv,delta,round(pct,3),sep='\t')
PY

tail -120 tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_COMMANDS.md
sed -n '240,360p' tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.md
cat tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json

shasum -a 256 tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json
python3 - <<'PY'
import json
from pathlib import Path
o=json.loads(Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact/docs/architecture/baselines/2026-07-24-organization-phase10a.json').read_text())['declarations']
n=json.loads(Path('tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json').read_text())
rows=[
('Declaration nodes',o['declaration_count'],n['declaration_count']),
('Declaration-bearing modules',o['module_count'],n['module_count']),
('Environment-public nodes',o['visibility_counts']['public'],n['visibility_counts']['public']),
('Private nodes',o['visibility_counts']['private'],n['visibility_counts']['private']),
('Internal-detail nodes',o['visibility_counts']['internal'],n['visibility_counts']['internal']),
('Signature edges',o['edge_counts']['signature'],n['edge_counts']['signature']),
('Body/proof edges',o['edge_counts']['body_or_proof'],n['edge_counts']['body_or_proof']),
('Union edges',o['edge_counts']['union'],n['edge_counts']['union']),
('Cross-module union edges',o['edge_counts']['cross_module_union'],n['edge_counts']['cross_module_union']),
('Public with incoming edge',o['graph_metrics']['public_referenced_somewhere'],n['graph_metrics']['public_referenced_somewhere']),
('Public used from another module',o['graph_metrics']['public_referenced_from_another_module'],n['graph_metrics']['public_referenced_from_another_module']),
('All-decl largest weak component',o['graph_metrics']['largest_weak_component_all'],n['graph_metrics']['largest_weak_component_all']),
('Public-induced largest weak component',o['graph_metrics']['largest_weak_component_public'],n['graph_metrics']['largest_weak_component_public']),
('All isolates',o['graph_metrics']['project_isolated_all'],n['graph_metrics']['project_isolated_all']),
('Public isolates',o['graph_metrics']['project_isolated_public'],n['graph_metrics']['project_isolated_public']),
]
for label,a,b in rows:
 print(f'| {label} | {a:,} | {b:,} | {b-a:+,} | {(b-a)/a*100:+.3f}% |')
PY
```

The final artifact validations, executed after note generation, were:

```bash
python3 -m json.tool tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json >/dev/null
python3 -m json.tool tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json >/dev/null
rg -n "not yet valid|status_before_exact_current_replay|necessary current-side" tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.md tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json
shasum -a 256 tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.md tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_COMMANDS.md tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json
git status --short --branch
```

After adding the compact current-replay checksum manifest, its retained and
logical-stream entries and the final JSON were validated with:

```bash
python3 - <<'PY'
import csv, gzip, hashlib
from pathlib import Path
base=Path('tmp/library_audit/higham_v01-045daf2/historical')
rows=list(csv.DictReader((base/'PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv').open(newline='')))
for row in rows:
    expected_size=int(row['bytes'])
    expected_hash=row['sha256']
    if row['representation']=='uncompressed_logical_stream':
        stream=gzip.open(base/'../raw/phase10a_exact_current.tsv.gz','rb')
    else:
        stream=(base/row['artifact']).open('rb')
    digest=hashlib.sha256(); size=0
    with stream:
        while chunk:=stream.read(1024*1024):
            digest.update(chunk); size+=len(chunk)
    assert size==expected_size,(row['artifact'],size,expected_size)
    assert digest.hexdigest()==expected_hash,(row['artifact'],digest.hexdigest(),expected_hash)
print('current_replay_checksum_manifest_ok=true')
PY
python3 -m json.tool tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json >/dev/null
python3 -m json.tool tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json >/dev/null
shasum -a 256 tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.md tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_RECOVERY.json tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_COMMANDS.md tmp/library_audit/higham_v01-045daf2/historical/PHASE10A_CURRENT_REPLAY_CHECKSUMS.csv tmp/library_audit/higham_v01-045daf2/historical/phase10a_exact_current_summary.json
git status --short --branch
```
