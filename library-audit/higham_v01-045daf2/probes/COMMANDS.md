# Public API probe command record

All Lean commands ran with working directory:

`<library-repo>/tmp/library_audit/higham_v01-045daf2/_worktree`

## Environment and source checks

```sh
git rev-parse HEAD
git status --short
lake --version
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
date '+%Y-%m-%dT%H:%M:%S%z %Z'
uname -a
rg --files -uu NumStability
sed -n '1,320p' docs/LibraryLookupChecks.lean
sed -n '1,260p' docs/LIBRARY_LOOKUP.md
rg -n '^(def|abbrev|structure|class|theorem|lemma|opaque|axiom)' NumStability
gzip -t ../raw/declarations.csv.gz
gzip -t ../raw/direct_dependencies.csv.gz
```

The actual selected source introducers and exact lines are recorded in
`PREDECLARED_SAMPLE.csv` and validated by `summarize_probes.py`. Additional
read-only `sed`, `rg`, `find`, `wc`, and small Python filters were used to narrow
these searches; they produced no accepted metric directly. Every command that
produced a reported compile result, timing, validation result, or summary is
recorded exactly in `run_commands.tsv`, `run_probes.sh`,
`VALIDATION_COMMANDS.md`, or above.

## Probe compilation

The exact 30 command strings, one independent visibility compile and one client
compile per selected API, are in `run_commands.tsv`. P01 was executed first
against the empty `probes/build` directory. P02--P15 were executed by:

```sh
chmod +x ../probes/run_probes.sh
../probes/run_probes.sh
```

The command template was:

```sh
/usr/bin/time -p -o <time-log> \
  lake env lean \
    -R <library-repo>/tmp/library_audit/higham_v01-045daf2/probes/src \
    -o <fresh-probe-output>.olean \
    -i <fresh-probe-output>.ilean \
    <probe-source>.lean
```

Every target `.olean` and `.ilean` was absent immediately before its recorded
run. Imported dependencies came from this isolated worktree's existing
`.lake/build`; therefore these are fresh probe-output timings with cached
dependencies, not clean NumStability compilation timings.

## Harness validation

Exact validation commands are in `VALIDATION_COMMANDS.md`. The known-good
visibility control exited 0. The deliberate ill-typed client exited 1 after its
`#check` printed successfully.

## Analysis and checksums

```sh
python3 ../probes/summarize_probes.py
```

The script reads the predeclared manifest, the probe statuses/timings/logs, the
compiled declaration metadata, the compiled direct-dependency rows, and the
static source-import graph. It writes `results.csv`, the selected type-edge and
entry-point excerpts, `summary.json`, and `SHA256SUMS`. Its absolute input paths
and schema version are embedded in the source and JSON.

## Read-only verification

```sh
git status --porcelain=v1 --untracked-files=all
```

This produced no output in the isolated worktree. All new files are outside the
worktree beneath the ignored audit root.
