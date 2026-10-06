# Reproduction commands: timings and proof hygiene

All commands were run against the detached clean worktree
`tmp/library_audit/higham_v01-045daf2/_worktree` at
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`. Paths below are relative to the
audit root unless shown otherwise.

## Predeclared fresh-output timings

```bash
python3 timings/run_fresh_module_timings.py
```

The command compiles the exact 30-module list embedded in the script. For each
module it invokes the command recorded verbatim in the `command` column of
`timings/fresh_module_timings.csv`, of the form:

```bash
/usr/bin/time -lp lake env lean \
  -o <audit>/timings/fresh_outputs/<unique>.olean \
  -i <audit>/timings/fresh_outputs/<unique>.ilean \
  <isolated-worktree>/<module-source>.lean
```

Rows 25 and 26 overlapped a recorded unrelated-host interference window. They
were replaced with identical quiet reruns:

```bash
python3 timings/rerun_interfered_timings.py
python3 timings/summarize_timings.py
```

The scripts hash and size each fresh target output, then unlink only the two
explicit output paths beneath `timings/fresh_outputs/`. Imported oleans remain
cached and unmodified.

## Representative proof-term axioms

From the isolated worktree:

```bash
/usr/bin/time -lp lake env lean \
  <audit>/hygiene/RepresentativeAxioms.lean \
  > <audit>/hygiene/representative_axioms.log \
  2> <audit>/hygiene/representative_axioms.time
python3 <audit>/hygiene/parse_axiom_probe.py
```

## Source and compiled-environment hygiene

```bash
python3 hygiene/analyze_proof_hygiene.py
```

Inputs are:

- `raw/declaration_metadata.csv` (77,246 compiled project declarations),
- `raw/declarations.csv.gz`,
- `raw/direct_dependencies.csv.gz` (3,963,823 direct edges), and
- every `*.lean` file under `NumStability/`, plus `NumStability.lean`.

The source scanner imports the tested nested-comment/string lexer preserved in
`static_architecture/static_architecture.py`. The compiled scan distinguishes
constructors, recursors, inductives, generated `native_decide` axioms,
generated `._unsafe_rec` partial helpers, `isUnsafe`, and direct `sorryAx`
dependencies.

## Summaries and checksums

```bash
python3 timings/make_subaudit_provenance.py
```

Run this last so `timings/TIMING_HYGIENE_SHA256SUMS` covers the final artifacts.
