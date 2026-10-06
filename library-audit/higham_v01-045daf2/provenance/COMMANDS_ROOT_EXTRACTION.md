# Root extraction and validation commands

All commands below were run on 2026-09-03 from
`<library-repo>`, unless an
explicit `cd` changes the directory. `AUDIT_ROOT` was always:

```bash
AUDIT_ROOT=<library-repo>/tmp/library_audit/higham_v01-045daf2
```

The Git/bootstrap and build commands are recorded separately in
`COMMANDS_BUILD_ENVIRONMENT.md`; historical recovery/replay commands are in
`../historical/PHASE10A_COMMANDS.md`; source/static commands are in
`../static_architecture/COMMANDS.md`; public-client commands are in
`../probes/COMMANDS.md` and `../probes/run_commands.tsv`.

## Full compiled declaration graph

The byte-recovered, unmodified post-Phase-10A extractor was executed outside
the presentation source tree. Named FIFOs allowed its large CSVs to be retained
losslessly as gzip streams without requiring a second multi-gigabyte copy.

```bash
FIFO_DIR="$AUDIT_ROOT/raw/library_audit_fifos"
mkdir -p "$FIFO_DIR"
mkfifo "$FIFO_DIR/declarations.csv" \
  "$FIFO_DIR/direct_dependencies.csv" \
  "$FIFO_DIR/module_imports.csv"
gzip -9 -c "$FIFO_DIR/declarations.csv" > "$AUDIT_ROOT/raw/declarations.csv.gz" &
gzip -9 -c "$FIFO_DIR/direct_dependencies.csv" > "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" &
gzip -9 -c "$FIFO_DIR/module_imports.csv" > "$AUDIT_ROOT/raw/module_imports.csv.gz" &
cd "$AUDIT_ROOT/_worktree"
NUMSTABILITY_AUDIT_OUT="$FIFO_DIR" /usr/bin/time -lp \
  lake env lean \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/DeclarationGraph.lean" \
  > "$AUDIT_ROOT/raw/library_audit_extraction.log" \
  2> "$AUDIT_ROOT/raw/library_audit_extraction.time"
```

The three FIFO paths were then unlinked individually and their now-empty
directory removed. (`unlink` on macOS accepts one path at a time.)

```bash
for f in declarations.csv direct_dependencies.csv module_imports.csv; do
  unlink "$FIFO_DIR/$f"
done
rmdir "$FIFO_DIR"
gzip -t "$AUDIT_ROOT/raw/declarations.csv.gz"
gzip -t "$AUDIT_ROOT/raw/direct_dependencies.csv.gz"
gzip -t "$AUDIT_ROOT/raw/module_imports.csv.gz"
gzip -dc "$AUDIT_ROOT/raw/declarations.csv.gz" | wc -l
gzip -dc "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" | wc -l
gzip -dc "$AUDIT_ROOT/raw/module_imports.csv.gz" | wc -l
shasum -a 256 "$AUDIT_ROOT/raw/declarations.csv.gz" \
  "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" \
  "$AUDIT_ROOT/raw/module_imports.csv.gz"
```

Validated row counts, including headers, were 77,247 declarations, 3,963,824
direct-reference rows, and 29,566 compiled-import rows. All three `gzip -t`
checks passed.

## Reserved names and enriched declaration metadata

The skill's exact `DeclarationOrigins.lean` was executed unchanged:

```bash
cd "$AUDIT_ROOT/_worktree"
NUMSTABILITY_AUDIT_OUT="$AUDIT_ROOT/raw" /usr/bin/time -lp \
  lake env lean \
  <codex-home>/skills/numstability-library-reorganization/scripts/DeclarationOrigins.lean \
  > "$AUDIT_ROOT/raw/declaration_origins_extraction.log" \
  2> "$AUDIT_ROOT/raw/declaration_origins_extraction.time"
```

The audit-only metadata extractor was run from the ignored artifact tree:

```bash
cd "$AUDIT_ROOT/_worktree"
NUMSTABILITY_AUDIT_OUT="$AUDIT_ROOT/raw" /usr/bin/time -lp \
  lake env lean "$AUDIT_ROOT/tooling/current_audit/DeclarationMetadata.lean" \
  > "$AUDIT_ROOT/raw/declaration_metadata_extraction.log" \
  2> "$AUDIT_ROOT/raw/declaration_metadata_extraction.time"
```

An initial enriched-metadata attempt failed before command elaboration because
`isStructure` was incorrectly invoked as an environment field. The ignored
extractor was corrected to call `Lean.isStructure`; the final command above
then exited 0 and replaced the metadata CSV. No presentation-branch source was
edited. The failed diagnostic is described in the final limitations/provenance
record and is not used as data.

## Exact expression-equivalence candidates

```bash
cd "$AUDIT_ROOT/_worktree"
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

The extractor reported 77,246 declarations in 59,848 exact Lean-expression
equivalence classes. Filtering to non-singletons produced 1,710 review groups
containing 3,533 declarations. These are review signals, not redundancy
findings.

## Recovered library-audit analyzer

Its included known-example test was run before current data were analyzed:

```bash
python3 \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/test_analyze_graph.py"
```

The test passed. The recovered analyzer was then run unchanged with gzip
decompression feeding three input FIFOs:

```bash
INPUT_DIR="$AUDIT_ROOT/metrics/_legacy_inputs"
OUT_DIR="$AUDIT_ROOT/metrics/recovered_library_audit_schema"
mkdir -p "$INPUT_DIR" "$OUT_DIR"
mkfifo "$INPUT_DIR/declarations.csv" \
  "$INPUT_DIR/direct_dependencies.csv" \
  "$INPUT_DIR/module_imports.csv"
gzip -dc "$AUDIT_ROOT/raw/declarations.csv.gz" > "$INPUT_DIR/declarations.csv" &
gzip -dc "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" > "$INPUT_DIR/direct_dependencies.csv" &
gzip -dc "$AUDIT_ROOT/raw/module_imports.csv.gz" > "$INPUT_DIR/module_imports.csv" &
/usr/bin/time -lp python3 \
  "$AUDIT_ROOT/historical/recovered_library_audit/tools/library_audit/analyze_graph.py" \
  "$INPUT_DIR" --output "$OUT_DIR" \
  > "$AUDIT_ROOT/metrics/recovered_library_audit_analyze.log" \
  2> "$AUDIT_ROOT/metrics/recovered_library_audit_analyze.time"
```

The three decompressor processes and analyzer all exited 0. The FIFOs were
unlinked individually afterward. This recovered schema is retained as an
independent check; the richer current audit uses a separately versioned and
tested schema.

## Read-only diagnostic checks

The following forms were used to inspect headers, counts, process completion,
and cleanliness:

```bash
gzip -dc "$AUDIT_ROOT/raw/declarations.csv.gz" | sed -n '1,4p'
gzip -dc "$AUDIT_ROOT/raw/direct_dependencies.csv.gz" | sed -n '1,4p'
gzip -dc "$AUDIT_ROOT/raw/module_imports.csv.gz" | sed -n '1,4p'
git -C "$AUDIT_ROOT/_worktree" status --short
git -C <library-repo> status --short
rg --files -uu
```

Additional narrowly scoped `rg`, `sed`, `find`, `wc`, `gzip -dc`, `shasum`,
`git show`, and Python `csv`/`json` read-only inspections were used to verify
specific rows cited in the reports. Every substantive extraction, build,
timing, probe, replay, and analyzer command is retained in the command records
linked above or produced alongside its artifact family.
