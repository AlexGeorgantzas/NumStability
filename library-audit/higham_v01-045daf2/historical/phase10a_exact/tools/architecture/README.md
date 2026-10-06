# Architecture baseline tooling

This directory contains the reproducible measurements used during the
book-formalization migration. The generator has two layers:

- `generate_baseline.py` scans Lean sources and the direct-import graph using
  only the Python standard library.
- `declaration_dependencies.lean` loads the compiled `NumStability`
  environment and separates references found in declaration signatures from
  references found only in definition bodies or theorem proofs.
- `check_compatibility.py` verifies that every old path documented in the
  compatibility table is an import-only wrapper around exactly its stated
  canonical targets, and that production code does not import old paths.
- `check_layout.py` enforces the naming, classification, aggregate, generated-
  artifact, and documentation ratchet recorded in
  `docs/architecture/layout-exceptions.json`.
- `check_provenance.py` validates license pointers and exact upstream evidence.
- `sort_aggregate_imports.py` mechanically normalizes import-only umbrellas.

Run the complete capture from the repository root:

```text
python tools/architecture/generate_baseline.py --name YYYY-MM-DD
```

Check the compatibility contract independently:

```text
python tools/architecture/check_compatibility.py
```

Sort and deduplicate an import-only aggregate mechanically:

```text
python tools/architecture/sort_aggregate_imports.py NumStability/Algorithms.lean --write
```

Check that no architectural debt has increased:

```text
python tools/architecture/check_layout.py
```

Check license pointers and evidenced upstream attribution:

```text
python tools/architecture/check_provenance.py
```

The reviewed one-time normalizer for legacy Apache notices is dry-run by
default. `--write` adds the canonical SPDX identifier and license path while
preserving copyright and author lines:

```text
python tools/architecture/normalize_apache_notices.py
python tools/architecture/normalize_apache_notices.py --write
```

`--write-baseline` is a review-only bootstrap/update operation. It records the
exact current legacy exception sets; ordinary CI requires equality so a debt
reduction must update the reviewed baseline and cannot silently regress at the
same path later. Never use it to make an unexplained regression pass.

The layout check also rejects production or test modules containing `sorry`,
`admit`, or top-level `axiom`/`constant` commands. This is a zero-debt gate, not
a grandfathered warning count.

The command builds `NumStability`, then writes matching JSON and Markdown files
under `docs/architecture/baselines/`. The JSON is the machine-readable source
of truth. The Markdown is generated for review.

Useful options:

```text
# Fast source/import-only capture
python tools/architecture/generate_baseline.py --skip-declarations --name source-only

# CI/release guard for unresolved imports, cycles, and classified forbidden edges
python tools/architecture/generate_baseline.py --skip-declarations --strict-source \
  --output-dir benchmark-results/architecture --name source-check

# Reuse already-current .olean files
python tools/architecture/generate_baseline.py --no-build --name YYYY-MM-DD

# Verify that a committed capture is reproducible
python tools/architecture/generate_baseline.py --check --name YYYY-MM-DD

# Retain the large raw dependency stream for separate analysis
python tools/architecture/generate_baseline.py \
  --keep-dependency-tsv benchmark-results/architecture/dependencies.tsv \
  --name YYYY-MM-DD

# Re-render from a previously retained raw stream
python tools/architecture/generate_baseline.py \
  --dependency-tsv benchmark-results/architecture/dependencies.tsv \
  --name YYYY-MM-DD
```

The raw TSV is kept below the ignored `benchmark-results/` tree by default. It
can contain hundreds of thousands of edges and is an intermediate
representation, not a stable data format.

Check mode compares the production-source SHA-256, source/import metrics,
compiled declaration metrics, Lean toolchain, and Mathlib revision. The digest
normalizes UTF-8 BOMs and CRLF/CR line endings so Windows and Linux checkouts
agree. Check mode ignores
capture-time Git fields such as `HEAD`, branch, and dirty-path provenance,
which necessarily change when a generated report is committed. It separately
requires the committed Markdown to be the exact rendering of the committed
JSON.

## Metric definitions

The import graph contains an edge `A -> B` when module `A` directly imports
module `B`.

The declaration graph contains an edge `A -> B` when the elaborated signature,
body, or proof of declaration `A` directly contains constant `B`. Signature and
body/proof edges are retained separately. An edge appearing in both sets is
counted once in the union graph.

- An **apparent leaf** has no incoming project declaration edge.
- A **project-foundational declaration** has no outgoing project declaration
  edge.
- A **project-isolated declaration** has neither incoming nor outgoing project
  declaration edges.
- **Cross-module utilization** is the fraction of public declarations that at
  least one project declaration in another module directly references.
- **Weak-component coverage** forgets edge direction and measures undirected
  connectedness. It does not measure reuse.

For the report, a declaration is classified as public when its Lean name is
neither private nor an internal-detail name. Generated recursors and
constructors remain visible in the raw population and are reported by kind.

These diagnostics identify review candidates. They are not dead-code tests,
and their percentages are not optimization targets.

## Tier audit

The generator also reads
[`docs/architecture/tiers.json`](../../docs/architecture/tiers.json). It reports
classification coverage, a tier-to-tier import matrix, and direct/transitive
`reusable -> source` / `reusable -> mixed` violations. The manifest is
deliberately partial while mixed historical modules are being split. A zero
violation count does not satisfy the physical-target gate until coverage
reaches 100% and no mixed modules remain; see
[`docs/architecture/TIERS.md`](../../docs/architecture/TIERS.md).
