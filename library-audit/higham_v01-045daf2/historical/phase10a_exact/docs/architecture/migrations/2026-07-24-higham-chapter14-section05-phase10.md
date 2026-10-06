# Phase 10A: Higham Chapter 14, Section 5

Date: 2026-07-24

Execution base: `227f41ce0018596c154d07a00631e9984d7b4c27`

This record is the authoritative pre-edit ownership map for the first Stage 1
slice after Phase 9. All Git blobs, line counts, import edges, and compiled
ownership counts refer to the immutable execution base above. The migration is
a path-and-import reorganization: declaration names, namespaces, types, bodies,
visibility, and source order remain unchanged.

## Scope and role decision

The slice moves the three modules formalizing the exact and rectangular Schulz
inverse iteration from the flat historical `Algorithms` directory into the
canonical source hierarchy for Higham Section 14.5. The family is
dependency-contained: its only production consumer outside the family is the
broad `NumStability.Algorithms` aggregate.

These modules are classified as `source`, not `reusable`. Their public names
are explicitly `higham14*` or `ch14ext_*`; their statements and documentation
track the printed Section 14.5 initialization and convergence argument; and no
source-independent production module consumes their declarations. A later API
extraction may introduce provenance-neutral Schulz vocabulary, but that would
be a declaration/API refactor and is intentionally separate from this
compatibility-preserving path migration.

The slice is complete only when:

1. each of the three declaration populations has exactly one canonical owner
   below `Source.Higham.Chapter14.Section05`;
2. `Source.Higham.Chapter14.Section05` is a documented, sorted,
   declaration-free aggregate;
3. all three historical paths are exact one-import compatibility wrappers;
4. no production module imports one of the three historical paths;
5. the existing Chapter 14 and broad public entry points expose representative
   declarations through the canonical family;
6. source and compiled old-versus-new ownership audits pass after normalizing
   only the three changed module owners and private-name module prefixes; and
7. isolated canonical-only, aggregate-only, and old-only tests plus the full
   repository architecture and build gates pass.

## Immutable source inventory

The three historical owners contain 87 explicit declaration blocks: 70
public-like blocks and 17 explicit private blocks. Their compiled environments
contain 121 owned constants: 75 public, 24 internal, and 22 private.

| Historical owner | Git blob | Lines | Explicit declarations | Compiled ownership | First declaration | Last declaration |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `Algorithms.Ch14SchulzIteration` | `8e5c39d08218997642571bcc08d3a395c6712e41` | 400 | 19 public-like | 21 public + 6 internal | `higham14SchulzStep` | `higham14Schulz_source_initialization_tendsto_inverse` |
| `Algorithms.Ch14SchulzRectangular` | `9c129b01ccf0f20989a03b58ed53bfcb1f88713b` | 603 | 30 public-like + 15 private | 32 public + 14 internal + 20 private | private `ch14ext_matrixOf_matMul`; first public `ch14ext_rectSchulzStep` | `ch14ext_schulzIter_tendsto_inverse_of_leftResidual_infNorm_lt_one` |
| `Algorithms.Ch14SchulzSpectralConvergence` | `77283f36c9c22c2af0bd8ec65b0e79f62c84aef7` | 658 | 21 public-like + 2 private | 22 public + 4 internal + 2 private | `ch14ext_rectOpNorm2` | `ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq` |

The compiled population includes generated equation and simplification
theorems. In particular, the spectral module owns the generated
`RectRankFactorization.mk.congr_simp` public theorem and
`rectRightGramBasisSVDHeadRankFactorization.eq_1` internal theorem. They are
part of the preservation target even though their names do not carry the
Chapter 14 prefix.

## Exact old-to-new ownership map

| Historical owner | Canonical owner | Role |
| --- | --- | --- |
| `Algorithms.Ch14SchulzIteration` | `Source.Higham.Chapter14.Section05.SquareIteration` | source |
| `Algorithms.Ch14SchulzRectangular` | `Source.Higham.Chapter14.Section05.RectangularIteration` | source |
| `Algorithms.Ch14SchulzSpectralConvergence` | `Source.Higham.Chapter14.Section05.SpectralConvergence` | source |

`Source.Higham.Chapter14.Section05` is the new declaration-free aggregate.
`SquareIteration`, `RectangularIteration`, and `SpectralConvergence` describe
the mathematical scope without repeating the chapter number or exposing proof
progress vocabulary. `Section05` records the stable source locator in the
repository's fixed-width dialect.

Each old module remains at its current path and imports exactly its canonical
owner. The wrappers are recorded in `COMPATIBILITY.md` and remain until a
declared breaking release.

## Dependency and consumer map

The immutable direct imports are:

- `Ch14SchulzIteration`: six Mathlib modules and
  `Analysis.MatrixAlgebra`;
- `Ch14SchulzRectangular`:
  `Algorithms.Underdetermined.UnderdeterminedSpec`;
- `Ch14SchulzSpectralConvergence`: `Ch14SchulzRectangular`,
  `Algorithms.MatrixPowers`, and
  `Algorithms.LeastSquares.Higham20Problem20_3`.

The canonical spectral module replaces its historical family import with
`Source.Higham.Chapter14.Section05.RectangularIteration`. All other mathematical
imports stay explicit and unchanged. The later Chapter 21 and Chapter 20
migrations will canonicalize the two source dependencies without changing this
family's ownership.

The only production imports of the historical family are:

- `Algorithms` imports all three historical modules; and
- `Ch14SchulzSpectralConvergence` imports `Ch14SchulzRectangular`.

`Algorithms` will import the new Section 5 aggregate once. The canonical
spectral leaf imports the canonical rectangular leaf directly. No declaration
outside this family is compiled as a consumer of the three owners.

## Preservation audit

The declaration blocks in each canonical implementation must compare
byte-for-byte with the corresponding base file after UTF-8/BOM and line-ending
normalization. Header comments, module documentation, direct import paths, and
path-specific comments may change; declarations and namespace scaffolding may
not.

Moving a file changes generated private names beginning with
`_private.<historical-owner>.0`. The compiled comparison may normalize only the
three recorded owner paths and their matching private prefixes in declaration
names, types, and bodies. It must then compare unique ownership, normalized
names, kinds, visibility, type structure, and body/proof structure. The
expected result is the same 121 constants with no added, removed, or mismatched
constant.

## Entry points, tests, and manifests

The implementation adds seven isolated tests:

- canonical-only tests for the three declaration leaves;
- an aggregate-only test for `Source.Higham.Chapter14.Section05`; and
- three old-only tests, each importing exactly one historical wrapper.

Representative checks cover the square step and convergence theorem, the
rectangular step and Moore--Penrose convergence bridge, and the spectral
initializer theorem. The existing Chapter 14, `Algorithms`, `Source`,
`Source.Higham`, historical `Higham`, `All`, root, `SourceCanonical`, and
`SourceMigration` smokes exercise the changed public surfaces.

The tier manifest records the three canonical owners as `source`, the new
Section 5 aggregate as `aggregate`, and the three old paths as
`compatibility`. The compatibility table records the exact one-to-one map.
The layout manifest records Section 5 as a complete aggregate and removes the
three old modules from the unclassified and noncanonical debt sets.

Before incidental line-count changes, the expected structural ratchet is:

| Measure | Phase 9 | Expected Phase 10A |
| --- | ---: | ---: |
| Production modules | 953 | 957 |
| Classified modules | 327 | 334 |
| Unclassified modules | 626 | 623 |
| Aggregate modules | 62 | 63 |
| Compatibility modules | 86 | 89 |
| Source modules | 123 | 126 |
| Missing module docs | 222 | 222 |
| Legacy naming exceptions | 419 | 416 |
| Mixed modules | 0 | 0 |
| Declaration-bearing umbrellas | 0 | 0 |
| Unsorted aggregates | 0 | 0 |

The `Algorithms` direct-project-import ceiling is expected to move from 447 to
445: three historical imports are replaced by one canonical Section 5
aggregate. Its direct `Source` imports move from nine to ten and direct
`Analysis` imports remain 44. The compatibility inventory grows from 86 to 89
wrappers and from 184 to 187 direct canonical targets.

## Validation commands

Validation requires:

- isolated builds of the three canonical leaves and the Section 5 aggregate;
- isolated builds of the three old-only wrapper tests;
- the registered `NumStabilityTest` target and `lake test`;
- `lake build NumStability NumStabilityTest`;
- `lake env lean examples/LibraryLookup.lean`;
- layout, compatibility, provenance, placeholder, classified-source-boundary,
  aggregate-ordering, Apache-normalization, Python-syntax, and JSON checks;
- a full compiled declaration capture and exact old-versus-new comparison;
- baseline regeneration and clean reproduction;
- `git diff --check`; and
- a final clean-commit rerun before pushing to `main`.
