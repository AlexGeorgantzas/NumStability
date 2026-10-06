# Organization phase 10A build evidence (2026-07-24)

This record covers the compatibility-preserving Higham Chapter 14 Section
14.5 migration developed on
`codex/organization-phase-10-chapter14-section05` from
`227f41ce0018596c154d07a00631e9984d7b4c27`. The immutable ownership map was
committed before implementation as
`899003baca0fdca2714344a69c10eef4b2d3c306`.

Candidate-worktree validation and clean-commit validation are recorded
separately. The declaration-bearing architecture capture was made from the
candidate worktree. Its source, import, declaration, toolchain, and Mathlib
measurements will be reproduced from the clean implementation revision before
push.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib revision | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Production target | `NumStability` |
| Test driver | `NumStabilityTest` |

## Migration result

The three historical declaration owners
`Algorithms.Ch14SchulzIteration`, `Algorithms.Ch14SchulzRectangular`, and
`Algorithms.Ch14SchulzSpectralConvergence` moved one-for-one into the semantic
`Source.Higham.Chapter14.Section05` hierarchy. The new Section 5 module is a
documented, sorted, declaration-free aggregate. Each old path is an exact
one-import compatibility wrapper, and no production module imports one of the
historical implementation paths.

The migration adds four canonical production modules: three source leaves and
one aggregate. Seven isolated tests cover every canonical leaf and aggregate
and every old-only wrapper import. The Chapter 14 smoke and eight shared entry-
point smokes exercise `Algorithms`, `All`, `Higham`, the root, `Source`,
`Source.Higham`, `SourceCanonical`, and `SourceMigration`.

All 87 source-written declaration blocks are preserved. Square iteration and
spectral convergence compare byte-for-byte from their first declarations;
rectangular iteration differs only in one module-path sentence inside a
documentation comment. No declaration statement or body differs.

The compiled audit compared all 121 owned constants: 75 public, 24 internal,
and 22 private. After normalizing only the three recorded owner paths and their
occurrences in private names, names, owners, kinds, and visibility match
exactly. All 738 compiled edges incident to the family also match exactly: 251
signature edges and 487 body/proof edges. There are zero missing, added, or
mismatched declaration or edge records.

## Candidate-worktree Lean validation

| Command or gate | Result |
| --- | --- |
| Three canonical declaration leaves and the Section 5 aggregate | passed |
| Seven isolated tests plus the Chapter 14 and eight shared entry-point smokes | passed |
| `lake test` | passed; 5,169 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,171 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Compiled declaration-graph extraction | passed |
| Compiled old-versus-new declaration and incident-edge audit | passed: exact 121-to-121 and 738-to-738 matches |
| Baseline reproducibility comparison | passed |

These were cache-preserving validation builds. Existing Lean linter and
deprecation warnings remained visible; no error was hidden or waived.

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 957 |
| Source lines | 1,467,997 |
| Direct imports | 4,009 |
| Internal import edges | 2,642 |
| Import cycles | 0 |
| Classified modules | 334 |
| Classification coverage | 34.901% |
| Mixed modules | 0 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Private declarations | 4,341 |
| Internal declarations | 21,422 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles comprise 63 aggregates, 89 compatibility wrappers, two
internal modules, 49 reusable modules, 126 source modules, five upstream
modules, and zero mixed modules. There are zero direct or transitive
reusable-to-source or reusable-to-mixed paths.

The global declaration graph is exactly unchanged from Phase 9: every
declaration and global signature, body/proof, and union edge count is
identical. Phase 10A classifies all four new production modules and all three
historical wrappers, reducing the unclassified inventory from 626 to 623.

## Static validation

| Gate | Result |
| --- | --- |
| Layout and exact legacy-debt contract | passed: 957 modules |
| Placeholder and test-reachability gate | passed |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 89 wrappers, 187 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural contract | passed: every aggregate declaration-free |
| Aggregate ordering | passed for all 63 classified aggregates |
| Strict-source baseline | passed |
| Apache normalization dry run | passed: zero files require changes |
| Architecture Python syntax validation | passed |
| Architecture JSON validation | passed: 15 files |
| Baseline reproducibility comparison | passed |
| `git diff --check` | passed |

The remaining exact debt is 623 unclassified modules, 222 missing module
docstrings, and 416 historical naming exceptions. There are zero mixed
modules, zero declaration-bearing umbrellas, and zero unsorted aggregates.

## Clean-commit verification

Pending the implementation commit. This section will record the exact clean
revision and rerun results before the branch is pushed to `main`.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-24-organization-phase10a.md)
- [Machine-readable architecture baseline](2026-07-24-organization-phase10a.json)
- [Phase 10A migration and ownership record](../migrations/2026-07-24-higham-chapter14-section05-phase10.md)

The baseline records the exact production paths included in the candidate
capture. A clean implementation-revision reproduction is required before push.
