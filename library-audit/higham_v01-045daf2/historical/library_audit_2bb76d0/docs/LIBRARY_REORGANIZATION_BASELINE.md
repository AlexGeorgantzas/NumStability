# NumStability reorganization baseline

This baseline was measured before any library source renaming, moving, splitting,
merging, or deletion.

- Commit: `2bb76d004b7dddd0e6dfb61f84c0be8e6816fa19`
- Lean: `v4.29.0-rc3`
- Mathlib: `v4.29.0`
- NumStability source worktree at capture time: clean
- Lean source files: 597
- Lean source lines: 1,404,857
- Source-level direct imports: 2,948
- Full incremental `lake build`: pass, 2.706 seconds with existing artifacts
- Independent module compilations: 597/597 pass (a module is essentialy a .lean file. Ignoring umbrella modules that contain only imports and only counting files that are part of the formalization and contain math they are 591 in total.)

## Declaration graph definitions

Every logical declaration edge is directed:

```text
A -> B means the elaborated type or body/proof of A directly references B.
```

- An **apparent leaf** has no incoming NumStability declaration edge.
- A **project-foundational declaration** has no outgoing NumStability edge.
- A **project-isolated declaration** has neither incoming nor outgoing
  NumStability edges.
- **Cross-module utilization** is the fraction of declarations referenced by at
  least one declaration in another NumStability module.
- **Weak-component coverage** forgets edge direction and measures undirected
  connectedness. It does not measure reuse.

Generated, internal, and private declarations are retained in the raw graph and
labelled. Public metrics exclude internal and private declarations.

## Baseline graph results

| Measure                                             |  Result |
| --------------------------------------------------- | ------: |
| All uniquely owned declarations                     |  76,247 |
| Public declarations                                 |  58,950 |
| Direct NumStability declaration edges               | 460,540 |
| Cross-module declaration edges                      | 200,854 |
| Project modules in compiled graph                   |     597 |
| Project modules containing declarations             |     591 |
| Apparent leaves                                     |  26,556 |
| Apparent public leaves                              |  19,403 |
| Public isolated declarations                        |     167 |
| Largest weak component, all declarations            | 90.514% |
| Largest weak component, public declarations         | 97.160% |
| Public declarations referenced somewhere in project | 67.086% |
| Public declarations referenced from another module  | 12.244% |

From the above table we can determine:

| Category                                      | Count  | % of all public declarations |
| --------------------------------------------- | ------ | ---------------------------- |
| Referenced from another module                | 7,218  | 12.24%                       |
| Referenced only inside their own module       | 32,329 | 54.84%                       |
| Not referenced by another project declaration | 19,403 | 32.91%                       |

## Compilation outliers

| Module                                                         |   Lines | Seconds | Public cross-module utilization |
| -------------------------------------------------------------- | ------: | ------: | ------------------------------: |
| `NumStability.Algorithms.HighamChapter9`                     | 113,808 | 104.141 |                          4.555% |
| `NumStability.Algorithms.HighamChapter11`                    | 137,119 |  78.260 |                          1.676% |
| `NumStability.Analysis.NonrandomRounding`                    |   3,952 |  66.243 |                          0.000% |
| `NumStability.Analysis.Problem2_10`                          |  33,474 |  65.175 |                          0.258% |
| `NumStability.Algorithms.LU.BlockLU`                         |  82,083 |  64.335 |                          8.989% |
| `NumStability.Analysis.Norms`                                |  24,042 |  54.830 |                         15.768% |
| `NumStability.Algorithms.LeastSquares.LSQRSolve`             |  74,409 |  50.888 |                         15.458% |
| `NumStability.Algorithms.LeastSquares.LSE`                   | 106,600 |  48.926 |                          7.726% |
| `NumStability.Algorithms.Cholesky.Higham10Theorem10_7Source` |   1,633 |  42.086 |                          7.692% |
| `NumStability.Analysis.InstabilityWithoutCancellation`       |  19,114 |  32.969 |                          0.470% |

The qualitative conclusion is not “large files bad, small files good.” For
example, `QR.Higham19` has 40,748 lines but compiled in 20.977 seconds, while
the smaller `NonrandomRounding` took 66.243 seconds. Conversely, the many
focused Higham 28 modules generally compiled in approximately 3–6 seconds.
Split priority must combine compilation time, size, utilization, and graph
community structure.

## Review queues

The generated apparent-leaf queue initially classifies only by visibility:

- 7,153 non-public leaves: `generated_or_private_helper` review.
- 1,637 public leaves: `possible_duplicate` because another public declaration
  has an exactly equal elaborated statement.
- 17,766 remaining public leaves: deliberately left `unreviewed`.

The exact structural statement pass uses Lean expression equality after hash
bucket selection. It produced 1,698 candidate groups containing 3,507 public
declarations. These are not automatic deletions: many are intentional aliases,
source-facing equation names, or specialized API endpoints.

## Reproduction

The complete commands, schemas, metric semantics, and limitations are documented
in [`tools/library_audit/README.md`](../tools/library_audit/README.md). Generated
raw data and reports live under ignored `tmp/library_audit/<commit>/` paths.

## Publication boundary

Report the following separately:

1. Weak connected-component coverage.
2. Percentage of declarations referenced anywhere inside NumStability.
3. Percentage of declarations referenced across module boundaries.
4. Public versus internal/private declaration results.

Do not use component membership as evidence of meaningful reuse, modularity, or
non-redundancy.
