# NumStability library reorganization standards

These standards govern the reorganization measured against
[`LIBRARY_REORGANIZATION_BASELINE.md`](LIBRARY_REORGANIZATION_BASELINE.md).
They apply incrementally; they do not authorize broad automatic deletion or
unreviewed public API changes.

## Non-negotiable invariants

Every bounded reorganization wave must preserve:

1. A successful full `lake build`.
2. All intentional public declaration names, or an explicit compatibility alias
   and deprecation path.
3. The meaning and assumptions of proved results.
4. The baseline metric definitions and edge direction.
5. Traceability from source-facing Higham results to canonical mathematical and
   algorithmic declarations.

Generated graph findings are review evidence, not deletion decisions.

## Target hierarchy

The primary hierarchy is mathematical/algorithmic domain, not the chronology of
formalization or an agent's work session.

```text
NumStability/
  FloatingPoint/          floating-point formats and operational models
  Analysis/               reusable mathematical and error-analysis foundations
  Algorithms/
    Summation/
    LinearSystems/
    Factorization/
      LU/
      Cholesky/
      QR/
    LeastSquares/
    Eigenvalue/
    MatrixFunctions/
    Randomized/
    TestMatrices/
    ...
  Source/
    Higham/
      ChapterNN/          source-labelled wrappers, equations, and endpoints
  Examples/               demonstrations and deliberately terminal examples
```

The exact domain list may evolve during pilots. The layer roles and dependency
direction may not be inverted merely to avoid moving a declaration.

### Dependency direction

Allowed direction, from higher layer to lower dependency:

```text
Examples -> Source -> Algorithms -> Analysis -> FloatingPoint
```

- `FloatingPoint` must not import `Analysis`, `Algorithms`, or `Source`.
- `Analysis` must not import `Algorithms` or `Source`.
- Canonical `Algorithms` modules must not import source-facing chapter wrappers.
- `Source/Higham/ChapterNN` may assemble canonical results and expose book-facing
  names, theorem numbers, and closure endpoints.
- Umbrella modules may re-export lower modules, but implementation modules must
  not import their own umbrella.

Any exception requires a written rationale and a graph check showing that it
does not introduce a layer cycle.

## Naming

### Modules and files

- Use `UpperCamelCase` Lean module components.
- Use one canonical spelling for source chapters: `ChapterNN`, never a mixture
  of `Ch14`, `HighamChapter14`, and `Chapter14` at the same hierarchy level.
- Prefer a mathematical or algorithmic concept in canonical modules, such as
  `Summation/Compensated` or `Factorization/LU/Block`, over a theorem number.
- Put theorem/equation numbers in `Source/Higham/ChapterNN` wrappers when source
  traceability is the module's primary responsibility.
- Avoid workflow-state terms such as `Actual`, `Final`, `Remaining`, `Whole`,
  `Bridge`, or `Closure` unless the module exposes a stable, documented API role
  that cannot be named mathematically.
- Do not encode temporary agent waves, repair numbers, or work order in module
  names.

### Declarations

- Keep existing public declaration names during file moves whenever possible;
  moving a declaration does not require renaming it.
- Use descriptive `snake_case` for new declarations.
- Give the canonical reusable theorem the concept-facing name.
- Source-labelled aliases must be thin and documented as aliases or wrappers.
- Avoid multiple undocumented names with exactly equal elaborated statements.
  Classify them as intentional aliases or consolidate them.

## Module responsibility

Each non-umbrella module must have a short statement of responsibility that can
be completed as:

> This module defines/proves ______ for ______.

If the blank requires unrelated conjunctions, split the module. A module may
contain local supporting lemmas for its responsibility; it should not become a
general dumping ground for every later theorem that can import it.

Prefer splitting at declaration-graph community boundaries:

- Keep strongly interdependent definitions and theorems together.
- Separate low-coupling communities with few cross-community edges.
- Place shared foundations below the communities that consume them.
- Keep thin source-facing endpoints separate when doing so preserves clear
  traceability and low compilation cost.

Do not split solely to satisfy a line-count target, and do not merge focused
modules solely to reduce file count.

## Imports

- Import the narrowest stable modules that supply required declarations,
  notation, attributes, tactics, and elaboration support.
- Do not use `NumStability`, `NumStability.Algorithms`, or another broad umbrella
  inside implementation modules.
- A module that directly references another project's declarations should
  normally import the owning module directly instead of relying accidentally on
  a transitive import.
- Treat the 717 baseline imports without direct logical edges as review
  candidates. Check syntax, macro, tactic, attribute, and instance requirements
  before removal.
- After import cleanup, rebuild the module from a clean temporary output and
  compare both the source import graph and compiled import graph.

## Size and compilation thresholds

Baseline independent compilation statistics are:

- Median: 3.765 seconds.
- 90th percentile: 8.121 seconds.
- Maximum: 104.141 seconds.

Use thresholds as review triggers, not gameable acceptance tests:

| Signal | Review | Priority review |
| --- | ---: | ---: |
| Independent compilation time | over 20 s | over 40 s |
| Source lines | over 10,000 | over 25,000 |
| Public cross-module utilization | under 5% | 0% with no documented endpoint role |

- Any module above a priority threshold needs a written keep/split decision.
- A module above 40 seconds should normally be split unless the declaration
  graph shows one inseparable community and a pilot demonstrates no improvement.
- A small but slow file is not exempt. `NonrandomRounding` is only 3,952 lines
  but took 66.243 seconds.
- A large but relatively cheaper file still requires responsibility review.
  `QR.Higham19` has 40,748 lines but took 20.977 seconds.
- Aim for new or split modules near the baseline 90th percentile when coherent
  boundaries permit it.

## Leaf classification

An apparent leaf must receive exactly one reviewed classification:

- `intended_public_endpoint`
- `legitimate_final_result`
- `foundational_or_interface_declaration`
- `unfinished_or_experimental`
- `generated_or_private_helper`
- `possible_duplicate`
- `genuinely_unused`

No declaration may be deleted while classified `unreviewed`,
`intended_public_endpoint`, `legitimate_final_result`, or
`foundational_or_interface_declaration`.

`possible_duplicate` means only that another declaration has an exactly equal
elaborated statement or a strong review signal. Before consolidation, determine:

1. Which name is canonical.
2. Whether another name is a source-facing or compatibility alias.
3. Whether proof independence has documentary value.
4. Which downstream declarations or external users reference each name.

## Split, merge, move, and delete decisions

### Split when

- the module has multiple graph communities with a small cut;
- independent compilation exceeds the thresholds;
- only a small fraction of a large module is reused outside it;
- canonical infrastructure and source-facing endpoints are interleaved; or
- the module responsibility cannot be stated coherently.

### Merge when

- tiny modules form one inseparable responsibility and always change together;
- the separation creates circular or inverted dependencies; and
- merging does not create a compilation or navigation outlier.

Low-cost endpoint modules are not merged merely because they are small.

### Move when

- a declaration's canonical domain conflicts with its current directory;
- moving restores the target dependency direction; and
- public declaration names can remain stable.

### Delete only when

- the declaration is manually classified `genuinely_unused`, or a
  `possible_duplicate` has an approved canonical replacement;
- source inventories and public endpoint documentation do not require it;
- repository and declaration-graph references are absent or migrated;
- compatibility policy has been satisfied; and
- the affected build, full build, and post-change audit pass.

## Public API compatibility

- Prefer moving declarations without renaming them.
- When a public name changes, retain a documented alias and mark it deprecated
  where Lean's compatibility mechanisms permit.
- Keep temporary forwarding modules for moved import paths during a migration
  wave.
- Record intentional removals and their replacements in the wave report.
- Compare the public declaration manifest before and after every wave.

## AI-agent navigability

To make the library easier for agents as well as humans:

- keep canonical definitions and theorems in predictable domain modules;
- keep source aliases visibly separate from canonical results;
- add module docstrings stating responsibility and intended downstream users;
- document the canonical theorem when multiple aliases exist;
- keep imports narrow so retrieved context reflects real dependencies;
- prefer modules small enough to inspect and compile independently; and
- regenerate the declaration/module graphs after structural changes.

## Verification gate for every wave

Each bounded wave must produce:

1. An affected-module build.
2. A full `lake build`.
3. A public declaration manifest diff.
4. A source and compiled import-graph diff.
5. A declaration-graph metric diff using unchanged definitions.
6. Independent timing for affected modules.
7. A list of moves, aliases, consolidations, and removals with rationale.

A wave is rejected if it improves folder appearance while worsening dependency
direction, losing public API without approval, or making the measured structure
less truthful.

The validated `NonrandomRounding` pilot also establishes that cross-module
utilization is boundary-sensitive: splitting one module raised its scoped public
utilization from 0% to 21.8085% without adding or removing any stable public
logical edge. Every wave report must therefore show stable declaration-edge
diffs separately from module-level utilization.
