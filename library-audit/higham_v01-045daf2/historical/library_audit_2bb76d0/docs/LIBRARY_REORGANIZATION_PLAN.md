# NumStability library reorganization plan

We first measured the existing library and tested the proposed organization on one representative file. The rest of the reorganization will be performed in small batches that can each be reviewed and tested. It is governed by
[`LIBRARY_REORGANIZATION_STANDARDS.md`](LIBRARY_REORGANIZATION_STANDARDS.md).
No graph result alone authorizes deletion or a public API break.

## Current state

| Phase                               | Status                            | Evidence                                                                      |
| ----------------------------------- | --------------------------------- | ----------------------------------------------------------------------------- |
| Freeze baseline                     | Complete                          | [`LIBRARY_REORGANIZATION_BASELINE.md`](LIBRARY_REORGANIZATION_BASELINE.md)   |
| Declaration-level analyzer          | Complete                          | `tools/library_audit/`                                                      |
| Leaf and duplicate candidate queues | Complete, human review ongoing    | ignored audit artifacts under`tmp/library_audit/2bb76d0/`                   |
| Standards                           | Complete                          | [`LIBRARY_REORGANIZATION_STANDARDS.md`](LIBRARY_REORGANIZATION_STANDARDS.md) |
| Representative pilot                | Complete                          | [`LIBRARY_REORGANIZATION_PILOT.md`](LIBRARY_REORGANIZATION_PILOT.md)         |
| Repository-wide waves               | Planned below                     | one independently gated wave at a time                                        |
| Publication claim                   | Blocked until final remeasurement | baseline wording remains authoritative                                        |

## Wave size and gate

A wave contains at most five implementation modules or 250 moved public
declarations, whichever limit is reached first.  Smaller waves are required
when a module exceeds 40 seconds to compile or 25,000 lines.

Before a wave starts, record its exact module list, intended moves, compatibility
paths, and exclusions.  A wave is accepted only after:

1. affected-module builds pass;
2. the full library builds;
3. existing public names are preserved or approved aliases are present;
4. stable public logical-edge changes are explained;
5. source and compiled import diffs are reviewed;
6. affected-module fresh-output timings are recorded; and
7. leaf and exact-statement candidate diffs are classified.

Use `compare_audits.py` for the graph gate.  Cross-module utilization may change
mechanically after a split, so stable declaration-edge preservation is reported
separately.

## Ordered waves

### Wave 1: safe hierarchy and naming moves

- Move source-labelled wrappers toward `Source/Higham/ChapterNN` in small
  chapter/domain batches.
- Keep canonical algorithmic declarations under their mathematical domain.
- Preserve declaration names and leave forwarding modules at old import paths.
- Normalize only module components whose target domain is unambiguous.
- Defer ambiguous `Actual`, `Bridge`, `Closure`, `Final`, and `Remaining` modules
  until their endpoint or canonical role has been reviewed.

Start with small, already focused modules.  Do not begin with
`HighamChapter9`, `HighamChapter11`, or another compilation outlier.

### Wave 2: import cleanup

- Review the 717 baseline direct imports with no direct logical declaration
  edge; the post-pilot count is 719 because of the new boundaries.
- Check tactics, notation, instances, macros, and attributes before removal.
- Replace implementation imports of broad umbrellas with narrow owning modules.
- Compile each edited source to a fresh artifact, because a cached full build is
  insufficient evidence for import removal.

Batch by independent module so a failed elaboration has a small search surface.

### Wave 3: compilation-hotspot splits

Review in this order, combining compilation time, responsibility, graph
communities, and utilization:

1. `NonrandomRounding.SourceGrid` follow-up (49.975 seconds after the pilot).
2. `Analysis.Problem2_10` (65.175 seconds, 0.258% public utilization).
3. `Algorithms.LU.BlockLU` (64.335 seconds).
4. `Analysis.Norms` (54.830 seconds).
5. `Algorithms.LeastSquares.LSQRSolve` and `LSE` (50.888 and 48.926 seconds).
6. The very large `HighamChapter9` and `HighamChapter11` modules only after the
   earlier waves validate repeatable boundaries and compatibility conventions.

Split at low-cut declaration communities, not arbitrary line counts.  A helper
used across a boundary becomes a deliberately named shared declaration or the
boundary is rejected.

### Wave 4: fragmentation review and merges

- Find tiny modules that form one strongly coupled responsibility and are
  imported together.
- Keep cheap intentional endpoint modules separate.
- Merge only when doing so removes artificial layering without creating a
  compilation or navigation outlier.
- Retain forwarding modules for old import paths during the migration window.

### Wave 5: duplicate consolidation

- Human-review the 1,698 exact-statement candidate groups.
- Mark source aliases and compatibility endpoints as intentional.
- For confirmed duplicates, choose a canonical declaration, redirect internal
  users, and retain documented aliases when externally meaningful.
- Never infer semantic duplication from a hash or statement equality alone.

### Wave 6: confirmed dead-content removal

- Consider only declarations manually classified `genuinely_unused` or
  approved duplicate implementations with a canonical replacement.
- Check source-coverage inventories, documentation, examples, and downstream
  repository references.
- Remove content in very small batches with explicit recovery through version
  control and a full graph/build gate.

## Final remeasurement and publication

After all accepted waves, rerun the unchanged baseline workflow.  Report at
least:

- weak-component coverage;
- declarations referenced anywhere in NumStability;
- declarations referenced across module boundaries;
- public versus private/internal results;
- import-versus-declaration-use discrepancies; and
- affected and library-wide compilation distributions.

The current defensible statement is that 97.160% of public declarations belong
to the largest weak component, while 12.244% are referenced from another module
at baseline.  The first number is connectedness, not reuse.  No stronger
publication claim should be made until final remeasurement and review of the
apparent leaves.

## Automation modes

The validated process is packaged with three explicit modes:

- `audit`: read-only capture, graph generation, metrics, and comparison;
- `propose`: produce a bounded dry-run manifest with rationale and gates; and
- `fix`: apply only an approved manifest, then build and compare.

`fix` must not select deletions, public renames, or wave scope on its own.
