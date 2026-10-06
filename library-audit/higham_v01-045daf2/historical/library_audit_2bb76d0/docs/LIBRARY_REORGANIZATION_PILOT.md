# NumStability reorganization pilot

The pilot applied the reorganization standards to
`NumStability.Analysis.NonrandomRounding`, a 3,952-line module that compiled in
66.243 seconds despite being far smaller than the library's largest files.  It
was selected because it contained four clear responsibilities and had no public
declarations used by another module at baseline.

## Change

The original import path remains a compatibility umbrella.  Its implementation
is now divided into:

| Module | Responsibility | Lines |
| --- | --- | ---: |
| `NonrandomRounding.Core` | exact rational function, continued fraction, abstract rounded trace | 209 |
| `NonrandomRounding.IEEETrace` | concrete IEEE-double Horner trace | 325 |
| `NonrandomRounding.SourceGrid` | source-grid range, variation, and diagnostic certificates | 1,589 |
| `NonrandomRounding.StoredGrid` | stored-input exact IEEE-double certificates | 1,865 |
| `NonrandomRounding` | compatibility umbrella | 9 |

The boundaries at the start of `IEEETrace` and `SourceGrid` had no references to
private declarations on the earlier side.  The stored-grid boundary needed one
range lemma 24 times.  That lemma was promoted from a module-private generated
name to the documented public name
`NumStability.ieeeDouble_finiteNormalRange_of_abs_between_one_thousand`.

## Verification

- The affected target builds.
- A full `lake build` passes.
- No existing public declaration was removed or renamed.
- All 187 stable public declarations moved only in module ownership.
- No stable public logical dependency edge was added or removed.
- Apparent leaves remain 55 total and 44 public.
- Isolated declarations remain 7.
- Exact-statement duplicate candidates remain 1,698 groups and 3,507 public
  declarations.
- The leaf-review queue remains 7,153 generated/private helpers, 1,637 possible
  duplicates, and 17,766 unreviewed declarations library-wide.

One public declaration and ten declarations overall were added relative to the
baseline accounting.  The public addition is the promoted shared lemma; the
remaining difference comes from private/generated identities changing when
their owning module changes.

## Compilation comparison

Each timing compiles the named source to a fresh output artifact while using
existing dependency artifacts, matching the baseline method.

| Module | Seconds |
| --- | ---: |
| Baseline `NonrandomRounding` | 66.243 |
| `Core` | 5.623 |
| `IEEETrace` | 2.712 |
| `SourceGrid` | 49.975 |
| `StoredGrid` | 3.757 |
| Compatibility umbrella | 2.346 |
| Post-pilot sequential sum | 64.413 |

The comparable sequential sum is 1.830 seconds, or about 2.8%, below the
baseline.  That small aggregate improvement is less important than incremental
isolation: editing `StoredGrid` no longer requires elaborating the 49.975-second
`SourceGrid`, and consumers needing only the abstract or IEEE trace can import
much smaller modules.

The pilot also localized the remaining hotspot.  `SourceGrid` alone exceeds the
40-second priority threshold and needs a separate community-aware split review.

## Import and metric interpretation

The subsystem changed from two direct project imports to six: two foundation
imports in `Core` plus four explicit edges through the new module chain.  Across
all imports, the source files changed from eight direct imports to twelve.  This
is an intentional cost of explicit responsibility boundaries, not evidence of
broader external dependency breadth: each module after `Core` has one direct
project import.

Public cross-module utilization within the subsystem rises from 0% to 21.8085%
because 41 declarations now cross the newly introduced file boundaries.  The
stable public logical-edge diff is exactly zero.  Therefore this increase must
not be reported as new mathematical reuse; it demonstrates that cross-module
utilization is sensitive to module granularity.

## Decision

Accept the pilot hierarchy and compatibility umbrella.  Use the same gates for
later waves, but do not treat splitting as automatically beneficial.  A proposed
split must expose a coherent responsibility, preserve stable public logical
edges, and improve navigation or incremental compilation enough to justify its
additional import edges.

Generated evidence is under `tmp/library_audit/pilot/`.  The reusable comparison
command is documented in
[`tools/library_audit/README.md`](../tools/library_audit/README.md).
