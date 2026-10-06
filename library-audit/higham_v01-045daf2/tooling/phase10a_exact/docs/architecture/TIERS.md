# Executable tier inventory

[`tiers.json`](tiers.json) is the machine-readable classification used by the
architecture generator. Exact module rules take precedence over prefix rules.
The source audit reports classified import edges and treats every direct or
transitive path from `reusable` into `source` or `mixed` as forbidden. This
prevents aggregate, compatibility, internal, or not-yet-classified
intermediate modules from hiding a dependency inversion.

The inventory is intentionally partial during this migration. Large historical
areas below `Algorithms/` and `Analysis/` still mix reusable mathematics,
numbered-source correspondence, and proof support; assigning either directory
one blanket tier would hide the problem. The generated baseline therefore
reports both classification coverage and the complete unclassified queue.

A zero forbidden-edge count is conclusive only when classification coverage is
100% and no `mixed` modules remain. Until then, the physical-source-target gate
is not satisfied, even when all currently classified reusable modules have zero
source or mixed imports.

When a module is reviewed:

1. classify it by mathematical role, not pathname;
2. add the narrowest exact or prefix rule that does not misclassify siblings;
3. run the strict source audit;
4. resolve any new reusable-to-source edge or document why the proposed tier is
   wrong;
5. split mixed modules before claiming complete coverage.

`compatibility` is a transitional tier for old import-only paths, and
`aggregate` is used for umbrella entry points. Neither is a destination for new
mathematical declarations. `mixed` marks a reviewed module that still contains
more than one declaration tier; it is an explicit split queue, not a permanent
architecture category.

The Chapter 1 Section 1.17 migration uses exact `aggregate` rules for
`NumStability.Source.Higham.Chapter01` and its `Section17` child. The five
canonical leaves inherit `source` from the `NumStability.Source` prefix. The
six historical `NumStability.Analysis.NonrandomRounding*` paths use exact
`compatibility` rules; there is deliberately no source-tier prefix rule for
that historical directory.

Phase 9 applies the same rule to Higham Chapters 12, 13, 22, and 27. Exact
`aggregate` rules cover `Chapter12`, `Chapter22`, `Chapter22.Section03`, and
`Chapter27`; the existing `Chapter13` aggregate keeps that role. The eleven
canonical implementation leaves inherit `source`, while their eleven former
`Algorithms*` owners now have exact `compatibility` rules. Consequently 327 of
953 production modules are classified: 123 as source, 62 as aggregate, 86 as
compatibility, and the remainder in the other reviewed tiers. The explicit
unclassified queue is 626 modules and the mixed queue remains empty.
The `NumStability.Algorithms` direct-import ceilings are 447 imports below
`NumStability`, including 9 below `NumStability.Source` and 44 below
`NumStability.Analysis`.

Because structural aggregates do not themselves own declarations,
`reusable_entrypoints` separately lists aggregates whose entire reachable
surface must obey the reusable-to-source dependency gate. This keeps structural
role and dependency semantics distinct: `Core` and `FloatingPoint` remain
import-only aggregates while still seeding the transitive forbidden-edge audit.
