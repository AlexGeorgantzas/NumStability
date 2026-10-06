# Reporting and Completion

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->


## Contents

- Phase 8 decision report
- Report template
- Completion checklist
- Source and scope
- Selection quality
- Library and architecture
- Proof quality
- Reporting
- Expected final response

## Phase 8: Produce the decision report

Create or update a chapter report. Include the conditional sections only when relevant, but never omit information needed to understand an open or excluded source item.

```markdown
# Higham Chapter X Formalization Report

## Source and scope
- Edition:
- Chapter:
- Printed pages:
- Source file:
- Mode: core | comprehensive | benchmark
- Parallel split: 1 | 2 | 3 | 4
- Planning documents consulted: blueprint | assigned split contract | chapter index
- Selected-scope gate: PASS | FAIL

## Completed selected targets
| Source label | Lean declaration | File | Theorem surface | Notes |

## Reused from repository or Mathlib
| Source concept/result | Existing declaration | File/module |

## New dependencies
| Declaration | Why needed | Used by | Feasibility status |

## External proof sources
| Selected claim | Source and exact location | Role | Local Lean closure | Status |

## Skipped items
| Source location | Summary | Reason code |

## Empirical source outputs
| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |

## Deferred items
| Source location | Summary | Destination/dependency | Reason |

## Benchmark candidates
| Source location | Methods compared | Required dependencies |

## Open selected-scope items
| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |

## Hidden-hypothesis summary
- Final theorem assumptions and classifications:
- Suspicious assumptions found and resolved:

## Weak-component and bottleneck summary
- Weak components checked:
- Active/closed bottlenecks:
- Failed routes and next listed dependency, if any:

## Verification
- Commands run:
- Result:
- New versus pre-existing warnings:

## Documentation
- Inventory path:
- Not-proved/proof-source/bottleneck ledger paths, if any:
- Theorem note or PDF path, if generated:

## Open issues
- Ambiguities, suspected source typos, route choices, or genuine blockers.
```

The report and source inventory together must account for every named result,
numbered equation, selected or unselected Problem/exercise/Appendix row, and
empirical output claim. A reviewer should be able to see why any item is absent
from Lean and whether the absence is an intentional selection decision or an
unresolved selected-scope gap.

A skipped or correctly classified under-specified empirical output does not make the selected-scope gate fail. The gate fails when such an item is unrecorded or overstated, when a formalizable subclaim around it is missed, or when a selected mathematical target remains open.


# Completion checklist

Before finishing, verify every box:

## Source and scope

- [ ] Exact edition verified and recorded.
- [ ] Entire chapter body read, with footnotes affecting assumptions checked.
- [ ] Every named result inventoried.
- [ ] Every numbered equation inventoried.
- [ ] Every Problem, exercise, and Appendix solution row is either recorded as selected/formalized or given a concise unselected/deferred/benchmark/skip status.
- [ ] Core/comprehensive/benchmark mode recorded.
- [ ] `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md` was read first, the assigned split's section of `split_primary_contracts.md` was read, and `chapter_index.md` was used as the lookup table.
- [ ] The implementation and any cross-split placeholders respect the assigned split's ownership and the shared merge protocol.
- [ ] Source proof status recorded for selected imported or nontrivial claims.
- [ ] Algorithms and experiments split into formalizable subclaims, computed quantities, analysis-only objects, and empirical outputs when relevant.

## Selection quality

- [ ] Precise prose claims were considered, not ignored.
- [ ] Empirical and machine-specific material was excluded from core scope.
- [ ] Qualitative claims were not turned into invented theorems.
- [ ] Terminology-only material was skipped unless needed.
- [ ] Symbolic examples and fixed numerical examples were distinguished.
- [ ] Cross-chapter foreshadowing was identified.
- [ ] Benchmark candidates were separated from core work.

## Library and architecture

- [ ] Repository and Mathlib searched before new definitions or proofs.
- [ ] Existing declarations reused where appropriate.
- [ ] No duplicate parallel API was introduced without justification.
- [ ] Dependency graph is acyclic and matches the chapter boundary.
- [ ] Source labels and index translations are correct.
- [ ] Foundation feasibility gate completed for hard selected targets.
- [ ] External proof sources and route choices recorded when local foundations were missing.
- [ ] Public repository navigation updated only where required.
- [ ] After each small milestone or completed cycle with a successful relevant build, the intended tracked work was committed, merged with latest `origin/main`, rebuilt if the merge changed the tree, and pushed to the branch and `main` before starting the next cycle.

## Proof quality

- [ ] All selected declarations compile.
- [ ] No `sorry`, `admit`, or new global `axiom` remains.
- [ ] No target or equivalent missing theorem is smuggled in as a hypothesis.
- [ ] Necessary domain and nonzero assumptions are explicit.
- [ ] Statements preserve the source's meaning.
- [ ] Proofs are maintainable and use existing library results.
- [ ] `#print axioms` checked for final selected theorems when practical.
- [ ] High-probability claims prove the event probability rather than assume it.
- [ ] Implementation-facing floating-point claims account for all modeled computed quantities and rounded operations.
- [ ] Exact, simplified, and asymptotic bound descriptions agree and are non-vacuous when such descriptions are present.
- [ ] No weaker subtheorem or conditional transfer is mislabeled as closing a stronger source claim.

## Reporting

- [ ] Completed targets listed with Lean names and files.
- [ ] Reused results listed.
- [ ] Skipped items have reason codes.
- [ ] Deferred items name their dependency or destination.
- [ ] Benchmark candidates listed separately.
- [ ] Verification commands and results recorded.
- [ ] Genuine ambiguities or blockers reported honestly.
- [ ] Open selected-scope items remain in the not-proved ledger.
- [ ] Proof-source and bottleneck ledgers are present when triggered.
- [ ] Hidden hypotheses were classified and suspicious artifacts resolved or reported.
- [ ] Weak components received two consecutive clean checks.
- [ ] Empirical source outputs record missing machine details and any replacement theorem.
- [ ] Optional theorem PDF or note, if generated, matches Lean and was textually and visually inspected.

# Expected final response to the user

After modifying the repository, respond with:

1. a short statement of what was formalized in the selected mode;
2. the main Lean theorem or corollary names;
3. the files changed;
4. the build, test, placeholder-scan, and relevant axiom-check results;
5. the most important skipped, empirical, deferred, and benchmark categories;
6. the status of open selected-scope rows and any active bottleneck;
7. a concise hidden-hypothesis and weak-component summary when relevant;
8. the external proof sources used and whether each was formalized, advisory, rejected, or still open when proof-source acquisition was triggered; and
9. a link or path to the chapter decision report and any generated theorem note or PDF.

Keep the response concise when the report contains the detail. Do not claim full chapter coverage if a selected target remains unproved, and do not treat correctly classified empirical output as an unproved mathematical theorem.
