# Verification, Audits, and Blockers

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->


## Contents

- Phase 7 verification
- Milestone synchronization
- Hidden-hypothesis audit
- Probabilistic audit
- Floating-point and computed-quantity audit
- Repeated weak-component audit
- Adversarial and cleanup audit
- Optional theorem-note or PDF audit
- Precision audit
- Handling ambiguity and blockers

## Phase 7: Verify and audit the formalization

At minimum:

1. Compile every changed Lean file.
2. Run the repository's relevant build or test target.
3. Search touched files for unfinished proofs, new axioms, unsafe placeholders, and accidental experimental declarations.
4. Run `#print axioms` for each final selected theorem when practical.
5. Confirm imports are no broader than necessary.
6. Confirm all source labels, theorem statements, and inventory decisions against the rendered source.
7. Confirm the code reuses current repository definitions rather than duplicates.
8. Check one-based/zero-based index translations, dimensions, row/column orientation, denominators, and domain restrictions.
9. Confirm every open selected-scope row remains visible in the not-proved ledger and every skipped empirical row remains visible in the source inventory.
10. Distinguish new warnings from pre-existing baseline warnings.

Typical final checks, adapted to the repository, include:

```bash
git status -sb
git diff --stat
git diff --check
rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" path/to/touched/files
lake env lean path/to/Changed.lean
lake build
lake env lean examples/LibraryLookup.lean  # when this repository uses it
```

Use repository-specific commands when they differ. A text scan is an audit prompt, not proof that every matched token is invalid; inspect each new match. Do not claim completion if a selected declaration does not compile or an open selected-scope row remains.

### Milestone synchronization

For this Higham formalization project, a milestone is not finished when Lean
first builds locally. A milestone is finished only after the validated tracked
changes have been committed, merged with the latest `origin/main`, rebuilt if the
merge changed the tree, and pushed to the branch and `main`.

Use a constant main-merge discipline: whenever a small milestone, dependency
row, proof cycle, documentation cycle, or chapter-loop cycle reaches a
successful relevant build, stop formalization work and synchronize with
`origin/main`
before starting any new milestone.

Every successful build that closes a small cycle is a synchronization trigger.
Do not start the next proof, dependency, documentation, or inventory cycle
before committing the passing tracked changes, merging current `origin/main`,
rebuilding if needed, and pushing branch and `main`.

Treat synchronization as a mandatory part of every completed work cycle, not a
chapter-end cleanup step. Every time a small milestone, dependency row, proof
branch, documentation update, or chapter-loop cycle reaches a successful
relevant build, immediately stop further formalization work and run the full
sync loop for tracked milestone work:

Interpret this as a constant synchronization rule: each successful focused
Lean check, module build, or full build that closes a meaningful cycle triggers
the sync loop before any new formalization work starts.

The sync loop is the immediate next action after the successful cycle. Do not
use a passing build as a checkpoint and then continue locally; complete the
commit, latest-main merge, rebuild-if-needed, and push branch and `main` first.

1. Inspect `git status` and stage only intended tracked milestone changes.
2. Commit the validated tracked changes.
3. Run `git fetch origin` and merge the latest `origin/main` into the working branch.
4. If the merge changes the working tree, rerun the relevant Lean build.
5. Push the current branch.

Apply this loop even when the chapter still has open selected-scope rows: a
passing build milestone is synchronized before the next dependency row,
proof branch, or chapter cycle starts. Do not batch several successful
milestones locally when a commit, merge with `origin/main`, rebuild if needed, and
push branch and `main` can be performed immediately.

If a build succeeds after a small cycle, do not continue coding first. Commit,
merge `origin/main`, rebuild when necessary, and push branch and `main` before starting the next cycle.

Do not start the next milestone while validated tracked work remains only on
the local machine. Do not push a milestone with a failing build, unresolved
conflicts, or uncommitted tracked milestone changes. If local-only ignored
source artifacts changed during the milestone, leave them unstaged unless the
project explicitly reverses that policy. This includes `References/`,
`chapter_splitting/`, and this local skill copy.

### Hidden-hypothesis audit

List every hypothesis of every final selected theorem and classify it as `source assumption`, `domain assumption`, `floating-point/model validity`, `reused theorem assumption`, or `suspicious proof artifact`.

Answer explicitly:

1. Is the target conclusion or an equivalent missing theorem assumed?
2. Is a concentration, stability, unbiasedness, variance, perturbation, or correctness result assumed when it should be proved?
3. Is exact arithmetic assumed for a quantity that the theorem presents as computed?
4. Does a conditional, expectation, deterministic, transfer, or different-object result falsely close a stronger source row?
5. Does the report or optional PDF say more than the Lean theorem proves?

Any affirmative answer keeps the final gate open until corrected or the source row is honestly reclassified.

### Probabilistic audit

For each selected probabilistic theorem, verify:

- the probability space or distribution;
- the event and all random variables;
- deterministic parameters and support/measurability assumptions;
- the exact lower probability bound;
- the local theorem proving each concentration or tail step; and
- the absence of an unproved `goodEvent`, `boundedEvent`, or equivalent hidden event.

A high-probability source row fails the gate if concentration is only assumed.

### Floating-point and computed-quantity audit

For each selected floating-point theorem, verify:

- the exact algorithm and computed algorithm are both identifiable;
- every rounded operation and computed quantity on the advertised path is listed;
- exact-operation conventions are explicit and justified;
- local error lemmas are instantiated rather than replaced by a generic unexplained certificate;
- dimension and sample-count dependence is visible;
- indexed notation genuinely depends on its displayed indices; and
- the final exact bound, simplified interpretation, and non-vacuity claim agree.

If a concrete computation routine is not formalized, do not describe that path as fully implementation-facing.

### Repeated weak-component audit

Automatically mark as weak:

- final theorems with more than three nontrivial hypotheses;
- any probability, concentration, expectation, floating-point, stability, perturbation, or transfer theorem;
- adapters around existing results;
- theorem statements changed during implementation;
- new distributions, events, norm bridges, or error budgets;
- places where exact and inexact arithmetic coexist;
- source rows claimed to close a numbered equation or major theorem; and
- inventory, not-proved, bottleneck, report, or optional PDF claims about completion.

Use a ledger such as:

```markdown
| Component | Why weak | First check | Fix/justification | Second independent check | Third check if needed | Evidence | Status |
|---|---|---|---|---|---|---|---|
```

Check each weak component from at least two independent angles: Lean theorem type and axioms, mathematical comparison with the book, documentation comparison, and repository-reuse search. A component passes only after two consecutive clean checks. If it fails twice for the same reason, invoke the bottleneck protocol.

### Adversarial and cleanup audit

Act as a skeptical reviewer and look for:

- prose stronger than Lean;
- a theorem name suggesting a different algorithmic object;
- expectation described as high probability;
- deterministic described as randomized;
- a floating-point path omitting a computed operation;
- irrelevant but true results promoted as core;
- a duplicated library theorem;
- an open row that disappeared without a matching Lean theorem;
- misleading indexed or dimensional notation; and
- unused helpers left from a failed route.

Remove unused or misleading material. If risky to delete, quarantine it in a clearly experimental location and do not count it as a chapter result. Update repository navigation documents only when new public declarations or repository practice require it.

### Optional theorem-note or PDF audit

Generate a theorem-style PDF or standalone mathematical note only when the user requests it or the repository requires it. Build it only after the corresponding Lean results compile.

The note should contain, as appropriate:

1. a title and short abstract;
2. notation and algorithm or equation setup;
3. mathematical definitions;
4. readable theorem, lemma, and corollary statements;
5. compact Lean-provenance blocks after the mathematics;
6. a `Hypotheses and Scope` section;
7. a `What Is Not Proved` section generated from the live ledger when limitations remain; and
8. an optional file map.

Keep Lean names subordinate to the mathematics. Every probability statement must identify its event and failure probability; every floating-point statement must identify the rounded path and perturbation budget. Do not overstate conditional or partial results. Include a concise proof-dependency outline only when requested or customary; do not invent proof sketches unsupported by Lean.

When a PDF is produced, compile it with a halting-on-error mode, extract text, render representative pages, and visually inspect theorem readability, long identifiers, cross-references, and margins.


# Precision audit

Before accepting any statement as a target, answer all of these:

1. What are the quantified variables?
2. What are their types and dimensions?
3. What assumptions are explicit or mathematically necessary?
4. Are all denominators nonzero?
5. Is the norm specified?
6. Is the indexing convention clear?
7. Does `min` actually exist, or is an infimum intended?
8. Does approximate notation have a defined semantics?
9. Is the conclusion exact enough to be true or false?
10. Can the statement be formalized without inventing a constant or threshold?
11. Is it a theorem, a model assumption, a definition, or merely an observation?
12. Is a later theorem being used prematurely?
13. If probabilistic, what are the distribution, event, random variables, and exact probability guarantee?
14. If implementation-facing, which quantities are computed and which are analysis-only?
15. Does the source prove the claim, sketch it, cite it, or omit it?
16. Does a proposed theorem close the exact source claim rather than only a transfer, expectation, deterministic subcase, or different object?
17. Are all asymptotic regimes and dimension dependencies explicit?

If the answer to 9 or 10 is no, skip or defer rather than guessing. If 13 through 17 reveal a missing foundation, keep the claim selected but make the missing foundation the active target.


# Handling ambiguity and blockers

Do not ask broad questions that the chapter or repository can answer. Continue all unambiguous work.

Ask a targeted clarification when:

- the edition changes the statement;
- the source formula is unreadable after inspecting the rendered page;
- two non-equivalent formalizations are both plausible;
- the repository has conflicting conventions; or
- a requested scope mode is genuinely unclear and would multiply the work substantially.

When blocked by a missing deep dependency:

1. record the exact selected target and dependency;
2. search the repository and Mathlib again with alternate terminology;
3. inspect the book's proof, citation, and later cross-reference;
4. run proof-source acquisition when the source is incomplete;
5. update the feasibility table and choose a local, shared-module, later-chapter, or route-choice disposition;
6. make the smallest meaningful missing dependency the next Lean target;
7. complete independent selected targets without hiding the blocker; and
8. report the blocker precisely.

If the same blocker survives repeated passes, create the bottleneck ledger and obey the red-bottleneck protocol. Ask the user only for a genuine mathematical choice that changes the theorem, not for questions answerable from the source or repository.

