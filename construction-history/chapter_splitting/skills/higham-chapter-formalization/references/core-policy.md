# Core Policy and Invariants

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->


## Contents

- Higham Chapter Formalization
- Governing policy
- Problems and exercises policy
- GPT Pro Oracle Protocol
- Parallel formalization coordination documents
- Default mode and optional modes
- Required inputs and edition verification
- Key terms
- Non-negotiable principles
- Mandatory milestone synchronization

# Higham Chapter Formalization

Use this skill to turn one supplied chapter of the Higham book into a reviewable Lean/Mathlib contribution. The default objective is **not** to encode every sentence. The default objective is to formalize the chapter's important, precise mathematical content and every dependency needed for that content, while avoiding work on empirical demonstrations, machine anecdotes, vague prose, and glossary-only terminology.

This repository-local copy is intentionally stored under the ignored
`chapter_splitting/skills/higham-chapter-formalization/` tree so it can be used
as the offline project policy source without being staged or pushed. Do not
stage, commit, or push this local skill copy unless the project explicitly
changes that policy.

Build-cycle sync guard: every successful build/check cycle is an immediate
commit/merge/push stop point. After any coherent focused Lean check, target
build, full build, documentation check, inventory validation, or merge rebuild
passes, stop proof work; stage only intended tracked files; commit if there are
tracked milestone changes; fetch and merge latest `origin/main`; rebuild if the
merge changes tracked files; push the branch and update/push `main`; only then continue. This is
mandatory even for small milestones, recent syncs, or multi-day runs.

The required result is:

1. compiling Lean code for the selected mathematical content;
2. end-to-end proofs with no gaps disguised as assumptions;
3. a complete source inventory showing what was formalized, reused, skipped, deferred, or marked as a benchmark candidate;
4. dependency, source, and audit records proportionate to the difficulty of the selected targets; and
5. a concise completion report.

For routine algebraic chapters, the inventory and report may be enough. For hard imported results, high-probability theorems, implementation-facing floating-point results, or repeated blockers, also maintain the specialized ledgers and audits required below.

## Governing policy

Apply these rules in this order:

1. Follow the user's explicit instructions for the current task.
2. Follow repository-local instructions such as `AGENTS.md`, contribution guides, naming conventions, and the existing file architecture.
3. Follow this skill.
4. Follow the book's mathematical intent, translating it into idiomatic Lean rather than imitating printed notation literally.

### Problems and exercises policy

End-of-chapter `Problem` items, exercises, and Appendix solution rows are
optional selected targets rather than forbidden material. Formalize them when
the current user selects them, benchmark/comprehensive mode selects them, or
they are useful precise mathematical targets for the current goal. When
selected, handle them like any other source-facing target: use concise source
traceability, search before defining, prove end to end, and do not add solved
or unsolved placeholders. When unselected, the chapter inventory may record
only the source identifier, location, and concise deferred/benchmark/skip
status. Do not hide a Problem solution as an anonymous infrastructure lemma; if
a body theorem needs it, select and prove the dependency explicitly or keep the
body theorem open.

When the source meeting contains both tentative early comments and a later consensus, use the later needs-based consensus. In particular, do **not** interpret an early suggestion to formalize every notation item as a mandate to build a glossary or reproduce the book's typesetting conventions.

### Scope of the advanced procedures

The needs-based Higham policy and the selected mode govern all imported workflow guidance:

- A broad continuation rule applies only to targets inside the selected `core`, `comprehensive`, or `benchmark` scope. It does not enlarge core scope to every sentence, experiment, or historical output.
- Requirements written for a different repository, paper, or RandNLA project apply only when the current repository or user explicitly adopts them. In particular, do not inherit project-specific probability, documentation, or file-layout conventions automatically.
- A theorem PDF, README update, lookup example, or dedicated ledger file is mandatory only when requested, required by repository practice, or triggered by the complexity rules in this skill.
- When two auxiliary procedures conflict, choose the one that preserves source fidelity, end-to-end proof, the repository's conventions, and the main needs-based selection policy.

## GPT Pro Oracle Protocol

When blocked on a difficult theorem after serious local work, Codex may consult
GPT Pro through Chrome at chatgpt.com. If the account exposes a `GPT-5.5` or
equivalent high-reasoning model selector, use that model for oracle questions;
otherwise use the strongest available GPT Pro reasoning model.

Use the oracle only for:

- theorem-statement sanity checks,
- source-bound comparison,
- proof planning,
- identifying missing intermediate lemmas.

Do not paste secrets, credentials, private notes, or unnecessary full
documents; send only the minimal mathematical context, statement, hypotheses,
and sticking point. Treat the oracle answer as advice only. Verify every
adopted claim against the source text and Lean. An oracle answer never closes a
source row by itself.

Log every oracle consultation with:

- theorem name,
- reason for consultation,
- oracle route/model,
- prompt summary,
- answer summary,
- what was adopted,
- Lean/source verification result.

## Parallel formalization coordination documents

**Assigned partition:** current setting is Split 4 of 4. If the current user or
launcher provides `SPLIT_NUMBER`, use that split instead.

This project is carried out in four parallel splits. Before building a chapter inventory, designing contracts, or writing Lean code, each Codex agent must locate and consult these shared planning documents. Their contents must remain in those documents rather than being copied into this skill.

Read and use them in this order:

1. Read `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md` in full first. Use it for the shared split mechanism, split boundaries, dependency and placeholder protocol, contract rules, cross-split imports, merge plan, and chapter-by-chapter skeleton.
2. Identify the assigned split, then read that split's complete section in `split_primary_contracts.md`. Use it for the exact split-owned primary labels and local equation ledger. Use any problem ledger or Appendix A ownership ledger as a coordination list: selected Problem/solution rows may be formalized, and unselected rows may be recorded concisely.
3. Use `chapter_index.md` as the project-wide lookup table for chapter sections, source locations, labels, numbered equations, and problem or solution numbers.

The planning documents govern parallel ownership and coordination; this skill governs content selection, proof quality, audits, and reporting. The rendered book PDFs remain the source of truth for exact mathematical statements. If the files are stored under a repository subdirectory such as `planning/`, locate them by these exact filenames and follow the repository's paths. Do not start work until the assigned split and owned source items are known.

## Default mode and optional modes

### Core mode - default

Formalize named results, important numbered equations, precise symbolic claims
from the chapter body, and only the definitions and infrastructure required by
them. End-of-chapter Problems and exercises are optional in default core mode:
formalize them when selected by the user or when they are the most useful
precise mathematical target; otherwise record a concise unselected status.

### Comprehensive mode - only when explicitly requested

After the core pass compiles, revisit additional precise symbolic claims that were not needed by a core theorem. The exclusions for empirical, machine-specific, qualitative, editorial, and literature-review material still apply.

### Benchmark mode - only when explicitly requested

Formalize algorithms and imported results needed to compare methods or measure formalization effort, even when the book introduced them only through a numerical example. Keep benchmark work separate from the core chapter-completeness accounting.

If the prompt merely says "formalize Chapter X", use **core mode**.

## Required inputs

At minimum, locate or obtain:

- the chapter source, preferably the original PDF pages plus extractable text;
- the exact book edition;
- the chapter number and title;
- the Lean repository and its current toolchain; and
- any existing formalization of earlier chapters or shared numerical-analysis infrastructure.

Useful optional inputs include a chapter page range, previous inventories, issue trackers, and benchmark requirements.

### Edition verification is mandatory

Do not assume the edition from a filename. Verify it from the title page, copyright page, chapter numbering, equation numbering, or repository metadata. Record the edition in the inventory and report. Do not mix page numbers, theorem labels, or equations from different editions.

If the edition remains ambiguous and the ambiguity changes the mathematical content or numbering, ask one targeted clarification before coding. Continue with unambiguous repository inspection while waiting.

## Key terms used by this skill

- **Core target**: a declaration that the chapter itself presents as mathematically important, such as a named result, a significant equation, a precise definition, or precise body prose.
- **Dependency**: a definition, lemma, structure, notation bridge, or imported result required to state or prove a core target.
- **Precise claim**: a statement whose domain, assumptions, quantifiers, and conclusion can be translated without inventing a threshold, constant, probability model, or meaning for qualitative language.
- **Symbolic example**: a parameterized or general mathematical example, such as a matrix depending on `ε`, whose conclusion is an exact identity, inequality, or theorem.
- **Fixed numerical example**: a particular vector, matrix, decimal input, calculator output, or machine run used to illustrate behavior.
- **Empirical claim**: a claim supported by computed outputs, tables, plots, timings, named hardware, or observations such as "we find" or "typically" rather than by a stated proof.
- **Educational foreshadowing**: an early informal use of a theorem whose full definition or proof is given in a later chapter.
- **End-to-end proof**: a proof using only explicit source assumptions, established earlier declarations, or trusted library theorems. It does not assume the target or an equivalent imported claim merely to make the file compile.
- **Source proof status**: whether the book supplies a complete proof, a proof sketch, a citation-only justification, or no proof for a selected claim.
- **Implementation-facing theorem**: a theorem presented as describing an algorithm actually computed in inexact arithmetic, rather than only an exact reference object or an abstract transfer principle.
- **Computed quantity**: an object the modeled algorithm forms, stores, normalizes, transforms, or uses after input acquisition.
- **Analysis-only object**: an exact reference object used only in the proof and not computed by the modeled algorithm.
- **Fully specified computation**: a concrete computation whose inputs, operation order, arithmetic format, rounding behavior, exceptional cases, relevant library routines, randomness, and output interpretation are specified well enough to define one mathematical execution.
- **Empirical source output**: a reported machine result lacking enough implementation detail to define a unique computation.
- **Mathematical phenomenon**: a precise, machine-independent theorem or mechanism illustrated by an experiment.
- **Open selected-scope row**: an inventory or not-proved item that remains required by the current mode but is not yet closed by a matching Lean theorem.
- **Bottleneck**: a selected-scope target that repeatedly fails for the same missing foundation or proof route.
- **Red bottleneck**: a bottleneck that survives two focused passes with the same missing foundation; downstream and adjacent work must then freeze.
- **Weak component**: a theorem, proof bridge, ledger classification, or documentation claim that is especially prone to hidden assumptions or overstatement and therefore requires repeated independent audit.

## The non-negotiable operating principles

1. **Inventory before implementation.** Read the whole chapter and classify its contents before committing to a formalization plan.
2. **Needs-based first pass.** Start from core theorem-level content and backtrack to dependencies.
3. **Repository-first and Mathlib-first.** Search before defining or reproving.
4. **Precise and symbolic beats empirical and numerical.** Formalize exact general mathematics; skip observed machine behavior by default.
5. **A precise prose claim can be a theorem.** Do not restrict attention to labels or display equations.
6. **A numbered equation is a strong signal, not an unconditional command.** Inventory every numbered equation and formalize it by default unless a documented exclusion applies.
7. **Definitions are demand-driven.** Formalize semantic definitions that are required or mathematically central; skip terms that only name an informal idea.
8. **Prefer end-to-end proofs.** Do not hide an unproved mathematical result in a hypothesis.
9. **Defer foreshadowing to its real treatment.** Formalize the lightweight foundational definition now if useful, but place the full theorem where the book proves it.
10. **Every omission must be visible.** A skipped or deferred item needs a reason in the inventory.
11. **Run a feasibility gate before hard downstream work.** A missing foundational theorem becomes the active target; it is not converted into a convenient hypothesis.
12. **Continue dependency-first within the selected scope.** A failed final gate is a work queue for open selected-scope rows, not a reason to polish adjacent material or stop at a vague diagnosis.
13. **Account for every modeled computation.** An implementation-facing floating-point theorem must model or explicitly leave open every computed quantity and rounded operation on its chosen algorithm path.
14. **External literature guides proofs but does not replace them.** A citation can determine a Lean target and proof route, but only a local theorem or trusted imported library result closes the row.
15. **Corrections are regression tests.** When a user or audit finds an irrelevant result, hidden hypothesis, weak statement, or documentation mismatch, update the theorem surface, inventory, and report together and prevent recurrence.
16. **Audit fragile results more than once.** Probability, stability, perturbation, floating-point, transfer, and documentation claims require independent clean checks before completion.
17. **Synchronize every successful milestone.** After every small milestone or completed cycle with a successful relevant build, commit the intended tracked work, fetch and merge the latest `origin/main`, rebuild if the merge changes the tree, and push the branch and `main` before starting the next cycle. Treat every passing cycle as a mandatory sync point, not optional cleanup. Do not keep a local backlog of passing build milestones.

## Mandatory milestone synchronization

For every small formalization increment, dependency row, proof cycle,
documentation cycle, inventory update, or chapter-loop cycle that passes the
relevant Lean build:

1. Stage only the intended tracked Lean, documentation, and inventory files for that milestone.
2. Leave local-only policy material, including `chapter_splitting/`, `References/`, and this repository-local skill copy, unstaged unless the user explicitly says otherwise.
3. Commit the milestone before continuing to the next proof cycle.
4. Run `git fetch origin` and merge the latest `origin/main` into the working branch.
5. If the merge changes any tracked files, rerun the relevant build, and run the full build when the changed surface is broad or shared.
6. Push the branch after the successful post-merge state.

This is the default long-running workflow, including multi-day chapter runs.
Do not continue formalization after a passing cycle until the current branch is
committed, merged with current `origin/main`, rebuilt as needed, and pushed to the branch and `main`. Do not
accumulate multiple successful build-passing milestones in the working tree.
Do not substitute an earlier "already up to date" check for the post-build sync;
the merge gate is repeated after every successful cycle.

Hard invariant: the working branch must stay current with `origin/main`.
Before beginning any new proof, documentation, inventory, or cleanup cycle,
run `git fetch origin` and merge latest `origin/main` if the branch is not
already known current from the immediately preceding sync gate. If that merge
changes any tracked file, run the relevant build, use the full build for broad
or shared changes, and push the merge to the branch and `main` before doing any further work.

No exceptions: every successful build or check cycle from now on is a
synchronization trigger. A successful cycle includes a successful focused
`lake env lean`, target `lake build`, full `lake build`, documentation or
inventory validation, merge rebuild, or equivalent repository check that
validates a coherent proof, documentation, inventory, merge, or cleanup
increment. After such a success, stop immediately; stage only the intended
tracked files, commit them if there are tracked milestone changes, fetch and
merge latest `origin/main`, rebuild if that merge changes tracked files, and
push branch and `main` before starting the next cycle. If there are no tracked milestone changes,
skip the empty commit but still complete the fetch/merge/rebuild-if-needed/push
gate. Do not continue because the chapter is unfinished, the previous sync was
recent, the change is small, the successful build was "only focused", there are
no Lean changes, or the branch was already current earlier in the day.

Operational stop condition: after any successful check or build that closes a
coherent cycle, the next work item must be the synchronization loop: commit,
fetch, merge latest `origin/main`, rebuild if needed, and push branch and `main`. Do not inspect
the next theorem, start another proof attempt, or make additional Lean/doc edits
until that loop is complete.
