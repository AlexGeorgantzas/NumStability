---
name: higham-chapter-formalization
description: Use when Codex is asked to read, inventory, or formalize a chapter of Higham's numerical analysis book in Lean/Mathlib, especially in the local four-way split project. Applies the project-local core-mode selection policy, split coordination, optional Problem/exercise handling, end-to-end proof discipline, milestone sync with main, and conditional audit workflow.
---
# Higham Chapter Formalization

This repository-local skill is the offline project policy source for Higham chapter formalization. It is intentionally stored under the ignored `chapter_splitting/skills/higham-chapter-formalization/` tree. Do not stage, commit, or push this skill, `chapter_splitting/`, or `References/` unless the user explicitly reverses that local-only policy.

The Markdown files are authoritative. Any `SKILL.pdf` in this local folder is only a non-authoritative export unless regenerated from the current Markdown.

Keep this `SKILL.md` as the always-loaded control file. Load the reference files in `references/` only when their routing condition applies; do not read every reference file by default.

If a pasted prompt, older note, or reference file conflicts with the hard invariants below, follow these hard invariants unless a higher-priority system/developer instruction or an explicit current user instruction says otherwise.

## Hard Invariants

- Default to **core mode** when the user says only to formalize a chapter. Comprehensive mode and benchmark mode require explicit user request.
- **Assigned partition: current setting is Split 4 of 4.** If the current user
  or launcher provides `SPLIT_NUMBER`, use that split instead. Before chapter
  work, read `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, then the assigned
  split's section of `split_primary_contracts.md`, then use `chapter_index.md`
  for lookup.
- The rendered book PDF is the source of truth for exact mathematical statements. Verify the book edition before relying on page, theorem, or equation numbering.
- End-of-chapter `Problem` items, exercises, and Appendix solution rows may be formalized when the current user selects them, when benchmark/comprehensive work selects them, or when they are useful precise mathematical targets. In default core chapter-completion mode they are optional, not required blockers. If selected, give them the same source-fidelity, proof, and no-placeholder treatment as body results; if not selected, record only enough inventory information to explain the omission.
- Inventory before implementation. Account for named results, numbered equations, precise prose claims, definitions, algorithms, empirical outputs, selected Problems/exercises, skipped/deferred rows, and benchmark identifiers according to the selected mode.
- Search the repository and installed Mathlib before defining or reproving anything. Reuse matching declarations directly, or add thin proved wrappers when source traceability helps.
- Prefer end-to-end proofs. Do not assume the target theorem, a concentration/stability/perturbation result, or an equivalent missing theorem merely to make a file compile.
- Do not introduce `sorry`, `admit`, new global `axiom`, `unsafe`, or opaque placeholders to close selected chapter work.
- Source-facing Lean declarations need concise source traceability: edition, chapter/section, page or label when available, and a short mathematical paraphrase. Do not paste long book text.
- Keep statements honest about their strength. A conditional transfer, expectation result, exact-arithmetic subcase, or theorem about a different object does not close a stronger source row.

## Mandatory Milestone Synchronization

Every successful build/check cycle is an immediate synchronization trigger. A successful cycle includes a focused `lake env lean`, target `lake build`, full `lake build`, documentation or inventory validation, merge rebuild, or equivalent check that validates a coherent proof, documentation, inventory, merge, or cleanup increment.

After any such success:

1. Stop proof/documentation work immediately.
2. Inspect `git status`.
3. Stage only intended tracked Lean, documentation, and inventory files. Leave `chapter_splitting/`, `References/`, this skill, and other local-only files unstaged.
4. Commit if there are tracked milestone changes.
5. Run `git fetch origin --prune` and merge latest `origin/main` into the working branch.
6. If the merge changes tracked files, rerun the relevant build; use a full `lake build` for broad or shared changes.
7. Push the working branch and update/push `main` to the same verified state so collaborators pulling `main` receive the update.
8. If there are no tracked milestone changes, skip the empty commit but still complete the fetch/merge/rebuild-if-needed/push gate before starting another cycle.

Do not batch multiple passing milestones locally. Do not inspect the next theorem, start another proof, or make extra edits after a passing cycle until this sync loop is complete.

### Isolated async sync exception

When the user explicitly enables coordinated parallel mode, CI/merge-queue mode,
or a dedicated sync worker, a successful milestone may be handed off
asynchronously only after the validated tracked changes are committed. The
sync worker must use a separate worktree, acquire the main-sync lock or CI/merge
queue, merge current `origin/main`, rebuild as required, and update `main` only
after verification succeeds.

The main agent may continue proof exploration during that wait only in a
separate speculative worktree or branch. Work in that speculative context is not
a finalized milestone until the sync worker reports success and the main agent
rebases or merges onto the verified `main` head. In a single shared checkout,
the normal immediate stop-and-sync rule still applies.

## GPT Pro Oracle Protocol

When blocked on a difficult theorem after serious local work, Codex may consult
GPT Pro through Chrome at `chatgpt.com`. If the account exposes a `GPT-5.5` or
equivalent high-reasoning model selector, use that model for oracle questions;
otherwise use the strongest available GPT Pro reasoning model.

Use the oracle only for theorem-statement sanity checks, source-bound
comparison, proof planning, or identifying missing intermediate lemmas. Do not
paste secrets, credentials, private notes, or unnecessary full documents; send
only the minimal mathematical context, statement, hypotheses, and sticking
point. Treat the answer as advice only and verify every adopted claim against
the source text and Lean. An oracle answer never closes a source row by itself.

Log every oracle consultation with theorem name, reason, oracle route/model,
prompt summary, answer summary, what was adopted, and Lean/source verification
result.

## Reference Routing

Load only the files needed for the current step:

- `references/core-policy.md`: Read when resolving a scope or policy conflict, when exact older wording matters, or before a final chapter-level policy audit.
- `references/parallel-agents.md`: Read before worktree creation, branch switching, builds, proof work, or sync when multiple agents, async sync, CI handoff, or a shared `main` coordination workflow is active. It routes to the detailed orchestration files under `references/parallel-orchestration/`.
- `references/parallel-orchestration/main-sync-queue.md`: Read before any coordinated or async milestone sync that can update `main`.
- `references/parallel-orchestration/agent-persistence-loop.md`: Read only for explicitly requested autonomous `proof-completion` runs that should continue through open selected-scope rows until PASS, allowed BLOCKED, or user stop/status request.
- `references/codex-subagents.md`: Read when the current user, launcher prompt, or orchestration prompt explicitly enables Codex parallel subagents or asks for subagent/delegated work.
- `references/workflow.md`: Read when starting or resuming a chapter, building the source inventory, designing theorem statements, planning dependencies, or implementing a new proof group.
- `references/content-selection.md`: Read before classifying source items or deciding `FORMALIZE_CORE`, `FORMALIZE_DEPENDENCY`, `FORMALIZE_PROBLEM`, `REUSE_EXISTING`, `DEFER`, `BENCHMARK_CANDIDATE`, or `SKIP`.
- `references/lean-modeling.md`: Read when designing definitions or theorem surfaces for vectors, matrices, norms, error measures, conditioning, floating-point models, probability, or factorizations.
- `references/verification-audits.md`: Read before verification, when working on probability/floating-point/stability/perturbation claims, when a hidden-hypothesis risk appears, or when a blocker repeats.
- `references/reporting.md`: Read when updating source coverage, not-proved/proof-source/bottleneck ledgers, theorem notes, chapter reports, or final user-facing completion summaries.

Single-agent compatibility: if the user is running one agent in a private
checkout with no shared branch, async sync, CI handoff, or shared `main`
coordination, do not require the launcher, worktree orchestration, hooks, or
parallel-agent references. Use the normal chapter workflow and milestone sync
rules.

## Default Chapter Workflow

1. Establish baseline: inspect repository state, instructions, coordination state if present, toolchain, imports, nearby files, and existing chapter infrastructure.
2. Verify the book edition and read the entire assigned chapter section before substantial Lean work.
3. Build the source inventory and classify every relevant item. For Problems/exercises/Appendix solution rows, either select them explicitly for formalization or record a concise unselected/benchmark/deferred status.
4. Search repository and Mathlib for every proposed concept or theorem.
5. Build a dependency graph and theorem-design table before main proof work.
6. Implement in small coherent proof groups, compiling incrementally.
7. Keep open selected-scope rows visible in the inventory or not-proved ledger; do not let related weaker theorems hide them.
8. Verify changed Lean files, hygiene scans, relevant builds, source labels, hidden hypotheses, and documentation claims.
9. After every successful cycle, run the mandatory milestone synchronization loop before continuing.
10. If coordinated parallel or async sync mode is active, use isolated
    worktrees, leases, and the main-sync queue/CI handoff before treating a
    milestone as finalized.

## Core Selection Summary

Formalize or reuse named mathematical results, important numbered equations, central precise definitions, precise body prose claims, and dependencies required by selected targets. Formalize precise symbolic examples when they expose a reusable mathematical phenomenon.

Skip or defer editorial prose, historical notes, qualitative claims, underspecified approximate statements, fixed numerical experiments, machine-specific outputs, figures/tables as artifacts, glossary-only terminology, and later-chapter foreshadowing. Keep skipped/deferred decisions visible with reason codes.

## Verification Summary

For selected final theorem surfaces, verify the Lean type against the source, inspect assumptions for hidden target-equivalent hypotheses, check practical axioms when appropriate, distinguish new warnings from baseline warnings, and keep documentation no stronger than Lean.

Fragile probability, floating-point, stability, perturbation, transfer, and documentation claims require the relevant audit reference and at least two independent clean checks before being treated as closed.

## Expected Final Response Shape

After repository-modifying formalization work, report concisely: what was formalized in the selected mode, main Lean declarations, files changed, verification commands/results, skipped/deferred/benchmark categories, open selected-scope rows or bottlenecks, hidden-hypothesis/weak-component status when relevant, external proof sources if used, and the chapter report path.

Do not claim full chapter coverage while selected-scope rows remain open. Correctly skipped empirical output is not an unproved theorem.
