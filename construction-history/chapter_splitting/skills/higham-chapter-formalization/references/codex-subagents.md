# Codex Parallel Subagents

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push unless updating the skill itself. -->

Read this only when the current user, launcher prompt, or orchestration prompt
explicitly enables Codex parallel subagents or asks for subagent/delegated work.

## Activation

- Do not infer subagent permission from requests for speed, depth,
  thoroughness, or proof-completion persistence alone.
- When enabled, use subagents opportunistically for independent work that can
  proceed in parallel with the main agent's immediate next step.
- The main agent remains responsible for reading `SKILL.md`, all required
  policy references, planning documents, source material, and final verification.
  Do not outsource interpretation of controlling instructions.

## Good Subagent Work

Prefer explorer subagents for bounded, independent questions:

- search the repository and Mathlib for existing declarations around a target;
- cross-check source coverage, equation labels, selected Problem/exercise rows,
  and benchmark identifiers against planning ledgers and reports;
- audit a theorem surface for hidden target-equivalent hypotheses;
- inspect lookup docs, examples, and report text for consistency with Lean names;
- run independent hygiene or axiom-audit checks when the main agent can continue
  unrelated work.

Use worker subagents only for disjoint write scopes:

- assign explicit file or module ownership;
- prefer helper modules, isolated documentation, or examples over a shared
  chapter file;
- tell workers they are not alone in the codebase and must not revert or
  overwrite others' edits;
- require workers to report changed file paths, commands run, and any remaining
  failures.

## Forbidden Delegation

Do not delegate:

- final selected-scope gate decisions;
- main-sync queue ownership, sync-lock acquisition, commits, merges, or pushes
  to ordinary proof/search subagents;
- credential handling, Telegram sending, or oracle calls;
- edits to the same file from multiple workers unless the main agent explicitly
  serializes and integrates the patches;
- proof closure by prose summary alone.

## Main-Agent Duties

Before spawning, make a short plan that identifies:

1. the immediate critical-path task the main agent will do locally;
2. the independent sidecar tasks suitable for subagents;
3. each worker's write scope, if any.

After subagents return:

- inspect all claims against file paths, Lean declaration names, and source
  labels;
- review any uploaded changes before integration;
- run the relevant focused Lean checks, builds, placeholder scans, and practical
  axiom audits locally in the authoritative worktree;
- update reports and ledgers yourself;
- perform the mandatory milestone sync yourself after a successful cycle, or
  hand the committed milestone to a dedicated isolated sync worker/CI queue
  when the top-level async sync exception is explicitly active.

Subagent output is evidence, not completion. A selected source row closes only
when the main agent verifies a matching compiled Lean declaration and records
the result in the chapter report or ledger.
