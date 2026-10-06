# Early construction history of NumStability

Evidence for the first-pass, correction and scope-decision passages of
Chapter 6. Every item was checked on 2026-10-06 against its source:

- Git: the `lean-numerical-stability` repository (all branches), with read-only `git log` /
  `git show`.
- Codex history: the local Codex CLI history database `thread_history_1.sqlite`, table `thread_items`,
  opened read-only. Thread ids are shortened to their first 8 characters.
  Times are UTC. Quotes are verbatim and kept short.
- Local planning material: the ignored `chapter_splitting/` folder of the
  library working tree, and the project memory in `project-memory/` (next to
  this file).

The March 2026 Claude Code transcripts and the very first prompt are not
preserved on this machine.

## 1. First pass (March 2026)

| Date | Evidence | Content |
|---|---|---|
| 2026-03-03 | commit `5bede9ad1a` | "Initial commit" |
| 2026-03-03 | commit `db37be8f9c` | "defined FP model" |
| 2026-03-20 | commit `414f3eb0a2` | first commit tagged `Co-Authored-By: Claude` |
| 2026-03-20 | commit `781ded4867` | "fix: match book gamma(n-1) bound for recursive summation" |
| 2026-03-22 to 03-31 | commits `b3736e72c1` (Ch9) ... `030f246f5d` (Ch22) | Chapters 7-22, usually one commit per chapter |
| 2026-03-26 | commit `c20987397c` | "formalize Higham Ch7 ... (24 results, 0 sorry)" |
| 2026-03-27 | commit `69901d1049` | message ends "0 sorry, 0 warnings"; the diff adds `True -- placeholder` fields |

Size of the library (counted with `git ls-tree` and `git show`): at
`caddd4ffb0` (2026-03-18, "chapter 3 complete?") 14 `.lean` files and 1,403
lines; at `030f246f5d` (2026-03-31) 95 `.lean` files and 23,799 lines.
Commits up to 2026-03-19 (`4daeed165b`) carry no `Co-Authored-By` agent
trailer; from 2026-03-20 Claude-tagged commits add the remaining chapters.

Source edition: `References/Chapter11.pdf` in commit `c3375505cc`
(2026-03-20) begins "Chapter 11 / Iterative Refinement". In the second
edition (ISBN 9780898718027, `References/1.9780898718027.ch12.pdf`),
Iterative Refinement is Chapter 12 and Chapter 11 is "Symmetric Indefinite
and Skew-Symmetric Systems". The README at `030f246f5d` states "2nd ed.,
SIAM, 2002". The March chapter commits follow the older numbering (e.g.
"Ch13: matrix inversion", "Ch18 (QR factorization)").

Partial source: `References/Chapter01.pdf` (commit `549b696aec`,
2026-03-10) has 6 pages. Commit `e8d1e9cf93` (2026-06-14) adds
`docs/CHAPTER01_FORMALIZATION_LEDGER.md` ("Status: PASS for the formalizable
mathematical content in the local six-page excerpt") and
`docs/CHAPTER01_FULL_FORMALIZATION_LEDGER.md` for the 38-page
`References/Chapter01_full.pdf` ("Status: **INCOMPLETE for the full local
PDF**"). The chapter skill of `db57023150` has the heading "Edition
verification is mandatory" (`SKILL.md`, line 82).

Agent memory of that period, printed by Codex in thread `019dc8a2`
(2026-04-26 07:24): "Only formalize results that serve as reusable stepping
stones"; "The user doesn't need to formalize all of Higham".

Author's retrospective, thread `019f8427` (2026-07-21 10:16): "So the library
was initially built by just me. I did a first, initial pass of the whole
book"; "Claude/Codex were using a lot of hypothesis+assumptions when proving
theorems and not actually constructing end to end proofs"; "many parts of the
book that should have been formalized were glossed over by the AI"; "After
this we split the book in 4 Splits and 4 of us worked at the same time."

## 2. Detection of the problems

- Thread `019dc8a2`, 2026-04-26 07:15 (user): "I have built this project with
  Claude. Now I have switched to you."
- Same thread, 07:18 (Codex): theorem wrappers "whose key conclusion is
  supplied as a hypothesis and then returned".
- Same thread, 07:25 (Codex): results that "look like proved Higham theorems
  but are really 'assume the bound, return the bound' wrappers".
- Thread `019de2ef`, 2026-05-13 12:25 (user): "Look full one complete
  mathematical proofs in lean? Or are we scamming it?"
- Same thread, 12:44 (Codex): "the full rounded QR algorithm is not
  implemented as an executable FP algorithm".

- Commit `8691c7591e` (2026-05-18), `docs/AlgorithmInventory.md`: "There are
  no `sorry`, `admit`, or Lean `axiom` declarations"; Gaussian elimination/LU,
  QR, Cholesky, Gauss-Jordan, fast matrix multiplication and least-squares QR
  are listed under "Contract / Specification-Transfer Interfaces" (e.g. "no
  rounded Cholesky loop returning `R_hat`"; "QR least-squares stability is
  axiomatized as a structure").

## 3. Corrections decided by the author

- Thread `019de2ef`, 2026-05-18 12:20: "add implementations where they are
  missing. Do not change the error results."
- Same thread, 2026-05-26 22:33: "The goal is to back up those contracts with
  the actual algorithm implementations."
- Thread `019e698a`, 2026-05-29 14:07: "So whole library needs a repass. ...
  stop taking everything as a hypothesis."
- Same thread, 2026-06-02 15:49: "Fully prove all higham bounds exactly, no
  workarounds, no skips."
- Same thread, 2026-06-02 20:27: "There shouldn't be a \"safe\" version for
  everything. Just one version that is as general as possible".
- Same thread, 2026-06-11 15:31: "We should have a 1 to 1 formalization of
  every book premise."
- Same thread, 2026-06-23 08:06: "Match the book 100%. Don't make anything
  easier in the bounds".

## 4. Scope decisions and rejected ideas

- `project-memory/DECISION_LOG.md`, line 52: "avoid adding
  IEEE-specific assumptions to core modules"; line 89: "Use Mathlib As The
  Source Of Truth For Exact Norms"; line 123: "Prioritize Rectangular Real
  Matrices Before Complex Matrices".
- `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, line 28:
  "Do not spend formalization time on historical notes, prose-only warnings,
  MATLAB timing tables, figures, or numerical experiments".
- `chapter_splitting/skills/higham-chapter-formalization/SKILL.md`, line 122:
  "Skip or defer editorial prose, historical notes, ... glossary-only
  terminology, and later-chapter foreshadowing. Keep skipped/deferred
  decisions visible with reason codes."
- Same skill, `references/content-selection.md`, line 238: "Do not
  reconstruct an unspecified machine merely to match a printed number".
- Commit `db57023150` (2026-06-24), `.codex/skills/higham-chapter-formalization/SKILL.md`,
  line 29: "do **not** interpret an early suggestion to formalize every
  notation item as a mandate to build a glossary".
- Problems (exercises): thread `019ef4df`, 2026-06-26 07:14: "Problems should
  not be formalized at all. They should remain unproven, unsolved as that will be part of the benchmark process"; same
  thread, 2026-07-03 12:52: "Change of plan. You can formalize Problems if
  you want to."; `content-selection.md`, line 262: "no longer forbidden".

## 5. Instructions and skills over time

| Date | Evidence | Step |
|---|---|---|
| 2026-04-26 | commit `015d6c478d` | Codex project memory after the switch from Claude |
| 2026-04-27 | commit `a0620c161a` | "Record project decisions and remove Claude artifacts" (decision log) |
| 2026-05-29 | thread `019e698a`, 14:11 | "what are skills in Codex? Could creating one help with this repass?" |
| 2026-06-01 | thread `019e698a`, 15:14 | Codex creates the audit skill `lean-fp-stability-audit` |
| 2026-06-14 | commit `835db328d9` | "Export lean stability formalizer skill"; `SKILL.md`, line 15: "Treat user corrections as regression tests for the workflow." |
| 2026-06-24 | commit `db57023150` | chapter-formalization skill in `.codex/skills/` |
| 2026-06-24 | same commit, `SKILL.md`, line 58 | targets include "theoretical exercises" |
| 2026-07-22 | local Codex skill `numstability-library-reorganization/SKILL.md` (file creation time) | library reorganization skill |
| 2026-08-28 | commit `045daf280` | release `higham_v01` |
