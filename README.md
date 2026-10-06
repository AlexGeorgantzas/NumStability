# NumStability — thesis documentation

This branch holds the evidence that the thesis *Formal Proofs of Numerical
Stability in Lean 4* cites and that is not stored on the other branches of
this repository. It has no history and no relation to the `library` branch,
which it does not change.

Other evidence cited by the thesis lives on the other branches:

- `tiered_benchmark_30`: the thirty-task fixed-target study, and the source of
  the `higham_v01` library (commit `045daf280`) under
  `historical-library-snapshot/`.
- `ten_task_benchmark`: the ten-task formalize-and-prove study.
- `library`: the library snapshot `45813a95d` used by the ten-task study.

## Contents and origin

| Path | Content | Origin |
|---|---|---|
| `library-audit/higham_v01-045daf2/` | Static architecture check, declaration dependency graph, cohesion metrics, public-interface check, build and timing records of `higham_v01` | thesis repository, `sources/library-audit/` at commit `bd3ce1c` |
| `library-audit/higham_v01-045daf2-derived/` | Derived tables used in Chapter 5 | same |
| `source-coverage/AUDIT_ch01-28_PDF_FIRST_2026-07-21.md` | PDF-first source-coverage audit of Chapters 1–28 | `lean-numerical-stability`, commit `5e69ce3d5`, `docs/source_coverage/` |
| `source-coverage/AUDIT_ch01-28_PDF_FIRST_INDEPENDENT_2026-07-21.md` | Independent PDF-first audit (Kahan summation case) | `lean-numerical-stability`, commit `9a4067d58`, `docs/source_coverage/` |
| `faithfulness/METHODOLOGY.md` | Faithfulness-check protocol | thesis repository, `sources/faithfulness/` at `bd3ce1c` |
| `construction-history/EARLY_HISTORY.md` | Verified evidence for the first pass, its corrections and the scope decisions | thesis repository, `sources/construction-history/` (2026-10-06) |
| `construction-history/project-memory/` | Decision log, repass ledger and implementation-backed audit | thesis repository, `sources/old_thesis_memory/` at `bd3ce1c` |
| `construction-history/chapter_splitting/` | Parallel-formalization blueprint and the chapter-formalization skill (`SKILL.md`, `references/`) | ignored folder `chapter_splitting/` of the `lean-numerical-stability` working tree, copied on 2026-10-06 |

All files are copies of their origin with one systematic edit: local
absolute paths of the author's machine were replaced by placeholders, so
that no local path appears in this branch. The placeholders are
`<library-repo>` (the `lean-numerical-stability` checkout), `<workspace>`,
`<home>`, `<codex-home>`, `<elan-home>`, `<cache-home>` and `<tmp>`. The edit
touched 44 text files (mostly build and audit logs); compressed files and
figures contained no local paths. `construction-history/EARLY_HISTORY.md`
also describes its sources without local paths and refers to
`project-memory/` by its name in this branch.
