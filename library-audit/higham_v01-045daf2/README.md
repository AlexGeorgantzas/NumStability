# NumStability `higham_v01` audit evidence

This directory is an immutable copy of the 485 artifacts listed in
`ARTIFACT_SHA256SUMS` from the read-only NumStability library audit at:

```text
<library-repo>/tmp/library_audit/higham_v01-045daf2
```

The audited source was commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e` on `higham_v01`. At the final
audit check, the local branch, the remote-tracking branch, and the live remote
reference agreed on that commit. The artifact bundle was copied into the
thesis repository on 2026-09-15.

Recorded environment:

- Audit reference-resolution time: `2026-09-03T11:07:13+03:00`
  (`Europe/Athens`).
- Lean: `4.29.0-rc3`, revision
  `5d86aa4032284a5242470e95fbe25f1ff506763d`.
- Mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.

Canonical source repository:

```text
https://github.com/AlexGeorgantzas/lean-numerical-stability
```

The absolute source path above records where the audit was produced and is not
required to read or verify this copy.

The original checksum manifest has SHA-256:

```text
bbb51e2b7aa2a5effea13d30079e6296c62a31ae23466e9a8bcd75cbc70e4e1c
```

Verify all 485 retained audit artifacts from this directory with:

```bash
shasum -a 256 -c ARTIFACT_SHA256SUMS
```

The audit's full temporary `_worktree/` is intentionally excluded. It was not
part of `ARTIFACT_SHA256SUMS`, occupied approximately 8.3 GiB, and is
reconstructible from the audited Git commit and the pinned Lean/Mathlib
environment recorded in the provenance files. No manifest-listed file was
omitted. The small `_worktree/docs/LIBRARY_LOOKUP.md` file is retained
separately, byte-for-byte from the audited commit, solely because a preserved
report links to it. Its SHA-256 is
`61e98a6c241a93e1e489b09ebae66eb4d392586a980cee8c5471a9b8fd4f5f11`.
The manifest itself, this README, the lookup material, the retained compiled
probe outputs, and five small historical documents needed by relative report
links are additional files outside the 485-file manifest. Their hashes are recorded separately in
`SUPPLEMENTAL_SHA256SUMS`; `probes/build/README.md` explains their status.

Start with `THESIS_EVIDENCE.md` for thesis-safe claims and exact metric
definitions. Consult `REPORT.md` for the complete synthesis and
`LIMITATIONS.md` before interpreting any result. In particular, the evidence
supports internal formal reuse and composition in the recorded environment;
it does not establish faithfulness to Higham or a library-wide usability rate.
The same-commit cached `lake build` succeeded, but no clean full build
completed because the audit host lacked sufficient disk capacity. Therefore
the bundle contains no clean whole-library compilation time.

Evidence map:

- Cohesion and metric denominators: `THESIS_EVIDENCE.md` and
  `current_graph/metrics/incoming_and_cross_boundary_coverage_contract.csv`.
- Exact dependency chains: `DEPENDENCY_CHAINS.md` and
  `current_graph/chains/`.
- Public-interface probes: `PUBLIC_API_CONSUMABILITY.md` and `probes/`.
- Final architecture and historical comparison: `ARCHITECTURE_REVIEW.md`,
  `static_architecture/`, and `HISTORICAL_COMPARISON.md`.
- Build and proof hygiene: `TIMINGS_AND_PROOF_HYGIENE.md`, `build/`, and
  `hygiene/`.
- Reproduction and interpretation limits: `REPRODUCE.md` and
  `LIMITATIONS.md`.

In all elaborated declaration-graph artifacts, an edge `A -> B` is directed
from consumer to dependency: declaration `A` directly references declaration
`B` in its fully elaborated type or body/proof.

Do not modify files covered by `ARTIFACT_SHA256SUMS`. A later audit should be
stored under a new commit-labelled directory instead.
