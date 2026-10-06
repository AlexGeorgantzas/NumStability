## Condition L: NumStability access

A frozen external NumStability checkout at commit
`{{NUMSTABILITY_COMMIT}}` is mounted read-only. It is not part of the benchmark
repository.

- Guide: `/library/docs/LIBRARY_LOOKUP.md`
- Source: `/library/NumStability` and `/library/NumStability.lean`
- Compiled modules: `/library-olean` (already on `LEAN_PATH`)

Use local search tools to find relevant declarations and import any needed
`NumStability...` modules.
