# Fresh-output timing sample design

This audit uses a predeclared, deterministic, stratified sample of 30 modules.
The sample was frozen in `run_fresh_module_timings.py` and materialized as
`timing_sample_predeclared.csv` before the first timed compiler invocation.

The strata cover seven root or aggregate entry points; foundational
FloatingPoint modules; rounding, gamma-product, norm, conditioning, and
least-squares Analysis modules; dot product, matrix multiplication, LU, QR,
summation, and matrix-equation Algorithms modules; Chapter 9 and Chapter 12
entry points; large source modules from Chapters 9, 11, 19, and 20; and two
source-facing bridge/endpoint modules.

The sample deliberately includes the largest source module by code-bearing
lines and several other modules above the skill's 10,000-line review threshold.
It is not a random or exhaustive sample. Therefore every percentile derived
from it is labelled **sample-only**, and no claim about the distribution of all
2,839 modules may be inferred from these timings.

Each target is compiled to a unique, initially absent `.olean` and `.ilean`
path beneath this ignored audit directory. Imported modules use the exact
same-commit cached artifacts in the isolated worktree. Output sizes and hashes
are recorded before those two temporary outputs are deleted to conserve disk.
Accordingly these measurements are fresh-output *target-module* times, but not
clean full-library build times.
