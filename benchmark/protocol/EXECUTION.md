# Execution method for the ten-task archive

This describes how the measured pairs under `benchmark/runs/<task-id>/`
were run; it is not an instruction to rerun them. Each pair report is the authority for its actual condition
order, prompt hashes, attempt counts, hardware, audit outcome, and proof
outcome. The archived effective prompts and observable agent events are
under each condition's submission and audit directories.

## Conditions and isolation

- N received Lean 4, Mathlib, the hashed paper/task packet, and the common
  statement and proof prompts. It did not have access to NumStability.
- L received the same materials plus the frozen NumStability source and
  compiled declarations, the treatment appendix, and a task-neutral
  orientation conversation performed once before measured tasks.
- Both formalizers used GPT-6 Sol/high. Faithfulness roles used GPT-6
  Astra/high. The archived session records attest disabled contestant
  subagents. Observable tool events are retained; hidden chain-of-thought
  is not available.
- The contestant workspaces were isolated. The fact that this archive
  packages both the library and N records together does **not** mean N
  could read the library during measurement.

## Statement and proof stages

1. The contestant wrote a Lean theorem statement with a target-proof
   `sorry`. At most four statement submissions were allowed. A submission
   was hashed before the contestant clock stopped; compilation, integrity
   validation, and a fresh blind/direct/round-trip/adjudication faithfulness
   audit ran outside that clock. Unfaithful statements received neutral
   feedback in the same conversation. Only a full-domain faithful statement
   was accepted.
2. After that statement was frozen, the same conversation attempted to
   prove the exact proposition, again with at most four submissions.
   Proof turns were timed. A changed statement, remaining `sorry`,
   `admit`, added axiom, or trust escape was rejected. Success required a
   zero-hole kernel-accepted proof.
3. Audit, compilation, semantic-dossier, and proof-validation effort was
   logged separately from contestant-active time. Failed attempts remain
   in the condition directories. The exact effective prompt for a turn is
   its archived `prompt.md`; the reusable prompt sources are in
   `benchmark/prompts/`.

All ten pairs in this archive reached faithful statements and complete
proofs in both conditions.

## Environment

The runs used three concurrent, disjoint lanes with 8 logical CPUs and
24 GiB RAM per lane, on Titan's Intel Core i9-13900K Linux host. The
repository root pins Lean and Mathlib; `benchmark/evidence/` records the
NumStability snapshot, one-time build, runtime, and scout. Individual
condition records contain pre/post hardware snapshots and sampled
resource peaks. The archive excludes source-paper PDFs, authentication
state, checkpoint databases, and rebuildable compiled caches.

To verify archived task IDs, source-packet hashes, paired statuses, and
candidate hashes without a model run, execute `python3 benchmark/verify.py`
from the repository root. This verifier is narrower than a fresh audit or
full replay of the original controller.
