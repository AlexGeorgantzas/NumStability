# One-time, task-neutral NumStability orientation

There is no benchmark paper, task, target, or task list in this conversation.
Explore only the exact frozen NumStability snapshot read-only. Do not access
the network or edit the library. Later L contestants will fork this actual
conversation, so keep its context compact and useful.

Verify with source inspection and focused Lean `#check` probes:

1. Exact owner imports and signatures of `FPModel`, its rounded operations,
   `BasicOp`, `gamma`, `gammaValid`, and the main rounding-factor lemmas.
2. The principal algorithm families for recursive and compensated summation,
   dot products, polynomial evaluation, matrix operations, and linear-system
   solves. For each family, identify a few canonical definitions and reusable
   error or perturbation interfaces, not an exhaustive declaration dump.
3. Important representation limits: deterministic `FPModel` versus finite-
   format, stochastic, or independently varying per-operation models; whether
   an algorithm's input/output convention differs from a common paper model.
4. An efficient ordinary search workflow using exact imports, focused `rg`,
   and Lean type probes. No task-specific declaration ranking is prepared.

Finish with a verified, navigable map of at most 2,000 words: exact core types,
module families, representative algorithm/error declarations, assumptions,
and how to inspect neighbors. Do not include any target result, proof script,
future paper-specific match, or speculation about the task corpus. This scout
turn is logged once outside per-task metrics; every L task forks the same
frozen conversation.
