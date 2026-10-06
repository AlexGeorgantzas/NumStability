# Agent Persistence Loop

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

Read this for autonomous proof-completion runs, especially Claude-based or
non-interactive agents.

## Core Rule

A proof-completion agent does not stop because a remaining selected-scope row is
hard, foundational, slow, or multi-session sized.

If the chapter selected-scope gate is not `PASS`, the agent's state is one of:

- continue working;
- enter the main-sync queue after a successful verified increment;
- report `BLOCKED` only for an exact obstruction that cannot be resolved locally.

A partial-progress summary is not a terminal state. Producing one while the
gate is FAIL and no `BLOCKED` obstruction or explicit user stop exists is a
policy violation: continue the loop instead.

## Terminal States

A proof-completion turn may end voluntarily only in one of these states:

1. `PASS` — the chapter selected-scope gate passes and the final audit/reporting
   requirements are recorded.
2. `BLOCKED` — an allowed exact obstruction is named per "Allowed Blocked
   States" below.
3. `USER-REQUESTED-STOP` — the current user explicitly asks to stop, pause, or
   provide status only. This is a user interruption, not proof-completion
   success.

Everything else is non-terminal. In particular these are not stops:

- a verified increment or useful checkpoint;
- a completed milestone sync;
- `main-sync-deferred` or any main-sync queue wait;
- a large, foundational, slow, or uncertain next row;
- a partial-progress summary.

After a verified increment and its sync/defer, immediately return to the loop
in the same turn, normally at step 2. Do not emit a final completion summary or
yield the turn voluntarily unless one of the terminal states above applies.

## Loop

Repeat until the selected-scope gate passes:

1. read the current chapter report, not-proved ledger, proof-source ledger, and
   selected-scope inventory;
2. select the earliest or highest-leverage open selected-scope row;
3. if the row needs a missing foundation, make the smallest reusable foundation
   theorem the current target;
4. search the repo and Mathlib before adding definitions;
5. prove a meaningful dependency or the selected row itself;
6. run the smallest relevant Lean verification;
7. update lookup docs, examples, and ledgers for the verified increment;
8. run the mandatory milestone sync or enter the deterministic sync queue;
9. resume from the next open selected-scope row.

Before yielding, run the terminal-state check above. If the gate is FAIL and no
`BLOCKED` obstruction or explicit user stop exists, continue from step 2.

## Missing Foundations

A missing foundation is work, not a reason to stop.

Examples:

- absent executable floating-point algorithm;
- absent factorization backward-error proof;
- absent spectral, SVD, perturbation, or rank theory;
- absent probability or concentration infrastructure.

For each missing foundation, write the next Lean target explicitly:

```md
| Selected row | Missing foundation | Smallest next Lean theorem | Current blocker | Status |
|---|---|---|---|---|
```

Do not replace the missing theorem with a hypothesis equivalent to the target.

## Allowed Blocked States

`BLOCKED` is allowed only when all applicable local routes are exhausted and the
obstruction is exact, for example:

- source text or cited proof is unavailable and no honest local route is known;
- repo cannot build because of an unrelated upstream breakage;
- coordination cannot be made safe because worktree creation or sync locking is
  unavailable;
- the user must choose between materially different mathematical theorem routes.

The report must name the exact Lean theorem, file, command, and obstruction.
