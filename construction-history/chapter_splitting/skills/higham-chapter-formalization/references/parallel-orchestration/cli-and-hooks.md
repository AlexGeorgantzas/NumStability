# CLI and Hooks

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

Use this when installing hooks, using launcher scripts, or diagnosing a hook
refusal. For a single agent in a private checkout, this file is optional.

## Launcher-First Workflow

For coordinated parallel runs, do not start an automated proof-completion agent
by pasting a prompt into a shared checkout. First run the launcher:

```bash
higham-start-agent --agent codex --chapter 9 --split 2 --mode proof-completion
```

The launcher creates or selects an isolated worktree, registers the lease, and
prints a prompt containing the safe `WORKDIR`. Paste that generated prompt into
the agent window.

The model does not decide whether preflight happened; the launcher does.

For a single agent in a private checkout, the launcher is optional; the normal
skill prompt may still be pasted directly into the agent window.

## v0 Scripts

The scripts live under the skill's `scripts/` directory:

- `higham-start-agent`: create/select worktree, register lease, print prompt.
- `higham-agent-status`: show active leases, locks, branches, dirty files.
- `higham-install-hooks`: install the v0 `pre-push` guard with `core.hooksPath`.

The wrappers delegate to `scripts/higham_agent.py` so lease parsing and lock
logic have one implementation.

Full main-sync automation is intentionally deferred. In v0, the queue policy in
`main-sync-queue.md` is authoritative, but agents still execute the fetch,
merge, rebuild, and push steps explicitly.

## v0 Hook

The hook files live under the skill's `hooks/` directory:

- `pre-push`: reject `main` pushes unless the session owns `main-sync.lock`.

Hooks are guardrails, not the primary workflow. A hook refusal means the agent
is in the wrong worktree, lacks a lease, or is trying to update `main` outside
the sync lock.

## Status Inspection

Use:

```bash
higham-agent-status
```

for a dashboard of active leases, stale leases, lock ownership, worktrees,
branches, dirty file counts, and recent commits.
