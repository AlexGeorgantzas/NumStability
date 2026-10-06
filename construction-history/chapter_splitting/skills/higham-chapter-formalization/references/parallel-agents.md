# Parallel Agents

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

Read this before any git checkout, branch switch, build, proof work, or sync in
a repository that may have multiple active agents.

If the user is running a single agent in a private checkout with no shared
branch or shared `main` coordination, stop here: the normal chapter workflow
applies, and no launcher, hook, lease, worktree, or sync-lock setup is required.

## Hard Rules

- In coordinated parallel mode, every active automated agent must use a distinct
  git worktree or clone.
- A shared checkout is read-only unless no other live lease names it.
- If another non-stale lease names the current worktree, stop before branch
  switches, builds, commits, merges, pushes, or proof work. Create an isolated
  worktree or report the conflict.
- In coordinated parallel mode, main-updating sync must go through the
  main-sync lock and deterministic queue.
- Coordination files, locks, hooks, and generated prompts are local runtime
  artifacts. Do not stage or commit them unless the project explicitly says so.

## Required Detail Files

Load only what applies:

- `parallel-orchestration/worktrees-and-leases.md`: required during startup,
  preflight, lease registration, lease refresh, or worktree conflict handling.
- `parallel-orchestration/main-sync-queue.md`: required before any milestone
  sync that can update `main`.
- `parallel-orchestration/cli-and-hooks.md`: required when installing hooks,
  using launcher scripts, or diagnosing a hook refusal.
- `parallel-orchestration/agent-persistence-loop.md`: required for autonomous
  proof-completion agents that must continue through missing foundations.

## Coordination Location

Do not hard-code user-local absolute paths in this reference.

Use the first available coordination location:

1. a project-provided `COORDINATION_DIR`;
2. an existing project-local coordination directory containing
   `ACTIVE_AGENTS.md`;
3. a git-common-dir fallback such as
   `$(git rev-parse --git-common-dir)/agent-coordination/`.

The active-agent lease file is:

```text
$COORDINATION_DIR/ACTIVE_AGENTS.md
```

The main-sync lock is:

```text
$COORDINATION_DIR/main-sync.lock/
```

## Startup Gate

In coordinated parallel mode, before proof work, builds, or milestone sync:

1. inspect `git status`;
2. read the active-agent lease file;
3. reject any non-stale lease for the current worktree that belongs to another
   session;
4. create or switch to an isolated worktree when needed;
5. register or refresh the current agent lease with status `starting`;
6. fetch and merge current `origin/main`;
7. rebuild if tracked files changed;
8. set status to `active` before proof work.

Prefer the deterministic launcher described in
`parallel-orchestration/cli-and-hooks.md`; it performs this gate before the
model receives the prompt.

## Non-Codex Agents

Non-Codex agents must receive the `SKILL.md` path explicitly and report
commands, files changed, Lean declarations, external model/oracle use,
assumptions, verification results, branch, worktree, and commit. Prose
reasoning alone does not close a formalization milestone.
