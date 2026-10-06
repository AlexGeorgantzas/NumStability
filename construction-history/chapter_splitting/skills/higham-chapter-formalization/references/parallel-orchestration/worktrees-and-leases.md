# Worktrees and Leases

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

Use this for coordinated parallel-mode startup, preflight, lease registration,
lease refresh, or worktree conflict handling.

## Worktree Rule

In coordinated parallel mode, every active automated agent must use a distinct
git worktree or clone. A shared checkout is read-only unless no other live lease
names it.

If another non-stale lease names the current worktree and the session differs,
do not branch-switch, build, edit, commit, merge, push, or start proof work in
that checkout. Create an isolated worktree or report the conflict.

Recommended worktree root:

```text
$HIGHAM_WORKTREE_ROOT
```

If `HIGHAM_WORKTREE_ROOT` is unset, the launcher uses a `worktrees/` directory
next to the repository root.

Recommended worktree name:

```text
ch<chapter>-split<split>-<agent>-<date-or-session>
```

## Lease File

Use the coordination location selected by `parallel-agents.md`.

The active-agent lease file is:

```text
$COORDINATION_DIR/ACTIVE_AGENTS.md
```

Lease rows use this schema:

```md
| Agent | Session | Chapter | Split | Worktree | Branch | Scope | Milestone | Status | Started UTC | Updated UTC | Expires UTC |
|---|---|---:|---:|---|---|---|---|---|---|---|---|
```

Allowed statuses:

- `starting`
- `active`
- `syncing-main`
- `main-sync-deferred`
- `paused`
- `blocked`
- `complete`

Refresh `Updated UTC` during long work, before long builds, after long builds,
before sync, and after sync. Use a short lease window, normally 20-30 minutes
after the last heartbeat.

A stale row may be treated as inactive only after recording that it was stale.
Do not delete another agent's row unless the user or coordinator confirms it.

## Startup Decision

At startup:

1. read the lease file;
2. identify live rows whose `Expires UTC` is in the future;
3. reject any live row with the same `Worktree` and a different `Session`;
4. reject same-branch or same-chapter/split work unless explicitly coordinated;
5. create or select an isolated worktree from current `origin/main`;
6. register or refresh the current lease as `starting`;
7. set status to `active` only after baseline fetch/merge/build checks pass.

## Shared Dependencies

If two chapters need the same shared API, stop chapter work and make that API a
separate milestone. Build, commit, merge with current `origin/main`, rebuild if
needed, and push before either chapter depends on it.
