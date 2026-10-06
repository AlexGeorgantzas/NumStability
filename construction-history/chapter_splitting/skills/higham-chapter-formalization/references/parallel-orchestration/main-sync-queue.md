# Main Sync Queue

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

Use this before any coordinated parallel-mode milestone sync that can update
`main`. For a single agent in a private checkout, use the normal milestone sync
rules from `SKILL.md`; no local sync lock is required unless the project or user
requests one.

## Lock

Serialize main-updating sync with:

```text
$COORDINATION_DIR/main-sync.lock/
```

Acquire the lock by creating that directory atomically. While holding it, write
an owner/heartbeat file, set the lease status to `syncing-main`, run the sync,
then remove the lock and set the lease back to `active`, `complete`, or
`main-sync-deferred`.

Do not delete another agent's non-stale lock. Break a lock only when both the
lock heartbeat and owner lease are stale, or when the user/coordinator confirms
it is abandoned.

## Deterministic Queue Order

When multiple live agents need to update `main`, priority order is:

1. lower chapter number;
2. lower split number;
3. earlier `Started UTC`;
4. lexical `Session`.

A later chapter may continue local proof work in its own worktree while waiting,
but it must not update `main`. It may push only its feature branch and should
mark status `main-sync-deferred`.

If the user has explicitly enabled the top-level async sync exception, the
milestone author may hand a committed, locally verified milestone to a
dedicated sync worker. The sync worker owns this queue entry, lock acquisition,
merge, rebuild, and `main` push. The original author may continue only in a
separate speculative worktree or branch and must rebase or merge onto the
verified synced head before finalizing the next milestone.

If a non-stale earlier sync lock persists for more than 30 minutes, do not break
the lock. Refresh the current lease, fetch `origin/main`, continue local work if
safe, and keep status `main-sync-deferred`.

## Sync Steps

After any successful build/check cycle:

1. stop proof/documentation work;
2. inspect `git status`;
3. stage only intended tracked Lean, documentation, and inventory files;
4. commit if tracked milestone changes exist;
5. acquire the main-sync lock in queue order;
6. run `git fetch origin --prune`;
7. merge current `origin/main` into the working branch;
8. rebuild if the merge changes tracked files;
9. push the feature branch;
10. update and push `main` to the same verified state;
11. release the lock.

Raw `git push origin HEAD:main` is not allowed outside the sync lock.

The v0 helper scripts do not automate this full sync sequence. They provide the
launcher, status view, and optional `pre-push` guard. Until full automation is
added, agents execute the steps above explicitly while holding the lock.
