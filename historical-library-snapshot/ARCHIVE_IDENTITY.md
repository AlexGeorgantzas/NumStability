# Historical L-condition library source

This directory is the tracked source exported from NumStability commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e` for the archived r09/r10/r11
proof campaigns. The original commit's `NumStability/` tree object is
`f8518667fcd2c8399688947f0a15309110884874`.

`lean-toolchain` pins Lean `v4.29.0-rc3`; `lake-manifest.json` pins the
historical Mathlib dependency. These files are source and dependency
identities, not prebuilt `.olean` artifacts. Rebuilding requires the pinned
toolchain and dependency downloads or equivalent local caches.

The repository-root `NumStability/` directory is a later library snapshot.
Use this directory, not the root copy, when checking historical direct-proof
dependency counts.
