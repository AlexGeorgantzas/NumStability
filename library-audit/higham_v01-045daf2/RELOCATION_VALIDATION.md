# Relocation validation

Validation date: 2026-09-15.

The audit evidence was copied from its ignored temporary directory into this
permanent thesis source bundle without changing any of the 485 authoritative
artifacts. Validation after relocation produced:

```text
Markdown files scanned:                 49
Relative Markdown links checked:       462
Missing relative targets:                0
ARTIFACT_SHA256SUMS:                   PASS
SUPPLEMENTAL_SHA256SUMS:               PASS
```

The link check examined ordinary relative Markdown links, resolved them from
the directory of the containing document, ignored external URLs and local
fragment-only links, and checked that the target path existed. It did not
validate remote URLs or individual Markdown heading fragments.

The supplemental files preserve small generated probe outputs and link targets
that were outside the original manifest. They do not alter the historical
reports or their authoritative checksum set. Python bytecode caches and the
full 8.3 GiB temporary worktree remain excluded.
