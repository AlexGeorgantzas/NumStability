# Local Lean environment

Run this exact command from the workspace:

```bash
lean --root . -o Candidate.olean Candidate.lean
```

The controller supplies the frozen Lean/Mathlib search path. If a read-only
`LIBRARY_GUIDE.md` is present, it describes the treatment library's compact
declaration atlas and reuse workflow. Read it before searching source files.
For a compiler-path check, use exactly `printenv LEAN_PATH`. Do not run
`env`, bare `printenv`, or a root-wide search such as `find /`; these broad
environment/filesystem inventories invalidate the submission in either
condition. Search the mounted library index or known module paths instead.
Do not add package files, download dependencies, or access the network.
Positive-PID/process-group signaling and file metadata mutation syscalls are
disabled by the common command sandbox. Use ordinary file writes and renames;
the controller owns process cleanup and time limits.
