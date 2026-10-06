# Public-consumer probe schema

Schema version: `numstability-public-api-probes/v1`.

The sample in `PREDECLARED_SAMPLE.csv` was fixed before any probe was compiled.
Each `*_check.lean` file tests visibility after importing only its recorded
`narrow_import`. Each `*_client.lean` repeats the `#check` and adds a small
external `example` that applies the declaration. The check and client files are
compiled separately, so visibility and actual theorem use have independent
statuses. Successful client compilation establishes usability for that exact
probe only.

`results.csv` columns are: probe identity and API metadata; check/client command;
exit status; real/user/system seconds from `/usr/bin/time -p`; output paths;
source/log SHA-256; required namespace, assumptions and helpers; and observed
friction. A command has `fresh_output=true` only when its target `.olean` and
`.ilean` were absent immediately before that invocation. Imported project and
Mathlib dependencies are cached artifacts from the isolated worktree build.

The declaration universe is the predeclared, explicitly named, non-Source,
non-compatibility canonical public sample only. It is stratified rather than
random and is not an estimate of library-wide API success.
