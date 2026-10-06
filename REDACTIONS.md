# Public-release redactions

This branch is the public copy of the private branch `tiered_benchmark_30` (commit
`a585a685d`), published as a single commit without history. Its content is
identical except for the systematic replacements below, made so that no
local path, host name, user name or IP address appears. Only text files were
edited; no binary file contained any of these strings.

| Replaced | Placeholder | Occurrences |
|---|---|---:|
| data-drive mount point `/mnt/<uuid>` | `<data-drive>` | 110,317 |
| Linux home directory of a person | `<home>` | 20,817 |
| temporary directory (`/tmp`, `/private/tmp`) | `<tmp>` | 1,892 |
| per-user runtime directory (`/run/user/<uid>`) | `<run-user>` | 80 |
| IP address in the download banner of source PDFs | `<ip>` | 7 |
| host name of the execution machine | `<host>` | 6 |
| a person's user name | `<user>` | 1 |

2,963 files were edited. SHA-256 digests recorded inside the run records
refer to the original files and therefore do not match the edited ones, and
helper scripts that connected to the execution machine need its address
supplied again. Generic paths inside the benchmark sandbox (for example
`/workspace`, `/home/bench`, `/run/highambench`) and standard system paths
were kept.

## Files left out

63 files are not included in this public copy: the task context files
`paper_bencmark/highambench/tasks/<paper>/<task>/context.md`. Each one
reproduces or closely paraphrases passages of the source paper, and the
first four below contain whole publisher pages with their download notices.
Source text may not be redistributed, so these files remain in the private
archive. The other files of every task (`Target.lean`, `task.json` and the
paper's `paper.json`) are included. No file cited by the thesis is among the
files left out.

- `paper_bencmark/highambench/tasks/P20/T3/context.md`
- `paper_bencmark/highambench/tasks/P05/T3/context.md`
- `paper_bencmark/highambench/tasks/P04/T1/context.md`
- `paper_bencmark/highambench/tasks/P06/T3/context.md`
- `paper_bencmark/highambench/tasks/P01/T1/context.md`
- `paper_bencmark/highambench/tasks/P01/T2/context.md`
- `paper_bencmark/highambench/tasks/P02/T1/context.md`
- `paper_bencmark/highambench/tasks/P02/T3/context.md`
- `paper_bencmark/highambench/tasks/P03/T3/context.md`
- `paper_bencmark/highambench/tasks/P08/T3/context.md`
- `paper_bencmark/highambench/tasks/P09/T3/context.md`
- `paper_bencmark/highambench/tasks/P11/T3/context.md`
- `paper_bencmark/highambench/tasks/P12/T1/context.md`
- `paper_bencmark/highambench/tasks/P13/T3/context.md`
- `paper_bencmark/highambench/tasks/P14/T1/context.md`
- `paper_bencmark/highambench/tasks/P15/T1/context.md`
- `paper_bencmark/highambench/tasks/P15/T2/context.md`
- `paper_bencmark/highambench/tasks/P15/T3/context.md`
- `paper_bencmark/highambench/tasks/P17/T1/context.md`
- `paper_bencmark/highambench/tasks/P17/T3/context.md`
- `paper_bencmark/highambench/tasks/P19/T3/context.md`
- `paper_bencmark/highambench/tasks/P23/T1/context.md`
- `paper_bencmark/highambench/tasks/P24/T3/context.md`
- `paper_bencmark/highambench/tasks/P25/T3/context.md`
- `paper_bencmark/highambench/tasks/P26/T1/context.md`
- `paper_bencmark/highambench/tasks/P27/T3/context.md`
- `paper_bencmark/highambench/tasks/P28/T1/context.md`
- `paper_bencmark/highambench/tasks/P28/T3/context.md`
- `paper_bencmark/highambench/tasks/P29/T1/context.md`
- `paper_bencmark/highambench/tasks/P29/T2/context.md`
- `paper_bencmark/highambench/tasks/P32/T3/context.md`
- `paper_bencmark/highambench/tasks/P33/T1/context.md`
- `paper_bencmark/highambench/tasks/P34/T3/context.md`
- `paper_bencmark/highambench/tasks/P35/T3/context.md`
- `paper_bencmark/highambench/tasks/P36/T3/context.md`
- `paper_bencmark/highambench/tasks/P37/T3/context.md`
- `paper_bencmark/highambench/tasks/P39/T3/context.md`
- `paper_bencmark/highambench/tasks/P40/T3/context.md`
- `paper_bencmark/highambench/tasks/P41/T3/context.md`
- `paper_bencmark/highambench/tasks/P42/T3/context.md`
- `paper_bencmark/highambench/tasks/P43/T1/context.md`
- `paper_bencmark/highambench/tasks/P43/T3/context.md`
- `paper_bencmark/highambench/tasks/P45/T1/context.md`
- `paper_bencmark/highambench/tasks/P48/T3/context.md`
- `paper_bencmark/highambench/tasks/P49/T1/context.md`
- `paper_bencmark/highambench/tasks/P50/T3/context.md`
- `paper_bencmark/highambench/tasks/P53/T3/context.md`
- `paper_bencmark/highambench/tasks/P54/T3/context.md`
- `paper_bencmark/highambench/tasks/P55/T3/context.md`
- `paper_bencmark/highambench/tasks/P56/T3/context.md`
- `paper_bencmark/highambench/tasks/P57/T3/context.md`
- `paper_bencmark/highambench/tasks/P61/T1/context.md`
- `paper_bencmark/highambench/tasks/P61/T2/context.md`
- `paper_bencmark/highambench/tasks/P62/T1/context.md`
- `paper_bencmark/highambench/tasks/P62/T2/context.md`
- `paper_bencmark/highambench/tasks/P63/T1/context.md`
- `paper_bencmark/highambench/tasks/P64/T2/context.md`
- `paper_bencmark/highambench/tasks/P65/T2/context.md`
- `paper_bencmark/highambench/tasks/P66/T1/context.md`
- `paper_bencmark/highambench/tasks/P66/T2/context.md`
- `paper_bencmark/highambench/tasks/P67/T1/context.md`
- `paper_bencmark/highambench/tasks/P67/T2/context.md`
- `paper_bencmark/highambench/tasks/P68/T2/context.md`
