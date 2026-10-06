# HighamBench proof task

> **Legacy construction-runner artifact:** this file is not staged or read by
> the measured-v3 runner. Its 1,800-second and token-cap rules below describe
> the retired protocol. Current measurements use `measurement_prompt.md`, a
> 3,600-second wall-clock limit, and no token ceiling; see `RUNNING.md` and
> `metadata/measurement_protocol.json`.

You are given an informal statement, a short paper-proof explanation, a fixed
Lean theorem, and shared Lean definitions.  Your only job is to construct a
Lean proof of the fixed theorem.

The complete context and fixed target are appended below. Read-only copies of
them and the task's shared Lean files are also below the `task/` directory;
use `find task -type f` if you want their paths.  Develop the proof in the scratch
file `Candidate.lean`.  Copy the import, namespace, theorem name,
arguments, assumptions, and conclusion from the fixed target exactly.  Replace
only the proof that starts after `-- PROOF_START`.  You may put proved local
helper lemmas in the candidate before the target theorem.

The fixed wall-clock limit is 1,800 seconds.  The fixed model limit is 5,000,000
input-plus-output tokens, with cached input counted as input.

Never create, modify, rename, or copy a file to `Submission.lean`; that path is
owned by the trusted benchmark runner.  Test the complete scratch candidate
with Lean first.  If you delegated work, the root coordinator must then wait
until every subagent is terminal, collect all useful results, and make sure no
child work or message remains pending.  Only the root coordinator may submit.
In a separate final model response, make exactly one model tool call: `exec`.
Its raw input must be exactly these two lines, including the final newline:

```javascript
// @exec: {"yield_time_ms": 2400000}
await tools.submit_proof({candidate_path:"Candidate.lean"});
```

Do not add any other code, text, tool call, or action to that response.  The
yield setting is transport-only and does not extend the 1,800-second proof
deadline.  A rejection result permits repair and another tested submission; an
accepted call ends the attempt automatically and must remain unanswered.

Rules:

- Do not change `Target.lean`, `context.md`, or any file below
  `task/shared/HighamBench/`.
- Do not use `sorry`, `admit`, `sorryAx`, a new `axiom` or `constant`, `unsafe`,
  `opaque`, or any device that avoids Lean's proof checker.
- Do not import a hidden answer or any file outside the mounted workspace and
  locally mounted libraries.
- Do not use the internet or attempt any network request.
- You may inspect and search local files with normal shell tools.
- You may import and use a locally mounted formal library if one is present.
- Submit only through `submit_proof`; a normal final message is not a submission.

The validator will rebuild the file in a fresh hidden copy, confirm that the
fixed statement is unchanged, reject forbidden shortcuts, and inspect the
proof's actual declaration dependencies.
