# HighamBench proof task

Construct a Lean proof of the fixed theorem described below. Work only in
`Candidate.lean`. Preserve the fixed target theorem's namespace, name,
arguments, assumptions, and conclusion exactly, and replace its proof beginning
after `-- PROOF_START`. You may add imports permitted by the condition and
proved helper lemmas before the target; do not alter the target theorem surface.

Test the complete candidate with Lean as you work. When your final candidate is
ready, leave it in `Candidate.lean`, briefly report what you did, and end the
turn. Ending the turn submits that final file and stops the measured clock.
Hidden validation starts afterward and its time is recorded separately.

The wall-clock limit is 7,200 seconds. There is no benchmark token ceiling.
Input, cached input, output, and exposed reasoning-token usage are recorded but
never stop the attempt.

Rules:

- Do not change `Target.lean`, `context.md`, or any file below
  `task/shared/HighamBench/`.
- Do not use `sorry`, `admit`, `sorryAx`, a new `axiom` or `constant`, `unsafe`,
  `opaque`, or any device that avoids Lean's proof checker.
- Do not import a hidden answer or any file outside the mounted workspace and
  mounted read-only libraries.
- Do not use the internet or attempt any network request.
- You may inspect and search local files with normal shell tools.
- You may import and use a locally mounted formal library if one is present.
- Do not spawn or use subagents. Complete the attempt with the single root agent.

The exact task context and target follow this protocol text.
