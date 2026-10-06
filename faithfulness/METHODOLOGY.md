# HighamBench faithfulness audit

## Purpose

This audit determines whether a fixed Lean target represents the result selected
from its reference paper. Kernel acceptance is necessary but irrelevant to this
question: a provable theorem can still formalize the wrong statement.

The audit accepts either:

- `faithful-equivalent`: the Lean and paper statements have the same mathematical
  content, allowing definitional reformulation and harmless presentation changes;
- `faithful-stronger`: Lean genuinely proves a more general domain or a stronger
  conclusion while retaining the selected paper result.

Adding hypotheses, restricting dimensions, deleting conclusions, replacing an
algorithmic claim by an unrelated analytic fact, or making a theorem vacuous is
not a stronger result.

## Repository layout

All reusable audit material lives here:

```text
paper_bencmark/faithfulness_audit/
  METHODOLOGY.md
  prompts/
  schemas/
  scripts/
  templates/
  skill/highambench-faithfulness-audit/
```

One task audit uses a dedicated result folder:

```text
paper_bencmark/highambench/tasks/P11/T1/faithfulness/
  manifest.json
  inputs/
    source_locator.json
    declaration_dossier.md
    blind_dossier.md
  agent_outputs/
    source_contract.json
    blind_translation.json
    direct_judge.json
    roundtrip_judge.json
    adjudicator.json          # only when required
  decision.json
  report.md
  history/                    # prior runs archived by an intentional refresh
```

The folder is used because an audit has several independent inputs and outputs.
No audit agent may edit `Target.lean`, `context.md`, `task.json`, shared Lean
sources, or the reference PDF.

## Sources of authority

The reference PDF and the exact Lean environment are authoritative.
`task.json` may locate the PDF, source pages, and theorem declaration, but its
informal paraphrases are not evidence. `context.md` is an object being audited,
not evidence for the verdict. The target proof is excluded because faithfulness
concerns the proposition, not how it is proved.

Before any model call, `scripts/prepare_audit.py` must:

1. validate the task ID and required files;
2. verify the reference PDF against the SHA-256 recorded in `task.json`;
3. hash the target, metadata, context, and every local imported source;
4. compile the unchanged target and local imports in a temporary Lean module tree;
5. inspect the elaborated theorem type through Lean's environment API;
6. generate the direct and blind declaration dossiers;
7. write a `prepared` manifest.

If preparation fails, no judge runs.

## Declaration dossier coverage

A judge must never infer the meaning of a symbol from its name. For example,
`p11VecNorm` must be checked from its body rather than assumed to be a Euclidean
norm.

The dossier has four complementary layers:

1. **Exact declaration source.** The theorem text is included without its doc
   comment or proof.
2. **Elaborated type.** Lean prints both a readable type and a fully explicit type
   exposing implicit arguments, typeclass instances, coercions, and notation.
3. **Recursive local closure.** Starting only from constants in the theorem type,
   the tool recursively follows the types and bodies of every declaration owned
   by the target's local HighamBench import modules. For a local inductive or
   structure, it also follows every constructor so all fields and invariants are
   exposed even when a projection does not appear separately in the target.
4. **External semantic frontier.** Every directly reached Lean/mathlib declaration
   is listed with its owner, kind, type, and one-level definition body. Traversal
   stops there to avoid replacing a statement audit with an expansion of all of
   Lean and mathlib.

The direct dossier additionally includes the complete, hashed source text of
every local imported module, including locally imported files that turn out not
to occur in the semantic closure. The manifest fingerprints the complete
compiled environment and records dependency edges.

The blind dossier deterministically replaces every benchmark-local declaration
and owner module with neutral identifiers such as `LocalDef001` and
`LocalImport001`. This removes paper numbers and semantic hints from local names
without changing types, bodies, dependency IDs, or mathematical content.

Each semantic dependency receives an ID such as `D001`. Both the blind
translator and direct judge must return exactly one coverage record for every
ID. Missing or duplicate IDs invalidate the run. This makes "I read the imports"
an auditable requirement rather than a prompt suggestion.

The external frontier is the declared trust boundary. If a verdict depends on a
nonstandard external declaration whose one-level body is insufficient, the judge
must mark it `unclear`; the adjudicator must inspect deeper source before a final
decision.

## Stateless audit loop

All roles are fresh subagents started with inherited conversation disabled. A
role receives only its declared input bundle. Invalid output is retried with a
new subagent, not repaired in the old conversation.

### 1. Source-contract agent

Inputs:

- `prompts/source_contract.md`;
- `inputs/source_locator.json`;
- the cited PDF pages and enough surrounding pages to resolve definitions,
  assumptions, and cross-references.

It does not receive the Lean target, declaration dossiers, `context.md`, or
informal statement fields from `task.json`. It extracts the paper statement,
including implicit context and undebatable constraints.

### 2. Blind-translation agent

Inputs:

- `prompts/blind_translation.md`;
- the complete text of `inputs/blind_dossier.md`, supplied inline.

It receives no paper, task identity, theorem name, proof, prior agent output,
conversation history, filesystem access, or tools. A run that uses outside
information is invalid. The dossier contains all semantic dependencies but no
source commentary.

The source-contract and blind-translation agents run in parallel.

### 3. Direct judge

Inputs:

- `prompts/direct_judge.md`;
- the PDF source packet and source contract;
- `inputs/declaration_dossier.md` and the manifest's dependency inventory.

It independently checks the paper rather than treating the source-contract
agent as authoritative. It must complete every `Dxxx` dependency and every
`Sxx` numerical semantic check.

### 4. Round-trip judge

Inputs:

- `prompts/roundtrip_judge.md`;
- the PDF source packet and source contract;
- the blind translation.

It does not see Lean or either declaration dossier. This preserves an
independent round-trip test. The blind translator's mandatory dependency ledger
is how imported semantics enter this path.

The two judges run in parallel after the first two agents finish.

### 5. Adjudicator

A fresh adjudicator is mandatory when:

- classifications differ;
- either judge requests adjudication or returns `undetermined`;
- a dependency or semantic check is unresolved;
- the implication directions conflict with the stated classification.

It receives the paper source packet, both dossiers, all prior outputs, and
`prompts/adjudicator.md`. It resolves evidence item by item; it does not vote or
average judgments.

## Implication decisions

Every judge answers both questions separately:

1. Does the Lean proposition imply the selected paper result under the paper's
   context?
2. Does the selected paper result imply the Lean proposition?

The domain-aware classification is:

| Lean implies paper | Paper implies Lean | Classification |
|---|---|---|
| yes | yes | `faithful-equivalent` |
| yes | no | `faithful-stronger` only when the extra strength is genuine |
| no | yes | `not-faithful-weaker` |
| no | no | `not-faithful-different` |
| unclear | any | `undetermined` |

Logical implication alone does not excuse vacuity. Added assumptions, restricted
types, or an impossible premise must be analyzed as loss of applicability.

## Numerical semantic checks

The generated manifest fixes 16 required checks (`S01`-`S16`): source selection;
binders and types; quantifier scope; hypotheses; conclusion completeness;
operators and imported definitions; exact versus computed values; algorithm
linkage; norm semantics; constants and indexing; floating-point model and
exceptional values; relation strength; error notion; higher-order terms;
specialization/generalization; and nonvacuity.

Each judge records `pass`, `fail`, `unclear`, or `not-applicable`, with concrete
paper and Lean/translation evidence. `not-applicable` requires an explanation.

## Finalization and later repair

Only the orchestrator writes agent outputs. It validates JSON, hashes every
artifact, invokes adjudication when required, writes `decision.json`, renders
`report.md`, and changes the manifest status to `completed` only after the
complete validator passes.

An audit does not repair the target. A later repair agent may consume the final
report and retry the formalization, after which the changed target must receive
a new audit because its hash has changed.

Validate every role immediately after writing its JSON. An invalid role output
is removed from the active run and retried with a new stateless agent:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/validate_agent_output.py \
  P11-T1 source-contract
```

## Commands

Prepare and validate an input bundle:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1
python3 paper_bencmark/faithfulness_audit/scripts/validate_audit.py P11-T1 --phase prepared
```

Refresh prepared inputs only when intentionally invalidating prior results:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/prepare_audit.py P11-T1 --force
```

Install the repository's skill copy locally:

```bash
python3 paper_bencmark/faithfulness_audit/scripts/install_skill.py
```
