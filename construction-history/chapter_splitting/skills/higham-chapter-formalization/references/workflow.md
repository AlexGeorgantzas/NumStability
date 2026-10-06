# Workflow and Proof Planning

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->


## Contents

- Workflow overview
- Phase 0: repository baseline
- Phase 1: chapter inventory
- Phase 2: classification routing
- Phase 3: repository and Mathlib search
- Phase 3A: proof-source acquisition
- Phase 4: dependency graph and boundary
- Phase 5: theorem-design plan
- Phase 6: Lean implementation

# Workflow

## Phase 0: Inspect the repository and establish a clean baseline

Before reading the chapter in detail:

1. Complete the mandatory planning-document read described in **Parallel formalization coordination documents**, and record the assigned split and owned chapter range.
2. Read all applicable `AGENTS.md` files and project documentation.
3. Inspect `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`, import conventions, namespaces, and nearby chapter files.
4. Identify the project's standard build and test commands.
5. Run the smallest relevant baseline check before editing.
6. Search for existing definitions and results from previous chapters.
7. Note whether the repository uses one file per chapter, multiple topic files, or shared foundational modules.
8. Locate repository navigation and theorem-discovery documents such as `README.md`, library lookup notes, examples, or generated theorem summaries when they exist.
9. Record the baseline status of files and warnings that may later need to be distinguished from new issues.
10. Do not reorganize unrelated code.

Typical checks, adjusted to the repository, include:

```bash
rg -n "relevantName|relevant phrase" .
lake env lean path/to/File.lean
lake build
```

Do not assume these exact commands if the repository defines another workflow.

## Phase 1: Read the entire chapter and build the source inventory

Read the full chapter before writing substantial Lean code. Do not stop after the first theorem.

For PDFs:

- use extracted text for search and navigation;
- inspect rendered pages whenever equations, subscripts, superscripts, matrix layout, diagrams, or footnotes may have been corrupted by extraction;
- use printed page numbers and source labels, not only raw PDF page indices;
- inspect footnotes when they change assumptions, such as a guard-digit requirement; and
- do not guess an unreadable formula.

Inventory all of the following, even when the final decision is to skip:

- every theorem, lemma, proposition, corollary, and explicitly named result;
- every numbered equation;
- every precise unnumbered identity, inequality, recurrence, limit, expansion, or invariance claim;
- mathematical definitions embedded in prose;
- algorithms and pseudocode;
- symbolic and numerical examples;
- figures and tables;
- cross-references to earlier or later chapters;
- end-of-chapter Problem, exercise, and Appendix solution rows, either as
  selected formalization targets or as concise unselected/deferred/benchmark
  rows;
- imported claims attributed to other sources;
- explicit phrases such as "not proved", "it follows from", "with high probability", "standard", "future work", or "see Chapter Y" that may conceal dependencies; and
- for each algorithm, every quantity that is an input, a random choice, computed in exact arithmetic, computed in inexact arithmetic, or used only in the analysis.

Use this inventory schema:

```markdown
| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
```

Recommended values:

- `Precision`: `precise`, `partly precise`, `underspecified`.
- `Generality`: `general`, `symbolic family`, `fixed exact instance`, `fully specified computation`, `empirical run`, `editorial`.
- `Source proof`: `complete`, `sketch`, `citation-only`, `none`, `not applicable`.
- `Decision`: `FORMALIZE_CORE`, `FORMALIZE_DEPENDENCY`, `FORMALIZE_PROBLEM`, `REUSE_EXISTING`, `DEFER`, `BENCHMARK_CANDIDATE`, `SKIP`.

For selected Problem, exercise, or Appendix solution rows, fill `Statement
summary` with a concise mathematical paraphrase, set `Decision` to
`FORMALIZE_PROBLEM` or `FORMALIZE_DEPENDENCY`, and give the Lean artifact/status.
For unselected rows, it is enough to record the identifier, location, and a
concise `BENCHMARK_CANDIDATE`, `DEFER`, or `SKIP` status.

For an algorithmic or probabilistic chapter, supplement the inventory with an extraction table:

```markdown
| Algorithm/source | Inputs | Outputs | Deterministic parameters | Random choices/law | Exact object | Computed object | Computed quantities | Analysis-only objects | Target claims |
|---|---|---|---|---|---|---|---|---|---|
```

For every reported experiment, split the surrounding passage into separately classifiable subclaims and assign one of:

- `fully-specified-computation`;
- `empirical-source-output`; or
- `mathematical-phenomenon`.

A single paragraph may contain all three. Keep the historical output visible in the inventory, formalize any selected precise phenomenon, and do not let an empirical label hide an algorithm specification, invariant, exact computation, or theorem.

Treat user corrections to an inventory row, theorem statement, or scope classification as regression tests: update the affected row and audit analogous rows before continuing.

Do not begin the main implementation until all named results and numbered equations have inventory rows.


## Phase 2: Classify each item with the decision procedure

Read `content-selection.md` for the full decision procedure, subclaim splitting rules, reason codes, and detailed content-selection cases. Complete that classification before Phase 3.

## Phase 3: Search the repository and Mathlib before defining anything

For every proposed definition or theorem:

1. Search the current repository by mathematical term, likely Lean name, notation, and neighboring concepts.
2. Search the installed Mathlib source and use Lean queries such as `#check` or `#find` where useful.
3. Inspect the actual theorem statement and required imports. Do not rely only on a search-result title.
4. Reuse the existing declaration directly when it matches.
5. If source traceability is useful, add a thin, proved wrapper theorem rather than duplicating the underlying development.
6. If a book definition differs only by notation, translate it to the existing representation instead of creating a parallel type.
7. Record the reused declaration in the inventory.

Examples of concepts that are likely to exist in some form include matrices, finite vectors, norms, floor and ceiling, real and complex analysis, probability distributions, determinants, QR-related infrastructure, limits, asymptotics, and standard series identities. Their existence must still be checked in the actual project version.

### Do not build a duplicate lexicon

Printed conventions such as "capital letters denote matrices" or MATLAB-style colon notation are not mathematical objects that need independent Lean declarations. Use the repository's existing matrix and indexing representation. Add source-facing notation only when it materially improves later statements and does not create a competing API.

## Phase 3A: Acquire proof sources before hard missing-foundation work

Run this phase when a selected target has a proof sketch, citation-only proof, omitted intermediate mathematics, or a missing foundation not found in the repository or installed Mathlib.

1. Classify the source proof as `complete`, `sketch`, `citation-only`, or `none`.
2. Search the source's own citations first, then primary literature such as original papers, journal or arXiv versions, official monographs, and author notes.
3. Follow citation chains until the missing step is explicit enough to state in Lean or a genuine mathematical route choice remains.
4. Compare candidate routes by source fidelity, assumptions, constants, formalization difficulty, and fit with local definitions.
5. Translate each external result into an explicit local Lean target. Do not cite the external result as a hypothesis substitute.
6. Record hidden assumptions exposed by the source, including independence, measurability, boundedness, finite dimension, positivity, invertibility, self-adjointness, rank, or floating-point validity.
7. Stop source acquisition once the dependency route is sufficiently explicit; do not turn it into an unrelated literature survey.

Maintain a proof-source ledger when this phase is triggered:

```markdown
| Selected claim | Missing proof step | External source and exact location | Assumptions/constants | Intended Lean target | Route/status | Local closure theorem |
|---|---|---|---|---|---|---|
```

Allowed route/status values include `formalized`, `partial foundation`, `advisory only`, `rejected`, `route choice`, and `open`. Record theorem, lemma, equation, page, section, bibliographic identifier, and stable URL when available. Represent multi-source citation chains in the dependency graph. External sources may guide statement design and proof order, but a selected row closes only through a local proof or an already formalized trusted dependency.

## Phase 4: Build the dependency graph and choose the chapter boundary

For each selected target, list:

- source definitions it uses;
- existing repository or Mathlib declarations it uses;
- new local definitions required;
- lemmas needed for the proof;
- results referenced from earlier chapters;
- results referenced from later chapters; and
- any ambiguity or missing side condition.

Then topologically order the implementation.

### Cross-chapter rules

1. Reuse already formalized earlier chapters.
2. Reuse Mathlib when possible.
3. If the current chapter's selected theorem genuinely requires a local missing lemma, prove it now.
4. If the passage is merely an early illustration of a theorem developed later, defer the illustration or full stability analysis to the later chapter.
5. If a later result is essential to a current named theorem rather than mere exposition, either formalize the dependency in a reusable earlier module or report a genuine blocker. Do not assume it.
6. Every deferred row must name the likely destination chapter or section when the source identifies one.

### End-to-end does not mean assumption-free

Mathematical hypotheses and model specifications are allowed. For example, a theorem may assume a standard roundoff model, differentiability, nonzero denominators, or matrix invertibility when those are source assumptions.

What is forbidden is adding a hypothesis equivalent to an unproved intermediate theorem merely to complete the current proof. For example, if the text informally invokes "the QR algorithm is backward stable" before proving it later, do not add that sentence as a free hypothesis and call the resulting example end-to-end.

### Foundation feasibility gate

Before hard proof work on each selected chapter-level theorem, create a feasibility table:

```markdown
| Selected theorem/source | Intended Lean theorem | Required foundation | Status | Existing theorem/source | Smallest next Lean target | Downstream work allowed? |
|---|---|---|---|---|---|---|
```

Use these statuses:

- `available-local`: directly reusable;
- `small-adapter`: a small proved wrapper is needed;
- `missing-foundation`: absent locally and required;
- `route-choice`: several mathematically different proof routes are plausible;
- `out-of-scope-by-policy`: excluded by the selected mode.

If a required foundation is `missing-foundation`, make that foundation the active target before proving downstream algorithm, stability, floating-point transfer, or documentation-facing theorems that depend on it. If it is a `route-choice`, compare assumptions, constants, source fidelity, and library fit before choosing. Ask the user only when the choice changes the mathematical theorem or requested scope in a material way.

Examples of foundations that often need an explicit gate include probability constructions, concentration inequalities, spectral and perturbation theory, SVD/rank results, convexity or optimization, graph/Laplacian facts, asymptotic bridges, and floating-point primitives. When matrix concentration is required, name the intended route explicitly—for example trace-MGF/Lieb-Tropp, Golden-Thompson/Ahlswede-Winter, a covering-net argument, scalar symmetrization, or another precise route—before downstream work.

### Selected-scope continuation rule

For an autonomous request to complete the selected mode, a failed final gate is a work queue:

1. rank open selected-scope rows by user priority, number of dependents unlocked, proximity to local infrastructure, and risk of documentation overclaiming;
2. choose the highest-leverage row;
3. make its smallest meaningful missing dependency the next Lean target;
4. update the inventory and any not-proved or proof-source ledger immediately after progress; and
5. rerun the relevant validation before moving on.

This rule never promotes skipped empirical, qualitative, machine-specific, or comprehensive-only material into core scope. If a target is too large, close a genuine reusable dependency, keep the chapter-level row open, and continue dependency-first.

### Bottleneck detection and red-bottleneck protocol

A target is bottlenecked when any of the following holds:

- the same selected-scope row survives two proof or audit passes;
- two or more new lemmas were added but the missing foundation did not change;
- Lean failures repeatedly return to the same API, typeclass, measurability, norm, spectral, probability, or floating-point issue;
- the report repeats the same next step; or
- a new theorem is not used by the target or any listed dependency.

Create a bottleneck ledger entry containing the source claim, exact blocking Lean theorem, dependency list, local and external candidates, failed routes with concrete errors, chosen route, next dependency theorem, and validation command.

A bottleneck becomes **red** after two focused passes with the same missing foundation. Then:

- freeze downstream, transfer, PDF-polish, and adjacent infrastructure work;
- keep a dedicated bottleneck ledger file or clearly named report section;
- count progress only when a listed dependency closes, a route is ruled out with evidence, a hidden hypothesis is removed, or the theorem statement is corrected to match the source; and
- after one focused pass with no dependency-status change, switch to another listed route or present the genuine route choice if it changes the theorem.

Do not orbit a blocker with unrelated adapters.

## Phase 5: Write an implementation and theorem-design plan before the main proof work

The plan should state:

- files to create or modify;
- selected declarations in source order;
- reused repository and Mathlib declarations;
- new dependencies and their feasibility status;
- external proof sources and route choices, when needed;
- deferred items and benchmark candidates;
- expected proof risks and weak components;
- any computed-quantity, probability, or floating-point audit required; and
- the incremental and final verification commands.

Design the theorem statements before proving them. Use a table such as:

```markdown
| Source target | Lean name | Plain mathematical statement | Exact hypotheses | Hypothesis classes | Dependencies | Source proof | Final or internal | Status |
|---|---|---|---|---|---|---|---|---|
```

Classify hypotheses as:

- `source assumption`;
- `domain assumption`;
- `floating-point/model validity`;
- `reused theorem assumption`; or
- `suspicious proof artifact`.

Reject a design that assumes the requested concentration, stability, perturbation, correctness, or error bound. Also reject a design that closes a source theorem only with an expectation result, deterministic consequence, conditional transfer, different algorithmic object, or exact-arithmetic subcase unless that is exactly the selected source claim.

When selected-scope claims remain open, maintain a not-proved ledger:

```markdown
| Source location | Exact selected claim | Current Lean status | Why current results do not close it | Missing foundation | Next concrete theorem | Blocking final gate? |
|---|---|---|---|---|---|---|
```

Recommended Lean-status values are `unstarted`, `partial foundation`, `deterministic subtheorem`, `conditional transfer`, `exact-arithmetic subcase`, `fully proved`, and `out of scope by policy`.

The source inventory remains the authoritative record for all chapter content; the not-proved ledger is a focused gate for still-open selected-scope claims. Do not let a row disappear merely because a related subtheorem was proved. A conditional theorem does not close a row whose missing content is exactly the condition; an expectation theorem does not close a high-probability row; and a theorem about a different object or algorithm does not close the source claim.

Prefer a small number of coherent declarations over many speculative helpers. Do not over-generalize beyond the source merely because a more abstract theorem is conceivable.

## Phase 6: Implement in Lean

### Source fidelity

- Preserve the source's mathematical domain unless a library theorem supplies a harmless generalization.
- Make necessary side conditions explicit: nonzero denominators, positivity, dimensions, differentiability, invertibility, and index bounds.
- Do not replace `≈`, `O(·)`, `≪`, or qualitative prose by equality or an arbitrary inequality.
- Do not silently repair a suspected typo. State the issue in the report and, if safe, implement a clearly documented corrected version.
- Distinguish a minimum from an infimum. If existence of a minimizer is not established, do not assert `min` merely because the prose uses that word informally.
- When an audit or user correction changes a theorem's assumptions, computed objects, probability loss, perturbation radius, or conclusion, make the correction as a named Lean result or corrected theorem statement. Do not patch only the prose while leaving the mathematical surface unchanged. The corrected surface must list the new hypotheses and loss terms, identify computed versus analysis-only objects, name the Lean declarations that prove it, and leave any uninstantiated routine visible in the not-proved ledger.

### Declaration choice

- Use `def` for semantic definitions.
- Use `abbrev` only for transparent source-facing aliases that add no new mathematics.
- Use `lemma` or `theorem` for true/false claims.
- Use a `structure` or predicate for an abstract numerical model when appropriate.
- Comments and docstrings document a declaration but never count as formalization by themselves.

### Partial mathematical notions

If the book says a notion is undefined on part of its domain, model that honestly. Prefer an explicit domain hypothesis, subtype, or existing partial representation over an arbitrary totalization.

Example: for relative error, do not silently define the zero-denominator case to be zero unless the project has already adopted that convention. State `x ≠ 0` where needed.

### Abstract numerical models versus machine emulation

Formalize the mathematical specification, not a named calculator or historical workstation.

For a standard floating-point model, prefer a predicate or structure expressing the existence of an error term `δ` satisfying the stated bound. Do not attempt to emulate MATLAB, Fortran, an HP calculator, or a particular processor unless the user explicitly requests a machine-semantics project.

Incidental values such as the unit roundoff of a historical machine are skipped in core mode. A precise abstract theorem about a floating-point system may still be core in a chapter devoted to that mathematical model.

### Computed quantities and implementation-facing theorems

For every selected algorithm, distinguish exact reference objects, computed objects, and analysis-only objects before stating a floating-point or inexact-arithmetic theorem.

Audit every quantity the modeled implementation forms, stores, normalizes, transforms, or uses, including when relevant:

- bases, singular vectors, projectors, factorizations, pseudoinverses, and preconditioners;
- random transforms, signs, scale factors, denominators, square roots, and normalization constants;
- matrix products, dot products, sketches, Gram matrices, right-hand sides, solver inputs, and returned outputs;
- input conversion, storage, and intermediate rounding when they are part of the chosen model; and
- probability tables or sampling-law construction when the source or repository models them as computed.

Do not add error terms to objects used only in the proof and never computed. Use them as exact reference objects. Conversely, do not silently use an exact basis, projector, factorization, or transform in an implementation-facing theorem when the algorithm is claimed to compute it.

No project-specific exception—such as treating probability construction as exact—applies unless the user, source model, or repository explicitly adopts it. State any exact-operation convention on the theorem surface and in the report.

Generic certificates and transfer theorems are useful intermediate infrastructure, but they do not by themselves close an implementation-facing path. The final theorem for that path must either instantiate locally proved bounds for all modeled computed quantities and propagate them to the output, or leave the path visibly open in the not-proved ledger. Label theorem surfaces honestly as one of:

- exact arithmetic;
- exact object plus rounded use;
- fully computed-object implementation-facing; or
- intermediate certificate/transfer infrastructure.

### Algorithms

Do not formalize pseudocode merely because it appears.

Formalize an algorithm when at least one of these holds:

- the algorithm is itself a central mathematical definition;
- a selected theorem proves its correctness or stability;
- later core results require its semantics; or
- benchmark mode explicitly requests it.

Translate the mathematical semantics, not MATLAB syntax or comment markers. A function that compiles is not, by itself, a proof of the book's claim about the algorithm.

If an algorithm appears only to generate a table or demonstrate one machine's behavior, skip it in core mode.

### Probabilistic and high-probability claims

When a selected claim is probabilistic:

- identify the probability space or distribution, random variables, deterministic parameters, and event;
- state the exact probability bound and failure probability;
- prove the event probability using a local theorem or a newly formalized result;
- name the concentration or probability inequality used and expose all of its hypotheses; and
- verify that thresholds such as `Q`, `τ`, or `ε` receive their guarantee from the stated random model.

A deterministic theorem conditioned on `goodEvent`, a bound on a random counter, or a concentration event does not close a high-probability source theorem unless the probability of that event is also proved. An expectation theorem does not close a high-probability theorem. Keep the source row open and describe the proved result at its actual strength.

### Symbolic versus numerical examples

Formalize a parameterized example when it yields an exact proof, such as an `ε`-dependent matrix factorization or a symbolic error bound. Skip a fixed decimal matrix and its observed output by default.

A fixed exact instance may be promoted only when it is logically necessary as a witness or counterexample to a selected theorem. If promoted, encode the exact mathematical values, not rounded display strings.

### Indexing

The book commonly uses one-based mathematical indices while Lean structures often use zero-based finite types. Make the translation explicit and test boundary cases.

- Prefer existing finite-index conventions in the repository.
- State how source index `i = 1, ..., n` maps to Lean indices.
- Avoid ad hoc natural-number indexing with repeated bound proofs when a finite type is standard.
- Check row/column orientation carefully for submatrices and replaced columns.

### Norms and unspecified choices

Do not choose an "appropriate norm" on the author's behalf. Formalize a generic normed statement when the source supports it, or wait until the book specifies a concrete norm such as the 2-norm.

### Exact and approximate arithmetic

- Exact algebraic identities and inequalities are suitable targets.
- Approximate decimal outputs from floating-point runs are empirical and skipped by default.
- A theorem about an error bound is suitable when the bound and assumptions are explicit.
- A rule of thumb such as "forward error is approximately condition number times backward error" is not a theorem until the source gives a precise formulation.

### Bound interpretability

For a selected implementation-facing error or stability theorem with a complicated final radius:

1. state the exact proved inequality with no hidden computed quantities;
2. give a readable closed form in primitive source parameters, dimensions, norms, unit-roundoff or `γ` terms, and solver/denominator errors;
3. recursively expand locally introduced shorthand near the theorem until a reviewer can see the primitive dependence;
4. give a big-`O` or big-`Θ` interpretation only when justified, state the asymptotic regime, and show both compact and fully expanded parameter dependence when the compact form hides meaningful terms;
5. prove or check non-vacuity, such as convergence of the bound to zero as roundoff terms tend to zero with dimensions and source parameters fixed; and
6. keep the exact theorem primary—the asymptotic explanation never replaces it.

Do not present only opaque aliases such as `T`, `τ`, `ρ`, or `K` on the final theorem surface.

### Proof construction

- Reuse library lemmas before writing low-level algebra.
- Keep helper lemmas local to the mathematical dependency they serve.
- Prefer transparent, maintainable proofs over brittle tactic scripts.
- Compile incrementally after each coherent declaration.
- Do not use `sorry`, `admit`, `by_contra!`-style guesswork without understanding the goal, or a new global `axiom`.
- Do not assume the target conclusion or an imported stability theorem as a hypothesis.
- Do not weaken the statement merely to obtain an easy proof without reporting the change.
- Implement in layers: add a coherent definition or lemma group, compile the touched module, update the theorem-design and ledger status, then continue.
- If a proof becomes unexpectedly large, search the repository and proof-source ledger again before writing more low-level infrastructure.
- If the same dependency fails twice, invoke the bottleneck protocol rather than adding adjacent bridge lemmas.
- Name internal adapters and transfer lemmas as such; do not advertise them as the chapter-level result.

### Source traceability

Every source-facing declaration should have a concise docstring containing, when available:

- book edition;
- chapter and section;
- printed page;
- equation, theorem, lemma, or problem label; and
- a short paraphrase of the source statement.

Do not paste long book passages into comments. Keep docstrings concise and mathematical.

Example pattern:

```lean
/-- Higham, 2nd ed., Chapter X, Section X.Y, equation (X.Z):
    concise paraphrase of the mathematical statement. -/
theorem ... := by
  ...
```

Follow the repository's naming conventions. Do not force this exact name or layout when the project uses another standard.

When an external source supplied a missing proof route, record its exact theorem, lemma, equation, page, or section in the proof-source ledger and, when appropriate, in a concise code comment or report entry. Do not paste long copyrighted passages.

