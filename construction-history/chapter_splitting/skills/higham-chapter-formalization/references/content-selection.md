# Content Selection Rules

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->


## Contents

- Decision procedure and reason codes
- Named results
- Numbered equations
- Precise prose claims
- Qualitative prose
- Definitions and terminology
- Notation and background conventions
- Figures and tables
- Numerical experiments
- Complexity and flop counts
- Problems, exercises, and Appendix solution rows
- Imported claims
- Educational foreshadowing
- Benchmark candidates
- Chapter 1 calibration examples
- Anti-patterns

## Phase 2: Classify each item with the decision procedure

Apply the following decision procedure in order.

```text
1. Is the item merely editorial, historical, bibliographic, typographic, or expository?
   -> SKIP.

2. Is it an end-of-chapter `Problem`, exercise, or Appendix solution row?
   -> If the current user, benchmark mode, comprehensive mode, or local proof
      plan selects it, classify it as `FORMALIZE_PROBLEM` and formalize the
      precise mathematical target with the normal no-placeholder proof
      discipline. Otherwise mark `BENCHMARK_CANDIDATE`, `DEFER`, or `SKIP`
      with a concise reason; unselected rows need only enough inventory detail
      to identify what was omitted.

3. Is it a programming-language convention, named-machine observation,
   calculator example or instruction, empirical table, plot, or
   hardware-specific output outside the end-of-chapter exercise section?
   -> SKIP in core mode.

4. Is its mathematical conclusion underspecified by words such as
   "much worse", "almost", "typically", "small", "large", "can be",
   "virtually constant", or "of order" without a precise meaning?
   -> SKIP or DEFER. Do not invent a theorem.

5. Is it educational foreshadowing whose required theorem is proved later?
   -> DEFER the full result; formalize only a central lightweight definition
      if it is independently useful now.

6. Is it a named theorem, lemma, proposition, or corollary?
   -> FORMALIZE_CORE, unless the statement itself is empirical or underspecified.

7. Is it a numbered mathematical equation?
   -> FORMALIZE_CORE by default, unless it is only fixed test data,
      machine output, an empirical-only formula, a duplicate already reused,
      or a result explicitly deferred to a later chapter.

8. Is it a precise unnumbered mathematical claim with a true/false content?
   -> FORMALIZE_CORE if central; otherwise FORMALIZE_DEPENDENCY or include
      it in the optional comprehensive pass.

9. Is it a definition needed to state or prove a selected target?
   -> FORMALIZE_DEPENDENCY or REUSE_EXISTING.

10. Is it a precise symbolic example that proves or exposes a mathematical
   phenomenon independently of one machine run?
   -> Usually FORMALIZE_CORE or FORMALIZE_DEPENDENCY.

11. Is it a fixed numerical example?
    -> SKIP by default. Promote only if it is a necessary exact witness for a
       selected theorem or an explicitly requested benchmark.

12. Does it set up a useful algorithmic comparison for benchmarking?
    -> Mark BENCHMARK_CANDIDATE. Do not silently add it to core scope.
```

### Subclaim splitting and empirical classification

Do not classify an entire example as empirical merely because it contains printed output. Separate:

1. the algorithm or formula being used;
2. any exact deterministic or symbolic claim;
3. the machine-independent phenomenon the example illustrates; and
4. the historical output itself.

In core mode, a fully specified fixed computation is still skipped by default unless it is a necessary witness for a selected theorem or the user requests executable/machine semantics. In benchmark mode it may become a target. An under-specified historical output remains `SKIP-EMPIRICAL` or `SKIP-MACHINE-SPECIFIC`, but the row must state what details are missing and what precise replacement theorem, if any, was formalized.

### Reason codes

Use one of these stable reason codes in the inventory:

- `CORE-NAMED-RESULT`
- `CORE-NUMBERED-EQUATION`
- `CORE-PRECISE-PROSE`
- `CORE-SYMBOLIC-EXAMPLE`
- `DEP-REQUIRED`
- `PROBLEM-SELECTED`
- `REUSE-REPOSITORY`
- `REUSE-MATHLIB`
- `DEFER-LATER-CHAPTER`
- `DEFER-MISSING-PRECISE-STATEMENT`
- `BENCHMARK-RESERVED`
- `BENCHMARK-COMPARISON`
- `SKIP-EMPIRICAL`
- `SKIP-FIXED-NUMERICAL`
- `SKIP-MACHINE-SPECIFIC`
- `SKIP-PROGRAMMING-LANGUAGE`
- `SKIP-QUALITATIVE`
- `SKIP-TERMINOLOGY`
- `SKIP-FIGURE-TABLE`
- `SKIP-EDITORIAL`
- `SKIP-LITERATURE-REVIEW`
- `SKIP-DUPLICATE`


# Detailed content-selection rules

## Named theorems, lemmas, propositions, and corollaries

Formalize them unless:

- the printed statement is itself empirical;
- the conclusion is underspecified;
- it is only a citation to a theorem developed later and not needed now; or
- the user excludes it.

Include the proof. If the book omits proof but the result is core, search the repository and Mathlib, then prove or explicitly defer it. Do not create an axiom.

## Numbered equations

Every numbered equation must be inventoried. Formalize it by default when it is:

- a definition;
- an identity;
- an inequality or error bound;
- a recurrence with mathematical significance;
- an abstract model assumption;
- a formula used by a core result; or
- a precise statement that can stand independently of an experiment.

A numbered equation may be skipped or deferred when it is only:

- fixed test data for a numerical run;
- a machine-specific output;
- a formula whose only role is an excluded empirical experiment;
- a duplicate of a reused standard theorem; or
- an early preview of a theorem intentionally handled later.

Document the exception. Do not silently omit numbered material.

## Precise prose claims

A sentence embedded in prose should become a lemma when it has a determinate mathematical content.

Examples of the right shape include:

- invariance under a stated scaling;
- equality of two formulas;
- a bound under explicit assumptions;
- existence or uniqueness under clear hypotheses; and
- a symbolic implication.

Do not skip such a claim merely because it lacks a number or theorem heading.

## Qualitative or pseudo-theorem prose

Skip claims whose conclusion cannot be stated without making up mathematics. Red-flag words include:

- much better or much worse;
- nearly, almost, virtually, usually, generally, typically;
- small or large without a quantified context;
- severe, harmless, satisfactory, accurate, robust;
- can be or may be when no existential statement is intended;
- of order `u` when no asymptotic or explicit bound is provided; and
- phrases justified only by a figure or table.

Do not repair such prose by selecting an arbitrary epsilon, norm, probability distribution, constant, or asymptotic filter.

If a later chapter replaces the prose by a precise theorem, defer to that theorem.

## Definitions and terminology

Formalize a definition when:

- it is mathematically precise;
- it is used by a selected theorem;
- it is a central reusable concept of numerical analysis; or
- later chapters will clearly depend on it.

Skip or defer terminology when:

- it merely names an informal concept;
- the book does not reason with it formally;
- implementing it would require an arbitrary representation unrelated to later theorems; or
- its defining words are themselves qualitative.

Do not create a digit-list API merely to encode the phrase "significant digits" when no theorem requires it. Conversely, a precise concept such as relative residual or QR factorization is a legitimate definition when used by results.

## Notation and background conventions

Use Lean's and Mathlib's native representations. Do not formalize:

- letter-shape conventions;
- typography;
- comment syntax of another language;
- colon notation merely as printed syntax; or
- statements that a symbol will be used for a computed quantity.

Do formalize semantic operations, such as a submatrix or column replacement, when a selected theorem actually needs them and they are not already available.

## Figures and tables

Skip the visual artifact itself in core mode.

- Do not recreate plots.
- Do not encode table entries from experiments.
- Do not formalize a diagram as a graphical object.

If the surrounding text states an independent precise mathematical relation, formalize that relation separately.

## Numerical experiments and machine-specific material

Classify each experimental passage before deciding what to formalize.

### Fully specified computation

A computation is fully specified only when the source fixes enough detail to define a unique mathematical execution: inputs, algorithm, operation order, floating-point format, rounding mode, exceptional behavior, relevant library routines, randomness or seed/law, and output interpretation.

Even then, skip a fixed computation in core mode unless it is a necessary exact witness for a selected theorem. It may be formalized in benchmark mode, comprehensive mode when explicitly selected, or a user-requested machine-semantics task.

### Empirical source output

Skip the historical output itself when details such as hardware, compiler, fused operations, extended registers, library version, decimal I/O, calculator firmware, random seed, or exact program are missing. Do not reconstruct an unspecified machine merely to match a printed number, and do not count a local rerun or emulator trace as proof.

Keep the row visible with:

- the source location and printed claim;
- the missing implementation details;
- any precise algorithmic or mathematical subclaim extracted from the passage;
- the theorem formalized instead; and
- what additional model would be required to formalize the historical output.

### Mathematical phenomenon

Formalize a precise machine-independent phenomenon illustrated by the experiment when it is a selected theorem or dependency. Examples include exact cancellation identities, symbolic instability families, abstract roundoff bounds, or deterministic error propagation.

This rule does not prohibit formalizing an abstract floating-point model or a precise theorem about representable numbers when that is central mathematical content.

## Complexity and flop counts

Formalize a complexity result only when the cost model, input size, and conclusion are precise enough to state as a theorem and the result is core or needed later.

Skip informal highest-order flop commentary, implementation-dependent counts, and empirical timing comparisons unless benchmark mode requests them.

## Problems, exercises, and Appendix solution rows

Problem items, exercises, and Appendix solution rows are no longer forbidden
chapter-formalization targets. They are optional: formalize them when the
current user selects them, benchmark/comprehensive mode selects them, or they
are the most useful precise mathematical targets for the current goal.

When selected:

- set `Decision` to `FORMALIZE_PROBLEM` or `FORMALIZE_DEPENDENCY`;
- set the reason code to `PROBLEM-SELECTED` or another precise reason;
- state only a concise mathematical paraphrase in the inventory and docstrings;
- search repository and Mathlib before defining anything; and
- prove the result end to end, with no `sorry`, `admit`, axioms, unsafe code, or
  unsolved stubs.

When not selected, record enough to explain the omission. It is acceptable to
record only the source identifier, location, and status such as
`BENCHMARK_CANDIDATE`, `DEFER`, or `SKIP`.

If a selected body theorem/equation appears to require a Problem or exercise
fact, either select and prove that fact explicitly, or keep the body theorem
open with the missing dependency recorded. Do not hide a Problem solution as an
anonymous infrastructure lemma.

## Imported claims and standard results

When the book states a known result without proof:

1. Search the repository and Mathlib.
2. Reuse a matching theorem if available.
3. Classify the source proof as complete, sketch, citation-only, or absent.
4. If a selected dependency is absent locally, acquire primary proof sources and choose a route before building substantial infrastructure.
5. Prove the needed result in an appropriate reusable module or keep the selected row open with its exact missing foundation.
6. If it only supports an empirical illustration, skip it in core mode.
7. If it enables a useful method comparison, mark it as a benchmark candidate.

An external citation is not permission to add an unproved axiom or a free hypothesis. Record the exact source location and local theorem that ultimately closes the dependency.

## Educational foreshadowing

Introductory chapters often use a later theorem to explain intuition. Detect this pattern through phrases such as "see Chapter Y", "as will be shown", or a direct later theorem reference.

In core mode:

- formalize a central basic definition if lightweight;
- do not duplicate the later chapter's full analysis;
- do not assume the later theorem to make the current example compile; and
- record the deferral and destination.

This preserves end-to-end proofs and avoids doing a major topic in the wrong chapter.

## Benchmark candidates

A numerical example may reveal a useful benchmark when it compares two methods or algorithms and the project wants to measure formalization of their correctness or stability.

Mark it `BENCHMARK_CANDIDATE` when:

- two or more methods are explicitly contrasted;
- the comparison suggests a meaningful theorem-level task;
- dependencies can be isolated from the empirical data; and
- the benchmark would measure the intended capability rather than machine output transcription.

In benchmark mode, formalize the mathematical methods and precise claims, not the original sample table or hardware run.


# Chapter 1 calibration examples

Use these examples to calibrate future decisions. They are examples of the policy, not an exhaustive Chapter 1 task list.

## Formalize or reuse in core mode

- The abstract standard roundoff equation and its error bound, modeled as a specification rather than hardware emulation.
- Absolute, relative, and componentwise error definitions when used by later statements.
- The precise prose claim that relative error is invariant under nonzero common scaling.
- Precise mixed forward-backward error equations.
- Concrete Taylor expansions and condition-number formulas with explicit assumptions.
- The symbolic cancellation error inequality for perturbed `a` and `b`.
- The general quadratic formula, subject to the proper side conditions.
- General sample mean and variance formulas and their exact algebraic equivalence.
- Relative residual and the stated lemma identifying it with a normwise backward error.
- The `ε`-parameterized LU/pivoting example, because it is symbolic rather than one machine run.
- A standard exact series identity when it is useful and already available or reasonably reusable.
- A precise numbered error relation such as the displayed roundoff equation in the `expm1` discussion.
- The basic definition of QR factorization.
- Exact symbolic equations in the upper-Hessenberg analysis.

## Skip in core mode

- Letter-shape and MATLAB notation conventions.
- Historical single- and double-precision values tied to particular machines.
- A glossary implementation of significant digits when no theorem needs it.
- Fixed decimal examples comparing significant digits.
- Figures illustrating forward/backward error.
- MATLAB, Fortran, and calculator experiments.
- Fixed numerical vectors and matrices together with observed outputs.
- Claims such as "accuracy can be much worse", "the error typically increases", "virtually constant", or "almost entirely" without a quantified conclusion.
- Design advice, misconception lists, anecdotes, historical notes, and literature review.
- Tables and plots of computed values.
- Unselected end-of-chapter Problems, exercises, and Appendix solution rows.
- Calculator-oriented examples and experiments.

## Defer

- Full QR stability analysis used as educational foreshadowing before the later chapter that proves it. Formalize the QR definition now if needed; formalize the stability theorem at its proper treatment.
- Earlier prose that points directly to a later precise theorem.

## Mark as benchmark candidates

- GEPP versus Cramer's rule or similar explicit method comparisons. In core chapter mode, skip the empirical table; in benchmark mode, reuse or formalize the algorithms and theorem-level correctness/stability claims.

# Anti-patterns

Never do the following:

- Formalize every noun or terminology sentence "just in case".
- Recreate the book's notation as a parallel API when Mathlib already has the concept.
- Build a simulator for a historical calculator to explain one table.
- Treat every displayed formula as a theorem without checking its role.
- Skip a precise prose theorem because it is not numbered.
- Convert "almost" or "much worse" into an arbitrary epsilon statement.
- Use a future theorem as an unproved hypothesis and call the result end-to-end.
- Add `sorry`, `admit`, or a new `axiom` to satisfy the compiler.
- Reprove a standard result before searching the repository and Mathlib.
- Mix editions or copy equation labels from the wrong edition.
- Ignore the difference between one-based book indices and Lean indices.
- Choose a norm, tie-breaking rule, rounding mode, or zero-denominator convention without source or project support.
- Spend the core pass on benchmark infrastructure unless it has been selected
  by the user or is the most useful precise mathematical target.
- Claim the chapter is complete without an inventory accounting for skipped and deferred items.
- Close a high-probability theorem by assuming its concentration event.
- Close a chapter-level result with only a conditional transfer, expectation theorem, deterministic subcase, or different algorithmic object.
- Present a generic perturbation certificate as the final implementation-facing floating-point theorem without instantiating the computed path.
- Hide an exact-operation convention for a quantity the algorithm computes.
- Add adjacent lemmas after the same bottleneck has repeated without showing that they close a listed dependency.
- Let a source or not-proved row disappear because a related but weaker theorem was proved.
- Polish a PDF or README while a required foundation remains open and the documentation work does not record or close that blocker.
- Describe a theorem in prose more strongly than its Lean type.

