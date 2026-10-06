# Lean Modeling Guidance

<!-- Local-only Higham chapter formalization policy reference. Do not stage or push. -->

# Lean modeling guidance for recurring Higham concepts

These are modeling principles, not mandatory APIs. Follow the repository and installed Mathlib version.

## Vectors and matrices

Prefer the project's existing `Matrix` and finite-index representation. Match dimensions explicitly. Use standard matrix operations and finite sums instead of custom nested lists unless the repository already chose a list-based model.

## Error measures

Represent absolute, relative, normwise, and componentwise errors with explicit domains. If the source distinguishes signed error from absolute error, preserve that distinction.

Prove simple structural facts, such as scaling invariance, as lemmas when the assumptions are precise and the facts are used or mathematically central.

## Backward and forward error

Prefer problem-specific definitions over a premature universal stability framework. The book often adapts the notion to each problem. Avoid a generic predicate containing an undefined word such as "small".

When backward error is an optimization over perturbations, model the feasible set carefully and prove existence before using a minimum. Use an infimum if that is the mathematically correct available notion.

## Conditioning and asymptotics

A condition number formula, derivative expression, or Taylor theorem is suitable when differentiability and nonzero conditions are explicit. Intuitive rules of thumb are not substitutes for quantitative bounds.

Use Mathlib's asymptotic framework only when the source really states an asymptotic claim and it contributes to a selected target.

## Floating-point arithmetic

Separate:

- an abstract roundoff model;
- a mathematical floating-point system; and
- one concrete machine implementation.

The first two may be formal targets in appropriate chapters. The third is skipped by default. Model assumptions should be explicit predicates or structures, not global axioms about all real arithmetic.

For an implementation-facing theorem, inventory every computed object and rounded operation, reuse local error lemmas for arithmetic and matrix operations, make dimension dependence explicit, and propagate concrete bounds to the returned result. Treat abstract certificates as intermediate unless instantiated for the advertised path.

## Probability and randomized numerical analysis

Use the repository's existing probability model and distributions. State random and deterministic quantities separately, define the event, and prove its probability. Do not introduce hidden `goodEvent` assumptions. If the selected theorem needs concentration absent from the repository, run proof-source acquisition and the foundation feasibility gate before downstream work.

## Factorizations and numerical algorithms

Reuse existing determinant, LU, QR, orthogonality, triangularity, and norm infrastructure. Formalize the exact algebraic definition before a stability theorem. If a stability theorem belongs to a later chapter, defer it rather than using it as an assumption in an introductory example.

