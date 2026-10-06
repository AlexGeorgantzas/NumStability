# CAST08-PROP3.1: Castaldo–Whaley–Chronopoulos Proposition 3.1: optimal equal blocking and forward-error bound for t-temporary superblock summation

## Authoritative source

- Authors: Anthony M. Castaldo, R. Clint Whaley, Anthony T. Chronopoulos
- Title: Reducing Floating Point Error in Dot Product Using the Superblock Family of Algorithms
- Year: 2008
- PDF SHA-256: `ffdea8e2136c7f4226e4c0d382d512fef190cd207133a1a0c88c8ef7b9ebeeb2`

## Exact source locations

- Section 1.1 and Section 3, Proposition 3.1, printed page(s) 1157, 1162–1164, PDF page(s) 2, 7–9: Standard relative-error model without overflow or underflow; t-level summation, optimal equal blocking factor N^(1/t), and gamma_(t(N^(1/t)-1)) error bound

## Target clarification

- For positive integers t and b, set N=b^t. On arbitrary signed N-element data, compute the t-level equal-block superblock sum described by the source's mathematical prose, Figure 3.2, and Proposition 3.1: recursively sum each consecutive b-element group with rounded additions and recursively combine b child totals at every higher level, with exactly t summation levels. The literal printed propagation loop in Figure 3.1(a) excludes the final transfer to temporary accumulator zero and cannot implement that described computation as written; do not formalize this apparent pseudocode defect as the target algorithm.
- Under the source's standard relative-error model excluding overflow and underflow, and gamma-validity, formalize the forward bound |computed sum - exact sum| <= gamma_(t*(b-1)) times the sum of absolute input values. Include the endpoint t=1 and every positive integral t-level equal-block case.
- Also formalize the optimal-error-counter statement in Proposition 3.1: among positive integral blocking factors for t levels whose product is N, the sum of the per-level (factor-1) counters is no smaller than t*(b-1), with equality for the equal factor b. Do not substitute an unproved optimality assumption.

## Scope constraints

- Retain the recursive t-level rounded algorithm specified by the mathematical prose, diagram, and proposition, while disclosing the Figure 3.1(a) propagation-loop discrepancy; an abstract output satisfying the target bound by assumption is not the source computation.
- Do not narrow to nonnegative data, t=2, b=2, or only a finite list of t values.
- Do not replace independently rounded operations by exact addition or use a theorem that already states the whole requested t-level result as a premise.
- This is a prospective task only. It needs an independent source audit, target-result collision screen, and compile-checked private skeleton with task-relevant NumStability reach before admission to any measured corpus.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
