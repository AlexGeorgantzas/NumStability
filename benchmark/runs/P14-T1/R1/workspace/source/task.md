# P14-T1: The basic positive exponential-sum error analysis culminating in equation (3.3)

## Authoritative source

- Authors: Pierre Blanchard, Desmond J. Higham, Nicholas J. Higham
- Title: Accurately Computing the Log-Sum-Exp and Softmax Functions
- Year: 2021
- PDF SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Exact source locations

- Section 3, printed page(s) 2316, PDF page(s) 6: Basic Algorithm 3.1
- Section 3, printed page(s) 2317, PDF page(s) 7: Exponential errors (3.1), summation analysis and weighted error (3.2)
- Section 3, printed page(s) 2318, PDF page(s) 8: First-order positive sum error (3.3)

## Target clarification

- For positive n and real inputs x_i, compute w_i = exp(x_i) without overflow or underflow and sum the computed exponentials from left to right in the standard floating-point model.
- Each computed exponential satisfies what the paper labels (3.1), namely wHat_i = exp(x_i)*(1+delta_i) with |delta_i| <= u. Let s = sum_i exp(x_i), sTilde = sum_i wHat_i exactly, and sHat be their recursively computed sum.
- Formalize the derivation culminating in (3.3): sHat = s + Delta s and |Delta s| <= (n+1)*u*s + O(u^2). Preserve the positive-sum setting and the contribution of both exponential evaluation and recursive summation.
- A finite bound stronger than the displayed first-order estimate is acceptable only if it demonstrably yields the exact (n+1) first-order coefficient and a quadratic remainder that is uniform over admissible local rounding errors for fixed n and x.

## Scope constraints

- Do not formalize only a generic summation theorem while omitting the exponential stage or the link to the actual computed sum.
- Do not assume the requested Delta s bound as an execution premise.
- The basic unshifted Algorithm 3.1 is selected, not the shifted log-sum-exp method.
- No result-bearing common Lean definitions or source-faithful skeleton are supplied to either condition.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
