# P14-T2: Theorem 3.3 forward-error bound for the basic softmax algorithm

## Authoritative source

- Authors: Pierre Blanchard, Desmond J. Higham, Nicholas J. Higham
- Title: Accurately Computing the Log-Sum-Exp and Softmax Functions
- Year: 2021
- PDF SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Exact source locations

- Section 1, printed page(s) 2311, PDF page(s) 1: Softmax definition (1.2)
- Section 1, printed page(s) 2314, PDF page(s) 4: Standard floating-point model (1.7)
- Section 3, printed page(s) 2316, PDF page(s) 6: Algorithm 3.1 for the basic log-sum-exp and softmax evaluation
- Section 3, printed page(s) 2317, PDF page(s) 7: Exponential and recursive-summation error models (3.1)-(3.2)
- Section 3, printed page(s) 2318, PDF page(s) 8: Componentwise softmax error derivation following equation (3.5)
- Section 3, printed page(s) 2319, PDF page(s) 9: Theorem 3.3 and equation (3.6)

## Target clarification

- For a positive integer n and x in R^n, let g be the exact softmax vector, g_j = exp(x_j)/(sum_i exp(x_i)).
- Model the basic softmax part of Algorithm 3.1: compute each exponential, form the denominator by recursive floating-point summation, and perform the final componentwise divisions.
- In the absence of overflow and underflow, formalize Theorem 3.3: the computed vector ghat satisfies ||g-ghat||_infinity/||g||_infinity <= (n+3)*u + O(u^2).
- The preceding derivation expresses the componentwise result as ghat_j = g_j*(1+tau_j), with |tau_j| <= (n+3)*u + O(u^2).
- Interpret O(u^2) uniformly over admissible local rounding errors: for fixed n and x, there exist constants C > 0 and u_0 > 0, independent of u and of the admissible local errors, such that every admissible run with 0 < u <= u_0 has the stated componentwise and normwise error bounded by (n+3)*u + C*u^2.

## Scope constraints

- Use positive dimension, nonnegative unit roundoff u, and the exact softmax definition from the paper.
- Retain the exponentiation relative errors, recursive denominator summation, and final divisions under the paper's standard model.
- Preserve the source assumption that overflow and underflow are absent.
- Use the packet's explicit uniform quantified-remainder meaning for O(u^2); do not replace it by an unrelated finite error radius or allow C and u_0 to vary with u or the local errors.
- The selected algorithm is the unshifted basic Algorithm 3.1, not a shifted or alternative softmax method.
- Represent the computation and its local error assumptions rather than assuming the requested output-error conclusion.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
