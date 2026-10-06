# P14-LOGSUMEXP: Absolute forward-error bound immediately preceding Theorem 3.2 for basic log-sum-exp

## Authoritative source

- Authors: Pierre Blanchard, Desmond J. Higham, Nicholas J. Higham
- Title: Accurately Computing the Log-Sum-Exp and Softmax Functions
- Year: 2021
- PDF SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Exact source locations

- Section 3, printed page(s) 2316, PDF page(s) 6: Unshifted Algorithm 3.1
- Section 3, printed page(s) 2317-2318, PDF page(s) 7-8: Exponential evaluation (3.1) and positive sum error (3.3)
- Section 3, printed page(s) 2318, PDF page(s) 8: Absolute error bound |y-yHat| <= u|y|+(n+1)u+O(u^2), immediately before Theorem 3.2

## Target clarification

- For positive n and x in R^n, let s = sum_i exp(x_i) and y = log(s). Use the unshifted basic Algorithm 3.1 with each exponential evaluated under relative error at most u, recursive floating-point summation of those exponentials, and a final rounded logarithm under relative error at most u.
- Formalize the absolute forward-error estimate immediately preceding Theorem 3.2: |y-yHat| <= u*|y| + (n+1)*u + O(u^2). This statement is chosen instead of the following relative quotient, so it covers the case y = 0 as well.
- The O(u^2) remainder must be uniform over admissible local errors at fixed n and x. It may be expressed by constants C>0 and u0>0 independent of the individual execution, such that the displayed bound with +C*u^2 holds for every admissible execution with 0<u<=u0.

## Scope constraints

- Preserve the exponential errors, actual recursive summation, final logarithm and its rounding error, and the no-overflow/no-underflow relative model.
- Do not assume the requested output-error estimate or replace the basic algorithm with a shifted one.
- Do not narrow the x-domain by requiring y to be nonzero.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
