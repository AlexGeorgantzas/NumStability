# RUMP12-THM3.4: Rump Theorem 3.4 and equation (3.5): an unrestricted-length absolute forward-error bound for ordinary recursive summation in rounding to nearest

## Authoritative source

- Authors: Siegfried M. Rump
- Title: Error Estimation of Floating-Point Summation and Dot Product
- Year: 2012
- PDF SHA-256: `4b23ffc2f7588ddc5218b914e520acf6c6c1ba0ec07bdae221f3d692fc254706`

## Exact source locations

- Sections 1–2, printed page(s) 1–3, PDF page(s) 1–3: Binary floating-point set F, round-to-nearest operation, unit roundoff u, no overflow but underflow allowed
- Section 3, Algorithm 3.1, printed page(s) 3, PDF page(s) 3: Start from the first floating input and recursively add subsequent inputs in their given order
- Section 3, Theorem 3.4 and equation (3.5), printed page(s) 4, PDF page(s) 4: Absolute error at most (n−1)u times the exact sum of absolute input values, without a small-nu condition

## Target clarification

- For every positive length n and vector p of n representable binary floating-point numbers, let s_hat be Algorithm 3.1's left-to-right recursive sum computed by rounding each addition to nearest. Formalize |s_hat − Σ_i p_i| ≤ (n−1)u Σ_i |p_i|.
- The bound has no requirement n*u < 1 and no higher-order gamma factor. It is not merely the classical gamma_(n−1) estimate under its smallness guard.
- Include n=1, for which the computed sum is the first input and the right-hand side is zero.

## Scope constraints

- Do not narrow the inputs to nonnegative numbers, one sign, no cancellation, a fixed n, or a small-nu regime.
- Use genuine round-to-nearest semantics for representable inputs. An abstract relative-error law |delta| ≤ u alone is insufficient to express this sharper theorem; any additional rounding/format assumptions must describe the source arithmetic, not assume the target inequality.
- The paper excludes overflow and explicitly allows underflow. Do not add a no-underflow hypothesis.
- Preserve the exact absolute forward-error conclusion and the precise factor (n−1)u; a bound with gamma, 1.01, or an unspecified constant is not the selected result.
- The source uses n≥1 and the inputs' original order. A mathematically equivalent Lean indexing convention is acceptable if it does not change that order.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
