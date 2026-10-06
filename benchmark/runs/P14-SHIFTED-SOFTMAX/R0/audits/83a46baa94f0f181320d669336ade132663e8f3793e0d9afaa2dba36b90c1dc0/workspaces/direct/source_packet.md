# P14-SHIFTED-SOFTMAX: Theorem 4.3 shifted softmax normwise first-order forward-error bound

## Authoritative source

- Authors: Pierre Blanchard, Desmond J. Higham, Nicholas J. Higham
- Title: Accurately Computing the Log-Sum-Exp and Softmax Functions
- Year: 2021
- PDF SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Exact source locations

- Section 4, printed page(s) 2321-2324, PDF page(s) 11-14: Algorithm 4.1, shifted exponential sum error (4.6), and Theorem 4.3 equation (4.11)

## Target clarification

- For any real vector with at least two entries, choose any maximal entry a=x_k, evaluate every shifted exponential with one rounded subtraction and relative exponential error, recursively sum all nonmaximal computed exponentials, and divide each computed exponential by 1+the computed sum with a rounded division.
- Formalize the source Theorem 4.3: infinity-norm forward error of the computed softmax divided by the infinity norm of exact softmax is at most [n+2+2(xmax-xmin)]u+O(u^2). Preserve the full componentwise bound used immediately before the theorem if included.
- The quadratic remainder is uniform over admissible local errors for fixed input/order.

## Scope constraints

- Keep all n softmax outputs, including the selected maximum, and omit only the selected maximum from the shifted denominator sum.
- The source first-order model treats 1+the computed sum as the denominator of the final rounded division; do not insert an additional independently rounded denominator step that changes the displayed coefficient.
- Do not narrow to a particular location of the maximum, drop the recursive sum, or assume the result as an execution certificate.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
