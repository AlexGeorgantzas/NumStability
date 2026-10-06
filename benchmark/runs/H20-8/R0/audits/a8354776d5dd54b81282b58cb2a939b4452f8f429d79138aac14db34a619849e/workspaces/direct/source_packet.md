# H20-8: Higham Problem 20.8: evaluate the matrix-only least-squares backward error at the zero vector

## Authoritative source

- Authors: Nicholas J. Higham
- Title: Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 20: The Least Squares Problem, Problem 20.8
- Year: 2002
- PDF SHA-256: `7ca85d5caf3ffd5ae90fb315e9b4e00912e174881bcf969e7ba0a7b3ce9ec814`

## Exact source locations

- Chapter 20, Theorem 20.5 and discussion after equation (20.20), printed page(s) 392-393, PDF page(s) 12-13: The theorem excludes y = 0; theta tending to infinity forbids Delta b
- Chapter 20, Problems, printed page(s) 406, PDF page(s) 26: Problem 20.8 explicitly asks for eta_F(0) at theta = infinity, Delta b = 0

## Target clarification

- Let A be a real m-by-n matrix with m >= n, b a real m-vector, and let the approximate solution y be exactly the zero n-vector.
- The matrix-only backward error is the minimum Frobenius norm of Delta A such that y = 0 is a least-squares minimizer for (A + Delta A, b); Delta b is identically zero. This is the theta = infinity convention described after equation (20.20).
- Evaluate this error over the full b domain: it is zero if b = 0; otherwise it equals the Euclidean norm of A-transpose times b divided by the Euclidean norm of b.
- Formalize both the minimum value and an admissible Delta A attaining it. Do not substitute a generic nonzero-y theorem or merely state a theta-to-infinity limit.

## Scope constraints

- The target argument y is zero, despite Theorem 20.5 itself assuming y is nonzero.
- Cover both b = 0 and b != 0; do not narrow the source domain.
- Keep Delta b = 0 and use Frobenius norm for Delta A and Euclidean norm for vectors.
- The minimization condition is least-squares optimality for the perturbed matrix, not an exact solution requirement.
- Do not assume the closed-form value or an equivalent certificate as a hypothesis.
- The source uses a minimum, not merely an infimum: the formalization must account for attainment.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
