# HI21-LEM2.2: Lemma 2.2 first explicit forward-error expression for a general binary summation tree

## Authoritative source

- Authors: Eric Hallman, Ilse C. F. Ipsen
- Title: Deterministic and Probabilistic Error Bounds for Floating Point Summation Algorithms
- Year: 2021
- PDF SHA-256: `cce25923a86d5d2051a079ad4ae7ea965f1dde97ffb6d3bf6462d069968fd1c6`

## Exact source locations

- Section 2.1, printed page(s) 3-4, PDF page(s) 3-4: Algorithm 2.1, computational tree, equation (2.1), and Lemma 2.2 equation (2.3)

## Target clarification

- For an arbitrary finite binary summation tree with real leaves x_1,...,x_n and one rounded addition at each internal node, let s_k be each exact partial sum and delta_k the relative error of its actual addition, |delta_k|<=u. Child computations, not exact child sums, are the operands of each rounded addition.
- Formalize the exact Lemma 2.2 identity: final computed sum minus exact sum is the sum over all internal nodes k of s_k*delta_k times the product of (1+delta_j) for strict internal ancestors j of k, through the root. A flattened list of node contributions carrying their ancestor-product factors is acceptable if it has the same complete tree-wide content.
- The result holds for arbitrary tree shape and arbitrary signs and includes the one-leaf zero-error case. No probabilistic assumptions or later Theorem 2.4 bound belong to this task.

## Scope constraints

- Retain an actual binary summation execution linked to the local delta witnesses; do not simply assume the final error identity.
- Every internal node, including the root, contributes once, and the ancestor product includes no factor from the node itself.
- The target must not collapse the identity to a bare restatement of the local error recurrence.

The PDF is authoritative. This packet identifies the selected result and disambiguates its scope; it is not a Lean target or a proof.
