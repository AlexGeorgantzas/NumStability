# Case Study: A Compiling Lean Theorem That Weakens the Source Result

## Purpose

This case illustrates why Lean compilation is necessary but insufficient for
validating an autoformalization. Lean can certify a theorem exactly as stated
while the statement itself fails to preserve the mathematical claim selected
from the source paper.

The example is HighamBench task `P11-T1`, derived from equation (16) of:

> Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou, "A note on the
> error analysis of classical Gram-Schmidt," *Numerische Mathematik* 105(2),
> 299-313, 2006. DOI: 10.1007/s00211-006-0042-1.

The frozen source is the published journal PDF. Equation (16) appears on PDF
page 10, printed page 308.

## Original Mathematical Claim

In the first-column case of the floating-point analysis of the CGS-P
Gram-Schmidt algorithm, the paper obtains

\[
q_1 = (I+G_1)a_1/r_{11},
\qquad \lVert G_1\rVert_2 \leq \varepsilon_M,
\]

where \(\lVert G_1\rVert_2\) is the induced matrix 2-norm and
\(\varepsilon_M\) is the machine unit. It then derives the exact residual
identity

\[
A_1-Q_1R_1 = a_1-q_1r_{11} = -G_1a_1
\]

and the bound

\[
\lVert A_1-Q_1R_1\rVert_2
= \lVert a_1-q_1r_{11}\rVert_2
\leq \lVert G_1\rVert_2\lVert a_1\rVert_2
\leq \varepsilon_M\lVert a_1\rVert_2.
\tag{16}
\]

This is not merely a generic matrix-vector inequality. It connects a computed
Gram-Schmidt residual to the local floating-point perturbation model.

## Lean Benchmark Target

The corresponding target was:

```lean
theorem p11_t1_first_column_residual_action {n : ℕ}
    (G : P11Matrix n) (a : Fin n → ℝ) (epsilon : ℝ)
    (hG : p11FrobNorm G ≤ epsilon) :
    p11VecNorm (p11MatVec G a) ≤ epsilon * p11VecNorm a := by
  sorry
```

Here `p11FrobNorm` is explicitly defined as the Frobenius norm, `p11VecNorm`
as the Euclidean vector norm, and `p11MatVec` as ordinary matrix-vector
multiplication.

The public target file contains `sorry` because it is the proof-completion
task supplied to the benchmark agent. Separately, the benchmark's private
construction-validation record reports successful compilation
(`compile_exit_code = 0`) for completed proofs in both the no-library and
with-library conditions. Thus the statement is mechanically provable; the
problem is its relationship to the paper, not its consistency or provability.

## Why the Formalization Is Not Faithful

### 1. It changes the matrix norm

The source assumes

\[
\lVert G_1\rVert_2 \leq \varepsilon_M,
\]

using the induced matrix 2-norm. The Lean target instead assumes

\[
\lVert G\rVert_F \leq \varepsilon.
\]

The Frobenius condition is strictly stronger. For example, for
\(G=\varepsilon I_2\),

\[
\lVert G\rVert_2=\varepsilon,
\qquad
\lVert G\rVert_F=\sqrt{2}\,\varepsilon.
\]

Therefore the paper's norm hypothesis can hold while the Lean hypothesis
fails. Replacing the source norm with a convenient norm supported by a nearby
library theorem reduces the cases covered by the formalization.

### 2. It removes the algorithmic residual

Equation (16) concerns

\[
A_1-Q_1R_1=a_1-q_1r_{11}.
\]

The Lean statement has no `A1`, `Q1`, `R1`, `q1`, or `r11`, and it does not
state the residual identity. It only bounds \(Ga\). Consequently, the theorem
can be proved without formalizing or reasoning about Gram-Schmidt at all.

### 3. It removes the floating-point interpretation

In the paper, \(G_1\) is the perturbation produced by standard floating-point
error bounds for the computed first column, and \(\varepsilon_M\) is the
machine unit. In Lean, `G` and `epsilon` are arbitrary real data, with no
connection to a rounding model or computed algorithm.

### 4. It preserves only one generic inequality used inside the source proof

The Lean conclusion resembles the middle estimate

\[
\lVert G_1a_1\rVert_2
\leq \lVert G_1\rVert_2\lVert a_1\rVert_2,
\]

but changes its norm hypothesis and detaches it from the residual whose error
the paper is analyzing. It is therefore a related surrogate, not a
formalization of equation (16).

## Bidirectional Faithfulness Test

Let \(S\) be the complete source claim, including its surrounding algorithmic
context, and let \(T\) be the mathematical meaning of the Lean target.

| Test | Result | Reason |
|---|---|---|
| Does \(T\) imply \(S\)? | No | \(T\) supplies neither the computed residual identity nor the Gram-Schmidt and floating-point interpretation. Its Frobenius hypothesis also excludes matrices allowed by the source 2-norm bound. |
| Does \(S\) imply \(T\)? | No | \(S\) concerns the particular perturbation and first-column residual generated in CGS-P, whereas \(T\) is universally quantified over arbitrary matrices satisfying a different norm certificate. |

The two statements are neither equivalent nor a clean strengthening of one
another. The Lean theorem is best classified as a **surrogate**.

## Why Compilation Does Not Detect This

Lean checks that the proof term establishes the declared Lean proposition from
its declared hypotheses. It does not know that:

- the intended matrix norm was the induced 2-norm;
- `G` was supposed to arise from a floating-point computation;
- the selected paper result included a Gram-Schmidt residual identity; or
- the benchmark claimed correspondence with equation (16).

Once the weakened or altered statement has been encoded, a completely valid
Lean proof certifies only that altered statement. Kernel acceptance cannot by
itself certify source faithfulness.

## Methodological Lesson

A benchmark task should be audited before proof search or library matching:

1. Extract and freeze the complete source contract, including surrounding
   hypotheses, dimensions, norm semantics, constants, algorithmic quantities,
   and every component of the conclusion.
2. Translate the Lean declaration back into mathematics without looking at the
   source.
3. Compare source and Lean clauses one by one.
4. Test both implication directions.
5. Require a counterexample or proof of equivalence for every changed
   assumption, domain, constant, norm, or conclusion.
6. Keep semantic faithfulness separate from compilation and proof-completeness
   checks.

Under a strict benchmark standard, only logical equivalence or a previously
approved representation-preserving reformulation should count as fully
faithful. A convenient theorem that compiles but omits the algorithmic result
must not be reported as a formalization of the original equation.

## Local Evidence

- Original PDF:
  `<library-repo>/paper_bencmark/reference_papers/P11_A note on the error analysis of classical Gram–Schmidt.pdf`
- Lean target:
  `<library-repo>/paper_bencmark/highambench/tasks/P11/T1/Target.lean`
- Shared definitions:
  `<library-repo>/paper_bencmark/highambench/shared/HighamBench/P11Definitions.lean`
- Construction validation:
  `<library-repo>/paper_bencmark/highambench/metadata/evidence/construction_validation_P11_direct_fallback.json`

## Related Audit Method

The bidirectional implication test follows the semantic-correctness framework
in Theodore Meek, Siyuan Ge, Di Qiu Xiang, Simon Chess, and Vasily Ilin,
"Formalizing Numerical Analysis: An Agent Pipeline and Quality Audit Beyond
Kernel Acceptance," arXiv:2606.14000, 2026. That work also identifies
incomplete statements, added hypotheses, and parameter restrictions as common
formalization failures invisible to kernel acceptance.
