import NumStability.Analysis.Norms.Core
import NumStability.Source.Higham.Chapter06.Norms

/-!
# Historical norms import

Compatibility facade preserving the complete declaration surface formerly
provided by `NumStability.Analysis.Norms`. New reusable code should import a
canonical semantic family such as `NumStability.Analysis.VectorNorms` or
`NumStability.Analysis.MatrixNorms`; source-facing Higham Theorem 6.4 code
should import its Chapter 6 source module.
-/
