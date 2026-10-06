-- Analysis/Norms/Core.lean
--
-- Declaration-free aggregate for the reusable norms APIs.

import NumStability.Analysis.Asymptotics
import NumStability.Analysis.Conditioning
import NumStability.Analysis.LinearOperators
import NumStability.Analysis.MatrixNorms
import NumStability.Analysis.OperatorNorms
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.VectorNorms

/-!
# Reusable norms aggregate

This module keeps the historical `NumStability.Analysis.Norms.Core` path
importable for its reusable mathematical subset while declarations live in
focused semantic owners. Numbered Chapter 6 results are available through
`NumStability.Source.Higham.Chapter06.Norms` or the broader historical
`NumStability.Analysis.Norms` facade.
-/
