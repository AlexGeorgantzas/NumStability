import NumStability.Analysis.Error
import NumStability.Analysis.FirstOrderFramework
import NumStability.Analysis.Rounding
import NumStability.Analysis.Stability
import NumStability.FloatingPoint.Model

/-!
# Reusable NumStability foundations

This entry point exposes the source-independent floating-point model and the
small foundational error-analysis surface.  It is deliberately narrower than
`NumStability.All`; algorithm-family entry points will be added as their APIs are
classified during migration.
-/
