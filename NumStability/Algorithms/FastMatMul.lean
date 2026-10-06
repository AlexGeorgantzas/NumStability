import NumStability.Algorithms.FastMatMul.Internal.LegacyBounds
import NumStability.Algorithms.FastMatMul.Recurrences
import NumStability.Source.Higham.Chapter23

/-!
# Fast matrix multiplication

Historical complete-family entry point for fast matrix multiplication. It
exports the reusable recurrence API, the Chapter 23 formalization, and the
unsupported legacy declarations that this path exposed before the semantic
split. New code should import a specific reusable module or the canonical
`NumStability.Source.Higham.Chapter23` source entry point.
-/
