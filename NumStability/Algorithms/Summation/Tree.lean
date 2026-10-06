import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Algorithms.Summation.Tree.Chain
import NumStability.Algorithms.Summation.Tree.Core

/-!
# Summation-tree family umbrella

This is the canonical complete entry point for tree-based summation. New code
may import `Tree.Core`, `Tree.Balanced`, or `Tree.Chain` when it needs
a narrower dependency surface. The historical `Algorithms.SumTree` path
forwards here.
-/
