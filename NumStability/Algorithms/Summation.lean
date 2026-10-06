import NumStability.Algorithms.Summation.Accumulator
import NumStability.Algorithms.Summation.Compensated
import NumStability.Algorithms.Summation.DoublyCompensated
import NumStability.Algorithms.Summation.Insertion
import NumStability.Algorithms.Summation.Pairwise
import NumStability.Algorithms.Summation.PlusMinus
import NumStability.Algorithms.Summation.Recursive
import NumStability.Algorithms.Summation.Tree

/-!
# Summation algorithms

This complete published surface re-exports the canonical recursive, pairwise,
tree-based, insertion, compensated, and accumulator summation families.
Reusable code should prefer narrow semantic leaves such as `Recursive.Core`,
`Pairwise.Core`, and `Tree.Chain`; the broad family umbrellas intentionally
retain supported Chapter 4 source declarations.
-/
