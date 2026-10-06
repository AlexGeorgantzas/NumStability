-- NumStability/Source/Higham/Chapter19/StoredLoop.lean
--
-- Import-only Chapter 19 stored-loop aggregate completed at R11 integration.
--
-- This path remains the family entry point. Its former declarations moved
-- unchanged to `StoredLoop.Perturbation.Bridge`, while the aggregate also
-- exports the canonical all-pivots and strong-model descendants.

import NumStability.Source.Higham.Chapter19.StoredLoop.AllPivots
import NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge
import NumStability.Source.Higham.Chapter19.StoredLoop.StrongModel

/-!
# Chapter 19 stored-loop analysis

Declaration-free complete aggregate for the Chapter 19 stored-loop family.
It preserves the historical entry point while exposing every canonical
descendant.
-/
