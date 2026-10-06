-- NumStability/Source/Higham/Chapter19/Sensitivity.lean
--
-- Import-only Chapter 19 sensitivity aggregate completed at R11 integration.
--
-- This path remains the family entry point. Its former declarations moved
-- unchanged to `Sensitivity.Bounds.Results`, while the aggregate also exports
-- the canonical `Sensitivity.Closure` descendant.

import NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

/-!
# Chapter 19 sensitivity

Declaration-free complete aggregate for the Chapter 19 sensitivity family.
It preserves the historical entry point while exposing every canonical
descendant.
-/
