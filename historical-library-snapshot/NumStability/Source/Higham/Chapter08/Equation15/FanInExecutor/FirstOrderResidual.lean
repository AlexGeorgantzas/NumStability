-- NumStability/Source/Higham/Chapter08/Equation15/FanInExecutor/FirstOrderResidual.lean
--
-- Documented declaration-free bridge module delivered by reorganization wave R03
-- (phase branch B0005, projection P0005) under the reviewed fanIn7 private-closure
-- repair recorded in reviews/R03-route-amendment.md.
--
-- The pre-activation route split `NumStability.Algorithms.HighamChapters1To9SourceClosure`
-- between this module and the Equation 18 destination, but the owner's private helper
-- `higham8_18_fanIn7AbsApply_nonneg` is used by BOTH of its public theorems, and a Lean
-- private declaration is module-scoped, so that split could not compile. The amended
-- route delivers the indivisible three-declaration component at the Equation 18
-- destination; this module remains so the frozen R0005 consumer postimages and the
-- historical wrapper, which import it, keep resolving with an identical surface.

import NumStability.Source.Higham.Chapter08.Equation18.FanInExecutor.FirstOrderForwardError

/-!
# FirstOrderResidual (declaration-free bridge)

The Equation 8.15 first-order residual theorem
`NumStability.higham8_15_fanIn7Executor_residual_family_firstOrder` lives at
`NumStability.Source.Higham.Chapter08.Equation18.FanInExecutor.FirstOrderForwardError`
together with the Equation 8.18 theorem and their shared private helper, per the
reviewed R03 route amendment. This module re-exports that destination.
-/
