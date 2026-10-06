-- NumStability/Algorithms/QR/HouseholderSpecSupport.lean
--
-- Declaration-free import-only compatibility wrapper. This historical path is
-- retained so existing imports keep resolving; it declares nothing itself and
-- forwards to the canonical module(s) below.
--
-- Reorganization wave R11 (phase branch B0003) relocated the support
-- declarations this wrapper forwarded to, so the single support import is
-- retargeted to the canonical destination:
--   NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport
--     -> NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels

import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels

/-!
# HouseholderSpecSupport (compatibility wrapper)

Declaration-free import-only wrapper retained for backward-compatible imports.

Canonical module(s):

* `NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels`

Documented by wave R11 under phase branch B0003; this module adds no
declaration and changes no public surface.
-/
