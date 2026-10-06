-- Algorithms/Summation/Compensated/Kahan/Internal/FinFold.lean

import Mathlib.Data.List.OfFn

namespace NumStability.Compensated.Kahan.Internal

/-!
# Internal finite-fold bridge

This unsupported owner-local module contains implementation infrastructure
shared by the Kahan Affine and Coupled coefficient proofs.  It is not part of
the supported Kahan public API.
-/

/-- Internal bridge between folding a `List.ofFn` and folding its finite
index type directly.  This theorem is unsupported outside the owning Kahan
coefficient implementation. -/
theorem listFoldlOfFn_eq_finFoldl {α β : Type*}
    (f : β → α → β) :
    ∀ (n : ℕ) (g : Fin n → α) (init : β),
      (List.ofFn g).foldl f init =
        Fin.foldl n (fun acc i => f acc (g i)) init
  | 0, _g, init => by
      simp [List.ofFn_zero]
  | n + 1, g, init => by
      rw [Fin.foldl_succ, List.ofFn_succ, List.foldl_cons]
      exact listFoldlOfFn_eq_finFoldl f n (fun i => g i.succ)
        (f init (g 0))

end NumStability.Compensated.Kahan.Internal
