import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients

open Classical

namespace NumStability

/-!
# Kahan summation: finite-format correction exactness

Reusable finite binary round-to-even realization of the exact correction
subtraction required by ordinary Kahan summation.
-/

/-- Per-step exact correction subtraction for the safe-completion model's Kahan
trace, discharged from finite equation (4.7).

For each step either the Dekker magnitude order `|yᵢ| ≤ |tempᵢ|` holds with
`tempᵢ + yᵢ` in normal range (so `FastTwoSumFiniteCertificate.of_base2_abs_le`
makes `tempᵢ - sᵢ` representable), or `tempᵢ = 0` (first step / cancellation, so
`sᵢ = yᵢ` and `tempᵢ - sᵢ = -yᵢ` is representable). -/
theorem kahanFF_kahan_correctionSub_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hY : ∀ i : Fin n,
      fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).y)
    (hstep : ∀ i : Fin n,
      (fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).temp ∧
        |(kahanTrace (kahanFF_model fmt) v i).y| ≤
          |(kahanTrace (kahanFF_model fmt) v i).temp| ∧
        fmt.finiteNormalRange
          ((kahanTrace (kahanFF_model fmt) v i).temp +
            (kahanTrace (kahanFF_model fmt) v i).y)) ∨
        (kahanTrace (kahanFF_model fmt) v i).temp = 0) :
    KahanPrefixCorrectionSubExact (kahanFF_model fmt) v n (Nat.le_refl n) := by
  intro i
  show (kahanFF_model fmt).fl_sub (kahanTrace (kahanFF_model fmt) v i).temp
        (kahanTrace (kahanFF_model fmt) v i).s =
      (kahanTrace (kahanFF_model fmt) v i).temp -
        (kahanTrace (kahanFF_model fmt) v i).s
  have hs_def :
      (kahanTrace (kahanFF_model fmt) v i).s =
        (kahanFF_model fmt).fl_add (kahanTrace (kahanFF_model fmt) v i).temp
          (kahanTrace (kahanFF_model fmt) v i).y := rfl
  rcases hstep i with ⟨htemp_fin, horder, hrange⟩ | htemp0
  · have hs_eq :
        (kahanTrace (kahanFF_model fmt) v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (kahanTrace (kahanFF_model fmt) v i).temp
            (kahanTrace (kahanFF_model fmt) v i).y := by
      rw [hs_def]
      exact kahanFF_fl_add_eq_finiteRoundToEvenOp fmt (hY i) (Or.inl hrange)
    have hcert :
        FastTwoSumFiniteCertificate fmt
          (kahanTrace (kahanFF_model fmt) v i).temp
          (kahanTrace (kahanFF_model fmt) v i).y :=
      FastTwoSumFiniteCertificate.of_base2_abs_le fmt hbeta ht htemp_fin
        (hY i) horder hrange
    have hsub_fin :
        fmt.finiteSystem
          ((kahanTrace (kahanFF_model fmt) v i).temp -
            (kahanTrace (kahanFF_model fmt) v i).s) := by
      rw [hs_eq]; exact hcert.finite_a_sub_s
    exact kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin
  · have hs_eq :
        (kahanTrace (kahanFF_model fmt) v i).s =
          (kahanTrace (kahanFF_model fmt) v i).y := by
      rw [hs_def, htemp0, kahanFF_model_fl_add]; simp
    have hsub_fin :
        fmt.finiteSystem
          ((kahanTrace (kahanFF_model fmt) v i).temp -
            (kahanTrace (kahanFF_model fmt) v i).s) := by
      rw [htemp0, hs_eq]
      have h0 :
          (0 : ℝ) - (kahanTrace (kahanFF_model fmt) v i).y =
            -(kahanTrace (kahanFF_model fmt) v i).y := by ring
      rw [h0]; exact fmt.finiteSystem_neg (hY i)
    exact kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin

end NumStability
