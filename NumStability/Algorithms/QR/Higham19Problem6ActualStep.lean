import NumStability.Algorithms.QR.HouseholderMatrixStep

/-!
# Higham Problem 19.6: actual computed-reflector panel step

This module isolates the implementation-backed componentwise construction and
application bridge used by the proof of Theorem 19.6.  It deliberately keeps
the computed normalized vector distinct from its exact comparison vector.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave19

/-- **Actual construction-and-application form of Higham (19.39)--(19.40).**

The vector passed to the rounded panel application is the genuinely computed
`fl_householderNormalizedVector`.  Its exact comparison vector is the
normalized exact Householder vector constructed from the same input column.
Thus this theorem includes both the vector-construction error (Higham (18.3))
and every rounded operation in the application kernel.  Componentwise,

`|f_i| ≤ u |A_ij| + gamma_(11m+23) |v_i| sum_s |v_s| |A_sj|`.

This is the executor-backed bridge needed for Problem 19.6; in particular it
does not identify the computed normalized vector with the exact one. -/
theorem fl_householderConstructApplyMatrixRect_entrywise_backward_error
    (fp : FPModel) (m p : ℕ) (hm : 0 < m)
    (x : Fin m → ℝ) (A : Fin m → Fin p → ℝ) (hx : x ≠ 0)
    (hvalid : gammaValid fp (11 * m + 23))
    (i : Fin m) (j : Fin p) :
    |fl_householderApplyMatrixRect fp m p
          (fl_householderNormalizedVector fp hm x) 1 A i j -
        matMulRect m m p
          (householder m
            (householderNormalizedVector m
              (householderVector hm x) (householderBetaFromScale hm x)) 1)
          A i j| ≤
      fp.u * |A i j| + gamma fp (11 * m + 23) *
        |householderNormalizedVector m
          (householderVector hm x) (householderBetaFromScale hm x) i| *
        (∑ s : Fin m,
          |householderNormalizedVector m
            (householderVector hm x) (householderBetaFromScale hm x) s| *
          |A s j|) := by
  let v : Fin m → ℝ :=
    householderNormalizedVector m
      (householderVector hm x) (householderBetaFromScale hm x)
  let vhat : Fin m → ℝ := fl_householderNormalizedVector fp hm x
  have hvalidVec : gammaValid fp (8 * m + 16) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalidEps : gammaValid fp (5 * m + 10) :=
    gammaValid_mono fp (by omega) hvalid
  have hvec : HouseholderVectorError m v vhat (gamma fp (5 * m + 10)) := by
    simpa [v, vhat] using fl_householderVectorError fp hm x hx hvalidVec
  have hraw :=
    fl_householderApply_normalized_entrywise_error fp (5 * m + 10) m
      v vhat (gamma fp (5 * m + 10)) (fun s => A s j)
      hvec (gamma_nonneg fp hvalidEps) le_rfl (by
        simpa [show 2 * (5 * m + 10) + m + 3 = 11 * m + 23 by omega]
          using hvalid) i
  simpa [v, vhat,
    show 2 * (5 * m + 10) + m + 3 = 11 * m + 23 by omega,
    fl_householderApplyMatrixRect, matMulRect, matMulVec] using hraw

/-- Row-growth collapse of the genuine construction-and-application error.

The fold keeps the two terms of (19.40) visible: `u` for the componentwise
subtraction term and `2 gamma_(11m+23) m Vmax alphaMax` for the normalized
reflector term. -/
theorem householderConstructApplyMatrixRect_entrywise_le_rowGrowth
    (fp : FPModel) (m p : ℕ) (hm : 0 < m)
    (x : Fin m → ℝ) (A : Fin m → Fin p → ℝ) (hx : x ≠ 0)
    (α : Fin m → ℝ) (γtil Vmax αmax : ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hα : ∀ s, 0 ≤ α s) (hVmax : 0 ≤ Vmax) (_hαmax : 0 ≤ αmax)
    (hAα : ∀ s j', |A s j'| ≤ α s)
    (hv2α : ∀ s,
      |householderNormalizedVector m
        (householderVector hm x) (householderBetaFromScale hm x) s| ≤ 2 * α s)
    (hVbound : ∀ s,
      |householderNormalizedVector m
        (householderVector hm x) (householderBetaFromScale hm x) s| ≤ Vmax)
    (hαbound : ∀ s, α s ≤ αmax)
    (hfold : fp.u +
      2 * gamma fp (11 * m + 23) * ((m : ℝ) * (Vmax * αmax)) ≤ γtil)
    (i : Fin m) (j : Fin p) :
    |fl_householderApplyMatrixRect fp m p
          (fl_householderNormalizedVector fp hm x) 1 A i j -
        matMulRect m m p
          (householder m
            (householderNormalizedVector m
              (householderVector hm x) (householderBetaFromScale hm x)) 1)
          A i j| ≤ γtil * α i := by
  let v : Fin m → ℝ :=
    householderNormalizedVector m
      (householderVector hm x) (householderBetaFromScale hm x)
  have hraw :=
    fl_householderConstructApplyMatrixRect_entrywise_backward_error
      fp m p hm x A hx hvalid i j
  have hγ : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hdot : (∑ s : Fin m, |v s| * |A s j|) ≤
      (m : ℝ) * (Vmax * αmax) := by
    calc
      (∑ s : Fin m, |v s| * |A s j|) ≤
          ∑ _s : Fin m, Vmax * αmax := by
            apply Finset.sum_le_sum
            intro s _
            have hAs : |A s j| ≤ αmax := le_trans (hAα s j) (hαbound s)
            exact mul_le_mul (by simpa [v] using hVbound s) hAs
              (abs_nonneg _) hVmax
      _ = (m : ℝ) * (Vmax * αmax) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
  have hdotNonneg : 0 ≤ ∑ s : Fin m, |v s| * |A s j| := by
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hdotMaxNonneg : 0 ≤ (m : ℝ) * (Vmax * αmax) := by positivity
  have houter :
      gamma fp (11 * m + 23) * |v i| *
          (∑ s : Fin m, |v s| * |A s j|) ≤
        (2 * gamma fp (11 * m + 23) *
          ((m : ℝ) * (Vmax * αmax))) * α i := by
    have hv : |v i| ≤ 2 * α i := by simpa [v] using hv2α i
    have hprod : |v i| * (∑ s : Fin m, |v s| * |A s j|) ≤
        (2 * α i) * ((m : ℝ) * (Vmax * αmax)) :=
      mul_le_mul hv hdot hdotNonneg
        (mul_nonneg (by norm_num) (hα i))
    calc
      gamma fp (11 * m + 23) * |v i| *
          (∑ s : Fin m, |v s| * |A s j|) =
        gamma fp (11 * m + 23) *
          (|v i| * (∑ s : Fin m, |v s| * |A s j|)) := by ring
      _ ≤ gamma fp (11 * m + 23) *
          ((2 * α i) * ((m : ℝ) * (Vmax * αmax))) :=
        mul_le_mul_of_nonneg_left hprod hγ
      _ = (2 * gamma fp (11 * m + 23) *
          ((m : ℝ) * (Vmax * αmax))) * α i := by ring
  have hbudget :
      fp.u * |A i j| +
          gamma fp (11 * m + 23) * |v i| *
            (∑ s : Fin m, |v s| * |A s j|) ≤
        (fp.u + 2 * gamma fp (11 * m + 23) *
          ((m : ℝ) * (Vmax * αmax))) * α i := by
    calc
      fp.u * |A i j| +
          gamma fp (11 * m + 23) * |v i| *
            (∑ s : Fin m, |v s| * |A s j|) ≤
        fp.u * α i +
          (2 * gamma fp (11 * m + 23) *
            ((m : ℝ) * (Vmax * αmax))) * α i :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hAα i j) fp.u_nonneg) houter
      _ = (fp.u + 2 * gamma fp (11 * m + 23) *
          ((m : ℝ) * (Vmax * αmax))) * α i := by ring
  calc
    |fl_householderApplyMatrixRect fp m p
          (fl_householderNormalizedVector fp hm x) 1 A i j -
        matMulRect m m p
          (householder m
            (householderNormalizedVector m
              (householderVector hm x) (householderBetaFromScale hm x)) 1)
          A i j| ≤
      fp.u * |A i j| + gamma fp (11 * m + 23) *
        |householderNormalizedVector m
          (householderVector hm x) (householderBetaFromScale hm x) i| *
        (∑ s : Fin m,
          |householderNormalizedVector m
            (householderVector hm x) (householderBetaFromScale hm x) s| *
          |A s j|) := hraw
    _ ≤ (fp.u + 2 * gamma fp (11 * m + 23) *
        ((m : ℝ) * (Vmax * αmax))) * α i := by simpa [v] using hbudget
    _ ≤ γtil * α i :=
      mul_le_mul_of_nonneg_right hfold (hα i)

end NumStability.Wave19
