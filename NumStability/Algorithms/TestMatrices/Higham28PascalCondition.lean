import NumStability.Algorithms.TestMatrices.Higham28PascalSpectral
import NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic
import Mathlib.Data.Nat.Choose.Bounds

namespace NumStability

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

noncomputable section

/-! # Higham Chapter 28: faithful Pascal condition growth

The ratio-one display on p. 520 is inconsistent with the norm bound printed
on the same page.  This file proves its invariant mathematical content: a
finite exponential sandwich and the resulting exact logarithmic rate.
-/

/-- Every entry is bounded by the exact l2 operator norm. -/
theorem abs_matrix_entry_le_opNorm2 {n : ℕ} (A : RSqMat n)
    (i j : Fin n) : |A i j| ≤ opNorm2 A := by
  let e : RVec n := finiteBasisVec j
  have he : vecNorm2 e = 1 := by
    simpa [e, finiteVecNorm2_fin] using
      (finiteVecNorm2_finiteBasisVec j)
  have haction := opNorm2Le_opNorm2 A e
  have hcol : Matrix.mulVec A e = fun k => A k j := by
    simpa [finiteMatVec, matMulVec] using finiteMatVec_finiteBasisVec A j
  change vecNorm2 (Matrix.mulVec A e) ≤ opNorm2 A * vecNorm2 e at haction
  rw [hcol, he, mul_one] at haction
  exact (abs_coord_le_vecNorm2 (fun k => A k j) i).trans haction

/-- Every entry of the order-`n+1` Pascal matrix is at most `4^n`. -/
theorem pascalMatrix_entry_le_four_pow (n : ℕ) (i j : Fin (n + 1)) :
    |pascalMatrix (n + 1) i j| ≤ (4 : ℝ) ^ n := by
  have hchoose : Nat.choose (i.val + j.val) j.val ≤ 2 ^ (i.val + j.val) :=
    Nat.choose_le_two_pow _ _
  have hij : i.val + j.val ≤ 2 * n := by omega
  have hpows : 2 ^ (i.val + j.val) ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) hij
  have hnat : Nat.choose (i.val + j.val) j.val ≤ 4 ^ n := by
    calc
      Nat.choose (i.val + j.val) j.val ≤ 2 ^ (i.val + j.val) := hchoose
      _ ≤ 2 ^ (2 * n) := hpows
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  rw [pascalMatrix_apply, abs_of_nonneg (by positivity)]
  exact_mod_cast hnat

/-- A direct finite upper bound sufficient for the exact logarithmic rate. -/
theorem opNorm2_pascalMatrix_le_nat_mul_four_pow (n : ℕ) :
    opNorm2 (pascalMatrix (n + 1)) ≤ (n + 1 : ℝ) * (4 : ℝ) ^ n := by
  let C : RSqMat (n + 1) := fun _ _ => (4 : ℝ) ^ n
  have hentry : ∀ i j : Fin (n + 1),
      |pascalMatrix (n + 1) i j| ≤ C i j := by
    intro i j
    exact pascalMatrix_entry_le_four_pow n i j
  have hfrob : frobNorm (pascalMatrix (n + 1)) ≤ frobNorm C :=
    frobNorm_le_of_entry_abs_le _ C (by intro i j; positivity) hentry
  have hopfrob : opNorm2 (pascalMatrix (n + 1)) ≤
      frobNorm (pascalMatrix (n + 1)) :=
    opNorm2_le_of_opNorm2Le _ (frobNorm_nonneg _)
      (opNorm2Le_of_frobNorm_self _)
  calc
    opNorm2 (pascalMatrix (n + 1)) ≤
        frobNorm (pascalMatrix (n + 1)) := hopfrob
    _ ≤ frobNorm C := hfrob
    _ = (n + 1 : ℝ) * (4 : ℝ) ^ n := by
      simpa [C] using
        (frobNorm_const (n := n + 1)
          (show 0 ≤ (4 : ℝ) ^ n by positivity))

/-- The final Pascal entry is the central binomial coefficient. -/
theorem pascalMatrix_last_last_eq_centralBinom (n : ℕ) :
    pascalMatrix (n + 1) (Fin.last n) (Fin.last n) =
      (Nat.centralBinom n : ℝ) := by
  simp [pascalMatrix_apply, Nat.centralBinom, two_mul]

/-- The central binomial coefficient is a lower bound for the Pascal norm. -/
theorem centralBinom_le_opNorm2_pascalMatrix (n : ℕ) :
    (Nat.centralBinom n : ℝ) ≤ opNorm2 (pascalMatrix (n + 1)) := by
  have h := abs_matrix_entry_le_opNorm2
    (pascalMatrix (n + 1)) (Fin.last n) (Fin.last n)
  rw [pascalMatrix_last_last_eq_centralBinom,
    abs_of_nonneg (by positivity)] at h
  exact h

/-- The proved inverse-norm symmetry turns the Pascal condition number into
the square of one matrix norm. -/
theorem pascalConditionTwo_eq_opNorm2_sq (n : ℕ) :
    pascalConditionTwo n = opNorm2 (pascalMatrix n) ^ 2 := by
  unfold pascalConditionTwo
  change opNorm2 (pascalMatrix n) * opNorm2 (pascalInverseMatrix n) = _
  rw [opNorm2_pascalInverseMatrix_eq_pascalMatrix]
  ring

/-- Finite, unconditional exponential sandwich for the Pascal condition
number.  Together with the already proved central-binomial Stirling theorem,
this is the faithful replacement for the false ratio-one display. -/
theorem pascalConditionTwo_exponential_sandwich (n : ℕ) :
    (Nat.centralBinom n : ℝ) ^ 2 ≤ pascalConditionTwo (n + 1) ∧
      pascalConditionTwo (n + 1) ≤
        ((n + 1 : ℝ) * (4 : ℝ) ^ n) ^ 2 := by
  rw [pascalConditionTwo_eq_opNorm2_sq]
  constructor
  · exact (sq_le_sq₀ (by positivity) (opNorm2_nonneg _)).2
      (centralBinom_le_opNorm2_pascalMatrix n)
  · exact (sq_le_sq₀ (opNorm2_nonneg _) (by positivity)).2
      (opNorm2_pascalMatrix_le_nat_mul_four_pow n)

/-- The exact logarithmic condition-number growth rate is `log 16`.  This is
the source-faithful leading-exponential interpretation of the p. 520 display. -/
theorem pascalConditionTwo_log_rate :
    Tendsto
      (fun n : ℕ =>
        Real.log (pascalConditionTwo (n + 1)) / (n : ℝ))
      atTop (nhds (Real.log 16)) := by
  have hlognat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa [Function.comp_def] using h.tendsto_div_nhds_zero
  have hlogsuccBase : Tendsto
      (fun n : ℕ => Real.log (n + 1 : ℝ) / (n + 1 : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hlognat.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun n : ℕ => (n + 1 : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
    have hadd : Tendsto
        (fun n : ℕ => (1 : ℝ) + (1 : ℝ) / (n : ℝ))
        atTop (nhds ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add hsmall
    have heq : (fun n : ℕ => (1 : ℝ) + (1 : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (n + 1 : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp [hn0]
    simpa using hadd.congr' heq
  have hlogsucc : Tendsto
      (fun n : ℕ => Real.log (n + 1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    have hmul := hlogsuccBase.mul hratio
    convert hmul using 1
    · apply funext
      intro n
      by_cases hn : n = 0
      · subst n
        simp
      · field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]
    · norm_num
  have hlowerT : Tendsto
      (fun n : ℕ => 2 *
        (Real.log (Nat.centralBinom n : ℝ) / (n : ℝ)))
      atTop (nhds (Real.log 16)) := by
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    have h := htwo.mul centralBinomial_log_div_nat_tendsto
    convert h using 1
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupperT : Tendsto
      (fun n : ℕ => 2 *
        (Real.log (n + 1 : ℝ) / (n : ℝ) + Real.log 4))
      atTop (nhds (Real.log 16)) := by
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hlog4 : Tendsto (fun _ : ℕ => Real.log 4) atTop
        (nhds (Real.log 4)) := tendsto_const_nhds
    have h := htwo.mul (hlogsucc.add hlog4)
    convert h using 1
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowerT hupperT
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcbpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos n
    have hsand := (pascalConditionTwo_exponential_sandwich n).1
    have hlog := Real.log_le_log (sq_pos_of_pos hcbpos) hsand
    rw [Real.log_pow] at hlog
    calc
      2 * (Real.log (Nat.centralBinom n : ℝ) / (n : ℝ)) =
          (2 * Real.log (Nat.centralBinom n : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.log (pascalConditionTwo (n + 1)) / (n : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2 hlog
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcondpos : 0 < pascalConditionTwo (n + 1) := by
      have hcbpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
        exact_mod_cast Nat.centralBinom_pos n
      exact lt_of_lt_of_le (sq_pos_of_pos hcbpos)
        (pascalConditionTwo_exponential_sandwich n).1
    have hbasepos : 0 < (n + 1 : ℝ) * (4 : ℝ) ^ n := by positivity
    have hsand := (pascalConditionTwo_exponential_sandwich n).2
    have hlog := Real.log_le_log hcondpos hsand
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at hlog
    calc
      Real.log (pascalConditionTwo (n + 1)) / (n : ℝ) ≤
          (2 * (Real.log (n + 1 : ℝ) +
            (n : ℝ) * Real.log 4)) / (n : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2 (by simpa using hlog)
      _ = 2 * (Real.log (n + 1 : ℝ) / (n : ℝ) + Real.log 4) := by
        field_simp [ne_of_gt hnpos]

/-- The smallest Pascal singularizing perturbation has exact exponential
rate `4^{-n}`.  The separately proved factorial-ratio Stirling theorem refines
the comparison model by its `sqrt(n*pi)` subexponential factor. -/
theorem pascalOptimalPerturbation_log_rate :
    Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (pascalOptimalSingularizingPerturbation n)) /
          (n : ℝ))
      atTop (nhds (-Real.log 4)) := by
  have hcondHalf : Tendsto
      (fun n : ℕ => (2 : ℝ)⁻¹ *
        (Real.log (pascalConditionTwo (n + 1)) / (n : ℝ)))
      atTop (nhds ((2 : ℝ)⁻¹ * Real.log 16)) :=
    tendsto_const_nhds.mul pascalConditionTwo_log_rate
  have hnorm : Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ))
      atTop (nhds (Real.log 4)) := by
    have hcongr : (fun n : ℕ => (2 : ℝ)⁻¹ *
          (Real.log (pascalConditionTwo (n + 1)) / (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ =>
          Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ)) := by
      filter_upwards with n
      have hPpos : 0 < opNorm2 (pascalMatrix (n + 1)) :=
        lt_of_lt_of_le (by
          exact_mod_cast Nat.centralBinom_pos n)
          (centralBinom_le_opNorm2_pascalMatrix n)
      rw [pascalConditionTwo_eq_opNorm2_sq, Real.log_pow]
      ring
    have h := hcondHalf.congr' hcongr
    convert h using 1
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
    ring
  have hneg : Tendsto
      (fun n : ℕ =>
        -(Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ)))
      atTop (nhds (-Real.log 4)) := hnorm.neg
  apply hneg.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hPpos : 0 < opNorm2 (pascalMatrix (n + 1)) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.centralBinom_pos n)
      (centralBinom_le_opNorm2_pascalMatrix n)
  have hopt : opNorm2 (pascalOptimalSingularizingPerturbation n) =
      (opNorm2 (pascalMatrix (n + 1)))⁻¹ := by
    calc
      opNorm2 (pascalOptimalSingularizingPerturbation n) =
          (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ :=
        (pascalOptimalPerturbation_is_operator2_minimal n).1
      _ = (opNorm2 (pascalMatrix (n + 1)))⁻¹ := by
        rw [opNorm2_pascalInverseMatrix_eq_pascalMatrix]
  rw [hopt, Real.log_inv]
  ring

end

end NumStability
