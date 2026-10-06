import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- The exact positive sum in the summation part of Algorithm 3.1. -/
noncomputable def exactExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (x i)

/-- The exact sum of the values returned by the exponential evaluations. -/
noncomputable def exactComputedExpSum {n : ℕ} (wHat : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, wHat i

/-- The computed sum uses Algorithm 3.1's left-to-right additions from zero. -/
noncomputable def roundedExpSum (fp : FPModel) {n : ℕ}
    (wHat : Fin n → ℝ) : ℝ :=
  fl_recursiveSum fp n wHat

private lemma power_radius_nonneg (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ (1 + u) ^ n - 1 := by
  have h : (1 : ℝ) ≤ 1 + u := by linarith
  have hpow : (1 : ℝ) ≤ (1 + u) ^ n := one_le_pow₀ h
  nlinarith

private lemma local_add_error (fp : FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hround⟩ := fp.model_add a b
  rw [hround]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma fold_from_nonneg_error (fp : FPModel) (n : ℕ)
    (a : ℝ) (v : Fin n → ℝ) (ha : 0 ≤ a)
    (hv : ∀ i, 0 ≤ v i) :
    |Fin.foldl n (fun acc i => fp.fl_add acc (v i)) a -
        (a + ∑ i : Fin n, v i)| ≤
      ((1 + fp.u) ^ n - 1) * (a + ∑ i : Fin n, v i) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      let vp : Fin n → ℝ := fun i => v i.castSucc
      let z : ℝ := v (Fin.last n)
      let p : ℝ := Fin.foldl n (fun acc i => fp.fl_add acc (vp i)) a
      let t : ℝ := a + ∑ i : Fin n, vp i
      have hvp : ∀ i, 0 ≤ vp i := fun i => hv i.castSucc
      have hz : 0 ≤ z := hv (Fin.last n)
      have ht : 0 ≤ t := add_nonneg ha (Finset.sum_nonneg (fun i _ => hvp i))
      have hprev : |p - t| ≤ ((1 + fp.u) ^ n - 1) * t := by
        simpa [p, t, vp] using ih a vp ha hvp
      have hfold : Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) a =
          fp.fl_add p z := by
        simpa [p, vp, z] using
          (Fin.foldl_succ_last (fun acc i => fp.fl_add acc (v i)) a)
      have hsum : a + ∑ i : Fin (n + 1), v i = t + z := by
        simp [t, vp, z, Fin.sum_univ_castSucc]
        ring
      have htr : 0 ≤ t + z := add_nonneg ht hz
      have harg : |p + z| ≤ |p - t| + (t + z) := by
        calc
          |p + z| = |(p - t) + (t + z)| := by congr 1; ring
          _ ≤ |p - t| + |t + z| := abs_add_le _ _
          _ = |p - t| + (t + z) := by rw [abs_of_nonneg htr]
      have hstep : |fp.fl_add p z - (t + z)| ≤
          (1 + fp.u) * |p - t| + fp.u * (t + z) := by
        calc
          |fp.fl_add p z - (t + z)| =
              |(fp.fl_add p z - (p + z)) + (p - t)| := by congr 1; ring
          _ ≤ |fp.fl_add p z - (p + z)| + |p - t| := abs_add_le _ _
          _ ≤ fp.u * |p + z| + |p - t| := by
            gcongr
            exact local_add_error fp p z
          _ ≤ fp.u * (|p - t| + (t + z)) + |p - t| := by
            exact add_le_add (mul_le_mul_of_nonneg_left harg fp.u_nonneg) le_rfl
          _ = (1 + fp.u) * |p - t| + fp.u * (t + z) := by ring
      have hrad : 0 ≤ (1 + fp.u) ^ n - 1 :=
        power_radius_nonneg fp.u fp.u_nonneg n
      have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      rw [hfold, hsum]
      calc
        |fp.fl_add p z - (t + z)| ≤
            (1 + fp.u) * |p - t| + fp.u * (t + z) := hstep
        _ ≤ (1 + fp.u) * (((1 + fp.u) ^ n - 1) * t) +
              fp.u * (t + z) := by gcongr
        _ ≤ ((1 + fp.u) ^ (n + 1) - 1) * (t + z) := by
          rw [pow_succ]
          nlinarith [mul_nonneg hrad hz]

private lemma rounded_exp_sum_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (wHat : Fin n → ℝ) (hw : ∀ i, 0 ≤ wHat i) :
    |roundedExpSum fp wHat - exactComputedExpSum wHat| ≤
      ((1 + fp.u) ^ (n - 1) - 1) * exactComputedExpSum wHat := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have h := fold_from_nonneg_error fp m (wHat 0)
    (fun i : Fin m => wHat i.succ) (hw 0) (fun i => hw i.succ)
  simpa [roundedExpSum, exactComputedExpSum, fl_recursiveSum,
    Fin.foldl_succ, fp.fl_add_zero, Fin.sum_univ_succ] using h

private lemma exp_stage (fp : FPModel) (hu : fp.u < 1) (n : ℕ)
    (x wHat : Fin n → ℝ)
    (hExp : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ wHat i = Real.exp (x i) * (1 + δ)) :
    (∀ i, 0 ≤ wHat i) ∧
    |exactComputedExpSum wHat - exactExpSum x| ≤ fp.u * exactExpSum x ∧
    exactComputedExpSum wHat ≤ (1 + fp.u) * exactExpSum x := by
  have hlocal (i : Fin n) :
      0 ≤ wHat i ∧
      |wHat i - Real.exp (x i)| ≤ fp.u * Real.exp (x i) ∧
      wHat i ≤ (1 + fp.u) * Real.exp (x i) := by
    obtain ⟨δ, hδ, hw⟩ := hExp i
    have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
    have hδhi : δ ≤ fp.u := (abs_le.mp hδ).2
    have hfactor : 0 ≤ 1 + δ := by linarith
    have hexp : 0 ≤ Real.exp (x i) := (Real.exp_pos _).le
    rw [hw]
    refine ⟨mul_nonneg hexp hfactor, ?_, ?_⟩
    · have heq : Real.exp (x i) * (1 + δ) - Real.exp (x i) =
          Real.exp (x i) * δ := by ring
      rw [heq, abs_mul, abs_of_nonneg hexp]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ hexp
    · nlinarith [mul_nonneg hexp (sub_nonneg.mpr hδhi)]
  refine ⟨fun i => (hlocal i).1, ?_, ?_⟩
  · have hsum : exactComputedExpSum wHat - exactExpSum x =
        ∑ i : Fin n, (wHat i - Real.exp (x i)) := by
      simp [exactComputedExpSum, exactExpSum, Finset.sum_sub_distrib]
    rw [hsum]
    calc
      |∑ i : Fin n, (wHat i - Real.exp (x i))| ≤
          ∑ i : Fin n, |wHat i - Real.exp (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, fp.u * Real.exp (x i) := by
        exact Finset.sum_le_sum (fun i _ => (hlocal i).2.1)
      _ = fp.u * exactExpSum x := by
        simp [exactExpSum, Finset.mul_sum]
  · change (∑ i : Fin n, wHat i) ≤
      (1 + fp.u) * (∑ i : Fin n, Real.exp (x i))
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hlocal i).2.2)

private lemma quadratic_coefficient_nonneg (n : ℕ) :
    0 ≤ (2 : ℝ) ^ n - (n : ℝ) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hcoeff : (2 : ℝ) ^ (n + 1) - ((n + 1 : ℕ) : ℝ) - 1 =
          2 * ((2 : ℝ) ^ n - (n : ℝ) - 1) + (n : ℝ) := by
        push_cast
        ring
      rw [hcoeff]
      exact add_nonneg (mul_nonneg (by norm_num) ih) (Nat.cast_nonneg n)

private lemma power_quadratic_bound (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (n : ℕ) :
    (1 + u) ^ n ≤
      1 + (n : ℝ) * u + ((2 : ℝ) ^ n - (n : ℝ) - 1) * u ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let C : ℝ := (2 : ℝ) ^ n - (n : ℝ) - 1
      have hC : 0 ≤ C := quadratic_coefficient_nonneg n
      have hU : 0 ≤ 1 + u := by linarith
      have hcube : 0 ≤ C * (u ^ 2 - u ^ 3) := by
        apply mul_nonneg hC
        nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
      have hcoeff : (2 : ℝ) ^ (n + 1) - ((n + 1 : ℕ) : ℝ) - 1 =
          2 * C + (n : ℝ) := by
        dsimp [C]
        push_cast
        ring
      calc
        (1 + u) ^ (n + 1) = (1 + u) ^ n * (1 + u) := pow_succ _ _
        _ ≤ (1 + (n : ℝ) * u + C * u ^ 2) * (1 + u) := by
          exact mul_le_mul_of_nonneg_right (by simpa [C] using ih) hU
        _ ≤ 1 + ((n + 1 : ℕ) : ℝ) * u +
            ((2 : ℝ) ^ (n + 1) - ((n + 1 : ℕ) : ℝ) - 1) * u ^ 2 := by
          rw [hcoeff]
          push_cast
          nlinarith [hcube]

/-- Equation (3.3) for the positive exponential sum in basic Algorithm 3.1.
The explicit quadratic coefficient is uniform over all permitted local errors
for fixed `n` and `x`. -/
theorem target
    (fp : FPModel) (hu : fp.u < 1)
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (wHat : Fin n → ℝ)
    (hExp : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ wHat i = Real.exp (x i) * (1 + δ)) :
    let s := exactExpSum x
    let sTilde := exactComputedExpSum wHat
    let sHat := roundedExpSum fp wHat
    ∃ Δs : ℝ,
      sHat = s + Δs ∧
      |sTilde - s| ≤ fp.u * s ∧
      |Δs| ≤
        (((n : ℝ) + 1) * fp.u +
          ((2 : ℝ) ^ n - (n : ℝ) - 1) * fp.u ^ 2) * s := by
  change ∃ Δs : ℝ,
    roundedExpSum fp wHat = exactExpSum x + Δs ∧
    |exactComputedExpSum wHat - exactExpSum x| ≤ fp.u * exactExpSum x ∧
    |Δs| ≤
      (((n : ℝ) + 1) * fp.u +
        ((2 : ℝ) ^ n - (n : ℝ) - 1) * fp.u ^ 2) * exactExpSum x
  obtain ⟨hw, hExpErr, hSumLe⟩ := exp_stage fp hu n x wHat hExp
  have hSumErr := rounded_exp_sum_error fp n hn wHat hw
  have hs0 : 0 ≤ exactExpSum x := by
    unfold exactExpSum
    exact Finset.sum_nonneg (fun i _ => (Real.exp_pos (x i)).le)
  have hRad : 0 ≤ (1 + fp.u) ^ (n - 1) - 1 :=
    power_radius_nonneg fp.u fp.u_nonneg (n - 1)
  have hPow : (1 + fp.u) ^ n = (1 + fp.u) ^ (n - 1) * (1 + fp.u) := by
    rw [← pow_succ]
    congr 1
    omega
  have hCombined :
      |roundedExpSum fp wHat - exactExpSum x| ≤
        ((1 + fp.u) ^ n - 1) * exactExpSum x := by
    calc
      |roundedExpSum fp wHat - exactExpSum x| ≤
          |roundedExpSum fp wHat - exactComputedExpSum wHat| +
            |exactComputedExpSum wHat - exactExpSum x| := by
              have heq : roundedExpSum fp wHat - exactExpSum x =
                  (roundedExpSum fp wHat - exactComputedExpSum wHat) +
                    (exactComputedExpSum wHat - exactExpSum x) := by ring
              rw [heq]
              exact abs_add_le _ _
      _ ≤ ((1 + fp.u) ^ (n - 1) - 1) * exactComputedExpSum wHat +
            fp.u * exactExpSum x := add_le_add hSumErr hExpErr
      _ ≤ ((1 + fp.u) ^ (n - 1) - 1) *
            ((1 + fp.u) * exactExpSum x) + fp.u * exactExpSum x := by
              exact add_le_add (mul_le_mul_of_nonneg_left hSumLe hRad) le_rfl
      _ = ((1 + fp.u) ^ n - 1) * exactExpSum x := by
        rw [hPow]
        ring
  have hQuad := power_quadratic_bound fp.u fp.u_nonneg (le_of_lt hu) n
  have hFinalRad :
      (1 + fp.u) ^ n - 1 ≤
        ((n : ℝ) + 1) * fp.u +
          ((2 : ℝ) ^ n - (n : ℝ) - 1) * fp.u ^ 2 := by
    nlinarith [hQuad, fp.u_nonneg]
  refine ⟨roundedExpSum fp wHat - exactExpSum x, by ring, hExpErr, ?_⟩
  exact hCombined.trans (mul_le_mul_of_nonneg_right hFinalRad hs0)

end HighamBenchCandidate
