import Mathlib

namespace HighamBenchCandidate

/-- The exact log-sum-exp for an input vector of length `n`. -/
noncomputable def exactLogSumExp {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.log (∑ i : Fin n, Real.exp (x i))

/-- The result of evaluating each exponential with its own relative error. -/
noncomputable def computedExp {n : ℕ} (x : Fin n → ℝ) (expError : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + expError i)

/-- Recursive summation in the order `0, ..., n-1`. The target constrains
    the first addition's error to zero, since adding a computed value to zero
    is exact. -/
noncomputable def computedSum {n : ℕ} (x : Fin n → ℝ)
    (expError addError : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun s i => (s + computedExp x expError i) * (1 + addError i)) 0

/-- The final logarithm is evaluated with one relative rounding error. -/
noncomputable def computedLogSumExp {n : ℕ} (x : Fin n → ℝ)
    (expError addError : Fin n → ℝ) (logError : ℝ) : ℝ :=
  Real.log (computedSum x expError addError) * (1 + logError)

private theorem sumStepBounds (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (k : ℕ) (S A w δ ε : ℝ) (hS : 0 ≤ S) (hw : 0 ≤ w)
    (hδ : |δ| ≤ u) (hε : |ε| ≤ u)
    (hlo : (1 - u) ^ (k + 1) * S ≤ A)
    (hhi : A ≤ (1 + u) ^ (k + 1) * S) :
    (1 - u) ^ (k + 2) * (S + w) ≤ (A + w * (1 + δ)) * (1 + ε) ∧
    (A + w * (1 + δ)) * (1 + ε) ≤ (1 + u) ^ (k + 2) * (S + w) := by
  have ha : 0 ≤ 1 - u := by linarith
  have hb : 0 ≤ 1 + u := by linarith
  have ha1 : 1 - u ≤ 1 := by linarith
  have hb1 : 1 ≤ 1 + u := by linarith
  have hapow : (1 - u) ^ (k + 1) ≤ 1 - u := by
    calc
      _ = (1 - u) ^ k * (1 - u) := by rw [pow_succ]
      _ ≤ 1 * (1 - u) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha1) ha
      _ = 1 - u := one_mul _
  have hbpow : 1 + u ≤ (1 + u) ^ (k + 1) := by
    calc
      _ = 1 * (1 + u) := (one_mul _).symm
      _ ≤ (1 + u) ^ k * (1 + u) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hb1) hb
      _ = (1 + u) ^ (k + 1) := by rw [pow_succ]
  have hδlo : 1 - u ≤ 1 + δ := by have := (abs_le.mp hδ).1; linarith
  have hδhi : 1 + δ ≤ 1 + u := by have := (abs_le.mp hδ).2; linarith
  have hεlo : 1 - u ≤ 1 + ε := by have := (abs_le.mp hε).1; linarith
  have hεhi : 1 + ε ≤ 1 + u := by have := (abs_le.mp hε).2; linarith
  have hwlo : (1 - u) ^ (k + 1) * w ≤ w * (1 + δ) := by
    calc
      _ ≤ (1 - u) * w := mul_le_mul_of_nonneg_right hapow hw
      _ ≤ w * (1 + δ) := by nlinarith [mul_le_mul_of_nonneg_left hδlo hw]
  have hwhi : w * (1 + δ) ≤ (1 + u) ^ (k + 1) * w := by
    calc
      _ ≤ w * (1 + u) := mul_le_mul_of_nonneg_left hδhi hw
      _ ≤ (1 + u) ^ (k + 1) * w := by
        nlinarith [mul_le_mul_of_nonneg_right hbpow hw]
  have hmidlo : (1 - u) ^ (k + 1) * (S + w) ≤ A + w * (1 + δ) := by
    nlinarith [hlo, hwlo]
  have hmidhi : A + w * (1 + δ) ≤ (1 + u) ^ (k + 1) * (S + w) := by
    nlinarith [hhi, hwhi]
  have hmidnonneg : 0 ≤ A + w * (1 + δ) := by
    nlinarith [hmidlo, mul_nonneg (pow_nonneg ha (k + 1)) (add_nonneg hS hw)]
  constructor
  · calc
      (1 - u) ^ (k + 2) * (S + w) =
          ((1 - u) ^ (k + 1) * (S + w)) * (1 - u) := by
            rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring
      _ ≤ (A + w * (1 + δ)) * (1 - u) :=
        mul_le_mul_of_nonneg_right hmidlo ha
      _ ≤ (A + w * (1 + δ)) * (1 + ε) :=
        mul_le_mul_of_nonneg_left hεlo hmidnonneg
  · calc
      (A + w * (1 + δ)) * (1 + ε) ≤
          (A + w * (1 + δ)) * (1 + u) :=
            mul_le_mul_of_nonneg_left hεhi hmidnonneg
      _ ≤ ((1 + u) ^ (k + 1) * (S + w)) * (1 + u) :=
        mul_le_mul_of_nonneg_right hmidhi hb
      _ = (1 + u) ^ (k + 2) * (S + w) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring

private theorem foldBoundsAux {n : ℕ} (x : Fin n → ℝ)
    (expError addError : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (he : ∀ i, |expError i| ≤ u) (ha : ∀ i, |addError i| ≤ u)
    (l : List (Fin n)) (k : ℕ) (S A : ℝ) (hS : 0 ≤ S)
    (hlo : (1 - u) ^ (k + 1) * S ≤ A)
    (hhi : A ≤ (1 + u) ^ (k + 1) * S) :
    (1 - u) ^ (k + l.length + 1) *
        (S + (l.map (fun i => Real.exp (x i))).sum) ≤
      l.foldl (fun s i => (s + computedExp x expError i) * (1 + addError i)) A ∧
    l.foldl (fun s i => (s + computedExp x expError i) * (1 + addError i)) A ≤
      (1 + u) ^ (k + l.length + 1) *
        (S + (l.map (fun i => Real.exp (x i))).sum) := by
  induction l generalizing k S A with
  | nil => simpa using And.intro hlo hhi
  | cons i tail ih =>
      have hstep := sumStepBounds u hu hu1 k S A (Real.exp (x i))
        (expError i) (addError i) hS (le_of_lt (Real.exp_pos _)) (he i) (ha i) hlo hhi
      have hnext := ih (k + 1) (S + Real.exp (x i))
        ((A + computedExp x expError i) * (1 + addError i))
        (add_nonneg hS (le_of_lt (Real.exp_pos _)))
        (by simpa only [show k + 1 + 1 = k + 2 by omega, computedExp] using hstep.1)
        (by simpa only [show k + 1 + 1 = k + 2 by omega, computedExp] using hstep.2)
      have hidx : k + (tail.length + 1) + 1 =
          (k + 1) + tail.length + 1 := by omega
      simpa only [List.length_cons, List.map_cons, List.sum_cons, List.foldl_cons,
        computedExp, hidx, add_assoc] using hnext

private theorem logAbsDiffBound (m : ℕ) (s t u : ℝ)
    (hs : 0 < s) (hu : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hlo : (1 - u) ^ m * s ≤ t)
    (hhi : t ≤ (1 + u) ^ m * s) :
    |Real.log s - Real.log t| ≤ (m : ℝ) * (u + 2 * u ^ 2) := by
  have ha : 0 < 1 - u := by linarith
  have hb : 0 < 1 + u := by linarith
  have hpowA : 0 < (1 - u) ^ m := pow_pos ha _
  have hpowB : 0 < (1 + u) ^ m := pow_pos hb _
  have ht : 0 < t := lt_of_lt_of_le (mul_pos hpowA hs) hlo
  have hloglo := Real.log_le_log (mul_pos hpowA hs) hlo
  have hloghi := Real.log_le_log ht hhi
  rw [Real.log_mul hpowA.ne' hs.ne', Real.log_pow] at hloglo
  rw [Real.log_mul hpowB.ne' hs.ne', Real.log_pow] at hloghi
  have hlogB : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos hb
    linarith
  have hrec : -Real.log (1 - u) ≤ u / (1 - u) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
    rw [Real.log_inv] at h
    have hid : (1 - u)⁻¹ - 1 = u / (1 - u) := by
      apply (eq_div_iff ha.ne').2
      rw [sub_mul, inv_mul_cancel₀ ha.ne']
      ring
    linarith
  have hrecBound : u / (1 - u) ≤ u + 2 * u ^ 2 := by
    apply (div_le_iff₀ ha).mpr
    have hnonneg : 0 ≤ u ^ 2 * (1 - 2 * u) :=
      mul_nonneg (sq_nonneg u) (by linarith)
    nlinarith
  have hlogA : -Real.log (1 - u) ≤ u + 2 * u ^ 2 :=
    hrec.trans hrecBound
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hleft := mul_le_mul_of_nonneg_left hlogB hm
  have hright := mul_le_mul_of_nonneg_left hlogA hm
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Absolute forward-error estimate immediately preceding Theorem 3.2 of
    Blanchard, Higham and Higham (2021), for basic Algorithm 3.1. -/
theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧
      ∃ u₀ : ℝ, 0 < u₀ ∧
      ∀ (u : ℝ) (expError addError : Fin n → ℝ) (logError : ℝ),
        0 < u → u ≤ u₀ →
        (∀ i : Fin n, |expError i| ≤ u) →
        (addError ⟨0, hn⟩ = 0) →
        (∀ i : Fin n, |addError i| ≤ u) →
        |logError| ≤ u →
        |exactLogSumExp x - computedLogSumExp x expError addError logError| ≤
          u * |exactLogSumExp x| + ((n : ℝ) + 1) * u + C * u ^ 2 := by
  intro n hn x
  refine ⟨4 * ((n : ℝ) + 1), by positivity, 1 / 2, by norm_num, ?_⟩
  intro u expError addError logError hu huHalf he _ ha hlogError
  let s : ℝ := ∑ i : Fin n, Real.exp (x i)
  let t : ℝ := computedSum x expError addError
  have hs : 0 < s := by
    dsimp [s]
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsumList : ((List.finRange n).map (fun i => Real.exp (x i))).sum = s := by
    dsimp [s]
    simpa only [List.toFinset_finRange] using
      (List.sum_toFinset (fun i : Fin n => Real.exp (x i))
        (List.nodup_finRange n)).symm
  have hraw := foldBoundsAux x expError addError u (le_of_lt hu)
    (by linarith : u < 1) he ha (List.finRange n) 0 0 0 (le_refl 0)
    (by simp) (by simp)
  have hbounds : (1 - u) ^ (n + 1) * s ≤ t ∧
      t ≤ (1 + u) ^ (n + 1) * s := by
    simpa only [List.length_finRange, zero_add, hsumList, t, computedSum] using hraw
  have hdiff : |Real.log s - Real.log t| ≤
      ((n : ℝ) + 1) * (u + 2 * u ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      logAbsDiffBound (n + 1) s t u hs (le_of_lt hu) huHalf hbounds.1 hbounds.2
  have hη : |logError| ≤ u := hlogError
  have hlogt : |Real.log t| ≤ |Real.log s| + |Real.log s - Real.log t| := by
    have h := abs_sub_le (Real.log t) (Real.log s) 0
    simpa only [sub_zero, abs_sub_comm, add_comm] using h
  have herror : |Real.log s - Real.log t * (1 + logError)| ≤
      u * |Real.log s| + (1 + u) * |Real.log s - Real.log t| := by
    have htri : |Real.log s - Real.log t * (1 + logError)| ≤
        |Real.log s - Real.log t| + |Real.log t * logError| := by
      calc
        _ = |(Real.log s - Real.log t) + -(Real.log t * logError)| := by ring
        _ ≤ |Real.log s - Real.log t| + |-(Real.log t * logError)| :=
          abs_add_le _ _
        _ = |Real.log s - Real.log t| + |Real.log t * logError| := by rw [abs_neg]
    rw [abs_mul] at htri
    have hprod := mul_le_mul_of_nonneg_left hη (abs_nonneg (Real.log t))
    have hlogprod := mul_le_mul_of_nonneg_right hlogt (le_of_lt hu)
    nlinarith
  have hrem : (1 + u) * (((n : ℝ) + 1) * (u + 2 * u ^ 2)) ≤
      ((n : ℝ) + 1) * u + (4 * ((n : ℝ) + 1)) * u ^ 2 := by
    have hm : 0 ≤ (n : ℝ) + 1 := by positivity
    have hpoly : (1 + u) * (u + 2 * u ^ 2) ≤ u + 4 * u ^ 2 := by
      have hnonneg : 0 ≤ u ^ 2 * (1 - 2 * u) :=
        mul_nonneg (sq_nonneg u) (by linarith)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpoly hm]
  have hscale := mul_le_mul_of_nonneg_left hdiff (by linarith : 0 ≤ 1 + u)
  dsimp [exactLogSumExp, computedLogSumExp, s, t] at *
  nlinarith [herror, hscale, hrem]

end HighamBenchCandidate
