import NumStability.Algorithms.HighamChapter10

namespace NumStability

open scoped BigOperators Topology

/-!
# Higham Lemma 10.13: Kahan-family sharpness

This module supplies the constructive limit calculation following (10.20).
The diagonal scaling in `kahanR` cancels from the leading triangular solve;
the solution columns are the explicit geometric vector below.
-/

/-- The exact columns of `R₁₁⁻¹ R₁₂` for the Kahan factor (10.20). -/
noncomputable def higham10KahanW (r m : ℕ) (c : ℝ) :
    Fin r → Fin m → ℝ :=
  fun i _ => -c * (1 + c) ^ (r - 1 - i.val)

/-- Embed a leading-block index into all columns of the rectangular factor. -/
def higham10KahanLeadCol {r m : ℕ} (i : Fin r) : Fin (r + m) :=
  Fin.castLE (Nat.le_add_right r m) i

theorem kahanR_above {r n : ℕ} (c s : ℝ)
    {i : Fin r} {j : Fin n} (hij : i.val < j.val) :
    kahanR r n c s i j = -c * s ^ i.val := by
  unfold kahanR
  rw [if_neg (by omega), if_pos hij]

theorem kahanR_below {r n : ℕ} (c s : ℝ)
    {i : Fin r} {j : Fin n} (hji : j.val < i.val) :
    kahanR r n c s i j = 0 := by
  unfold kahanR
  rw [if_neg (by omega), if_neg (by omega)]

@[simp] theorem higham10KahanW_last (r m : ℕ) (c : ℝ)
    (j : Fin m) :
    higham10KahanW (r + 1) m c (Fin.last r) j = -c := by
  simp [higham10KahanW]

theorem higham10KahanW_succ_castSucc (r m : ℕ) (c : ℝ)
    (i : Fin r) (j : Fin m) :
    higham10KahanW (r + 1) m c i.castSucc j =
      (1 + c) * higham10KahanW r m c i j := by
  unfold higham10KahanW
  change -c * (1 + c) ^ (r + 1 - 1 - i.val) =
    (1 + c) * (-c * (1 + c) ^ (r - 1 - i.val))
  have he : r + 1 - 1 - i.val = (r - 1 - i.val) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem kahanR_succ_castSucc_castSucc (r m : ℕ) (c s : ℝ)
    (i k : Fin r) :
    kahanR (r + 1) (r + 1 + m) c s i.castSucc
        (higham10KahanLeadCol (r := r + 1) (m := m) k.castSucc) =
      kahanR r (r + m) c s i
        (higham10KahanLeadCol (r := r) (m := m) k) := by
  simp [kahanR, higham10KahanLeadCol]

/-- Every explicit Kahan column solves the leading triangular system against
each border column.  No inverse or target residual is assumed. -/
theorem higham10KahanW_solve (r m : ℕ) (c s : ℝ) :
    ∀ (i : Fin r) (j : Fin m),
      (∑ k : Fin r,
        kahanR r (r + m) c s i
          (higham10KahanLeadCol (r := r) (m := m) k) *
            higham10KahanW r m c k j) =
      kahanR r (r + m) c s i
        ⟨r + j.val, by omega⟩ := by
  induction r with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ r ih =>
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.sum_univ_castSucc]
        have hzero :
            (∑ k : Fin r,
              kahanR (r + 1) (r + 1 + m) c s (Fin.last r)
                (higham10KahanLeadCol (r := r + 1) (m := m) k.castSucc) *
                higham10KahanW (r + 1) m c k.castSucc j) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hk :
              (higham10KahanLeadCol (r := r + 1) (m := m) k.castSucc).val <
                (Fin.last r).val := by
            simp [higham10KahanLeadCol]
          rw [kahanR_below c s hk]
          simp
        rw [hzero, zero_add]
        have hgt : r < r + 1 + j.val := by omega
        have hdiag :
            kahanR (r + 1) (r + 1 + m) c s (Fin.last r)
                (higham10KahanLeadCol (r := r + 1) (m := m) (Fin.last r)) =
              s ^ r := by
          simp [kahanR, higham10KahanLeadCol]
        have hborder :
            kahanR (r + 1) (r + 1 + m) c s (Fin.last r)
                ⟨r + 1 + j.val, by omega⟩ = -c * s ^ r :=
          kahanR_above c s hgt
        rw [hdiag, higham10KahanW_last, hborder]
        ring
      · rw [Fin.sum_univ_castSucc]
        have hfirst :
            (∑ k : Fin r,
              kahanR (r + 1) (r + 1 + m) c s i.castSucc
                (higham10KahanLeadCol (r := r + 1) (m := m) k.castSucc) *
                higham10KahanW (r + 1) m c k.castSucc j) =
              (1 + c) *
                (∑ k : Fin r,
                  kahanR r (r + m) c s i
                    (higham10KahanLeadCol (r := r) (m := m) k) *
                    higham10KahanW r m c k j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [kahanR_succ_castSucc_castSucc,
            higham10KahanW_succ_castSucc]
          ring
        rw [hfirst, ih i j]
        have hborderOld :
            kahanR r (r + m) c s i ⟨r + j.val, by omega⟩ =
              -c * s ^ i.val := by
          have hgt : i.val < r + j.val := by omega
          exact kahanR_above c s hgt
        have hlastR :
            kahanR (r + 1) (r + 1 + m) c s i.castSucc
                (higham10KahanLeadCol (r := r + 1) (m := m) (Fin.last r)) =
              -c * s ^ i.val := by
          have hgt : i.val < r := i.isLt
          apply kahanR_above c s
          simpa [higham10KahanLeadCol] using hgt
        have hborderNew :
            kahanR (r + 1) (r + 1 + m) c s i.castSucc
                ⟨r + 1 + j.val, by omega⟩ = -c * s ^ i.val := by
          have hgt : i.val < r + 1 + j.val := by omega
          exact kahanR_above c s hgt
        rw [hborderOld, hlastR, higham10KahanW_last, hborderNew]
        ring

/-- Squared Frobenius norm of the explicit Kahan solve. -/
noncomputable def higham10KahanWFrobSq (r m : ℕ) (c : ℝ) : ℝ :=
  ∑ j : Fin m, ∑ i : Fin r, higham10KahanW r m c i j ^ 2

theorem higham10KahanWFrobSq_continuous (r m : ℕ) :
    Continuous (higham10KahanWFrobSq r m) := by
  unfold higham10KahanWFrobSq higham10KahanW
  fun_prop

theorem higham10KahanWFrobSq_one (r m : ℕ) :
    higham10KahanWFrobSq r m 1 =
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hinner : ∀ j : Fin m,
      (∑ i : Fin r, higham10KahanW r m 1 i j ^ 2) =
        (((4 : ℝ) ^ r - 1) / 3) := by
    intro j
    unfold higham10KahanW
    norm_num only [neg_mul, one_mul, one_add_one_eq_two]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (-(2 : ℝ) ^ (r - 1 - i)) ^ 2) r]
    have hreflect := Finset.sum_range_reflect (fun q : ℕ => (4 : ℝ) ^ q) r
    have hrewrite :
        (∑ i ∈ Finset.range r,
          (-(2 : ℝ) ^ (r - 1 - i)) ^ 2) =
            ∑ i ∈ Finset.range r, (4 : ℝ) ^ (r - 1 - i) := by
      apply Finset.sum_congr rfl
      intro i _
      norm_num [pow_two, ← mul_pow]
    rw [hrewrite, hreflect]
    have hgeom := geom_sum_mul (4 : ℝ) r
    norm_num at hgeom
    calc
      (∑ i ∈ Finset.range r, (4 : ℝ) ^ i) =
          ((∑ i ∈ Finset.range r, (4 : ℝ) ^ i) * 3) / 3 := by ring
      _ = ((4 : ℝ) ^ r - 1) / 3 :=
        congrArg (fun x : ℝ => x / 3) hgeom
  unfold higham10KahanWFrobSq
  simp_rw [hinner]
  simp

/-- The squared Frobenius norm reaches the printed Lemma 10.13 constant in
the Kahan limit `c → 1`. -/
theorem higham10_13_kahan_frobenius_sq_tendsto (r m : ℕ) :
    Filter.Tendsto (higham10KahanWFrobSq r m) (𝓝 1)
      (𝓝 ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3))) := by
  have h : ContinuousAt (higham10KahanWFrobSq r m) 1 :=
    (higham10KahanWFrobSq_continuous r m).continuousAt
  change Filter.Tendsto (higham10KahanWFrobSq r m) (𝓝 1)
    (𝓝 (higham10KahanWFrobSq r m 1)) at h
  simpa only [higham10KahanWFrobSq_one] using h

/-- Source parametrization `c = cos θ`: as `θ → 0`, the same squared norm
tends to the printed sharp constant. -/
theorem higham10_13_kahan_theta_frobenius_sq_tendsto (r m : ℕ) :
    Filter.Tendsto
      (fun θ : ℝ => higham10KahanWFrobSq r m (Real.cos θ))
      (𝓝 0) (𝓝 ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3))) := by
  have hcos : Filter.Tendsto Real.cos (𝓝 0) (𝓝 1) := by
    have h : ContinuousAt Real.cos 0 := Real.continuous_cos.continuousAt
    change Filter.Tendsto Real.cos (𝓝 0) (𝓝 (Real.cos 0)) at h
    simpa only [Real.cos_zero] using h
  exact (higham10_13_kahan_frobenius_sq_tendsto r m).comp hcos

/-- Norm (rather than squared-norm) form printed in Lemma 10.13. -/
theorem higham10_13_kahan_theta_frobenius_tendsto (r m : ℕ) :
    Filter.Tendsto
      (fun θ : ℝ => Real.sqrt
        (higham10KahanWFrobSq r m (Real.cos θ)))
      (𝓝 0)
      (𝓝 (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) := by
  have hsqrt : Filter.Tendsto Real.sqrt
      (𝓝 ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))
      (𝓝 (Real.sqrt ((m : ℝ) * (((4 : ℝ) ^ r - 1) / 3)))) :=
    Real.continuous_sqrt.continuousAt
  exact hsqrt.comp (higham10_13_kahan_theta_frobenius_sq_tendsto r m)

end NumStability
