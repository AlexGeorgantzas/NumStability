-- Algorithms/QR/HouseholderOneStep.lean
--
-- Bridge from concrete Householder construction to concrete Householder
-- application for one reflector.

import NumStability.Algorithms.QR.HouseholderReflector
import NumStability.Algorithms.QR.HouseholderApply

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Exact identity behind the Householder zeroing step:
    for `v = x + s e₀`, `vᵀx = s v₀`. -/
theorem householderVector_dot_original_eq_scale_mul_zero {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) :
    (∑ i : Fin n, householderVector hn0 x i * x i) =
      householderScale hn0 x * householderVector hn0 x ⟨0, hn0⟩ := by
  let first : Fin n := ⟨0, hn0⟩
  let tailSum : ℝ :=
    ∑ i ∈ (Finset.univ : Finset (Fin n)).erase first, x i * x i
  have hmem : first ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ first
  have hsum_vx :
      (∑ i : Fin n, householderVector hn0 x i * x i) =
        householderVector hn0 x first * x first + tailSum := by
    have hsplit :=
      Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun i => householderVector hn0 x i * x i) hmem
    calc
      (∑ i : Fin n, householderVector hn0 x i * x i)
          =
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase first,
              householderVector hn0 x i * x i) +
              householderVector hn0 x first * x first := by
                rw [hsplit]
      _ =
            householderVector hn0 x first * x first + tailSum := by
                rw [add_comm]
                congr 1
                unfold tailSum
                apply Finset.sum_congr rfl
                intro i hi
                have hne : i ≠ first := (Finset.mem_erase.mp hi).1
                rw [householderVector_tail hn0 x i hne]
  have hsum_x : (∑ i : Fin n, x i * x i) =
      x first * x first + tailSum := by
    have hsplit :=
      Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun i => x i * x i) hmem
    calc
      (∑ i : Fin n, x i * x i)
          =
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase first,
              x i * x i) + x first * x first := by
                rw [hsplit]
      _ = x first * x first + tailSum := by
            rw [add_comm]
  have hscale_sq := householderScale_mul_self hn0 x
  have hv0 : householderVector hn0 x first = x first + householderScale hn0 x := by
    simp [first, householderVector]
  rw [hsum_vx, hv0]
  rw [hsum_x] at hscale_sq
  nlinarith

/-- Exact constructed Householder reflector maps its source vector's first
    component to `-s`, where `s = sign(x₀)||x||₂`. -/
theorem householder_constructed_matMulVec_first {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0) :
    matMulVec n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      x ⟨0, hn0⟩ =
        -householderScale hn0 x := by
  let first : Fin n := ⟨0, hn0⟩
  let v : Fin n → ℝ := householderVector hn0 x
  let beta : ℝ := householderBetaFromScale hn0 x
  have hbeta_nonneg : 0 ≤ beta := by
    exact le_of_lt (by simpa [beta] using householderBetaFromScale_pos_of_ne_zero hn0 x hx)
  have hden : householderScale hn0 x * v first ≠ 0 := by
    exact mul_ne_zero
      (householderScale_ne_zero_of_ne_zero hn0 x hx)
      (by simpa [v, first] using householderVector_zero_ne_zero_of_ne_zero hn0 x hx)
  have hs_ne : householderScale hn0 x ≠ 0 :=
    householderScale_ne_zero_of_ne_zero hn0 x hx
  have hv0_ne : householderVector hn0 x ⟨0, hn0⟩ ≠ 0 :=
    householderVector_zero_ne_zero_of_ne_zero hn0 x hx
  have hdot :
      (∑ j : Fin n, v j * x j) =
        householderScale hn0 x * v first := by
    simpa [v, first] using householderVector_dot_original_eq_scale_mul_zero hn0 x
  calc
    matMulVec n
        (householder n
          (householderNormalizedVector n
            (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
        x first
        =
          matMulVec n (householder n v beta) x first := by
            rw [householder_normalizedVector_eq n v beta hbeta_nonneg]
    _ = x first - beta * v first * (∑ j : Fin n, v j * x j) := by
          rw [householder_matMulVec_eq]
    _ = x first - beta * v first * (householderScale hn0 x * v first) := by
          rw [hdot]
    _ = -householderScale hn0 x := by
          have hv0 : v first = x first + householderScale hn0 x := by
            simp [v, first]
          have hv0_direct :
              householderVector hn0 x ⟨0, hn0⟩ =
                x first + householderScale hn0 x := by
            simp [first]
          unfold beta householderBetaFromScale
          field_simp [hs_ne, hv0_ne]
          rw [hv0, hv0_direct]
          ring_nf

/-- Exact constructed Householder reflector zeros all tail components of the
    vector it is constructed from.  This is the exact triangularization fact
    needed before a full Householder QR loop can be proved. -/
theorem householder_constructed_matMulVec_tail_zero {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (i : Fin n) (hi : i ≠ ⟨0, hn0⟩) :
    matMulVec n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      x i = 0 := by
  let first : Fin n := ⟨0, hn0⟩
  let v : Fin n → ℝ := householderVector hn0 x
  let beta : ℝ := householderBetaFromScale hn0 x
  have hbeta_nonneg : 0 ≤ beta := by
    exact le_of_lt (by simpa [beta] using householderBetaFromScale_pos_of_ne_zero hn0 x hx)
  have hden : householderScale hn0 x * v first ≠ 0 := by
    exact mul_ne_zero
      (householderScale_ne_zero_of_ne_zero hn0 x hx)
      (by simpa [v, first] using householderVector_zero_ne_zero_of_ne_zero hn0 x hx)
  have hs_ne : householderScale hn0 x ≠ 0 :=
    householderScale_ne_zero_of_ne_zero hn0 x hx
  have hv0_ne : householderVector hn0 x ⟨0, hn0⟩ ≠ 0 :=
    householderVector_zero_ne_zero_of_ne_zero hn0 x hx
  have hdot :
      (∑ j : Fin n, v j * x j) =
        householderScale hn0 x * v first := by
    simpa [v, first] using householderVector_dot_original_eq_scale_mul_zero hn0 x
  have htail : v i = x i := by
    simpa [v, first] using householderVector_tail hn0 x i hi
  calc
    matMulVec n
        (householder n
          (householderNormalizedVector n
            (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
        x i
        =
          matMulVec n (householder n v beta) x i := by
            rw [householder_normalizedVector_eq n v beta hbeta_nonneg]
    _ = x i - beta * v i * (∑ j : Fin n, v j * x j) := by
          rw [householder_matMulVec_eq]
    _ = x i - beta * x i * (householderScale hn0 x * v first) := by
          rw [htail, hdot]
    _ = 0 := by
          unfold beta householderBetaFromScale
          field_simp [hs_ne, hv0_ne]
          ring

/-- Concrete construction plus concrete application satisfies the normalized
    one-reflector application contract.

    This combines the implementation-backed construction theorem
    `fl_householderVectorError` with the implementation-backed application
    theorem `fl_householderApply_normalized_appError`.  The exact reflector is
    written in Higham's normalized form `I - v vᵀ`, where `v` is the normalized
    exact Householder vector produced from the input `x`.

    The raw bound is
    `sqrt(n*u^2) + 2*gamma(11n+23)`, obtained by instantiating the application
    theorem with the construction perturbation index `a = 5n+10`. -/
theorem fl_householderConstructApply_appError (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x b : Fin n → ℝ)
    (hx : x ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderAppError n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      b
      (fl_householderApply fp n
        (fl_householderNormalizedVector fp hn0 x) 1 b)
      (Real.sqrt ((n : ℝ) * fp.u ^ 2) +
        2 * gamma fp (11 * n + 23)) := by
  let a : ℕ := 5 * n + 10
  let v : Fin n → ℝ :=
    householderNormalizedVector n
      (householderVector hn0 x) (householderBetaFromScale hn0 x)
  let v_hat : Fin n → ℝ := fl_householderNormalizedVector fp hn0 x
  have hvalid_vec : gammaValid fp (8 * n + 16) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalid_eps : gammaValid fp a :=
    gammaValid_mono fp (by omega) hvalid
  have hvec : HouseholderVectorError n v v_hat (gamma fp a) := by
    simpa [v, v_hat, a] using
      fl_householderVectorError fp hn0 x hx hvalid_vec
  have heps_nonneg : 0 ≤ gamma fp a := gamma_nonneg fp hvalid_eps
  have hvalid_apply : gammaValid fp (2 * a + n + 3) := by
    exact gammaValid_mono fp (by unfold a; omega) hvalid
  have happ :=
    fl_householderApply_normalized_appError fp a n v v_hat (gamma fp a) b
      hvec heps_nonneg le_rfl hvalid_apply
  have hidx : 2 * a + n + 3 = 11 * n + 23 := by
    unfold a
    omega
  rw [hidx] at happ
  simpa [v, v_hat] using happ

end NumStability
