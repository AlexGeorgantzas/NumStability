import NumStability.Algorithms.LeastSquares.Higham20Refinement

namespace NumStability

/-!
# Higham Theorem 20.4: total-perturbation witness normalization

The printed matrix bounds use a nonnegative Frobenius-unit witness.  The
lemmas in this file normalize an arbitrary nonnegative finite witness, with a
one-hot fallback for the zero matrix.  This is the algebraic normalization
step needed after the common QR-panel perturbation and the two transported
triangular-solve perturbations have been combined.
-/

/-- Normalize a nonnegative square witness to Frobenius norm one.  The
one-hot branch makes the definition total when the supplied witness is zero. -/
noncomputable def higham20Theorem20_4NormalizedWitness {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  if frobNorm W = 0 then
    lsTheorem20_4OneHotMajorant row0 col0
  else
    fun i j => W i j / frobNorm W

theorem higham20Theorem20_4NormalizedWitness_nonneg {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ)
    (hW : ∀ i j, 0 ≤ W i j) :
    ∀ i j, 0 ≤ higham20Theorem20_4NormalizedWitness row0 col0 W i j := by
  classical
  intro i j
  by_cases hzero : frobNorm W = 0
  · simp [higham20Theorem20_4NormalizedWitness, hzero,
      lsTheorem20_4OneHotMajorant_nonneg row0 col0 i j]
  · simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    exact div_nonneg (hW i j) (frobNorm_nonneg W)

theorem higham20Theorem20_4NormalizedWitness_frobNorm {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) :
    frobNorm (higham20Theorem20_4NormalizedWitness row0 col0 W) = 1 := by
  classical
  by_cases hzero : frobNorm W = 0
  · simp [higham20Theorem20_4NormalizedWitness, hzero,
      lsTheorem20_4OneHotMajorant_frobNorm row0 col0]
  · have hpos : 0 < frobNorm W :=
      lt_of_le_of_ne (frobNorm_nonneg W) (Ne.symm hzero)
    simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    rw [← frobNormRect_eq_frobNormFn]
    have hfun : (fun i j => W i j / frobNorm W) =
        fun i j => (frobNorm W)⁻¹ * W i j := by
      funext i j
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun, frobNormRect_smul, frobNormRect_eq_frobNormFn,
      abs_of_pos (inv_pos.mpr hpos)]
    exact inv_mul_cancel₀ hzero

/-- The unnormalized witness is exactly its Frobenius norm times the normalized
witness, including the zero-witness fallback branch. -/
theorem higham20Theorem20_4_witness_eq_frobNorm_mul_normalized {m : ℕ}
    (row0 col0 : Fin m) (W : Fin m → Fin m → ℝ) (i j : Fin m) :
    W i j = frobNorm W *
      higham20Theorem20_4NormalizedWitness row0 col0 W i j := by
  classical
  by_cases hzero : frobNorm W = 0
  · have hWij : W i j = 0 := (frobNorm_eq_zero_iff W).mp hzero i j
    simp [higham20Theorem20_4NormalizedWitness, hzero, hWij]
  · simp only [higham20Theorem20_4NormalizedWitness, hzero, if_false]
    field_simp

theorem higham20Theorem20_4_le_normalized_of_left_domination
    {m n : ℕ} (row0 col0 : Fin m)
    (A D : Fin m → Fin n → ℝ) (W : Fin m → Fin m → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hWnorm : frobNorm W ≤ C)
    (hdom : ∀ i j,
      |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j) :
    ∀ i j,
      |D i j| ≤ C * matMulRect m m n
        (higham20Theorem20_4NormalizedWitness row0 col0 W)
        (fun r s => |A r s|) i j := by
  intro i j
  let G := higham20Theorem20_4NormalizedWitness row0 col0 W
  have hprod_nonneg :
      0 ≤ matMulRect m m n G (fun r s => |A r s|) i j := by
    unfold matMulRect
    exact Finset.sum_nonneg (fun r _ =>
      mul_nonneg
        (higham20Theorem20_4NormalizedWitness_nonneg
          row0 col0 W hW i r)
        (abs_nonneg (A r j)))
  have hscale :
      matMulRect m m n W (fun r s => |A r s|) i j =
        frobNorm W * matMulRect m m n G (fun r s => |A r s|) i j := by
    unfold matMulRect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [higham20Theorem20_4_witness_eq_frobNorm_mul_normalized
      row0 col0 W i r]
    ring
  calc
    |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j := hdom i j
    _ = frobNorm W * matMulRect m m n G (fun r s => |A r s|) i j := hscale
    _ ≤ C * matMulRect m m n G (fun r s => |A r s|) i j :=
      mul_le_mul_of_nonneg_right hWnorm hprod_nonneg

/-- Normalize any nonnegative square left witness that already dominates a
rectangular perturbation.  The conclusion has exactly the printed Theorem
20.4 shape: one nonnegative Frobenius-unit matrix multiplying `|A|`, with a
scalar coefficient that can be bounded using dimensions and gamma factors. -/
theorem higham20Theorem20_4_exists_unit_witness_of_left_domination
    {m n : ℕ} (row0 col0 : Fin m)
    (A D : Fin m → Fin n → ℝ) (W : Fin m → Fin m → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hWnorm : frobNorm W ≤ C)
    (hdom : ∀ i j,
      |D i j| ≤ matMulRect m m n W (fun r s => |A r s|) i j) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      ∀ i j,
        |D i j| ≤ C * matMulRect m m n G (fun r s => |A r s|) i j := by
  let G := higham20Theorem20_4NormalizedWitness row0 col0 W
  refine ⟨G, higham20Theorem20_4NormalizedWitness_nonneg
    row0 col0 W hW, higham20Theorem20_4NormalizedWitness_frobNorm
    row0 col0 W, ?_⟩
  exact higham20Theorem20_4_le_normalized_of_left_domination
    row0 col0 A D W C hW hWnorm hdom

/-- The nonnegative kernel `|Q| |Qᵀ|` that transports a componentwise
triangular perturbation back to source coordinates. -/
noncomputable def higham20Theorem20_4OrthogonalAbsKernel {m : ℕ}
    (Q : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  matMul m (fun i j => |Q i j|) (fun i j => |matTranspose Q i j|)

/-- Combined left witness for a common QR-panel perturbation of coefficient
`c` and a transported triangular perturbation of relative size `eta`. -/
noncomputable def higham20Theorem20_4TotalLeftWitness {m : ℕ}
    (Q G : Fin m → Fin m → ℝ) (c eta : ℝ) : Fin m → Fin m → ℝ :=
  let K := higham20Theorem20_4OrthogonalAbsKernel Q
  fun i j =>
    c * G i j +
      (eta * K i j + eta * c * matMul m K G i j)

private theorem higham20Theorem20_4_frobNorm_smul_nonneg {m : ℕ}
    (a : ℝ) (M : Fin m → Fin m → ℝ) (ha : 0 ≤ a) :
    frobNorm (fun i j => a * M i j) = a * frobNorm M := by
  rw [← frobNormRect_eq_frobNormFn, frobNormRect_smul,
    frobNormRect_eq_frobNormFn, abs_of_nonneg ha]

private theorem higham20Theorem20_4_abs_matMulRectLeft_le {m n : ℕ}
    (L : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    |matMulRectLeft L B i j| ≤
      matMulRect m m n (fun r s => |L r s|) (fun r s => |B r s|) i j := by
  unfold matMulRectLeft matMulRect
  calc
    |∑ k : Fin m, L i k * B k j| ≤
        ∑ k : Fin m, |L i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, |L i k| * |B k j| := by simp [abs_mul]

private theorem higham20Theorem20_4_matMulRect_mono_right {m n : ℕ}
    (L : Fin m → Fin m → ℝ) (B C : Fin m → Fin n → ℝ)
    (hL : ∀ i j, 0 ≤ L i j) (hBC : ∀ i j, B i j ≤ C i j)
    (i : Fin m) (j : Fin n) :
    matMulRect m m n L B i j ≤ matMulRect m m n L C i j := by
  unfold matMulRect
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left (hBC k j) (hL i k)

private theorem higham20Theorem20_4_matMulRect_mono_left {m n : ℕ}
    (L M : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (hLM : ∀ i j, L i j ≤ M i j) (hB : ∀ i j, 0 ≤ B i j)
    (i : Fin m) (j : Fin n) :
    matMulRect m m n L B i j ≤ matMulRect m m n M B i j := by
  unfold matMulRect
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_right (hLM i k) (hB k j)

theorem higham20Theorem20_4OrthogonalAbsKernel_nonneg {m : ℕ}
    (Q : Fin m → Fin m → ℝ) :
    ∀ i j, 0 ≤ higham20Theorem20_4OrthogonalAbsKernel Q i j := by
  intro i j
  unfold higham20Theorem20_4OrthogonalAbsKernel matMul
  exact Finset.sum_nonneg (fun k _ =>
    mul_nonneg (abs_nonneg (Q i k)) (abs_nonneg (matTranspose Q k j)))

theorem higham20Theorem20_4TotalLeftWitness_nonneg {m : ℕ}
    (Q G : Fin m → Fin m → ℝ) (c eta : ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (hc : 0 ≤ c) (heta : 0 ≤ eta) :
    ∀ i j, 0 ≤ higham20Theorem20_4TotalLeftWitness Q G c eta i j := by
  intro i j
  let K := higham20Theorem20_4OrthogonalAbsKernel Q
  have hK : ∀ r s, 0 ≤ K r s :=
    higham20Theorem20_4OrthogonalAbsKernel_nonneg Q
  have hKG : 0 ≤ matMul m K G i j := by
    unfold matMul
    exact Finset.sum_nonneg (fun r _ => mul_nonneg (hK i r) (hG r j))
  change 0 ≤ c * G i j +
    (eta * K i j + eta * c * matMul m K G i j)
  exact add_nonneg (mul_nonneg hc (hG i j))
    (add_nonneg (mul_nonneg heta (hK i j))
      (mul_nonneg (mul_nonneg heta hc) hKG))

/-- The orthogonal absolute-value transport kernel has Frobenius norm at most
the row dimension. -/
theorem higham20Theorem20_4OrthogonalAbsKernel_frobNorm_le {m : ℕ}
    (Q : Fin m → Fin m → ℝ) (hQ : IsOrthogonal m Q) :
    frobNorm (higham20Theorem20_4OrthogonalAbsKernel Q) ≤ (m : ℝ) := by
  let AQ : Fin m → Fin m → ℝ := fun i j => |Q i j|
  let AQT : Fin m → Fin m → ℝ := fun i j => |matTranspose Q i j|
  have hAQ : frobNorm AQ = frobNorm Q := by
    rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
    exact frobNormRect_abs Q
  have hAQT : frobNorm AQT = frobNorm Q := by
    calc
      frobNorm AQT = frobNorm (matTranspose Q) := by
        rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
        exact frobNormRect_abs (matTranspose Q)
      _ = frobNorm Q := frobNorm_transpose Q
  calc
    frobNorm (higham20Theorem20_4OrthogonalAbsKernel Q) =
        frobNorm (matMul m AQ AQT) := by rfl
    _ ≤ frobNorm AQ * frobNorm AQT := frobNorm_matMul_le AQ AQT
    _ = Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := by
      rw [hAQ, hAQT, hQ.frobNorm_eq_sqrt_card]
    _ = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)

/-- The combined witness has a data-independent Frobenius bound.  This is the
point where the hidden dimension constant in Higham's `gamma_tilde_m` is made
explicit. -/
theorem higham20Theorem20_4TotalLeftWitness_frobNorm_le {m : ℕ}
    (Q G : Fin m → Fin m → ℝ) (c eta : ℝ)
    (hQ : IsOrthogonal m Q) (hGnorm : frobNorm G = 1)
    (hc : 0 ≤ c) (heta : 0 ≤ eta) :
    frobNorm (higham20Theorem20_4TotalLeftWitness Q G c eta) ≤
      c + eta * (m : ℝ) + eta * c * (m : ℝ) := by
  let K := higham20Theorem20_4OrthogonalAbsKernel Q
  have hK : frobNorm K ≤ (m : ℝ) :=
    higham20Theorem20_4OrthogonalAbsKernel_frobNorm_le Q hQ
  have hKG : frobNorm (matMul m K G) ≤ (m : ℝ) := by
    calc
      frobNorm (matMul m K G) ≤ frobNorm K * frobNorm G :=
        frobNorm_matMul_le K G
      _ = frobNorm K := by rw [hGnorm, mul_one]
      _ ≤ (m : ℝ) := hK
  have hcG : frobNorm (fun i j => c * G i j) = c := by
    rw [higham20Theorem20_4_frobNorm_smul_nonneg c G hc, hGnorm, mul_one]
  have hetaK : frobNorm (fun i j => eta * K i j) = eta * frobNorm K :=
    higham20Theorem20_4_frobNorm_smul_nonneg eta K heta
  have heta_c : 0 ≤ eta * c := mul_nonneg heta hc
  have hetacKG :
      frobNorm (fun i j => eta * c * matMul m K G i j) =
        (eta * c) * frobNorm (matMul m K G) := by
    simpa [mul_assoc] using
      higham20Theorem20_4_frobNorm_smul_nonneg
        (eta * c) (matMul m K G) heta_c
  calc
    frobNorm (higham20Theorem20_4TotalLeftWitness Q G c eta) =
        frobNorm (fun i j => c * G i j +
          ((eta * K i j) + (eta * c * matMul m K G i j))) := by rfl
    _ ≤ frobNorm (fun i j => c * G i j) +
          frobNorm (fun i j => eta * K i j +
            eta * c * matMul m K G i j) := frobNorm_add_le _ _
    _ ≤ frobNorm (fun i j => c * G i j) +
          (frobNorm (fun i j => eta * K i j) +
            frobNorm (fun i j => eta * c * matMul m K G i j)) :=
      add_le_add le_rfl (frobNorm_add_le _ _)
    _ = c + (eta * frobNorm K +
          (eta * c) * frobNorm (matMul m K G)) := by
      rw [hcG, hetaK, hetacKG]
    _ ≤ c + (eta * (m : ℝ) + (eta * c) * (m : ℝ)) := by
      gcongr
    _ = c + eta * (m : ℝ) + eta * c * (m : ℝ) := by ring

/-- Mechanical assembly of the common panel bound and the transported
triangular bound into `higham20Theorem20_4TotalLeftWitness`.  The separate
transport hypothesis is exactly the analytic consequence of
`R̂ = Qᵀ(A+ΔA)` and `|ΔR| ≤ eta |R|`. -/
theorem higham20Theorem20_4TotalLeftWitness_domination_of_transport
    {m n : ℕ} (Q G : Fin m → Fin m → ℝ) (A D0 D1 : Fin m → Fin n → ℝ)
    (c eta : ℝ)
    (hD0 : ∀ i j,
      |D0 i j| ≤ c * matMulRect m m n G (fun r s => |A r s|) i j)
    (hD1 : ∀ i j,
      |D1 i j| ≤
        eta * matMulRect m m n
          (higham20Theorem20_4OrthogonalAbsKernel Q)
          (fun r s => |A r s|) i j +
        eta * c * matMulRect m m n
          (matMul m (higham20Theorem20_4OrthogonalAbsKernel Q) G)
          (fun r s => |A r s|) i j) :
    ∀ i j,
      |D0 i j + D1 i j| ≤
        matMulRect m m n
          (higham20Theorem20_4TotalLeftWitness Q G c eta)
          (fun r s => |A r s|) i j := by
  intro i j
  have hexpand :
      matMulRect m m n
          (higham20Theorem20_4TotalLeftWitness Q G c eta)
          (fun r s => |A r s|) i j =
        c * matMulRect m m n G (fun r s => |A r s|) i j +
          (eta * matMulRect m m n
              (higham20Theorem20_4OrthogonalAbsKernel Q)
              (fun r s => |A r s|) i j +
            eta * c * matMulRect m m n
              (matMul m (higham20Theorem20_4OrthogonalAbsKernel Q) G)
              (fun r s => |A r s|) i j) := by
    unfold matMulRect higham20Theorem20_4TotalLeftWitness
    simp_rw [add_mul, Finset.sum_add_distrib]
    simp_rw [Finset.mul_sum]
    ring
  calc
    |D0 i j + D1 i j| ≤ |D0 i j| + |D1 i j| := abs_add_le _ _
    _ ≤ c * matMulRect m m n G (fun r s => |A r s|) i j +
          (eta * matMulRect m m n
              (higham20Theorem20_4OrthogonalAbsKernel Q)
              (fun r s => |A r s|) i j +
            eta * c * matMulRect m m n
              (matMul m (higham20Theorem20_4OrthogonalAbsKernel Q) G)
              (fun r s => |A r s|) i j) :=
      add_le_add (hD0 i j) (hD1 i j)
    _ = matMulRect m m n
          (higham20Theorem20_4TotalLeftWitness Q G c eta)
          (fun r s => |A r s|) i j := hexpand.symm

/-- Derive the transported-triangular part of the total witness from the exact
QR relation and a componentwise relative perturbation of the tall `R` panel. -/
theorem higham20Theorem20_4_transport_domination_of_qr_relation
    {m n : ℕ} (Q G : Fin m → Fin m → ℝ)
    (A D0 Rhat Dhat : Fin m → Fin n → ℝ) (c eta : ℝ)
    (hc : 0 ≤ c) (heta : 0 ≤ eta) (hG : ∀ i j, 0 ≤ G i j)
    (hQR : Rhat = matMulRectLeft (matTranspose Q)
      (fun i j => A i j + D0 i j))
    (hD0 : ∀ i j,
      |D0 i j| ≤ c * matMulRect m m n G (fun r s => |A r s|) i j)
    (hDhat : ∀ i j, |Dhat i j| ≤ eta * |Rhat i j|) :
    ∀ i j,
      |matMulRectLeft Q Dhat i j| ≤
        eta * matMulRect m m n
          (higham20Theorem20_4OrthogonalAbsKernel Q)
          (fun r s => |A r s|) i j +
        eta * c * matMulRect m m n
          (matMul m (higham20Theorem20_4OrthogonalAbsKernel Q) G)
          (fun r s => |A r s|) i j := by
  let AQ : Fin m → Fin m → ℝ := fun i j => |Q i j|
  let AQT : Fin m → Fin m → ℝ := fun i j => |matTranspose Q i j|
  let Aabs : Fin m → Fin n → ℝ := fun i j => |A i j|
  let Dabs : Fin m → Fin n → ℝ := fun i j => |D0 i j|
  let GA : Fin m → Fin n → ℝ := matMulRect m m n G Aabs
  let S : Fin m → Fin n → ℝ := fun i j => Aabs i j + c * GA i j
  let K : Fin m → Fin m → ℝ := matMul m AQ AQT
  have hAQ : ∀ i j, 0 ≤ AQ i j := fun i j => abs_nonneg _
  have hAQT : ∀ i j, 0 ≤ AQT i j := fun i j => abs_nonneg _
  have hGA : ∀ i j, 0 ≤ GA i j := by
    intro i j
    unfold GA matMulRect
    exact Finset.sum_nonneg (fun r _ => mul_nonneg (hG i r) (abs_nonneg _))
  have hS : ∀ i j, 0 ≤ S i j := by
    intro i j
    exact add_nonneg (abs_nonneg _) (mul_nonneg hc (hGA i j))
  have hRabs : ∀ i j,
      |Rhat i j| ≤ matMulRect m m n AQT S i j := by
    intro i j
    have hraw := higham20Theorem20_4_abs_matMulRectLeft_le
      (matTranspose Q) (fun r s => A r s + D0 r s) i j
    rw [hQR]
    refine hraw.trans ?_
    apply higham20Theorem20_4_matMulRect_mono_right
      AQT (fun r s => |A r s + D0 r s|) S hAQT
    intro r s
    calc
      |A r s + D0 r s| ≤ |A r s| + |D0 r s| := abs_add_le _ _
      _ ≤ Aabs r s + c * GA r s := add_le_add le_rfl (hD0 r s)
      _ = S r s := rfl
  have hDhatS : ∀ i j,
      |Dhat i j| ≤ eta * matMulRect m m n AQT S i j := by
    intro i j
    exact (hDhat i j).trans
      (mul_le_mul_of_nonneg_left (hRabs i j) heta)
  intro i j
  have hraw := higham20Theorem20_4_abs_matMulRectLeft_le Q Dhat i j
  have hmono :
      matMulRect m m n AQ (fun r s => |Dhat r s|) i j ≤
        matMulRect m m n AQ
          (fun r s => eta * matMulRect m m n AQT S r s) i j :=
    higham20Theorem20_4_matMulRect_mono_right AQ
      (fun r s => |Dhat r s|)
      (fun r s => eta * matMulRect m m n AQT S r s)
      hAQ hDhatS i j
  have hscale :
      matMulRect m m n AQ
          (fun r s => eta * matMulRect m m n AQT S r s) i j =
        eta * matMulRect m m n AQ (matMulRect m m n AQT S) i j := by
    unfold matMulRect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  have hassoc :
      matMulRect m m n AQ (matMulRect m m n AQT S) i j =
        matMulRect m m n K S i j := by
    exact congrFun (congrFun
      (matMulRect_assoc_square_left m n AQ AQT S).symm i) j
  have hexpand :
      matMulRect m m n K S i j =
        matMulRect m m n K Aabs i j +
          c * matMulRect m m n (matMul m K G) Aabs i j := by
    calc
      matMulRect m m n K S i j =
          matMulRect m m n K Aabs i j +
            matMulRect m m n K (fun r s => c * GA r s) i j := by
        exact congrFun (congrFun (matMulRect_add_right m m n K Aabs
          (fun r s => c * GA r s)) i) j
      _ = matMulRect m m n K Aabs i j +
            c * matMulRect m m n K GA i j := by
        congr 1
        unfold matMulRect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
      _ = matMulRect m m n K Aabs i j +
            c * matMulRect m m n (matMul m K G) Aabs i j := by
        rw [matMulRect_assoc_square_left m n K G Aabs]
  calc
    |matMulRectLeft Q Dhat i j| ≤
        matMulRect m m n AQ (fun r s => |Dhat r s|) i j := hraw
    _ ≤ matMulRect m m n AQ
          (fun r s => eta * matMulRect m m n AQT S r s) i j := hmono
    _ = eta * matMulRect m m n AQ (matMulRect m m n AQT S) i j := hscale
    _ = eta * matMulRect m m n K S i j := by rw [hassoc]
    _ = eta * (matMulRect m m n K Aabs i j +
          c * matMulRect m m n (matMul m K G) Aabs i j) := by rw [hexpand]
    _ = eta * matMulRect m m n
          (higham20Theorem20_4OrthogonalAbsKernel Q)
          (fun r s => |A r s|) i j +
        eta * c * matMulRect m m n
          (matMul m (higham20Theorem20_4OrthogonalAbsKernel Q) G)
          (fun r s => |A r s|) i j := by
      dsimp [K, Aabs, AQ, AQT, higham20Theorem20_4OrthogonalAbsKernel]
      ring

/-- Source-shaped augmented-system handoff that deliberately retains the two
exact QR identities needed to absorb the triangular-solve perturbations.  The
older public handoffs discarded these identities after constructing the exact
system, which was the final obstruction to the printed total-matrix bound. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_with_source_bounds_and_qr_relation
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A Rhat : Fin (n + k) → Fin n → ℝ)
    (f c_hat : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (cA cComp cF cFsrc cG : ℝ)
    (H1 H2 H3 : Fin (n + k) → Fin (n + k) → ℝ)
    (hQR : StructuredHouseholderQRPanelHighamBackwardError (n + k) n
      A Q Rhat cA cComp)
    (hRhs : HouseholderQRRhsPanelExplicitBackwardError (n + k) n
      A f Q c_hat cF)
    (hcG : 0 ≤ cG)
    (hH1nonneg : ∀ i j, 0 ≤ H1 i j)
    (hH2nonneg : ∀ i j, 0 ≤ H2 i j)
    (hH3nonneg : ∀ i j, 0 ≤ H3 i j)
    (hH1norm : frobNorm H1 = 1)
    (hH2norm : frobNorm H2 = 1)
    (hH3norm : frobNorm H3 = 1)
    (hDeltafDom :
      let R : Fin n → Fin n → ℝ :=
        fun i j => Rhat (Fin.castAdd k i) j
      let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
      let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
      let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
      ∀ i : Fin (n + k),
        cF ≤ cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i)
    (hdiag : ∀ i : Fin n, Rhat (Fin.castAdd k i) i ≠ 0)
    (hgamma : gammaValid fp n) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i => cTop i - h i)
    let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ G : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ Deltag : Fin n → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤ cA ∧
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      (∀ i j, |DeltaA i j| ≤
        cComp * matMulRect (n + k) (n + k) n G
          (fun a b => |A a b|) i j) ∧
      (∀ i, |Deltaf i| ≤
        cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i) ∧
      (∀ j, |Deltag j| ≤
        cG * lsTheorem20_4DeltagMajorant A H3 rhat j) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      Rhat = matMulRectLeft (matTranspose Q)
        (fun i j => A i j + DeltaA i j) ∧
      Rhat = lsQRTallBlock (k := k) R ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) (fun j => g j + Deltag j)
        rhat x := by
  let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
  let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
  let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
  obtain ⟨DeltaA, G, hRrep, hDeltaA, hGnonneg, hGnorm, hDeltaAcomp⟩ :=
    hQR.result
  obtain ⟨Deltaf, hfRep, hDeltaf⟩ := hRhs.result
  have hRhatBlock : Rhat = lsQRTallBlock (k := k) R := by
    simpa [R] using lsQRTallBlock_of_upper_trapezoidal
      (n := n) (k := k) Rhat hQR.upper
  have hupperR : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R] using lsQRTallBlock_top_upper_of_upper_trapezoidal
      (n := n) (k := k) Rhat hQR.upper
  have hdiagR : ∀ i : Fin n, R i i ≠ 0 := by
    intro i
    simpa [R] using hdiag i
  have hRmat : Rhat = matMulRectLeft (matTranspose Q)
      (fun r col => A r col + DeltaA r col) := by
    ext i j
    simpa [matMulRectLeft, matMulRect] using hRrep i j
  have hApert :
      (fun i j => A i j + DeltaA i j) =
        matMulRectLeft Q (lsQRTallBlock R) := by
    have hQRmat : matMulRectLeft Q Rhat =
        (fun i j => A i j + DeltaA i j) := by
      rw [hRmat, ← matMulRectLeft_assoc]
      have hQQT : matMul (n + k) Q (matTranspose Q) = idMatrix (n + k) := by
        ext i j
        exact hQR.orth.right_inv i j
      rw [hQQT, matMulRectLeft_id]
    rw [← hQRmat, hRhatBlock]
  have hd : matMulVec (n + k) (matTranspose Q)
      (fun i => f i + Deltaf i) = Fin.append cTop cBot := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row =
          c_hat row := (hfRep row).symm
      _ = Fin.append cTop cBot row := by
        cases row using Fin.addCases with
        | left row => simp [cTop]
        | right row => simp [cBot]
  have hd0 : matMulVec (n + k) (matTranspose Q)
      (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => cTop i + (fun _ : Fin n => 0) i)
          cBot := by simpa using hd
  rcases LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
      fp Q (fun i j => A i j + DeltaA i j) R
      (fun i => f i + Deltaf i) cTop (fun _ : Fin n => 0) cBot g
      hQR.orth hApert hd0 hdiagR hupperR hgamma with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  let Deltag : Fin n → ℝ := fun _ => 0
  have hDeltafSrc : ∀ i : Fin (n + k),
      |Deltaf i| ≤ cFsrc * lsTheorem20_4DeltafMajorant H1 H2 f rhat i := by
    intro i
    exact (hDeltaf i).trans (hDeltafDom i)
  have hDeltag : ∀ j : Fin n,
      |Deltag j| ≤ cG * lsTheorem20_4DeltagMajorant A H3 rhat j := by
    intro j
    have hmaj := lsTheorem20_4DeltagMajorant_nonneg A H3 rhat hH3nonneg j
    simpa [Deltag] using mul_nonneg hcG hmaj
  refine ⟨DeltaA, G, Deltaf, Deltag, DeltaR1, DeltaR2,
    hDeltaA, hGnonneg, hGnorm, hDeltaAcomp, hDeltafSrc, hDeltag,
    hDeltaR1, hDeltaR2, hRmat, hRhatBlock, ?_⟩
  simpa [R, cTop, cBot, h, rhat, Deltag] using hsys

/-- Explicit tilde-gamma for the fully absorbed Theorem 20.4 matrix
perturbations.  Its extra terms are dimension-only transport costs for the two
triangular solves; no input-data-dependent coefficient is hidden here. -/
noncomputable def lsTheorem20_4ConcreteGammaTildeTotal (fp : FPModel)
    (m n : ℕ) : ℝ :=
  let g0 := lsTheorem20_4ConcreteGammaTildeSqrtResidual fp m n
  let c := (m : ℝ) * (n : ℝ) * g0
  2 * (g0 + gamma fp n + gamma fp n * c)

/-- Higham, 2nd ed., Theorem 20.4, with both actual total matrix
perturbations absorbed into one common nonnegative Frobenius-unit witness.

The theorem executes the repository's Householder panel/RHS kernels and both
rounded triangular solves.  `gamma_tilde` is explicit and depends only on the
format and dimensions. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_printed_total_perturbations
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex (n + k)))
    (hdomain : lsTheorem20_4FullRankComputedQRDomain fp A) :
    let gammaTilde :=
      lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n
    let Q := fl_householderQRPanel_Q fp (n + k) n A
    let Rhat := fl_householderQRPanel_R fp (n + k) n A
    let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
    let c_hat := fl_householderQRPanel_rhs fp (n + k) n A f
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i => cTop i - h i)
    let rhat : Fin (n + k) → ℝ := matMulVec (n + k) Q (Fin.append h cBot)
    ∃ DeltaA1 DeltaA2 : Fin (n + k) → Fin n → ℝ,
    ∃ G H1 H2 H3 : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ Deltag : Fin n → ℝ,
      (∀ i j, 0 ≤ G i j) ∧ frobNorm G = 1 ∧
      (∀ i j, 0 ≤ H1 i j) ∧ frobNorm H1 = 1 ∧
      (∀ i j, 0 ≤ H2 i j) ∧ frobNorm H2 = 1 ∧
      (∀ i j, 0 ≤ H3 i j) ∧ frobNorm H3 = 1 ∧
      (∀ i j, |DeltaA1 i j| ≤
        ((n + k : ℝ) * (n : ℝ) * gammaTilde) *
          matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j) ∧
      (∀ i j, |DeltaA2 i j| ≤
        ((n + k : ℝ) * (n : ℝ) * gammaTilde) *
          matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j) ∧
      (∀ i, |Deltaf i| ≤
        (Real.sqrt (n + k : ℝ) * (n : ℝ) * gammaTilde) *
          lsTheorem20_4DeltafMajorant H1 H2 f rhat i) ∧
      (∀ j, |Deltag j| ≤
        (Real.sqrt (n + k : ℝ) * (n : ℝ) * gammaTilde) *
          lsTheorem20_4DeltagMajorant A H3 rhat j) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA1 i j)
        (fun i j => A i j + DeltaA2 i j)
        (fun i => f i + Deltaf i) (fun j => g j + Deltag j)
        rhat x := by
  let m : ℕ := n + k
  let Q : Fin m → Fin m → ℝ := fl_householderQRPanel_Q fp m n A
  let Rhat : Fin m → Fin n → ℝ := fl_householderQRPanel_R fp m n A
  let R : Fin n → Fin n → ℝ := fun i j => Rhat (Fin.castAdd k i) j
  let c_hat : Fin m → ℝ := fl_householderQRPanel_rhs fp m n A f
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
  let rhat : Fin m → ℝ := matMulVec m Q (Fin.append h cBot)
  let Kidx : ℕ := householderConstructApplyGammaIndex m
  let gammaPanel : ℝ := gamma fp (n * Kidx)
  let resCoeff : ℝ := householderQRRhsPanelSqrtResidualGrowthCoeff fp m n
  let g0 : ℝ := lsTheorem20_4ConcreteGammaTildeSqrtResidual fp m n
  let c : ℝ := (m : ℝ) * (n : ℝ) * g0
  let eta : ℝ := gamma fp n
  let gammaTilde : ℝ := lsTheorem20_4ConcreteGammaTildeTotal fp m n
  have hgamma : gammaValid fp n :=
    gammaValid_n_of_householderConstructApplyGammaValid fp m n (by
      simpa [m, Kidx] using hvalid)
  have hn_le_rows : n ≤ m := by simp [m]
  have hsteps : 0 < Nat.min m n := by
    simpa [Nat.min_eq_right hn_le_rows] using hn
  have hQR : StructuredHouseholderQRPanelHighamBackwardError m n A Q Rhat
      (gammaPanel * frobNorm A) ((m : ℝ) * gammaPanel) := by
    have hraw :=
      fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid
        fp m n A hsteps (by
          simpa [m, Kidx, Nat.min_eq_right hn_le_rows] using hvalid)
    simpa [Q, Rhat, gammaPanel, Kidx, Nat.min_eq_right hn_le_rows] using hraw
  have hK_le_nK : Kidx ≤ n * Kidx := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right Kidx hn1
  have hbase_le_K : 11 * m + 23 ≤ Kidx := by
    dsimp [Kidx, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * m + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) (by
      simpa [m, Kidx] using hvalid)
  have hready : HouseholderQRPanelReady fp m n A :=
    HouseholderQRPanelReady_of_global_gammaValid fp m n m A le_rfl hbase_valid
  have hRhs : HouseholderQRRhsPanelExplicitBackwardError m n A f Q c_hat
      (householderQRRhsPanelSqrtResidualBackwardBound fp m n A f) := by
    simpa [Q, c_hat] using
      fl_householderQRPanel_rhs_explicit_backward_error_sqrt_residual
        fp m n A f hready
  rcases
      householderQRRhsPanelSqrtResidualBackwardBound_uniform_f_source_witness_of_sqrtResidualGrowthCoeff
        fp A f g hn hbase_valid hready with
    ⟨H1, H2, hH1nonneg, hH2nonneg, hH1norm, hH2norm, hDeltafDom⟩
  let row0 : Fin m := ⟨0, by simp [m]; omega⟩
  let H3 : Fin m → Fin m → ℝ := lsTheorem20_4OneHotMajorant row0 row0
  have hH3nonneg : ∀ i j, 0 ≤ H3 i j :=
    lsTheorem20_4OneHotMajorant_nonneg row0 row0
  have hH3norm : frobNorm H3 = 1 :=
    lsTheorem20_4OneHotMajorant_frobNorm row0 row0
  have hcG : 0 ≤ Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg n))
      (gamma_nonneg fp (by simpa [m, Kidx, gammaPanel] using hvalid))
  rcases LSAsymmetricAugmentedSystem.exists_exact_qr_solution_with_source_bounds_and_qr_relation
      fp Q A Rhat f c_hat g
      (gammaPanel * frobNorm A) ((m : ℝ) * gammaPanel)
      (householderQRRhsPanelSqrtResidualBackwardBound fp m n A f)
      (Real.sqrt (m : ℝ) * resCoeff)
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel)
      H1 H2 H3 hQR hRhs hcG hH1nonneg hH2nonneg hH3nonneg
      hH1norm hH2norm hH3norm
      (by simpa [Q, Rhat, R, c_hat, cBot, h, rhat, m, resCoeff] using
        hDeltafDom)
      (by simpa [Rhat, m] using hdomain.computedQRNonbreakdown) hgamma with
    ⟨DeltaA, G0, Deltaf, Deltag, DeltaR1, DeltaR2,
      _hDeltaAnorm, hG0nonneg, hG0norm, hDeltaAraw, hDeltaf, hDeltag,
      hDeltaR1, hDeltaR2, hQRrel, hRhatBlock, hsys⟩
  have hg0_nonneg : 0 ≤ g0 := by
    simpa [g0, m] using
      lsTheorem20_4ConcreteGammaTildeSqrtResidual_nonneg fp hn (by
        simpa [m, Kidx] using hvalid)
  have heta_nonneg : 0 ≤ eta := gamma_nonneg fp hgamma
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))
      hg0_nonneg
  have hpanel_le_g0 : gammaPanel ≤ g0 := by
    simpa [gammaPanel, g0, m, Kidx] using
      gamma_le_lsTheorem20_4ConcreteGammaTildeSqrtResidual fp hn (by
        simpa [m, Kidx] using hvalid)
  have hres_le_g0 : resCoeff ≤ g0 := by
    simpa [resCoeff, g0, m] using
      householderQRRhsPanelSqrtResidualGrowthCoeff_le_lsTheorem20_4ConcreteGammaTildeSqrtResidual
        fp (m := m) (n := n) (by simpa [m, Kidx] using hvalid)
  have hDeltaA : ∀ i j,
      |DeltaA i j| ≤ c * matMulRect m m n G0 (fun r s => |A r s|) i j := by
    intro i j
    have hmaj : 0 ≤ matMulRect m m n G0 (fun r s => |A r s|) i j := by
      unfold matMulRect
      exact Finset.sum_nonneg (fun r _ =>
        mul_nonneg (hG0nonneg i r) (abs_nonneg _))
    have hcoeff : (m : ℝ) * gammaPanel ≤ c := by
      dsimp [c]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
      calc
        (m : ℝ) * gammaPanel ≤ (m : ℝ) * g0 :=
          mul_le_mul_of_nonneg_left hpanel_le_g0 (Nat.cast_nonneg m)
        _ = (m : ℝ) * (1 : ℝ) * g0 := by ring
        _ ≤ (m : ℝ) * (n : ℝ) * g0 := by gcongr
    exact (hDeltaAraw i j).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have hDhat1 : ∀ i j,
      |lsQRTallBlock (k := k) DeltaR1 i j| ≤ eta * |Rhat i j| := by
    intro i j
    rw [hRhatBlock]
    cases i using Fin.addCases with
    | left i => simpa [lsQRTallBlock, eta, R] using hDeltaR1 i j
    | right i => simp [lsQRTallBlock, eta]
  have hDhat2 : ∀ i j,
      |lsQRTallBlock (k := k) DeltaR2 i j| ≤ eta * |Rhat i j| := by
    intro i j
    rw [hRhatBlock]
    cases i using Fin.addCases with
    | left i => simpa [lsQRTallBlock, eta, R] using hDeltaR2 i j
    | right i => simp [lsQRTallBlock, eta]
  have htransport1 := higham20Theorem20_4_transport_domination_of_qr_relation
    Q G0 A DeltaA Rhat (lsQRTallBlock (k := k) DeltaR1) c eta
    hc_nonneg heta_nonneg hG0nonneg hQRrel hDeltaA hDhat1
  have htransport2 := higham20Theorem20_4_transport_domination_of_qr_relation
    Q G0 A DeltaA Rhat (lsQRTallBlock (k := k) DeltaR2) c eta
    hc_nonneg heta_nonneg hG0nonneg hQRrel hDeltaA hDhat2
  let QdR1 : Fin m → Fin n → ℝ := matMulRectLeft Q (lsQRTallBlock DeltaR1)
  let QdR2 : Fin m → Fin n → ℝ := matMulRectLeft Q (lsQRTallBlock DeltaR2)
  let DeltaA1 : Fin m → Fin n → ℝ := fun i j => DeltaA i j + QdR1 i j
  let DeltaA2 : Fin m → Fin n → ℝ := fun i j => DeltaA i j + QdR2 i j
  let W1 := higham20Theorem20_4TotalLeftWitness Q G0 c eta
  let W2 := higham20Theorem20_4TotalLeftWitness Q G0 c eta
  let W : Fin m → Fin m → ℝ := fun i j => W1 i j + W2 i j
  have hW1nonneg : ∀ i j, 0 ≤ W1 i j :=
    higham20Theorem20_4TotalLeftWitness_nonneg Q G0 c eta
      hG0nonneg hc_nonneg heta_nonneg
  have hW2nonneg : ∀ i j, 0 ≤ W2 i j := hW1nonneg
  have hdomW1 : ∀ i j, |DeltaA1 i j| ≤
      matMulRect m m n W1 (fun r s => |A r s|) i j := by
    simpa [DeltaA1, QdR1, W1] using
      higham20Theorem20_4TotalLeftWitness_domination_of_transport
        Q G0 A DeltaA QdR1 c eta hDeltaA htransport1
  have hdomW2 : ∀ i j, |DeltaA2 i j| ≤
      matMulRect m m n W2 (fun r s => |A r s|) i j := by
    simpa [DeltaA2, QdR2, W2] using
      higham20Theorem20_4TotalLeftWitness_domination_of_transport
        Q G0 A DeltaA QdR2 c eta hDeltaA htransport2
  have hWnonneg : ∀ i j, 0 ≤ W i j := by
    intro i j
    exact add_nonneg (hW1nonneg i j) (hW2nonneg i j)
  have hdom1 : ∀ i j, |DeltaA1 i j| ≤
      matMulRect m m n W (fun r s => |A r s|) i j := by
    intro i j
    exact (hdomW1 i j).trans
      (higham20Theorem20_4_matMulRect_mono_left W1 W
        (fun r s => |A r s|)
        (fun r s => le_add_of_nonneg_right (hW2nonneg r s))
        (fun r s => abs_nonneg _) i j)
  have hdom2 : ∀ i j, |DeltaA2 i j| ≤
      matMulRect m m n W (fun r s => |A r s|) i j := by
    intro i j
    exact (hdomW2 i j).trans
      (higham20Theorem20_4_matMulRect_mono_left W2 W
        (fun r s => |A r s|)
        (fun r s => le_add_of_nonneg_left (hW1nonneg r s))
        (fun r s => abs_nonneg _) i j)
  have hW1norm : frobNorm W1 ≤
      c + eta * (m : ℝ) + eta * c * (m : ℝ) := by
    simpa [W1] using higham20Theorem20_4TotalLeftWitness_frobNorm_le
      Q G0 c eta hQR.orth hG0norm hc_nonneg heta_nonneg
  have hW2norm : frobNorm W2 ≤
      c + eta * (m : ℝ) + eta * c * (m : ℝ) := by simpa [W2, W1] using hW1norm
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have heta_m_le : eta * (m : ℝ) ≤ eta * (m : ℝ) * (n : ℝ) := by
    calc
      eta * (m : ℝ) = (eta * (m : ℝ)) * 1 := by ring
      _ ≤ (eta * (m : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn1R
          (mul_nonneg heta_nonneg (Nat.cast_nonneg m))
  have hetac_m_le : eta * c * (m : ℝ) ≤
      eta * c * (m : ℝ) * (n : ℝ) := by
    calc
      eta * c * (m : ℝ) = (eta * c * (m : ℝ)) * 1 := by ring
      _ ≤ (eta * c * (m : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn1R
          (mul_nonneg (mul_nonneg heta_nonneg hc_nonneg) (Nat.cast_nonneg m))
  have hC : 2 * (c + eta * (m : ℝ) + eta * c * (m : ℝ)) ≤
      (m : ℝ) * (n : ℝ) * gammaTilde := by
    dsimp [gammaTilde, lsTheorem20_4ConcreteGammaTildeTotal]
    dsimp [c]
    calc
      2 * (((m : ℝ) * (n : ℝ) * g0) + eta * (m : ℝ) +
          eta * ((m : ℝ) * (n : ℝ) * g0) * (m : ℝ)) ≤
        2 * (((m : ℝ) * (n : ℝ) * g0) +
          eta * (m : ℝ) * (n : ℝ) +
          eta * ((m : ℝ) * (n : ℝ) * g0) * (m : ℝ) * (n : ℝ)) := by
            gcongr
      _ = (m : ℝ) * (n : ℝ) *
          (2 * (g0 + eta + eta * ((m : ℝ) * (n : ℝ) * g0))) := by ring
  have hWnorm : frobNorm W ≤ (m : ℝ) * (n : ℝ) * gammaTilde := by
    calc
      frobNorm W ≤ frobNorm W1 + frobNorm W2 := by
        simpa [W] using frobNorm_add_le W1 W2
      _ ≤ 2 * (c + eta * (m : ℝ) + eta * c * (m : ℝ)) := by linarith
      _ ≤ (m : ℝ) * (n : ℝ) * gammaTilde := hC
  let G := higham20Theorem20_4NormalizedWitness row0 row0 W
  have hGnonneg : ∀ i j, 0 ≤ G i j :=
    higham20Theorem20_4NormalizedWitness_nonneg row0 row0 W hWnonneg
  have hGnorm : frobNorm G = 1 :=
    higham20Theorem20_4NormalizedWitness_frobNorm row0 row0 W
  have htotal1 : ∀ i j, |DeltaA1 i j| ≤
      ((m : ℝ) * (n : ℝ) * gammaTilde) *
        matMulRect m m n G (fun r s => |A r s|) i j := by
    simpa [G] using higham20Theorem20_4_le_normalized_of_left_domination
      row0 row0 A DeltaA1 W ((m : ℝ) * (n : ℝ) * gammaTilde)
      hWnonneg hWnorm hdom1
  have htotal2 : ∀ i j, |DeltaA2 i j| ≤
      ((m : ℝ) * (n : ℝ) * gammaTilde) *
        matMulRect m m n G (fun r s => |A r s|) i j := by
    simpa [G] using higham20Theorem20_4_le_normalized_of_left_domination
      row0 row0 A DeltaA2 W ((m : ℝ) * (n : ℝ) * gammaTilde)
      hWnonneg hWnorm hdom2
  have hg0_le_total : g0 ≤ gammaTilde := by
    dsimp [gammaTilde, lsTheorem20_4ConcreteGammaTildeTotal]
    have hsum : 0 ≤ g0 + eta + eta * c := by positivity
    nlinarith
  have hDeltafTotal : ∀ i, |Deltaf i| ≤
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde) *
        lsTheorem20_4DeltafMajorant H1 H2 f rhat i := by
    intro i
    have hmaj := lsTheorem20_4DeltafMajorant_nonneg
      H1 H2 f rhat hH1nonneg hH2nonneg i
    have hcoeff : Real.sqrt (m : ℝ) * resCoeff ≤
        Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by
      have hres : resCoeff ≤ (n : ℝ) * gammaTilde :=
        hres_le_g0.trans <| calc
          g0 = 1 * g0 := by ring
          _ ≤ (n : ℝ) * gammaTilde :=
            mul_le_mul hn1R hg0_le_total hg0_nonneg (by positivity)
      calc
        Real.sqrt (m : ℝ) * resCoeff ≤
            Real.sqrt (m : ℝ) * ((n : ℝ) * gammaTilde) :=
          mul_le_mul_of_nonneg_left hres (Real.sqrt_nonneg _)
        _ = Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by ring
    exact (hDeltaf i).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have hDeltagTotal : ∀ j, |Deltag j| ≤
      (Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde) *
        lsTheorem20_4DeltagMajorant A H3 rhat j := by
    intro j
    have hmaj := lsTheorem20_4DeltagMajorant_nonneg A H3 rhat hH3nonneg j
    have hcoeff : Real.sqrt (m : ℝ) * (n : ℝ) * gammaPanel ≤
        Real.sqrt (m : ℝ) * (n : ℝ) * gammaTilde := by
      gcongr
      exact hpanel_le_g0.trans hg0_le_total
    exact (hDeltag j).trans (mul_le_mul_of_nonneg_right hcoeff hmaj)
  have htotal1' : ∀ i j, |DeltaA1 i j| ≤
      ((n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j := by
    simpa [m, gammaTilde] using htotal1
  have htotal2' : ∀ i j, |DeltaA2 i j| ≤
      ((n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        matMulRect (n + k) (n + k) n G (fun r s => |A r s|) i j := by
    simpa [m, gammaTilde] using htotal2
  have hDeltafTotal' : ∀ i, |Deltaf i| ≤
      (Real.sqrt (n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        lsTheorem20_4DeltafMajorant H1 H2 f
          (matMulVec (n + k) (fl_householderQRPanel_Q fp (n + k) n A)
            (Fin.append
              (fl_forwardSub fp n
                (matTranspose (fun i j =>
                  fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) j)) g)
              (fun i =>
                fl_householderQRPanel_rhs fp (n + k) n A f (Fin.natAdd n i)))) i := by
    simpa [m, gammaTilde, rhat, Q, R, c_hat, cBot, h] using hDeltafTotal
  have hDeltagTotal' : ∀ j, |Deltag j| ≤
      (Real.sqrt (n + k : ℝ) * (n : ℝ) *
        lsTheorem20_4ConcreteGammaTildeTotal fp (n + k) n) *
        lsTheorem20_4DeltagMajorant A H3
          (matMulVec (n + k) (fl_householderQRPanel_Q fp (n + k) n A)
            (Fin.append
              (fl_forwardSub fp n
                (matTranspose (fun i j =>
                  fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) j)) g)
              (fun i =>
                fl_householderQRPanel_rhs fp (n + k) n A f (Fin.natAdd n i)))) j := by
    simpa [m, gammaTilde, rhat, Q, R, c_hat, cBot, h] using hDeltagTotal
  refine ⟨DeltaA1, DeltaA2, G, H1, H2, H3, Deltaf, Deltag,
    hGnonneg, hGnorm, hH1nonneg, hH1norm, hH2nonneg, hH2norm,
    hH3nonneg, hH3norm, htotal1', htotal2', hDeltafTotal', hDeltagTotal', ?_⟩
  simpa [m, Q, Rhat, R, c_hat, cBot, h, rhat, DeltaA1, DeltaA2,
    QdR1, QdR2, add_assoc] using hsys

end NumStability
