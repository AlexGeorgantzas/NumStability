import NumStability.Analysis.MatrixAlgebra

namespace NumStability

/-!
# Absorption

Canonical reusable module extracted without change from Higham20Theorem20_4Absorption.
-/

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

end NumStability
