-- Algorithms/Ch14MethodDUpperCertificate.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.3.4 "Method D", equations (14.20)-(14.23),
-- pp. 270-271.
--
-- WAVE-4 GOAL (discharge Method D's upper-triangular-inverse LEFT certificate).
--
-- `Ch14MethodDLeftResidual.ch14ext_methodD_left_residual_bound_eps` derives the
-- printed Method D componentwise envelope
--
--     |X̂ A − I| ≤ (4γ + 2γ²) |X_U||X_L| |L̂||Û|                       (14.23)
--
-- from four local certificates.  Wave 3 discharged the LOWER-triangular inverse
-- LEFT residual with the concrete Method 2 loop
-- (`Ch14Method2Loop.ch14ext_method2_left_residual`) but left the UPPER-triangular
-- inverse LEFT residual  |X_U Û − I| ≤ γ|X_U||Û|  as an OPEN hypothesis: the
-- Method 2 loop's residual is LEFT for lower-triangular inputs, and transposing
-- it produces a RIGHT (not LEFT) residual for an upper-triangular matrix, which
-- does not match the slot Method D needs.
--
-- THIS FILE closes that gap.  The correct bridge is NOT the transpose (which
-- reverses the product order, turning a left residual into a right one) but the
-- REVERSAL (persymmetric) conjugation  A ↦ J A J,  where `J` is the reversal
-- permutation `Fin.rev`.  Because `J² = I`, the map `A ↦ J A J` is an ALGEBRA
-- automorphism — it preserves the product order  (JAJ)(JBJ) = J(AB)J — and it
-- carries lower-triangular matrices to upper-triangular ones.  Hence Higham's
-- "analogue of Method 2 for upper triangular matrices" (§14.3.4) is realised
-- concretely as the reversal-conjugated Method 2 loop
--
--     X_U := J · ch14ext_method2Inv(J U J) · J ,
--
-- and its LEFT residual  |X_U U − I| = |J (Z L − I) J|  inherits the wave-2
-- Method 2 LEFT residual  |Z L − I| ≤ γ|Z||L|  entry-for-entry (both sides are
-- merely reindexed by `Fin.rev`), giving the required
--
--     |X_U U − I|_{ij} ≤ γ_{n+2} (|X_U||U|)_{ij}.
--
-- What is CLOSED unconditionally here:
--   * `ch14ext_method2InvUpper`               — the concrete upper-triangular
--       Method 2 loop (reversal-conjugated lower loop).
--   * `ch14ext_method2Upper_left_residual`    — Lemma 14.1 LEFT residual for the
--       upper-triangular inverse at `γ_{n+2}`, DERIVED (no hypothesis).
--   * `ch14ext_method2Upper_left_residual_normwise` — its ‖·‖_∞ companion.
--   * `ch14ext_methodD_left_residual_both`    — the printed (4γ+2γ²) Method D
--       envelope (14.23) with BOTH triangular-inverse LEFT residual certificates
--       DISCHARGED (X_U by this file's upper loop, X_L by the wave-2 lower loop).
--       The only remaining hypotheses are the two genuine UPSTREAM certificates:
--       `hLU` (Higham Thm 9.3 GE backward error, A = L̂Û + ΔA) and `hProd`
--       (the fl-matmul certificate for the final product X̂ = fl(X_U X_L)).
--   * `ch14ext_methodD_left_residual_both_infNorm` — its normwise companion.
--
-- No new floating-point analysis is assumed for the triangular inverses: every
-- constant is DERIVED, and both inverse certificates are concrete loop results.

import NumStability.Algorithms.Ch14Method2Loop
import NumStability.Algorithms.Ch14MethodDLeftResidual

namespace NumStability.Ch14Ext

open scoped BigOperators

-- ============================================================
-- The reversal (persymmetric) permutation as an involutive equivalence
-- ============================================================

/-- The reversal permutation `Fin.rev` packaged as an involutive equivalence,
    used to reindex the whole-matrix sums.  `J i = n-1-i`; `J² = id`. -/
def ch14ext_finRev (n : ℕ) : Fin n ≃ Fin n :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

@[simp] lemma ch14ext_finRev_apply (n : ℕ) (i : Fin n) :
    ch14ext_finRev n i = Fin.rev i := rfl

-- ============================================================
-- The concrete upper-triangular Method 2 loop (reversal-conjugated)
-- ============================================================

/-- **Method 2 upper-triangular inversion (Higham §14.3.4 "analogue of Method 2
    for upper triangular matrices"), concrete loop.**

    `ch14ext_method2InvUpper n fp U` is the reversal-conjugation `J Z J` of the
    concrete lower-triangular Method 2 loop `Z = ch14ext_method2Inv` applied to
    `J U J` (where `J = Fin.rev`).  Since `A ↦ J A J` is a product-order-preserving
    automorphism carrying upper-triangular `U` to the lower-triangular `J U J`,
    this is the honest upper-triangular analogue of Method 2, and its LEFT
    residual mirrors the lower loop's LEFT residual exactly. -/
noncomputable def ch14ext_method2InvUpper (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ch14ext_method2Inv n fp (fun a b => U (Fin.rev a) (Fin.rev b))
      (Fin.rev i) (Fin.rev j)

-- ============================================================
-- Structural facts of the reversal-conjugated lower matrix `J U J`
-- ============================================================

/-- `J U J` is lower triangular when `U` is upper triangular. -/
lemma ch14ext_revConj_lowerTri {n : ℕ} (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i j : Fin n, j.val > i.val →
      (fun a b => U (Fin.rev a) (Fin.rev b)) i j = 0 := by
  intro i j hij
  apply hUT
  simp only [Fin.val_rev]
  omega

/-- `J U J` has nonzero diagonal when `U` does. -/
lemma ch14ext_revConj_diag_nonzero {n : ℕ} (U : Fin n → Fin n → ℝ)
    (hUnz : ∀ j : Fin n, U j j ≠ 0) :
    ∀ j : Fin n, (fun a b => U (Fin.rev a) (Fin.rev b)) j j ≠ 0 :=
  fun j => hUnz (Fin.rev j)

-- ============================================================
-- Lemma 14.1 / (14.8) LEFT residual for the upper-triangular Method 2 loop
-- ============================================================

/-- **Higham Lemma 14.1 / (14.8) — upper-triangular Method 2 loop, LEFT residual,
    componentwise.**

    The upper-triangular inverse `X̂ = ch14ext_method2InvUpper n fp U` produced by
    the reversal-conjugated Method 2 loop on a nonsingular UPPER triangular `U`
    satisfies the componentwise LEFT residual bound

        |X̂ U − I|_{ij} ≤ γ_{n+2} · (|X̂| |U|)_{ij}.

    DERIVED from the wave-2 lower-triangular loop residual
    `ch14ext_method2_left_residual` by reindexing both the residual and the
    absolute-product bound with the reversal permutation `Fin.rev` (the
    persymmetric automorphism `A ↦ J A J` preserves the product order, so the
    LEFT residual stays a LEFT residual — no right/left swap as with a
    transpose). -/
theorem ch14ext_method2Upper_left_residual (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_method2InvUpper n fp U i k * U k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2InvUpper n fp U i k| * |U k j| := by
  intro i j
  -- wave-2 lower loop applied to the reversal-conjugated (lower-tri) matrix
  have hres :=
    ch14ext_method2_left_residual n fp (fun a b => U (Fin.rev a) (Fin.rev b))
      hn2 (ch14ext_revConj_lowerTri U hUT) (ch14ext_revConj_diag_nonzero U hUnz)
      (Fin.rev i) (Fin.rev j)
  -- reindex the product sum by `Fin.rev`
  have hA :
      (∑ k : Fin n, ch14ext_method2InvUpper n fp U i k * U k j) =
        ∑ k : Fin n,
          ch14ext_method2Inv n fp (fun a b => U (Fin.rev a) (Fin.rev b))
            (Fin.rev i) k *
            (fun a b => U (Fin.rev a) (Fin.rev b)) k (Fin.rev j) := by
    rw [← Equiv.sum_comp (ch14ext_finRev n)
      (fun k =>
        ch14ext_method2Inv n fp (fun a b => U (Fin.rev a) (Fin.rev b))
          (Fin.rev i) k *
          (fun a b => U (Fin.rev a) (Fin.rev b)) k (Fin.rev j))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ch14ext_finRev_apply, ch14ext_method2InvUpper, Fin.rev_rev]
  -- reindex the absolute-product sum by `Fin.rev`
  have hB :
      (∑ k : Fin n, |ch14ext_method2InvUpper n fp U i k| * |U k j|) =
        ∑ k : Fin n,
          |ch14ext_method2Inv n fp (fun a b => U (Fin.rev a) (Fin.rev b))
            (Fin.rev i) k| *
            |(fun a b => U (Fin.rev a) (Fin.rev b)) k (Fin.rev j)| := by
    rw [← Equiv.sum_comp (ch14ext_finRev n)
      (fun k =>
        |ch14ext_method2Inv n fp (fun a b => U (Fin.rev a) (Fin.rev b))
          (Fin.rev i) k| *
          |(fun a b => U (Fin.rev a) (Fin.rev b)) k (Fin.rev j)|)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ch14ext_finRev_apply, ch14ext_method2InvUpper, Fin.rev_rev]
  -- the identity index matches under `Fin.rev`
  have hC : (if i = j then (1 : ℝ) else 0) = if Fin.rev i = Fin.rev j then 1 else 0 := by
    simp only [Fin.rev_inj]
  rw [hA, hC, hB]
  exact hres

/-- **Higham Lemma 14.1 / (14.8) — upper-triangular Method 2 loop, LEFT residual,
    infinity-norm.**

        ‖X̂ U − I‖_∞ ≤ γ_{n+2} · ‖X̂‖_∞ · ‖U‖_∞ .

    Normwise companion of `ch14ext_method2Upper_left_residual`, via the repo
    componentwise→normwise bridge. -/
theorem ch14ext_method2Upper_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, ch14ext_method2InvUpper n fp U i k * U k j -
        if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm (ch14ext_method2InvUpper n fp U) * infNorm U :=
  higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (gamma_nonneg fp hn2)
    (ch14ext_method2Upper_left_residual n fp U hn2 hUT hUnz)

-- ============================================================
-- Method D (14.23) with BOTH triangular-inverse certificates discharged
-- ============================================================

/-- **Higham (14.23), Method D left residual — both triangular inverses concrete.**

    The printed `(4γ + 2γ²)` componentwise Method D envelope with

      * the UPPER inverse `X_U := ch14ext_method2InvUpper n fp U` (this file's
        reversal-conjugated Method 2 loop), its LEFT residual DISCHARGED by
        `ch14ext_method2Upper_left_residual`;
      * the LOWER inverse `X_L := ch14ext_method2Inv n fp L` (the wave-2 Method 2
        loop), its LEFT residual DISCHARGED by `ch14ext_method2_left_residual`;

    both at the shared honest accumulator `γ = gamma fp (n+2)`.  Neither
    triangular-inverse residual is a hypothesis any longer.

    The two REMAINING hypotheses are the genuine UPSTREAM certificates, not
    inverse-internal ones:

      * `hLU` — the LU backward-error certificate (Higham Thm 9.3, A = L̂Û + ΔA);
      * `hProd` — the fl product-formation certificate for X̂ = fl(X_U X_L).

    Both are naturally available at accumulator `γ_n ≤ γ_{n+2}`, so stating them
    at the shared `γ_{n+2}` is no strengthening. -/
theorem ch14ext_methodD_left_residual_both (n : ℕ) (fp : FPModel)
    (A L U X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2)))
    (hProd : MatProdError n X_hat
      (matMul n (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |ch14ext_method2InvUpper n fp U i q|
                * |ch14ext_method2Inv n fp L q p|) *
              (∑ r : Fin n, |L p r| * |U r j|) := by
  have hγ : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hn2
  -- lower-inverse LEFT residual, discharged by the wave-2 Method 2 loop
  have hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual (ch14ext_method2Inv n fp L) L i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2Inv n fp L i k| * |L k j| := by
    intro i j
    simpa [higham14_methodDXLLeftResidual, matMul] using
      ch14ext_method2_left_residual n fp L hn2 hLT hLnz i j
  -- upper-inverse LEFT residual, discharged by THIS file's reversal-conjugated loop
  have hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual (ch14ext_method2InvUpper n fp U) U i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2InvUpper n fp U i k| * |U k j| := by
    intro i j
    simpa [higham14_methodDXULeftResidual, matMul] using
      ch14ext_method2Upper_left_residual n fp U hn2 hUT hUnz i j
  exact ch14ext_methodD_left_residual_bound_eps (gamma fp (n + 2)) hγ
    A L U (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) X_hat
    hLU hXL_res hXU_res hProd

/-- **Higham (14.23), Method D left residual — both triangular inverses concrete,
    normwise.**

    Infinity-norm companion of `ch14ext_methodD_left_residual_both`; both
    triangular-inverse LEFT residual certificates are discharged by the concrete
    loops, with the same two upstream hypotheses (`hLU`, `hProd`). -/
theorem ch14ext_methodD_left_residual_both_infNorm (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (A L U X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2)))
    (hProd : MatProdError n X_hat
      (matMul n (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
        infNorm (matMul n (absMatrix n (ch14ext_method2InvUpper n fp U))
          (absMatrix n (ch14ext_method2Inv n fp L))) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  have hγ : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hn2
  have hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual (ch14ext_method2Inv n fp L) L i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2Inv n fp L i k| * |L k j| := by
    intro i j
    simpa [higham14_methodDXLLeftResidual, matMul] using
      ch14ext_method2_left_residual n fp L hn2 hLT hLnz i j
  have hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual (ch14ext_method2InvUpper n fp U) U i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2InvUpper n fp U i k| * |U k j| := by
    intro i j
    simpa [higham14_methodDXULeftResidual, matMul] using
      ch14ext_method2Upper_left_residual n fp U hn2 hUT hUnz i j
  exact ch14ext_methodD_left_residual_infNorm_eps hn0 (gamma fp (n + 2)) hγ
    A L U (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) X_hat
    hLU hXL_res hXU_res hProd

end NumStability.Ch14Ext
