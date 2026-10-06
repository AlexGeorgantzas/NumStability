/-
  Algorithms/LU/BlockLUComputationSourceClosure.lean

  Computation-derived source endpoint for Higham Theorem 13.6.

  The earlier conventional-solve theorem executed both triangular solves but
  accepted a completed `PartitionedLUFirstOrderSpec` for the factorization.
  The theorem below closes that gap: it consumes the recursive Algorithm 13.1
  computation certificate, derives its Theorem 13.5 residual, and only then
  executes the conventional Algorithm 13.3 solve path.
-/

import NumStability.Algorithms.LU.BlockLUFirstOrderFamilies

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-! ## Uniformly usable bounds for the concrete DHS solve

The legacy concrete solve theorem in `BlockLU` records several estimates with
`FirstOrderLe` at one fixed unit roundoff.  That is useful for a pointwise
calculation, but it cannot be lifted to a family theorem: the hidden
quadratic coefficient may depend on the family index.  The lemmas in this
section retain direct linear inequalities from the actual rounded
operations.  They are deliberately conservative (the matrix-product leading
constant is doubled under `n*u <= 1/2`), which makes the estimates uniform.
-/

/-- A direct, denominator-free max-entry bound for conventional matrix
multiplication when `n*u <= 1/2`.

Unlike `higham13_conventional_matmul_c1_maxEntry_bound`, this conclusion is
an ordinary inequality, not a fixed-`u` `FirstOrderLe`.  It is therefore safe
to use pointwise throughout a roundoff family. -/
theorem higham13_conventional_matmul_maxEntry_linear_bound
    {m n p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hSmall : (n : ℝ) * fp.u ≤ 1 / 2) :
    maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      (2 * (n : ℝ) ^ 2) * fp.u *
        maxEntryNormRect hm hn A * maxEntryNormRect hn hp B := by
  have hγ : gammaValid fp n := by
    unfold gammaValid
    linarith
  have hγle : gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp n hSmall
  have hγ0 : 0 ≤ gamma fp n := gamma_nonneg fp hγ
  have hA0 : 0 ≤ maxEntryNormRect hm hn A :=
    maxEntryNormRect_nonneg hm hn A
  have hB0 : 0 ≤ maxEntryNormRect hn hp B :=
    maxEntryNormRect_nonneg hn hp B
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  have hsum :
      (∑ k : Fin n, |A i k| * |B k j|) ≤
        (n : ℝ) *
          (maxEntryNormRect hm hn A * maxEntryNormRect hn hp B) := by
    calc
      (∑ k : Fin n, |A i k| * |B k j|) ≤
          ∑ _k : Fin n,
            maxEntryNormRect hm hn A * maxEntryNormRect hn hp B := by
        apply Finset.sum_le_sum
        intro k _hk
        exact mul_le_mul
          (entry_le_maxEntryNormRect hm hn A i k)
          (entry_le_maxEntryNormRect hn hp B k j)
          (abs_nonneg (B k j)) hA0
      _ = (n : ℝ) *
          (maxEntryNormRect hm hn A * maxEntryNormRect hn hp B) := by simp
  calc
    |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j| ≤
        gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
      matMul_error_bound fp m n p A B hγ i j
    _ ≤ gamma fp n *
        ((n : ℝ) *
          (maxEntryNormRect hm hn A * maxEntryNormRect hn hp B)) :=
      mul_le_mul_of_nonneg_left hsum hγ0
    _ ≤ (2 * ((n : ℝ) * fp.u)) *
        ((n : ℝ) *
          (maxEntryNormRect hm hn A * maxEntryNormRect hn hp B)) := by
      exact mul_le_mul_of_nonneg_right hγle
        (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hA0 hB0))
    _ = (2 * (n : ℝ) ^ 2) * fp.u *
        maxEntryNormRect hm hn A * maxEntryNormRect hn hp B := by ring

/-- The max-entry norm is bounded by the exact Euclidean operator norm. -/
theorem maxEntryNorm_le_opNorm2 {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    maxEntryNorm hn A ≤ opNorm2 A := by
  classical
  apply maxEntryNorm_le_of_entry_le_bound
  intro i j
  let e : Fin n → ℝ := finiteBasisVec j
  have hentry : matMulVec n A e i = A i j := by
    unfold matMulVec e finiteBasisVec
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  calc
    |A i j| = |matMulVec n A e i| := by rw [hentry]
    _ ≤ vecNorm2 (matMulVec n A e) := abs_coord_le_vecNorm2 _ i
    _ ≤ opNorm2 A * vecNorm2 e := opNorm2Le_opNorm2 A e
    _ = opNorm2 A := by rw [vecNorm2_finiteBasisVec, mul_one]

/-- The exact Euclidean operator norm is at most `n` times the max-entry
norm. -/
theorem opNorm2_le_dim_mul_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    opNorm2 A ≤ (n : ℝ) * maxEntryNorm hn A := by
  have hMax0 : 0 ≤ maxEntryNorm hn A := maxEntryNorm_nonneg hn A
  have hFrob : frobNorm A ≤ (n : ℝ) * maxEntryNorm hn A := by
    calc
      frobNorm A ≤ frobNorm (fun _i _j : Fin n => maxEntryNorm hn A) := by
        apply frobNorm_le_of_entry_abs_le
        · intro _i _j
          exact hMax0
        · intro i j
          exact entry_le_maxEntryNorm hn A i j
      _ = (n : ℝ) * maxEntryNorm hn A := frobNorm_const hMax0
  calc
    opNorm2 A ≤ frobNorm A :=
      opNorm2_le_of_opNorm2Le A (frobNorm_nonneg A)
        (opNorm2Le_of_frobNorm_self A)
    _ ≤ (n : ℝ) * maxEntryNorm hn A := hFrob

/-- Convert a uniform max-entry Theorem-13.6 estimate to the exact Euclidean
operator norm, keeping the explicit dimension factor. -/
theorem higham13_theorem13_6_opNorm2_family_from_maxEntry
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {n : ℕ} (hn : 0 < n) (c : ℝ)
    (A Lhat Uhat Delta : ι → Matrix (Fin n) (Fin n) ℝ)
    (hc : 0 ≤ c)
    (hMax : FamilyFirstOrderLe l Uround.unit
      (fun t => c * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (Delta t))) :
    FamilyFirstOrderLe l Uround.unit
      (fun t => ((n : ℝ) * c) * Uround.unit t *
        (opNorm2 (A t) + opNorm2 (Lhat t) * opNorm2 (Uhat t)))
      (fun t => opNorm2 (Delta t)) := by
  have hScaled := hMax.mul_bounded
    (scale := fun _t => (n : ℝ))
    (target := fun t => opNorm2 (Delta t))
    (fun _t => Nat.cast_nonneg n)
    (ScalarFamilyIsBigOOne.const (n : ℝ))
    (fun t => by
      calc
        opNorm2 (Delta t) ≤ (n : ℝ) * maxEntryNorm hn (Delta t) :=
          opNorm2_le_dim_mul_maxEntryNorm hn (Delta t)
        _ = maxEntryNorm hn (Delta t) * (n : ℝ) := by ring)
  apply hScaled.mono_leading
  intro t
  have hA := maxEntryNorm_le_opNorm2 hn (A t)
  have hL := maxEntryNorm_le_opNorm2 hn (Lhat t)
  have hU := maxEntryNorm_le_opNorm2 hn (Uhat t)
  have hProduct :
      maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t) ≤
        opNorm2 (Lhat t) * opNorm2 (Uhat t) :=
    mul_le_mul hL hU (maxEntryNorm_nonneg hn (Uhat t))
      (opNorm2_nonneg (Lhat t))
  have hInside :
      maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t) ≤
        opNorm2 (A t) + opNorm2 (Lhat t) * opNorm2 (Uhat t) :=
    add_le_add hA hProduct
  have hPrefactor : 0 ≤ (n : ℝ) * (c * Uround.unit t) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hc (Uround.unit_nonneg t))
  calc
    (c * Uround.unit t *
          (maxEntryNorm hn (A t) +
            maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t))) *
        (n : ℝ) =
      ((n : ℝ) * (c * Uround.unit t)) *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)) := by ring
    _ ≤ ((n : ℝ) * (c * Uround.unit t)) *
        (opNorm2 (A t) + opNorm2 (Lhat t) * opNorm2 (Uhat t)) :=
      mul_le_mul_of_nonneg_left hInside hPrefactor
    _ = ((n : ℝ) * c) * Uround.unit t *
        (opNorm2 (A t) + opNorm2 (Lhat t) * opNorm2 (Uhat t)) := by ring

/-- One source-correct conventional block-back row with a direct linear
coefficient bound.

The perturbation is lifted against the full upper suffix, so it may occupy
the diagonal block and is zero strictly below the current row.  The factor
`2` in front of `(m*r)^2` is the uniform price of replacing `gamma_(m*r)` by
`2*(m*r)*u` under the displayed small-roundoff hypothesis. -/
theorem
    dhs_block_back_upper_suffix_row_perturbation_linear_bound_from_conventional_operations
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (cRhs normU : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Y : Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hcRhs : 0 ≤ cRhs) (hNormU : 0 ≤ normU)
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i U) ≤ normU)
    (hRhsScale :
      maxEntryNormRect hr (Nat.succ_pos 0) Y +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) ≤
        cRhs * normU * infNormVec (dhsBlockBackUpperSuffixVector i X)) :
    ∃ (Delta : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      higham13_fl_matrixSub fp Y
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U j * X j) +
          (∑ j : Fin m, Delta j * X j) = Y ∧
      (∀ j : Fin m, j.val < i.val → Delta j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |Delta j s t| ≤ rowPerturbBound) ∧
      rowPerturbBound ≤
        (2 * (((m * r : ℕ) : ℝ) ^ 2) + cRhs) * fp.u * normU := by
  let A := dhsBlockBackUpperTailRowFlat i U
  let B := dhsBlockBackUpperTailColumn i X
  let Chat : Matrix (Fin r) (Fin 1) ℝ := fl_matMul fp r (m * r) 1 A B
  let DeltaC : Matrix (Fin r) (Fin 1) ℝ := fun s k =>
    Chat s k - ∑ jt : Fin (m * r), A s jt * B jt k
  let Fsub := higham13_fl_matrixSubError fp Y Chat
  let Dhat := higham13_fl_matrixSub fp Y Chat
  let tailNorm := infNormVec (dhsBlockBackUpperTailVector i X)
  let suffixNorm := infNormVec (dhsBlockBackUpperSuffixVector i X)
  let productCoefficient : ℝ := 2 * (((m * r : ℕ) : ℝ) ^ 2)
  let rowPerturbBound : ℝ :=
    (productCoefficient + cRhs) * fp.u * normU
  have hγ : gammaValid fp (m * r) := by
    unfold gammaValid
    linarith
  have hBnorm : maxEntryNormRect (Nat.mul_pos hm hr) (Nat.succ_pos 0) B =
      tailNorm := by
    rw [maxEntryNormRect_single_col_eq_infNormVec]
    rfl
  have hMul : MatMulFirstOrderSpec fp.u (((m * r : ℕ) : ℝ) ^ 2)
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A) tailNorm
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      A B Chat DeltaC := by
    simpa only [Chat, DeltaC, hBnorm] using
      higham13_conventional_matmul_spec_c1_maxEntry
        fp hr (Nat.mul_pos hm hr) (Nat.succ_pos 0) A B hγ
  have hSub : SubtractionFirstOrderSpec fp.u
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat := by
    exact higham13_conventional_subtraction_spec_maxEntry
      fp hr (Nat.succ_pos 0) Y Chat
  have hTailSuffix : tailNorm ≤ suffixNorm :=
    dhsBlockBackUpperTail_infNormVec_le_suffix i X
  have hTail0 : 0 ≤ tailNorm := infNormVec_nonneg _
  have hSuffix0 : 0 ≤ suffixNorm := infNormVec_nonneg _
  have hProductCoefficient0 : 0 ≤ productCoefficient := by
    dsimp only [productCoefficient]
    positivity
  have hProductPrefactor0 : 0 ≤ productCoefficient * fp.u :=
    mul_nonneg hProductCoefficient0 fp.u_nonneg
  have hDeltaLinear :
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC ≤
        productCoefficient * fp.u * normU * suffixNorm := by
    calc
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC ≤
          productCoefficient * fp.u *
            maxEntryNormRect hr (Nat.mul_pos hm hr) A *
              maxEntryNormRect (Nat.mul_pos hm hr) (Nat.succ_pos 0) B := by
        simpa only [productCoefficient, DeltaC, Chat] using
          higham13_conventional_matmul_maxEntry_linear_bound
            fp hr (Nat.mul_pos hm hr) (Nat.succ_pos 0) A B hSmallProduct
      _ = productCoefficient * fp.u *
            maxEntryNormRect hr (Nat.mul_pos hm hr) A * tailNorm := by
        rw [hBnorm]
      _ ≤ productCoefficient * fp.u * normU * tailNorm := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hUTailU hProductPrefactor0) hTail0
      _ ≤ productCoefficient * fp.u * normU * suffixNorm := by
        exact mul_le_mul_of_nonneg_left hTailSuffix
          (mul_nonneg hProductPrefactor0 hNormU)
  have hSubLinear :
      maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
        cRhs * fp.u * normU * suffixNorm := by
    calc
      maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
          fp.u *
            (maxEntryNormRect hr (Nat.succ_pos 0) Y +
              maxEntryNormRect hr (Nat.succ_pos 0) Chat) := hSub.norm_bound
      _ ≤ fp.u * (cRhs * normU * suffixNorm) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Chat, suffixNorm] using hRhsScale) fp.u_nonneg
      _ = cRhs * fp.u * normU * suffixNorm := by ring
  have hRow0 : 0 ≤ rowPerturbBound := by
    dsimp only [rowPerturbBound]
    exact mul_nonneg
      (mul_nonneg (add_nonneg hProductCoefficient0 hcRhs) fp.u_nonneg)
      hNormU
  have hResidualScale :
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
          maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
        rowPerturbBound * suffixNorm := by
    calc
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
          maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
          productCoefficient * fp.u * normU * suffixNorm +
            cRhs * fp.u * normU * suffixNorm :=
        add_le_add hDeltaLinear hSubLinear
      _ = rowPerturbBound * suffixNorm := by
        dsimp only [rowPerturbBound]
        ring
  obtain ⟨Delta, hEquation, hSupport, hEntry⟩ :=
    dhs_block_back_upper_suffix_row_perturbation_from_specs
      hm hr i fp.u (((m * r : ℕ) : ℝ) ^ 2)
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A) tailNorm
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      rowPerturbBound U X Chat DeltaC Y Fsub Dhat hRow0 hMul hSub
      hResidualScale
  exact ⟨Delta, rowPerturbBound, by simpa [A, B, Chat, Dhat] using hEquation,
    hSupport, hEntry, by
      dsimp only [rowPerturbBound, productCoefficient]
      exact le_rfl⟩

/-- The conservative row coefficient used by the uniform concrete DHS
block-back-substitution proof.

The first summand is the direct conventional tail-product bound, the second
is the source RHS comparison, and the final term is the local diagonal solve
(13.15). -/
def higham13DHSUniformBackRowCoefficient (m r : ℕ) : ℝ :=
  (2 * (((m * r : ℕ) : ℝ) ^ 2) +
      4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
    2 * (r : ℝ)

/-- Direct forward-product coefficient used by the uniform concrete DHS
solve. -/
def higham13DHSUniformForwardCoefficient (m r : ℕ) : ℝ :=
  2 * (((m * r : ℕ) : ℝ) ^ 2)

/-- Direct left-transport coefficient for the uniform block-back
perturbation. -/
def higham13DHSUniformBackCoefficient (m r : ℕ) : ℝ :=
  ((m * r : ℕ) : ℝ) * higham13DHSUniformBackRowCoefficient m r

/-- Total direct solve coefficient for the uniform concrete DHS endpoint. -/
def higham13DHSUniformSolveCoefficient (dFact : ℝ) (m r : ℕ) : ℝ :=
  dFact + higham13DHSUniformForwardCoefficient m r +
    higham13DHSUniformBackCoefficient m r

/-- Concrete recursive block back substitution with an ordinary, direct
entrywise perturbation bound.

This theorem executes the repository's descending block solution, derives
all conventional diagonal-solve perturbations, derives every rounded
tail-product/subtraction perturbation, combines them without discarding the
diagonal RHS perturbation, and flattens the exact block equations.  Its final
entry bound has no pointwise hidden constant and can therefore be selected
simultaneously over a roundoff family. -/
theorem
    dhs_block_back_substitution_rows_linear_bound_from_conventional_recursive_block_solution
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normU)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * maxEntryNorm hr (U i i)) ∧
      (∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec fp.u (2 * (r : ℝ))
          (maxEntryNorm hr (U i i)) (maxEntryNorm hr (DeltaDiag i))
          (U i i) (DeltaDiag i)
          (dhsBlockBackConventionalSolution fp U Y i)
          (dhsBlockBackConventionalRHS fp i U
            (dhsBlockBackConventionalSolution fp U Y) Y)) ∧
      DHSBlockBackSubstitutionRowsFirstOrderSpec
        fp.u (higham13DHSUniformBackRowCoefficient m r) normU
        (higham13DHSUniformBackRowCoefficient m r * fp.u * normU)
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin (dhsBlockBackConventionalSolution fp U Y))
        (blockMatrixRowsFlatFin Y) := by
  classical
  let X := dhsBlockBackConventionalSolution fp U Y
  let n : ℕ := m * r
  let cRhs : ℝ := 4 * (((m * r : ℕ) : ℝ) + (r : ℝ))
  let cSuffix : ℝ := 2 * (((m * r : ℕ) : ℝ) ^ 2) + cRhs
  let cDiag : ℝ := 2 * (r : ℝ)
  let cRows : ℝ := cSuffix + cDiag
  let suffixPerturbBound : ℝ := cSuffix * fp.u * normU
  let rowPerturbBound : ℝ := cRows * fp.u * normU
  have hNormU : 0 ≤ normU := by
    let i0 : Fin m := ⟨0, hm⟩
    exact le_trans (maxEntryNorm_nonneg hr (U i0 i0)) (hUiiNorm i0)
  have hSmallBlock : (r : ℝ) * fp.u ≤ 1 / 2 := by
    have hrNat : r ≤ m * r := by
      calc
        r = 1 * r := by simp
        _ ≤ m * r := Nat.mul_le_mul_right r (by omega)
    have hrReal : (r : ℝ) ≤ ((m * r : ℕ) : ℝ) := by
      exact_mod_cast hrNat
    exact le_trans
      (mul_le_mul_of_nonneg_right hrReal fp.u_nonneg) hSmallProduct
  have hSmallDiag : cDiag * fp.u ≤ 1 := by
    dsimp only [cDiag]
    calc
      (2 * (r : ℝ)) * fp.u = 2 * ((r : ℝ) * fp.u) := by ring
      _ ≤ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hSmallBlock (by norm_num)
      _ = 1 := by norm_num
  rcases dhs_conventional_diagonal_block_solve_specs
      fp hr (fun i => maxEntryNorm hr (U i i)) U X Y hSmallBlock
      (fun _i => le_rfl) hDiag hUpper
      (by
        intro i a
        simpa only [X] using
          dhsBlockBackConventionalSolution_execution fp U Y i a) with
    ⟨DeltaDiag, hDeltaDiag, hDiagonal⟩
  have hDeltaDiagU : ∀ i : Fin m,
      maxEntryNorm hr (DeltaDiag i) ≤ normU := by
    intro i
    have hUii0 : 0 ≤ maxEntryNorm hr (U i i) := maxEntryNorm_nonneg hr _
    calc
      maxEntryNorm hr (DeltaDiag i) ≤
          cDiag * fp.u * maxEntryNorm hr (U i i) := by
        simpa only [cDiag] using hDeltaDiag i
      _ ≤ 1 * maxEntryNorm hr (U i i) :=
        mul_le_mul_of_nonneg_right hSmallDiag hUii0
      _ ≤ 1 * normU :=
        mul_le_mul_of_nonneg_left (hUiiNorm i) (by norm_num)
      _ = normU := one_mul normU
  have hRowWitnesses : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (bound : ℝ),
        dhsBlockBackConventionalRHS fp i U X Y +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j : Fin m, DeltaRow j * X j) = Y i ∧
        (∀ j : Fin m, j.val < i.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r, |DeltaRow j s t| ≤ bound) ∧
        bound ≤ suffixPerturbBound := by
    intro i
    have hRhsScale :=
      dhs_block_back_conventional_rhs_scale_of_small_roundoff_and_diagonal_bounds
        fp hm hr i normU U (DeltaDiag i) X Y hSmallProduct
        (hUTailU i) (hUiiNorm i) (hDeltaDiagU i) (hDiagonal i).equation
    rcases
        dhs_block_back_upper_suffix_row_perturbation_linear_bound_from_conventional_operations
          fp hm hr i cRhs normU (U i) X (Y i) hSmallProduct
          (by dsimp only [cRhs]; positivity) hNormU (hUTailU i)
          (by
            simpa only [dhsBlockBackConventionalUpperProduct, cRhs] using
              hRhsScale) with
      ⟨DeltaRow, bound, hEquation, hSupport, hEntry, hBound⟩
    refine ⟨DeltaRow, bound, ?_, hSupport, hEntry, ?_⟩
    · simpa only [X, dhsBlockBackConventionalRHS,
        dhsBlockBackConventionalUpperProduct] using hEquation
    · simpa only [suffixPerturbBound, cSuffix, cRhs] using hBound
  choose DeltaRow rowBound hRow using hRowWitnesses
  let DeltaSuffix : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    fun i j => DeltaRow i j
  have hSuffix : DHSBlockBackSubstitutionSuffixRowsFirstOrderSpec
      fp.u cSuffix normU suffixPerturbBound U DeltaSuffix X Y
      (fun i => dhsBlockBackConventionalRHS fp i U X Y) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hji
      simpa only [DeltaSuffix] using (hRow i).2.1 j hji
    · intro i
      simpa only [DeltaSuffix] using (hRow i).1
    · intro i j s t
      calc
        |DeltaSuffix i j s t| ≤ rowBound i := by
          simpa only [DeltaSuffix] using (hRow i).2.2.1 j s t
        _ ≤ suffixPerturbBound := (hRow i).2.2.2
    · apply FirstOrderLe.of_le
      exact le_rfl
  let DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := fun i j =>
    DeltaSuffix i j + if j = i then DeltaDiag i else 0
  let DhatCombined : Fin m → Matrix (Fin r) (Fin 1) ℝ := fun i =>
    dhsBlockBackConventionalRHS fp i U X Y + DeltaSuffix i i * X i
  have hDiagLinear : ∀ i : Fin m,
      maxEntryNorm hr (DeltaDiag i) ≤ cDiag * fp.u * normU := by
    intro i
    calc
      maxEntryNorm hr (DeltaDiag i) ≤
          cDiag * fp.u * maxEntryNorm hr (U i i) := by
        simpa only [cDiag] using hDeltaDiag i
      _ ≤ cDiag * fp.u * normU := by
        exact mul_le_mul_of_nonneg_left (hUiiNorm i)
          (mul_nonneg (by dsimp only [cDiag]; positivity) fp.u_nonneg)
  have hDeltaUEntry : ∀ i j : Fin m, ∀ s t : Fin r,
      |DeltaU i j s t| ≤ rowPerturbBound := by
    intro i j s t
    by_cases hji : j = i
    · subst j
      simp only [DeltaU, if_pos]
      calc
        |DeltaSuffix i i s t + DeltaDiag i s t| ≤
            |DeltaSuffix i i s t| + |DeltaDiag i s t| := abs_add_le _ _
        _ ≤ suffixPerturbBound + maxEntryNorm hr (DeltaDiag i) :=
          add_le_add (hSuffix.entry_bound i i s t)
            (entry_le_maxEntryNorm hr (DeltaDiag i) s t)
        _ ≤ suffixPerturbBound + cDiag * fp.u * normU :=
          add_le_add le_rfl (hDiagLinear i)
        _ = rowPerturbBound := by
          dsimp only [rowPerturbBound, cRows, suffixPerturbBound]
          ring
    · simp only [DeltaU, if_neg hji, add_zero]
      calc
        |DeltaSuffix i j s t| ≤ suffixPerturbBound :=
          hSuffix.entry_bound i j s t
        _ ≤ suffixPerturbBound + cDiag * fp.u * normU := by
          exact le_add_of_nonneg_right
            (mul_nonneg
              (mul_nonneg (by dsimp only [cDiag]; positivity) fp.u_nonneg)
              hNormU)
        _ = rowPerturbBound := by
          dsimp only [rowPerturbBound, cRows, suffixPerturbBound]
          ring
  have hFixed : DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
      hr fp.u cRows cRows normU rowPerturbBound (fun _i => normU)
      U DeltaU X Y DhatCombined := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j hji
      have hneji : j ≠ i := by omega
      refine ⟨hUUpper i j hji, ?_⟩
      simp [DeltaU, hneji, hSuffix.support i j hji]
    · intro i
      let g : Fin m → Matrix (Fin r) (Fin 1) ℝ :=
        fun j => DeltaSuffix i j * X j
      have hbelow :
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬i.val ≤ j.val),
            g j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hji : j.val < i.val := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
            using hj
        simp [g, hSuffix.support i j hji]
      have htailset :
          Finset.univ.filter (fun j : Fin m => i.val ≤ j.val) \ {i} =
            Finset.univ.filter (fun j : Fin m => i.val < j.val) := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_singleton]
        omega
      have hge :
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
            g j) =
            DeltaSuffix i i * X i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                DeltaSuffix i j * X j := by
        calc
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
              g j) =
              g i +
                ∑ j ∈ (Finset.univ.filter
                  (fun j : Fin m => i.val ≤ j.val)) \ {i}, g j := by
            exact Finset.sum_eq_add_sum_diff_singleton i g (by simp)
          _ = g i +
                ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                  g j := by rw [htailset]
          _ = DeltaSuffix i i * X i +
                ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                  DeltaSuffix i j * X j := by rfl
      have hDeltaDecomp :
          (∑ j : Fin m, DeltaSuffix i j * X j) =
            DeltaSuffix i i * X i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                DeltaSuffix i j * X j := by
        change (∑ j : Fin m, g j) = _
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j : Fin m => i.val ≤ j.val)]
        rw [hbelow, add_zero, hge]
      have hTailExpand :
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U i j + DeltaU i j) * X j) =
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              DeltaSuffix i j * X j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i.val < j.val := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
        have hneji : j ≠ i := by omega
        simp only [DeltaU, if_neg hneji, add_zero, Matrix.add_mul]
      rw [hTailExpand]
      simp only [DhatCombined]
      calc
        dhsBlockBackConventionalRHS fp i U X Y +
              DeltaSuffix i i * X i +
              ((∑ j ∈ Finset.univ.filter
                    (fun j : Fin m => i.val < j.val), U i j * X j) +
                ∑ j ∈ Finset.univ.filter
                    (fun j : Fin m => i.val < j.val),
                  DeltaSuffix i j * X j) =
            dhsBlockBackConventionalRHS fp i U X Y +
              (∑ j ∈ Finset.univ.filter
                (fun j : Fin m => i.val < j.val), U i j * X j) +
              (DeltaSuffix i i * X i +
                ∑ j ∈ Finset.univ.filter
                  (fun j : Fin m => i.val < j.val),
                  DeltaSuffix i j * X j) := by abel
        _ = dhsBlockBackConventionalRHS fp i U X Y +
              (∑ j ∈ Finset.univ.filter
                (fun j : Fin m => i.val < j.val), U i j * X j) +
              (∑ j : Fin m, DeltaSuffix i j * X j) := by
          rw [hDeltaDecomp]
        _ = Y i := hSuffix.rhs_formation i
    · intro i
      constructor
      · have hDeltaAtDiag :
            DeltaU i i = DeltaSuffix i i + DeltaDiag i := by simp [DeltaU]
        rw [hDeltaAtDiag]
        calc
          (U i i + (DeltaSuffix i i + DeltaDiag i)) * X i =
              (U i i + DeltaDiag i) * X i + DeltaSuffix i i * X i := by
            rw [show U i i + (DeltaSuffix i i + DeltaDiag i) =
                (U i i + DeltaDiag i) + DeltaSuffix i i by abel]
            rw [Matrix.add_mul]
          _ = dhsBlockBackConventionalRHS fp i U X Y +
                DeltaSuffix i i * X i := by rw [(hDiagonal i).equation]
          _ = DhatCombined i := by rfl
      · apply FirstOrderLe.of_le
        apply maxEntryNorm_le_of_entry_le_bound
        exact hDeltaUEntry i i
    · exact hDeltaUEntry
    · apply FirstOrderLe.of_le
      exact le_rfl
  have hRows : DHSBlockBackSubstitutionRowsFirstOrderSpec
      fp.u cRows normU rowPerturbBound
      (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
      (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) :=
    dhs_block_back_substitution_rows_spec_from_fixed_block_rows_and_eq13_15
      hr fp.u cRows cRows normU rowPerturbBound (fun _i => normU)
      U DeltaU X Y DhatCombined hFixed
  refine ⟨DeltaDiag, DeltaU, hDeltaDiag, hDiagonal, ?_⟩
  simpa only [X, cRows, cSuffix, cDiag, cRhs, rowPerturbBound,
    higham13DHSUniformBackRowCoefficient] using hRows

/-- Family-level aggregation for equation (13.16).  Unlike the legacy
pointwise adapter, the hidden quadratic constants here are uniform along the
roundoff filter. -/
theorem higham13_theorem13_6_eq13_16_family_from_factor_solve_bounds
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (dFact dSolve dn : ℝ)
    (normA normL normU normDeltaFact normDeltaSolve : ι → ℝ)
    (hA : ∀ t, 0 ≤ normA t) (hL : ∀ t, 0 ≤ normL t)
    (hU : ∀ t, 0 ≤ normU t)
    (hFactLe : dFact ≤ dn) (hSolveLe : dSolve ≤ dn)
    (hFact : FamilyFirstOrderLe l Uround.unit
      (fun t => dFact * Uround.unit t *
        (normA t + normL t * normU t)) normDeltaFact)
    (hSolve : FamilyFirstOrderLe l Uround.unit
      (fun t => dSolve * Uround.unit t *
        (normA t + normL t * normU t)) normDeltaSolve) :
    FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t)) normDeltaFact ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t)) normDeltaSolve ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t))
        (fun t => max (normDeltaFact t) (normDeltaSolve t)) := by
  have hFactDn := hFact.mono_leading (fun t => by
    have hscale : 0 ≤ Uround.unit t *
        (normA t + normL t * normU t) :=
      mul_nonneg (Uround.unit_nonneg t)
        (add_nonneg (hA t) (mul_nonneg (hL t) (hU t)))
    calc
      dFact * Uround.unit t * (normA t + normL t * normU t) =
          dFact * (Uround.unit t *
            (normA t + normL t * normU t)) := by ring
      _ ≤ dn * (Uround.unit t *
            (normA t + normL t * normU t)) :=
        mul_le_mul_of_nonneg_right hFactLe hscale
      _ = dn * Uround.unit t *
            (normA t + normL t * normU t) := by ring)
  have hSolveDn := hSolve.mono_leading (fun t => by
    have hscale : 0 ≤ Uround.unit t *
        (normA t + normL t * normU t) :=
      mul_nonneg (Uround.unit_nonneg t)
        (add_nonneg (hA t) (mul_nonneg (hL t) (hU t)))
    calc
      dSolve * Uround.unit t * (normA t + normL t * normU t) =
          dSolve * (Uround.unit t *
            (normA t + normL t * normU t)) := by ring
      _ ≤ dn * (Uround.unit t *
            (normA t + normL t * normU t)) :=
        mul_le_mul_of_nonneg_right hSolveLe hscale
      _ = dn * Uround.unit t *
            (normA t + normL t * normU t) := by ring)
  exact ⟨hFactDn, hSolveDn,
    FamilyFirstOrderLe.combineMax hFactDn hSolveDn |>.mono_leading
      (fun _ => (max_self _).le)⟩

/-- Family-level Theorem 13.6 factor/solve endpoint with the factorization
half derived from the recursive Algorithm 13.1 computation rather than
accepted as a completed `PartitionedLUFirstOrderSpec`.

The solve perturbation and its equation are tied to the actual displayed
matrix family.  `hSolve` is the remaining implementation-specific DHS solve
estimate; the theorem does not disguise it as a final factorization premise. -/
theorem higham13_theorem13_6_family_from_partitioned_computation_and_solve
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {n m p : ℕ} (hn : 0 < n)
    (c₁ c₂ c₃ dFact dSolve dn : ℝ)
    (A DeltaFact Lhat Uhat DeltaSolve :
      ι → Matrix (Fin n) (Fin n) ℝ)
    (xhat b : ι → Matrix (Fin n) (Fin p) ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hDelta : blockErrorDelta m ≤ dFact)
    (hTheta : blockErrorTheta c₁ c₂ c₃ m ≤ dFact)
    (hFactLe : dFact ≤ dn) (hSolveLe : dSolve ≤ dn)
    (hmatrix : ∀ t,
      PartitionedLUComputationFirstOrder (Uround.unit t) c₁ c₂ c₃ m
        (maxEntryNorm hn (A t)) (maxEntryNorm hn (Lhat t))
        (maxEntryNorm hn (Uhat t)) (maxEntryNorm hn (DeltaFact t))
        (A t) (DeltaFact t) (Lhat t) (Uhat t))
    (hscalar : Higham13PartitionedLUScalarFamilyComputation
      Uround c₁ c₂ c₃ m
      (fun t => maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t))
      (fun t => maxEntryNorm hn (Uhat t))
      (fun t => maxEntryNorm hn (DeltaFact t)))
    (hSolveEquation : ∀ t,
      (A t + DeltaSolve t) * xhat t = b t)
    (hSolve : FamilyFirstOrderLe l Uround.unit
      (fun t => dSolve * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (DeltaSolve t))) :
    Higham13PartitionedLUFamilySpec Uround hn (blockErrorDelta m)
        (blockErrorTheta c₁ c₂ c₃ m) A DeltaFact Lhat Uhat ∧
      (∀ t, (A t + DeltaSolve t) * xhat t = b t) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => maxEntryNorm hn (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => maxEntryNorm hn (DeltaSolve t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => max (maxEntryNorm hn (DeltaFact t))
            (maxEntryNorm hn (DeltaSolve t))) := by
  have hFact := higham13_theorem13_5_eq13_7_family_from_computation
    Uround hn c₁ c₂ c₃ A DeltaFact Lhat Uhat hc₁ hc₂ hc₃ hmatrix hscalar
  have hFactScaled : FamilyFirstOrderLe l Uround.unit
      (fun t => dFact * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (DeltaFact t)) := by
    apply hFact.norm_bound.mono_leading
    intro t
    have hA0 := maxEntryNorm_nonneg hn (A t)
    have hL0 := maxEntryNorm_nonneg hn (Lhat t)
    have hU0 := maxEntryNorm_nonneg hn (Uhat t)
    have hu0 := Uround.unit_nonneg t
    have hδA := mul_le_mul_of_nonneg_right hDelta hA0
    have hθLU := mul_le_mul_of_nonneg_right hTheta (mul_nonneg hL0 hU0)
    nlinarith [mul_nonneg hu0
      (add_nonneg hA0 (mul_nonneg hL0 hU0))]
  have hAll := higham13_theorem13_6_eq13_16_family_from_factor_solve_bounds
    Uround dFact dSolve dn
      (fun t => maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t))
      (fun t => maxEntryNorm hn (Uhat t))
      (fun t => maxEntryNorm hn (DeltaFact t))
      (fun t => maxEntryNorm hn (DeltaSolve t))
      (fun t => maxEntryNorm_nonneg hn (A t))
      (fun t => maxEntryNorm_nonneg hn (Lhat t))
      (fun t => maxEntryNorm_nonneg hn (Uhat t))
      hFactLe hSolveLe hFactScaled hSolve
  exact ⟨hFact, hSolveEquation, hAll.1, hAll.2.1, hAll.2.2⟩

/-- Higham Theorem 13.6 / equation (13.16), Implementation 1, as a genuine
roundoff-family theorem with both computational halves derived.

The factor residual comes from the recursive partitioned-LU computation
certificate.  For every family index, the solve witnesses are selected from
the actual conventional flattened forward substitution and the actual
descending block back substitution.  Direct inequalities from the rounded
operations give one uniform family proof; no fixed-`u` `FirstOrderLe` proof
and no unrelated equation-(13.14) premise is lifted into the conclusion. -/
theorem
    higham13_theorem13_6_implementation1_family_from_partitioned_computation_and_conventional_recursive_solve
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (fp : ι → FPModel) (hfp : ∀ t, (fp t).u = Uround.unit t)
    {m r q : ℕ} (hm : 0 < m) (hr : 0 < r)
    (c₁ c₂ c₃ dFact dn : ℝ)
    (A DeltaFact : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (Lhat U : ι → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : ι → Fin (m * r) → ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : blockErrorDelta q ≤ dFact)
    (hθ : blockErrorTheta c₁ c₂ c₃ q ≤ dFact)
    (hdFact : dFact ≤ dn)
    (hdSolve : higham13DHSUniformSolveCoefficient dFact m r ≤ dn)
    (hFactComputation : ∀ t,
      PartitionedLUComputationFirstOrder
        (Uround.unit t) c₁ c₂ c₃ q
        (maxEntryNorm (Nat.mul_pos hm hr) (A t))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t))
        (A t) (DeltaFact t)
        (blockMatrixFlatFin (Lhat t)) (blockMatrixFlatFin (U t)))
    (hScalar : Higham13PartitionedLUScalarFamilyComputation
      Uround c₁ c₂ c₃ q
      (fun t => maxEntryNorm (Nat.mul_pos hm hr) (A t))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (Lhat t)))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (U t)))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t)))
    (hSmallProduct : ∀ t,
      (((m * r : ℕ) : ℝ) * Uround.unit t) ≤ 1 / 2)
    (hLdiag : ∀ t, ∀ i : Fin (m * r),
      blockMatrixFlatFin (Lhat t) i i ≠ 0)
    (hLower : ∀ t, ∀ i j : Fin (m * r), i.val < j.val →
      blockMatrixFlatFin (Lhat t) i j = 0)
    (hUUpper : ∀ t, ∀ i j : Fin m, j.val < i.val → U t i j = 0)
    (hDiag : ∀ t, ∀ i : Fin m, ∀ a : Fin r, U t i i a a ≠ 0)
    (hUpper : ∀ t, ∀ i : Fin m, ∀ a b' : Fin r,
      b'.val < a.val → U t i i a b' = 0) :
    ∃ (DeltaDiag : ι → Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaL : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : ι → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ t, ∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag t i) ≤
          (2 * (r : ℝ)) * Uround.unit t * maxEntryNorm hr (U t i i)) ∧
      (∀ t, ∀ i j : Fin (m * r),
        |DeltaL t i j| ≤ gamma (fp t) (m * r) *
          |blockMatrixFlatFin (Lhat t) i j|) ∧
      (∀ t, ∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec (Uround.unit t) (2 * (r : ℝ))
          (maxEntryNorm hr (U t i i)) (maxEntryNorm hr (DeltaDiag t i))
          (U t i i) (DeltaDiag t i)
          (dhsBlockBackConventionalSolution (fp t) (U t)
            (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)) i)
          (dhsBlockBackConventionalRHS (fp t) i (U t)
            (dhsBlockBackConventionalSolution (fp t) (U t)
              (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)))
            (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)))) ∧
      Higham13PartitionedLUFamilySpec Uround (Nat.mul_pos hm hr)
        (blockErrorDelta q) (blockErrorTheta c₁ c₂ c₃ q)
        A DeltaFact
        (fun t => blockMatrixFlatFin (Lhat t))
        (fun t => blockMatrixFlatFin (U t)) ∧
      (∀ t,
        (blockMatrixFlatFin (Lhat t) + DeltaL t) *
            blockMatrixRowsFlatFin
              (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)) =
          (fun i (_k : Fin 1) => b t i)) ∧
      (∀ t,
        (blockMatrixFlatFin (U t) + blockMatrixFlatFin (DeltaU t)) *
            blockMatrixRowsFlatFin
              (dhsBlockBackConventionalSolution (fp t) (U t)
                (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t))) =
          blockMatrixRowsFlatFin
            (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t))) ∧
      (∀ t,
        (A t +
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t))) *
            blockMatrixRowsFlatFin
              (dhsBlockBackConventionalSolution (fp t) (U t)
                (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t))) =
          (fun i (_k : Fin 1) => b t i)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (maxEntryNorm (Nat.mul_pos hm hr) (A t) +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)) *
              maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t))))
        (fun t => maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (maxEntryNorm (Nat.mul_pos hm hr) (A t) +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)) *
              maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t))))
        (fun t => maxEntryNorm (Nat.mul_pos hm hr)
          (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
            blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
            DeltaL t * blockMatrixFlatFin (DeltaU t))) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (maxEntryNorm (Nat.mul_pos hm hr) (A t) +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)) *
              maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t))))
        (fun t => max
          (maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t))
          (maxEntryNorm (Nat.mul_pos hm hr)
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t)))) := by
  classical
  let hn : 0 < m * r := Nat.mul_pos hm hr
  let Lflat : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
    fun t => blockMatrixFlatFin (Lhat t)
  let Uflat : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
    fun t => blockMatrixFlatFin (U t)
  let Y : ι → Fin m → Matrix (Fin r) (Fin 1) ℝ := fun t =>
    dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)
  let X : ι → Fin m → Matrix (Fin r) (Fin 1) ℝ := fun t =>
    dhsBlockBackConventionalSolution (fp t) (U t) (Y t)
  have hFactFamily := higham13_theorem13_5_eq13_7_family_from_computation
    Uround hn c₁ c₂ c₃ A DeltaFact Lflat Uflat
    hc₁ hc₂ hc₃ hFactComputation hScalar
  have hForwardWitness : ∀ t,
      ∃ Delta : Matrix (Fin (m * r)) (Fin (m * r)) ℝ,
        (∀ i j : Fin (m * r),
          |Delta i j| ≤ gamma (fp t) (m * r) * |Lflat t i j|) ∧
        DHSBlockForwardSubstitutionFirstOrderSpec
          (fp t).u (((m * r : ℕ) : ℝ) ^ 2)
          (maxEntryNorm hn (A t)) (maxEntryNorm hn (Lflat t))
          (maxEntryNorm hn (Uflat t))
          (maxEntryNorm hn (Delta * Uflat t))
          (Lflat t) Delta
          (fun i (_k : Fin 1) =>
            fl_forwardSub (fp t) (m * r) (Lflat t) (b t) i)
          (fun i (_k : Fin 1) => b t i) := by
    intro t
    have hγ : gammaValid (fp t) (m * r) := by
      unfold gammaValid
      have hs := hSmallProduct t
      rw [← hfp t] at hs
      linarith
    exact
      dhs_block_forward_substitution_firstOrder_from_conventional_forwardSub_single_rhs
        (fp t) hn (maxEntryNorm hn (A t)) (Lflat t) (Uflat t) (b t)
        (maxEntryNorm_nonneg hn (A t)) (hLdiag t) (hLower t) hγ
  choose DeltaL hDeltaL hForward using hForwardWitness
  have hBackWitness : ∀ t,
      ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
        (∀ i : Fin m,
          maxEntryNorm hr (DeltaDiag i) ≤
            (2 * (r : ℝ)) * (fp t).u * maxEntryNorm hr (U t i i)) ∧
        (∀ i : Fin m,
          DiagonalBlockSolveFirstOrderSpec (fp t).u (2 * (r : ℝ))
            (maxEntryNorm hr (U t i i)) (maxEntryNorm hr (DeltaDiag i))
            (U t i i) (DeltaDiag i) (X t i)
            (dhsBlockBackConventionalRHS (fp t) i (U t) (X t) (Y t))) ∧
        DHSBlockBackSubstitutionRowsFirstOrderSpec
          (fp t).u (higham13DHSUniformBackRowCoefficient m r)
          (maxEntryNorm hn (Uflat t))
          (higham13DHSUniformBackRowCoefficient m r * (fp t).u *
            maxEntryNorm hn (Uflat t))
          (Uflat t) (blockMatrixFlatFin DeltaU)
          (blockMatrixRowsFlatFin (X t)) (blockMatrixRowsFlatFin (Y t)) := by
    intro t
    have hSmallFp : (((m * r : ℕ) : ℝ) * (fp t).u) ≤ 1 / 2 := by
      simpa only [hfp t] using hSmallProduct t
    have hUTail : ∀ i : Fin m,
        maxEntryNormRect hr hn (dhsBlockBackUpperTailRowFlat i (U t i)) ≤
          maxEntryNorm hn (Uflat t) := by
      intro i
      simpa only [Uflat, hn] using
        maxEntryNorm_upperTailRowFlat_le_blockMatrixFlatFin hm hr (U t) i
    have hUii : ∀ i : Fin m,
        maxEntryNorm hr (U t i i) ≤ maxEntryNorm hn (Uflat t) := by
      intro i
      simpa only [Uflat, hn] using
        maxEntryNorm_diagonalBlock_le_blockMatrixFlatFin hm hr (U t) i
    simpa only [X, Y, Uflat, hn] using
      dhs_block_back_substitution_rows_linear_bound_from_conventional_recursive_block_solution
        (fp t) hm hr (maxEntryNorm hn (Uflat t)) (U t) (Y t)
        hSmallFp (hUUpper t) hUTail hUii (hDiag t) (hUpper t)
  choose DeltaDiag DeltaU hDeltaDiag hDiagonal hRows using hBackWitness
  have hForwardEquation : ∀ t,
      (Lflat t + DeltaL t) * blockMatrixRowsFlatFin (Y t) =
        (fun i (_k : Fin 1) => b t i) := by
    intro t
    have hYFlat : blockMatrixRowsFlatFin (Y t) =
        (fun i (_k : Fin 1) =>
          fl_forwardSub (fp t) (m * r) (Lflat t) (b t) i) := by
      simpa only [Y, Lflat] using
        dhsBlockForwardConventionalSolution_flat (fp t) (Lhat t) (b t)
    rw [hYFlat]
    exact (hForward t).equation
  have hBackEquation : ∀ t,
      (Uflat t + blockMatrixFlatFin (DeltaU t)) *
          blockMatrixRowsFlatFin (X t) = blockMatrixRowsFlatFin (Y t) := by
    intro t
    ext i k
    simpa [Matrix.mul_apply] using (hRows t).equation i k
  have hSolveEquation : ∀ t,
      (A t +
          (DeltaFact t + DeltaL t * Uflat t +
            Lflat t * blockMatrixFlatFin (DeltaU t) +
            DeltaL t * blockMatrixFlatFin (DeltaU t))) *
          blockMatrixRowsFlatFin (X t) =
        (fun i (_k : Fin 1) => b t i) := by
    intro t
    exact dhs_lu_solve_perturbation_identity
      (A t) (DeltaFact t) (Lflat t) (Uflat t) (DeltaL t)
      (blockMatrixFlatFin (DeltaU t)) (blockMatrixRowsFlatFin (X t))
      (fun i (_k : Fin 1) => b t i) (blockMatrixRowsFlatFin (Y t))
      (hFactFamily.equation t) (hForwardEquation t) (hBackEquation t)
  have hFactScaled : FamilyFirstOrderLe l Uround.unit
      (fun t => dFact * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)))
      (fun t => maxEntryNorm hn (DeltaFact t)) := by
    apply hFactFamily.norm_bound.mono_leading
    intro t
    have hA0 := maxEntryNorm_nonneg hn (A t)
    have hL0 := maxEntryNorm_nonneg hn (Lflat t)
    have hU0 := maxEntryNorm_nonneg hn (Uflat t)
    have hu0 := Uround.unit_nonneg t
    have hδA := mul_le_mul_of_nonneg_right hδ hA0
    have hθLU := mul_le_mul_of_nonneg_right hθ (mul_nonneg hL0 hU0)
    nlinarith [mul_nonneg hu0 (add_nonneg hA0 (mul_nonneg hL0 hU0))]
  have hDeltaLNorm : ∀ t,
      maxEntryNorm hn (DeltaL t) ≤
        (2 * (((m * r : ℕ) : ℝ) * Uround.unit t)) *
          maxEntryNorm hn (Lflat t) := by
    intro t
    have hSmallFp : (((m * r : ℕ) : ℝ) * (fp t).u) ≤ 1 / 2 := by
      simpa only [hfp t] using hSmallProduct t
    have hγ : gammaValid (fp t) (m * r) := by
      unfold gammaValid
      linarith
    have hγ0 : 0 ≤ gamma (fp t) (m * r) := gamma_nonneg (fp t) hγ
    have hγle := gamma_le_two_mul_n_u_of_nu_le_half
      (fp t) (m * r) hSmallFp
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    calc
      |DeltaL t i j| ≤ gamma (fp t) (m * r) * |Lflat t i j| :=
        hDeltaL t i j
      _ ≤ gamma (fp t) (m * r) * maxEntryNorm hn (Lflat t) :=
        mul_le_mul_of_nonneg_left
          (entry_le_maxEntryNorm hn (Lflat t) i j) hγ0
      _ ≤ (2 * (((m * r : ℕ) : ℝ) * (fp t).u)) *
          maxEntryNorm hn (Lflat t) :=
        mul_le_mul_of_nonneg_right hγle (maxEntryNorm_nonneg hn (Lflat t))
      _ = (2 * (((m * r : ℕ) : ℝ) * Uround.unit t)) *
          maxEntryNorm hn (Lflat t) := by rw [hfp t]
  have hForwardProduct : FamilyFirstOrderLe l Uround.unit
      (fun t => higham13DHSUniformForwardCoefficient m r * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)))
      (fun t => maxEntryNorm hn (DeltaL t * Uflat t)) := by
    apply FamilyFirstOrderLe.of_le
    intro t
    have hA0 := maxEntryNorm_nonneg hn (A t)
    have hL0 := maxEntryNorm_nonneg hn (Lflat t)
    have hU0 := maxEntryNorm_nonneg hn (Uflat t)
    calc
      maxEntryNorm hn (DeltaL t * Uflat t) ≤
          ((m * r : ℕ) : ℝ) * maxEntryNorm hn (DeltaL t) *
            maxEntryNorm hn (Uflat t) :=
        maxEntryNorm_matrix_mul_le_dim hn (DeltaL t) (Uflat t)
      _ ≤ ((m * r : ℕ) : ℝ) *
          ((2 * (((m * r : ℕ) : ℝ) * Uround.unit t)) *
            maxEntryNorm hn (Lflat t)) * maxEntryNorm hn (Uflat t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hDeltaLNorm t)
            (Nat.cast_nonneg (m * r))) hU0
      _ = higham13DHSUniformForwardCoefficient m r * Uround.unit t *
          (maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
        simp only [higham13DHSUniformForwardCoefficient]
        ring
      _ ≤ higham13DHSUniformForwardCoefficient m r * Uround.unit t *
          (maxEntryNorm hn (A t) +
            maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hA0)
          (mul_nonneg
            (by
              simp only [higham13DHSUniformForwardCoefficient]
              positivity)
            (Uround.unit_nonneg t))
  have hDeltaUNorm : ∀ t,
      maxEntryNorm hn (blockMatrixFlatFin (DeltaU t)) ≤
        higham13DHSUniformBackRowCoefficient m r * Uround.unit t *
          maxEntryNorm hn (Uflat t) := by
    intro t
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    simpa only [hfp t] using (hRows t).entry_bound i j
  have hBackProduct : FamilyFirstOrderLe l Uround.unit
      (fun t => higham13DHSUniformBackCoefficient m r * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)))
      (fun t => maxEntryNorm hn
        (Lflat t * blockMatrixFlatFin (DeltaU t))) := by
    apply FamilyFirstOrderLe.of_le
    intro t
    have hA0 := maxEntryNorm_nonneg hn (A t)
    have hL0 := maxEntryNorm_nonneg hn (Lflat t)
    have hU0 := maxEntryNorm_nonneg hn (Uflat t)
    calc
      maxEntryNorm hn (Lflat t * blockMatrixFlatFin (DeltaU t)) ≤
          ((m * r : ℕ) : ℝ) * maxEntryNorm hn (Lflat t) *
            maxEntryNorm hn (blockMatrixFlatFin (DeltaU t)) :=
        maxEntryNorm_matrix_mul_le_dim hn (Lflat t)
          (blockMatrixFlatFin (DeltaU t))
      _ ≤ ((m * r : ℕ) : ℝ) * maxEntryNorm hn (Lflat t) *
          (higham13DHSUniformBackRowCoefficient m r * Uround.unit t *
            maxEntryNorm hn (Uflat t)) := by
        exact mul_le_mul_of_nonneg_left (hDeltaUNorm t)
          (mul_nonneg (Nat.cast_nonneg (m * r)) hL0)
      _ = higham13DHSUniformBackCoefficient m r * Uround.unit t *
          (maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
        simp only [higham13DHSUniformBackCoefficient]
        ring
      _ ≤ higham13DHSUniformBackCoefficient m r * Uround.unit t *
          (maxEntryNorm hn (A t) +
            maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hA0)
          (mul_nonneg
            (by
              simp only [higham13DHSUniformBackCoefficient,
                higham13DHSUniformBackRowCoefficient]
              positivity)
            (Uround.unit_nonneg t))
  let crossCoefficient : ℝ :=
    2 * (((m * r : ℕ) : ℝ) ^ 2) *
      higham13DHSUniformBackRowCoefficient m r
  have hCrossCoefficient0 : 0 ≤ crossCoefficient := by
    dsimp only [crossCoefficient, higham13DHSUniformBackRowCoefficient]
    positivity
  have hCrossPoint : ∀ t,
      maxEntryNorm hn (DeltaL t * blockMatrixFlatFin (DeltaU t)) ≤
        (crossCoefficient * Uround.unit t ^ 2) *
          (maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
    intro t
    have hU0 := maxEntryNorm_nonneg hn (Uflat t)
    have hTwoNu0 :
        0 ≤ 2 * (((m * r : ℕ) : ℝ) * Uround.unit t) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg (m * r)) (Uround.unit_nonneg t))
    calc
      maxEntryNorm hn (DeltaL t * blockMatrixFlatFin (DeltaU t)) ≤
          ((m * r : ℕ) : ℝ) * maxEntryNorm hn (DeltaL t) *
            maxEntryNorm hn (blockMatrixFlatFin (DeltaU t)) :=
        maxEntryNorm_matrix_mul_le_dim hn (DeltaL t)
          (blockMatrixFlatFin (DeltaU t))
      _ ≤ ((m * r : ℕ) : ℝ) *
          ((2 * (((m * r : ℕ) : ℝ) * Uround.unit t)) *
            maxEntryNorm hn (Lflat t)) *
          (higham13DHSUniformBackRowCoefficient m r * Uround.unit t *
            maxEntryNorm hn (Uflat t)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hDeltaLNorm t)
            (Nat.cast_nonneg (m * r)))
          (hDeltaUNorm t)
          (maxEntryNorm_nonneg hn (blockMatrixFlatFin (DeltaU t)))
          (mul_nonneg (Nat.cast_nonneg (m * r))
            (mul_nonneg hTwoNu0 (maxEntryNorm_nonneg hn (Lflat t))))
      _ = (crossCoefficient * Uround.unit t ^ 2) *
          (maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) := by
        dsimp only [crossCoefficient]
        ring
  have hCrossBase : FamilyFirstOrderLe l Uround.unit
      (fun _t => 0) (fun t => crossCoefficient * Uround.unit t ^ 2) := by
    apply FamilyFirstOrderLe.of_uniform_quadratic hCrossCoefficient0
    intro t
    simp
  have hLUO : ScalarFamilyIsBigOOne l
      (fun t => maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)) :=
    hFactFamily.lower_norm_isBigO_one.mul hFactFamily.upper_norm_isBigO_one
  have hCross : FamilyFirstOrderLe l Uround.unit (fun _t => 0)
      (fun t => maxEntryNorm hn
        (DeltaL t * blockMatrixFlatFin (DeltaU t))) := by
    have h := hCrossBase.mul_bounded
      (fun t => mul_nonneg (maxEntryNorm_nonneg hn (Lflat t))
        (maxEntryNorm_nonneg hn (Uflat t))) hLUO hCrossPoint
    simpa only [zero_mul] using h
  let normSolve : ι → ℝ := fun t => maxEntryNorm hn
    (DeltaFact t + DeltaL t * Uflat t +
      Lflat t * blockMatrixFlatFin (DeltaU t) +
      DeltaL t * blockMatrixFlatFin (DeltaU t))
  have hTotal : ∀ t, normSolve t ≤
      maxEntryNorm hn (DeltaFact t) + maxEntryNorm hn (DeltaL t * Uflat t) +
        maxEntryNorm hn (Lflat t * blockMatrixFlatFin (DeltaU t)) +
        maxEntryNorm hn (DeltaL t * blockMatrixFlatFin (DeltaU t)) := by
    intro t
    simpa only [normSolve] using
      maxEntryNorm_four_add_le hn (DeltaFact t) (DeltaL t * Uflat t)
        (Lflat t * blockMatrixFlatFin (DeltaU t))
        (DeltaL t * blockMatrixFlatFin (DeltaU t))
  have hSolveScaled : FamilyFirstOrderLe l Uround.unit
      (fun t => higham13DHSUniformSolveCoefficient dFact m r * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lflat t) * maxEntryNorm hn (Uflat t)))
      normSolve := by
    have h12 := FamilyFirstOrderLe.add hFactScaled hForwardProduct
      (fun _t => le_rfl)
    have h123 := FamilyFirstOrderLe.add h12 hBackProduct
      (fun _t => le_rfl)
    have hAll := FamilyFirstOrderLe.add h123 hCross hTotal
    convert hAll using 1
    funext t
    simp only [higham13DHSUniformSolveCoefficient]
    ring
  have hAll := higham13_theorem13_6_eq13_16_family_from_factor_solve_bounds
    Uround dFact (higham13DHSUniformSolveCoefficient dFact m r) dn
    (fun t => maxEntryNorm hn (A t))
    (fun t => maxEntryNorm hn (Lflat t))
    (fun t => maxEntryNorm hn (Uflat t))
    (fun t => maxEntryNorm hn (DeltaFact t)) normSolve
    (fun t => maxEntryNorm_nonneg hn (A t))
    (fun t => maxEntryNorm_nonneg hn (Lflat t))
    (fun t => maxEntryNorm_nonneg hn (Uflat t))
    hdFact hdSolve hFactScaled hSolveScaled
  refine ⟨DeltaDiag, DeltaL, DeltaU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i
    simpa only [hfp t] using hDeltaDiag t i
  · exact hDeltaL
  · intro t i
    simpa only [hfp t, X, Y] using hDiagonal t i
  · simpa only [Lflat, Uflat, hn] using hFactFamily
  · simpa only [Lflat, Y] using hForwardEquation
  · simpa only [Uflat, X, Y] using hBackEquation
  · simpa only [Lflat, Uflat, X, Y] using hSolveEquation
  · simpa only [Lflat, Uflat, hn] using hAll.1
  · simpa only [normSolve, Lflat, Uflat, hn] using hAll.2.1
  · simpa only [normSolve, Lflat, Uflat, hn] using hAll.2.2

/-- Higham Theorem 13.6 / equation (13.16), Implementation 1, with both the
partitioned factorization and conventional solve paths operation-derived.

The scalar norm occurring in the result is the actual max-entry norm of `A`;
the factor norms in the recursive computation certificate and conclusion are
likewise the actual norms of the flattened computed factors. -/
theorem
    higham13_theorem13_6_implementation1_from_partitioned_computation_and_conventional_recursive_solve
    {m r q : ℕ} {s : Type*}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (c₁ c₂ c₃ dFact dn : ℝ)
    (A DeltaFact : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ)
    (c₄ normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s (Fin r) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : blockErrorDelta q ≤ dFact)
    (hθ : blockErrorTheta c₁ c₂ c₃ q ≤ dFact)
    (hdFact : dFact ≤ dn)
    (hdSolve : dFact + (((m * r : ℕ) : ℝ) ^ 2) +
      (((m * r : ℕ) : ℝ) *
        ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
          2 * (r : ℝ))) ≤ dn)
    (hFactComputation : PartitionedLUComputationFirstOrder
      fp.u c₁ c₂ c₃ q
      (maxEntryNorm (Nat.mul_pos hm hr) A)
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat))
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U))
      (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact)
      A DeltaFact (blockMatrixFlatFin Lhat) (blockMatrixFlatFin U))
    (hStep2 : BlockSolveFirstOrderSpec
      fp.u c₄ normLhat21 normA11 normE21 Lhat21 A21 E21 A11)
    (hLdiag : ∀ i : Fin (m * r), blockMatrixFlatFin Lhat i i ≠ 0)
    (hLower : ∀ i j : Fin (m * r), i.val < j.val →
      blockMatrixFlatFin Lhat i j = 0)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaL : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * maxEntryNorm hr (U i i)) ∧
      (∀ i j : Fin (m * r),
        |DeltaL i j| ≤ gamma fp (m * r) *
          |blockMatrixFlatFin Lhat i j|) ∧
      (blockMatrixFlatFin Lhat * blockMatrixFlatFin U = A + DeltaFact) ∧
      ((A + (DeltaFact + DeltaL * blockMatrixFlatFin U +
          blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
          DeltaL * blockMatrixFlatFin DeltaU)) *
          blockMatrixRowsFlatFin
            (dhsBlockBackConventionalSolution fp U
              (dhsBlockForwardConventionalSolution fp Lhat b)) =
        (fun i (_k : Fin 1) => b i)) ∧
      ((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound fp.u c₄ normLhat21 normA11 normE21) ∧
        (∀ i : Fin m,
          (U i i + DeltaDiag i) *
              dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b) i =
            dhsBlockBackConventionalRHS fp i U
              (dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b))
              (dhsBlockForwardConventionalSolution fp Lhat b) ∧
          DiagonalBlockSolveFirstOrderBound fp.u (2 * (r : ℝ))
            (maxEntryNorm hr (U i i))
            (maxEntryNorm hr (DeltaDiag i)))) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr)
          (DeltaFact + DeltaL * blockMatrixFlatFin U +
            blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
            DeltaL * blockMatrixFlatFin DeltaU)) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (max (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact)
          (maxEntryNorm (Nat.mul_pos hm hr)
            (DeltaFact + DeltaL * blockMatrixFlatFin U +
              blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
              DeltaL * blockMatrixFlatFin DeltaU))) := by
  have hFactSpec :=
    hFactComputation.to_spec fp.u_nonneg hc₁ hc₂ hc₃
  exact
    higham13_theorem13_6_implementation1_from_partitioned_factorization_and_conventional_recursive_solve
      fp hm hr (blockErrorDelta q) (blockErrorTheta c₁ c₂ c₃ q)
      dFact dn (maxEntryNorm (Nat.mul_pos hm hr) A)
      A DeltaFact Lhat U b c₄ normLhat21 normA11 normE21
      Lhat21 A21 E21 A11 hSmallProduct
      (maxEntryNorm_nonneg (Nat.mul_pos hm hr) A)
      hδ hθ hdFact hdSolve hFactSpec hStep2 hLdiag hLower
      hUUpper hDiag hUpper

end NumStability
