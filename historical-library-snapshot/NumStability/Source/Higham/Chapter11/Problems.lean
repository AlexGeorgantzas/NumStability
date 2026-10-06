import NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter11.Section01.Basic

/-!
# Higham Chapter 11: Problems

Canonical owner materialized from the reviewed Chapter 11 route contract.
-/

namespace NumStability

open scoped BigOperators

/-! ## Problems -/

/-- **Problem 11.2**, inertia formula for block diagonal `D`: each 2 by 2
indefinite block contributes one positive and one negative eigenvalue. -/
def higham11_problem_11_2_inertiaFormula
    (pPlus pMinus pZero q iPlus iMinus iZero : ℕ) : Prop :=
  iPlus = pPlus + q ∧ iMinus = pMinus + q ∧ iZero = pZero

/-- **Problem 11.3**, the simplified 2 by 2 Bunch-Kaufman decision tree. -/
def higham11_problem_11_3_twoByTwoPartialPivoting
    (α a11 a22 a21 : ℝ) (s : PivotSize) : Prop :=
  (|a11| ≥ α * |a21| ∧ s = PivotSize.one) ∨
  (|a22| ≥ α * |a21| ∧ s = PivotSize.one) ∨
  (|a11| < α * |a21| ∧ |a22| < α * |a21| ∧ s = PivotSize.two)

/-- **Problem 11.4**, SPD inputs to Bunch-Kaufman partial pivoting use only
positive 1 by 1 pivots, possibly after symmetric interchanges. -/
def higham11_problem_11_4_spdPartialPivotingOutcome
    (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≠ j → D i j = 0) ∧
  (∀ i : Fin n, 0 < D i i)

/-- **Problem 11.9**, symmetric quasidefinite block matrix source predicate. -/
def higham11_problem_11_9_isSymmetricQuasidefinite
    (n m : ℕ)
    (H : Fin n → Fin n → ℝ)
    (G : Fin m → Fin m → ℝ) : Prop :=
  IsSymPosDef n H ∧ IsSymPosDef m G

/-! ## Problem proof-completion lemmas -/

/-- **Problem 11.1**, determinant of the principal `2 x 2` block on rows
and columns `i,j`. -/
def higham11_problem_11_1_principalTwoByTwoDet {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  A i i * A j j - A i j * A j i

/-- **Problem 11.1**: if every `1 x 1` and `2 x 2` principal pivot block of
a symmetric matrix is singular, then the matrix is zero.  This is the exact
Appendix A argument used to justify the existence of a nonsingular pivot block
for any nonzero symmetric matrix. -/
theorem higham11_problem_11_1_zero_of_symmetric_singular_principal_pivots
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hSym : ∀ i j : Fin n, A i j = A j i)
    (hOne : ∀ i : Fin n, A i i = 0)
    (hTwo : ∀ i j : Fin n,
      higham11_problem_11_1_principalTwoByTwoDet A i j = 0) :
    ∀ i j : Fin n, A i j = 0 := by
  intro i j
  by_cases hij : i = j
  · subst i
    exact hOne j
  · have hdet :
        -(A i j * A i j) = 0 := by
      simpa [higham11_problem_11_1_principalTwoByTwoDet, hOne i, hOne j,
        hSym j i] using hTwo i j
    have hsq : (A i j) ^ 2 = 0 := by
      nlinarith
    exact sq_eq_zero_iff.mp hsq

/-- **Problem 11.2**, exact `2 x 2` symmetric pivot block. -/
def higham11_problem_11_2_twoByTwoPivot (a b c : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then a
    else if i.val = 0 ∧ j.val = 1 then b
    else if i.val = 1 ∧ j.val = 0 then b
    else c

/-- **Problem 11.2**, overflow-avoiding inverse formula from Appendix A:
`E^{-1} = 1/(b*((a/b)*(c/b)-1)) * [[c/b,-1],[-1,a/b]]`. -/
noncomputable def higham11_problem_11_2_twoByTwoPivotScaledInverse
    (a b c : ℝ) : Fin 2 → Fin 2 → ℝ :=
  let d : ℝ := b * ((a / b) * (c / b) - 1)
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then (c / b) / d
    else if i.val = 0 ∧ j.val = 1 then (-1) / d
    else if i.val = 1 ∧ j.val = 0 then (-1) / d
    else (a / b) / d

/-- **Problem 11.2**, proved inverse certificate for the Appendix A scaled
`2 x 2` pivot inverse formula. -/
theorem higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec
    (a b c : ℝ) (hb : b ≠ 0)
    (hd : b * ((a / b) * (c / b) - 1) ≠ 0) :
    higham11_2_NonsingularPivotBlock 2
      (higham11_problem_11_2_twoByTwoPivot a b c)
      (higham11_problem_11_2_twoByTwoPivotScaledInverse a b c) := by
  have hd_eq :
      b * ((a / b) * (c / b) - 1) = (a * c - b ^ 2) / b := by
    field_simp [hb]
  have hdet_ne : a * c - b ^ 2 ≠ 0 := by
    intro hzero
    apply hd
    rw [hd_eq, hzero, zero_div]
  have hdet_ne_comm : c * a - b ^ 2 ≠ 0 := by
    intro hzero
    apply hdet_ne
    rwa [mul_comm c a] at hzero
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [higham11_problem_11_2_twoByTwoPivot,
      higham11_problem_11_2_twoByTwoPivotScaledInverse, Fin.sum_univ_two] <;>
    field_simp [hb, hdet_ne, hdet_ne_comm] <;>
    ring_nf

/-- **Problem 11.2**, determinant negativity from the common Appendix A
pivot-growth estimate `det(E) <= (alpha^2 - 1) * beta^2`, with
`alpha^2 < 1` and nonzero pivot scale `beta`. -/
theorem higham11_problem_11_2_det_negative_of_pivot_bound
    (α β detE : ℝ) (hα : α ^ 2 < 1) (hβ : β ≠ 0)
    (hdet : detE ≤ (α ^ 2 - 1) * β ^ 2) :
    detE < 0 := by
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hcoef : α ^ 2 - 1 < 0 := by linarith
  have hrhs : (α ^ 2 - 1) * β ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hcoef hβsq
  exact lt_of_le_of_lt hdet hrhs

/-- **Problem 11.4**, local SPD obstruction: a real SPD matrix cannot have a
`2 x 2` principal pivot block whose determinant is negative. -/
theorem higham11_problem_11_4_spd_no_negative_twoByTwo_principal_det
    {n : ℕ} (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    {i j : Fin n} (hij : i ≠ j) :
    ¬ A i i * A j j - A i j ^ 2 < 0 := by
  have hpos := higham10_problem_10_1_two_by_two_minor_pos A hSPD hij
  linarith

/-- **Problem 11.7**, core algebra for the modified Bunch-Kaufman test.
If the `2 x 2` principal block is positive definite, the modified
`omega_r = ||A(:,r)||_inf` quantity dominates `a_rr`, and `alpha <= 1`, then
the second pivot test `|a_11| omega_r >= alpha * omega_1^2` is passed. -/
theorem higham11_problem_11_7_modifiedOmega_second_test_from_spd_minor
    (α a11 arr ar1 ωr : ℝ)
    (ha11 : 0 < a11)
    (hminor : 0 < a11 * arr - ar1 ^ 2)
    (harr_le : arr ≤ ωr)
    (hα : α ≤ 1) :
    α * ar1 ^ 2 ≤ |a11| * ωr := by
  have har_sq_nonneg : 0 ≤ ar1 ^ 2 := sq_nonneg ar1
  have har_sq_lt : ar1 ^ 2 < a11 * arr := by linarith
  have harr_to_ω : a11 * arr ≤ a11 * ωr :=
    mul_le_mul_of_nonneg_left harr_le (le_of_lt ha11)
  have har_sq_le_ω : ar1 ^ 2 ≤ a11 * ωr :=
    le_trans (le_of_lt har_sq_lt) harr_to_ω
  have hα_sq : α * ar1 ^ 2 ≤ ar1 ^ 2 :=
    calc
      α * ar1 ^ 2 ≤ 1 * ar1 ^ 2 :=
        mul_le_mul_of_nonneg_right hα har_sq_nonneg
      _ = ar1 ^ 2 := by ring
  rw [abs_of_pos ha11]
  exact le_trans hα_sq har_sq_le_ω

/-- **Problem 11.8**, the permuted matrix obtained from the example (11.6)
under complete pivoting or rook pivoting. -/
noncomputable def higham11_problem_11_8_rookCompleteExampleA
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else if i.val = 1 ∧ j.val = 2 then ε
    else if i.val = 2 ∧ j.val = 1 then ε
    else if i.val = 2 ∧ j.val = 2 then 1
    else 0

/-- **Problem 11.8**, the lower triangular factor produced for the
complete/rook-pivoting factorization of the example (11.6). -/
noncomputable def higham11_problem_11_8_rookCompleteExampleL
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = j.val then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else if i.val = 2 ∧ j.val = 1 then -ε
    else 0

/-- **Problem 11.8**, the diagonal factor
`diag(1, -1, 1 + eps^2)`. -/
noncomputable def higham11_problem_11_8_rookCompleteExampleD
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 1 ∧ j.val = 1 then -1
    else if i.val = 2 ∧ j.val = 2 then 1 + ε ^ 2
    else 0

/-- **Problem 11.8**, exact algebraic factorization produced by complete
pivoting and rook pivoting for the matrix in (11.6). -/
theorem higham11_problem_11_8_rookCompleteExample_factorization
    (ε : ℝ) :
    ∀ i j : Fin 3,
      ∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
        higham11_problem_11_8_rookCompleteExampleL ε i k₁ *
          higham11_problem_11_8_rookCompleteExampleD ε k₁ k₂ *
          higham11_problem_11_8_rookCompleteExampleL ε j k₂ =
      higham11_problem_11_8_rookCompleteExampleA ε i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham11_problem_11_8_rookCompleteExampleA,
      higham11_problem_11_8_rookCompleteExampleL,
      higham11_problem_11_8_rookCompleteExampleD]
  ring

/-- **Problem 11.9(a)**, kernel-trivial form of nonsingularity for a
symmetric quasidefinite block matrix
`[[H, B^T], [B, -G]]` with `H` and `G` SPD.  This is the Appendix A argument
written directly on the block equations, avoiding a separate determinant API:
multiply the two block rows by `u` and `v`, cancel the `B` cross terms, and use
positive definiteness of `H` and `G`. -/
theorem higham11_problem_11_9_quasidefinite_kernel_trivial
    {n m : ℕ} (H : Fin n → Fin n → ℝ)
    (B : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ)
    (hH : IsSymPosDef n H) (hG : IsSymPosDef m G)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (h₁ : ∀ i : Fin n,
      (∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k) = 0)
    (h₂ : ∀ k : Fin m,
      (∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l) = 0) :
    (∀ i : Fin n, u i = 0) ∧ (∀ k : Fin m, v k = 0) := by
  let qH : ℝ := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j
  let qG : ℝ := ∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l
  let cross₁ : ℝ := ∑ i : Fin n, ∑ k : Fin m, u i * B k i * v k
  let cross₂ : ℝ := ∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i
  have hrow_zero :
      ∑ i : Fin n,
        u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k)) = 0 := by
    calc
      ∑ i : Fin n,
          u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k))
          = ∑ i : Fin n, u i * 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h₁ i]
      _ = 0 := by simp
  have hcol_zero :
      ∑ k : Fin m,
        v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l)) = 0 := by
    calc
      ∑ k : Fin m,
          v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l))
          = ∑ k : Fin m, v k * 0 := by
            apply Finset.sum_congr rfl
            intro k _
            rw [h₂ k]
      _ = 0 := by simp
  have hrow_expand :
      ∑ i : Fin n,
        u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k)) =
      qH + cross₁ := by
    have hHsum :
        ∑ i : Fin n, u i * (∑ j : Fin n, H i j * u j) = qH := by
      dsimp [qH]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hBsum :
        ∑ i : Fin n, u i * (∑ k : Fin m, B k i * v k) = cross₁ := by
      dsimp [cross₁]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hHsum, hBsum]
  have hcol_expand :
      ∑ k : Fin m,
        v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l)) =
      cross₂ - qG := by
    have hBsum :
        ∑ k : Fin m, v k * (∑ i : Fin n, B k i * u i) = cross₂ := by
      dsimp [cross₂]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hGsum :
        ∑ k : Fin m, v k * (∑ l : Fin m, G k l * v l) = qG := by
      dsimp [qG]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hBsum, hGsum]
  have hcross : cross₂ = cross₁ := by
    dsimp [cross₁, cross₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hrow_q : qH + cross₁ = 0 := by
    rw [← hrow_expand]
    exact hrow_zero
  have hcol_q : cross₁ - qG = 0 := by
    rw [← hcross, ← hcol_expand]
    exact hcol_zero
  have hqsum : qH + qG = 0 := by
    nlinarith
  have hqH_nonneg : 0 ≤ qH := by
    by_cases hu : ∃ i : Fin n, u i ≠ 0
    · exact le_of_lt (hH.2 u hu)
    · push_neg at hu
      simp [qH, hu]
  have hqG_nonneg : 0 ≤ qG := by
    by_cases hv : ∃ k : Fin m, v k ≠ 0
    · exact le_of_lt (hG.2 v hv)
    · push_neg at hv
      simp [qG, hv]
  have hqH_zero : qH = 0 := by nlinarith
  have hqG_zero : qG = 0 := by nlinarith
  constructor
  · by_contra hu
    push_neg at hu
    have hpos := hH.2 u hu
    nlinarith
  · by_contra hv
    push_neg at hv
    have hpos := hG.2 v hv
    nlinarith

/-- **Problem 11.9(c)**, concrete block-quadratic form for
`A S = [[H, -B^T], [B, G]]`.  The off-diagonal block terms cancel, leaving the
sum of the SPD quadratic forms for `H` and `G`. -/
theorem higham11_problem_11_9_signed_block_quadratic_pos
    {n m : ℕ} (H : Fin n → Fin n → ℝ)
    (B : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ)
    (hH : IsSymPosDef n H) (hG : IsSymPosDef m G)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (hnz : (∃ i : Fin n, u i ≠ 0) ∨ (∃ k : Fin m, v k ≠ 0)) :
    0 <
      (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) +
      (∑ i : Fin n, ∑ k : Fin m, u i * (-B k i) * v k) +
      (∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i) +
      (∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l) := by
  let qH : ℝ := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j
  let qG : ℝ := ∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l
  let cross₁ : ℝ := ∑ i : Fin n, ∑ k : Fin m, u i * B k i * v k
  let cross₂ : ℝ := ∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i
  have hcross : cross₂ = cross₁ := by
    dsimp [cross₁, cross₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hneg :
      (∑ i : Fin n, ∑ k : Fin m, u i * (-B k i) * v k) = -cross₁ := by
    dsimp [cross₁]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpos_cross :
      (∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i) = cross₂ := by
    rfl
  have hqH_nonneg : 0 ≤ qH := by
    by_cases hu : ∃ i : Fin n, u i ≠ 0
    · exact le_of_lt (hH.2 u hu)
    · push_neg at hu
      simp [qH, hu]
  have hqG_nonneg : 0 ≤ qG := by
    by_cases hv : ∃ k : Fin m, v k ≠ 0
    · exact le_of_lt (hG.2 v hv)
    · push_neg at hv
      simp [qG, hv]
  have hq_pos : 0 < qH + qG := by
    rcases hnz with hu | hv
    · have hpos := hH.2 u hu
      nlinarith
    · have hpos := hG.2 v hv
      nlinarith
  rw [show
      (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) = qH by rfl]
  rw [show
      (∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l) = qG by rfl]
  rw [hneg, hpos_cross, hcross]
  nlinarith

/-- **Problem 11.9(c)** reuse of Chapter 10: a matrix whose symmetric part is
SPD is nonsymmetric positive definite.  The block computation
`(AS + (AS)^T)/2 = diag(H,G)` is the remaining block-layout step. -/
theorem higham11_problem_11_9_nonsymPosDef_of_symPartSPD {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n (symmetricPart n A)) :
    IsNonsymPosDef n A :=
  (nonsymPosDef_iff_symPartSPD n A).mpr hSPD


end NumStability
