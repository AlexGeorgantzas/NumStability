import NumStability.Algorithms.HighamChapter10

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-!
# Higham Theorem 10.8: literal-source audit and corrected domain

The printed theorem on p. 201 defines

`epsilon = frobNorm DeltaA / norm_p A`, for `p = 2, F`,

but assumes only `opNorm2 (A^-1 DeltaA) < 1`.  Those hypotheses do not imply
`kappa_2(A) * epsilon < 1`, although the displayed rational estimate has
denominator `1 - kappa_2(A) * epsilon`.  The two-dimensional scalar-diagonal
example below satisfies every printed existence hypothesis while making that
denominator negative.  Consequently the printed normwise conclusion is false
as stated already for the faithful `p = 2` specialization.

This is a source discrepancy, not a missing Lean bridge.  The declarations
below keep the literal formula visible and prove the counterexample without
postulating a failed Cholesky run or a candidate factor perturbation.
-/

/-- The condition number occurring in the printed Theorem 10.8 display. -/
noncomputable def higham10_8_sourceKappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  opNorm2 A * opNorm2 Ainv

/-- The printed relative perturbation for a supplied `p`-norm value of `A`.
The numerator is Frobenius for both `p = 2` and `p = F`. -/
noncomputable def higham10_8_sourceEpsilon {n : ℕ}
    (A_p : ℝ) (DeltaA : Fin n → Fin n → ℝ) : ℝ :=
  frobNorm DeltaA / A_p

/-- The literal rational right-hand side of the normwise Theorem 10.8
estimate. -/
noncomputable def higham10_8_sourceNormwiseRHS (kappa epsilon : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * (kappa * epsilon) /
    (1 - kappa * epsilon)

/-- The SPD diagonal matrix `diag(1, 1/4)` used in the literal-source
counterexample.  Its condition number is four. -/
def higham10_8_counterA : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then if i.val = 0 then 1 else 1 / 4 else 0

/-- The exact Cholesky factor `diag(1, 1/2)`. -/
def higham10_8_counterR : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then if i.val = 0 then 1 else 1 / 2 else 0

/-- The exact inverse `diag(1, 4)`. -/
def higham10_8_counterAinv : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then if i.val = 0 then 1 else 4 else 0

/-- The symmetric perturbation `diag(1/2, 0)`.  It satisfies
`||A^-1 DeltaA||_2 = 1/2 < 1`, while
`kappa_2(A) * ||DeltaA||_2 / ||A||_2 = 2 > 1`. -/
def higham10_8_counterDeltaA : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j ∧ i.val = 0 then 1 / 2 else 0

/-- The perturbed matrix `A + DeltaA`, kept in literal source form. -/
def higham10_8_counterAplus : Fin 2 → Fin 2 → ℝ :=
  fun i j => higham10_8_counterA i j + higham10_8_counterDeltaA i j

/-- The (unique) positive-diagonal Cholesky factor of the perturbed matrix. -/
def higham10_8_counterRhat : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then
    if i.val = 0 then Real.sqrt (3 / 2 : ℝ) else 1 / 2
  else 0

theorem higham10_8_counterA_isSymPosDef :
    IsSymPosDef 2 higham10_8_counterA := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [higham10_8_counterA]
  · intro x hx
    obtain ⟨i, hi⟩ := hx
    have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    simp only [Fin.sum_univ_two, higham10_8_counterA]
    rcases hcoords with h0 | h1
    · have hs0 : 0 < x 0 ^ 2 := sq_pos_of_ne_zero h0
      have hs1 : 0 ≤ x 1 ^ 2 := sq_nonneg (x 1)
      norm_num
      nlinarith
    · have hs0 : 0 ≤ x 0 ^ 2 := sq_nonneg (x 0)
      have hs1 : 0 < x 1 ^ 2 := sq_pos_of_ne_zero h1
      norm_num
      nlinarith

theorem higham10_8_counterR_cholesky :
    CholeskyFactSpec 2 higham10_8_counterA higham10_8_counterR := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    have hij : i ≠ j := by
      intro h
      subst j
      omega
    simp [higham10_8_counterR, hij]
  · intro i
    fin_cases i <;> norm_num [higham10_8_counterR]
  · intro i j
    fin_cases i <;> fin_cases j
    · norm_num [Fin.sum_univ_two, higham10_8_counterR,
        higham10_8_counterA]
    · simp [Fin.sum_univ_two, higham10_8_counterR,
        higham10_8_counterA]
    · simp [Fin.sum_univ_two, higham10_8_counterR,
        higham10_8_counterA]
    · norm_num [Fin.sum_univ_two, higham10_8_counterR,
        higham10_8_counterA]

theorem higham10_8_counterDeltaA_symmetric :
    ∀ i j : Fin 2,
      higham10_8_counterDeltaA i j = higham10_8_counterDeltaA j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [higham10_8_counterDeltaA]

theorem higham10_8_counterAplus_eq :
    higham10_8_counterAplus =
      fun i j : Fin 2 =>
        if i = j then if i.val = 0 then (3 / 2 : ℝ) else 1 / 4 else 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham10_8_counterAplus, higham10_8_counterA,
      higham10_8_counterDeltaA]

theorem higham10_8_counterRhat_cholesky :
    CholeskyFactSpec 2 higham10_8_counterAplus higham10_8_counterRhat := by
  have hsqrt : 0 < Real.sqrt (3 / 2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsquare : Real.sqrt (3 / 2 : ℝ) * Real.sqrt (3 / 2 : ℝ) =
      3 / 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    have hij : i ≠ j := by
      intro h
      subst j
      omega
    simp [higham10_8_counterRhat, hij]
  · intro i
    fin_cases i <;> norm_num [higham10_8_counterRhat, hsqrt]
  · intro i j
    rw [higham10_8_counterAplus_eq]
    fin_cases i <;> fin_cases j
    · simpa [Fin.sum_univ_two, higham10_8_counterRhat] using hsquare
    · simp [Fin.sum_univ_two, higham10_8_counterRhat]
    · simp [Fin.sum_univ_two, higham10_8_counterRhat]
    · norm_num [Fin.sum_univ_two, higham10_8_counterRhat]

/-- The displayed perturbed factor is not merely a witness: it is the unique
positive-diagonal Cholesky factor required by the source. -/
theorem higham10_8_counterRhat_unique
    (S : Fin 2 → Fin 2 → ℝ)
    (hS : CholeskyFactSpec 2 higham10_8_counterAplus S) :
    ∀ i j : Fin 2, S i j = higham10_8_counterRhat i j :=
  higham10_1_cholesky_uniqueness 2 higham10_8_counterAplus S
    higham10_8_counterRhat hS higham10_8_counterRhat_cholesky

theorem higham10_8_counterA_inverse :
    IsLeftInverse 2 higham10_8_counterA higham10_8_counterAinv ∧
      IsRightInverse 2 higham10_8_counterA higham10_8_counterAinv := by
  constructor <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [matMul, Fin.sum_univ_two, higham10_8_counterA,
        higham10_8_counterAinv, idMatrix] <;> rfl

theorem higham10_8_counterA_opNorm2 :
    opNorm2 higham10_8_counterA = 1 := by
  unfold opNorm2
  rw [show higham10_8_counterA =
      Matrix.diagonal (fun i : Fin 2 => if i.val = 0 then (1 : ℝ) else 1 / 4) by
        ext i j
        simp [higham10_8_counterA, Matrix.diagonal_apply]]
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  have hsup : Finset.univ.sup
      (fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 1 / 4‖₊) = 1 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _hi
      fin_cases i
      · norm_num
      · norm_num
        exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ 1)
    · simpa using Finset.le_sup
        (s := Finset.univ)
        (f := fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 1 / 4‖₊)
        (Finset.mem_univ (0 : Fin 2))
  rw [hsup]
  norm_num

theorem higham10_8_counterR_opNorm2 :
    opNorm2 higham10_8_counterR = 1 := by
  unfold opNorm2
  rw [show higham10_8_counterR =
      Matrix.diagonal (fun i : Fin 2 => if i.val = 0 then (1 : ℝ) else 1 / 2) by
        ext i j
        simp [higham10_8_counterR, Matrix.diagonal_apply]]
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  have hsup : Finset.univ.sup
      (fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 1 / 2‖₊) = 1 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _hi
      fin_cases i
      · norm_num
      · norm_num
        exact_mod_cast (by norm_num : (1 / 2 : ℝ) ≤ 1)
    · simpa using Finset.le_sup
        (s := Finset.univ)
        (f := fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 1 / 2‖₊)
        (Finset.mem_univ (0 : Fin 2))
  rw [hsup]
  norm_num

theorem higham10_8_counterAinv_opNorm2 :
    opNorm2 higham10_8_counterAinv = 4 := by
  unfold opNorm2
  rw [show higham10_8_counterAinv =
      Matrix.diagonal (fun i : Fin 2 => if i.val = 0 then (1 : ℝ) else 4) by
        ext i j
        simp [higham10_8_counterAinv, Matrix.diagonal_apply]]
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  have hsup : Finset.univ.sup
      (fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 4‖₊) = 4 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _hi
      fin_cases i
      · norm_num
        change (1 : ℝ) ≤ 4
        norm_num
      · norm_num
    · simpa using Finset.le_sup
        (s := Finset.univ)
        (f := fun i : Fin 2 => ‖if i.val = 0 then (1 : ℝ) else 4‖₊)
        (Finset.mem_univ (1 : Fin 2))
  rw [hsup]
  norm_num

theorem higham10_8_counter_product :
    matMul 2 higham10_8_counterAinv higham10_8_counterDeltaA =
      higham10_8_counterDeltaA := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matMul, Fin.sum_univ_two, higham10_8_counterAinv,
      higham10_8_counterDeltaA] <;> rfl

theorem higham10_8_counterDeltaA_opNorm2 :
    opNorm2 higham10_8_counterDeltaA = 1 / 2 := by
  unfold opNorm2
  rw [show higham10_8_counterDeltaA =
      Matrix.diagonal (fun i : Fin 2 => if i.val = 0 then (1 / 2 : ℝ) else 0) by
        ext i j
        simp [higham10_8_counterDeltaA, Matrix.diagonal_apply]
        aesop]
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  have hsup : Finset.univ.sup
      (fun i : Fin 2 => ‖if i.val = 0 then (1 / 2 : ℝ) else 0‖₊) =
        (1 / 2 : NNReal) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _hi
      fin_cases i
      · norm_num
      · norm_num
        exact (zero_le (1 / 2 : NNReal))
    · have h := Finset.le_sup
        (s := Finset.univ)
        (f := fun i : Fin 2 => ‖if i.val = 0 then (1 / 2 : ℝ) else 0‖₊)
        (Finset.mem_univ (0 : Fin 2))
      norm_num at h ⊢
      exact h
  rw [hsup]
  norm_num

theorem higham10_8_counterDeltaA_frobNormSq :
    frobNormSq higham10_8_counterDeltaA = 1 / 4 := by
  unfold frobNormSq higham10_8_counterDeltaA
  norm_num [Fin.sum_univ_two]

theorem higham10_8_counterDeltaA_frobNorm :
    frobNorm higham10_8_counterDeltaA = 1 / 2 := by
  have hsq := higham10_8_counterDeltaA_frobNormSq
  have hnonneg := frobNorm_nonneg higham10_8_counterDeltaA
  rw [← frobNorm_sq] at hsq
  nlinarith

/-- The counterexample satisfies the literal smallness hypothesis printed in
Theorem 10.8. -/
theorem higham10_8_counter_sourceSmallness :
    opNorm2
        (matMul 2 higham10_8_counterAinv higham10_8_counterDeltaA) < 1 := by
  rw [higham10_8_counter_product, higham10_8_counterDeltaA_opNorm2]
  norm_num

theorem higham10_8_counter_sourceKappa2 :
    higham10_8_sourceKappa2 higham10_8_counterA
      higham10_8_counterAinv = 4 := by
  simp [higham10_8_sourceKappa2, higham10_8_counterA_opNorm2,
    higham10_8_counterAinv_opNorm2]

theorem higham10_8_counter_sourceEpsilon :
    higham10_8_sourceEpsilon (opNorm2 higham10_8_counterA)
        higham10_8_counterDeltaA = 1 / 2 := by
  simp [higham10_8_sourceEpsilon, higham10_8_counterDeltaA_frobNorm,
    higham10_8_counterA_opNorm2]

theorem higham10_8_counter_kappa_mul_epsilon_gt_one :
    1 < higham10_8_sourceKappa2 higham10_8_counterA
        higham10_8_counterAinv *
      higham10_8_sourceEpsilon
        (opNorm2 higham10_8_counterA)
        higham10_8_counterDeltaA := by
  rw [higham10_8_counter_sourceKappa2, higham10_8_counter_sourceEpsilon]
  norm_num

theorem higham10_8_counter_sourceNormwiseRHS_neg :
    higham10_8_sourceNormwiseRHS
        (higham10_8_sourceKappa2 higham10_8_counterA
          higham10_8_counterAinv)
        (higham10_8_sourceEpsilon
          (opNorm2 higham10_8_counterA)
          higham10_8_counterDeltaA) < 0 := by
  rw [higham10_8_counter_sourceKappa2, higham10_8_counter_sourceEpsilon]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  unfold higham10_8_sourceNormwiseRHS
  have hnum : 0 < (1 / Real.sqrt 2) * ((4 : ℝ) * (1 / 2)) := by
    positivity
  have hden : 1 - (4 : ℝ) * (1 / 2) < 0 := by norm_num
  exact div_neg_of_pos_of_neg hnum hden

/-- **Source discrepancy for the printed Theorem 10.8 normwise display.**

For the literal `p = 2` data above, no perturbation can satisfy the printed
rational inequality: its left side is nonnegative while its right side is
strictly negative. -/
theorem higham10_8_printed_normwise_p2_source_discrepancy :
    ¬ ∃ DeltaR : Fin 2 → Fin 2 → ℝ,
      frobNorm DeltaR / opNorm2 higham10_8_counterR ≤
        higham10_8_sourceNormwiseRHS
          (higham10_8_sourceKappa2 higham10_8_counterA
            higham10_8_counterAinv)
          (higham10_8_sourceEpsilon
            (opNorm2 higham10_8_counterA)
            higham10_8_counterDeltaA) := by
  rintro ⟨DeltaR, hbound⟩
  have hlhs : 0 ≤ frobNorm DeltaR / opNorm2 higham10_8_counterR := by
    simpa [higham10_8_counterR_opNorm2] using frobNorm_nonneg DeltaR
  have hrhs := higham10_8_counter_sourceNormwiseRHS_neg
  linarith

/-- Literal conclusion-shaped version of the source discrepancy: adding the
actual Cholesky-factor requirement cannot rescue the impossible printed
inequality. -/
theorem higham10_8_printed_normwise_p2_factor_source_discrepancy :
    ¬ ∃ DeltaR : Fin 2 → Fin 2 → ℝ,
      CholeskyFactSpec 2 higham10_8_counterAplus
        (fun i j => higham10_8_counterR i j + DeltaR i j) ∧
      frobNorm DeltaR / opNorm2 higham10_8_counterR ≤
        higham10_8_sourceNormwiseRHS
          (higham10_8_sourceKappa2 higham10_8_counterA
            higham10_8_counterAinv)
          (higham10_8_sourceEpsilon
            (opNorm2 higham10_8_counterA)
            higham10_8_counterDeltaA) := by
  rintro ⟨DeltaR, _hfactor, hbound⟩
  exact higham10_8_printed_normwise_p2_source_discrepancy
    ⟨DeltaR, hbound⟩

/-- The corrected rational display has a positive denominator exactly on its
mathematically meaningful domain. -/
theorem higham10_8_sourceNormwiseRHS_nonneg_of_domain
    {kappa epsilon : ℝ} (hkappa : 0 ≤ kappa) (hepsilon : 0 ≤ epsilon)
    (hsmall : kappa * epsilon < 1) :
    0 ≤ higham10_8_sourceNormwiseRHS kappa epsilon := by
  unfold higham10_8_sourceNormwiseRHS
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hden : 0 < 1 - kappa * epsilon := sub_pos.mpr hsmall
  positivity

/-- Conversely, a nonzero relative factor perturbation cannot satisfy the
printed rational inequality unless the omitted domain condition holds.  Thus
`kappa * epsilon < 1` is logically necessary for the displayed estimate, not
just a convenient proof side condition. -/
theorem higham10_8_sourceNormwise_domain_necessary
    {kappa epsilon lhs : ℝ}
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) (hlhs : 0 < lhs)
    (hbound : lhs ≤ higham10_8_sourceNormwiseRHS kappa epsilon) :
    kappa * epsilon < 1 := by
  by_contra hnot
  have hge : 1 ≤ kappa * epsilon := not_lt.mp hnot
  by_cases heq : kappa * epsilon = 1
  · have hrhs : higham10_8_sourceNormwiseRHS kappa epsilon = 0 := by
      simp [higham10_8_sourceNormwiseRHS, heq]
    rw [hrhs] at hbound
    linarith
  · have hgt : 1 < kappa * epsilon := lt_of_le_of_ne hge (Ne.symm heq)
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hnum : 0 < (1 / Real.sqrt 2) * (kappa * epsilon) := by
      positivity
    have hden : 1 - kappa * epsilon < 0 := by linarith
    have hrhs : higham10_8_sourceNormwiseRHS kappa epsilon < 0 := by
      exact div_neg_of_pos_of_neg hnum hden
    linarith

end

end NumStability
