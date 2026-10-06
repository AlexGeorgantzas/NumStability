import NumStability.Algorithms.TestMatrices.Higham28Contracts
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators

namespace NumStability

def headTailEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

open Matrix

theorem det_succ_eq_pivot_mul_schur
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ha : A 0 0 ≠ 0) :
    Matrix.det A = A 0 0 * Matrix.det (fun i j : Fin n =>
      A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ) := by
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := headTailEquiv n
  let a : ℝ := A 0 0
  let B : Matrix (Fin 1) (Fin n) ℝ := fun _ j => a⁻¹ * A 0 j.succ
  let C : Matrix (Fin n) (Fin 1) ℝ := fun i _ => A i.succ 0
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.succ j.succ
  let L : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (fun _ _ => a) 0 0 1
  let M : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
    Matrix.fromBlocks 1 B C D
  have he_left : e (Sum.inl 0) = 0 := by
    ext
    simp [e, headTailEquiv]
  have he_right (i : Fin n) : e (Sum.inr i) = i.succ := by
    ext
    simp [e, headTailEquiv]
  have hfactor : A.submatrix e e = L * M := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, L, M, a, he_left]
    · fin_cases i
      simp [Matrix.mul_apply, L, M, B, a, he_left, he_right, ha]
    · fin_cases j
      simp [Matrix.mul_apply, Matrix.one_apply, L, M, C, a, he_left, he_right]
    · simp [Matrix.mul_apply, Matrix.one_apply, L, M, D, he_right]
  have hdetL : Matrix.det L = a := by
    simp [L]
  have hdetM : Matrix.det M = Matrix.det (fun i j : Fin n =>
      A i.succ j.succ - A i.succ 0 * a⁻¹ * A 0 j.succ) := by
    rw [show M = Matrix.fromBlocks 1 B C D by rfl,
      Matrix.det_fromBlocks_one₁₁]
    congr 1
    ext i j
    simp [B, C, D, Matrix.mul_apply, a]
    ring
  calc
    Matrix.det A = Matrix.det (A.submatrix e e) :=
      (Matrix.det_submatrix_equiv_self e A).symm
    _ = Matrix.det (L * M) := by rw [hfactor]
    _ = Matrix.det L * Matrix.det M := Matrix.det_mul L M
    _ = a * Matrix.det (fun i j : Fin n =>
        A i.succ j.succ - A i.succ 0 * a⁻¹ * A 0 j.succ) := by
      rw [hdetL, hdetM]
    _ = A 0 0 * Matrix.det (fun i j : Fin n =>
        A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ) := by
      rfl

theorem prod_Ioi_zero_fin {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), f j) = ∏ j : Fin n, f j.succ := by
  symm
  refine Finset.prod_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_Ioi.mpr (Fin.succ_pos j)
  · intro a _ b _ hab
    exact Fin.succ_injective _ hab
  · intro b hb
    have hb0 : b ≠ 0 := ne_of_gt (Finset.mem_Ioi.mp hb)
    refine ⟨b.pred hb0, Finset.mem_univ _, ?_⟩
    exact Fin.succ_pred b hb0
  · intro j _
    rfl

theorem prod_Ioi_succ_fin {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i.succ, f j) =
      ∏ j ∈ Finset.Ioi i, f j.succ := by
  symm
  refine Finset.prod_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Ioi.mpr (Fin.succ_lt_succ_iff.mpr (Finset.mem_Ioi.mp hj))
  · intro a _ b _ hab
    exact Fin.succ_injective _ hab
  · intro b hb
    have hb0 : b ≠ 0 := by
      exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (Finset.mem_Ioi.mp hb))
    let a : Fin n := b.pred hb0
    have hia : i < a := by
      apply Fin.succ_lt_succ_iff.mp
      simpa [a] using Finset.mem_Ioi.mp hb
    refine ⟨a, Finset.mem_Ioi.mpr hia, ?_⟩
    exact Fin.succ_pred b hb0
  · intro j _
    rfl

theorem cauchyDetNumerator_succ
    {n : ℕ} (x y : RVec (n + 1)) :
    cauchyDetNumerator (n + 1) x y =
      (∏ i : Fin n, (x i.succ - x 0) * (y i.succ - y 0)) *
        cauchyDetNumerator n (fun i => x i.succ) (fun i => y i.succ) := by
  unfold cauchyDetNumerator
  rw [Fin.prod_univ_succ, prod_Ioi_zero_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simpa using prod_Ioi_succ_fin
    (fun j => (x j - x i.succ) * (y j - y i.succ)) i

theorem cauchyDetDenominator_succ
    {n : ℕ} (x y : RVec (n + 1)) :
    cauchyDetDenominator (n + 1) x y =
      (x 0 + y 0) *
        (∏ j : Fin n, (x 0 + y j.succ)) *
        (∏ i : Fin n, (x i.succ + y 0)) *
        cauchyDetDenominator n (fun i => x i.succ) (fun i => y i.succ) := by
  unfold cauchyDetDenominator
  rw [Fin.prod_univ_succ]
  simp_rw [Fin.prod_univ_succ]
  rw [Finset.prod_mul_distrib]
  ring

theorem cauchyAdmissible_tail
    {n : ℕ} {x y : RVec (n + 1)} (h : CauchyAdmissible x y) :
    CauchyAdmissible (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ) where
  x_injective := fun i j hij => Fin.succ_injective _ (h.x_injective hij)
  y_injective := fun i j hij => Fin.succ_injective _ (h.y_injective hij)
  sum_ne_zero := fun i j => h.sum_ne_zero i.succ j.succ

theorem cauchyDetFormula_succ
    {n : ℕ} {x y : RVec (n + 1)} (h : CauchyAdmissible x y) :
    cauchyDetFormula (n + 1) x y =
      (1 / (x 0 + y 0)) *
        (∏ i : Fin n, (x i.succ - x 0) / (x i.succ + y 0)) *
        (∏ j : Fin n, (y j.succ - y 0) / (x 0 + y j.succ)) *
        cauchyDetFormula n (fun i => x i.succ) (fun i => y i.succ) := by
  have htail := cauchyAdmissible_tail h
  have h00 : x 0 + y 0 ≠ 0 := h.sum_ne_zero 0 0
  have hxprod : (∏ i : Fin n, (x i.succ + y 0)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => h.sum_ne_zero i.succ 0
  have hyprod : (∏ j : Fin n, (x 0 + y j.succ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ => h.sum_ne_zero 0 j.succ
  have htailDen : cauchyDetDenominator n (fun i => x i.succ)
      (fun i => y i.succ) ≠ 0 := cauchyDetDenominator_ne_zero htail
  rw [cauchyDetFormula_eq_num_div_den,
    cauchyDetFormula_eq_num_div_den,
    cauchyDetNumerator_succ, cauchyDetDenominator_succ]
  rw [Finset.prod_mul_distrib]
  simp_rw [Finset.prod_div_distrib]
  field_simp

theorem cauchyMatrix_det_succ
    {n : ℕ} {x y : RVec (n + 1)} (h : CauchyAdmissible x y) :
    Matrix.det (cauchyMatrix x y) =
      (1 / (x 0 + y 0)) *
        (∏ i : Fin n, (x i.succ - x 0) / (x i.succ + y 0)) *
        (∏ j : Fin n, (y j.succ - y 0) / (x 0 + y j.succ)) *
        Matrix.det (cauchyMatrix (fun i : Fin n => x i.succ)
          (fun i : Fin n => y i.succ)) := by
  let rowScale : Fin n → ℝ := fun i =>
    (x i.succ - x 0) / (x i.succ + y 0)
  let colScale : Fin n → ℝ := fun j =>
    (y j.succ - y 0) / (x 0 + y j.succ)
  let tail : Matrix (Fin n) (Fin n) ℝ :=
    cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)
  have hpivot : cauchyMatrix x y 0 0 ≠ 0 := by
    simp [cauchyMatrix, h.sum_ne_zero 0 0]
  rw [det_succ_eq_pivot_mul_schur (cauchyMatrix x y) hpivot]
  have hschur :
      (fun i j : Fin n =>
        cauchyMatrix x y i.succ j.succ -
          cauchyMatrix x y i.succ 0 * (cauchyMatrix x y 0 0)⁻¹ *
            cauchyMatrix x y 0 j.succ) =
        (fun i j => rowScale i * tail i j * colScale j) := by
    funext i j
    simp only [cauchyMatrix_apply]
    dsimp [rowScale, colScale, tail]
    field_simp [h.sum_ne_zero i.succ j.succ, h.sum_ne_zero i.succ 0,
      h.sum_ne_zero 0 j.succ, h.sum_ne_zero 0 0]
    ring
  rw [hschur]
  have hrow := Matrix.det_mul_column rowScale
    (fun i j => tail i j * colScale j)
  have hrow' : Matrix.det (fun i j => rowScale i * tail i j * colScale j) =
      (∏ i, rowScale i) * Matrix.det (fun i j => tail i j * colScale j) := by
    simpa only [mul_assoc] using hrow
  have hcol : Matrix.det (fun i j => tail i j * colScale j) =
      (∏ j, colScale j) * Matrix.det tail := by
    simpa [mul_comm] using Matrix.det_mul_row colScale tail
  rw [hrow', hcol]
  simp only [cauchyMatrix_apply]
  dsimp [rowScale, colScale, tail]
  ring

theorem cauchyMatrix_det_eq_formula :
    ∀ (n : ℕ) (x y : RVec n), CauchyAdmissible x y →
      Matrix.det (cauchyMatrix x y) = cauchyDetFormula n x y
  | 0, x, y, _ => by
      simp [cauchyMatrix, cauchyDetFormula]
  | n + 1, x, y, h => by
      rw [cauchyMatrix_det_succ h, cauchyDetFormula_succ h,
        cauchyMatrix_det_eq_formula n (fun i => x i.succ)
          (fun i => y i.succ) (cauchyAdmissible_tail h)]

theorem cauchy_ordered_minor_det_formula
    {m n k : ℕ} (x : RVec m) (y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j)
    (r : Fin k → Fin m) (c : Fin k → Fin n)
    (hr : StrictMono r) (hc : StrictMono c) :
    Matrix.det (fun i j => cauchyMatrix x y (r i) (c j)) =
      cauchyDetFormula k (fun i => x (r i)) (fun j => y (c j)) := by
  apply cauchyMatrix_det_eq_formula
  exact cauchyAdmissible_of_strictMono_of_pos
    (fun i => x (r i)) (fun j => y (c j))
    (hx.comp hr) (hy.comp hc) (fun i j => hsum (r i) (c j))

theorem cauchyMatrix_isStrictlyTotallyPositive
    {m n : ℕ} (x : RVec m) (y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    IsStrictlyTotallyPositive (cauchyMatrix x y) := by
  intro k _ r c hr hc
  rw [cauchy_ordered_minor_det_formula x y hx hy hsum r c hr hc]
  exact cauchyMinorDetFormula_pos x y hx hy hsum r c hr hc

theorem hilbertMatrix_eq_cauchyMatrix (n : ℕ) :
    hilbertMatrix n = cauchyMatrix
      (fun i : Fin n => (i.val : ℝ))
      (fun j : Fin n => (j.val : ℝ) + 1) := by
  ext i j
  simp only [hilbertMatrix_apply, cauchyMatrix_apply]
  congr 2
  push_cast
  ring

theorem hilbertMatrix_isStrictlyTotallyPositive (n : ℕ) :
    IsStrictlyTotallyPositive (hilbertMatrix n) := by
  rw [hilbertMatrix_eq_cauchyMatrix]
  apply cauchyMatrix_isStrictlyTotallyPositive
  · intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast hij
  · intro i j hij
    change (i.val : ℝ) + 1 < (j.val : ℝ) + 1
    have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  · intro i j
    positivity

theorem lagrange_basis_univ_factor
    {n : ℕ} (x : RVec n) (i j : Fin n) (hij : i ≠ j) :
    Lagrange.basis Finset.univ x j =
      Lagrange.basisDivisor (x j) (x i) *
        Lagrange.basis (Finset.univ.erase i) x j := by
  unfold Lagrange.basis
  have hi : i ∈ (Finset.univ.erase j : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  calc
    (∏ a ∈ Finset.univ.erase j, Lagrange.basisDivisor (x j) (x a)) =
        Lagrange.basisDivisor (x j) (x i) *
          ∏ a ∈ (Finset.univ.erase j).erase i,
            Lagrange.basisDivisor (x j) (x a) :=
      (Finset.mul_prod_erase (Finset.univ.erase j)
        (fun a => Lagrange.basisDivisor (x j) (x a)) hi).symm
    _ = Lagrange.basisDivisor (x j) (x i) *
          ∏ a ∈ (Finset.univ.erase i).erase j,
            Lagrange.basisDivisor (x j) (x a) := by
      congr 1
      apply Finset.prod_congr
      · ext a
        simp [and_comm]
      · intro a _
        rfl

noncomputable def cauchyInverseInterpolationPoly
    {n : ℕ} (x : RVec n) (i j : Fin n) : Polynomial ℝ :=
  if i = j then Lagrange.basis Finset.univ x j
  else
    Polynomial.C (-(x j - x i)⁻¹) *
      (Polynomial.C (x j) - Polynomial.X) *
      Lagrange.basis (Finset.univ.erase i) x j

theorem cauchyInverseInterpolationPoly_eval
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j k : Fin n) :
    Polynomial.eval (-y k) (cauchyInverseInterpolationPoly x i j) =
      ((x j + y k) / (x i + y k)) *
        Polynomial.eval (-y k) (Lagrange.basis Finset.univ x j) := by
  by_cases hij : i = j
  · subst i
    simp [cauchyInverseInterpolationPoly, h.sum_ne_zero j k]
  · rw [cauchyInverseInterpolationPoly, if_neg hij,
      lagrange_basis_univ_factor x i j hij]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Lagrange.basisDivisor]
    field_simp [h.sum_ne_zero i k,
      sub_ne_zero.mpr (fun hxij => hij (h.x_injective hxij).symm)]
    ring

theorem cauchyInverseInterpolationPoly_degree_lt
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    (cauchyInverseInterpolationPoly x i j).degree < (n : WithBot ℕ) := by
  by_cases hij : i = j
  · subst i
    rw [cauchyInverseInterpolationPoly, if_pos rfl,
      Lagrange.degree_basis h.x_injective.injOn (Finset.mem_univ j)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.pred_lt (Fin.pos j).ne'
  · have hxji : x j - x i ≠ 0 :=
      sub_ne_zero.mpr (fun hxij => hij (h.x_injective hxij).symm)
    have hn2 : 2 ≤ n := by
      omega
    have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    have hlinear :
        (Polynomial.C (x j) - Polynomial.X : Polynomial ℝ).degree = 1 := by
      rw [show (Polynomial.C (x j) - Polynomial.X : Polynomial ℝ) =
          -(Polynomial.X - Polynomial.C (x j)) by ring,
        Polynomial.degree_neg, Polynomial.degree_X_sub_C]
    rw [cauchyInverseInterpolationPoly, if_neg hij,
      Polynomial.degree_mul, Polynomial.degree_mul,
      Polynomial.degree_C (neg_ne_zero.mpr (inv_ne_zero hxji)),
      hlinear,
      Lagrange.degree_basis
        (h.x_injective.injOn.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))
        hjmem]
    simp only [Finset.card_erase_of_mem, Finset.mem_univ, Finset.card_univ,
      Fintype.card_fin]
    norm_num
    exact_mod_cast (show 1 + (n - 1 - 1) < n by omega)

theorem eval_lagrange_basis_univ
    {n : ℕ} (v : RVec n) (i : Fin n) (z : ℝ) :
    Polynomial.eval z (Lagrange.basis Finset.univ v i) =
      (∏ k ∈ Finset.univ.erase i, (z - v k)) /
        (∏ k ∈ Finset.univ.erase i, (v i - v k)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  simp only [Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  simp [div_eq_mul_inv, mul_comm]

theorem cauchyInverseEntry_eq_lagrange
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseEntry n x y i j =
      (x j + y i) *
        Polynomial.eval (-y i) (Lagrange.basis Finset.univ x j) *
        Polynomial.eval (-x j) (Lagrange.basis Finset.univ y i) := by
  have hxy : x j + y i ≠ 0 := h.sum_ne_zero j i
  have hxden : (∏ k ∈ Finset.univ.erase j, (x j - x k)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr fun heq =>
        (Finset.mem_erase.mp hk).1 (h.x_injective heq).symm
  have hyden : (∏ k ∈ Finset.univ.erase i, (y i - y k)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr fun heq =>
        (Finset.mem_erase.mp hk).1 (h.y_injective heq).symm
  have hfullX :
      (∏ k : Fin n, (x k + y i)) =
        (x j + y i) * ∏ k ∈ Finset.univ.erase j, (x k + y i) := by
    exact (Finset.mul_prod_erase Finset.univ (fun k => x k + y i)
      (Finset.mem_univ j)).symm
  have hfullY :
      (∏ k : Fin n, (x j + y k)) =
        (x j + y i) * ∏ k ∈ Finset.univ.erase i, (x j + y k) := by
    exact (Finset.mul_prod_erase Finset.univ (fun k => x j + y k)
      (Finset.mem_univ i)).symm
  have hnegX :
      (∏ k ∈ Finset.univ.erase j, (-y i - x k)) =
        (-1 : ℝ) ^ (n - 1) *
          ∏ k ∈ Finset.univ.erase j, (x k + y i) := by
    calc
      (∏ k ∈ Finset.univ.erase j, (-y i - x k)) =
          ∏ k ∈ Finset.univ.erase j, -(x k + y i) := by
        apply Finset.prod_congr rfl
        intro k _
        ring
      _ = (-1 : ℝ) ^ (Finset.univ.erase j).card *
          ∏ k ∈ Finset.univ.erase j, (x k + y i) :=
        Finset.prod_neg (fun k => x k + y i)
      _ = (-1 : ℝ) ^ (n - 1) *
          ∏ k ∈ Finset.univ.erase j, (x k + y i) := by
        simp
  have hnegY :
      (∏ k ∈ Finset.univ.erase i, (-x j - y k)) =
        (-1 : ℝ) ^ (n - 1) *
          ∏ k ∈ Finset.univ.erase i, (x j + y k) := by
    calc
      (∏ k ∈ Finset.univ.erase i, (-x j - y k)) =
          ∏ k ∈ Finset.univ.erase i, -(x j + y k) := by
        apply Finset.prod_congr rfl
        intro k _
        ring
      _ = (-1 : ℝ) ^ (Finset.univ.erase i).card *
          ∏ k ∈ Finset.univ.erase i, (x j + y k) :=
        Finset.prod_neg (fun k => x j + y k)
      _ = (-1 : ℝ) ^ (n - 1) *
          ∏ k ∈ Finset.univ.erase i, (x j + y k) := by
        simp
  have hsign : ((-1 : ℝ) ^ (n - 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [cauchyInverseEntry_eq_num_div_den]
  unfold cauchyInverseNumerator cauchyInverseDenominator
  rw [eval_lagrange_basis_univ, eval_lagrange_basis_univ,
    hnegX, hnegY, Finset.prod_mul_distrib, hfullX, hfullY]
  field_simp
  rw [hsign]
  ring

theorem lagrange_sum_eval_basis
    {n : ℕ} (v : RVec n) (hv : Function.Injective v)
    (p : Polynomial ℝ) (hp : p.degree < (n : WithBot ℕ)) (z : ℝ) :
    (∑ k : Fin n,
        Polynomial.eval (v k) p *
          Polynomial.eval z (Lagrange.basis Finset.univ v k)) =
      Polynomial.eval z p := by
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin n))) hv.injOn (by simpa using hp)
  have heval := congrArg (Polynomial.eval z) hinterp
  rw [Lagrange.interpolate_apply] at heval
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C] at heval
  simpa using heval.symm

theorem cauchyInverseInterpolationPoly_eval_at_node
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    Polynomial.eval (x j) (cauchyInverseInterpolationPoly x i j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl, cauchyInverseInterpolationPoly, if_pos rfl]
    exact Lagrange.eval_basis_self h.x_injective.injOn (Finset.mem_univ j)
  · rw [if_neg hij, cauchyInverseInterpolationPoly, if_neg hij]
    simp

theorem cauchyMatrix_mul_cauchyInverseFormula
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyMatrix x y * cauchyInverseFormula n x y = (1 : RSqMat n) := by
  ext i j
  rw [Matrix.mul_apply]
  let p : Polynomial ℝ := cauchyInverseInterpolationPoly x i j
  let q : Polynomial ℝ := p.comp (-Polynomial.X)
  have hpdeg : p.degree < (n : WithBot ℕ) :=
    cauchyInverseInterpolationPoly_degree_lt h i j
  have hqdeg : q.degree < (n : WithBot ℕ) := by
    simpa [q] using hpdeg
  have hterm (k : Fin n) :
      cauchyMatrix x y i k * cauchyInverseFormula n x y k j =
        Polynomial.eval (y k) q *
          Polynomial.eval (-x j) (Lagrange.basis Finset.univ y k) := by
    rw [show cauchyInverseFormula n x y k j = cauchyInverseEntry n x y k j by rfl,
      cauchyInverseEntry_eq_lagrange h]
    simp only [cauchyMatrix_apply]
    have hqeval : Polynomial.eval (y k) q = Polynomial.eval (-y k) p := by
      simp [q, Polynomial.eval_comp]
    rw [hqeval]
    have hpeval := cauchyInverseInterpolationPoly_eval h i j k
    change Polynomial.eval (-y k) p = _ at hpeval
    rw [hpeval]
    field_simp [h.sum_ne_zero i k]
  calc
    (∑ k, cauchyMatrix x y i k * cauchyInverseFormula n x y k j) =
        ∑ k, Polynomial.eval (y k) q *
          Polynomial.eval (-x j) (Lagrange.basis Finset.univ y k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    _ = Polynomial.eval (-x j) q :=
      lagrange_sum_eval_basis y h.y_injective q hqdeg (-x j)
    _ = Polynomial.eval (x j) p := by
      simp [q, Polynomial.eval_comp]
    _ = if i = j then 1 else 0 := by
      exact cauchyInverseInterpolationPoly_eval_at_node h i j
    _ = (1 : RSqMat n) i j := by
      simp [Matrix.one_apply, eq_comm]

theorem cauchyInverseFormula_mul_cauchyMatrix
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyInverseFormula n x y * cauchyMatrix x y = (1 : RSqMat n) := by
  exact mul_eq_one_comm.mp (cauchyMatrix_mul_cauchyInverseFormula h)

noncomputable def cauchyInverseOnesEntry
    {n : ℕ} (x y : RVec n) (k : Fin n) : ℝ :=
  (∏ j : Fin n, (x j + y k)) /
    (∏ l ∈ Finset.univ.erase k, (y k - y l))

theorem cauchyInverseOnes_residue_sum
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) (i : Fin n) :
    (∑ k : Fin n,
        (∏ j ∈ Finset.univ.erase i, (x j + y k)) /
          (∏ l ∈ Finset.univ.erase k, (y k - y l))) = 1 := by
  let p : Polynomial ℝ :=
    Lagrange.nodal (Finset.univ.erase i) (fun j : Fin n => -x j)
  have hpdeg : p.degree < (n : WithBot ℕ) := by
    dsimp [p]
    rw [Lagrange.degree_nodal]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.pred_lt (Fin.pos i).ne'
  have hpnat : p.natDegree = n - 1 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    dsimp [p]
    rw [Lagrange.degree_nodal]
    simp
  have hpcoeff : p.coeff (n - 1) = 1 := by
    rw [← hpnat]
    exact (Lagrange.nodal_monic (s := Finset.univ.erase i)
      (v := fun j : Fin n => -x j)).coeff_natDegree
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin n))) (v := y) (P := p)
    h.y_injective.injOn (by simpa using hpdeg)
  simp only [Finset.card_univ, Fintype.card_fin] at hcoeff
  rw [hpcoeff] at hcoeff
  symm
  simpa [p, Lagrange.eval_nodal, add_comm] using hcoeff

theorem cauchyMatrix_mulVec_cauchyInverseOnesEntry
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    (cauchyMatrix x y).mulVec (cauchyInverseOnesEntry x y) =
      (fun _ : Fin n => 1) := by
  funext i
  rw [Matrix.mulVec]
  rw [← cauchyInverseOnes_residue_sum h i]
  apply Finset.sum_congr rfl
  intro k _
  have hfull :
      (∏ j : Fin n, (x j + y k)) =
        (x i + y k) *
          ∏ j ∈ Finset.univ.erase i, (x j + y k) := by
    exact (Finset.mul_prod_erase Finset.univ (fun j => x j + y k)
      (Finset.mem_univ i)).symm
  change cauchyMatrix x y i k * cauchyInverseOnesEntry x y k = _
  rw [cauchyMatrix_apply]
  unfold cauchyInverseOnesEntry
  rw [hfull]
  field_simp [h.sum_ne_zero i k]

theorem cauchyInverseFormula_mulVec_one
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    (cauchyInverseFormula n x y).mulVec (fun _ : Fin n => 1) =
      cauchyInverseOnesEntry x y := by
  calc
    (cauchyInverseFormula n x y).mulVec (fun _ : Fin n => 1) =
        (cauchyInverseFormula n x y).mulVec
          ((cauchyMatrix x y).mulVec (cauchyInverseOnesEntry x y)) := by
      rw [cauchyMatrix_mulVec_cauchyInverseOnesEntry h]
    _ = (cauchyInverseFormula n x y * cauchyMatrix x y).mulVec
          (cauchyInverseOnesEntry x y) :=
      Matrix.mulVec_mulVec (cauchyInverseOnesEntry x y)
        (cauchyInverseFormula n x y) (cauchyMatrix x y)
    _ = (1 : RSqMat n).mulVec (cauchyInverseOnesEntry x y) := by
      rw [cauchyInverseFormula_mul_cauchyMatrix h]
    _ = cauchyInverseOnesEntry x y := Matrix.one_mulVec _

theorem sum_cauchyInverseOnesEntry
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    (∑ k : Fin n, cauchyInverseOnesEntry x y k) =
      ∑ k : Fin n, (x k + y k) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let f : Polynomial ℝ :=
      Lagrange.nodal Finset.univ (fun i : Fin n => -x i)
    let g : Polynomial ℝ := Lagrange.nodal Finset.univ y
    let p : Polynomial ℝ := f - g
    have hfdeg : f.degree = (n : WithBot ℕ) := by
      simp [f]
    have hgdeg : g.degree = (n : WithBot ℕ) := by
      simp [g]
    have hfmonic : f.Monic := by
      exact Lagrange.nodal_monic
    have hgmonic : g.Monic := by
      exact Lagrange.nodal_monic
    have hpdeg : p.degree < (n : WithBot ℕ) := by
      dsimp [p]
      rw [← hfdeg]
      exact Polynomial.degree_sub_lt (hfdeg.trans hgdeg.symm)
        hfmonic.ne_zero (hfmonic.leadingCoeff.trans hgmonic.leadingCoeff.symm)
    have hfnat : f.natDegree = n := by
      simp [f]
    have hgnat : g.natDegree = n := by
      simp [g]
    have hfnext : f.nextCoeff = ∑ i : Fin n, x i := by
      simpa [f, Lagrange.nodal_eq] using
        (Polynomial.prod_X_sub_C_nextCoeff
          (s := (Finset.univ : Finset (Fin n))) (fun i => -x i))
    have hgnext : g.nextCoeff = -∑ i : Fin n, y i := by
      simpa [g, Lagrange.nodal_eq] using
        (Polynomial.prod_X_sub_C_nextCoeff
          (s := (Finset.univ : Finset (Fin n))) y)
    have hfcoeff : f.coeff (n - 1) = ∑ i : Fin n, x i := by
      calc
        f.coeff (n - 1) = f.coeff (f.natDegree - 1) := by rw [hfnat]
        _ = f.nextCoeff :=
          (Polynomial.nextCoeff_of_natDegree_pos (by simpa [hfnat] using hnpos)).symm
        _ = ∑ i : Fin n, x i := hfnext
    have hgcoeff : g.coeff (n - 1) = -∑ i : Fin n, y i := by
      calc
        g.coeff (n - 1) = g.coeff (g.natDegree - 1) := by rw [hgnat]
        _ = g.nextCoeff :=
          (Polynomial.nextCoeff_of_natDegree_pos (by simpa [hgnat] using hnpos)).symm
        _ = -∑ i : Fin n, y i := hgnext
    have hpcoeff : p.coeff (n - 1) =
        (∑ i : Fin n, x i) + ∑ i : Fin n, y i := by
      change (f - g).coeff (n - 1) = _
      rw [Polynomial.coeff_sub, hfcoeff, hgcoeff]
      ring
    have hpeval (k : Fin n) :
        Polynomial.eval (y k) p = ∏ i : Fin n, (x i + y k) := by
      have hgzero : Polynomial.eval (y k) g = 0 := by
        exact Lagrange.eval_nodal_at_node (s := Finset.univ) (v := y)
          (Finset.mem_univ k)
      change Polynomial.eval (y k) (f - g) = _
      rw [Polynomial.eval_sub, hgzero, sub_zero]
      simp [f, Lagrange.eval_nodal, add_comm]
    have hcoeff := Lagrange.coeff_eq_sum
      (s := (Finset.univ : Finset (Fin n))) (v := y) (P := p)
      h.y_injective.injOn (by simpa using hpdeg)
    simp only [Finset.card_univ, Fintype.card_fin] at hcoeff
    rw [hpcoeff] at hcoeff
    have hresidue :
        (∑ k : Fin n, cauchyInverseOnesEntry x y k) =
          (∑ i : Fin n, x i) + ∑ i : Fin n, y i := by
      rw [hcoeff]
      apply Finset.sum_congr rfl
      intro k _
      rw [hpeval]
      rfl
    rw [hresidue, Finset.sum_add_distrib]

theorem sum_cauchyInverseFormula
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    (∑ i : Fin n, ∑ j : Fin n, cauchyInverseFormula n x y i j) =
      ∑ i : Fin n, (x i + y i) := by
  rw [← sum_cauchyInverseOnesEntry h]
  apply Finset.sum_congr rfl
  intro i _
  have hrow := congrFun (cauchyInverseFormula_mulVec_one h) i
  simpa [Matrix.mulVec, dotProduct] using hrow

noncomputable def cauchyChoPotential
    {n : ℕ} (x y : RVec n) (i j : Fin n) (r : ℕ) : ℝ :=
  (1 / (x i + y j)) *
    ∏ l ∈ Finset.univ.filter (fun l : Fin n => l.val < r),
      ((x i - x l) * (y j - y l)) /
        ((x i + y l) * (x l + y j))

noncomputable def cauchyChoTerm
    {n : ℕ} (x y : RVec n) (i j k : Fin n) : ℝ :=
  ((x k + y k) / ((x i + y k) * (x k + y j))) *
    ∏ l ∈ Finset.Iio k,
      ((x i - x l) * (y j - y l)) /
        ((x i + y l) * (x l + y j))

theorem cauchyChoPotential_zero
    {n : ℕ} (x y : RVec n) (i j : Fin n) :
    cauchyChoPotential x y i j 0 = 1 / (x i + y j) := by
  simp [cauchyChoPotential]

theorem cauchyChoPotential_eq_Iio
    {n : ℕ} (x y : RVec n) (i j k : Fin n) :
    cauchyChoPotential x y i j k.val =
      (1 / (x i + y j)) *
        ∏ l ∈ Finset.Iio k,
          ((x i - x l) * (y j - y l)) /
            ((x i + y l) * (x l + y j)) := by
  unfold cauchyChoPotential
  congr 2
  ext l
  simp

theorem cauchyChoPotential_succ
    {n : ℕ} (x y : RVec n) (i j k : Fin n) :
    cauchyChoPotential x y i j (k.val + 1) =
      cauchyChoPotential x y i j k.val *
        (((x i - x k) * (y j - y k)) /
          ((x i + y k) * (x k + y j))) := by
  unfold cauchyChoPotential
  have hset :
      Finset.univ.filter (fun l : Fin n => l.val < k.val + 1) =
        insert k (Finset.univ.filter (fun l : Fin n => l.val < k.val)) := by
    ext l
    simp
    omega
  rw [hset, Finset.prod_insert (by simp)]
  ring

theorem cauchyChoPotential_at_dim
    {n : ℕ} (x y : RVec n) (i j : Fin n) :
    cauchyChoPotential x y i j n = 0 := by
  unfold cauchyChoPotential
  have hi : i ∈ Finset.univ.filter (fun l : Fin n => l.val < n) := by
    simp
  have hfactor :
      ((x i - x i) * (y j - y i)) /
          ((x i + y i) * (x i + y j)) = 0 := by
    simp
  rw [Finset.prod_eq_zero hi hfactor, mul_zero]

theorem cauchyChoPotential_sub_succ
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j k : Fin n) :
    cauchyChoPotential x y i j k.val -
        cauchyChoPotential x y i j (k.val + 1) =
      cauchyChoTerm x y i j k := by
  rw [cauchyChoPotential_succ, cauchyChoPotential_eq_Iio]
  unfold cauchyChoTerm
  field_simp [h.sum_ne_zero i j, h.sum_ne_zero i k, h.sum_ne_zero k j]
  ring

theorem cauchyLower_mul_cauchyUpper_term_diagonal
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (k j : Fin n) (hkj : k ≤ j) :
    cauchyLower n x y k k * cauchyUpper n x y k j =
      cauchyChoTerm x y k j k := by
  rw [cauchyLower_diagonal, cauchyUpper_entry_of_le x y k j hkj]
  unfold cauchyChoTerm
  simp_rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hden :
      (∏ l ∈ Finset.Iio k, (x k + y l)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l _ => h.sum_ne_zero k l
  have hden' :
      (∏ l ∈ Finset.Iio k, (x l + y j)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l _ => h.sum_ne_zero l j
  field_simp [h.sum_ne_zero k k, h.sum_ne_zero k j, hden, hden']

theorem cauchyLower_mul_cauchyUpper_term_of_lt
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j k : Fin n) (hki : k < i) (hkj : k ≤ j) :
    cauchyLower n x y i k * cauchyUpper n x y k j =
      cauchyChoTerm x y i j k := by
  rw [cauchyLower_entry_of_lt x y i k hki,
    cauchyUpper_entry_of_le x y k j hkj]
  unfold cauchyChoTerm
  simp_rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hA : (∏ l ∈ Finset.Iio k, (x k + y l)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l _ => h.sum_ne_zero k l
  have hC : (∏ l ∈ Finset.Iio k, (x i + y l)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l _ => h.sum_ne_zero i l
  have hD : (∏ l ∈ Finset.Iio k, (x k - x l)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l hl =>
      sub_ne_zero.mpr fun heq =>
        (Finset.mem_Iio.mp hl).ne (h.x_injective heq).symm
  have hF : (∏ l ∈ Finset.Iio k, (x l + y j)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun l _ => h.sum_ne_zero l j
  field_simp [h.sum_ne_zero i k, h.sum_ne_zero k j, hA, hC, hD, hF]

theorem cauchyChoTerm_zero_of_row_lt
    {n : ℕ} (x y : RVec n) (i j k : Fin n) (hik : i < k) :
    cauchyChoTerm x y i j k = 0 := by
  unfold cauchyChoTerm
  have hi : i ∈ Finset.Iio k := Finset.mem_Iio.mpr hik
  have hfactor :
      ((x i - x i) * (y j - y i)) /
          ((x i + y i) * (x i + y j)) = 0 := by
    simp
  rw [Finset.prod_eq_zero hi hfactor, mul_zero]

theorem cauchyChoTerm_zero_of_col_lt
    {n : ℕ} (x y : RVec n) (i j k : Fin n) (hjk : j < k) :
    cauchyChoTerm x y i j k = 0 := by
  unfold cauchyChoTerm
  have hj : j ∈ Finset.Iio k := Finset.mem_Iio.mpr hjk
  have hfactor :
      ((x i - x j) * (y j - y j)) /
          ((x i + y j) * (x j + y j)) = 0 := by
    simp
  rw [Finset.prod_eq_zero hj hfactor, mul_zero]

theorem cauchyLower_mul_cauchyUpper_term
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j k : Fin n) :
    cauchyLower n x y i k * cauchyUpper n x y k j =
      cauchyChoTerm x y i j k := by
  by_cases hki : k ≤ i
  · by_cases hkj : k ≤ j
    · rcases hki.eq_or_lt with rfl | hki'
      · exact cauchyLower_mul_cauchyUpper_term_diagonal h k j hkj
      · exact cauchyLower_mul_cauchyUpper_term_of_lt h i j k hki' hkj
    · have hjk : j < k := lt_of_not_ge hkj
      rw [cauchyUpper_zero_of_lt x y k j hjk,
        cauchyChoTerm_zero_of_col_lt x y i j k hjk, mul_zero]
  · have hik : i < k := lt_of_not_ge hki
    rw [cauchyLower_zero_of_lt x y i k hik,
      cauchyChoTerm_zero_of_row_lt x y i j k hik, zero_mul]

theorem sum_cauchyChoTerm
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    (∑ k : Fin n, cauchyChoTerm x y i j k) = cauchyMatrix x y i j := by
  calc
    (∑ k : Fin n, cauchyChoTerm x y i j k) =
        ∑ k : Fin n,
          (cauchyChoPotential x y i j k.val -
            cauchyChoPotential x y i j (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (cauchyChoPotential_sub_succ h i j k).symm
    _ = ∑ r ∈ Finset.range n,
          (cauchyChoPotential x y i j r -
            cauchyChoPotential x y i j (r + 1)) := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun r => cauchyChoPotential x y i j r -
          cauchyChoPotential x y i j (r + 1)) n
    _ = cauchyChoPotential x y i j 0 - cauchyChoPotential x y i j n :=
      Finset.sum_range_sub' _ n
    _ = 1 / (x i + y j) := by
      rw [cauchyChoPotential_zero, cauchyChoPotential_at_dim, sub_zero]
    _ = cauchyMatrix x y i j := by
      rw [cauchyMatrix_apply]

theorem cauchyLower_mul_cauchyUpper
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyLower n x y * cauchyUpper n x y = cauchyMatrix x y := by
  ext i j
  rw [Matrix.mul_apply]
  calc
    (∑ k, cauchyLower n x y i k * cauchyUpper n x y k j) =
        ∑ k, cauchyChoTerm x y i j k := by
      apply Finset.sum_congr rfl
      intro k _
      exact cauchyLower_mul_cauchyUpper_term h i j k
    _ = cauchyMatrix x y i j := sum_cauchyChoTerm h i j

end NumStability
