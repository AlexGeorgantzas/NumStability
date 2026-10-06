import HighamBench.P35Definitions
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion

namespace HighamBench

open scoped BigOperators

private lemma p35_eq_of_prod_eq_of_pos_le {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hab : ∀ i, a i ≤ b i) (hprod : ∏ i, a i = ∏ i, b i) :
    ∀ i, a i = b i := by
  classical
  intro i
  apply le_antisymm (hab i)
  by_contra hnot
  have hlt : a i < b i := lt_of_not_ge hnot
  have harest : 0 < ∏ j ∈ ({i}ᶜ : Finset (Fin n)), a j :=
    Finset.prod_pos (fun j _ ↦ ha j)
  have hrest :
      ∏ j ∈ ({i}ᶜ : Finset (Fin n)), a j ≤
        ∏ j ∈ ({i}ᶜ : Finset (Fin n)), b j := by
    exact Finset.prod_le_prod (fun j _ ↦ (ha j).le) (fun j _ ↦ hab j)
  have hstrict :
      a i * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), a j <
        b i * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), b j := by
    calc
      a i * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), a j <
          b i * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), a j :=
        mul_lt_mul_of_pos_right hlt harest
      _ ≤ b i * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), b j :=
        mul_le_mul_of_nonneg_left hrest (hb i).le
  rw [← Fintype.prod_eq_mul_prod_compl i a,
    ← Fintype.prod_eq_mul_prod_compl i b] at hstrict
  exact (ne_of_lt hstrict) hprod

/-- P35-T3: all five Hadamard-measure conclusions of Proposition 6.2. -/
theorem p35_t3_hadamard_measure_jacobi_growth
    (n M : ℕ) (L : Fin n → Fin n → ℝ) (s : Fin n → ℝ)
    (detH : ℝ) (diagProduct measure jacobiEntry : ℕ → ℝ)
    (lambdaMin lambdaMax : ℕ → ℝ)
    (tailEigen : ℕ → Fin n → ℝ) (kappa : ℕ → ℝ)
    (hn : 0 < n)
    (hLdiag : ∀ i, 0 < L i i)
    (hs : ∀ i, s i ≠ 0)
    (hdetH : detH = ∏ i, p35DiagSquare L i)
    (hdiag0 : diagProduct 0 = ∏ i, p35RowEnergy L i)
    (hdiagPos : ∀ m, m ≤ M → 0 < diagProduct m)
    (hmeasure : ∀ m, m ≤ M → measure m = detH / diagProduct m)
    (hjacobi : ∀ m, m < M →
      diagProduct (m + 1) =
        (1 - (jacobiEntry m) ^ 2) * diagProduct m)
    (hjacobiSmall : ∀ m, m < M → (jacobiEntry m) ^ 2 < 1)
    (hlambdaMinPos : ∀ m, m ≤ M → 0 < lambdaMin m)
    (htailPos : ∀ m, m ≤ M → ∀ i, 0 < tailEigen m i)
    (htailSum : ∀ m, m ≤ M →
      ∑ i, tailEigen m i ≤ (n + 1 : ℝ))
    (hmeasureEigen : ∀ m, m ≤ M →
      measure m = lambdaMin m * ∏ i, tailEigen m i)
    (hlambdaMax : ∀ m, m ≤ M → lambdaMax m ≤ (n + 1 : ℝ))
    (hkappa : ∀ m, m ≤ M → kappa m = lambdaMax m / lambdaMin m) :
    p35HadamardMeasure L ≤ 1 ∧
    (p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L) ∧
    p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L ∧
    (∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m) ∧
    (∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1)) ∧
    (∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L) := by
  -- PROOF_START P35-T3-H001
  classical
  have hdiagSqPos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    simpa [p35DiagSquare] using sq_pos_of_pos (hLdiag i)
  have hrowPos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    exact add_pos_of_pos_of_nonneg (hdiagSqPos i)
      (Finset.sum_nonneg (fun k _ ↦ sq_nonneg (L i k)))
  have hdiag_le_row : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg (fun k _ ↦ sq_nonneg (L i k)))
  have hdiagProdPos : 0 < ∏ i, p35DiagSquare L i :=
    Finset.prod_pos (fun i _ ↦ hdiagSqPos i)
  have hrowProdPos : 0 < ∏ i, p35RowEnergy L i :=
    Finset.prod_pos (fun i _ ↦ hrowPos i)
  have hprod_le :
      (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i := by
    exact Finset.prod_le_prod (fun i _ ↦ (hdiagSqPos i).le)
      (fun i _ ↦ hdiag_le_row i)
  have hhad_le : p35HadamardMeasure L ≤ 1 := by
    unfold p35HadamardMeasure
    exact (div_le_one hrowProdPos).2 hprod_le
  have hhad_pos : 0 < p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    exact div_pos hdiagProdPos hrowProdPos
  have hhad_eq :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprodEq :
          (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i :=
        (div_eq_one_iff_eq hrowProdPos.ne').mp (by
          simpa [p35HadamardMeasure] using hmeasureOne)
      have hrowEq : ∀ i, p35DiagSquare L i = p35RowEnergy L i :=
        p35_eq_of_prod_eq_of_pos_le _ _ hdiagSqPos hrowPos hdiag_le_row hprodEq
      intro i k hik
      have hsumZero :
          ∀ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
              (L i j) ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg (L i j))).mp
        have hi := hrowEq i
        unfold p35RowEnergy at hi
        linarith
      have hkSq : (L i k) ^ 2 = 0 :=
        hsumZero k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hik⟩)
      nlinarith
    · intro hdiagonal
      have hrowEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        unfold p35RowEnergy
        rw [add_eq_left]
        apply Finset.sum_eq_zero
        intro k hk
        have hik : k.val < i.val := (Finset.mem_filter.mp hk).2
        rw [hdiagonal i k hik]
        norm_num
      have hprodEq :
          (∏ i, p35RowEnergy L i) = ∏ i, p35DiagSquare L i :=
        Finset.prod_congr rfl (fun i _ ↦ hrowEq i)
      unfold p35HadamardMeasure
      rw [hprodEq, div_self hdiagProdPos.ne']
  have hscale_eq :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    have hscaleDiag : ∀ i,
        p35DiagSquare (p35ScaleRows s L) i =
          (s i) ^ 2 * p35DiagSquare L i := by
      intro i
      simp only [p35DiagSquare, p35ScaleRows]
      ring
    have hscaleRow : ∀ i,
        p35RowEnergy (p35ScaleRows s L) i =
          (s i) ^ 2 * p35RowEnergy L i := by
      intro i
      unfold p35RowEnergy p35DiagSquare p35ScaleRows
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      ring
    have hscaleProdNe : (∏ i, (s i) ^ 2) ≠ 0 := by
      apply (Finset.prod_ne_zero_iff).2
      intro i _
      exact pow_ne_zero 2 (hs i)
    unfold p35HadamardMeasure
    simp_rw [hscaleDiag, hscaleRow]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hscaleProdNe
  have hdetPos : 0 < detH := by
    rw [hdetH]
    exact hdiagProdPos
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetPos (hdiagPos m hm)
  have htailProdBound : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsumNonneg : 0 ≤ ∑ i, tailEigen m i := by
      exact Finset.sum_nonneg (fun i _ ↦ (htailPos m hm i).le)
    have hamgm :=
      NumStability.higham14_problem14_13_amgm_prod_le_pow_sum_div_card
        hn (tailEigen m) (fun i ↦ (htailPos m hm i).le)
    have havg :
        ((∑ i, tailEigen m i) / (n : ℝ)) ≤
          (n + 1 : ℝ) / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnR).2 (htailSum m hm)
    have hpavg :
        ((∑ i, tailEigen m i) / (n : ℝ)) ^ n ≤
          ((n + 1 : ℝ) / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ (div_nonneg hsumNonneg hnR.le) havg n
    have hbaseEq :
        (n + 1 : ℝ) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
      push_cast
      field_simp
    have hbaseExp :
        (n + 1 : ℝ) / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      rw [hbaseEq]
      simpa [add_comm] using Real.add_one_le_exp (1 / (n : ℝ))
    have heuler :
        ((n + 1 : ℝ) / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc
        ((n + 1 : ℝ) / (n : ℝ)) ^ n
            ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) hbaseExp n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) :=
          (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by
          congr 1
          field_simp
    exact hamgm.trans (hpavg.trans heuler)
  have hlambdaLower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [hmeasureEigen m hm]
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    exact mul_le_mul_of_nonneg_left (htailProdBound m hm)
      (hlambdaMinPos m hm).le
  have hjacobiConclusion : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
        measure m ≤ measure (m + 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.le_of_lt hm
    have hsuccM : m + 1 ≤ M := hm
    have hfactorPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have heq :
        measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hsuccM, hmeasure m hmM, hjacobi m hm]
      field_simp [hfactorPos.ne', (hdiagPos m hmM).ne']
    refine ⟨heq, ?_⟩
    rw [heq]
    apply (le_div_iff₀ hfactorPos).2
    exact mul_le_of_le_one_right (hmeasurePos m hmM).le
      (sub_le_self 1 (sq_nonneg (jacobiEntry m)))
  have hmeasureZero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hmeasureMono : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        have hm_lt : m < M := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hm_lt)).trans
          (hjacobiConclusion m hm_lt).2
  have hkappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hhadMeasure : p35HadamardMeasure L ≤ measure m := by
      rw [← hmeasureZero]
      exact hmeasureMono m hm
    have hhadDiv :
        p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m :=
      (div_le_div_of_nonneg_right hhadMeasure (Real.exp_pos 1).le).trans
        (hlambdaLower m hm)
    rw [hkappa m hm]
    calc
      lambdaMax m / lambdaMin m ≤ (n + 1 : ℝ) / lambdaMin m :=
        div_le_div_of_nonneg_right (hlambdaMax m hm) (hlambdaMinPos m hm).le
      _ ≤ (n + 1 : ℝ) /
          (p35HadamardMeasure L / Real.exp 1) :=
        div_le_div_of_nonneg_left (by positivity)
          (div_pos hhad_pos (Real.exp_pos 1)) hhadDiv
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
        field_simp [hhad_pos.ne', (Real.exp_pos 1).ne']
  exact ⟨hhad_le, hhad_eq, hscale_eq, hlambdaLower,
    hjacobiConclusion, hkappaBound⟩

end HighamBench
