import HighamBench.P35Definitions

namespace HighamBench

open scoped BigOperators

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
  have hdiagSqPos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    exact sq_pos_of_pos (hLdiag i)
  have hrowPos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    have hsumsq : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
        (L i k) ^ 2 := by positivity
    linarith [hdiagSqPos i]
  have hdiag_le_row : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    exact le_add_of_nonneg_right (by positivity)
  have hdiagProdPos : 0 < ∏ i, p35DiagSquare L i :=
    Finset.prod_pos fun i _ ↦ hdiagSqPos i
  have hrowProdPos : 0 < ∏ i, p35RowEnergy L i :=
    Finset.prod_pos fun i _ ↦ hrowPos i
  have hprod_le : (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i :=
    Finset.prod_le_prod (fun i _ ↦ (hdiagSqPos i).le) fun i _ ↦ hdiag_le_row i
  have hHadPos : 0 < p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    positivity
  have hHadLe : p35HadamardMeasure L ≤ 1 := by
    unfold p35HadamardMeasure
    exact (div_le_one hrowProdPos).2 hprod_le
  have hHadEq : p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprodEq : (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        unfold p35HadamardMeasure at hmeasureOne
        exact (div_eq_one_iff_eq hrowProdPos.ne').mp hmeasureOne
      have hpoint : ∀ i, p35DiagSquare L i = p35RowEnergy L i := by
        intro i
        apply le_antisymm (hdiag_le_row i)
        by_contra hnot
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_not_ge hnot
        have hallstrict : (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod (s := Finset.univ)
          · intro j _
            exact hdiagSqPos j
          · intro j _
            exact hdiag_le_row j
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hallstrict) hprodEq
      intro i k hik
      have hsumzero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
              (L i j) ^ 2 = 0 := by
        have hi := hpoint i
        unfold p35RowEnergy at hi
        linarith
      have htermzero : (L i k) ^ 2 = 0 := by
        have hmem : k ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ k, hik⟩
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (L i j))).mp
          hsumzero k hmem
      nlinarith
    · intro hdiagonal
      have hrowEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        unfold p35RowEnergy
        have hsum :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
                (L i k) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [hdiagonal i k (Finset.mem_filter.mp hk).2]
          norm_num
        rw [hsum, add_zero]
      unfold p35HadamardMeasure
      rw [Finset.prod_congr rfl (fun i _ ↦ hrowEq i)]
      exact div_self hdiagProdPos.ne'
  have hscaleDiag : ∀ i,
      p35DiagSquare (p35ScaleRows s L) i = (s i) ^ 2 * p35DiagSquare L i := by
    intro i
    unfold p35DiagSquare p35ScaleRows
    ring
  have hscaleRow : ∀ i,
      p35RowEnergy (p35ScaleRows s L) i = (s i) ^ 2 * p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy p35DiagSquare p35ScaleRows
    simp_rw [mul_pow]
    rw [mul_add, Finset.mul_sum]
  have hscaleProdNe : (∏ i, (s i) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero 2 (hs i)
  have hscaleInvariant :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    simp_rw [hscaleDiag, hscaleRow, Finset.prod_mul_distrib]
    field_simp
  have hmeasureZero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hdetHPos : 0 < detH := by
    rw [hdetH]
    exact hdiagProdPos
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetHPos (hdiagPos m hm)
  have hstep : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
        measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := hm
    have hmle : m ≤ M := Nat.le_trans (Nat.le_add_right m 1) hm1
    have hpivotPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hformula : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m hmle, hjacobi m hm]
      field_simp
      <;> ring
    refine ⟨hformula, ?_⟩
    rw [hformula]
    exact (le_div_iff₀ hpivotPos).2
      (mul_le_of_le_one_right (hmeasurePos m hmle).le (by nlinarith [sq_nonneg (jacobiEntry m)]))
  have hmonoZero : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        have hmM : m < M := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hmM)).trans (by simpa [Nat.succ_eq_add_one] using (hstep m hmM).2)
  have htailProdExp : ∀ m, m ≤ M → (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (1 / (n : ℝ)) := by
      intro i hi
      positivity
    have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun _ ↦ (1 / (n : ℝ))) (tailEigen m) hw hw'
      (fun i _ ↦ (htailPos m hm i).le)
    have hmeanLe :
        ∑ i : Fin n, (1 / (n : ℝ)) * tailEigen m i ≤
          ((n + 1 : ℝ) / (n : ℝ)) := by
      rw [← Finset.mul_sum]
      apply (mul_le_mul_of_nonneg_left (htailSum m hm) (by positivity)).trans_eq
      field_simp
      <;> ring
    have hrootLe :
        ∏ i, (tailEigen m i) ^ (1 / (n : ℝ)) ≤
          ((n + 1 : ℝ) / (n : ℝ)) := hgm.trans hmeanLe
    have hrootNonneg : 0 ≤ ∏ i, (tailEigen m i) ^ (1 / (n : ℝ)) := by
      apply Finset.prod_nonneg
      intro i _
      exact Real.rpow_nonneg (htailPos m hm i).le _
    have hpow : (∏ i, (tailEigen m i) ^ (1 / (n : ℝ))) ^ n =
        ∏ i, tailEigen m i := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_natCast ((tailEigen m i) ^ (1 / (n : ℝ))) n,
        ← Real.rpow_mul (htailPos m hm i).le]
      rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
    have hprodMean : (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / (n : ℝ)) ^ n := by
      rw [← hpow]
      exact pow_le_pow_left₀ hrootNonneg hrootLe n
    have hmeanExp : ((n + 1 : ℝ) / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      have hneg : (-1 : ℝ) ≤ (n : ℝ) :=
        (show (-1 : ℝ) ≤ 0 by norm_num).trans (Nat.cast_nonneg n)
      have he := Real.one_sub_div_pow_le_exp_neg (n := n) (t := (-1 : ℝ)) hneg
      convert he using 1 <;> field_simp <;> ring
    exact hprodMean.trans hmeanExp
  have hlambdaLower : ∀ m, m ≤ M → measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [div_le_iff₀ (Real.exp_pos 1), hmeasureEigen m hm]
    exact mul_le_mul_of_nonneg_left (htailProdExp m hm) (hlambdaMinPos m hm).le
  refine ⟨hHadLe, hHadEq, hscaleInvariant, hlambdaLower, hstep, ?_⟩
  intro m hm
  rw [hkappa m hm]
  have hlower0 : p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
    rw [← hmeasureZero]
    exact (div_le_div_of_nonneg_right (hmonoZero m hm) (Real.exp_pos 1).le).trans
      (hlambdaLower m hm)
  have hcross : p35HadamardMeasure L ≤ lambdaMin m * Real.exp 1 :=
    (div_le_iff₀ (Real.exp_pos 1)).mp hlower0
  apply (div_le_div_of_nonneg_right (hlambdaMax m hm) (hlambdaMinPos m hm).le).trans
  apply (div_le_div_iff₀ (hlambdaMinPos m hm) hHadPos).2
  have hdim : (0 : ℝ) ≤ n + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcross hdim]

end HighamBench
