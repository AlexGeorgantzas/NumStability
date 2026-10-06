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
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hdiagSqPos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    exact sq_pos_of_pos (hLdiag i)
  have hrowEnergyPos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    exact add_pos_of_pos_of_nonneg (hdiagSqPos i)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hdiagLeRow : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hprodDiagPos : 0 < ∏ i, p35DiagSquare L i :=
    Finset.prod_pos fun i _ => hdiagSqPos i
  have hprodRowPos : 0 < ∏ i, p35RowEnergy L i :=
    Finset.prod_pos fun i _ => hrowEnergyPos i
  have hprodDiagLeRow :
      (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i :=
    Finset.prod_le_prod (fun i _ => (hdiagSqPos i).le) (fun i _ => hdiagLeRow i)
  have hHadPos : 0 < p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    positivity
  have hHadLe : p35HadamardMeasure L ≤ 1 := by
    unfold p35HadamardMeasure
    exact (div_le_one hprodRowPos).2 hprodDiagLeRow
  have hHadEq :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprodEq :
          (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        apply (div_eq_one_iff_eq hprodRowPos.ne').mp
        simpa only [p35HadamardMeasure] using hmeasureOne
      intro i k hki
      have henergyEq : p35DiagSquare L i = p35RowEnergy L i := by
        by_contra hne
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hdiagLeRow i) hne
        have hprodStrict :
            (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod
          · intro j _
            exact hdiagSqPos j
          · intro j _
            exact hdiagLeRow j
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hprodStrict) hprodEq
      have hsumZero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
              (L i j) ^ 2 = 0 := by
        unfold p35RowEnergy at henergyEq
        linarith
      have hkMem :
          k ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_lt_mk]
          using hki
      have hkSq : (L i k) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (L i j))).mp
          hsumZero k hkMem
      exact sq_eq_zero_iff.mp hkSq
    · intro hdiag
      have hrowEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        unfold p35RowEnergy
        have hsumZero :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
                (L i k) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
          rw [hdiag i k hki]
          simp
        rw [hsumZero, add_zero]
      unfold p35HadamardMeasure
      simp_rw [hrowEq]
      exact div_self hprodDiagPos.ne'
  have hscaleInvariant :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    have hscaleDiag : ∀ i,
        p35DiagSquare (p35ScaleRows s L) i =
          (s i) ^ 2 * p35DiagSquare L i := by
      intro i
      unfold p35DiagSquare p35ScaleRows
      ring
    have hscaleRow : ∀ i,
        p35RowEnergy (p35ScaleRows s L) i =
          (s i) ^ 2 * p35RowEnergy L i := by
      intro i
      unfold p35RowEnergy p35DiagSquare p35ScaleRows
      simp only [mul_pow]
      rw [← Finset.mul_sum
        (Finset.univ.filter (fun k : Fin n => k.val < i.val))
        (fun k => (L i k) ^ 2) ((s i) ^ 2)]
      ring
    have hsProdNe : (∏ i, (s i) ^ 2) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact pow_ne_zero _ (hs i)
    unfold p35HadamardMeasure
    simp_rw [hscaleDiag, hscaleRow]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hsProdNe
  have htailProdExp : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (0 : ℝ) ≤ 1 / (n : ℝ) := by
      intro i hi
      positivity
    have hwSum : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun _ : Fin n => (1 / (n : ℝ))) (tailEigen m) hw hwSum
      (fun i _ => (htailPos m hm i).le)
    have hweighted :
        (∑ i : Fin n, (1 / (n : ℝ)) * tailEigen m i) ≤
          (n + 1 : ℝ) / (n : ℝ) := by
      rw [← Finset.mul_sum]
      calc
        (1 / (n : ℝ)) * ∑ i, tailEigen m i ≤
            (1 / (n : ℝ)) * (n + 1 : ℝ) :=
          mul_le_mul_of_nonneg_left (htailSum m hm) (by positivity)
        _ = (n + 1 : ℝ) / (n : ℝ) := by ring
    have hroot :
        (∏ i : Fin n, (tailEigen m i) ^ (1 / (n : ℝ))) ≤
          (n + 1 : ℝ) / (n : ℝ) := hgm.trans hweighted
    have hrootNonneg :
        0 ≤ ∏ i : Fin n, (tailEigen m i) ^ (1 / (n : ℝ)) := by
      apply Finset.prod_nonneg
      intro i _
      exact Real.rpow_nonneg (htailPos m hm i).le _
    have hrootPow :
        (∏ i : Fin n, (tailEigen m i) ^ (1 / (n : ℝ))) ^ n =
          ∏ i, tailEigen m i := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_natCast ((tailEigen m i) ^ (1 / (n : ℝ))) n,
        ← Real.rpow_mul (htailPos m hm i).le]
      rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
    have hprodMean :
        (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / (n : ℝ)) ^ n := by
      rw [← hrootPow]
      exact pow_le_pow_left₀ hrootNonneg hroot n
    have hmeanEq :
        (n + 1 : ℝ) / (n : ℝ) = 1 / (n : ℝ) + 1 := by
      field_simp
      ring
    have hbaseExp :
        (n + 1 : ℝ) / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      rw [hmeanEq]
      exact Real.add_one_le_exp _
    have hmeanNonneg : 0 ≤ (n + 1 : ℝ) / (n : ℝ) := by positivity
    have hexpPow : (Real.exp (1 / (n : ℝ))) ^ n = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    exact hprodMean.trans <| (pow_le_pow_left₀ hmeanNonneg hbaseExp n).trans_eq hexpPow
  have hlambdaLower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    rw [hmeasureEigen m hm]
    exact mul_le_mul_of_nonneg_left (htailProdExp m hm) (hlambdaMinPos m hm).le
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm, hdetH]
    exact div_pos hprodDiagPos (hdiagPos m hm)
  have hjacobiConclusion : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := hm
    have hqPos : 0 < 1 - (jacobiEntry m) ^ 2 := sub_pos.mpr (hjacobiSmall m hm)
    have hupdate :
        measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m hm.le, hjacobi m hm]
      field_simp
    refine ⟨hupdate, ?_⟩
    rw [hupdate]
    apply (le_div_iff₀ hqPos).2
    have hqLe : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    exact mul_le_of_le_one_right (hmeasurePos m hm.le).le hqLe
  have hmeasureZero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hmeasureMonotoneFromZero : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        have hmLt : m < M := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_trans (Nat.le_succ m) hm)).trans
          (hjacobiConclusion m hmLt).2
  have hkappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hHadDivExpLe :
        p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      rw [← hmeasureZero]
      exact le_trans
        (div_le_div_of_nonneg_right (hmeasureMonotoneFromZero m hm)
          (Real.exp_pos 1).le)
        (hlambdaLower m hm)
    have hfirst :
        kappa m ≤ (n + 1 : ℝ) / lambdaMin m := by
      rw [hkappa m hm]
      exact div_le_div_of_nonneg_right (hlambdaMax m hm) (hlambdaMinPos m hm).le
    have hsecond :
        (n + 1 : ℝ) / lambdaMin m ≤
          (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) := by
      exact div_le_div_of_nonneg_left (by positivity)
        (div_pos hHadPos (Real.exp_pos 1)) hHadDivExpLe
    calc
      kappa m ≤ (n + 1 : ℝ) / lambdaMin m := hfirst
      _ ≤ (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) := hsecond
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
        field_simp
  exact ⟨hHadLe, hHadEq, hscaleInvariant, hlambdaLower,
    hjacobiConclusion, hkappaBound⟩

end HighamBench
