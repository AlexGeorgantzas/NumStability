import HighamBench.P35Definitions
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion

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
    unfold p35DiagSquare
    exact sq_pos_of_ne_zero (ne_of_gt (hLdiag i))
  have hrowExtraNonneg : ∀ i,
      0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
        (L i k) ^ 2 := by
    intro i
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hdiagSqLeRow : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    unfold p35RowEnergy
    linarith [hrowExtraNonneg i]
  have hrowPos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    exact lt_of_lt_of_le (hdiagSqPos i) (hdiagSqLeRow i)
  have hdiagProdPos : 0 < ∏ i, p35DiagSquare L i := by
    exact Finset.prod_pos (fun i _ ↦ hdiagSqPos i)
  have hrowProdPos : 0 < ∏ i, p35RowEnergy L i := by
    exact Finset.prod_pos (fun i _ ↦ hrowPos i)
  have hdiagProdLeRow :
      (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i := by
    exact Finset.prod_le_prod
      (fun i _ ↦ (hdiagSqPos i).le) (fun i _ ↦ hdiagSqLeRow i)
  have hHadPos : 0 < p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    exact div_pos hdiagProdPos hrowProdPos
  have hHadLe : p35HadamardMeasure L ≤ 1 := by
    unfold p35HadamardMeasure
    exact (div_le_one hrowProdPos).2 hdiagProdLeRow
  have hHadEq :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprodEq :
          (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        exact (div_eq_one_iff_eq hrowProdPos.ne').mp
          (by simpa [p35HadamardMeasure] using hmeasureOne)
      have hrowEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        by_contra hne
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hdiagSqLeRow i) (Ne.symm hne)
        have hprodStrict :
            (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod
          · intro j _
            exact hdiagSqPos j
          · intro j _
            exact hdiagSqLeRow j
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hprodStrict) hprodEq
      intro i k hki
      have hsumZero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
              (L i j) ^ 2 = 0 := by
        have hi := hrowEq i
        unfold p35RowEnergy at hi
        linarith
      have hallZero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ.filter (fun j : Fin n ↦ j.val < i.val))
          (f := fun j ↦ (L i j) ^ 2)
          (by intro j _; exact sq_nonneg _)).mp hsumZero
      have hkSq : (L i k) ^ 2 = 0 :=
        hallZero k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩)
      nlinarith [sq_nonneg (L i k)]
    · intro hdiagonal
      unfold p35HadamardMeasure
      apply (div_eq_one_iff_eq hrowProdPos.ne').2
      apply Finset.prod_congr rfl
      intro i _
      unfold p35RowEnergy
      have hsumZero :
          ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (L i k) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hki : k.val < i.val := by simpa using hk
        rw [hdiagonal i k hki]
        norm_num
      rw [hsumZero, add_zero]
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
    simp only [p35RowEnergy, p35DiagSquare, p35ScaleRows]
    calc
      (s i * L i i) ^ 2 +
            ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (s i * L i k) ^ 2 =
          (s i) ^ 2 * (L i i) ^ 2 +
            ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (s i) ^ 2 * (L i k) ^ 2 := by
                apply congrArg₂ (· + ·)
                · ring
                · apply Finset.sum_congr rfl
                  intro k _
                  ring
      _ = (s i) ^ 2 * (L i i) ^ 2 +
            (s i) ^ 2 *
              ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
                (L i k) ^ 2 := by rw [Finset.mul_sum]
      _ = (s i) ^ 2 *
            ((L i i) ^ 2 +
              ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
                (L i k) ^ 2) := by ring
  have hscaleProdPos : 0 < ∏ i, (s i) ^ 2 := by
    apply Finset.prod_pos
    intro i _
    exact sq_pos_of_ne_zero (hs i)
  have hscaleInvariant :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    unfold p35HadamardMeasure
    rw [Finset.prod_congr rfl (fun i _ ↦ hscaleDiag i),
      Finset.prod_congr rfl (fun i _ ↦ hscaleRow i),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    field_simp [hscaleProdPos.ne', hrowProdPos.ne']
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htailProdExp : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hamgm :=
      NumStability.higham14_problem14_13_amgm_prod_le_pow_sum_div_card
        hn (tailEigen m) (fun i ↦ (htailPos m hm i).le)
    have havg :
        (∑ i, tailEigen m i) / (n : ℝ) ≤
          (n + 1 : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnR).2 (htailSum m hm)
    have havgNonneg : 0 ≤ (∑ i, tailEigen m i) / (n : ℝ) := by
      exact div_nonneg
        (Finset.sum_nonneg (fun i _ ↦ (htailPos m hm i).le)) hnR.le
    have hpowAvg :
        ((∑ i, tailEigen m i) / (n : ℝ)) ^ n ≤
          ((n + 1 : ℝ) / (n : ℝ)) ^ n := by
      exact pow_le_pow_left₀ havgNonneg havg n
    have hbase : (n + 1 : ℝ) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
      field_simp
    have honeExp :
        (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc
        (1 + 1 / (n : ℝ)) ^ n
            ≤ (Real.exp (1 / (n : ℝ))) ^ n := by
                apply pow_le_pow_left₀
                · positivity
                · linarith [Real.add_one_le_exp (1 / (n : ℝ))]
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) :=
          (Real.exp_nat_mul (1 / (n : ℝ)) n).symm
        _ = Real.exp 1 := by
          rw [mul_one_div, div_self hnR.ne']
    exact hamgm.trans (hpowAvg.trans (by simpa [hbase] using honeExp))
  have hdetHPos : 0 < detH := by
    rw [hdetH]
    exact hdiagProdPos
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetHPos (hdiagPos m hm)
  have hmeasure0 : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hlambdaLower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [hmeasureEigen m hm]
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    exact mul_le_mul_of_nonneg_left (htailProdExp m hm)
      (hlambdaMinPos m hm).le
  have hjacobiConclusion : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
        measure m ≤ measure (m + 1) := by
    intro m hm
    have hmM : m ≤ M := by omega
    have hsuccM : m + 1 ≤ M := by omega
    have hfactorPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have heq :
        measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hsuccM, hmeasure m hmM, hjacobi m hm]
      field_simp [hfactorPos.ne', (hdiagPos m hmM).ne']
    refine ⟨heq, ?_⟩
    rw [heq]
    apply (le_div_iff₀ hfactorPos).2
    have hmpos := hmeasurePos m hmM
    nlinarith [sq_nonneg (jacobiEntry m)]
  have hmeasureMono : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        exact (ih (by omega)).trans (hjacobiConclusion m (by omega)).2
  have hkappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    rw [hkappa m hm]
    have hHadDivExp :
        p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      rw [← hmeasure0]
      exact (div_le_div_of_nonneg_right (hmeasureMono m hm)
        (Real.exp_pos 1).le).trans (hlambdaLower m hm)
    have hHadLeMinExp :
        p35HadamardMeasure L ≤ lambdaMin m * Real.exp 1 :=
      (div_le_iff₀ (Real.exp_pos 1)).mp hHadDivExp
    rw [div_le_div_iff₀ (hlambdaMinPos m hm) hHadPos]
    calc
      lambdaMax m * p35HadamardMeasure L
          ≤ (n + 1 : ℝ) * p35HadamardMeasure L :=
        mul_le_mul_of_nonneg_right (hlambdaMax m hm) hHadPos.le
      _ ≤ (n + 1 : ℝ) * (lambdaMin m * Real.exp 1) := by
        exact mul_le_mul_of_nonneg_left hHadLeMinExp (by positivity)
      _ = ((n + 1 : ℝ) * Real.exp 1) * lambdaMin m := by ring
  exact ⟨hHadLe, hHadEq, hscaleInvariant, hlambdaLower,
    hjacobiConclusion, hkappaBound⟩

end HighamBench
