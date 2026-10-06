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
  classical
  have hdiagSqPos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    simp only [p35DiagSquare]
    exact sq_pos_of_pos (hLdiag i)
  have hrowEnergyPos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    rw [p35RowEnergy]
    have hsquares : 0 ≤
        ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val), (L i k) ^ 2 := by
      positivity
    linarith [hdiagSqPos i]
  have hdiagRow : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    rw [p35RowEnergy]
    exact le_add_of_nonneg_right (by positivity)
  have hdiagProdPos : 0 < ∏ i, p35DiagSquare L i :=
    Finset.prod_pos (fun i _ ↦ hdiagSqPos i)
  have hrowProdPos : 0 < ∏ i, p35RowEnergy L i :=
    Finset.prod_pos (fun i _ ↦ hrowEnergyPos i)
  have hmeasureLPos : 0 < p35HadamardMeasure L := by
    rw [p35HadamardMeasure]
    positivity
  have hmeasureL_le_one : p35HadamardMeasure L ≤ 1 := by
    rw [p35HadamardMeasure, div_le_one hrowProdPos]
    exact Finset.prod_le_prod (fun i _ ↦ (hdiagSqPos i).le)
      (fun i _ ↦ hdiagRow i)
  have hmeasureL_eq_one :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprodEq :
          (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        exact (div_eq_one_iff_eq hrowProdPos.ne').mp (by
          simpa only [p35HadamardMeasure] using hmeasureOne)
      have hpointEq : ∀ i, p35DiagSquare L i = p35RowEnergy L i := by
        intro i
        by_contra hne
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hdiagRow i) hne
        have hprodStrict :
            (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j :=
          Finset.prod_lt_prod (fun j _ ↦ hdiagSqPos j)
            (fun j _ ↦ hdiagRow j) ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hprodStrict) hprodEq
      intro i k hki
      have hsumZero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (L i j) ^ 2 = 0 := by
        have hi := hpointEq i
        rw [p35RowEnergy] at hi
        linarith
      have hkmem : k ∈
          Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩
      have hkZero : (L i k) ^ 2 = 0 :=
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (L i j))).mp
          hsumZero) k hkmem
      nlinarith
    · intro hdiagonal
      have hpointEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        rw [p35RowEnergy]
        have hsumZero :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
                (L i k) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
          rw [hdiagonal i k hki, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        rw [hsumZero, add_zero]
      rw [p35HadamardMeasure]
      have hprodEq : (∏ i, p35RowEnergy L i) = ∏ i, p35DiagSquare L i := by
        apply Finset.prod_congr rfl
        intro i _
        exact hpointEq i
      rw [hprodEq, div_self hdiagProdPos.ne']
  have hdiagScale : ∀ i,
      p35DiagSquare (p35ScaleRows s L) i =
        (s i) ^ 2 * p35DiagSquare L i := by
    intro i
    simp only [p35DiagSquare, p35ScaleRows]
    ring
  have hrowScale : ∀ i,
      p35RowEnergy (p35ScaleRows s L) i =
        (s i) ^ 2 * p35RowEnergy L i := by
    intro i
    rw [p35RowEnergy, hdiagScale]
    have hsumScale :
        (∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
            (p35ScaleRows s L i k) ^ 2) =
          (s i) ^ 2 *
            ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (L i k) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [p35ScaleRows]
      ring
    rw [hsumScale, p35RowEnergy]
    ring
  have hscaleInvariant :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    rw [p35HadamardMeasure, p35HadamardMeasure]
    simp_rw [hdiagScale, hrowScale]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hscaleProdNe : (∏ i, (s i) ^ 2) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero 2 (hs i)
    field_simp
  have hdetHPos : 0 < detH := by
    rw [hdetH]
    exact hdiagProdPos
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetHPos (hdiagPos m hm)
  have hmeasureZero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have htailProdBound : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have htailProductPos : 0 < ∏ i, tailEigen m i :=
      Finset.prod_pos (fun i _ ↦ htailPos m hm i)
    have hlogBound : Real.log (∏ i, tailEigen m i) ≤ 1 := by
      rw [Real.log_prod (fun i _ ↦ (htailPos m hm i).ne')]
      calc
        (∑ i, Real.log (tailEigen m i)) ≤
            ∑ i, (tailEigen m i - 1) := by
              apply Finset.sum_le_sum
              intro i _
              exact Real.log_le_sub_one_of_pos (htailPos m hm i)
        _ = (∑ i, tailEigen m i) - n := by simp
        _ ≤ 1 := by
          have := htailSum m hm
          norm_num at this ⊢
          linarith
    rw [← Real.exp_log htailProductPos]
    exact Real.exp_le_exp.mpr hlogBound
  have hlambdaLower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [hmeasureEigen m hm]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    calc
      lambdaMin m * (∏ i, tailEigen m i) ≤
          lambdaMin m * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (htailProdBound m hm)
          (hlambdaMinPos m hm).le
      _ = lambdaMin m * Real.exp 1 := rfl
  have hjacobiStep : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.le_of_lt hm
    have hsuccM : m + 1 ≤ M := by omega
    have hpivotPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hstepEq :
        measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hsuccM, hmeasure m hmM, hjacobi m hm]
      field_simp
    refine ⟨hstepEq, ?_⟩
    rw [hstepEq]
    apply (le_div_iff₀ hpivotPos).mpr
    have hmeasureNonneg := (hmeasurePos m hmM).le
    have hsquareNonneg : 0 ≤ (jacobiEntry m) ^ 2 := sq_nonneg _
    nlinarith
  have hmeasureMonotoneFromZero : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
        intro hsuccM
        have hmM : m ≤ M := Nat.le_trans (Nat.le_succ m) hsuccM
        have hmLtM : m < M := by omega
        exact le_trans (ih hmM) (hjacobiStep m hmLtM).2
  have hkappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hdimPos : 0 < (n + 1 : ℝ) := by positivity
    have hlowerFromInitial :
        p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      rw [← hmeasureZero]
      exact le_trans
        (div_le_div_of_nonneg_right (hmeasureMonotoneFromZero m hm)
          (Real.exp_pos 1).le)
        (hlambdaLower m hm)
    rw [hkappa m hm]
    calc
      lambdaMax m / lambdaMin m ≤
          (n + 1 : ℝ) / lambdaMin m :=
        div_le_div_of_nonneg_right (hlambdaMax m hm) (hlambdaMinPos m hm).le
      _ ≤ (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) :=
        (div_le_div_iff_of_pos_left hdimPos (hlambdaMinPos m hm)
          (div_pos hmeasureLPos (Real.exp_pos 1))).mpr hlowerFromInitial
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
        field_simp
  exact ⟨hmeasureL_le_one, hmeasureL_eq_one, hscaleInvariant,
    hlambdaLower, hjacobiStep, hkappaBound⟩

end HighamBench
