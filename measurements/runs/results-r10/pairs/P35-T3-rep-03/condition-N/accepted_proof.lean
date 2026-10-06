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
  have hDiagPos (i : Fin n) : 0 < p35DiagSquare L i := by
    simp only [p35DiagSquare]
    exact pow_pos (hLdiag i) 2
  have hRowPos (i : Fin n) : 0 < p35RowEnergy L i := by
    rw [p35RowEnergy]
    exact add_pos_of_pos_of_nonneg (hDiagPos i)
      (Finset.sum_nonneg fun k hk => sq_nonneg (L i k))
  have hDiagRow (i : Fin n) : p35DiagSquare L i ≤ p35RowEnergy L i := by
    rw [p35RowEnergy]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k hk => sq_nonneg (L i k))
  have hDiagProdPos : 0 < ∏ i, p35DiagSquare L i := by
    exact Finset.prod_pos fun i hi => hDiagPos i
  have hRowProdPos : 0 < ∏ i, p35RowEnergy L i := by
    exact Finset.prod_pos fun i hi => hRowPos i
  have hProdLe : (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i := by
    exact Finset.prod_le_prod (fun i hi => (hDiagPos i).le) (fun i hi => hDiagRow i)
  have hHadamardLe : p35HadamardMeasure L ≤ 1 := by
    rw [p35HadamardMeasure]
    exact (div_le_one hRowProdPos).2 hProdLe
  have hHadamardEq :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hProdEq : (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        apply (div_eq_one_iff_eq hRowProdPos.ne').1
        simpa only [p35HadamardMeasure] using hmeasureOne
      have hEachEq : ∀ i, p35DiagSquare L i = p35RowEnergy L i := by
        intro i
        by_contra hne
        have hiStrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hDiagRow i) hne
        have hStrict : (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          refine Finset.prod_lt_prod (fun j hj => hDiagPos j)
            (fun j hj => hDiagRow j) ?_
          exact ⟨i, Finset.mem_univ i, hiStrict⟩
        exact hStrict.ne hProdEq
      intro i k hki
      have hsum :
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
            (L i j) ^ 2) = 0 := by
        have hi := hEachEq i
        rw [p35RowEnergy] at hi
        linarith
      have hterm : (L i k) ^ 2 = 0 := by
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val)) =>
            sq_nonneg (L i j))).1 hsum
        exact hall k (Finset.mem_filter.2 ⟨Finset.mem_univ k, hki⟩)
      exact (sq_eq_zero_iff).1 hterm
    · intro hdiagonal
      have hEachEq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        rw [p35RowEnergy]
        have hz :
            (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
              (L i k) ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := by simpa using hk
          rw [hdiagonal i k hki]
          norm_num
        rw [hz, add_zero]
      rw [p35HadamardMeasure]
      have hden : (∏ i, p35RowEnergy L i) = ∏ i, p35DiagSquare L i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hEachEq i
      rw [hden, div_self hDiagProdPos.ne']
  have hScaleDiag (i : Fin n) :
      p35DiagSquare (p35ScaleRows s L) i = (s i) ^ 2 * p35DiagSquare L i := by
    simp only [p35DiagSquare, p35ScaleRows]
    ring
  have hScaleRow (i : Fin n) :
      p35RowEnergy (p35ScaleRows s L) i = (s i) ^ 2 * p35RowEnergy L i := by
    simp only [p35RowEnergy, hScaleDiag, p35ScaleRows, mul_pow]
    rw [mul_add, Finset.mul_sum]
  have hScaleFactorNe : (∏ i, (s i) ^ 2) ≠ 0 := by
    apply (Finset.prod_ne_zero_iff).2
    intro i hi
    exact pow_ne_zero 2 (hs i)
  have hScaleInvariant :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    rw [p35HadamardMeasure, p35HadamardMeasure]
    simp_rw [hScaleDiag, hScaleRow]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hScaleFactorNe
  have hTailProdPos (m : ℕ) (hm : m ≤ M) : 0 < ∏ i, tailEigen m i := by
    exact Finset.prod_pos fun i hi => htailPos m hm i
  have hTailProdExp (m : ℕ) (hm : m ≤ M) :
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    have hroot :
        (∏ i, tailEigen m i) ^ (n : ℝ)⁻¹ ≤
          (∑ i, tailEigen m i) / (n : ℝ) := by
      simpa using (Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
        (fun _ => (1 : ℝ)) (tailEigen m)
        (by intro i hi; norm_num)
        (by simpa using (show (0 : ℝ) < n by exact_mod_cast hn))
        (fun i hi => (htailPos m hm i).le))
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hroot' :
        (∏ i, tailEigen m i) ^ (n : ℝ)⁻¹ ≤ (n + 1 : ℝ) / (n : ℝ) := by
      exact hroot.trans (div_le_div_of_nonneg_right (htailSum m hm) hnreal.le)
    have hpow := pow_le_pow_left₀
      (Real.rpow_nonneg (hTailProdPos m hm).le _) hroot' n
    have hprodBound :
        (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / (n : ℝ)) ^ n := by
      rw [Real.rpow_inv_natCast_pow (hTailProdPos m hm).le hn.ne'] at hpow
      exact hpow
    have hexp : (1 - (-1 : ℝ) / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      simpa using (Real.one_sub_div_pow_le_exp_neg
        (n := n) (t := (-1 : ℝ)) (by linarith [hnreal]))
    calc
      (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / (n : ℝ)) ^ n := hprodBound
      _ = (1 - (-1 : ℝ) / (n : ℝ)) ^ n := by
        congr 1
        field_simp
        ring
      _ ≤ Real.exp 1 := hexp
  have hEigenLower : ∀ m, m ≤ M → measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [hmeasureEigen m hm]
    calc
      lambdaMin m * (∏ i, tailEigen m i) / Real.exp 1 =
          lambdaMin m * ((∏ i, tailEigen m i) / Real.exp 1) := by ring
      _ ≤ lambdaMin m * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact (div_le_one (Real.exp_pos 1)).2 (hTailProdExp m hm)
        · exact (hlambdaMinPos m hm).le
      _ = lambdaMin m := by ring
  have hJacobiMeasure : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := by omega
    have hfactorPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hdiagMNe : diagProduct m ≠ 0 := (hdiagPos m hm.le).ne'
    have hfactorNe : 1 - (jacobiEntry m) ^ 2 ≠ 0 := hfactorPos.ne'
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m hm.le, hjacobi m hm]
      field_simp
    refine ⟨heq, ?_⟩
    rw [heq]
    apply (le_div_iff₀ hfactorPos).2
    have hmeasurePos : 0 < measure m := by
      rw [hmeasureEigen m hm.le]
      exact mul_pos (hlambdaMinPos m hm.le) (hTailProdPos m hm.le)
    simpa using (mul_le_mul_of_nonneg_left
      (sub_le_self 1 (sq_nonneg (jacobiEntry m))) hmeasurePos.le)
  have hMeasureZero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0, p35HadamardMeasure]
  have hMeasureMonoZero : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        have hmM : m < M := by omega
        exact (ih (by omega)).trans (hJacobiMeasure m hmM).2
  have hHadamardPos : 0 < p35HadamardMeasure L := by
    rw [← hMeasureZero, hmeasureEigen 0 (Nat.zero_le M)]
    exact mul_pos (hlambdaMinPos 0 (Nat.zero_le M))
      (hTailProdPos 0 (Nat.zero_le M))
  have hKappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hnOneNonneg : (0 : ℝ) ≤ n + 1 := by positivity
    have hbaseLower : p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      rw [← hMeasureZero]
      exact (div_le_div_of_nonneg_right (hMeasureMonoZero m hm)
        (Real.exp_pos 1).le).trans (hEigenLower m hm)
    rw [hkappa m hm]
    calc
      lambdaMax m / lambdaMin m ≤ (n + 1 : ℝ) / lambdaMin m := by
        exact div_le_div_of_nonneg_right (hlambdaMax m hm) (hlambdaMinPos m hm).le
      _ ≤ (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) := by
        exact div_le_div_of_nonneg_left hnOneNonneg
          (div_pos hHadamardPos (Real.exp_pos 1)) hbaseLower
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
        field_simp
  exact ⟨hHadamardLe, hHadamardEq, hScaleInvariant, hEigenLower,
    hJacobiMeasure, hKappaBound⟩

end HighamBench
