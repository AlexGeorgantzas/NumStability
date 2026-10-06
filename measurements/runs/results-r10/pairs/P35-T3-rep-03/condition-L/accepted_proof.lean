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
  have hdiag_pos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    simp only [p35DiagSquare]
    exact sq_pos_of_pos (hLdiag i)
  have hrow_ge : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    simp only [p35RowEnergy]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => sq_nonneg (L i k))
  have hrow_pos : ∀ i, 0 < p35RowEnergy L i :=
    fun i => (hdiag_pos i).trans_le (hrow_ge i)
  have hprod_diag_pos : 0 < ∏ i, p35DiagSquare L i := by
    exact Finset.prod_pos fun i _ => hdiag_pos i
  have hprod_row_pos : 0 < ∏ i, p35RowEnergy L i := by
    exact Finset.prod_pos fun i _ => hrow_pos i
  have hprod_le : (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i := by
    exact Finset.prod_le_prod
      (fun i _ => (hdiag_pos i).le) (fun i _ => hrow_ge i)
  have hHadLe : p35HadamardMeasure L ≤ 1 := by
    rw [p35HadamardMeasure]
    exact (div_le_one hprod_row_pos).2 hprod_le
  have hHadIff :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasureOne
      have hprod_eq :
          (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        exact (div_eq_one_iff_eq hprod_row_pos.ne').mp
          (by simpa only [p35HadamardMeasure] using hmeasureOne)
      intro i k hik
      have henergy_eq : p35DiagSquare L i = p35RowEnergy L i := by
        by_contra hne
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hrow_ge i) hne
        have hprod_strict :
            (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod
          · intro j _
            exact hdiag_pos j
          · intro j _
            exact hrow_ge j
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact hprod_strict.ne hprod_eq
      have hsum_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
              (L i j) ^ 2 = 0 := by
        rw [p35RowEnergy] at henergy_eq
        linarith
      have hk_mem : k ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hik⟩
      have hk_sq : (L i k) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (L i j))).mp hsum_zero k hk_mem
      nlinarith [sq_nonneg (L i k)]
    · intro hdiag
      have henergy_eq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        simp only [p35RowEnergy]
        have hsum_zero :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
                (L i k) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
          rw [hdiag i k hki]
          norm_num
        rw [hsum_zero, add_zero]
      rw [p35HadamardMeasure]
      simp_rw [henergy_eq]
      exact div_self hprod_diag_pos.ne'
  have hscale_diag : ∀ i,
      p35DiagSquare (p35ScaleRows s L) i =
        (s i) ^ 2 * p35DiagSquare L i := by
    intro i
    simp only [p35DiagSquare, p35ScaleRows]
    ring
  have hscale_row : ∀ i,
      p35RowEnergy (p35ScaleRows s L) i =
        (s i) ^ 2 * p35RowEnergy L i := by
    intro i
    simp only [p35RowEnergy, p35DiagSquare, p35ScaleRows]
    simp_rw [mul_pow]
    rw [mul_add, Finset.mul_sum]
  have hscale_prod_pos : 0 < ∏ i, (s i) ^ 2 := by
    apply Finset.prod_pos
    intro i _
    exact sq_pos_of_ne_zero (hs i)
  have hScale :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    rw [p35HadamardMeasure, p35HadamardMeasure]
    simp_rw [hscale_diag, hscale_row]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hscale_prod_pos.ne'
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have htail_prod_pos : ∀ m, m ≤ M → 0 < ∏ i, tailEigen m i := by
    intro m hm
    exact Finset.prod_pos fun i _ => htailPos m hm i
  have htail_prod_le_exp : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hamgm :=
      NumStability.higham14_problem14_13_amgm_prod_le_pow_sum_div_card
        hn (tailEigen m) (fun i => (htailPos m hm i).le)
    have hsum_nonneg : 0 ≤ ∑ i, tailEigen m i :=
      Finset.sum_nonneg fun i _ => (htailPos m hm i).le
    have hmean_nonneg : 0 ≤ (∑ i, tailEigen m i) / (n : ℝ) :=
      div_nonneg hsum_nonneg hnR.le
    have hmean_le :
        (∑ i, tailEigen m i) / (n : ℝ) ≤
          (n + 1 : ℝ) / (n : ℝ) := by
      exact (div_le_div_iff_of_pos_right hnR).2 (htailSum m hm)
    have hpow_mean_le :
        ((∑ i, tailEigen m i) / (n : ℝ)) ^ n ≤
          ((n + 1 : ℝ) / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ hmean_nonneg hmean_le n
    have hbase_nonneg : 0 ≤ (n + 1 : ℝ) / (n : ℝ) := by positivity
    have hbase_exp :
        (n + 1 : ℝ) / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have hadd := Real.add_one_le_exp (1 / (n : ℝ))
      have hbase_eq :
          (n + 1 : ℝ) / (n : ℝ) = 1 / (n : ℝ) + 1 := by
        field_simp
        ring
      rwa [hbase_eq]
    have hpow_exp :
        ((n + 1 : ℝ) / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc
        ((n + 1 : ℝ) / (n : ℝ)) ^ n
            ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
              pow_le_pow_left₀ hbase_nonneg hbase_exp n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) :=
          (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by
          rw [mul_one_div, div_self hnR.ne']
    exact hamgm.trans (hpow_mean_le.trans hpow_exp)
  have hmeasure_pos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasureEigen m hm]
    exact mul_pos (hlambdaMinPos m hm) (htail_prod_pos m hm)
  have hmeasure0 : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hstep_eq : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
    intro m hm
    rw [hmeasure (m + 1) (by omega), hmeasure m hm.le, hjacobi m hm]
    have hfac_pos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    field_simp
  have hstep_mono : ∀ m, m < M → measure m ≤ measure (m + 1) := by
    intro m hm
    rw [hstep_eq m hm]
    have hfac_pos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    apply (le_div_iff₀ hfac_pos).2
    have hmpos := (hmeasure_pos m hm.le).le
    nlinarith [sq_nonneg (jacobiEntry m)]
  have hmeasure0_le : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        exact (ih (by omega)).trans (hstep_mono m (by omega))
  have hMeasureLower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    rw [div_le_iff₀ (Real.exp_pos 1), hmeasureEigen m hm]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (htail_prod_le_exp m hm)
        (hlambdaMinPos m hm).le
  have hJacobi : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    exact ⟨hstep_eq m hm, hstep_mono m hm⟩
  have hKappa : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hHadPos : 0 < p35HadamardMeasure L := by
      rw [p35HadamardMeasure]
      exact div_pos hprod_diag_pos hprod_row_pos
    have hHad_le_measure : p35HadamardMeasure L ≤ measure m := by
      rw [← hmeasure0]
      exact hmeasure0_le m hm
    have hHad_div_le :
        p35HadamardMeasure L / Real.exp 1 ≤ measure m / Real.exp 1 := by
      exact (div_le_div_iff_of_pos_right (Real.exp_pos 1)).2 hHad_le_measure
    have hlambda_lower :
        p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m :=
      hHad_div_le.trans (hMeasureLower m hm)
    have hNpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [hkappa m hm]
    calc
      lambdaMax m / lambdaMin m
          ≤ (n + 1 : ℝ) / lambdaMin m :=
            (div_le_div_iff_of_pos_right (hlambdaMinPos m hm)).2
              (hlambdaMax m hm)
      _ ≤ (n + 1 : ℝ) /
            (p35HadamardMeasure L / Real.exp 1) :=
          (div_le_div_iff_of_pos_left hNpos
            (hlambdaMinPos m hm)
            (div_pos hHadPos (Real.exp_pos 1))).2 hlambda_lower
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
        field_simp
  exact ⟨hHadLe, hHadIff, hScale, hMeasureLower, hJacobi, hKappa⟩

end HighamBench
