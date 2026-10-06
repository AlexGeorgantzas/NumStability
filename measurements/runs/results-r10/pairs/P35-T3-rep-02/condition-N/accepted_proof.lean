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
  have hdiag_sq_pos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    simp only [p35DiagSquare]
    nlinarith [hLdiag i, sq_nonneg (L i i)]
  have hrow_pos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    rw [p35RowEnergy]
    exact add_pos_of_pos_of_nonneg (hdiag_sq_pos i)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hdiag_le_row : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    rw [p35RowEnergy]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hprod_diag_pos : 0 < ∏ i, p35DiagSquare L i := by
    exact Finset.prod_pos fun i _ => hdiag_sq_pos i
  have hprod_row_pos : 0 < ∏ i, p35RowEnergy L i := by
    exact Finset.prod_pos fun i _ => hrow_pos i
  have hprod_le : (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i := by
    exact Finset.prod_le_prod (fun i _ => (hdiag_sq_pos i).le)
      (fun i _ => hdiag_le_row i)
  have hhad_pos : 0 < p35HadamardMeasure L := by
    rw [p35HadamardMeasure]
    positivity
  have hhad_le : p35HadamardMeasure L ≤ 1 := by
    rw [p35HadamardMeasure, div_le_one hprod_row_pos]
    exact hprod_le
  have henergy_eq_iff (i : Fin n) :
      p35RowEnergy L i = p35DiagSquare L i ↔
        ∀ k, k.val < i.val → L i k = 0 := by
    constructor
    · intro h k hk
      have hsum :
          (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val), (L i k) ^ 2) = 0 := by
        rw [p35RowEnergy] at h
        linarith
      have hkmem : k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ k, ?_⟩
        change k.val < i.val
        exact hk
      have hsquare : (L i k) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (L i j))).mp hsum k hkmem
      nlinarith [sq_nonneg (L i k)]
    · intro h
      rw [p35RowEnergy]
      have : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
          (L i k) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [h k hk]
      rw [this, add_zero]
  have hhad_eq_iff :
      p35HadamardMeasure L = 1 ↔ p35IsDiagonalCholesky L := by
    constructor
    · intro hmeasure_one
      have hprod_eq : (∏ i, p35DiagSquare L i) = ∏ i, p35RowEnergy L i := by
        rw [p35HadamardMeasure, div_eq_one_iff_eq (ne_of_gt hprod_row_pos)] at hmeasure_one
        exact hmeasure_one
      intro i k hk
      have hrow_eq : p35RowEnergy L i = p35DiagSquare L i := by
        by_contra hne
        have hstrict : p35DiagSquare L i < p35RowEnergy L i :=
          lt_of_le_of_ne (hdiag_le_row i) (Ne.symm hne)
        have hstrict_prod : (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod
          · intro j _
            exact hdiag_sq_pos j
          · intro j _
            exact hdiag_le_row j
          · exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact (ne_of_lt hstrict_prod) hprod_eq
      exact (henergy_eq_iff i).mp hrow_eq k hk
    · intro hdiagonal
      rw [p35HadamardMeasure]
      have heq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        exact (henergy_eq_iff i).mpr (hdiagonal i)
      simp_rw [heq]
      exact div_self (ne_of_gt hprod_diag_pos)
  have hscale_diag (i : Fin n) :
      p35DiagSquare (p35ScaleRows s L) i = s i ^ 2 * p35DiagSquare L i := by
    simp only [p35DiagSquare, p35ScaleRows]
    ring
  have hscale_row (i : Fin n) :
      p35RowEnergy (p35ScaleRows s L) i = s i ^ 2 * p35RowEnergy L i := by
    simp only [p35RowEnergy, p35ScaleRows, p35DiagSquare]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    ring
  have hscale :
      p35HadamardMeasure (p35ScaleRows s L) = p35HadamardMeasure L := by
    rw [p35HadamardMeasure, p35HadamardMeasure]
    simp_rw [hscale_diag, hscale_row, Finset.prod_mul_distrib]
    have hscale_prod_ne : (∏ i, s i ^ 2) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact pow_ne_zero _ (hs i)
    field_simp
  have hmeasure_zero : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), p35HadamardMeasure, hdetH, hdiag0]
  have hmeasure_pos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasureEigen m hm]
    exact mul_pos (hlambdaMinPos m hm)
      (Finset.prod_pos fun i _ => htailPos m hm i)
  have htail_prod_le_exp : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hamgm := Real.geom_mean_le_arith_mean Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (tailEigen m)
      (fun _ _ => zero_le_one) (by simpa using hnR)
      (fun i _ => (htailPos m hm i).le)
    have havg : (∑ i, tailEigen m i) / (n : ℝ) ≤ (n + 1 : ℝ) / n := by
      exact div_le_div_of_nonneg_right (htailSum m hm) hnR.le
    have hroot :
        ((∏ i, tailEigen m i) : ℝ) ^ ((n : ℝ)⁻¹) ≤ (n + 1 : ℝ) / n := by
      calc
        ((∏ i, tailEigen m i) : ℝ) ^ ((n : ℝ)⁻¹) ≤
            (∑ i, tailEigen m i) / (n : ℝ) := by simpa using hamgm
        _ ≤ (n + 1 : ℝ) / n := havg
    have hbase_nonneg : (0 : ℝ) ≤ (n + 1 : ℝ) / n := by positivity
    have hprod_pos : 0 < ∏ i, tailEigen m i :=
      Finset.prod_pos fun i _ => htailPos m hm i
    have hprod_le_pow :
        (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / n) ^ n := by
      have hp := pow_le_pow_left₀ (Real.rpow_nonneg hprod_pos.le _) hroot n
      calc
        (∏ i, tailEigen m i) =
            (((∏ i, tailEigen m i) : ℝ) ^ ((n : ℝ)⁻¹)) ^ n := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hprod_pos.le]
              field_simp
              simp
        _ ≤ ((n + 1 : ℝ) / n) ^ n := hp
    have hbase_exp : (n + 1 : ℝ) / n ≤ Real.exp ((n : ℝ)⁻¹) := by
      calc
        (n + 1 : ℝ) / n = (n : ℝ)⁻¹ + 1 := by field_simp; ring
        _ ≤ Real.exp ((n : ℝ)⁻¹) := Real.add_one_le_exp _
    calc
      (∏ i, tailEigen m i) ≤ ((n + 1 : ℝ) / n) ^ n := hprod_le_pow
      _ ≤ (Real.exp ((n : ℝ)⁻¹)) ^ n :=
        pow_le_pow_left₀ hbase_nonneg hbase_exp n
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
  have hlambda_lower : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    have hp := htail_prod_le_exp m hm
    have hlpos := hlambdaMinPos m hm
    rw [hmeasureEigen m hm]
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  have hjacobi_step : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.le_of_lt hm
    have hsuccM : m + 1 ≤ M := hm
    have hfactor : 0 < 1 - (jacobiEntry m) ^ 2 := sub_pos.mpr (hjacobiSmall m hm)
    have hdpos := hdiagPos m hmM
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hsuccM, hmeasure m hmM, hjacobi m hm]
      field_simp
    refine ⟨heq, ?_⟩
    rw [heq, le_div_iff₀ hfactor]
    have hmp := hmeasure_pos m hmM
    nlinarith [sq_nonneg (jacobiEntry m)]
  have hmeasure_mono_from_zero : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        have hm_lt : m < M := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hm_lt)).trans (hjacobi_step m hm_lt).2
  have hkappa_bound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hlpos := hlambdaMinPos m hm
    have hexp := Real.exp_pos 1
    have hinitial : p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      rw [← hmeasure_zero]
      exact (div_le_div_of_nonneg_right (hmeasure_mono_from_zero m hm) hexp.le).trans
        (hlambda_lower m hm)
    rw [hkappa m hm]
    have hfirst : lambdaMax m / lambdaMin m ≤ (n + 1 : ℝ) / lambdaMin m := by
      exact div_le_div_of_nonneg_right (hlambdaMax m hm) hlpos.le
    have hden : 0 < p35HadamardMeasure L / Real.exp 1 := div_pos hhad_pos hexp
    have hn1 : (0 : ℝ) ≤ n + 1 := by positivity
    have hsecond : (n + 1 : ℝ) / lambdaMin m ≤
        (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) := by
      rw [div_le_div_iff₀ hlpos hden]
      nlinarith
    calc
      lambdaMax m / lambdaMin m ≤ (n + 1 : ℝ) / lambdaMin m := hfirst
      _ ≤ (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) := hsecond
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by field_simp
  exact ⟨hhad_le, hhad_eq_iff, hscale, hlambda_lower, hjacobi_step, hkappa_bound⟩

end HighamBench
