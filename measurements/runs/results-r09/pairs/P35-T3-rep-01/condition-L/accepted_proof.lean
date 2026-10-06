import HighamBench.P35Definitions

namespace HighamBench

open scoped BigOperators

private lemma p35_tail_prod_le_exp_one {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i, z i ≤ (n + 1 : ℝ)) :
    ∏ i, z i ≤ Real.exp 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (1 / (n : ℝ)) := by
    intro i _
    positivity
  have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (1 / (n : ℝ))) z hw hw' (fun i _ => hz i)
  have havg : ∑ i : Fin n, (1 / (n : ℝ)) * z i ≤ 1 + 1 / (n : ℝ) := by
    rw [← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
    field_simp
  have hroot : ∏ i, z i ^ (1 / (n : ℝ)) ≤ 1 + 1 / (n : ℝ) :=
    hgm.trans havg
  have hrootnn : 0 ≤ ∏ i, z i ^ (1 / (n : ℝ)) := by
    apply Finset.prod_nonneg
    intro i _
    exact Real.rpow_nonneg (hz i) _
  have hpow : (∏ i, z i ^ (1 / (n : ℝ))) ^ n = ∏ i, z i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (z i ^ (1 / (n : ℝ))) n, ← Real.rpow_mul (hz i)]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  have hbasepos : 0 ≤ 1 + 1 / (n : ℝ) := by positivity
  have hprod_base : ∏ i, z i ≤ (1 + 1 / (n : ℝ)) ^ n := by
    rw [← hpow]
    exact pow_le_pow_left₀ hrootnn hroot n
  have hbase_exp : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (n : ℝ))
  have hpow_exp : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
    calc
      (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / (n : ℝ)) ^ n :=
        pow_le_pow_left₀ hbasepos hbase_exp n
      _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) :=
        (Real.exp_nat_mul _ n).symm
      _ = Real.exp 1 := by rw [mul_one_div, div_self hnR.ne']
  exact hprod_base.trans hpow_exp

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
  have hdpos : ∀ i, 0 < p35DiagSquare L i := by
    intro i
    exact sq_pos_of_pos (hLdiag i)
  have hrge : ∀ i, p35DiagSquare L i ≤ p35RowEnergy L i := by
    intro i
    simp only [p35RowEnergy]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => sq_nonneg (L i k)))
  have hrpos : ∀ i, 0 < p35RowEnergy L i := by
    intro i
    exact lt_of_lt_of_le (hdpos i) (hrge i)
  have hprodDpos : 0 < ∏ i, p35DiagSquare L i :=
    Finset.prod_pos (fun i _ => hdpos i)
  have hprodRpos : 0 < ∏ i, p35RowEnergy L i :=
    Finset.prod_pos (fun i _ => hrpos i)
  have hprodle : (∏ i, p35DiagSquare L i) ≤ ∏ i, p35RowEnergy L i :=
    Finset.prod_le_prod (fun i _ => (hdpos i).le) (fun i _ => hrge i)
  constructor
  · rw [p35HadamardMeasure]
    exact (div_le_one hprodRpos).2 hprodle
  constructor
  · rw [p35HadamardMeasure, div_eq_one_iff_eq hprodRpos.ne']
    constructor
    · intro hprod i k hk
      have hroweq : p35DiagSquare L i = p35RowEnergy L i := by
        apply le_antisymm (hrge i)
        apply not_lt.mp
        intro hstrict
        have hprodstrict :
            (∏ j, p35DiagSquare L j) < ∏ j, p35RowEnergy L j := by
          apply Finset.prod_lt_prod (fun j _ => hdpos j) (fun j _ => hrge j)
          exact ⟨i, Finset.mem_univ i, hstrict⟩
        exact hprodstrict.ne hprod
      have hsumzero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), (L i j) ^ 2 = 0 := by
        simp only [p35RowEnergy] at hroweq
        linarith
      have hallzero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_hj : j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val)) =>
            sq_nonneg (L i j))).mp hsumzero
      have hkmem :
          k ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      exact sq_eq_zero_iff.mp (hallzero k hkmem)
    · intro hdiag
      have hroweq : ∀ i, p35RowEnergy L i = p35DiagSquare L i := by
        intro i
        simp only [p35RowEnergy]
        have hsumzero :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val), (L i k) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hkmem
          have hk : k.val < i.val := (Finset.mem_filter.mp hkmem).2
          rw [hdiag i k hk, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        rw [hsumzero, add_zero]
      rw [Finset.prod_congr rfl (fun i _ => hroweq i)]
  constructor
  · have hdscale : ∀ i,
        p35DiagSquare (p35ScaleRows s L) i = (s i) ^ 2 * p35DiagSquare L i := by
      intro i
      simp [p35DiagSquare, p35ScaleRows, mul_pow]
    have hrscale : ∀ i,
        p35RowEnergy (p35ScaleRows s L) i = (s i) ^ 2 * p35RowEnergy L i := by
      intro i
      simp only [p35RowEnergy, hdscale, p35ScaleRows, mul_pow]
      rw [← Finset.mul_sum]
      ring
    have hsquares : (∏ i, (s i) ^ 2) ≠ 0 := by
      apply (Finset.prod_ne_zero_iff).2
      intro i _
      exact pow_ne_zero 2 (hs i)
    simp only [p35HadamardMeasure]
    rw [Finset.prod_congr rfl (fun i _ => hdscale i)]
    rw [Finset.prod_congr rfl (fun i _ => hrscale i)]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hsquares
  have hlower : ∀ m, m ≤ M → measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    have hprod : ∏ i, tailEigen m i ≤ Real.exp 1 :=
      p35_tail_prod_le_exp_one hn (tailEigen m)
        (fun i => (htailPos m hm i).le) (htailSum m hm)
    have hexppos : 0 < Real.exp 1 := Real.exp_pos 1
    rw [hmeasureEigen m hm, mul_div_assoc]
    have hratio : (∏ i, tailEigen m i) / Real.exp 1 ≤ 1 :=
      (div_le_one hexppos).mpr hprod
    nlinarith [hlambdaMinPos m hm]
  constructor
  · exact hlower
  have hdetPos : 0 < detH := by
    rw [hdetH]
    exact Finset.prod_pos fun i _ => sq_pos_of_pos (hLdiag i)
  have hmeasure0 : measure 0 = p35HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hhadPos : 0 < p35HadamardMeasure L := by
    rw [← hmeasure0, hmeasure 0 (Nat.zero_le M)]
    exact div_pos hdetPos (hdiagPos 0 (Nat.zero_le M))
  have hjac : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
        measure m ≤ measure (m + 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.le_of_lt hm
    have hm1M : m + 1 ≤ M := by omega
    have hdm : 0 < diagProduct m := hdiagPos m hmM
    have hc : 0 < 1 - (jacobiEntry m) ^ 2 := sub_pos.mpr (hjacobiSmall m hm)
    have hrec : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1M, hmeasure m hmM, hjacobi m hm]
      field_simp
    refine ⟨hrec, ?_⟩
    rw [hrec]
    apply (le_div_iff₀ hc).2
    calc
      measure m * (1 - (jacobiEntry m) ^ 2) =
          measure m - measure m * (jacobiEntry m) ^ 2 := by ring
      _ ≤ measure m := sub_le_self _ (mul_nonneg
        (le_of_lt (by rw [hmeasure m hmM]; positivity)) (sq_nonneg _))
  have hmono0 : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
        exact ih (Nat.le_trans (Nat.le_succ m) hm) |>.trans
          ((hjac m (Nat.lt_of_succ_le hm)).2)
  have hkappaBound : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by
    intro m hm
    have hmin : p35HadamardMeasure L / Real.exp 1 ≤ lambdaMin m := by
      calc
        p35HadamardMeasure L / Real.exp 1 = measure 0 / Real.exp 1 := by
          rw [hmeasure0]
        _ ≤ measure m / Real.exp 1 :=
          (div_le_div_iff_of_pos_right (Real.exp_pos 1)).2 (hmono0 m hm)
        _ ≤ lambdaMin m := hlower m hm
    rw [hkappa m hm]
    calc
      lambdaMax m / lambdaMin m ≤ (n + 1 : ℝ) / lambdaMin m :=
        div_le_div_of_nonneg_right (hlambdaMax m hm) (le_of_lt (hlambdaMinPos m hm))
      _ ≤ (n + 1 : ℝ) / (p35HadamardMeasure L / Real.exp 1) :=
        div_le_div_of_nonneg_left (by positivity)
          (div_pos hhadPos (Real.exp_pos 1)) hmin
      _ = (n + 1 : ℝ) * Real.exp 1 / p35HadamardMeasure L := by field_simp
  constructor
  · exact hjac
  · exact hkappaBound

end HighamBench
