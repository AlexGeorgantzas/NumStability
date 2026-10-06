-- Algorithms/Cholesky/AasenGrowthCh11Closure.lean
--
-- Closure of the Higham, 2nd ed., Chapter 11, Theorem 11.8 growth-factor
-- remark for Aasen's method.  Higham states that, using the fact that the
-- multipliers in Aasen's method with partial pivoting are bounded by `1`, it
-- is straightforward to show `ρ_n ≤ 4^{n-2}` for the tridiagonal middle factor
-- `T` of `P A Pᵀ = L T Lᵀ`.
--
-- Here we discharge the growth half from the `AasenSpec` factorization
-- structure plus the legitimate partial-pivoting multiplier bound
-- `|L i j| ≤ 1` (added as an explicit hypothesis, analogous to how the
-- 1×1 path assumes nonzero pivots).  We derive the exact `A = L H` recurrence
-- for `H = T Lᵀ`, prove a clean row-wise growth bound
-- `|H_{r,c}| ≤ 2^r · maxEntryNorm A` by strong induction, convert it to a
-- per-entry bound `|T_{i j}| ≤ 2^n · maxEntryNorm A`, and finish with
-- `2^n ≤ 4^{n-2}` for `n ≥ 4`.  The result is then fed into the existing
-- growth-bound plumbing.

import NumStability.Algorithms.HighamChapter11

open scoped BigOperators

namespace NumStability.Ch11Closure.Aasen

open NumStability

/-- Geometric sum of powers of two over `Finset.range m`. -/
private lemma geom_two_sum (m : ℕ) :
    ∑ k ∈ Finset.range m, (2 : ℝ) ^ k = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih]; ring

/-- Monotonicity of `2^·` on the reals. -/
private lemma pow_two_mono {a b : ℕ} (hab : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b :=
  pow_le_pow_right₀ (by norm_num) hab

/-- Scalar comparison used by the infinity-norm Aasen growth bridge.

The max-entry proof gives a `2^n` per-entry cap.  Tridiagonal row support costs
three entries, so the printed `4^(n-2)` infinity-norm cap follows directly in
the range `n ≥ 6`. -/
private lemma three_mul_two_pow_le_four_pow_sub_two {n : ℕ} (hn6 : 6 ≤ n) :
    (3 : ℝ) * 2 ^ n ≤ 4 ^ (n - 2) := by
  have h3 : (3 : ℝ) ≤ 2 ^ (n - 4) := by
    have hmono : (2 : ℝ) ^ 2 ≤ 2 ^ (n - 4) := pow_two_mono (by omega)
    norm_num at hmono
    linarith
  calc
    (3 : ℝ) * 2 ^ n ≤ 2 ^ (n - 4) * 2 ^ n :=
      mul_le_mul_of_nonneg_right h3 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    _ = 2 ^ ((n - 4) + n) := by rw [← pow_add]
    _ = 2 ^ (2 * (n - 2)) := by congr; omega
    _ = 4 ^ (n - 2) := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]

/-- **Row-wise Aasen growth bound.**  For the canonical Aasen middle factor
`H = T Lᵀ` of an identity-permutation `AasenSpec`, using `A = L H`, unit
lower-triangularity of `L`, and the partial-pivoting multiplier bound
`|L i j| ≤ 1`, every entry in row `r` of `H` obeys
`|H_{r,c}| ≤ 2^r · maxEntryNorm A`. -/
lemma aasenH_row_bound
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) :
    ∀ r : ℕ, ∀ hr : r < n, ∀ c : Fin n,
      |higham11_10_aasenH n T L ⟨r, hr⟩ c| ≤ 2 ^ r * maxEntryNorm hn A := by
  set M := maxEntryNorm hn A with hM
  have hMnn : 0 ≤ M := maxEntryNorm_nonneg hn A
  have hentry : ∀ i j : Fin n, |A i j| ≤ M := fun i j => entry_le_maxEntryNorm hn A i j
  have hprod : ∀ i k : Fin n,
      (∑ j : Fin n, L i j * higham11_10_aasenH n T L j k) = A i k :=
    higham11_8_AasenSpec_identity_aasenH_product_eq n A L T σ hspec hσ
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr c
    set i : Fin n := ⟨r, hr⟩ with hi
    have hival : i.val = r := rfl
    -- Isolate the diagonal (`j = i`) term of the row-`i` product `A = L H`.
    have hsplit :
        A i c = higham11_10_aasenH n T L i c
          + ∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c := by
      have h1 :
          (∑ j : Fin n, L i j * higham11_10_aasenH n T L j c)
            = L i i * higham11_10_aasenH n T L i c
              + ∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c :=
        (Finset.add_sum_erase Finset.univ
          (fun j => L i j * higham11_10_aasenH n T L j c) (Finset.mem_univ i)).symm
      rw [hspec.L_diag i, one_mul] at h1
      rw [← h1]; exact (hprod i c).symm
    -- Per-term bound for the off-diagonal part.
    have hterm : ∀ j ∈ Finset.univ.erase i,
        |L i j * higham11_10_aasenH n T L j c|
          ≤ (if j.val < r then (2 : ℝ) ^ j.val * M else 0) := by
      intro j hj
      by_cases hjr : j.val < r
      · rw [if_pos hjr, abs_mul]
        have hL : |L i j| ≤ 1 := hmult i j
        have hH : |higham11_10_aasenH n T L j c| ≤ 2 ^ j.val * M :=
          ih j.val hjr j.isLt c
        calc |L i j| * |higham11_10_aasenH n T L j c|
            ≤ 1 * (2 ^ j.val * M) :=
              mul_le_mul hL hH (abs_nonneg _) (by norm_num)
          _ = 2 ^ j.val * M := by ring
      · rw [if_neg hjr]
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have hjine : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hlt : i.val < j.val := by omega
        have hLzero : L i j = 0 := hspec.L_upper_zero i j hlt
        rw [hLzero]; simp
    -- Nonnegativity of the majorising summand.
    have hfnn : ∀ j : Fin n, 0 ≤ (if j.val < r then (2 : ℝ) ^ j.val * M else 0) := by
      intro j
      split_ifs with h
      · exact mul_nonneg (by positivity) hMnn
      · exact le_refl 0
    -- Evaluate the majorising sum as a geometric series.
    have hcast : ∀ j : Fin n,
        (if j.val < r then (2 : ℝ) ^ j.val * M else 0)
          = (if j.val < r then (2 : ℝ) ^ j.val else 0) * M := by
      intro j; split_ifs with h
      · rfl
      · rw [zero_mul]
    have hfilter : (Finset.range n).filter (fun k => k < r) = Finset.range r := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hgeom :
        (∑ j : Fin n, (if j.val < r then (2 : ℝ) ^ j.val else 0)) = 2 ^ r - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k < r then (2 : ℝ) ^ k else 0) n,
        ← Finset.sum_filter, hfilter]
      exact geom_two_sum r
    have hSumMaj :
        (∑ j : Fin n, (if j.val < r then (2 : ℝ) ^ j.val * M else 0)) = (2 ^ r - 1) * M := by
      rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Finset.sum_mul, hgeom]
    have hSum_le :
        (∑ j ∈ Finset.univ.erase i, |L i j * higham11_10_aasenH n T L j c|)
          ≤ (2 ^ r - 1) * M := by
      calc
        (∑ j ∈ Finset.univ.erase i, |L i j * higham11_10_aasenH n T L j c|)
            ≤ ∑ j ∈ Finset.univ.erase i, (if j.val < r then (2 : ℝ) ^ j.val * M else 0) :=
              Finset.sum_le_sum hterm
        _ ≤ ∑ j : Fin n, (if j.val < r then (2 : ℝ) ^ j.val * M else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                (fun j _ _ => hfnn j)
        _ = (2 ^ r - 1) * M := hSumMaj
    -- Assemble the row bound.
    have htri :
        |A i c - ∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c|
          ≤ |A i c|
            + |∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c| := by
      have h := abs_add_le (A i c)
        (-(∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c))
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    have hHeq :
        higham11_10_aasenH n T L i c
          = A i c - ∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c := by
      linarith [hsplit]
    calc
      |higham11_10_aasenH n T L i c|
          = |A i c - ∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c| := by
            rw [hHeq]
      _ ≤ |A i c|
            + |∑ j ∈ Finset.univ.erase i, L i j * higham11_10_aasenH n T L j c| := htri
      _ ≤ M + ∑ j ∈ Finset.univ.erase i, |L i j * higham11_10_aasenH n T L j c| :=
            add_le_add (hentry i c) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ M + (2 ^ r - 1) * M := by linarith [hSum_le]
      _ = 2 ^ r * M := by ring

/-- **Per-entry Aasen tridiagonal growth bound.**  Every entry of the Aasen
middle factor `T` is bounded by `2^n · maxEntryNorm A`, derived from the
row-wise `H = T Lᵀ` bound together with the tridiagonal band, the symmetry of
`T`, and the subdiagonal identity `H_{i+1,i} = T_{i+1,i}`. -/
lemma aasenT_entry_bound
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) :
    ∀ i j : Fin n, |T i j| ≤ 2 ^ n * maxEntryNorm hn A := by
  set M := maxEntryNorm hn A with hM
  have hMnn : 0 ≤ M := maxEntryNorm_nonneg hn A
  have hrow := aasenH_row_bound n hn A L T σ hspec hσ hmult
  have hsub := higham11_8_AasenSpec_identity_aasenH_subdiagonal_eq_T n A L T σ hspec
  -- `|H_{r,c}| ≤ 2^r M ≤ 2^n M` for any row `r`.
  have hrow_n : ∀ (r : ℕ) (hr : r < n) (c : Fin n),
      |higham11_10_aasenH n T L ⟨r, hr⟩ c| ≤ 2 ^ n * M := by
    intro r hr c
    exact (hrow r hr c).trans
      (mul_le_mul_of_nonneg_right (pow_two_mono (le_of_lt hr)) hMnn)
  intro i j
  -- Off-band entries vanish.
  by_cases hband : i.val + 1 < j.val ∨ j.val + 1 < i.val
  · rw [hspec.T_tridiag.2 i j hband, abs_zero]
    positivity
  · push_neg at hband
    obtain ⟨hb1, hb2⟩ := hband
    -- `|i.val - j.val| ≤ 1`.
    rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
    · -- superdiagonal: `j.val = i.val + 1`.
      have hjnext : j.val = i.val + 1 := by omega
      have hsym : T i j = T j i := hspec.T_tridiag.1 i j
      have hHij : higham11_10_aasenH n T L j i = T j i := hsub i j hjnext
      have : |T i j| = |higham11_10_aasenH n T L j i| := by rw [hsym, hHij]
      rw [this]
      have := hrow_n j.val j.isLt i
      simpa using this
    · -- diagonal.
      have hij : i = j := Fin.ext heq
      subst hij
      by_cases hi0 : i.val = 0
      · -- `T_{0,0} = H_{0,0}`.
        have hdiag :
            higham11_10_aasenH n T L i i
              = T i i * L i i
                + ∑ k ∈ Finset.univ.erase i, T i k * L i k :=
          (Finset.add_sum_erase Finset.univ (fun k => T i k * L i k)
            (Finset.mem_univ i)).symm
        have herase0 : (∑ k ∈ Finset.univ.erase i, T i k * L i k) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k ≠ i := Finset.ne_of_mem_erase hk
          have hkival : k.val ≠ i.val := fun h => hki (Fin.ext h)
          have : i.val < k.val := by omega
          rw [hspec.L_upper_zero i k this, mul_zero]
        rw [herase0, add_zero, hspec.L_diag i, mul_one] at hdiag
        have : |T i i| = |higham11_10_aasenH n T L i i| := by rw [hdiag]
        rw [this]
        have := hrow_n i.val i.isLt i
        simpa using this
      · -- `i.val ≥ 1`: `T_{i,i} = H_{i,i} - T_{i,i-1} L_{i,i-1}`.
        have hipos : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
        have hple : i.val - 1 < n := by omega
        set p : Fin n := ⟨i.val - 1, hple⟩ with hp
        have hpval : p.val = i.val - 1 := rfl
        have hpi : p ≠ i := by
          intro h; apply hi0; have := congrArg Fin.val h; simp [hpval] at this; omega
        have hpmem : p ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hpi, Finset.mem_univ p⟩
        have hdiag :
            higham11_10_aasenH n T L i i
              = T i i * L i i
                + ∑ k ∈ Finset.univ.erase i, T i k * L i k :=
          (Finset.add_sum_erase Finset.univ (fun k => T i k * L i k)
            (Finset.mem_univ i)).symm
        have hsingle :
            (∑ k ∈ Finset.univ.erase i, T i k * L i k) = T i p * L i p := by
          apply Finset.sum_eq_single_of_mem p hpmem
          intro k hk hkp
          have hki : k ≠ i := Finset.ne_of_mem_erase hk
          have hkival : k.val ≠ i.val := fun h => hki (Fin.ext h)
          have hkpval : k.val ≠ p.val := fun h => hkp (Fin.ext h)
          have hkp1 : k.val ≠ i.val - 1 := by rw [hpval] at hkpval; exact hkpval
          rcases Nat.lt_or_ge k.val i.val with hlo | hhi
          · -- `k.val ≤ i.val - 2`: band kills `T i k`.
            have hbandk : k.val + 1 < i.val := by omega
            rw [hspec.T_tridiag.2 i k (Or.inr hbandk), zero_mul]
          · -- `k.val ≥ i.val + 1`: upper-triangularity kills `L i k`.
            have : i.val < k.val := by omega
            rw [hspec.L_upper_zero i k this, mul_zero]
        rw [hsingle, hspec.L_diag i, mul_one] at hdiag
        -- `T i p = H i p`, since `i.val = p.val + 1`.
        have hpnext : i.val = p.val + 1 := by rw [hpval]; omega
        have hTip : T i p = higham11_10_aasenH n T L i p := (hsub p i hpnext).symm
        have hTii : T i i = higham11_10_aasenH n T L i i - T i p * L i p := by
          linarith [hdiag]
        have hbound :
            |T i i| ≤ |higham11_10_aasenH n T L i i| + |higham11_10_aasenH n T L i p| := by
          have hstep : |T i i|
              ≤ |higham11_10_aasenH n T L i i| + |T i p| * |L i p| := by
            rw [hTii]
            calc |higham11_10_aasenH n T L i i - T i p * L i p|
                ≤ |higham11_10_aasenH n T L i i| + |T i p * L i p| := by
                  have h := abs_add_le (higham11_10_aasenH n T L i i) (-(T i p * L i p))
                  rw [abs_neg] at h
                  simpa [sub_eq_add_neg] using h
              _ = |higham11_10_aasenH n T L i i| + |T i p| * |L i p| := by rw [abs_mul]
          have hLp : |L i p| ≤ 1 := hmult i p
          have hmul : |T i p| * |L i p| ≤ |T i p| := by
            calc |T i p| * |L i p| ≤ |T i p| * 1 :=
                  mul_le_mul_of_nonneg_left hLp (abs_nonneg _)
              _ = |T i p| := mul_one _
          have hTipabs : |T i p| = |higham11_10_aasenH n T L i p| := by rw [hTip]
          calc |T i i| ≤ |higham11_10_aasenH n T L i i| + |T i p| * |L i p| := hstep
            _ ≤ |higham11_10_aasenH n T L i i| + |T i p| := by linarith [hmul]
            _ = |higham11_10_aasenH n T L i i| + |higham11_10_aasenH n T L i p| := by
                rw [hTipabs]
        -- Both `H` entries are in row `i.val`, bounded by `2^{i.val} M`.
        have hHii : |higham11_10_aasenH n T L i i| ≤ 2 ^ i.val * M := hrow i.val i.isLt i
        have hHip : |higham11_10_aasenH n T L i p| ≤ 2 ^ i.val * M := hrow i.val i.isLt p
        have hsum2 : |T i i| ≤ 2 ^ i.val * M + 2 ^ i.val * M :=
          le_trans hbound (add_le_add hHii hHip)
        have hpow : 2 ^ i.val * M + 2 ^ i.val * M ≤ 2 ^ n * M := by
          have : (2 : ℝ) ^ i.val + 2 ^ i.val = 2 ^ (i.val + 1) := by ring
          calc 2 ^ i.val * M + 2 ^ i.val * M
              = (2 ^ i.val + 2 ^ i.val) * M := by ring
            _ = 2 ^ (i.val + 1) * M := by rw [this]
            _ ≤ 2 ^ n * M :=
                mul_le_mul_of_nonneg_right (pow_two_mono (by omega)) hMnn
        exact le_trans hsum2 hpow
    · -- subdiagonal: `i.val = j.val + 1`.
      have hinext : i.val = j.val + 1 := by omega
      have hHij : higham11_10_aasenH n T L i j = T i j := hsub j i hinext
      have : |T i j| = |higham11_10_aasenH n T L i j| := by rw [hHij]
      rw [this]
      have := hrow_n i.val i.isLt j
      simpa using this

/-- **Higham, 2nd ed., Chapter 11, Theorem 11.8 growth remark (max-entry form).**
For an identity-permutation Aasen factorization `A = L T Lᵀ` with unit
lower-triangular `L` whose multipliers satisfy `|L i j| ≤ 1` (partial
pivoting), the symmetric tridiagonal middle factor `T` obeys the printed
growth bound `maxEntryNorm T ≤ 4^{n-2} · maxEntryNorm A` for `n ≥ 4`. -/
theorem higham11_8_aasen_maxEntryNorm_T_le_printed_mul_maxEntryNorm
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) (hn4 : 4 ≤ n) :
    maxEntryNorm hn T ≤ (4 : ℝ) ^ (n - 2) * maxEntryNorm hn A := by
  have hle : maxEntryNorm hn T ≤ 2 ^ n * maxEntryNorm hn A :=
    maxEntryNorm_le_of_entry_le_bound hn T _
      (aasenT_entry_bound n hn A L T σ hspec hσ hmult)
  refine hle.trans ?_
  apply mul_le_mul_of_nonneg_right _ (maxEntryNorm_nonneg hn A)
  have h4 : (4 : ℝ) ^ (n - 2) = 2 ^ (2 * (n - 2)) := by
    rw [pow_mul]; norm_num
  rw [h4]
  exact pow_two_mono (by omega)

/-- Infinity-norm form of the Aasen growth estimate in the range where the
existing per-entry proof plus tridiagonal row support fits inside Higham's
printed `4^(n-2)` factor.  This is deliberately stated with `6 ≤ n`; the
all-dimension closure above is the max-entry result. -/
theorem higham11_8_aasen_infNorm_T_le_printed_mul_infNorm_of_multiplier_bound
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) (hn6 : 6 ≤ n) :
    infNorm T ≤ (4 : ℝ) ^ (n - 2) * infNorm A := by
  have hA_nonneg : 0 ≤ infNorm A := infNorm_nonneg A
  have hTmax : maxEntryNorm hn T ≤ (2 : ℝ) ^ n * infNorm A := by
    refine maxEntryNorm_le_of_entry_le_bound hn T ((2 : ℝ) ^ n * infNorm A) ?_
    intro i j
    exact (aasenT_entry_bound n hn A L T σ hspec hσ hmult i j).trans
      (mul_le_mul_of_nonneg_left (maxEntryNorm_le_infNorm hn A)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
  calc
    infNorm T ≤ (3 : ℝ) * maxEntryNorm hn T :=
      higham11_8_infNorm_le_three_mul_maxEntryNorm_of_isTridiagonal
        n hn T hspec.T_tridiag.2
    _ ≤ (3 : ℝ) * ((2 : ℝ) ^ n * infNorm A) :=
      mul_le_mul_of_nonneg_left hTmax (by norm_num : (0 : ℝ) ≤ 3)
    _ = ((3 : ℝ) * 2 ^ n) * infNorm A := by ring
    _ ≤ ((4 : ℝ) ^ (n - 2)) * infNorm A :=
      mul_le_mul_of_nonneg_right (three_mul_two_pow_le_four_pow_sub_two hn6) hA_nonneg
    _ = (4 : ℝ) ^ (n - 2) * infNorm A := by ring

/-- **Growth-bound plumbing feed.**  With the multiplier bound `|L i j| ≤ 1`
discharging the growth half, the printed Aasen growth-factor predicate
`ρ_n ≤ 4^{n-2}` holds without assuming any separate growth cap. -/
theorem higham11_8_aasen_aasenGrowthBound_of_multiplier_bound
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) (hn4 : 4 ≤ n)
    (hA : 0 < maxEntryNorm hn A) :
    higham11_8_aasenGrowthBound n
      (higham11_8_aasenGrowthFactor (maxEntryNorm hn T) (maxEntryNorm hn A)) :=
  higham11_8_aasenGrowthBound_of_maxEntryNorm_le_printed_mul_maxEntryNorm n hn T A hA
    (higham11_8_aasen_maxEntryNorm_T_le_printed_mul_maxEntryNorm
      n hn A L T σ hspec hσ hmult hn4)

/-- Infinity-norm growth-bound plumbing feed for `n ≥ 6`.  This supplies the
source-norm growth predicate used by exact-`T_hat` Aasen callers whenever the
matrix dimension is large enough for the tridiagonal row-support conversion to
fit inside the printed factor. -/
theorem higham11_8_aasen_infNormGrowthBound_of_multiplier_bound
    (n : ℕ) (hn : 0 < n) (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n)
    (hspec : AasenSpec n A L T σ) (hσ : ∀ i : Fin n, σ i = i)
    (hmult : ∀ i j : Fin n, |L i j| ≤ 1) (hn6 : 6 ≤ n)
    (hA : 0 < infNorm A) :
    higham11_8_aasenGrowthBound n
      (higham11_8_aasenGrowthFactor (infNorm T) (infNorm A)) :=
  higham11_8_aasenGrowthBound_of_infNorm_le_printed_mul_infNorm n T A hA
    (higham11_8_aasen_infNorm_T_le_printed_mul_infNorm_of_multiplier_bound
      n hn A L T σ hspec hσ hmult hn6)

end NumStability.Ch11Closure.Aasen
