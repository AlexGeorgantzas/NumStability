import NumStability.Source.Higham.Chapter22.VandermondeSystems

/-!
# Higham Chapter 22: monomial residual bounds

Canonical source-correspondence owner for the closed monomial-basis
factorization and residual bounds completing Corollary 22.7.
-/

namespace NumStability

open scoped BigOperators

noncomputable def higham22ClosureComplexUpperBidiag {N : ℕ}
    (u e : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then u i else if (i : ℕ) + 1 = j then e i else 0

theorem higham22ClosureComplexUpperBidiag_mul_apply {N : ℕ}
    (u e : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (higham22ClosureComplexUpperBidiag u e * X) i j =
      u i * X i j +
        if h : (i : ℕ) + 1 < N then e i * X ⟨(i : ℕ) + 1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) + 1 < N
  · let is : Fin N := ⟨(i : ℕ) + 1, h⟩
    have his : is ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [is] at this
    simp only [higham22ClosureComplexUpperBidiag]
    rw [dif_pos h]
    calc
      (∑ x : Fin N,
          (if i = x then u i else if (i : ℕ) + 1 = x then e i else 0) * X x j) =
          ∑ x : Fin N,
            ((if x = i then u i * X x j else 0) +
              (if x = is then e i * X x j else 0)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxi : x = i
            · subst x
              rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm his)]
              simp
            · by_cases hxs : x = is
              · subst x
                rw [if_neg (Ne.symm his), if_pos rfl, if_neg his, if_pos rfl]
                simp [is]
              · have hval : (i : ℕ) + 1 ≠ (x : ℕ) := by
                  intro heq
                  apply hxs
                  apply Fin.ext
                  simpa [is] using heq.symm
                rw [if_neg (Ne.symm hxi), if_neg hval, zero_mul,
                  if_neg hxi, if_neg hxs, zero_add]
      _ = u i * X i j + e i * X is j := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq',
          Fintype.sum_ite_eq']
      _ = _ := by rfl
  · simp only [higham22ClosureComplexUpperBidiag]
    rw [dif_neg h]
    calc
      (∑ x : Fin N,
          (if i = x then u i else if (i : ℕ) + 1 = x then e i else 0) * X x j) =
          ∑ x : Fin N, if x = i then u i * X x j else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxi : x = i
            · subst x
              simp
            · have hval : (i : ℕ) + 1 ≠ (x : ℕ) := by
                intro heq
                have hxlt : (i : ℕ) + 1 < N := heq ▸ x.isLt
                exact h hxlt
              rw [if_neg (Ne.symm hxi), if_neg hval, zero_mul, if_neg hxi]
      _ = u i * X i j := by rw [Fintype.sum_ite_eq']
      _ = _ := by ring

theorem higham22ClosureComplexUpperBidiag_mulVec_apply {N : ℕ}
    (u e : Fin N → ℂ) (z : Fin N → ℂ) (i : Fin N) :
    (higham22ClosureComplexUpperBidiag u e).mulVec z i =
      u i * z i +
        if h : (i : ℕ) + 1 < N then e i * z ⟨(i : ℕ) + 1, h⟩ else 0 := by
  rw [Matrix.mulVec, dotProduct]
  by_cases h : (i : ℕ) + 1 < N
  · let is : Fin N := ⟨(i : ℕ) + 1, h⟩
    have his : is ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      simp [is] at this
    simp only [higham22ClosureComplexUpperBidiag]
    rw [dif_pos h]
    calc
      (∑ x : Fin N,
          (if i = x then u i else if (i : ℕ) + 1 = x then e i else 0) * z x) =
          ∑ x : Fin N,
            ((if x = i then u i * z x else 0) +
              (if x = is then e i * z x else 0)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxi : x = i
            · subst x
              rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm his)]
              simp
            · by_cases hxs : x = is
              · subst x
                rw [if_neg (Ne.symm his), if_pos rfl, if_neg his, if_pos rfl]
                simp [is]
              · have hval : (i : ℕ) + 1 ≠ (x : ℕ) := by
                  intro heq
                  apply hxs
                  apply Fin.ext
                  simpa [is] using heq.symm
                rw [if_neg (Ne.symm hxi), if_neg hval, zero_mul,
                  if_neg hxi, if_neg hxs, zero_add]
      _ = u i * z i + e i * z is := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq',
          Fintype.sum_ite_eq']
      _ = _ := by rfl
  · simp only [higham22ClosureComplexUpperBidiag]
    rw [dif_neg h]
    calc
      (∑ x : Fin N,
          (if i = x then u i else if (i : ℕ) + 1 = x then e i else 0) * z x) =
          ∑ x : Fin N, if x = i then u i * z x else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxi : x = i
            · subst x
              simp
            · have hval : (i : ℕ) + 1 ≠ (x : ℕ) := by
                intro heq
                have hxlt : (i : ℕ) + 1 < N := heq ▸ x.isLt
                exact h hxlt
              rw [if_neg (Ne.symm hxi), if_neg hval, zero_mul, if_neg hxi]
      _ = u i * z i := by rw [Fintype.sum_ite_eq']
      _ = _ := by ring

noncomputable def higham22ClosureComplexUpperBidiagInvEntry {N : ℕ}
    (u e : Fin N → ℂ) (i j : Fin N) : ℂ :=
  if (j : ℕ) < i then 0
  else
    (∏ p ∈ Finset.univ.filter
      (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j), (-e p / u p)) *
      (1 / u j)

theorem higham22ClosureComplexUpperBidiagInvEntry_diag {N : ℕ}
    (u e : Fin N → ℂ) (i : Fin N) :
    higham22ClosureComplexUpperBidiagInvEntry u e i i = 1 / u i := by
  simp only [higham22ClosureComplexUpperBidiagInvEntry, lt_irrefl, if_false]
  have hempty : Finset.univ.filter
      (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < i) = ∅ := by
    ext p
    simp
  rw [hempty]
  simp

theorem higham22ClosureComplexUpperBidiagInvEntry_below {N : ℕ}
    (u e : Fin N → ℂ) (i j : Fin N) (hji : (j : ℕ) < i) :
    higham22ClosureComplexUpperBidiagInvEntry u e i j = 0 := by
  simp [higham22ClosureComplexUpperBidiagInvEntry, hji]

theorem higham22ClosureComplexUpperBidiagInvEntry_recurrence {N : ℕ}
    (u e : Fin N → ℂ) (hu : ∀ p, u p ≠ 0)
    (i j : Fin N) (hij : (i : ℕ) < j) :
    let is : Fin N := ⟨(i : ℕ) + 1, by omega⟩
    u i * higham22ClosureComplexUpperBidiagInvEntry u e i j +
      e i * higham22ClosureComplexUpperBidiagInvEntry u e is j = 0 := by
  let is : Fin N := ⟨(i : ℕ) + 1, by omega⟩
  have hnotji : ¬(j : ℕ) < i := by omega
  have hnjs : ¬(j : ℕ) < (i : ℕ) + 1 := by omega
  let S : Finset (Fin N) := Finset.univ.filter
    (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j)
  let Ss : Finset (Fin N) := Finset.univ.filter
    (fun p : Fin N => (i : ℕ) + 1 ≤ p ∧ (p : ℕ) < j)
  have hsplit : S = insert i Ss := by
    ext p
    simp only [S, Ss, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hp
      by_cases hpi : p = i
      · exact Or.inl hpi
      · right
        constructor
        · omega
        · exact hp.2
    · rintro (hpi | hp)
      · subst p
        exact ⟨le_rfl, hij⟩
      · constructor
        · omega
        · exact hp.2
  have hini : i ∉ Ss := by
    simp [Ss]
  simp only [higham22ClosureComplexUpperBidiagInvEntry, if_neg hnotji, if_neg hnjs]
  change u i * ((∏ p ∈ S, -e p / u p) * (1 / u j)) +
      e i * ((∏ p ∈ Ss, -e p / u p) * (1 / u j)) = 0
  rw [hsplit, Finset.prod_insert hini]
  field_simp [hu i]
  ring

noncomputable def higham22ClosureComplexUpperBidiagInvMatrix {N : ℕ}
    (u e : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => higham22ClosureComplexUpperBidiagInvEntry u e i j

theorem higham22ClosureComplexUpperBidiag_mul_invEntries {N : ℕ}
    (u e : Fin N → ℂ) (hu : ∀ p, u p ≠ 0) :
    higham22ClosureComplexUpperBidiag u e *
        higham22ClosureComplexUpperBidiagInvMatrix u e = 1 := by
  ext i j
  rw [higham22ClosureComplexUpperBidiag_mul_apply]
  simp only [higham22ClosureComplexUpperBidiagInvMatrix]
  by_cases hji : (j : ℕ) < i
  · rw [higham22ClosureComplexUpperBidiagInvEntry_below u e i j hji]
    by_cases hi : (i : ℕ) + 1 < N
    · rw [dif_pos hi]
      have hjs : (j : ℕ) < ((⟨(i : ℕ) + 1, hi⟩ : Fin N) : ℕ) := by
        simp
        omega
      rw [higham22ClosureComplexUpperBidiagInvEntry_below u e _ j hjs]
      simp [Matrix.one_apply, Fin.ext_iff]
      omega
    · rw [dif_neg hi]
      simp [Matrix.one_apply, Fin.ext_iff]
      omega
  · by_cases hij : i = j
    · subst j
      rw [higham22ClosureComplexUpperBidiagInvEntry_diag]
      by_cases hi : (i : ℕ) + 1 < N
      · rw [dif_pos hi]
        have hisi : (i : ℕ) < ((⟨(i : ℕ) + 1, hi⟩ : Fin N) : ℕ) := by simp
        rw [higham22ClosureComplexUpperBidiagInvEntry_below u e _ i hisi]
        simp [Matrix.one_apply, hu i]
      · rw [dif_neg hi]
        simp [Matrix.one_apply, hu i]
    · have hijlt : (i : ℕ) < j := by omega
      have hi : (i : ℕ) + 1 < N := by omega
      rw [dif_pos hi]
      have hrec := higham22ClosureComplexUpperBidiagInvEntry_recurrence
        u e hu i j hijlt
      dsimp only at hrec
      rw [hrec]
      simp [Matrix.one_apply, hij]

theorem higham22ClosureComplexUpperBidiag_inv_apply {N : ℕ}
    (u e : Fin N → ℂ) (hu : ∀ p, u p ≠ 0) (i j : Fin N) :
    (higham22ClosureComplexUpperBidiag u e)⁻¹ i j =
      higham22ClosureComplexUpperBidiagInvEntry u e i j := by
  have hinv : (higham22ClosureComplexUpperBidiag u e)⁻¹ =
      higham22ClosureComplexUpperBidiagInvMatrix u e :=
    Matrix.inv_eq_right_inv (higham22ClosureComplexUpperBidiag_mul_invEntries u e hu)
  exact congrFun (congrFun hinv i) j

theorem higham22ClosureComplexErrorProd_eq_prod :
    ∀ (m : ℕ) (δ : Fin m → ℂ),
      higham22ComplexErrorProd m δ = ∏ i : Fin m, (1 + δ i) := by
  intro m
  induction m with
  | zero =>
      intro δ
      simp [higham22ComplexErrorProd]
  | succ m ih =>
      intro δ
      rw [higham22ComplexErrorProd, Fin.prod_univ_succ, ih]

theorem higham22Closure_complex_problem22_8_mixed_product
    {N : ℕ} (eps delta : Fin N → ℂ) (i j : Fin N) (uround : ℝ)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, ‖eps p‖ ≤ uround)
    (hdelta : ∀ p, ‖delta p‖ ≤ uround)
    (hu1 : uround < 1)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff uround hu0)
      ((Finset.univ.filter
        (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j)).card + 1)) :
    ∃ η : ℂ,
      ‖η‖ ≤ gamma (FPModel.exactWithUnitRoundoff uround hu0)
        ((Finset.univ.filter
          (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j)).card + 1) ∧
      ((∏ p ∈ Finset.univ.filter
          (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) = 1 + η := by
  let S : Finset (Fin N) := Finset.univ.filter
    (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j)
  let fp := FPModel.exactWithUnitRoundoff uround hu0
  let d : Fin S.card → ℂ := fun k => delta ((S.equivFin).symm k)
  have hvalidS : gammaValid fp S.card :=
    gammaValid_mono fp (Nat.le_succ S.card) (by simpa [fp, S] using hvalid)
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (Nat.succ_le_succ (Nat.zero_le S.card))
      (by simpa [fp, S, Nat.add_comm] using hvalid)
  have hd : ∀ k, ‖d k‖ ≤ fp.u := by
    intro k
    simpa [d, fp, FPModel.exactWithUnitRoundoff] using
      hdelta (((S.equivFin).symm k).1)
  have hprodS : (∏ p ∈ S, (1 + delta p)) = ∏ k : Fin S.card, (1 + d k) := by
    calc
      (∏ p ∈ S, (1 + delta p)) = ∏ p : S, (1 + delta p.1) := by
        exact (Finset.prod_attach S (fun p => 1 + delta p)).symm
      _ = ∏ k : Fin S.card, (1 + d k) := by
        apply Fintype.prod_equiv S.equivFin
        intro p
        simp [d]
  let θ : ℂ := (∏ k : Fin S.card, (1 + d k)) - 1
  have hθraw : ‖θ‖ ≤ (1 + uround) ^ S.card - 1 := by
    have h := higham22ComplexErrorProd_sub_one_norm_le
      uround hu0 S.card d (by simpa [fp, FPModel.exactWithUnitRoundoff] using hd)
    simpa [θ, higham22ClosureComplexErrorProd_eq_prod] using h
  have hθgamma : ‖θ‖ ≤ gamma fp S.card := by
    apply hθraw.trans
    simpa using
      (one_add_pow_sub_one_le_gamma_mul_of_le_gamma fp S.card 1 hu0
        (u_le_gamma fp Nat.one_pos hvalid1) (by simpa using hvalidS))
  let α : ℂ := higham22InverseLocalError (eps j)
  have hα : ‖α‖ ≤ gamma fp 1 := by
    have h := higham22_inverseLocalError_norm_le uround hu0 hu1 (heps j)
    simpa [α, fp, gamma, FPModel.exactWithUnitRoundoff] using h
  have hepsne : 1 + eps j ≠ 0 := by
    apply higham22_one_add_ne_zero_of_norm_lt_one
    exact (heps j).trans_lt hu1
  let η : ℂ := θ + α + θ * α
  have hηγamma : ‖η‖ ≤ gamma fp (S.card + 1) := by
    calc
      ‖η‖ ≤ ‖θ‖ + ‖α‖ + ‖θ‖ * ‖α‖ := by
        dsimp [η]
        calc
          ‖θ + α + θ * α‖ ≤ ‖θ + α‖ + ‖θ * α‖ := norm_add_le _ _
          _ ≤ (‖θ‖ + ‖α‖) + ‖θ‖ * ‖α‖ := by
            rw [norm_mul]
            gcongr
            exact norm_add_le _ _
      _ ≤ gamma fp S.card + gamma fp 1 +
          gamma fp S.card * gamma fp 1 := by
        have hgS : 0 ≤ gamma fp S.card := gamma_nonneg fp hvalidS
        have hg1 : 0 ≤ gamma fp 1 := gamma_nonneg fp hvalid1
        gcongr
      _ ≤ gamma fp (S.card + 1) :=
        gamma_sum_le fp S.card 1 (by simpa [fp, S] using hvalid)
  refine ⟨η, by simpa [fp, S] using hηγamma, ?_⟩
  change ((∏ p ∈ S, (1 + delta p)) / (1 + eps j)) = 1 + η
  rw [hprodS]
  have hθeq : (∏ k : Fin S.card, (1 + d k)) = 1 + θ := by
    simp [θ]
  rw [hθeq, div_eq_mul_inv, ← higham22_one_add_inverseLocalError hepsne]
  simp only [α, η]
  ring

theorem higham22Closure_complex_problem22_8_structured_factor
    {N : ℕ} (u e eps delta : Fin N → ℂ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (heps : ∀ p, 1 + eps p ≠ 0) :
    higham22ClosureComplexUpperBidiagInvEntry
        (fun p => (1 + eps p) * u p)
        (fun p => (1 + eps p) * (1 + delta p) * e p) i j =
      ((∏ p ∈ Finset.univ.filter
          (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) * higham22ClosureComplexUpperBidiagInvEntry u e i j := by
  simp only [higham22ClosureComplexUpperBidiagInvEntry, not_lt.mpr hij, if_false]
  have hterm : ∀ p : Fin N,
      -((1 + eps p) * (1 + delta p) * e p) /
          ((1 + eps p) * u p) =
        (1 + delta p) * (-e p / u p) := by
    intro p
    field_simp [heps p]
    <;> ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  field_simp [heps j]
  <;> ring

theorem higham22Closure_complex_problem22_8_structured_difference
    {N : ℕ} (u e eps delta : Fin N → ℂ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (heps : ∀ p, 1 + eps p ≠ 0) :
    higham22ClosureComplexUpperBidiagInvEntry
          (fun p => (1 + eps p) * u p)
          (fun p => (1 + eps p) * (1 + delta p) * e p) i j -
        higham22ClosureComplexUpperBidiagInvEntry u e i j =
      (((∏ p ∈ Finset.univ.filter
          (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) - 1) * higham22ClosureComplexUpperBidiagInvEntry u e i j := by
  rw [higham22Closure_complex_problem22_8_structured_factor
    u e eps delta i j hij heps]
  ring

theorem higham22Closure_complex_problem22_8_inverse_entry_bound
    {N : ℕ} (u e eps delta : Fin N → ℂ) (i j : Fin N) (uround : ℝ)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, ‖eps p‖ ≤ uround)
    (hdelta : ∀ p, ‖delta p‖ ≤ uround)
    (hvalid : gammaValid (FPModel.exactWithUnitRoundoff uround hu0) N) :
    ‖higham22ClosureComplexUpperBidiagInvEntry
          (fun p => (1 + eps p) * u p)
          (fun p => (1 + eps p) * (1 + delta p) * e p) i j -
        higham22ClosureComplexUpperBidiagInvEntry u e i j‖ ≤
      gamma (FPModel.exactWithUnitRoundoff uround hu0) N *
        ‖higham22ClosureComplexUpperBidiagInvEntry u e i j‖ := by
  let fp := FPModel.exactWithUnitRoundoff uround hu0
  have hu1 : uround < 1 := by
    have hv := hvalid
    unfold gammaValid at hv
    dsimp [FPModel.exactWithUnitRoundoff] at hv
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le i) i.isLt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hNpos)
    have hu_le : uround ≤ (N : ℝ) * uround := by
      simpa using mul_le_mul_of_nonneg_right hN hu0
    linarith
  have heps_ne : ∀ p, 1 + eps p ≠ 0 := by
    intro p
    apply higham22_one_add_ne_zero_of_norm_lt_one
    exact (heps p).trans_lt hu1
  by_cases hij : (i : ℕ) ≤ j
  · let S : Finset (Fin N) := Finset.univ.filter
      (fun p : Fin N => (i : ℕ) ≤ p ∧ (p : ℕ) < j)
    have hSsub : S ⊂ (Finset.univ : Finset (Fin N)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro hEq
      have hjmem : j ∈ S := by simpa [hEq]
      simp [S] at hjmem
    have hcardlt : S.card < N := by
      simpa using Finset.card_lt_card hSsub
    have hcard : S.card + 1 ≤ N := by omega
    have hvalidS : gammaValid fp (S.card + 1) :=
      gammaValid_mono fp hcard (by simpa [fp] using hvalid)
    obtain ⟨η, hη, hratio⟩ := higham22Closure_complex_problem22_8_mixed_product
      eps delta i j uround hu0 heps hdelta hu1
        (by simpa [S, fp] using hvalidS)
    have hdiff := higham22Closure_complex_problem22_8_structured_difference
      u e eps delta i j hij heps_ne
    have hfactor :
        higham22ClosureComplexUpperBidiagInvEntry
              (fun p => (1 + eps p) * u p)
              (fun p => (1 + eps p) * (1 + delta p) * e p) i j -
            higham22ClosureComplexUpperBidiagInvEntry u e i j =
          η * higham22ClosureComplexUpperBidiagInvEntry u e i j := by
      rw [hdiff, hratio]
      ring
    rw [hfactor, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact hη.trans (gamma_mono fp hcard (by simpa [fp] using hvalid))
  · have hji : (j : ℕ) < i := Nat.lt_of_not_ge hij
    simp [higham22ClosureComplexUpperBidiagInvEntry, hji]

theorem higham22Closure_complex_problem22_8_matrix_inverse_bound
    {N : ℕ} (u e eps delta : Fin N → ℂ) (i j : Fin N) (uround : ℝ)
    (hu : ∀ p, u p ≠ 0)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, ‖eps p‖ ≤ uround)
    (hdelta : ∀ p, ‖delta p‖ ≤ uround)
    (hvalid : gammaValid (FPModel.exactWithUnitRoundoff uround hu0) N) :
    ‖(higham22ClosureComplexUpperBidiag
          (fun p => (1 + eps p) * u p)
          (fun p => (1 + eps p) * (1 + delta p) * e p))⁻¹ i j -
        (higham22ClosureComplexUpperBidiag u e)⁻¹ i j‖ ≤
      gamma (FPModel.exactWithUnitRoundoff uround hu0) N *
        ‖(higham22ClosureComplexUpperBidiag u e)⁻¹ i j‖ := by
  have hu1 : uround < 1 := by
    have hv := hvalid
    unfold gammaValid at hv
    dsimp [FPModel.exactWithUnitRoundoff] at hv
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le i) i.isLt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hNpos)
    have hu_le : uround ≤ (N : ℝ) * uround := by
      simpa using mul_le_mul_of_nonneg_right hN hu0
    linarith
  have hup : ∀ p, (1 + eps p) * u p ≠ 0 := by
    intro p
    apply mul_ne_zero
    · apply higham22_one_add_ne_zero_of_norm_lt_one
      exact (heps p).trans_lt hu1
    · exact hu p
  simp only [higham22ClosureComplexUpperBidiag_inv_apply _ _ hup,
    higham22ClosureComplexUpperBidiag_inv_apply _ _ hu]
  exact higham22Closure_complex_problem22_8_inverse_entry_bound
    u e eps delta i j uround hu0 heps hdelta hvalid

noncomputable def higham22ClosureMonomialStageIIDiag {n : ℕ} : Fin (n + 1) → ℂ :=
  fun _ => 1

noncomputable def higham22ClosureMonomialStageIISuper {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (k : ℕ) : Fin (n + 1) → ℂ :=
  fun i => if k ≤ (i : ℕ) ∧ (i : ℕ) < n then
    -higham22FinExtend alpha k else 0

theorem higham22Closure_exact_monomial_stageII_factor_eq_bidiag {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (k : ℕ) (hk : k < n) :
    higham22StageIIUpperFactor higham22MonomialTheta
        higham22MonomialBeta higham22MonomialGamma alpha k =
      higham22ClosureComplexUpperBidiag higham22ClosureMonomialStageIIDiag
        (higham22ClosureMonomialStageIISuper alpha k) := by
  ext i j
  rw [higham22StageIIUpperFactor, LinearMap.toMatrix'_apply]
  change higham22Algorithm22_2PrintedStageIIStep
      higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
      (higham22FinExtend alpha) n k
      (higham22FinExtend (Pi.single j 1)) i = _
  simp only [higham22Algorithm22_2PrintedStageIIStep,
    higham22MonomialTheta, higham22MonomialBeta, higham22MonomialGamma,
    higham22ClosureComplexUpperBidiag, higham22ClosureMonomialStageIIDiag,
    higham22ClosureMonomialStageIISuper]
  split_ifs with hi hinter hlast hn hdiag hactive hsuper
  all_goals simp only [higham22FinExtend_single]
  all_goals split_ifs <;> subst_vars
  all_goals try omega
  all_goals simp

@[simp] theorem higham22Closure_source_addError_zero_right
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.addError x 0 = 0 := by
  by_cases hx : x = 0
  · simp [Higham22ScalarRoundModel.addError, hx]
  · have h := rm.toHigham22ScalarRoundModel.flAdd_eq x 0
    rw [rm.flAdd_zero_right] at h
    have h' : x = x * (1 + rm.toHigham22ScalarRoundModel.addError x 0) := by
      simpa using h
    have he : x * rm.toHigham22ScalarRoundModel.addError x 0 = 0 := by
      rw [show x * rm.toHigham22ScalarRoundModel.addError x 0 =
          x * (1 + rm.toHigham22ScalarRoundModel.addError x 0) - x by ring]
      exact sub_eq_zero.mpr h'.symm
    exact (mul_eq_zero.mp he).resolve_left hx

@[simp] theorem higham22Closure_source_subError_zero_left
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.subError 0 x = 0 := by
  by_cases hx : x = 0
  · simp [Higham22ScalarRoundModel.subError, hx]
  · have h := rm.toHigham22ScalarRoundModel.flSub_eq 0 x
    rw [rm.flSub_zero_left] at h
    have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    have he : (-x) * rm.toHigham22ScalarRoundModel.subError 0 x = 0 := by
      rw [show (-x) * rm.toHigham22ScalarRoundModel.subError 0 x =
          (0 - x) * (1 + rm.toHigham22ScalarRoundModel.subError 0 x) - (-x) by ring]
      exact sub_eq_zero.mpr h.symm
    exact (mul_eq_zero.mp he).resolve_left hnx

@[simp] theorem higham22Closure_source_divError_one
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.divError x 1 = 0 := by
  by_cases hx : x = 0
  · simp [Higham22ScalarRoundModel.divError, hx]
  · have h := rm.toHigham22ScalarRoundModel.flDiv_eq x 1
    rw [rm.flDiv_one] at h
    have he : x * rm.toHigham22ScalarRoundModel.divError x 1 = 0 := by
      rw [show x * rm.toHigham22ScalarRoundModel.divError x 1 =
          (x / 1) * (1 + rm.toHigham22ScalarRoundModel.divError x 1) - x by ring]
      exact sub_eq_zero.mpr h.symm
    exact (mul_eq_zero.mp he).resolve_left hx

@[simp] theorem higham22Closure_source_flSub_zero_left
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.flSub 0 x = -x := rm.flSub_zero_left x

@[simp] theorem higham22Closure_source_flAdd_zero_right
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.flAdd x 0 = x := rm.flAdd_zero_right x

@[simp] theorem higham22Closure_source_flDiv_one
    (rm : Higham22SourceRoundModel) (x : ℂ) :
    rm.toHigham22ScalarRoundModel.flDiv x 1 = x := rm.flDiv_one x

@[simp] theorem higham22Closure_scalar_flMul_zero_left
    (rm : Higham22ScalarRoundModel) (x : ℂ) : rm.flMul 0 x = 0 := by
  rw [Higham22ScalarRoundModel.flMul_eq]
  ring

noncomputable def higham22ClosureMonomialStageIIEps {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    Fin (n + 1) → ℂ := fun i =>
  if k ≤ (i : ℕ) ∧ (i : ℕ) < n then
    rm.toHigham22ScalarRoundModel.addError
      (higham22FinExtend a i)
      (rm.toHigham22ScalarRoundModel.flMul
        (-higham22FinExtend alpha k) (higham22FinExtend a ((i : ℕ) + 1)))
  else 0

noncomputable def higham22ClosureMonomialStageIIDelta {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    Fin (n + 1) → ℂ := fun i =>
  if k ≤ (i : ℕ) ∧ (i : ℕ) < n then
    rm.toHigham22ScalarRoundModel.mulError
      (-higham22FinExtend alpha k) (higham22FinExtend a ((i : ℕ) + 1))
  else 0

theorem higham22Closure_monomial_stageII_eps_bound {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    ∀ i, ‖higham22ClosureMonomialStageIIEps rm alpha a k i‖ ≤ rm.u := by
  intro i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < n
  · simp only [higham22ClosureMonomialStageIIEps, if_pos h]
    exact rm.toHigham22ScalarRoundModel.addError_bound _ _
  · simp [higham22ClosureMonomialStageIIEps, h, rm.u_nonneg]

theorem higham22Closure_monomial_stageII_delta_bound {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    ∀ i, ‖higham22ClosureMonomialStageIIDelta rm alpha a k i‖ ≤ rm.u := by
  intro i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < n
  · simp only [higham22ClosureMonomialStageIIDelta, if_pos h]
    exact rm.toHigham22ScalarRoundModel.mulError_bound _ _
  · simp [higham22ClosureMonomialStageIIDelta, h, rm.u_nonneg]

theorem higham22Closure_monomial_stageII_linearized_eq_bidiag_mulVec {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a z : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k < n) :
    (fun i : Fin (n + 1) =>
      higham22StageIILinearizedStep rm.toHigham22ScalarRoundModel
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
        (higham22FinExtend alpha) n k (higham22FinExtend a)
        (higham22FinExtend z) i) =
      (higham22ClosureComplexUpperBidiag
        (fun i => (1 + higham22ClosureMonomialStageIIEps rm alpha a k i) *
          higham22ClosureMonomialStageIIDiag i)
        (fun i => (1 + higham22ClosureMonomialStageIIEps rm alpha a k i) *
          (1 + higham22ClosureMonomialStageIIDelta rm alpha a k i) *
            higham22ClosureMonomialStageIISuper alpha k i)).mulVec z := by
  funext i
  rw [higham22ClosureComplexUpperBidiag_mulVec_apply]
  simp only [higham22StageIILinearizedStep,
    higham22MonomialTheta, higham22MonomialBeta, higham22MonomialGamma,
    higham22ClosureMonomialStageIIDiag, higham22ClosureMonomialStageIISuper,
    higham22ClosureMonomialStageIIEps, higham22ClosureMonomialStageIIDelta]
  split_ifs
  all_goals try omega
  all_goals simp [higham22ThreeTermTotalEta0, higham22ThreeTermTotalEta1,
    higham22ThreeTermTotalEta2, higham22ThreeTermEta0, higham22ThreeTermEta1,
    higham22ThreeTermEta2, higham22ThreeTermMul1, higham22ThreeTermMul2,
    higham22ThreeTermSum1, higham22TwoTermTotalEta0,
    higham22TwoTermTotalEta1]
  all_goals simp only [higham22FinExtend]
  all_goals split_ifs
  all_goals try omega
  all_goals subst_vars
  all_goals try ring
  all_goals
    by_cases hiN : (i : ℕ) = n
    · first
      | omega
      | (have hiFinN : (⟨n, by omega⟩ : Fin (n + 1)) = i := by
           apply Fin.ext
           exact hiN.symm
         exact congrArg z hiFinN)
    · first
      | omega
      | (have hiLast : (i : ℕ) = n - 1 := by omega
         have hiFin : i = (⟨n - 1, by omega⟩ : Fin (n + 1)) := by
           apply Fin.ext
           exact hiLast
         have hnsub : 1 + (n - 1) = n := by omega
         simpa only [hiFin, Fin.val_mk, hnsub])

theorem higham22Closure_rounded_monomial_stageII_factor_eq_bidiag {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k < n) :
    higham22RoundedStageIIUpperFactor rm.toHigham22ScalarRoundModel
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
        alpha a k =
      higham22ClosureComplexUpperBidiag
        (fun i => (1 + higham22ClosureMonomialStageIIEps rm alpha a k i) *
          higham22ClosureMonomialStageIIDiag i)
        (fun i => (1 + higham22ClosureMonomialStageIIEps rm alpha a k i) *
          (1 + higham22ClosureMonomialStageIIDelta rm alpha a k i) *
            higham22ClosureMonomialStageIISuper alpha k i) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  simp only [higham22RoundedStageIIUpperFactor,
    LinearMap.toMatrix'_mulVec, higham22RoundedStageIIUpperLinear]
  exact higham22Closure_monomial_stageII_linearized_eq_bidiag_mulVec
    rm alpha a (Pi.single j 1) k hk

theorem higham22Closure_monomial_stageII_factor_inverse_bound {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k < n)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1)) :
    ∀ i j,
      ‖(higham22RoundedStageIIUpperFactor rm.toHigham22ScalarRoundModel
            higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
            alpha a k)⁻¹ i j -
          (higham22StageIIUpperFactor higham22MonomialTheta
            higham22MonomialBeta higham22MonomialGamma alpha k)⁻¹ i j‖ ≤
        higham22Problem22_8Coefficient (n + 1) rm.u *
          ‖(higham22StageIIUpperFactor higham22MonomialTheta
            higham22MonomialBeta higham22MonomialGamma alpha k)⁻¹ i j‖ := by
  intro i j
  rw [higham22Closure_rounded_monomial_stageII_factor_eq_bidiag rm alpha a k hk,
    higham22Closure_exact_monomial_stageII_factor_eq_bidiag alpha k hk]
  simpa [higham22Problem22_8Coefficient, gamma,
    FPModel.exactWithUnitRoundoff] using
    (higham22Closure_complex_problem22_8_matrix_inverse_bound
      higham22ClosureMonomialStageIIDiag (higham22ClosureMonomialStageIISuper alpha k)
      (higham22ClosureMonomialStageIIEps rm alpha a k)
      (higham22ClosureMonomialStageIIDelta rm alpha a k) i j rm.u
      (by intro p; simp [higham22ClosureMonomialStageIIDiag]) rm.u_nonneg
      (higham22Closure_monomial_stageII_eps_bound rm alpha a k)
      (higham22Closure_monomial_stageII_delta_bound rm alpha a k) hvalid)

theorem higham22Closure_monomial_stageII_factor_det_isUnit {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k < n)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1)) :
    IsUnit (higham22RoundedStageIIUpperFactor rm.toHigham22ScalarRoundModel
      higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
      alpha a k).det := by
  have hu1 : rm.u < 1 := by
    have hv := hvalid
    unfold gammaValid at hv
    dsimp [FPModel.exactWithUnitRoundoff] at hv
    have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hu_le : rm.u ≤ ((n + 1 : ℕ) : ℝ) * rm.u := by
      simpa using mul_le_mul_of_nonneg_right hN rm.u_nonneg
    exact hu_le.trans_lt hv
  let eps := higham22ClosureMonomialStageIIEps rm alpha a k
  let delta := higham22ClosureMonomialStageIIDelta rm alpha a k
  let u := higham22ClosureMonomialStageIIDiag (n := n)
  let e := higham22ClosureMonomialStageIISuper alpha k
  have hup : ∀ p, (1 + eps p) * u p ≠ 0 := by
    intro p
    apply mul_ne_zero
    · apply higham22_one_add_ne_zero_of_norm_lt_one
      exact (higham22Closure_monomial_stageII_eps_bound rm alpha a k p).trans_lt hu1
    · simp [u, higham22ClosureMonomialStageIIDiag]
  rw [higham22Closure_rounded_monomial_stageII_factor_eq_bidiag rm alpha a k hk]
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hprod := higham22ClosureComplexUpperBidiag_mul_invEntries
    (fun p => (1 + eps p) * u p)
    (fun p => (1 + eps p) * (1 + delta p) * e p) hup
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hzero] at hdet
  norm_num at hdet

theorem higham22Closure_monomial_stageII_factorSeq_spec {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha a : Fin (n + 1) → ℂ)
    (s : ℕ) (hs : s ≤ n)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1)) :
    (∀ q : Fin s, IsUnit
      (higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
        alpha s a q).det) ∧
    ∀ q : Fin s, ∀ i j,
      ‖(higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
            higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
            alpha s a q)⁻¹ i j -
          (higham22ExactStageIIUpperFactorSeq higham22MonomialTheta
            higham22MonomialBeta higham22MonomialGamma alpha s q)⁻¹ i j‖ ≤
        higham22Problem22_8Coefficient (n + 1) rm.u *
          ‖(higham22ExactStageIIUpperFactorSeq higham22MonomialTheta
            higham22MonomialBeta higham22MonomialGamma alpha s q)⁻¹ i j‖ := by
  induction s generalizing a with
  | zero =>
      constructor
      · intro q
        exact Fin.elim0 q
      · intro q
        exact Fin.elim0 q
  | succ k ih =>
      let b : Fin (n + 1) → ℂ := fun i =>
        higham22RoundedAlgorithm22_2StageIIStep rm.toHigham22ScalarRoundModel
          higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
          (higham22FinExtend alpha) n k (higham22FinExtend a) i
      have ihb := ih b (by omega)
      constructor
      · intro q
        refine Fin.lastCases ?_ (fun r => ?_) q
        · simpa [higham22RoundedStageIIUpperFactorSeq] using
            higham22Closure_monomial_stageII_factor_det_isUnit
              rm alpha a k (by omega) hvalid
        · simpa [higham22RoundedStageIIUpperFactorSeq, b] using ihb.1 r
      · intro q i j
        refine Fin.lastCases ?_ (fun r => ?_) q
        · simpa [higham22RoundedStageIIUpperFactorSeq,
            higham22ExactStageIIUpperFactorSeq] using
            higham22Closure_monomial_stageII_factor_inverse_bound
              rm alpha a k (by omega) hvalid i j
        · simpa [higham22RoundedStageIIUpperFactorSeq,
            higham22ExactStageIIUpperFactorSeq, b] using ihb.2 r i j

theorem higham22Closure_eq22_24_monomial {n : ℕ}
    (rm : Higham22SourceRoundModel) (alpha f : Fin (n + 1) → ℂ)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1)) :
    Higham22Eq22_24 rm higham22MonomialTheta higham22MonomialBeta
      higham22MonomialGamma alpha f
      (higham22Problem22_8Coefficient (n + 1) rm.u) := by
  unfold Higham22Eq22_24
  exact higham22Closure_monomial_stageII_factorSeq_spec rm alpha
    (higham22RoundedAlgorithm22_2StageIFin rm.toHigham22ScalarRoundModel
      alpha f n) n (by omega) hvalid

/-- Corollary 22.7 for monomials with its Problem 22.8 premise produced from
the actual rounded Stage-II execution. -/
theorem higham22_corollary22_7_monomial_residual_closed
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    {n : ℕ} (alpha : Fin (n + 1) → ℝ) (halpha : StrictMono alpha)
    (f : Fin (n + 1) → ℂ)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1)) :
    ∀ i,
      ‖f i -
          (higham22HermiteConfluentVandermondeLike
            (fun q : Fin (n + 1) =>
              higham22PolynomialSequence higham22MonomialTheta
                higham22MonomialBeta higham22MonomialGamma q)
            (fun q => (alpha q : ℂ))).transpose.mulVec
            (higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
              higham22MonomialTheta higham22MonomialBeta
              higham22MonomialGamma (fun q => (alpha q : ℂ)) f) i‖ ≤
        higham22Corollary22_7Coefficient n rm.u *
          ∑ j : Fin (n + 1),
            matSeqProd (n + 1) (n + n)
                (fun r => higham22NormMatrix
                  (higham22ExactAlgorithm22_2InverseFactorSeq
                    higham22MonomialTheta higham22MonomialBeta
                    higham22MonomialGamma (fun q => (alpha q : ℂ)) r)) i j *
              ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
                higham22MonomialTheta higham22MonomialBeta
                higham22MonomialGamma (fun q => (alpha q : ℂ)) f j‖ := by
  apply higham22_corollary22_7_monomial_residual
    rm huround alpha halpha f hvalid
  simpa [higham22Corollary22_7UpperInverseCoefficient] using
    higham22Closure_eq22_24_monomial rm
      (fun q => (alpha q : ℂ)) f hvalid

end NumStability
