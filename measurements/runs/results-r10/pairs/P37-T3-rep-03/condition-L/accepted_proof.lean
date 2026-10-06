import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_power_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p37KrylovSpan A b n := by
  classical
  let q : Polynomial ℝ := Polynomial.X ^ k %ₘ A.charpoly
  have hchar_ne : A.charpoly ≠ 1 := by
    intro h
    have hdeg := A.charpoly_natDegree
    rw [h, Polynomial.natDegree_one, Module.finrank_fin_fun] at hdeg
    omega
  have hq : q.natDegree < n := by
    rw [show n = A.charpoly.natDegree by
      simpa [Module.finrank_fin_fun] using A.charpoly_natDegree.symm]
    exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hchar_ne
  have hpow : A ^ k = Polynomial.aeval A q := by
    exact A.pow_eq_aeval_mod_charpoly k
  rw [hpow, Polynomial.aeval_eq_sum_range' hq]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

private lemma p37_krylov_A_mem
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b x : Fin n → ℝ) (hx : x ∈ p37KrylovSpan A b n) :
    A x ∈ p37KrylovSpan A b n := by
  apply Submodule.span_induction (p := fun x _ ↦ A x ∈ p37KrylovSpan A b n) _ _ _ _ hx
  · rintro _ ⟨i, rfl⟩
    rw [← Module.End.mul_apply, ← pow_succ']
    exact p37_power_mem_krylov n hn A b (i + 1)
  · simp
  · intro x y _ _ hx hy
    simpa using (p37KrylovSpan A b n).add_mem hx hy
  · intro c x _ hx
    simpa using (p37KrylovSpan A b n).smul_mem c hx

private lemma p37_shift_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b x : Fin n → ℝ) (c : ℝ) (hx : x ∈ p37KrylovSpan A b n) :
    p37Shift A c x ∈ p37KrylovSpan A b n := by
  rw [p37Shift, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  exact (p37KrylovSpan A b n).add_mem (p37_krylov_A_mem n hn A b x hx)
    ((p37KrylovSpan A b n).smul_mem c hx)

private lemma p37_pow_shift_commute
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ)) (c : ℝ) (k : ℕ)
    (x : Fin n → ℝ) :
    (A ^ k) (p37Shift A c x) = p37Shift A c ((A ^ k) x) := by
  simp only [p37Shift, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_add, map_smul]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']

private lemma p37_krylov_shift_eq
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (c : ℝ) (hshift : Function.Bijective (p37Shift A c)) :
    p37KrylovSpan A (p37Shift A c b) n = p37KrylovSpan A b n := by
  classical
  let K := p37KrylovSpan A b n
  have hle : p37KrylovSpan A (p37Shift A c b) n ≤ K := by
    rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (A ^ (i : ℕ)) (p37Shift A c b) ∈ K
    rw [p37_pow_shift_commute]
    exact p37_shift_mem_krylov n hn A b _ c (p37_power_mem_krylov n hn A b i)
  have hstable : ∀ x ∈ K, p37Shift A c x ∈ K := by
    intro x hx
    exact p37_shift_mem_krylov n hn A b x c hx
  let T : K →ₗ[ℝ] K := (p37Shift A c).restrict hstable
  have hTinj : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    exact hshift.1 (congrArg Subtype.val hxy)
  have hTsurj : Function.Surjective T := LinearMap.surjective_of_injective hTinj
  have hbK : b ∈ K := p37_power_mem_krylov n hn A b 0
  obtain ⟨y, hy⟩ := hTsurj ⟨b, hbK⟩
  have hshift_span : ∀ x ∈ K,
      p37Shift A c x ∈ p37KrylovSpan A (p37Shift A c b) n := by
    intro x hx
    apply Submodule.span_induction
        (p := fun x _ ↦ p37Shift A c x ∈ p37KrylovSpan A (p37Shift A c b) n) _ _ _ _ hx
    · rintro _ ⟨i, rfl⟩
      rw [← p37_pow_shift_commute]
      apply Submodule.subset_span
      exact ⟨i, rfl⟩
    · simp
    · intro x z _ _ hx hz
      simpa using (p37KrylovSpan A (p37Shift A c b) n).add_mem hx hz
    · intro r x _ hx
      simpa using (p37KrylovSpan A (p37Shift A c b) n).smul_mem r hx
  have hb : b ∈ p37KrylovSpan A (p37Shift A c b) n := by
    have hm := hshift_span y y.property
    have hv : p37Shift A c y = b := congrArg Subtype.val hy
    rwa [hv] at hm
  apply le_antisymm hle
  change p37KrylovSpan A b n ≤ _
  rw [p37KrylovSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change (A ^ (i : ℕ)) b ∈ p37KrylovSpan A (p37Shift A c b) n
  generalize (i : ℕ) = k
  induction k with
  | zero => simpa using hb
  | succ i hi =>
      rw [pow_succ', Module.End.mul_apply]
      exact p37_krylov_A_mem n hn A (p37Shift A c b) _ hi

private lemma p37_consecutive_mono
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m n : ℕ} (hmn : m ≤ n) :
    p37ConsecutiveSpan v s m ≤ p37ConsecutiveSpan v s n := by
  rw [p37ConsecutiveSpan, p37ConsecutiveSpan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩

private lemma p37_A_consecutive_mem
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ p37ConsecutiveSpan v s m) :
    A x ∈ p37ConsecutiveSpan v s (m + 1) := by
  apply Submodule.span_induction
      (p := fun x _ ↦ A x ∈ p37ConsecutiveSpan v s (m + 1)) _ _ _ _ hx
  · rintro _ ⟨i, rfl⟩
    let j : ℤ := s + (i : ℕ)
    change A (v j) ∈ p37ConsecutiveSpan v s (m + 1)
    have hcur : v j ∈ p37ConsecutiveSpan v s (m + 1) := by
      apply Submodule.subset_span
      exact ⟨Fin.castSucc i, rfl⟩
    have hnext : v (j + 1) ∈ p37ConsecutiveSpan v s (m + 1) := by
      apply Submodule.subset_span
      refine ⟨Fin.succ i, ?_⟩
      exact congrArg v (by simp [j]; omega)
    have hrewrite : A (v j) = v (j + 1) - p j • v j := by
      apply eq_sub_iff_add_eq.mpr
      symm
      simpa [p37Shift] using hstep j
    rw [hrewrite]
    exact (p37ConsecutiveSpan v s (m + 1)).sub_mem hnext
      ((p37ConsecutiveSpan v s (m + 1)).smul_mem (p j) hcur)
  · simpa using (p37ConsecutiveSpan v s (m + 1)).zero_mem
  · intro y z _ _ hy hz
    rw [map_add]
    exact (p37ConsecutiveSpan v s (m + 1)).add_mem hy hz
  · intro r y _ hy
    rw [map_smul]
    exact (p37ConsecutiveSpan v s (m + 1)).smul_mem r hy

private lemma p37_power_mem_consecutive
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (k : ℕ) :
    (A ^ k) (v s) ∈ p37ConsecutiveSpan v s (k + 1) := by
  induction k with
  | zero =>
      simp only [pow_zero, zero_add]
      change v s ∈ p37ConsecutiveSpan v s 1
      apply Submodule.subset_span
      exact ⟨⟨0, by omega⟩, by simp⟩
  | succ k hk =>
      rw [pow_succ', Module.End.mul_apply]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        p37_A_consecutive_mem A p v hstep s (k + 1) _ hk

/-- P37-T3: the shifted-vector spanning equalities in Theorem 6.1. -/
theorem p37_t3_consecutive_shifted_vectors_span
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (hA : Function.Bijective A)
    (B : Fin n → ℝ) (hB : B ≠ 0)
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hv0 : v 0 = B)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s : ℤ) :
    p37TwoSidedSpan v = p37ConsecutiveSpan v s n ∧
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n ∧
      p37KrylovSpan A (v s) n = p37KrylovSpan A B n := by
  -- PROOF_START P37-T3-H001
  have hnext (j : ℤ) :
      p37KrylovSpan A (v (j + 1)) n = p37KrylovSpan A (v j) n := by
    rw [hstep j]
    exact p37_krylov_shift_eq n hn A (v j) (p j) (hinv j)
  have hallK (j : ℤ) :
      p37KrylovSpan A (v j) n = p37KrylovSpan A (v s) n := by
    refine Int.inductionOn' (motive := fun j ↦
      p37KrylovSpan A (v j) n = p37KrylovSpan A (v s) n) j s ?_ ?_ ?_
    · rfl
    · intro k _ hk
      exact (hnext k).trans hk
    · intro k _ hk
      have h := (hnext (k - 1)).symm
      have hidx : k - 1 + 1 = k := by omega
      rw [hidx] at h
      exact h.trans hk
  have hvK (j : ℤ) : v j ∈ p37KrylovSpan A (v s) n := by
    rw [← hallK j]
    exact p37_power_mem_krylov n hn A (v j) 0
  have htwo_le : p37TwoSidedSpan v ≤ p37KrylovSpan A (v s) n := by
    rw [p37TwoSidedSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hvK j
  have hvTwo (j : ℤ) : v j ∈ p37TwoSidedSpan v := by
    apply Submodule.subset_span
    exact ⟨j, rfl⟩
  have hATwo (x : Fin n → ℝ) (hx : x ∈ p37TwoSidedSpan v) :
      A x ∈ p37TwoSidedSpan v := by
    apply Submodule.span_induction
        (p := fun x _ ↦ A x ∈ p37TwoSidedSpan v) _ _ _ _ hx
    · rintro _ ⟨j, rfl⟩
      have hrewrite : A (v j) = v (j + 1) - p j • v j := by
        apply eq_sub_iff_add_eq.mpr
        symm
        simpa [p37Shift] using hstep j
      rw [hrewrite]
      exact (p37TwoSidedSpan v).sub_mem (hvTwo (j + 1))
        ((p37TwoSidedSpan v).smul_mem (p j) (hvTwo j))
    · simpa using (p37TwoSidedSpan v).zero_mem
    · intro y z _ _ hy hz
      rw [map_add]
      exact (p37TwoSidedSpan v).add_mem hy hz
    · intro r y _ hy
      rw [map_smul]
      exact (p37TwoSidedSpan v).smul_mem r hy
  have hkrylov_le_two : p37KrylovSpan A (v s) n ≤ p37TwoSidedSpan v := by
    rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (A ^ (i : ℕ)) (v s) ∈ p37TwoSidedSpan v
    generalize (i : ℕ) = k
    induction k with
    | zero => simpa using hvTwo s
    | succ k hk =>
        rw [pow_succ', Module.End.mul_apply]
        exact hATwo _ hk
  have htwo : p37TwoSidedSpan v = p37KrylovSpan A (v s) n :=
    le_antisymm htwo_le hkrylov_le_two
  have hconsecutive_le :
      p37ConsecutiveSpan v s n ≤ p37KrylovSpan A (v s) n := by
    rw [p37ConsecutiveSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hvK (s + (i : ℕ))
  have hkrylov_le_consecutive :
      p37KrylovSpan A (v s) n ≤ p37ConsecutiveSpan v s n := by
    rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (A ^ (i : ℕ)) (v s) ∈ p37ConsecutiveSpan v s n
    apply p37_consecutive_mono v s (Nat.succ_le_iff.mpr i.isLt)
    exact p37_power_mem_consecutive A p v hstep s i
  have hconsecutive :
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n :=
    le_antisymm hconsecutive_le hkrylov_le_consecutive
  have hbase : p37KrylovSpan A (v s) n = p37KrylovSpan A B n := by
    calc
      p37KrylovSpan A (v s) n = p37KrylovSpan A (v 0) n := (hallK 0).symm
      _ = p37KrylovSpan A B n := by rw [hv0]
  exact ⟨htwo.trans hconsecutive.symm, hconsecutive, hbase⟩

end HighamBench
