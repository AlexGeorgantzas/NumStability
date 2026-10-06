import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_aeval_mem_krylov
    (n : ℕ) (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (q : Polynomial ℝ) (hq : q.natDegree < n) :
    Polynomial.aeval A q b ∈ p37KrylovSpan A b n := by
  rw [Polynomial.aeval_endomorphism]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨k, (Polynomial.le_natDegree_of_mem_supp k hk).trans_lt hq⟩, ?_⟩
  rfl

private lemma p37_krylov_invariant
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) :
    ∀ x ∈ p37KrylovSpan A b n, A x ∈ p37KrylovSpan A b n := by
  let q : Polynomial ℝ := Polynomial.X ^ n %ₘ A.charpoly
  have hcpdeg : A.charpoly.natDegree = n := by
    simpa using A.charpoly_natDegree
  have hcpne : A.charpoly ≠ 1 := by
    intro h
    have : n = 0 := by
      rw [← hcpdeg, h]
      simp
    omega
  have hqdeg : q.natDegree < n := by
    rw [← hcpdeg]
    exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hcpne
  have hAn : (A ^ n) b ∈ p37KrylovSpan A b n := by
    rw [A.pow_eq_aeval_mod_charpoly]
    exact p37_aeval_mem_krylov n A b q hqdeg
  intro x hx
  change x ∈ Submodule.span ℝ (Set.range fun k : Fin n ↦ (A ^ (k : ℕ)) b) at hx
  change A x ∈ Submodule.span ℝ (Set.range fun k : Fin n ↦ (A ^ (k : ℕ)) b)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    have hle : k.val + 1 ≤ n := k.isLt
    rcases hle.lt_or_eq with hlt | heq
    · apply Submodule.subset_span
      refine ⟨⟨k.val + 1, hlt⟩, ?_⟩
      change (A ^ (k.val + 1)) b = A ((A ^ k.val) b)
      rw [pow_succ']
      rfl
    · have heval : A ((A ^ k.val) b) = (A ^ (k.val + 1)) b := by
        rw [pow_succ']
        rfl
      rw [heval, heq]
      exact hAn
  · simpa using (Submodule.zero_mem
      (Submodule.span ℝ (Set.range fun k : Fin n ↦ (A ^ (k : ℕ)) b)))
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

private lemma p37_krylov_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m l : ℕ} (hml : m ≤ l) :
    p37KrylovSpan A b m ≤ p37KrylovSpan A b l := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hml⟩, rfl⟩

private lemma p37_consecutive_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m l : ℕ} (hml : m ≤ l) :
    p37ConsecutiveSpan v s m ≤ p37ConsecutiveSpan v s l := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hml⟩, rfl⟩

private lemma p37_map_krylov_le_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) :
    Submodule.map A (p37KrylovSpan A b m) ≤ p37KrylovSpan A b (m + 1) := by
  rw [p37KrylovSpan, Submodule.map_span, Submodule.span_le]
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨i + 1, by omega⟩, ?_⟩
  change (A ^ (i.val + 1)) b = A ((A ^ i.val) b)
  rw [pow_succ']
  rfl

private lemma p37_map_consecutive_le_succ
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    Submodule.map A (p37ConsecutiveSpan v s m) ≤
      p37ConsecutiveSpan v s (m + 1) := by
  rw [p37ConsecutiveSpan, Submodule.map_span, Submodule.span_le]
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  have hi : v (s + (i : ℕ)) ∈ p37ConsecutiveSpan v s (m + 1) := by
    apply Submodule.subset_span
    exact ⟨⟨i, by omega⟩, rfl⟩
  have his : v (s + (i : ℕ) + 1) ∈ p37ConsecutiveSpan v s (m + 1) := by
    apply Submodule.subset_span
    refine ⟨⟨i + 1, by omega⟩, ?_⟩
    change v (s + ((i.val + 1 : ℕ) : ℤ)) = v (s + (i.val : ℤ) + 1)
    congr 1
    push_cast
    ring
  have hs := hstep (s + (i : ℕ))
  rw [p37Shift, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hs
  rw [hs] at his
  simpa using (p37ConsecutiveSpan v s (m + 1)).sub_mem his
    ((p37ConsecutiveSpan v s (m + 1)).smul_mem (p (s + (i : ℕ))) hi)

private lemma p37_shifted_mem_krylov
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) : ∀ k : ℕ, v (s + k) ∈ p37KrylovSpan A (v s) (k + 1) := by
  intro k
  induction k with
  | zero =>
      apply Submodule.subset_span
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp
  | succ k ih =>
      have hA : A (v (s + k)) ∈ p37KrylovSpan A (v s) (k + 2) := by
        apply p37_map_krylov_le_succ A (v s) (k + 1)
        exact ⟨v (s + k), ih, rfl⟩
      have hv : v (s + k) ∈ p37KrylovSpan A (v s) (k + 2) :=
        p37_krylov_mono A (v s) (by omega) ih
      have hs := hstep (s + k)
      rw [p37Shift, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hs
      rw [show s + (↑(k + 1) : ℤ) = s + (↑k : ℤ) + 1 by push_cast; omega, hs]
      exact (p37KrylovSpan A (v s) (k + 2)).add_mem hA
        ((p37KrylovSpan A (v s) (k + 2)).smul_mem _ hv)

private lemma p37_power_mem_consecutive
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) : ∀ k : ℕ, (A ^ k) (v s) ∈ p37ConsecutiveSpan v s (k + 1) := by
  intro k
  induction k with
  | zero =>
      apply Submodule.subset_span
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp
  | succ k ih =>
      rw [pow_succ']
      apply p37_map_consecutive_le_succ A p v hstep s (k + 1)
      exact ⟨(A ^ k) (v s), ih, rfl⟩

private lemma p37_consecutive_eq_krylov
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    p37ConsecutiveSpan v s m = p37KrylovSpan A (v s) m := by
  apply le_antisymm
  · rw [p37ConsecutiveSpan, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact p37_krylov_mono A (v s) (Nat.succ_le_of_lt i.isLt)
      (p37_shifted_mem_krylov A p v hstep s i)
  · rw [p37KrylovSpan, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact p37_consecutive_mono v s (Nat.succ_le_of_lt i.isLt)
      (p37_power_mem_consecutive A p v hstep s i)

private lemma p37_shift_maps_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (c : ℝ) :
    ∀ x ∈ p37KrylovSpan A b n,
      p37Shift A c x ∈ p37KrylovSpan A b n := by
  intro x hx
  simp only [p37Shift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  exact Submodule.add_mem _ (p37_krylov_invariant n hn A b x hx)
    (Submodule.smul_mem _ c hx)

private lemma p37_shift_preimage_mem_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (c : ℝ)
    (hbij : Function.Bijective (p37Shift A c))
    (x : Fin n → ℝ)
    (hx : p37Shift A c x ∈ p37KrylovSpan A b n) :
    x ∈ p37KrylovSpan A b n := by
  have hmaps := p37_shift_maps_krylov n hn A b c
  have hsurj : Set.SurjOn (p37Shift A c)
      (p37KrylovSpan A b n) (p37KrylovSpan A b n) :=
    (LinearMap.injOn_iff_surjOn hmaps).mp hbij.injective.injOn
  obtain ⟨y, hy, heq⟩ := hsurj hx
  have hyx : y = x := hbij.injective heq
  simpa only [hyx] using hy

private lemma p37_all_int_mem_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s j : ℤ) : v j ∈ p37KrylovSpan A (v s) n := by
  refine Int.inductionOn' j s ?_ ?_ ?_
  · exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
  · intro k _ ih
    rw [hstep k]
    exact p37_shift_maps_krylov n hn A (v s) (p k) _ ih
  · intro k _ ih
    apply p37_shift_preimage_mem_krylov n hn A (v s) (p (k - 1)) (hinv (k - 1))
    have hs := hstep (k - 1)
    have hs' : v k = p37Shift A (p (k - 1)) (v (k - 1)) := by
      simpa only [sub_add_cancel] using hs
    rw [← hs']
    exact ih

private lemma p37_two_sided_eq_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s : ℤ) : p37TwoSidedSpan v = p37KrylovSpan A (v s) n := by
  apply le_antisymm
  · rw [p37TwoSidedSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact p37_all_int_mem_krylov n hn A p v hstep hinv s j
  · rw [← p37_consecutive_eq_krylov A p v hstep s n]
    rw [p37ConsecutiveSpan, p37TwoSidedSpan]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨s + (k : ℕ), rfl⟩

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
  have hcs := p37_consecutive_eq_krylov A p v hstep s n
  have hts := p37_two_sided_eq_krylov n hn A p v hstep hinv s
  have ht0 := p37_two_sided_eq_krylov n hn A p v hstep hinv 0
  refine ⟨hts.trans hcs.symm, hcs, ?_⟩
  rw [← hv0]
  exact hts.symm.trans ht0

end HighamBench
