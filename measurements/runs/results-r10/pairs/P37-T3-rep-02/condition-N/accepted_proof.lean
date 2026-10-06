import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_shift_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (q : ℝ) (x : V) :
    p37Shift A q x = A x + q • x := by
  simp [p37Shift]

private lemma p37_krylov_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m l : ℕ} (hml : m ≤ l) :
    p37KrylovSpan A b m ≤ p37KrylovSpan A b l := by
  refine Submodule.span_mono ?_
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hml⟩, rfl⟩

private lemma p37_consecutive_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m l : ℕ} (hml : m ≤ l) :
    p37ConsecutiveSpan v s m ≤ p37ConsecutiveSpan v s l := by
  refine Submodule.span_mono ?_
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hml⟩, rfl⟩

private lemma p37_A_maps_krylov_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) :
    ∀ x ∈ p37KrylovSpan A b m, A x ∈ p37KrylovSpan A b (m + 1) := by
  intro x hx
  refine Submodule.span_induction (p := fun y _ ↦ A y ∈ p37KrylovSpan A b (m + 1))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨k, rfl⟩
    rw [← Module.End.mul_apply, ← pow_succ']
    exact Submodule.subset_span ⟨⟨k + 1, by omega⟩, rfl⟩
  · simpa using (p37KrylovSpan A b (m + 1)).zero_mem
  · intro x y _ _ hx hy
    simpa using (p37KrylovSpan A b (m + 1)).add_mem hx hy
  · intro c x _ hx
    simpa using (p37KrylovSpan A b (m + 1)).smul_mem c hx

private lemma p37_A_maps_consecutive_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    ∀ x ∈ p37ConsecutiveSpan v s m,
      A x ∈ p37ConsecutiveSpan v s (m + 1) := by
  intro x hx
  refine Submodule.span_induction
    (p := fun y _ ↦ A y ∈ p37ConsecutiveSpan v s (m + 1)) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨k, rfl⟩
    have hk : (k : ℕ) + 1 < m + 1 := by omega
    have hcur : v (s + (k : ℕ)) ∈ p37ConsecutiveSpan v s (m + 1) :=
      Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩
    have hnxt : v (s + ((k : ℕ) + 1)) ∈ p37ConsecutiveSpan v s (m + 1) :=
      Submodule.subset_span ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
    have hs := hstep (s + (k : ℕ))
    rw [p37_shift_apply] at hs
    have heq : s + (k : ℕ) + 1 = s + ((k : ℕ) + 1) := by omega
    rw [heq] at hs
    have hsolve : A (v (s + (k : ℕ))) =
        v (s + ((k : ℕ) + 1)) - p (s + (k : ℕ)) • v (s + (k : ℕ)) :=
      eq_sub_iff_add_eq.mpr hs.symm
    rw [hsolve]
    exact (p37ConsecutiveSpan v s (m + 1)).sub_mem hnxt
      ((p37ConsecutiveSpan v s (m + 1)).smul_mem _ hcur)
  · simpa using (p37ConsecutiveSpan v s (m + 1)).zero_mem
  · intro x y _ _ hx hy
    simpa using (p37ConsecutiveSpan v s (m + 1)).add_mem hx hy
  · intro c x _ hx
    simpa using (p37ConsecutiveSpan v s (m + 1)).smul_mem c hx

private lemma p37_shifted_mem_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) : ∀ k : ℕ,
      v (s + k) ∈ p37KrylovSpan A (v s) (k + 1) := by
  intro k
  induction k with
  | zero =>
      exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp⟩
  | succ k ih =>
      have hmono := p37_krylov_mono A (v s) (show k + 1 ≤ (k + 1) + 1 by omega)
      have hprev : v (s + k) ∈ p37KrylovSpan A (v s) ((k + 1) + 1) := hmono ih
      have hAv := p37_A_maps_krylov_succ A (v s) (k + 1) _ ih
      have hs := hstep (s + k)
      rw [p37_shift_apply] at hs
      have heq : s + k + 1 = s + (k + 1) := by omega
      rw [heq] at hs
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hs]
      exact (p37KrylovSpan A (v s) ((k + 1) + 1)).add_mem hAv
        ((p37KrylovSpan A (v s) ((k + 1) + 1)).smul_mem _ hprev)

private lemma p37_power_mem_consecutive {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) : ∀ k : ℕ,
      (A ^ k) (v s) ∈ p37ConsecutiveSpan v s (k + 1) := by
  intro k
  induction k with
  | zero =>
      exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp⟩
  | succ k ih =>
      rw [pow_succ']
      exact p37_A_maps_consecutive_succ A p v hstep s (k + 1) _ ih

private lemma p37_consecutive_eq_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    p37ConsecutiveSpan v s m = p37KrylovSpan A (v s) m := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro x ⟨k, rfl⟩
    exact p37_krylov_mono A (v s) (show (k : ℕ) + 1 ≤ m by omega)
      (p37_shifted_mem_krylov A p v hstep s k)
  · refine Submodule.span_le.2 ?_
    rintro x ⟨k, rfl⟩
    exact p37_consecutive_mono v s (show (k : ℕ) + 1 ≤ m by omega)
      (p37_power_mem_consecutive A p v hstep s k)

private lemma p37_all_powers_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p37KrylovSpan A b n := by
  let q : Polynomial ℝ := Polynomial.X ^ k %ₘ A.charpoly
  have hcpdeg : A.charpoly.natDegree = n := by
    rw [LinearMap.charpoly_natDegree]
    simp
  have hcpne : A.charpoly ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [hcpdeg] at hdeg
    simpa [hn.ne'] using hdeg
  have hqdeg : q.natDegree < n := by
    rw [← hcpdeg]
    exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hcpne
  rw [A.pow_eq_aeval_mod_charpoly k]
  change (Polynomial.aeval A q) b ∈ _
  rw [Polynomial.aeval_endomorphism]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rcases Polynomial.mem_support_iff.mp hi with hcoeff
  have hi_le : i ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff
  have hi_n : i < n := lt_of_le_of_lt hi_le hqdeg
  exact ⟨⟨i, hi_n⟩, rfl⟩

private lemma p37_krylov_invariant
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) :
    ∀ x ∈ p37KrylovSpan A b n, A x ∈ p37KrylovSpan A b n := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      rw [← Module.End.mul_apply, ← pow_succ']
      exact p37_all_powers_mem_krylov n hn A b (i + 1)
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

private lemma p37_shift_invariant
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (q : ℝ) :
    ∀ x ∈ p37KrylovSpan A b n,
      p37Shift A q x ∈ p37KrylovSpan A b n := by
  intro x hx
  rw [p37_shift_apply]
  exact (p37KrylovSpan A b n).add_mem (p37_krylov_invariant n hn A b x hx)
    ((p37KrylovSpan A b n).smul_mem q hx)

private lemma p37_all_shifted_mem_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s j : ℤ) : v j ∈ p37KrylovSpan A (v s) n := by
  let K := p37KrylovSpan A (v s) n
  have hbase : v s ∈ K := by
    exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
  by_cases hsj : s ≤ j
  · apply Int.le_induction (motive := fun i _ ↦ v i ∈ K) hbase _ j hsj
    intro i _ hi
    rw [hstep i]
    exact p37_shift_invariant n hn A (v s) (p i) _ hi
  · have hjs : j ≤ s := le_of_not_ge hsj
    apply Int.le_induction_down (motive := fun i _ ↦ v i ∈ K) hbase _ j hjs
    intro i _ hi
    let T := p37Shift A (p (i - 1))
    have hTK : ∀ x ∈ K, T x ∈ K := by
      intro x hx
      exact p37_shift_invariant n hn A (v s) (p (i - 1)) x hx
    have hsurj : Set.SurjOn T (K : Set (Fin n → ℝ)) K :=
      (LinearMap.injOn_iff_surjOn hTK).mp
        (fun _ _ _ _ hxy ↦ (hinv (i - 1)).injective hxy)
    obtain ⟨x, hx, hTx⟩ := hsurj hi
    have hrec := hstep (i - 1)
    have hiarith : i - 1 + 1 = i := by omega
    rw [hiarith] at hrec
    have heq : v (i - 1) = x :=
      (hinv (i - 1)).injective (hrec.symm.trans hTx.symm)
    rw [heq]
    exact hx

private lemma p37_twoSided_eq_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s : ℤ) : p37TwoSidedSpan v = p37KrylovSpan A (v s) n := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro x ⟨j, rfl⟩
    exact p37_all_shifted_mem_krylov n hn A p v hstep hinv s j
  · rw [← p37_consecutive_eq_krylov A p v hstep s n]
    refine Submodule.span_le.2 ?_
    rintro x ⟨k, rfl⟩
    exact Submodule.subset_span ⟨s + (k : ℕ), rfl⟩

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
  have hCKs : p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n :=
    p37_consecutive_eq_krylov A p v hstep s n
  have hTKs : p37TwoSidedSpan v = p37KrylovSpan A (v s) n :=
    p37_twoSided_eq_krylov n hn A p v hstep hinv s
  have hTK0 : p37TwoSidedSpan v = p37KrylovSpan A B n := by
    have h := p37_twoSided_eq_krylov n hn A p v hstep hinv 0
    rwa [hv0] at h
  exact ⟨hTKs.trans hCKs.symm, hCKs, hTKs.symm.trans hTK0⟩

end HighamBench
