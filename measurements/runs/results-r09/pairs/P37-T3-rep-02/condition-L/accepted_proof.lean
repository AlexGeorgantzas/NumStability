import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_aeval_apply_mem_krylov
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (q : Polynomial ℝ) (hq : q.natDegree < n) :
    (Polynomial.aeval A q) b ∈ p37KrylovSpan A b n := by
  unfold p37KrylovSpan
  rw [Polynomial.aeval_endomorphism]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hkn : k < n :=
    lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp (p := q) k hk) hq
  exact ⟨⟨k, hkn⟩, rfl⟩

private lemma p37_map_krylov_le
    {n : ℕ} (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) :
    Submodule.map A (p37KrylovSpan A b n) ≤ p37KrylovSpan A b n := by
  rw [p37KrylovSpan, Submodule.map_span_le]
  rintro _ ⟨k, rfl⟩
  change A ((A ^ (k : ℕ)) b) ∈ p37KrylovSpan A b n
  rw [← Module.End.mul_apply, ← pow_succ']
  by_cases hk : (k : ℕ) + 1 < n
  · apply Submodule.subset_span
    exact ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
  · have hkn : (k : ℕ) + 1 = n := by omega
    rw [hkn, A.pow_eq_aeval_mod_charpoly]
    apply p37_aeval_apply_mem_krylov
    have hdeg : A.charpoly.natDegree = n := by
      simpa using A.charpoly_natDegree
    apply lt_of_lt_of_eq _ hdeg
    apply Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic
    intro hcp
    rw [hcp] at hdeg
    simp at hdeg
    omega

private lemma p37_krylov_mono
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m n : ℕ} (hmn : m ≤ n) :
    p37KrylovSpan A b m ≤ p37KrylovSpan A b n := by
  rw [p37KrylovSpan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hmn⟩, rfl⟩

private lemma p37_consecutive_mono
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m n : ℕ} (hmn : m ≤ n) :
    p37ConsecutiveSpan v s m ≤ p37ConsecutiveSpan v s n := by
  rw [p37ConsecutiveSpan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hmn⟩, rfl⟩

private lemma p37_map_krylov_succ_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) :
    Submodule.map A (p37KrylovSpan A b m) ≤
      p37KrylovSpan A b (m + 1) := by
  rw [p37KrylovSpan, Submodule.map_span_le]
  rintro _ ⟨k, rfl⟩
  change A ((A ^ (k : ℕ)) b) ∈ p37KrylovSpan A b (m + 1)
  rw [← Module.End.mul_apply, ← pow_succ']
  apply Submodule.subset_span
  exact ⟨⟨(k : ℕ) + 1, by omega⟩, rfl⟩

private lemma p37_map_consecutive_succ_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    Submodule.map A (p37ConsecutiveSpan v s m) ≤
      p37ConsecutiveSpan v s (m + 1) := by
  rw [p37ConsecutiveSpan, Submodule.map_span_le]
  rintro _ ⟨k, rfl⟩
  have hcur : v (s + (k : ℕ)) ∈ p37ConsecutiveSpan v s (m + 1) := by
    apply Submodule.subset_span
    exact ⟨⟨(k : ℕ), by omega⟩, rfl⟩
  have hnext : v (s + ((k : ℕ) + 1)) ∈
      p37ConsecutiveSpan v s (m + 1) := by
    apply Submodule.subset_span
    exact ⟨⟨(k : ℕ) + 1, by omega⟩, rfl⟩
  have heq : A (v (s + (k : ℕ))) =
      v (s + ((k : ℕ) + 1)) - p (s + (k : ℕ)) • v (s + (k : ℕ)) := by
    have hs := hstep (s + (k : ℕ))
    rw [p37Shift] at hs
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hs
    rw [show s + ((k : ℕ) + 1) = (s + (k : ℕ)) + 1 by omega, hs]
    abel
  rw [heq]
  exact Submodule.sub_mem _ hnext (Submodule.smul_mem _ _ hcur)

private lemma p37_consecutive_eq_krylov
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    p37ConsecutiveSpan v s m = p37KrylovSpan A (v s) m := by
  have hshift : ∀ k : ℕ,
      v (s + k) ∈ p37KrylovSpan A (v s) (k + 1) := by
    intro k
    induction k with
    | zero =>
        apply Submodule.subset_span
        exact ⟨⟨0, by omega⟩, by simp⟩
    | succ k ih =>
        have hAv : A (v (s + k)) ∈
            p37KrylovSpan A (v s) ((k + 1) + 1) := by
          apply p37_map_krylov_succ_le A (v s) (k + 1)
          exact ⟨v (s + k), ih, rfl⟩
        have hv : v (s + k) ∈
            p37KrylovSpan A (v s) ((k + 1) + 1) :=
          p37_krylov_mono A (v s) (by omega) ih
        have hs := hstep (s + k)
        rw [p37Shift] at hs
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hs
        rw [show s + (↑(k + 1) : ℤ) = (s + k) + 1 by omega, hs]
        exact Submodule.add_mem _ hAv (Submodule.smul_mem _ _ hv)
  have hpower : ∀ k : ℕ,
      (A ^ k) (v s) ∈ p37ConsecutiveSpan v s (k + 1) := by
    intro k
    induction k with
    | zero =>
        apply Submodule.subset_span
        exact ⟨⟨0, by omega⟩, by simp⟩
    | succ k ih =>
        have hm := p37_map_consecutive_succ_le A p v hstep s (k + 1)
          ⟨(A ^ k) (v s), ih, rfl⟩
        simpa [← Module.End.mul_apply, ← pow_succ'] using hm
  apply le_antisymm
  · rw [p37ConsecutiveSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact p37_krylov_mono A (v s) (Nat.succ_le_iff.mpr k.isLt) (hshift k)
  · rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact p37_consecutive_mono v s (Nat.succ_le_iff.mpr k.isLt) (hpower k)

private lemma p37_shift_commute_pow
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (c : ℝ) (b : V) (k : ℕ) :
    p37Shift A c ((A ^ k) b) = (A ^ k) (p37Shift A c b) := by
  simp only [p37Shift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_smul]
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]

private lemma p37_map_shift_krylov_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (c : ℝ) (b : V) (m : ℕ) :
    Submodule.map (p37Shift A c) (p37KrylovSpan A b m) =
      p37KrylovSpan A (p37Shift A c b) m := by
  unfold p37KrylovSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (p37_shift_commute_pow A c b k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(A ^ (k : ℕ)) b, ⟨k, rfl⟩, p37_shift_commute_pow A c b k⟩

private lemma p37_map_shift_krylov_eq_self
    {n : ℕ} (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (c : ℝ) (b : Fin n → ℝ) (hT : Function.Bijective (p37Shift A c)) :
    Submodule.map (p37Shift A c) (p37KrylovSpan A b n) =
      p37KrylovSpan A b n := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    change A x + c • x ∈ p37KrylovSpan A b n
    exact Submodule.add_mem _
      (p37_map_krylov_le hn A b ⟨x, hx, rfl⟩)
      (Submodule.smul_mem _ _ hx)
  · let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
      LinearEquiv.ofBijective (p37Shift A c) hT
    simpa [e] using e.finrank_map_eq (p37KrylovSpan A b n)

private lemma p37_krylov_step_eq
    {n : ℕ} (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j))) (j : ℤ) :
    p37KrylovSpan A (v (j + 1)) n = p37KrylovSpan A (v j) n := by
  calc
    p37KrylovSpan A (v (j + 1)) n =
        p37KrylovSpan A (p37Shift A (p j) (v j)) n := by rw [hstep j]
    _ = Submodule.map (p37Shift A (p j)) (p37KrylovSpan A (v j) n) :=
      (p37_map_shift_krylov_eq A (p j) (v j) n).symm
    _ = p37KrylovSpan A (v j) n :=
      p37_map_shift_krylov_eq_self hn A (p j) (v j) (hinv j)

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
  have hK : ∀ j : ℤ,
      p37KrylovSpan A (v j) n = p37KrylovSpan A (v 0) n := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ j ih =>
        exact (p37_krylov_step_eq hn A p v hstep hinv j).trans ih
    | pred j ih =>
        calc
          p37KrylovSpan A (v (-(↑j : ℤ) - 1)) n =
              p37KrylovSpan A (v (-(↑j : ℤ))) n := by
                simpa using (p37_krylov_step_eq hn A p v hstep hinv
                  (-(↑j : ℤ) - 1)).symm
          _ = p37KrylovSpan A (v 0) n := ih
  have hconsecutive :
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n :=
    p37_consecutive_eq_krylov A p v hstep s n
  have hv_mem : ∀ j : ℤ, v j ∈ p37KrylovSpan A (v s) n := by
    intro j
    have hj : v j ∈ p37KrylovSpan A (v j) n := by
      apply Submodule.subset_span
      exact ⟨⟨0, hn⟩, by simp⟩
    rw [hK j, ← hK s] at hj
    exact hj
  have htwo : p37TwoSidedSpan v = p37KrylovSpan A (v s) n := by
    apply le_antisymm
    · rw [p37TwoSidedSpan, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hv_mem j
    · rw [← hconsecutive, p37ConsecutiveSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      apply Submodule.subset_span
      exact ⟨s + (k : ℕ), rfl⟩
  refine ⟨htwo.trans hconsecutive.symm, hconsecutive, ?_⟩
  calc
    p37KrylovSpan A (v s) n = p37KrylovSpan A (v 0) n := hK s
    _ = p37KrylovSpan A B n := by rw [hv0]

end HighamBench
