import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_pow_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p37KrylovSpan A b n := by
  let q : Polynomial ℝ := (Polynomial.X ^ k) %ₘ A.charpoly
  have hcpdeg : A.charpoly.natDegree = n := by
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_fin_fun ℝ
  have hcpne : A.charpoly ≠ 1 := by
    intro h
    have : n = 0 := by simpa [h] using hcpdeg.symm
    omega
  have hqdeg : q.natDegree < n := by
    rw [← hcpdeg]
    exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hcpne
  rw [LinearMap.pow_eq_aeval_mod_charpoly A k]
  change Polynomial.aeval A q b ∈ p37KrylovSpan A b n
  rw [Polynomial.aeval_eq_sum_range' hqdeg]
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rw [Set.mem_range]
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

private lemma p37_shift_pow_commute
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ)) (q : ℝ)
    (b : Fin n → ℝ) (k : ℕ) :
    p37Shift A q ((A ^ k) b) = (A ^ k) (p37Shift A q b) := by
  calc
    p37Shift A q ((A ^ k) b) = A ((A ^ k) b) + q • (A ^ k) b := by
      simp [p37Shift]
    _ = (A ^ (k + 1)) b + q • (A ^ k) b := by
      rw [pow_succ', Module.End.mul_apply]
    _ = (A ^ k) (A b) + (A ^ k) (q • b) := by
      rw [pow_succ, Module.End.mul_apply, map_smul]
    _ = (A ^ k) (A b + q • b) := by rw [map_add]
    _ = (A ^ k) (p37Shift A q b) := by simp [p37Shift]

private lemma p37_krylov_shift_eq
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (q : ℝ) (b : Fin n → ℝ)
    (hshift : Function.Bijective (p37Shift A q)) :
    p37KrylovSpan A (p37Shift A q b) n = p37KrylovSpan A b n := by
  have hle : p37KrylovSpan A (p37Shift A q b) n ≤ p37KrylovSpan A b n := by
    rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change (A ^ (k : ℕ)) (p37Shift A q b) ∈ p37KrylovSpan A b n
    rw [← p37_shift_pow_commute]
    change A ((A ^ (k : ℕ)) b) + q • (A ^ (k : ℕ)) b ∈
      p37KrylovSpan A b n
    apply Submodule.add_mem
    · rw [← Module.End.mul_apply, ← pow_succ']
      exact p37_pow_mem_krylov n hn A b ((k : ℕ) + 1)
    · exact Submodule.smul_mem _ _ (p37_pow_mem_krylov n hn A b k)
  have hmap :
      Submodule.map (p37Shift A q) (p37KrylovSpan A b n) =
        p37KrylovSpan A (p37Shift A q b) n := by
    rw [p37KrylovSpan, p37KrylovSpan, LinearMap.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (p37_shift_pow_commute A q b k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(A ^ (k : ℕ)) b, ⟨k, rfl⟩, p37_shift_pow_commute A q b k⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim :=
    (Submodule.equivMapOfInjective (p37Shift A q) hshift.1
      (p37KrylovSpan A b n)).finrank_eq
  rw [hmap] at hdim
  exact hdim.symm

private lemma p37_apply_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b x : Fin n → ℝ) (hx : x ∈ p37KrylovSpan A b n) :
    A x ∈ p37KrylovSpan A b n := by
  rw [p37KrylovSpan] at hx ⊢
  refine Submodule.span_induction (p := fun x _ ↦ A x ∈
    Submodule.span ℝ (Set.range fun k : Fin n ↦ (A ^ (k : ℕ)) b))
    ?_ (by change A 0 ∈ _; simpa) ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    rw [← Module.End.mul_apply, ← pow_succ']
    exact p37_pow_mem_krylov n hn A b ((k : ℕ) + 1)
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

private lemma p37_apply_mem_next_consecutive
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ p37ConsecutiveSpan v s m) :
    A x ∈ p37ConsecutiveSpan v s (m + 1) := by
  rw [p37ConsecutiveSpan] at hx ⊢
  refine Submodule.span_induction (p := fun x _ ↦ A x ∈
    Submodule.span ℝ (Set.range fun k : Fin (m + 1) ↦ v (s + (k : ℕ))))
    ?_ (by change A 0 ∈ _; simpa) ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    have hs := hstep (s + (k : ℕ))
    change v (s + (k : ℕ) + 1) =
      A (v (s + (k : ℕ))) + p (s + (k : ℕ)) • v (s + (k : ℕ)) at hs
    rw [eq_sub_of_add_eq hs.symm]
    apply Submodule.sub_mem
    · apply Submodule.subset_span
      exact ⟨⟨(k : ℕ) + 1, by omega⟩,
        by simp only [Fin.val_mk, Int.natCast_add, Int.natCast_one, add_assoc]⟩
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨(k : ℕ), by omega⟩, rfl⟩
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

private lemma p37_consecutive_eq_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j)) (s : ℤ) :
    p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n := by
  have hforward : ∀ m : ℕ,
      v (s + (m : ℕ)) ∈ p37KrylovSpan A (v s) n := by
    intro m
    induction m with
    | zero =>
        simpa using p37_pow_mem_krylov n hn A (v s) 0
    | succ m ih =>
        rw [show s + ((m + 1 : ℕ) : ℤ) = (s + (m : ℕ)) + 1 by
          push_cast; omega]
        rw [hstep]
        change A (v (s + (m : ℕ))) +
          p (s + (m : ℕ)) • v (s + (m : ℕ)) ∈
            p37KrylovSpan A (v s) n
        exact Submodule.add_mem _
          (p37_apply_mem_krylov n hn A (v s) _ ih)
          (Submodule.smul_mem _ _ ih)
  have hpowerPrefix : ∀ m : ℕ,
      (A ^ m) (v s) ∈ p37ConsecutiveSpan v s (m + 1) := by
    intro m
    induction m with
    | zero =>
        simp only [pow_zero]
        change v s ∈ p37ConsecutiveSpan v s (0 + 1)
        apply Submodule.subset_span
        exact ⟨⟨0, by omega⟩, by simp⟩
    | succ m ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact p37_apply_mem_next_consecutive A p v hstep s (m + 1) _ ih
  apply le_antisymm
  · rw [p37ConsecutiveSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hforward k
  · rw [p37KrylovSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    apply (show p37ConsecutiveSpan v s ((k : ℕ) + 1) ≤
        p37ConsecutiveSpan v s n from ?_) (hpowerPrefix k)
    rw [p37ConsecutiveSpan, p37ConsecutiveSpan]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), by omega⟩, rfl⟩

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
  have hadj (j : ℤ) :
      p37KrylovSpan A (v (j + 1)) n = p37KrylovSpan A (v j) n := by
    rw [hstep j]
    exact p37_krylov_shift_eq n hn A (p j) (v j) (hinv j)
  have hall : ∀ j : ℤ,
      p37KrylovSpan A (v j) n = p37KrylovSpan A (v s) n := by
    intro j
    refine Int.inductionOn' j s rfl ?_ ?_
    · intro k _ ih
      exact (hadj k).trans ih
    · intro k _ ih
      have h := hadj (k - 1)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm.trans ih
  have hconsecutive :
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n :=
    p37_consecutive_eq_krylov n hn A p v hstep s
  have htwo_le : p37TwoSidedSpan v ≤ p37KrylovSpan A (v s) n := by
    rw [p37TwoSidedSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : v j ∈ p37KrylovSpan A (v j) n := by
      simpa using p37_pow_mem_krylov n hn A (v j) 0
    rw [hall j] at hj
    exact hj
  have htwo_ge : p37KrylovSpan A (v s) n ≤ p37TwoSidedSpan v := by
    rw [← hconsecutive, p37ConsecutiveSpan, p37TwoSidedSpan,
      Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    apply Submodule.subset_span
    exact ⟨s + (k : ℕ), rfl⟩
  have htwo : p37TwoSidedSpan v = p37KrylovSpan A (v s) n :=
    le_antisymm htwo_le htwo_ge
  refine ⟨htwo.trans hconsecutive.symm, hconsecutive, ?_⟩
  simpa [hv0] using (hall 0).symm

end HighamBench
