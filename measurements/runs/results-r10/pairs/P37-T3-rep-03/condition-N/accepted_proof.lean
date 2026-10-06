import HighamBench.P37Definitions

namespace HighamBench

open Polynomial

private lemma p37_all_powers_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p37KrylovSpan A b n := by
  classical
  let q : ℝ[X] := X ^ k %ₘ A.charpoly
  have hcp : A.charpoly ≠ 1 := by
    intro h
    have hdeg := A.charpoly_natDegree
    rw [h, natDegree_one, Module.finrank_fin_fun] at hdeg
    omega
  have hqdeg : q.natDegree < n := by
    dsimp [q]
    simpa [A.charpoly_natDegree, Module.finrank_fin_fun] using
      (natDegree_modByMonic_lt (X ^ k : ℝ[X]) A.charpoly_monic hcp)
  have heval : (A ^ k) b = aeval A q b := by
    exact DFunLike.congr_fun (A.pow_eq_aeval_mod_charpoly k) b
  rw [heval, q.as_sum_range_C_mul_X_pow' hqdeg]
  simp only [map_sum, map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply,
    LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, one_mul]
  apply Submodule.sum_mem
  intro i hi
  change q.coeff i • (A ^ i) b ∈ p37KrylovSpan A b n
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

private lemma p37_krylov_invariant
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) :
    ∀ x ∈ p37KrylovSpan A b n, A x ∈ p37KrylovSpan A b n := by
  classical
  intro x hx
  refine Submodule.span_induction ?_ ?_ (fun x y _ _ hx hy ↦ ?_)
    (fun c x _ hx ↦ ?_) hx
  · rintro _ ⟨i, rfl⟩
    simpa [pow_succ'] using p37_all_powers_mem_krylov n hn A b (i + 1)
  · simpa using (p37KrylovSpan A b n).zero_mem
  · simpa using (p37KrylovSpan A b n).add_mem hx hy
  · simpa using (p37KrylovSpan A b n).smul_mem c hx

private lemma p37_shift_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (c : ℝ) {x : Fin n → ℝ}
    (hx : x ∈ p37KrylovSpan A b n) :
    p37Shift A c x ∈ p37KrylovSpan A b n := by
  rw [p37Shift]
  exact (p37KrylovSpan A b n).add_mem
    (p37_krylov_invariant n hn A b x hx) ((p37KrylovSpan A b n).smul_mem c hx)

private lemma p37_sequence_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (t j : ℤ) : v j ∈ p37KrylovSpan A (v t) n := by
  classical
  let K := p37KrylovSpan A (v t) n
  have hbase : v t ∈ K := by
    exact Submodule.subset_span ⟨⟨0, hn⟩, by simp [K, p37KrylovSpan]⟩
  have hforward : ∀ k : ℕ, v (t + (k : ℤ)) ∈ K := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
        rw [show t + ((k + 1 : ℕ) : ℤ) = (t + (k : ℤ)) + 1 by omega, hstep]
        exact p37_shift_mem_krylov n hn A (v t) _ ih
  have hbackward : ∀ k : ℕ, v (t - (k : ℤ)) ∈ K := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
        let r : ℤ := t - ((k + 1 : ℕ) : ℤ)
        have hnext : v (r + 1) ∈ K := by
          have hr : r + 1 = t - (k : ℤ) := by
            dsimp [r]
            push_cast
            omega
          rw [hr]
          exact ih
        have hmaps : Set.MapsTo (p37Shift A (p r)) K K := by
          intro x hx
          exact p37_shift_mem_krylov n hn A (v t) _ hx
        have hsurj : Set.SurjOn (p37Shift A (p r)) K K :=
          (LinearMap.injOn_iff_surjOn hmaps).mp (hinv r).1.injOn
        obtain ⟨x, hx, hxeq⟩ := hsurj hnext
        have hxv : x = v r := by
          apply (hinv r).1
          calc
            p37Shift A (p r) x = v (r + 1) := hxeq
            _ = p37Shift A (p r) (v r) := hstep r
        have hvr : v r ∈ K := hxv ▸ hx
        simpa [r] using hvr
  by_cases h : t ≤ j
  · let k := (j - t).natAbs
    have hk : (k : ℤ) = j - t := by
      rw [Int.natCast_natAbs, abs_of_nonneg (sub_nonneg.mpr h)]
    have hj : j = t + (k : ℤ) := by omega
    rw [hj]
    exact hforward k
  · have h' : j ≤ t := le_of_not_ge h
    let k := (t - j).natAbs
    have hk : (k : ℤ) = t - j := by
      rw [Int.natCast_natAbs, abs_of_nonneg (sub_nonneg.mpr h')]
    have hj : j = t - (k : ℤ) := by omega
    rw [hj]
    exact hbackward k

private lemma p37_A_maps_consecutive_to_next
    (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (t : ℤ) (m : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ p37ConsecutiveSpan v t m) :
    A x ∈ p37ConsecutiveSpan v t (m + 1) := by
  classical
  refine Submodule.span_induction ?_ ?_ (fun x y _ _ hx hy ↦ ?_)
    (fun c x _ hx ↦ ?_) hx
  · rintro _ ⟨i, rfl⟩
    let i0 : Fin (m + 1) := ⟨i, Nat.lt_succ_of_lt i.isLt⟩
    let i1 : Fin (m + 1) := ⟨i + 1, Nat.succ_lt_succ i.isLt⟩
    have h0 : v (t + (i : ℕ)) ∈ p37ConsecutiveSpan v t (m + 1) := by
      exact Submodule.subset_span ⟨i0, by simp [i0]⟩
    have h1 : v ((t + (i : ℕ)) + 1) ∈ p37ConsecutiveSpan v t (m + 1) := by
      apply Submodule.subset_span
      refine ⟨i1, ?_⟩
      simp [i1]
      congr 1
      abel
    have heq : A (v (t + (i : ℕ))) =
        v ((t + (i : ℕ)) + 1) - p (t + (i : ℕ)) • v (t + (i : ℕ)) := by
      rw [hstep, p37Shift]
      simp
    rw [heq]
    exact (p37ConsecutiveSpan v t (m + 1)).sub_mem h1
      ((p37ConsecutiveSpan v t (m + 1)).smul_mem _ h0)
  · simpa using (p37ConsecutiveSpan v t (m + 1)).zero_mem
  · simpa using (p37ConsecutiveSpan v t (m + 1)).add_mem hx hy
  · simpa using (p37ConsecutiveSpan v t (m + 1)).smul_mem c hx

private lemma p37_power_mem_consecutive_prefix
    (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (t : ℤ) (k : ℕ) :
    (A ^ k) (v t) ∈ p37ConsecutiveSpan v t (k + 1) := by
  induction k with
  | zero =>
      exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp [p37ConsecutiveSpan]⟩
  | succ k ih =>
      have hm := p37_A_maps_consecutive_to_next n A p v hstep t (k + 1) ih
      simpa [pow_succ'] using hm

private lemma p37_consecutive_eq_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (t : ℤ) :
    p37ConsecutiveSpan v t n = p37KrylovSpan A (v t) n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact p37_sequence_mem_krylov n hn A p v hstep hinv t _
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hpow := p37_power_mem_consecutive_prefix n A p v hstep t (k : ℕ)
    apply (Submodule.span_mono ?_) hpow
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i, ?_⟩, rfl⟩
    exact lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)

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
  have hfullK : ∀ t : ℤ,
      p37TwoSidedSpan v = p37KrylovSpan A (v t) n := by
    intro t
    have hCK := p37_consecutive_eq_krylov n hn A p v hstep hinv t
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact p37_sequence_mem_krylov n hn A p v hstep hinv t j
    · rw [← hCK]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨t + (i : ℕ), rfl⟩
  have hCKs := p37_consecutive_eq_krylov n hn A p v hstep hinv s
  refine ⟨(hfullK s).trans hCKs.symm, hCKs, ?_⟩
  calc
    p37KrylovSpan A (v s) n = p37TwoSidedSpan v := (hfullK s).symm
    _ = p37KrylovSpan A (v 0) n := hfullK 0
    _ = p37KrylovSpan A B n := by rw [hv0]

end HighamBench
