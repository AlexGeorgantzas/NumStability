import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_aeval_mem_krylov
    (n : ℕ) (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (q : Polynomial ℝ) (hq : q.natDegree < n) :
    (Polynomial.aeval A q) b ∈ p37KrylovSpan A b n := by
  rw [p37KrylovSpan]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  change q.coeff i • (A ^ i) b ∈ _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨i, ?_⟩, ?_⟩
  · have hi_le : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact lt_of_le_of_lt hi_le hq
  · simp

private lemma p37_pow_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (k : ℕ) :
    (A ^ k) b ∈ p37KrylovSpan A b n := by
  have hchar_ne : A.charpoly ≠ 1 := by
    intro h
    have hdeg := A.charpoly_natDegree
    rw [h] at hdeg
    simp at hdeg
    omega
  rw [A.pow_eq_aeval_mod_charpoly k]
  apply p37_aeval_mem_krylov
  have hrem := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k)
    A.charpoly_monic hchar_ne
  simpa [A.charpoly_natDegree, Module.finrank_fin_fun] using hrem

private lemma p37_A_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ)
    (hx : x ∈ p37KrylovSpan A b n) :
    A x ∈ p37KrylovSpan A b n := by
  rw [p37KrylovSpan] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      simpa [pow_succ'] using p37_pow_mem_krylov n hn A b (k.val + 1)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ihx => simpa using Submodule.smul_mem _ c ihx

private lemma p37_shift_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ)
    (c : ℝ) (hx : x ∈ p37KrylovSpan A b n) :
    p37Shift A c x ∈ p37KrylovSpan A b n := by
  change A x + c • x ∈ p37KrylovSpan A b n
  exact Submodule.add_mem _ (p37_A_mem_krylov n hn A b x hx)
    (Submodule.smul_mem _ c hx)

private lemma p37_preimage_mem
    (n : ℕ) (T : Module.End ℝ (Fin n → ℝ)) (K : Submodule ℝ (Fin n → ℝ))
    (hT : Function.Bijective T) (hstable : ∀ x ∈ K, T x ∈ K)
    {x y : Fin n → ℝ} (hx : x ∈ K) (hy : T y = x) : y ∈ K := by
  let Tr : K →ₗ[ℝ] K := T.restrict hstable
  have hTr_inj : Function.Injective Tr := by
    intro a b hab
    apply Subtype.ext
    apply hT.1
    exact congrArg Subtype.val hab
  have hTr_surj : Function.Surjective Tr :=
    LinearMap.surjective_of_injective hTr_inj
  obtain ⟨z, hz⟩ := hTr_surj ⟨x, hx⟩
  have hz' : T (z : Fin n → ℝ) = x := congrArg Subtype.val hz
  have hzy : (z : Fin n → ℝ) = y := hT.1 (hz'.trans hy.symm)
  rw [← hzy]
  exact z.property

private lemma p37_forward_mem
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (k : ℕ) :
    v (s + (k : ℤ)) ∈ p37KrylovSpan A (v s) n := by
  induction k with
  | zero =>
      simpa using (Submodule.subset_span
        (show v s ∈ Set.range (fun i : Fin n ↦ (A ^ (i : ℕ)) (v s)) from
          ⟨⟨0, hn⟩, by simp⟩))
  | succ k ih =>
      rw [show s + ((k + 1 : ℕ) : ℤ) = (s + (k : ℤ)) + 1 by push_cast; ring]
      rw [hstep]
      exact p37_shift_mem_krylov n hn A (v s) (v (s + (k : ℤ)))
        (p (s + (k : ℤ))) ih

private lemma p37_consecutive_le_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) :
    p37ConsecutiveSpan v s n ≤ p37KrylovSpan A (v s) n := by
  rw [p37ConsecutiveSpan]
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact p37_forward_mem n hn A p v hstep s k.val

private lemma p37_consecutive_mono
    {n : ℕ} (v : ℤ → Fin n → ℝ) (s : ℤ) {m l : ℕ} (hml : m ≤ l) :
    p37ConsecutiveSpan v s m ≤ p37ConsecutiveSpan v s l := by
  rw [p37ConsecutiveSpan, p37ConsecutiveSpan]
  apply Submodule.span_mono
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k.val, lt_of_lt_of_le k.isLt hml⟩, rfl⟩

private lemma p37_A_consecutive_mem
    {n m : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (x : Fin n → ℝ) (hx : x ∈ p37ConsecutiveSpan v s m) :
    A x ∈ p37ConsecutiveSpan v s (m + 1) := by
  rw [p37ConsecutiveSpan] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      have hcur : v (s + (k.val : ℤ)) ∈
          Submodule.span ℝ (Set.range fun i : Fin (m + 1) ↦ v (s + (i : ℕ))) :=
        Submodule.subset_span ⟨⟨k.val, Nat.lt_succ_of_lt k.isLt⟩, rfl⟩
      have hnxt : v (s + (k.val : ℤ) + 1) ∈
          Submodule.span ℝ (Set.range fun i : Fin (m + 1) ↦ v (s + (i : ℕ))) := by
        apply Submodule.subset_span
        refine ⟨⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩, ?_⟩
        simp [Nat.cast_add, add_assoc]
      have heq : A (v (s + (k.val : ℤ))) =
          v (s + (k.val : ℤ) + 1) - p (s + (k.val : ℤ)) • v (s + (k.val : ℤ)) := by
        rw [hstep]
        simp [p37Shift]
      rw [heq]
      exact Submodule.sub_mem _ hnxt (Submodule.smul_mem _ _ hcur)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ihx => simpa using Submodule.smul_mem _ c ihx

private lemma p37_pow_mem_consecutive
    {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) (k : ℕ) :
    (A ^ k) (v s) ∈ p37ConsecutiveSpan v s (k + 1) := by
  induction k with
  | zero =>
      rw [p37ConsecutiveSpan]
      simpa using (Submodule.subset_span
        (show v s ∈ Set.range (fun i : Fin 1 ↦ v (s + (i : ℕ))) from
          ⟨⟨0, Nat.zero_lt_one⟩, by simp⟩))
  | succ k ih =>
      simpa [pow_succ'] using p37_A_consecutive_mem A p v hstep s ((A ^ k) (v s)) ih

private lemma p37_krylov_le_consecutive
    (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) :
    p37KrylovSpan A (v s) n ≤ p37ConsecutiveSpan v s n := by
  rw [p37KrylovSpan]
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact p37_consecutive_mono v s (Nat.succ_le_iff.mpr k.isLt)
    (p37_pow_mem_consecutive A p v hstep s k.val)

private lemma p37_consecutive_eq_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (s : ℤ) :
    p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n :=
  le_antisymm (p37_consecutive_le_krylov n hn A p v hstep s)
    (p37_krylov_le_consecutive n A p v hstep s)

private lemma p37_all_v_mem_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s j : ℤ) :
    v j ∈ p37KrylovSpan A (v s) n := by
  refine Int.inductionOn' j s ?_ ?_ ?_
  · simpa using p37_forward_mem n hn A p v hstep s 0
  · intro k hsk hk
    rw [hstep]
    exact p37_shift_mem_krylov n hn A (v s) (v k) (p k) hk
  · intro k hks hk
    apply p37_preimage_mem n (p37Shift A (p (k - 1)))
      (p37KrylovSpan A (v s) n) (hinv (k - 1))
      (fun x hx ↦ p37_shift_mem_krylov n hn A (v s) x (p (k - 1)) hx)
      hk
    simpa using (hstep (k - 1)).symm

private lemma p37_consecutive_le_two_sided
    {n m : ℕ} (v : ℤ → Fin n → ℝ) (s : ℤ) :
    p37ConsecutiveSpan v s m ≤ p37TwoSidedSpan v := by
  rw [p37ConsecutiveSpan, p37TwoSidedSpan]
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact Submodule.subset_span ⟨s + (k.val : ℤ), rfl⟩

private lemma p37_two_sided_eq_krylov
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s : ℤ) :
    p37TwoSidedSpan v = p37KrylovSpan A (v s) n := by
  apply le_antisymm
  · rw [p37TwoSidedSpan]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact p37_all_v_mem_krylov n hn A p v hstep hinv s j
  · rw [← p37_consecutive_eq_krylov n hn A p v hstep s]
    exact p37_consecutive_le_two_sided v s

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
  have hconsecutive := p37_consecutive_eq_krylov n hn A p v hstep s
  have htwo := p37_two_sided_eq_krylov n hn A p v hstep hinv s
  have htwo_zero := p37_two_sided_eq_krylov n hn A p v hstep hinv 0
  refine ⟨?_, hconsecutive, ?_⟩
  · exact htwo.trans hconsecutive.symm
  · calc
      p37KrylovSpan A (v s) n = p37TwoSidedSpan v := htwo.symm
      _ = p37KrylovSpan A (v 0) n := htwo_zero
      _ = p37KrylovSpan A B n := by rw [hv0]

end HighamBench
