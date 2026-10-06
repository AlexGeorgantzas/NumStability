import HighamBench.P37Definitions

namespace HighamBench

open Polynomial

private def prefixSpan {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun i : Fin m ↦ w i)

private lemma prefixSpan_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) {m l : ℕ} (hml : m ≤ l) :
    prefixSpan w m ≤ prefixSpan w l := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hml⟩, rfl⟩

private lemma map_mem_krylov_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m : ℕ} {x : V}
    (hx : x ∈ prefixSpan (fun k ↦ (A ^ k) b) m) :
    A x ∈ prefixSpan (fun k ↦ (A ^ k) b) (m + 1) := by
  refine Submodule.span_induction
    (p := fun y _ ↦ A y ∈ prefixSpan (fun k ↦ (A ^ k) b) (m + 1))
    ?_ (by simp) ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    have hmem : (A ^ (i.val + 1)) b ∈
        prefixSpan (fun k ↦ (A ^ k) b) (m + 1) :=
      Submodule.subset_span ⟨⟨i.val + 1, by omega⟩, rfl⟩
    simpa [pow_succ', Module.End.mul_apply] using hmem
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa using Submodule.smul_mem _ c hx

private lemma triangular_prefix_eq_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (w : ℕ → V) (c : ℕ → ℝ)
    (hrec : ∀ k, w (k + 1) = A (w k) + c k • w k) (m : ℕ) :
    prefixSpan w m = prefixSpan (fun k ↦ (A ^ k) (w 0)) m := by
  have hA_prefix : ∀ {r : ℕ} {x : V}, x ∈ prefixSpan w r →
      A x ∈ prefixSpan w (r + 1) := by
    intro r x hx
    refine Submodule.span_induction
      (p := fun y _ ↦ A y ∈ prefixSpan w (r + 1))
      ?_ (by simp) ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      have hi : w i.val ∈ prefixSpan w (r + 1) :=
        Submodule.subset_span ⟨⟨i.val, by omega⟩, rfl⟩
      have his : w (i.val + 1) ∈ prefixSpan w (r + 1) :=
        Submodule.subset_span ⟨⟨i.val + 1, by omega⟩, rfl⟩
      rw [hrec i.val] at his
      simpa using
        (Submodule.sub_mem _ his (Submodule.smul_mem _ (c i.val) hi))
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro a x _ hx
      simpa using Submodule.smul_mem _ a hx
  have hw : ∀ k : ℕ, w k ∈ prefixSpan (fun i ↦ (A ^ i) (w 0)) (k + 1) := by
    intro k
    induction k with
    | zero =>
        exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp⟩
    | succ k ih =>
        rw [hrec k]
        exact Submodule.add_mem _
          (map_mem_krylov_succ A (w 0) ih)
          (Submodule.smul_mem _ _
            (prefixSpan_mono _ (by omega : k + 1 ≤ (k + 1) + 1) ih))
  have hpow : ∀ k : ℕ, (A ^ k) (w 0) ∈ prefixSpan w (k + 1) := by
    intro k
    induction k with
    | zero =>
        exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp⟩
    | succ k ih =>
        simpa [pow_succ', Module.End.mul_apply] using hA_prefix ih
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    exact prefixSpan_mono _ (Nat.succ_le_iff.2 i.isLt) (hw i)
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    exact prefixSpan_mono _ (Nat.succ_le_iff.2 i.isLt) (hpow i)

private lemma polynomial_apply_mem_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (n : ℕ) (q : ℝ[X])
    (hq : q.degree < n) :
    (Polynomial.aeval A q) b ∈ prefixSpan (fun k ↦ (A ^ k) b) n := by
  have hrange :
      (↑(Finset.image (fun k : ℕ ↦ (Polynomial.X : ℝ[X]) ^ k)
        (Finset.range n)) : Set ℝ[X]) =
        Set.range (fun i : Fin n ↦ (Polynomial.X : ℝ[X]) ^ (i : ℕ)) := by
    ext r
    constructor
    · intro hr
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      exact ⟨i.val, i.isLt, rfl⟩
  have hqspan : q ∈
      Submodule.span ℝ
        (Set.range (fun i : Fin n ↦ (Polynomial.X : ℝ[X]) ^ (i : ℕ))) := by
    rw [← hrange, ← Polynomial.degreeLT_eq_span_X_pow]
    exact Polynomial.mem_degreeLT.2 hq
  let F : ℝ[X] →ₗ[ℝ] V :=
    (LinearMap.applyₗ b).comp (Polynomial.aeval A).toLinearMap
  have hF : F q ∈ prefixSpan (fun k ↦ (A ^ k) b) n := by
    refine Submodule.span_induction
      (p := fun r _ ↦ F r ∈ prefixSpan (fun k ↦ (A ^ k) b) n)
      ?_ (by simp [F]) ?_ ?_ hqspan
    · rintro r ⟨i, rfl⟩
      have hmem : (A ^ (i : ℕ)) b ∈ prefixSpan (fun k ↦ (A ^ k) b) n :=
        Submodule.subset_span ⟨i, rfl⟩
      simpa [F] using hmem
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro a x _ hx
      simpa using Submodule.smul_mem _ a hx
  simpa [F] using hF

private lemma all_powers_mem_fin_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ prefixSpan (fun i ↦ (A ^ i) b) n := by
  let q : ℝ[X] := (Polynomial.X ^ k) %ₘ A.charpoly
  have hcpdeg : A.charpoly.natDegree = n := by
    simpa using A.charpoly_natDegree
  have hcp_ne_one : A.charpoly ≠ 1 := by
    intro h
    have : n = 0 := by simpa [h] using hcpdeg.symm
    omega
  have hqdeg : q.degree < n := by
    have h := Polynomial.degree_modByMonic_lt (Polynomial.X ^ k) A.charpoly_monic
    rw [Polynomial.degree_eq_natDegree A.charpoly_monic.ne_zero, hcpdeg] at h
    simpa [q] using h
  have hmem := polynomial_apply_mem_krylov A b n q hqdeg
  rw [A.pow_eq_aeval_mod_charpoly k]
  exact hmem

private lemma fin_krylov_map_mem (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) {x : Fin n → ℝ}
    (hx : x ∈ prefixSpan (fun k ↦ (A ^ k) b) n) :
    A x ∈ prefixSpan (fun k ↦ (A ^ k) b) n := by
  refine Submodule.span_induction
    (p := fun y _ ↦ A y ∈ prefixSpan (fun k ↦ (A ^ k) b) n)
    ?_ (by simp) ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    simpa [pow_succ', Module.End.mul_apply] using
      (all_powers_mem_fin_krylov n hn A b (i.val + 1))
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa using Submodule.smul_mem _ a hx

private lemma mem_of_injective_map_mem
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (K : Submodule ℝ V) (f : Module.End ℝ V)
    (hstable : ∀ x ∈ K, f x ∈ K) (hinj : Function.Injective f)
    {x : V} (hx : f x ∈ K) : x ∈ K := by
  let g : K →ₗ[ℝ] K := f.restrict hstable
  have hginj : Function.Injective g := by
    intro y z hyz
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hyz
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hginj ⟨f x, hx⟩
  have heq : (y : V) = x := by
    apply hinj
    exact congrArg Subtype.val hy
  simpa [heq] using y.property

private lemma all_shifted_vectors_mem_krylov
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p37Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p37Shift A (p j)))
    (s j : ℤ) :
    v j ∈ prefixSpan (fun k ↦ (A ^ k) (v s)) n := by
  let K := prefixSpan (fun k ↦ (A ^ k) (v s)) n
  have hAstable : ∀ x ∈ K, A x ∈ K := by
    intro x hx
    exact fin_krylov_map_mem n hn A (v s) hx
  have hshift : ∀ t x, x ∈ K → p37Shift A (p t) x ∈ K := by
    intro t x hx
    exact Submodule.add_mem K (hAstable x hx) (Submodule.smul_mem K (p t) hx)
  change v j ∈ K
  refine Int.inductionOn' j s ?_ ?_ ?_
  · exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
  · intro k _ hk
    rw [hstep k]
    exact hshift k (v k) hk
  · intro k _ hk
    have hrel : p37Shift A (p (k - 1)) (v (k - 1)) = v k := by
      rw [← hstep (k - 1)]
      congr 1
      omega
    apply mem_of_injective_map_mem K (p37Shift A (p (k - 1)))
      (hshift (k - 1)) (hinv (k - 1)).1
    simpa [hrel] using hk

private lemma fin_krylov_le_of_mem (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b c : Fin n → ℝ)
    (hb : b ∈ prefixSpan (fun k ↦ (A ^ k) c) n) :
    prefixSpan (fun k ↦ (A ^ k) b) n ≤
      prefixSpan (fun k ↦ (A ^ k) c) n := by
  have hpows : ∀ k : ℕ, (A ^ k) b ∈ prefixSpan (fun i ↦ (A ^ i) c) n := by
    intro k
    induction k with
    | zero => simpa using hb
    | succ k ih =>
        simpa [pow_succ', Module.End.mul_apply] using
          (fin_krylov_map_mem n hn A c ih)
  apply Submodule.span_le.2
  rintro x ⟨i, rfl⟩
  exact hpows i

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
  let w : ℕ → (Fin n → ℝ) := fun k ↦ v (s + (k : ℕ))
  let c : ℕ → ℝ := fun k ↦ p (s + (k : ℕ))
  have hrec : ∀ k, w (k + 1) = A (w k) + c k • w k := by
    intro k
    dsimp [w, c]
    rw [show s + ((k : ℤ) + 1) = (s + (k : ℕ)) + 1 by omega]
    rw [hstep]
    rfl
  have hconsecutive :
      p37ConsecutiveSpan v s n = p37KrylovSpan A (v s) n := by
    have h := triangular_prefix_eq_krylov A w c hrec n
    simpa [p37ConsecutiveSpan, p37KrylovSpan, prefixSpan, w] using h
  have hall_s : ∀ j : ℤ, v j ∈ p37KrylovSpan A (v s) n := by
    intro j
    simpa [p37KrylovSpan, prefixSpan] using
      (all_shifted_vectors_mem_krylov n hn A p v hstep hinv s j)
  have htwo_le : p37TwoSidedSpan v ≤ p37KrylovSpan A (v s) n := by
    apply Submodule.span_le.2
    rintro x ⟨j, rfl⟩
    exact hall_s j
  have hconsecutive_le_two : p37ConsecutiveSpan v s n ≤ p37TwoSidedSpan v := by
    apply Submodule.span_le.2
    rintro x ⟨k, rfl⟩
    exact Submodule.subset_span ⟨s + (k : ℕ), rfl⟩
  have htwo : p37TwoSidedSpan v = p37ConsecutiveSpan v s n := by
    apply le_antisymm
    · simpa [hconsecutive] using htwo_le
    · exact hconsecutive_le_two
  have hall_zero : ∀ j : ℤ, v j ∈ p37KrylovSpan A (v 0) n := by
    intro j
    simpa [p37KrylovSpan, prefixSpan] using
      (all_shifted_vectors_mem_krylov n hn A p v hstep hinv 0 j)
  have hKs_le_K0 : p37KrylovSpan A (v s) n ≤ p37KrylovSpan A (v 0) n := by
    simpa [p37KrylovSpan, prefixSpan] using
      (fin_krylov_le_of_mem n hn A (v s) (v 0) (hall_zero s))
  have hK0_le_Ks : p37KrylovSpan A (v 0) n ≤ p37KrylovSpan A (v s) n := by
    simpa [p37KrylovSpan, prefixSpan] using
      (fin_krylov_le_of_mem n hn A (v 0) (v s) (hall_s 0))
  have hK : p37KrylovSpan A (v s) n = p37KrylovSpan A (v 0) n :=
    le_antisymm hKs_le_K0 hK0_le_Ks
  refine ⟨htwo, hconsecutive, ?_⟩
  simpa [hv0] using hK

end HighamBench
