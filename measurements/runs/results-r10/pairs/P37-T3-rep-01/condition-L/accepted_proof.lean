import HighamBench.P37Definitions

namespace HighamBench

private lemma p37_span_fin_eq_of_triangular
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : ℕ → V)
    (htri : ∀ k, f k - g k ∈
      Submodule.span ℝ (Set.range fun i : Fin k ↦ g (i : ℕ))) :
    ∀ m, Submodule.span ℝ (Set.range fun i : Fin m ↦ f (i : ℕ)) =
      Submodule.span ℝ (Set.range fun i : Fin m ↦ g (i : ℕ)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : (i : ℕ) < m
        · have hf : f (i : ℕ) ∈
              Submodule.span ℝ (Set.range fun j : Fin m ↦ f (j : ℕ)) :=
            Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
          rw [ih] at hf
          exact (Submodule.span_mono (by
            rintro _ ⟨j, rfl⟩
            exact ⟨⟨j, Nat.lt.step j.isLt⟩, rfl⟩)) hf
        · have him : (i : ℕ) = m := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
          change f (i : ℕ) ∈ _
          rw [him, ← sub_add_cancel (f m) (g m)]
          apply Submodule.add_mem
          · exact (Submodule.span_mono (by
              rintro _ ⟨j, rfl⟩
              exact ⟨⟨j, Nat.lt.step j.isLt⟩, rfl⟩)) (htri m)
          · exact Submodule.subset_span ⟨⟨m, Nat.lt_succ_self m⟩, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : (i : ℕ) < m
        · have hg : g (i : ℕ) ∈
              Submodule.span ℝ (Set.range fun j : Fin m ↦ g (j : ℕ)) :=
            Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
          rw [← ih] at hg
          exact (Submodule.span_mono (by
            rintro _ ⟨j, rfl⟩
            exact ⟨⟨j, Nat.lt.step j.isLt⟩, rfl⟩)) hg
        · have him : (i : ℕ) = m := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
          change g (i : ℕ) ∈ _
          rw [him, ← sub_sub_cancel (f m) (g m)]
          apply Submodule.sub_mem
          · exact Submodule.subset_span ⟨⟨m, Nat.lt_succ_self m⟩, rfl⟩
          · have hd := htri m
            rw [← ih] at hd
            exact (Submodule.span_mono (by
              rintro _ ⟨j, rfl⟩
              exact ⟨⟨j, Nat.lt.step j.isLt⟩, rfl⟩)) hd

private lemma p37_consecutive_eq_krylov
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (w : ℕ → V) (q : ℕ → ℝ)
    (hstep : ∀ k, w (k + 1) = A (w k) + q k • w k) :
    ∀ m, Submodule.span ℝ (Set.range fun i : Fin m ↦ w (i : ℕ)) =
      p37KrylovSpan A (w 0) m := by
  have htri : ∀ k, w k - (A ^ k) (w 0) ∈ p37KrylovSpan A (w 0) k := by
    intro k
    induction k with
    | zero => simp [p37KrylovSpan]
    | succ k ih =>
        have hAih : A (w k - (A ^ k) (w 0)) ∈ p37KrylovSpan A (w 0) (k + 1) := by
          refine Submodule.span_induction (p := fun x _ ↦ A x ∈
            p37KrylovSpan A (w 0) (k + 1)) ?_ ?_ ?_ ?_ ih
          · intro x hx
            obtain ⟨i, rfl⟩ := hx
            exact Submodule.subset_span ⟨⟨i + 1, Nat.add_lt_add_right i.isLt 1⟩, by
              simp [pow_succ', Module.End.mul_apply]⟩
          · simp
          · intro x y _ _ hx hy
            simpa using Submodule.add_mem _ hx hy
          · intro c x _ hx
            simpa using Submodule.smul_mem _ c hx
        have hwk : w k ∈ p37KrylovSpan A (w 0) (k + 1) := by
          rw [← sub_add_cancel (w k) ((A ^ k) (w 0))]
          exact Submodule.add_mem _
            ((Submodule.span_mono (by
              rintro _ ⟨i, rfl⟩
              exact ⟨⟨i, Nat.lt.step i.isLt⟩, rfl⟩)) ih)
            (Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)
        have heq : w (k + 1) - (A ^ (k + 1)) (w 0) =
            A (w k - (A ^ k) (w 0)) + q k • w k := by
          rw [hstep k]
          simp only [pow_succ', Module.End.mul_apply, map_sub]
          module
        rw [heq]
        exact Submodule.add_mem _ hAih (Submodule.smul_mem _ (q k) hwk)
  intro m
  exact p37_span_fin_eq_of_triangular w (fun k ↦ (A ^ k) (w 0)) htri m

private lemma p37_krylov_invariant
    (n : ℕ) (hn : 0 < n) (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) :
    ∀ x ∈ p37KrylovSpan A b n, A x ∈ p37KrylovSpan A b n := by
  let r : Polynomial ℝ := Polynomial.X ^ n %ₘ A.charpoly
  have hdeg : A.charpoly.natDegree = n := by
    simpa using A.charpoly_natDegree
  have hne : A.charpoly ≠ 1 := by
    intro heq
    have := congrArg Polynomial.natDegree heq
    simp [hdeg] at this
    omega
  have hrdeg : r.natDegree < n := by
    exact (Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hne).trans_eq hdeg
  have hAn : (A ^ n) b ∈ p37KrylovSpan A b n := by
    rw [A.pow_eq_aeval_mod_charpoly n]
    change (Polynomial.aeval A r) b ∈ _
    rw [Polynomial.aeval_eq_sum_range' hrdeg A]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  intro x hx
  refine Submodule.span_induction (p := fun x _ ↦ A x ∈ p37KrylovSpan A b n)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : (i : ℕ) + 1 < n
    · exact Submodule.subset_span ⟨⟨i + 1, hi⟩, by
        simp [pow_succ', Module.End.mul_apply]⟩
    · have hin : (i : ℕ) + 1 = n := by omega
      rw [← Module.End.mul_apply, ← pow_succ', hin]
      exact hAn
  · simp
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa using Submodule.smul_mem _ c hx

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
  have hall : ∀ t : ℤ,
      p37TwoSidedSpan v = p37KrylovSpan A (v t) n ∧
      p37ConsecutiveSpan v t n = p37KrylovSpan A (v t) n := by
    intro t
    let w : ℕ → (Fin n → ℝ) := fun k ↦ v (t + (k : ℕ))
    let q : ℕ → ℝ := fun k ↦ p (t + (k : ℕ))
    have hwstep : ∀ k, w (k + 1) = A (w k) + q k • w k := by
      intro k
      simpa [w, q, p37Shift, add_assoc] using hstep (t + (k : ℕ))
    have hcons : p37ConsecutiveSpan v t n = p37KrylovSpan A (v t) n := by
      simpa [p37ConsecutiveSpan, w] using p37_consecutive_eq_krylov A w q hwstep n
    have hAinv : ∀ x ∈ p37KrylovSpan A (v t) n,
        A x ∈ p37KrylovSpan A (v t) n :=
      p37_krylov_invariant n hn A (v t)
    have hshift : ∀ j x, x ∈ p37KrylovSpan A (v t) n →
        p37Shift A (p j) x ∈ p37KrylovSpan A (v t) n := by
      intro j x hx
      simp only [p37Shift, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact Submodule.add_mem _ (hAinv x hx) (Submodule.smul_mem _ (p j) hx)
    have hshift_back : ∀ j x,
        p37Shift A (p j) x ∈ p37KrylovSpan A (v t) n →
        x ∈ p37KrylovSpan A (v t) n := by
      intro j x hx
      let K := p37KrylovSpan A (v t) n
      let T := p37Shift A (p j)
      have hTK : ∀ y ∈ K, T y ∈ K := by
        intro y hy
        exact hshift j y hy
      let Tr : K →ₗ[ℝ] K := T.restrict hTK
      have hTrinj : Function.Injective Tr := by
        intro y z hyz
        apply Subtype.ext
        apply (hinv j).1
        exact congrArg Subtype.val hyz
      have hTrsurj : Function.Surjective Tr :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hTrinj
      obtain ⟨z, hz⟩ := hTrsurj ⟨T x, hx⟩
      have hz' : T (z : Fin n → ℝ) = T x := congrArg Subtype.val hz
      have hzx : (z : Fin n → ℝ) = x := (hinv j).1 hz'
      rw [← hzx]
      exact z.property
    have hbase : v t ∈ p37KrylovSpan A (v t) n := by
      exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
    have hvt : ∀ d : ℤ, v (t + d) ∈ p37KrylovSpan A (v t) n := by
      intro d
      induction d using Int.induction_on with
      | zero => simpa using hbase
      | succ i ih =>
          have hi := hshift (t + (i : ℤ)) (v (t + (i : ℤ))) ih
          rw [← hstep (t + (i : ℤ))] at hi
          convert hi using 1 <;> congr 1 <;> omega
      | pred i ih =>
          apply hshift_back (t + (-(i : ℤ) - 1))
          rw [← hstep (t + (-(i : ℤ) - 1))]
          convert ih using 1 <;> congr 1 <;> omega
    have hvK : ∀ j : ℤ, v j ∈ p37KrylovSpan A (v t) n := by
      intro j
      convert hvt (j - t) using 1 <;> congr 1 <;> omega
    have htwo_le : p37TwoSidedSpan v ≤ p37KrylovSpan A (v t) n := by
      rw [p37TwoSidedSpan, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hvK j
    have hcons_le : p37ConsecutiveSpan v t n ≤ p37TwoSidedSpan v := by
      rw [p37ConsecutiveSpan, p37TwoSidedSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨t + (i : ℕ), rfl⟩
    constructor
    · apply le_antisymm htwo_le
      rw [← hcons]
      exact hcons_le
    · exact hcons
  obtain ⟨hst, hsc⟩ := hall s
  obtain ⟨hzt, hzc⟩ := hall 0
  refine ⟨hst.trans hsc.symm, hsc, ?_⟩
  calc
    p37KrylovSpan A (v s) n = p37TwoSidedSpan v := hst.symm
    _ = p37KrylovSpan A (v 0) n := hzt
    _ = p37KrylovSpan A B n := by rw [hv0]

end HighamBench
