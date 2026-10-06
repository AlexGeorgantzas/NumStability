import HighamBench.P29Definitions
import NumStability.Algorithms.LinearSystems.Triangular.Combined

set_option maxHeartbeats 2000000

namespace HighamBench

open scoped BigOperators

noncomputable def p29AsFPModel (fp : P29FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p29ForwardSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p29AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      unfold p29ForwardSubSteps NumStability.fl_forwardSub_steps
      simp only
      apply ih

private lemma p29ForwardSub_eq (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    p29ForwardSub fp n L b =
      NumStability.fl_forwardSub (p29AsFPModel fp) n L b := by
  unfold p29ForwardSub NumStability.fl_forwardSub
  apply p29ForwardSubSteps_eq

private lemma p29BackSubSteps_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p29BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p29AsFPModel fp) n U b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      unfold p29BackSubSteps NumStability.fl_backSub_steps
      simp only
      apply ih

private lemma p29BackSub_eq (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    p29BackSub fp n U b =
      NumStability.fl_backSub (p29AsFPModel fp) n U b := by
  unfold p29BackSub NumStability.fl_backSub
  apply p29BackSubSteps_eq

private lemma p29EntryNorm_nonneg {m n : ℕ} (M : P29Matrix m n) :
    0 ≤ p29EntryNorm M := by
  unfold p29EntryNorm
  positivity

private lemma p29Entry_abs_le {m n : ℕ} (M : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |M i j| ≤ p29EntryNorm M := by
  unfold p29EntryNorm
  calc
    |M i j| ≤ ∑ j' : Fin n, |M i j'| := by
      exact Finset.single_le_sum
        (f := fun j' : Fin n => |M i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |M i' j'| := by
      exact Finset.single_le_sum
        (f := fun i' : Fin m => ∑ j' : Fin n, |M i' j'|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (Finset.mem_univ i)

private lemma p29EntryNorm_add_le {m n : ℕ} (M N : P29Matrix m n) :
    p29EntryNorm (M + N) ≤ p29EntryNorm M + p29EntryNorm N := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |(M + N) i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, (|M i j| + |N i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa using abs_add_le (M i j) (N i j)
    _ = (∑ i : Fin m, ∑ j : Fin n, |M i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |N i j| := by
      simp only [Finset.sum_add_distrib]

private lemma p29EntryNorm_matMul_le {m n p : ℕ}
    (M : P29Matrix m n) (N : P29Matrix n p) :
    p29EntryNorm (p29MatMul M N) ≤
      (m : ℝ) * (n : ℝ) * (p : ℝ) *
        p29EntryNorm M * p29EntryNorm N := by
  have hM : ∀ i j, |M i j| ≤ p29EntryNorm M := p29Entry_abs_le M
  have hN : ∀ i j, |N i j| ≤ p29EntryNorm N := p29Entry_abs_le N
  have hM0 := p29EntryNorm_nonneg M
  have hN0 := p29EntryNorm_nonneg N
  unfold p29EntryNorm p29MatMul
  calc
    ∑ i : Fin m, ∑ j : Fin p, |∑ k : Fin n, M i k * N k j| ≤
        ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |M i k * N k j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin p, ∑ _k : Fin n,
          p29EntryNorm M * p29EntryNorm N := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) hM0
    _ = (m : ℝ) * (n : ℝ) * (p : ℝ) *
          p29EntryNorm M * p29EntryNorm N := by
      simp
      ring

private lemma p29MatMul_add_left {m n p : ℕ}
    (M N : P29Matrix m n) (R : P29Matrix n p) :
    p29MatMul (M + N) R = p29MatMul M R + p29MatMul N R := by
  funext i j
  simp [p29MatMul, add_mul, Finset.sum_add_distrib]

private lemma p29MatMul_add_right {m n p : ℕ}
    (M : P29Matrix m n) (N R : P29Matrix n p) :
    p29MatMul M (N + R) = p29MatMul M N + p29MatMul M R := by
  funext i j
  simp [p29MatMul, mul_add, Finset.sum_add_distrib]

private lemma p29TripleMatMul_apply {n : ℕ}
    (M N R : P29Matrix n n) (i j : Fin n) :
    p29MatMul (p29MatMul M N) R i j =
      ∑ p : Fin n, ∑ q : Fin n, M i p * N p q * R q j := by
  simp only [p29MatMul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma p29CombinedBackwardError_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  simp only [p29CombinedBackwardError, p29PerturbedLDLT, p29LDLT,
    p29MatMul_add_left, p29MatMul_add_right]
  abel

private lemma p29EntryNorm_tripleMatMul_le {n : ℕ}
    (M N R : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul M N) R) ≤
      (n : ℝ) ^ 6 * p29EntryNorm M * p29EntryNorm N * p29EntryNorm R := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hMN0 := p29EntryNorm_nonneg (p29MatMul M N)
  have hM0 := p29EntryNorm_nonneg M
  have hN0 := p29EntryNorm_nonneg N
  have hR0 := p29EntryNorm_nonneg R
  calc
    p29EntryNorm (p29MatMul (p29MatMul M N) R) ≤
        (n : ℝ) * (n : ℝ) * (n : ℝ) *
          p29EntryNorm (p29MatMul M N) * p29EntryNorm R :=
      p29EntryNorm_matMul_le (p29MatMul M N) R
    _ ≤ (n : ℝ) * (n : ℝ) * (n : ℝ) *
          ((n : ℝ) * (n : ℝ) * (n : ℝ) *
            p29EntryNorm M * p29EntryNorm N) * p29EntryNorm R := by
      gcongr
      exact p29EntryNorm_matMul_le M N
    _ = (n : ℝ) ^ 6 * p29EntryNorm M * p29EntryNorm N *
          p29EntryNorm R := by ring

private lemma p29EntryNorm_le_mul_of_entry_le {m n : ℕ}
    (c : ℝ) (M N : P29Matrix m n) (h : ∀ i j, |M i j| ≤ c * |N i j|) :
    p29EntryNorm M ≤ c * p29EntryNorm N := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |M i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |N i j| := by
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => h i j))
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |N i j| := by
      simp only [Finset.mul_sum]

/-- P29-T2: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p29_t2_ldlt_solve_backward_stability
    (fp : P29FPModel) (n : ℕ) (A L D E0 : P29Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p29LDLT L D = A + E0)
    (hE0 : p29EntryNorm E0 ≤ factorEta * p29EntryNorm A)
    (hDsolve : P29BlockSolveStable n D
      (p29ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P29Matrix n n),
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      p29EntryNorm ΔD ≤ eta * p29EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p29Gamma fp.u n * |p29Transpose L i j|) ∧
      F = p29TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j = b i) ∧
      p29EntryNorm F ≤
        p29TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P29-T2-H001
  have hvalid' : NumStability.gammaValid (p29AsFPModel fp) n := by
    simpa [NumStability.gammaValid, P29GammaValid, p29AsFPModel] using hvalid
  obtain ⟨ΔL, hΔLlib, hforwardLib⟩ :=
    NumStability.forwardSub_backward_error (p29AsFPModel fp) n L b
      hdiag hlower hvalid'
  have hΔL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j| := by
    simpa [NumStability.gamma, p29Gamma, p29AsFPModel] using hΔLlib
  have hforward : ∀ i, ∑ j : Fin n,
      (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
    simpa only [p29ForwardSub_eq] using hforwardLib
  rcases hDsolve with ⟨ΔD, hΔD, hmiddle⟩
  have hUdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    simpa [p29Transpose] using hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔUraw, hΔUlib, hbackLib⟩ :=
    NumStability.backSub_backward_error (p29AsFPModel fp) n
      (p29Transpose L) z hUdiag hUupper hvalid'
  let ΔU : P29Matrix n n := fun i j => ΔUraw i j
  have hΔU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j| := by
    simpa [ΔU, NumStability.gamma, p29Gamma, p29AsFPModel] using hΔUlib
  have hback : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + ΔU i j) *
        p29BackSub fp n (p29Transpose L) z j = z i := by
    simpa only [ΔU, p29BackSub_eq] using hbackLib
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · intro i
    have hperturbed :
        ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j *
            p29BackSub fp n (p29Transpose L) z j = b i := by
      calc
        ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j *
              p29BackSub fp n (p29Transpose L) z j =
            ∑ p : Fin n, (L i p + ΔL i p) *
              (∑ q : Fin n, (D p q + ΔD p q) *
                (∑ j : Fin n, (p29Transpose L q j + ΔU q j) *
                  p29BackSub fp n (p29Transpose L) z j)) := by
            simp only [p29PerturbedLDLT, p29TripleMatMul_apply,
              Matrix.add_apply]
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q hq
            ring_nf
        _ = ∑ p : Fin n, (L i p + ΔL i p) *
              (∑ q : Fin n, (D p q + ΔD p q) * z q) := by
            apply Finset.sum_congr rfl
            intro p hp
            congr 1
            apply Finset.sum_congr rfl
            intro q hq
            rw [hback q]
        _ = ∑ p : Fin n, (L i p + ΔL i p) *
              p29ForwardSub fp n L b p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [hmiddle p]
        _ = b i := hforward i
    calc
      ∑ j : Fin n, (A i j + F i j) *
            p29BackSub fp n (p29Transpose L) z j =
          ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j *
            p29BackSub fp n (p29Transpose L) z j := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have hf := congr_fun (congr_fun hfactor i) j
        simp only [F, p29TotalBackwardError, p29CombinedBackwardError,
          Matrix.add_apply, Matrix.sub_apply] at *
        rw [hf]
        ring
      _ = b i := hperturbed
  · dsimp [F]
    let γ : ℝ := p29Gamma fp.u n
    have hγ : 0 ≤ γ := by
      dsimp [γ, p29Gamma]
      apply div_nonneg
      · exact mul_nonneg (by positivity) fp.u_nonneg
      · exact le_of_lt (sub_pos.mpr hvalid)
    have hΔLnorm : p29EntryNorm ΔL ≤ γ * p29EntryNorm L := by
      exact p29EntryNorm_le_mul_of_entry_le γ ΔL L (by
        intro i j
        simpa [γ] using hΔL i j)
    have hΔUnorm : p29EntryNorm ΔU ≤
        γ * p29EntryNorm (p29Transpose L) := by
      exact p29EntryNorm_le_mul_of_entry_le γ ΔU (p29Transpose L) (by
        intro i j
        simpa [γ] using hΔU i j)
    have hDsum : p29EntryNorm (D + ΔD) ≤
        (1 + eta) * p29EntryNorm D := by
      calc
        p29EntryNorm (D + ΔD) ≤
            p29EntryNorm D + p29EntryNorm ΔD := p29EntryNorm_add_le D ΔD
        _ ≤ p29EntryNorm D + eta * p29EntryNorm D :=
          add_le_add_right hΔD _
        _ = (1 + eta) * p29EntryNorm D := by ring
    have hUsum : p29EntryNorm
        ((p29Transpose L : P29Matrix n n) + (ΔU : P29Matrix n n)) ≤
        (1 + γ) * p29EntryNorm (p29Transpose L) := by
      calc
        p29EntryNorm
            ((p29Transpose L : P29Matrix n n) + (ΔU : P29Matrix n n)) ≤
            p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
          p29EntryNorm_add_le (p29Transpose L) ΔU
        _ ≤ p29EntryNorm (p29Transpose L) +
            γ * p29EntryNorm (p29Transpose L) :=
          add_le_add_right hΔUnorm _
        _ = (1 + γ) * p29EntryNorm (p29Transpose L) := by ring
    have hn6 : 0 ≤ (n : ℝ) ^ 6 := by positivity
    have hL0 := p29EntryNorm_nonneg L
    have hD0 := p29EntryNorm_nonneg D
    have hU0 := p29EntryNorm_nonneg (p29Transpose L)
    have hΔL0 := p29EntryNorm_nonneg ΔL
    have hΔD0 := p29EntryNorm_nonneg ΔD
    have hΔU0 := p29EntryNorm_nonneg ΔU
    have hDsum0 := p29EntryNorm_nonneg (D + ΔD)
    have hUsum0 := p29EntryNorm_nonneg (p29Transpose L + ΔU)
    let T1 : P29Matrix n n :=
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)
    let T2 : P29Matrix n n :=
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)
    let T3 : P29Matrix n n := p29MatMul (p29MatMul L D) ΔU
    let K : ℝ := (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
      p29EntryNorm (p29Transpose L)
    let c1 : ℝ := γ * (1 + eta) * (1 + γ)
    let c2 : ℝ := eta * (1 + γ)
    have hterm1 : p29EntryNorm T1 ≤ K * c1 := by
      calc
        p29EntryNorm T1 ≤
            (n : ℝ) ^ 6 * p29EntryNorm ΔL *
              p29EntryNorm (D + ΔD) *
              p29EntryNorm (p29Transpose L + ΔU) := by
          dsimp only [T1]
          exact p29EntryNorm_tripleMatMul_le ΔL (D + ΔD)
            (p29Transpose L + ΔU)
        _ ≤ (n : ℝ) ^ 6 * (γ * p29EntryNorm L) *
              ((1 + eta) * p29EntryNorm D) *
              ((1 + γ) * p29EntryNorm (p29Transpose L)) := by
          gcongr
        _ = K * c1 := by
          dsimp only [K, c1]
          ring
    have hterm2 : p29EntryNorm T2 ≤ K * c2 := by
      calc
        p29EntryNorm T2 ≤
            (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm ΔD *
              p29EntryNorm (p29Transpose L + ΔU) := by
          dsimp only [T2]
          exact p29EntryNorm_tripleMatMul_le L ΔD (p29Transpose L + ΔU)
        _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
              (eta * p29EntryNorm D) *
              ((1 + γ) * p29EntryNorm (p29Transpose L)) := by
          gcongr
        _ = K * c2 := by
          dsimp only [K, c2]
          ring
    have hterm3 : p29EntryNorm T3 ≤ K * γ := by
      calc
        p29EntryNorm T3 ≤
            (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
              p29EntryNorm ΔU := by
          dsimp only [T3]
          exact p29EntryNorm_tripleMatMul_le L D ΔU
        _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
              (γ * p29EntryNorm (p29Transpose L)) := by
          gcongr
        _ = K * γ := by
          dsimp only [K]
          ring
    have hcombined : p29EntryNorm
        (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p29SolveBackwardFactor fp n eta L D := by
      calc
        p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) =
            p29EntryNorm (T1 + T2 + T3) := by
          congr 1
          simpa only [T1, T2, T3] using
            p29CombinedBackwardError_expand L D ΔL ΔD ΔU
        _ ≤ p29EntryNorm (T1 + T2) + p29EntryNorm T3 :=
          p29EntryNorm_add_le (T1 + T2) T3
        _ ≤ (p29EntryNorm T1 + p29EntryNorm T2) + p29EntryNorm T3 :=
          add_le_add_left (p29EntryNorm_add_le T1 T2) _
        _ ≤ (K * c1 + K * c2) + K * γ := by
          exact add_le_add (add_le_add hterm1 hterm2) hterm3
        _ = p29SolveBackwardFactor fp n eta L D := by
          dsimp only [K, c1, c2, γ, p29SolveBackwardFactor]
          ring
    calc
      p29EntryNorm (p29TotalBackwardError E0 L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 +
            p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        exact p29EntryNorm_add_le E0
          (p29CombinedBackwardError L D ΔL ΔD ΔU)
      _ ≤ factorEta * p29EntryNorm A +
          p29SolveBackwardFactor fp n eta L D := add_le_add hE0 hcombined
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
