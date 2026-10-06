import NumStability.Algorithms.Arithmetic.DotProduct.NoGuard.Core
import NumStability.Algorithms.Summation.Tree.Core

/-!
# Tree-ordered no-guard dot products

Reusable no-guard evaluation and backward-error bounds for arbitrary binary
summation trees and input permutations.
-/

namespace NumStability

open scoped BigOperators

namespace SumTree

/-- Evaluate an arbitrary binary summation tree with the Chapter 2 no-guard
addition operation.  Leaves are exact inputs; every internal node is an actual
call to `fp.fl_add`. -/
noncomputable def noGuardEval (fp : NoGuardFPModel) :
    SumTree n → (Fin n → ℝ) → ℝ
  | .leaf, v => v ⟨0, by norm_num⟩
  | .node l r, v =>
      fp.fl_add
        (noGuardEval fp l (fun i => v (Fin.castAdd _ i)))
        (noGuardEval fp r (fun i => v (Fin.natAdd _ i)))

/-- Arbitrary-tree backward error for no-guard summation.  A leaf in the left
subtree receives the top node's `alpha` factor, while a leaf in the right
subtree receives its `beta` factor.  Thus each leaf accumulates one local
factor per node on its path, and the radius is `gamma(depth)`. -/
theorem noGuard_backward_error (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) :
    ∀ (_ : noGuardDotGammaValid fp t.depth) (v : Fin n → ℝ),
      ∃ eta : Fin n → ℝ,
        (∀ i, |eta i| ≤ noGuardDotGamma fp t.depth) ∧
        noGuardEval fp t v = ∑ i : Fin n, v i * (1 + eta i) := by
  induction t with
  | leaf =>
      intro hvalid v
      refine ⟨fun _ => 0, ?_, by simp [noGuardEval]⟩
      intro i
      simp only [abs_zero]
      exact gamma_nonneg (noGuardDotGammaProxy fp) hvalid
  | node l r ihl ihr =>
      rename_i m k
      intro hvalid v
      simp only [depth] at hvalid
      have hldepth : l.depth ≤ max l.depth r.depth + 1 :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      have hrdepth : r.depth ≤ max l.depth r.depth + 1 :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
      have hvalidL : noGuardDotGammaValid fp l.depth :=
        gammaValid_mono (noGuardDotGammaProxy fp) hldepth hvalid
      have hvalidR : noGuardDotGammaValid fp r.depth :=
        gammaValid_mono (noGuardDotGammaProxy fp) hrdepth hvalid
      have hvalid1 : noGuardDotGammaValid fp 1 :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.succ_le_succ (Nat.zero_le _)) hvalid
      have hvalidL1 : noGuardDotGammaValid fp (l.depth + 1) :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1) hvalid
      have hvalidR1 : noGuardDotGammaValid fp (r.depth + 1) :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1) hvalid
      obtain ⟨etaL, hetaL, hleft⟩ :=
        ihl hvalidL (fun i => v (Fin.castAdd k i))
      obtain ⟨etaR, hetaR, hright⟩ :=
        ihr hvalidR (fun i => v (Fin.natAdd m i))
      obtain ⟨alpha, beta, hadd⟩ :=
        fp.model_add
          (noGuardEval fp l (fun i => v (Fin.castAdd k i)))
          (noGuardEval fp r (fun i => v (Fin.natAdd m i)))
      have halpha1 : |alpha| ≤ noGuardDotGamma fp 1 := by
        exact le_trans hadd.1
          (u_le_gamma (noGuardDotGammaProxy fp) one_pos hvalid1)
      have hbeta1 : |beta| ≤ noGuardDotGamma fp 1 := by
        exact le_trans hadd.2.1
          (u_le_gamma (noGuardDotGammaProxy fp) one_pos hvalid1)
      refine ⟨
        Fin.addCases
          (fun i => etaL i + alpha + etaL i * alpha)
          (fun i => etaR i + beta + etaR i * beta), ?_, ?_⟩
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.addCases_left]
          obtain ⟨e, he, heq⟩ :=
            gamma_mul (noGuardDotGammaProxy fp) l.depth 1
              (etaL j) alpha (hetaL j) halpha1 hvalidL1
          have heq' : e = etaL j + alpha + etaL j * alpha := by
            have hring :
                (1 + etaL j) * (1 + alpha) =
                  1 + (etaL j + alpha + etaL j * alpha) := by ring
            linarith [heq, hring]
          rw [← heq']
          exact le_trans he
            (gamma_mono (noGuardDotGammaProxy fp)
              (Nat.add_le_add_right (Nat.le_max_left _ _) 1) hvalid)
        · intro j
          simp only [Fin.addCases_right]
          obtain ⟨e, he, heq⟩ :=
            gamma_mul (noGuardDotGammaProxy fp) r.depth 1
              (etaR j) beta (hetaR j) hbeta1 hvalidR1
          have heq' : e = etaR j + beta + etaR j * beta := by
            have hring :
                (1 + etaR j) * (1 + beta) =
                  1 + (etaR j + beta + etaR j * beta) := by ring
            linarith [heq, hring]
          rw [← heq']
          exact le_trans he
            (gamma_mono (noGuardDotGammaProxy fp)
              (Nat.add_le_add_right (Nat.le_max_right _ _) 1) hvalid)
      · show
          fp.fl_add
              (noGuardEval fp l (fun i => v (Fin.castAdd k i)))
              (noGuardEval fp r (fun i => v (Fin.natAdd m i))) =
            ∑ i : Fin (m + k),
              v i *
                (1 + Fin.addCases
                  (fun i => etaL i + alpha + etaL i * alpha)
                  (fun i => etaR i + beta + etaR i * beta) i)
        rw [noGuardAddWitness_value hadd, hleft, hright]
        conv_rhs => rw [Fin.sum_univ_add]
        rw [Finset.sum_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          simp only [Fin.addCases_left]
          ring
        · apply Finset.sum_congr rfl
          intro i _
          simp only [Fin.addCases_right]
          ring

end SumTree

/-- An actual no-guard dot-product evaluation with arbitrary binary tree shape
and arbitrary leaf permutation.  Together, `t` and `perm` represent every
pairwise evaluation order of a nonempty dot product. -/
noncomputable def fl_noGuardDotProductTree (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ) : ℝ :=
  t.noGuardEval fp (fun i => fp.fl_mul (x (perm i)) (y (perm i)))

/-- Tree-depth form of the no-guard dot-product backward error.  The extra one
in `depth + 1` is the rounded multiplication at each leaf. -/
theorem noGuardDotTree_factor_backward_error (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp (t.depth + 1)) :
    ∃ eta : Fin n → ℝ,
      (∀ i, |eta i| ≤ noGuardDotGamma fp (t.depth + 1)) ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, x i * y i * (1 + eta i) := by
  let z : Fin n → ℝ :=
    fun i => fp.fl_mul (x (perm i)) (y (perm i))
  have hdepthValid : noGuardDotGammaValid fp t.depth :=
    gammaValid_mono (noGuardDotGammaProxy fp) (Nat.le_succ t.depth) hvalid
  have hOneValid : noGuardDotGammaValid fp 1 :=
    gammaValid_mono (noGuardDotGammaProxy fp)
      (Nat.succ_le_succ (Nat.zero_le t.depth)) hvalid
  obtain ⟨sumEta, hsumEta, hsum⟩ :=
    SumTree.noGuard_backward_error fp t hdepthValid z
  have hmul : ∀ i : Fin n, ∃ d : ℝ,
      |d| ≤ fp.u ∧
      z i = x (perm i) * y (perm i) * (1 + d) := by
    intro i
    obtain ⟨d, hd, heq⟩ :=
      fp.model_mul_signedRelErrorWitness (x (perm i)) (y (perm i))
    exact ⟨d, hd, heq⟩
  let mulDelta : Fin n → ℝ := fun i => Classical.choose (hmul i)
  have hmulBound : ∀ i, |mulDelta i| ≤ fp.u :=
    fun i => (Classical.choose_spec (hmul i)).1
  have hmulEq : ∀ i,
      z i = x (perm i) * y (perm i) * (1 + mulDelta i) :=
    fun i => (Classical.choose_spec (hmul i)).2
  have hvalidComm :
      noGuardDotGammaValid fp (1 + t.depth) := by
    simpa [Nat.add_comm] using hvalid
  let leafEta : Fin n → ℝ :=
    fun i => mulDelta i + sumEta i + mulDelta i * sumEta i
  have hleafEta : ∀ i,
      |leafEta i| ≤ noGuardDotGamma fp (t.depth + 1) := by
    intro i
    have hmulGamma : |mulDelta i| ≤ noGuardDotGamma fp 1 :=
      le_trans (hmulBound i)
        (u_le_gamma (noGuardDotGammaProxy fp) one_pos hOneValid)
    obtain ⟨e, he, heq⟩ :=
      gamma_mul (noGuardDotGammaProxy fp) 1 t.depth
        (mulDelta i) (sumEta i) hmulGamma (hsumEta i) hvalidComm
    have heq' : e = leafEta i := by
      have hring :
          (1 + mulDelta i) * (1 + sumEta i) = 1 + leafEta i := by
        simp only [leafEta]
        ring
      linarith [heq, hring]
    rw [heq'] at he
    simpa [Nat.add_comm] using he
  have hleafSum :
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n,
          x (perm i) * y (perm i) * (1 + leafEta i) := by
    change SumTree.noGuardEval fp t z = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hmulEq i]
    simp only [leafEta]
    ring
  let eta : Fin n → ℝ := fun i => leafEta (perm.symm i)
  refine ⟨eta, ?_, ?_⟩
  · intro i
    simpa [eta] using hleafEta (perm.symm i)
  · rw [hleafSum]
    exact Fintype.sum_equiv perm
      (fun i : Fin n => x (perm i) * y (perm i) * (1 + leafEta i))
      (fun i : Fin n => x i * y i * (1 + eta i))
      (fun i => by simp [eta])

end NumStability
