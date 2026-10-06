import HighamBench.P64Definitions

namespace HighamBench

open scoped BigOperators

/-- The G-stage block residual at a node whose child systems are GE leaves. -/
theorem p64_t2_G_stage_leaf_residual
    (fp : P64FPModel) (n : ℕ)
    (Ase Anw Ane Ls Us Ln Un : P64Matrix n n)
    (uvec : Fin n → ℝ)
    (hLs : P64LUCertificate fp n Ase Ls Us)
    (hLn : P64LUCertificate fp n Anw Ln Un)
    (hUsdiag : ∀ i : Fin n, Us i i ≠ 0)
    (hUndiag : ∀ i : Fin n, Un i i ≠ 0)
    (hvalid : P64GammaValid fp.u n) :
    let gs := p64LUSolve fp n Ls Us uvec
    let w := p64RoundedMatVec fp n Ane gs
    let gn := p64LUSolve fp n Ln Un w
    ∃ Ds Dn : P64Matrix n n, ∃ dw : Fin n → ℝ,
      (∀ i j, |Ds i j| ≤
        (3 * p64Gamma fp.u n + p64Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ls i k| * |Us k j|) ∧
      (∀ i j, |Dn i j| ≤
        (3 * p64Gamma fp.u n + p64Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ln i k| * |Un k j|) ∧
      (∀ i, |dw i| ≤ p64Gamma fp.u n *
        ∑ j : Fin n, |Ane i j| * |gs j|) ∧
      (∀ i,
        (∑ j : Fin n, Ase i j * gs j) - uvec i =
          -(∑ j : Fin n, Ds i j * gs j) ∧
        (∑ j : Fin n, Anw i j * gn j) -
          (∑ j : Fin n, Ane i j * gs j) =
            dw i - (∑ j : Fin n, Dn i j * gn j)) := by
  -- PROOF_START P64-T2-H001
  sorry

end HighamBench
