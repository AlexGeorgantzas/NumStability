import HighamBench.P11Definitions

namespace HighamBench

theorem p11_t3_orthogonality_defect_bound {m n : ℕ}
    (family : P11CGSPTheorem1Family m n)
    (analysis : P11Theorem1ResidualAsymptotics family) :
    ∀ epsilonM : P11PositiveEpsilon,
      epsilonM.1 ≤ p11Theorem1OrthogonalityRadius family analysis →
      ∀ k : Fin n,
      p11OpNorm2
          (p11RectOrthogonalityDefect
            (p11ColumnPrefix (family.run epsilonM).Q k)) ≤
        p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock (family.run epsilonM).R k)
                  ((family.run epsilonM).leadingInverse k) ^ 2 *
            epsilonM.1 +
          p11Theorem1OrthogonalityRemainderCoeff family analysis k *
            epsilonM.1 ^ 2 := by
  -- PROOF_START P11-T3-H001
  sorry

end HighamBench
