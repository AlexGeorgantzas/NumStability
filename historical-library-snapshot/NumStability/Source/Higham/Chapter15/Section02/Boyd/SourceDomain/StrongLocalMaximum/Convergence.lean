import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydCompletion
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.SecondDerivative.Rowwise

/-!
# Convergence

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.HighamChapter15BoydSourceClosure`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# HighamChapter15BoydSourceClosure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydSourceClosure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The audit-facing strong-maximum predicate supplies an actual second
derivative with a uniform negative tangent gap.  The derivative facts are
derived from the exact source domain rather than stored as assumptions. -/
theorem IsBoydConcreteSourceStrongLocalMaximum.hasActualSecondDerivativeGap
    {m n : Nat} {p : Real} (hp : 1 < p)
    {A : Fin m -> Fin n -> Real} {x : Fin n -> Real}
    (hstrong : IsBoydConcreteSourceStrongLocalMaximum p A x) :
    exists eta : Real, 0 < eta /\ forall h : Fin n -> Real,
      HasDerivAt (boydConstrainedLagrangianLine p A x h)
          (boydConstrainedLagrangianFirst p A x h 0) 0 /\
        HasDerivAt (boydConstrainedLagrangianFirst p A x h)
          (boydConstrainedSecondVariation p A x h) 0 /\
        (boydWeightedPair p x x h = 0 ->
          boydConstrainedSecondVariation p A x h <=
            -eta * boydWeightedPair p x h h) := by
  rcases hstrong with ⟨⟨_hstat, eta, heta, hgap⟩, hxcoord, hsmooth⟩
  refine ⟨eta, heta, ?_⟩
  intro h
  obtain ⟨hfirst, hsecond⟩ :=
    boydConstrainedSecondVariation_is_second_derivative_rowwise_source_domain
      hp A x h hxcoord hsmooth
  exact ⟨hfirst, hsecond, hgap h⟩

/-- Uniform local-linear theorem for the literal rectangular Boyd update on
the corrected source domain.  Fixedness, the actual Frechet derivative, and
power stability are all conclusions, not premises. -/
theorem rect_general_boyd_concrete_source_local_linear_uniform
    {m n : Nat} (_hm : 0 < m) (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hstrong : IsBoydConcreteSourceStrongLocalMaximum p A x) :
    exists N : Nat, 0 < N /\ exists c K : NNReal,
      0 < c /\ c < K /\ K < 1 /\ exists delta : Real, 0 < delta /\
        forall x0 : Fin n -> Real,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              (x0 - x) <= delta ->
            (forall k : Nat,
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  ((RectPNormPair.general hn hpq A).xseq x0 k - x) <=
                (K : Real) ^ k *
                  powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                    (x0 - x)) /\
            Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
              atTop (nhds x) := by
  obtain ⟨eta, heta, hactualGap⟩ :=
    hstrong.hasActualSecondDerivativeGap hpq.lt
  rcases hstrong with ⟨hstrong, hxcoord, hsmooth⟩
  rcases hstrong with ⟨hstat, _hnondeg⟩
  have hnondeg : IsBoydConcreteNondegenerate p A x :=
    ⟨eta, heta, fun h htangent => (hactualGap h).2.2 htangent⟩
  have hstat' := hstat
  obtain ⟨hunit, hS, hstationary⟩ := hstat
  have hfixed := rect_general_xnext_eq_of_stationarity_source_domain
    hn hpq A x hxcoord hunit hS hstationary
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hS
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hS
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hS hstationary
  have hderiv := rect_general_xnext_hasFDerivAt_boyd_rowwise_source_domain
    hn hpq A x hy hzcoord hsmooth
  have hL : boydSmoothRectDerivative (p := p) (q := q) A x =
      boydConcreteFullDerivative p A x := by
    ext h j
    have hactual :=
      rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_rowwise_source_domain
        hn hpq A x h hxcoord hsmooth hunit hS hstationary
    rw [hderiv.fderiv] at hactual
    rw [hactual]
    rw [boydConcreteFullDerivative_eq_normalized_projected
      p A x h hxcoord hstat']
  rw [hL] at hderiv
  obtain ⟨N, hN, c, hc0, hc1, hpow⟩ :=
    boydConcreteFullDerivative_power_stable
      hpq.lt A x hxcoord hunit hS hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  obtain ⟨delta, hdelta, hlocal⟩ :=
    exists_local_powerAdaptedSeminormContraction
      hN hc0 hcK hK1 hpow hfixed hderiv
  refine ⟨N, hN, c, K, hc0, hcK, hK1, delta, hdelta, ?_⟩
  intro x0 hx0
  have hgeom :=
    iterate_seminorm_le_geometric_of_localSeminormContraction hlocal hx0
  have hconv := tendsto_iterate_of_localSeminormContraction
    (fun y => norm_le_powerAdaptedSeminorm
      (boydConcreteFullDerivative p A x) c hN y) hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate]
    exact (hgeom k).1
  · rw [show (RectPNormPair.general hn hpq A).xseq x0 =
        (fun k : Nat =>
          (RectPNormPair.general hn hpq A).xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate _ _ _]
    exact hconv

/-- Fixed-start specialization of the corrected uniform theorem. -/
theorem rect_general_boyd_concrete_source_local_linear
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x0 x : Fin n -> Real)
    (hstrong : IsBoydConcreteSourceStrongLocalMaximum p A x) :
    exists N : Nat, 0 < N /\ exists c K : NNReal,
      0 < c /\ c < K /\ K < 1 /\ exists delta : Real, 0 < delta /\
        (powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
            (x0 - x) <= delta ->
          (forall k : Nat,
            powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 k - x) <=
              (K : Real) ^ k *
                powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  (x0 - x)) /\
          Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
            atTop (nhds x)) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, delta, hdelta, hlocal⟩ :=
    rect_general_boyd_concrete_source_local_linear_uniform
      hm hn hpq A x hstrong
  exact ⟨N, hN, c, K, hc0, hcK, hK1, delta, hdelta, hlocal x0⟩

/-- PDF-facing subsequential-limit theorem.  A convergent subsequence supplies
an entry point in the one uniform adapted neighborhood; the resulting finite
tail has a geometric rate and convergence transports to the whole trace. -/
theorem higham15_boyd_source_linear_of_strongLocalMaximum_subsequentialLimit
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x0 x : Fin n -> Real)
    (hstrong : IsBoydConcreteSourceStrongLocalMaximum p A x)
    (phi : Nat -> Nat) (_hphi : StrictMono phi)
    (hcluster : Tendsto
      (fun s => (RectPNormPair.general hn hpq A).xseq x0 (phi s))
      atTop (nhds x)) :
    exists r N : Nat, 0 < N /\ exists c K : NNReal,
      0 < c /\ c < K /\ K < 1 /\
        (forall k : Nat,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              ((RectPNormPair.general hn hpq A).xseq x0 (phi r + k) - x) <=
            (K : Real) ^ k *
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 (phi r) - x)) /\
        Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
          atTop (nhds x) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, delta, hdelta, hlocal⟩ :=
    rect_general_boyd_concrete_source_local_linear_uniform
      hm hn hpq A x hstrong
  obtain ⟨r, hr⟩ := exists_subsequence_in_powerAdapted_ball
    (RectPNormPair.general hn hpq A) x0 x
    (boydConcreteFullDerivative p A x) c N phi hdelta hcluster
  obtain ⟨hgeomTail, hconvTail⟩ :=
    hlocal ((RectPNormPair.general hn hpq A).xseq x0 (phi r)) hr
  refine ⟨r, N, hN, c, K, hc0, hcK, hK1, ?_, ?_⟩
  · intro k
    simpa only [rectPNormPair_xseq_shift_add] using hgeomTail k
  · exact tendsto_rectPNormPair_xseq_of_tail
      (RectPNormPair.general hn hpq A) x0 x (phi r) hconvTail

end Ch15
end NumStability
