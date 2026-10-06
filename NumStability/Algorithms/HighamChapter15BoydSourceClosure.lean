-- Algorithms/HighamChapter15BoydSourceClosure.lean
--
-- Final PDF-facing closure of Boyd's local and global Chapter 15 results.
-- The local theorem keeps the nondegenerate-curvature correction explicit and
-- uses the precise composition domain: below p = 2, a zero coordinate of A*x
-- is admitted when it comes from an identically zero row.

import NumStability.Algorithms.HighamChapter15BoydSourceSecondDerivative
import NumStability.Algorithms.HighamChapter15BoydScalar

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

/-- Audit-facing correction of Higham's phrase "strong local maximum with no
zero components".  It records all and only the data used by the corrected
Boyd proof: stationary normalized data, a uniform negative constrained-Hessian
gap, nonzero coordinates of the limiting vector, and the exact inner
composition smoothness domain. -/
def IsBoydConcreteSourceStrongLocalMaximum {m n : Nat} (p : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Prop :=
  IsBoydConcreteStrongLocalMaximum p A x /\
    (forall j : Fin n, x j ≠ 0) /\
    IsBoydInnerRowwiseSmoothDomain p A x

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

/-- A concrete `p < 2` source-domain witness with a genuine zero coordinate
of `A*x`: the second row is identically zero and is therefore harmless. -/
theorem boyd_inner_rowwise_domain_zero_row_example :
    IsBoydInnerRowwiseSmoothDomain ((3 : Real) / 2)
      (fun i : Fin 2 => fun _j : Fin 1 => if i = 0 then 1 else 0)
      (fun _j : Fin 1 => 1) := by
  right
  intro i
  fin_cases i
  · left
    simp [boydRectActionCLM_apply]
  · right
    intro j
    simp

/-- The complete corrected strong-local-maximum predicate is nonvacuous on
the genuinely enlarged `p < 2` source domain: the second row is identically
zero, while the one-dimensional active problem has a normalized stationary
point and a vacuous tangent space. -/
theorem boyd_concrete_source_strongLocalMaximum_zero_row_example :
    IsBoydConcreteSourceStrongLocalMaximum ((3 : Real) / 2)
      (fun i : Fin 2 => fun _j : Fin 1 => if i = 0 then 1 else 0)
      (fun _j : Fin 1 => 1) := by
  let A : Fin 2 -> Fin 1 -> Real :=
    fun i _j => if i = 0 then 1 else 0
  let x : Fin 1 -> Real := fun _j => 1
  have hsmooth : IsBoydInnerRowwiseSmoothDomain ((3 : Real) / 2) A x := by
    simpa [A, x] using boyd_inner_rowwise_domain_zero_row_example
  have hunit : realLpPowerSum ((3 : Real) / 2) x = 1 := by
    simp [realLpPowerSum, x]
  have hS : 0 < realLpPowerSum ((3 : Real) / 2)
      (boydRectActionCLM A x) := by
    norm_num [realLpPowerSum, boydRectActionCLM_apply, A, x]
  have hstationary : forall j : Fin 1,
      (∑ i : Fin 2, A i j *
        (|boydRectActionCLM A x i| ^ (((3 : Real) / 2) - 2) *
          boydRectActionCLM A x i)) =
        realLpPowerSum ((3 : Real) / 2) (boydRectActionCLM A x) *
          (|x j| ^ (((3 : Real) / 2) - 2) * x j) := by
    intro j
    fin_cases j
    norm_num [realLpPowerSum, boydRectActionCLM_apply, A, x]
  have hnondeg : IsBoydConcreteNondegenerate ((3 : Real) / 2) A x := by
    refine ⟨1, by norm_num, ?_⟩
    intro h htangent
    have hzero : h (0 : Fin 1) = 0 := by
      simpa [boydWeightedPair, x] using htangent
    have hh : h = 0 := by
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact hzero
    simp [hh, boydConstrainedSecondVariation, boydWeightedPair]
  change IsBoydConcreteSourceStrongLocalMaximum ((3 : Real) / 2) A x
  exact ⟨⟨⟨hunit, hS, hstationary⟩, hnondeg⟩,
    (by intro j; simp [x]), hsmooth⟩

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

end NumStability.Ch15
