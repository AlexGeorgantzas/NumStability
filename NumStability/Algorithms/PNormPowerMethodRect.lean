-- Algorithms/PNormPowerMethodRect.lean
--
-- Literal rectangular source form of Higham Algorithm 15.1 and Lemma 15.2.
-- The older `PNormPair` interface is intentionally preserved; this module adds
-- the missing `A : R^{m x n}` form without changing its clients.

import NumStability.Algorithms.PNormPowerMethodGeneralP

namespace NumStability

open scoped BigOperators
open Ch15

/-- Dual-norm data for the literal rectangular p-norm power method.

`pIn`/`qIn` live on the domain `R^n`; `pOut`/`qOut` live on the
codomain `R^m`.  The fields are exactly the dual-attainment, Holder, and
operator-norm facts used in Higham's proof of Lemma 15.2.  In particular, no
field is any inequality from Lemma 15.2 itself. -/
structure RectPNormPair (m n : ℕ) where
  A : Fin m → Fin n → ℝ
  pIn : (Fin n → ℝ) → ℝ
  qIn : (Fin n → ℝ) → ℝ
  pOut : (Fin m → ℝ) → ℝ
  qOut : (Fin m → ℝ) → ℝ
  opP : ℝ
  dpOut : (Fin m → ℝ) → (Fin m → ℝ)
  dqIn : (Fin n → ℝ) → (Fin n → ℝ)
  pIn_nonneg : ∀ v, 0 ≤ pIn v
  pOut_nonneg : ∀ v, 0 ≤ pOut v
  dpOut_attains : ∀ v, (∑ i : Fin m, dpOut v i * v i) = pOut v
  dpOut_qunit : ∀ v, qOut (dpOut v) ≤ 1
  dqIn_attains : ∀ w, (∑ j : Fin n, dqIn w j * w j) = qIn w
  dqIn_punit : ∀ w, pIn (dqIn w) = 1
  holderIn : ∀ u v, (∑ j : Fin n, u j * v j) ≤ qIn u * pIn v
  holderOut : ∀ u v, (∑ i : Fin m, u i * v i) ≤ qOut u * pOut v
  op_bound : ∀ v, pOut (fun i => ∑ j : Fin n, A i j * v j) ≤ opP * pIn v

namespace RectPNormPair

variable {m n : ℕ} (P : RectPNormPair m n)

/-- `y = A x`, with the source dimensions `x : R^n`, `y : R^m`. -/
noncomputable def yof (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, P.A i j * x j

/-- `z = A^T dualp(y)`, with `z : R^n`. -/
noncomputable def zof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, P.A i j * P.dpOut (P.yof x) i

/-- The nonterminal update `x := dualq(z)`. -/
noncomputable def xnext (x : Fin n → ℝ) : Fin n → ℝ :=
  P.dqIn (P.zof x)

/-- The exact scalar stopping test in Algorithm 15.1. -/
def StopsAt (x : Fin n → ℝ) : Prop :=
  P.qIn (P.zof x) ≤ ∑ j : Fin n, P.zof x j * x j

/-- State of the literal rectangular loop. -/
structure State where
  x : Fin n → ℝ
  γ : ℝ

/-- One literal loop step of rectangular Algorithm 15.1. -/
noncomputable def powerStep (st : State (n := n)) : State (n := n) × Bool :=
  let y := P.yof st.x
  let z := P.zof st.x
  let γ := P.pOut y
  let zTx := ∑ j : Fin n, z j * st.x j
  if P.qIn z ≤ zTx then
    (⟨st.x, γ⟩, true)
  else
    (⟨P.dqIn z, γ⟩, false)

lemma powerStep_gamma_eq (st : State (n := n)) :
    (P.powerStep st).1.γ = P.pOut (P.yof st.x) := by
  simp only [powerStep]
  split_ifs <;> rfl

/-- The transpose-pairing identity used in Lemma 15.2. -/
lemma z_dot (x v : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * v j) =
      ∑ i : Fin m, P.dpOut (P.yof x) i * P.yof v i := by
  unfold zof yof
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Higham Lemma 15.2(a), at its literal `m x n` source dimensions. -/
theorem higham15_lemma15_2a_rectangular (x : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * x j) = P.pOut (P.yof x) := by
  rw [P.z_dot x x]
  exact P.dpOut_attains _

/-- Higham Lemma 15.2(b), at its literal `m x n` source dimensions. -/
theorem higham15_lemma15_2b_rectangular (x : Fin n → ℝ)
    (hx : P.pIn x = 1) :
    P.pOut (P.yof x) ≤ P.qIn (P.zof x) ∧
      P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) ∧
        P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
  have hfirst : P.pOut (P.yof x) ≤ P.qIn (P.zof x) := by
    rw [← P.higham15_lemma15_2a_rectangular x]
    calc
      (∑ j : Fin n, P.zof x j * x j) ≤
          P.qIn (P.zof x) * P.pIn x := P.holderIn _ _
      _ = P.qIn (P.zof x) := by rw [hx, mul_one]
  have hznext :
      (∑ j : Fin n, P.zof x j * P.xnext x j) = P.qIn (P.zof x) := by
    unfold xnext
    rw [show (∑ j : Fin n, P.zof x j * P.dqIn (P.zof x) j) =
        ∑ j : Fin n, P.dqIn (P.zof x) j * P.zof x j by
      apply Finset.sum_congr rfl
      intro j _hj
      ring]
    exact P.dqIn_attains _
  have hmiddle : P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) := by
    rw [← hznext, P.z_dot x (P.xnext x)]
    calc
      (∑ i : Fin m, P.dpOut (P.yof x) i * P.yof (P.xnext x) i) ≤
          P.qOut (P.dpOut (P.yof x)) * P.pOut (P.yof (P.xnext x)) :=
        P.holderOut _ _
      _ ≤ 1 * P.pOut (P.yof (P.xnext x)) :=
        mul_le_mul_of_nonneg_right (P.dpOut_qunit _) (P.pOut_nonneg _)
      _ = P.pOut (P.yof (P.xnext x)) := one_mul _
  have hlast : P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
    have h := P.op_bound (P.xnext x)
    have hunit : P.pIn (P.xnext x) = 1 := by
      simp only [xnext]
      exact P.dqIn_punit _
    rw [hunit, mul_one] at h
    simpa [yof] using h
  exact ⟨hfirst, hmiddle, hlast⟩

/-- Package of both parts of Higham Lemma 15.2 at rectangular strength. -/
theorem higham15_lemma15_2_rectangular (x : Fin n → ℝ)
    (hx : P.pIn x = 1) :
    (∑ j : Fin n, P.zof x j * x j) = P.pOut (P.yof x) ∧
      P.pOut (P.yof x) ≤ P.qIn (P.zof x) ∧
      P.qIn (P.zof x) ≤ P.pOut (P.yof (P.xnext x)) ∧
      P.pOut (P.yof (P.xnext x)) ≤ P.opP := by
  exact ⟨P.higham15_lemma15_2a_rectangular x,
    P.higham15_lemma15_2b_rectangular x hx⟩

/-- The first inequality is strict exactly when the loop does not stop. -/
theorem higham15_lemma15_2_rectangular_strict (x : Fin n → ℝ)
    :
    ¬ P.StopsAt x ↔ P.pOut (P.yof x) < P.qIn (P.zof x) := by
  have heq := P.higham15_lemma15_2a_rectangular x
  simp only [StopsAt, heq]
  exact not_le

/-- Functional iteration underlying Algorithm 15.1.  Stopping is recorded
separately by `StopsAt`, so this trace does not assert termination. -/
noncomputable def xseq (x0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => P.xnext (xseq x0 k)

lemma xseq_punit (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.pIn (P.xseq x0 k) = 1 := by
  cases k with
  | zero => exact hx0
  | succ k => simpa [xseq, xnext] using P.dqIn_punit (P.zof (P.xseq x0 k))

noncomputable def gammaSeq (x0 : Fin n → ℝ) (k : ℕ) : ℝ :=
  P.pOut (P.yof (P.xseq x0 k))

theorem gammaSeq_mono (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.gammaSeq x0 (k + 1) := by
  have hk := P.xseq_punit x0 hx0 k
  have h := P.higham15_lemma15_2b_rectangular (P.xseq x0 k) hk
  exact h.1.trans (by simpa [gammaSeq, xseq] using h.2.1)

theorem gammaSeq_le_opP (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.opP := by
  have hk := P.xseq_punit x0 hx0 k
  have h := P.op_bound (P.xseq x0 k)
  rw [hk, mul_one] at h
  simpa [gammaSeq, yof] using h

/-- Relational terminal of Algorithm 15.1: the trace stops at iteration `k`
and returns the estimate attached to that iterate.  This represents the source
`repeat ... quit` without claiming termination for general `p`. -/
def AlgorithmResult (x0 : Fin n → ℝ) (k : ℕ) (γ : ℝ)
    (x : Fin n → ℝ) : Prop :=
  x = P.xseq x0 k ∧ P.StopsAt x ∧ γ = P.pOut (P.yof x)

/-- Literal rectangular Algorithm 15.1 output specification. -/
theorem higham15_algorithm15_1_rectangular_result
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1)
    {k : ℕ} {γ : ℝ} {x : Fin n → ℝ}
    (hresult : P.AlgorithmResult x0 k γ x) :
    γ ≤ P.opP ∧ P.pOut (P.yof x) = γ * P.pIn x := by
  rcases hresult with ⟨rfl, _hstop, rfl⟩
  have hx := P.xseq_punit x0 hx0 k
  refine ⟨P.gammaSeq_le_opP x0 hx0 k, ?_⟩
  rw [hx, mul_one]

/-- The Boolean loop body is the source stopping test and preserves unit input
norm in either branch. -/
theorem higham15_algorithm15_1_rectangular_step
    (st : State (n := n)) (hx : P.pIn st.x = 1) :
    ((P.powerStep st).2 = true ↔ P.StopsAt st.x) ∧
      P.pIn (P.powerStep st).1.x = 1 ∧
      (P.powerStep st).1.γ ≤ P.opP := by
  have hbound : P.pOut (P.yof st.x) ≤ P.opP := by
    have h := P.op_bound st.x
    rw [hx, mul_one] at h
    exact h
  unfold powerStep StopsAt
  dsimp only
  split_ifs with hstop
  · exact ⟨Iff.intro (fun _ => hstop) (fun _ => rfl), hx, hbound⟩
  · refine ⟨Iff.intro (fun h => h.elim) (fun h => hstop h), ?_, hbound⟩
    · exact P.dqIn_punit _

/-- Exact induced rectangular real matrix `l^p` norm used by the concrete
general-`p` instance below. -/
noncomputable def realRectMatrixLpNorm {m n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (A : Fin m → Fin n → ℝ) : ℝ :=
  complexMatrixLpNormOfReal hn p hp (realRectToCMatrix A)

/-- Concrete literal-rectangular instance for every Holder-conjugate
`1 < p,q < infinity`. -/
noncomputable def general {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := realVecLpNorm p
  qIn := realVecLpNorm q
  pOut := realVecLpNorm p
  qOut := realVecLpNorm q
  opP := realRectMatrixLpNorm hn p (le_of_lt hpq.lt) A
  dpOut := realLpDual hpq
  dqIn := realLpDualUnit hn hpq.symm
  pIn_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := n) (ENNReal.ofReal p)).nonneg _
  pOut_nonneg := fun v => by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    exact (complexVecLpNorm_isComplexVectorNorm
      (n := m) (ENNReal.ofReal p)).nonneg _
  dpOut_attains := fun v => (realLpDual_spec hpq v).2
  dpOut_qunit := fun v => (realLpDual_spec hpq v).1
  dqIn_attains := realLpDualUnit_attains hn hpq.symm
  dqIn_punit := realLpDualUnit_norm_eq_one hn hpq.symm
  holderIn := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  holderOut := fun u v => (le_abs_self _).trans (realVecLpNorm_holder hpq u v)
  op_bound := fun v => by
    have hval := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    have hbound := hval.1 (fun j : Fin n => (v j : ℂ))
    simpa [realRectMatrixLpNorm, realVecLpNorm, complexMatrixVecMul,
      realRectToCMatrix] using hbound

/-- Exact rectangular induced 1-norm inequality. -/
theorem oneNormVec_rectMatVec_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * x j) ≤
      oneNormRect A * oneNormVec x := by
  unfold oneNormVec
  calc
    (∑ i : Fin m, |∑ j : Fin n, A i j * x j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, |A i j * x j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j : Fin n, |x j| * ∑ i : Fin m, |A i j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      simp_rw [abs_mul]
      rw [← Finset.sum_mul]
      ring
    _ ≤ ∑ j : Fin n, |x j| * oneNormRect A :=
      Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (col_sum_le_oneNormRect A j) (abs_nonneg _))
    _ = oneNormRect A * ∑ j : Fin n, |x j| := by
      rw [← Finset.sum_mul]
      ring

/-- Exact rectangular induced infinity-norm inequality. -/
theorem infNormVec_rectMatVec_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    infNormVec (fun i => ∑ j : Fin n, A i j * x j) ≤
      infNormRect A * infNormVec x := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |∑ j : Fin n, A i j * x j| ≤ ∑ j : Fin n, |A i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j : Fin n, |A i j| * infNormVec x :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _))
      _ = (∑ j : Fin n, |A i j|) * infNormVec x := by rw [Finset.sum_mul]
      _ ≤ infNormRect A * infNormVec x :=
        mul_le_mul_of_nonneg_right (row_sum_le_infNormRect A i)
          (infNormVec_nonneg x)
  · exact mul_nonneg (infNormRect_nonneg A) (infNormVec_nonneg x)

/-- Literal rectangular endpoint instance `p=1`, `q=infinity`. -/
noncomputable def one {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := oneNormVec
  qIn := infNormVec
  pOut := oneNormVec
  qOut := infNormVec
  opP := oneNormRect A
  dpOut := signVec
  dqIn := dualq_one hn
  pIn_nonneg := oneNormVec_nonneg
  pOut_nonneg := oneNormVec_nonneg
  dpOut_attains := sign_attains_one
  dpOut_qunit := sign_qunit_one
  dqIn_attains := dualq_one_attains hn
  dqIn_punit := dualq_one_punit hn
  holderIn := holder_one
  holderOut := holder_one
  op_bound := oneNormVec_rectMatVec_le A

lemma signVec_infNorm_eq_one {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    infNormVec (signVec x) = 1 := by
  apply le_antisymm (sign_qunit_one x)
  let i0 : Fin n := ⟨0, hn⟩
  have h := abs_le_infNormVec (signVec x) i0
  simpa [abs_signVec] using h

/-- Holder inequality in the orientation `l^1`-dual against `l^infinity`. -/
lemma holder_inf {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ oneNormVec u * infNormVec v := by
  have h := holder_one v u
  calc
    (∑ i : Fin n, u i * v i) = ∑ i : Fin n, v i * u i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ infNormVec v * oneNormVec u := h
    _ = oneNormVec u * infNormVec v := by ring

/-- Literal rectangular endpoint instance `p=infinity`, `q=1`. -/
noncomputable def infinity {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := infNormVec
  qIn := oneNormVec
  pOut := infNormVec
  qOut := oneNormVec
  opP := infNormRect A
  dpOut := dualq_one hm
  dqIn := signVec
  pIn_nonneg := infNormVec_nonneg
  pOut_nonneg := infNormVec_nonneg
  dpOut_attains := dualq_one_attains hm
  dpOut_qunit := fun v => by rw [dualq_one_punit hm]
  dqIn_attains := sign_attains_one
  dqIn_punit := signVec_infNorm_eq_one hn
  holderIn := holder_inf
  holderOut := holder_inf
  op_bound := infNormVec_rectMatVec_le A

/-- Direct source-strength rectangular Lemma 15.2 for `p=1`. -/
theorem higham15_lemma15_2_rectangular_one {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : oneNormVec x = 1) :
    (∑ j : Fin n, (one hn A).zof x j * x j) =
        oneNormVec ((one hn A).yof x) ∧
      oneNormVec ((one hn A).yof x) ≤ infNormVec ((one hn A).zof x) ∧
      infNormVec ((one hn A).zof x) ≤
        oneNormVec ((one hn A).yof ((one hn A).xnext x)) ∧
      oneNormVec ((one hn A).yof ((one hn A).xnext x)) ≤ oneNormRect A :=
  (one hn A).higham15_lemma15_2_rectangular x hx

/-- Direct source-strength rectangular Lemma 15.2 for `p=infinity`. -/
theorem higham15_lemma15_2_rectangular_infinity {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : infNormVec x = 1) :
    (∑ j : Fin n, (infinity hm hn A).zof x j * x j) =
        infNormVec ((infinity hm hn A).yof x) ∧
      infNormVec ((infinity hm hn A).yof x) ≤
        oneNormVec ((infinity hm hn A).zof x) ∧
      oneNormVec ((infinity hm hn A).zof x) ≤
        infNormVec ((infinity hm hn A).yof ((infinity hm hn A).xnext x)) ∧
      infNormVec ((infinity hm hn A).yof ((infinity hm hn A).xnext x)) ≤
        infNormRect A :=
  (infinity hm hn A).higham15_lemma15_2_rectangular x hx

end RectPNormPair

end NumStability
