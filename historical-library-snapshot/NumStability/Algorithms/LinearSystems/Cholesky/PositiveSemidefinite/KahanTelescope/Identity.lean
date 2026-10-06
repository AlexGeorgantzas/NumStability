import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Identity

Canonical destination for 2 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- Geometric telescope: `∑_{i∈[k,k+m)} c²s^{2i} = s^{2k} − s^{2(k+m)}`
    under `c² + s² = 1`. -/
private lemma kahan_telescope (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (k m : ℕ) :
    ∑ i ∈ Finset.range m, c ^ 2 * s ^ (2 * (k + i)) =
      s ^ (2 * k) - s ^ (2 * (k + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : c ^ 2 = 1 - s ^ 2 := by linarith
    have h2 : s ^ (2 * (k + (m + 1))) =
        s ^ (2 * (k + m)) * s ^ 2 := by
      rw [show 2 * (k + (m + 1)) = 2 * (k + m) + 2 by ring, pow_add]
    rw [h1, h2]
    ring

/-- **The Kahan factor satisfies the (10.13) column-tail relation with
    equality on the square part** (Higham p. 205, "R satisfies the
    inequalities (10.13) (as equalities)"): for `k ≤ j < r`,
    `∑_{i≥k} R(θ)_{ij}² = R(θ)_{kk}²`. -/
theorem kahanR_tail_eq (r n : ℕ) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (hrn : r ≤ n)
    (k : Fin r) (j : Fin n) (hkj : k.val ≤ j.val) (hjr : j.val < r) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => k.val ≤ i.val),
      kahanR r n c s i j ^ 2 =
    kahanR r n c s k ⟨k.val, by omega⟩ ^ 2 := by
  -- diagonal value
  have hdiag : kahanR r n c s k ⟨k.val, by omega⟩ = s ^ k.val := by
    unfold kahanR
    rw [if_pos rfl]
  rw [hdiag]
  -- entries in the tail: [k, j) give c²s^{2i}, i = j gives s^{2j}, rest 0
  have hval : ∀ i : Fin r, k.val ≤ i.val →
      kahanR r n c s i j ^ 2 =
      if i.val < j.val then c ^ 2 * s ^ (2 * i.val)
      else if i.val = j.val then s ^ (2 * j.val) else 0 := by
    intro i hki
    unfold kahanR
    by_cases hij : j.val = i.val
    · rw [if_pos hij, if_neg (by omega), if_pos hij.symm, ← pow_mul]
      congr 1
      omega
    · rw [if_neg hij]
      by_cases hlt : i.val < j.val
      · rw [if_pos hlt, if_pos hlt]
        rw [mul_pow, neg_pow, ← pow_mul]
        ring_nf
      · rw [if_neg hlt, if_neg hlt, if_neg (fun h => hij h.symm)]
        norm_num
  rw [Finset.sum_congr rfl fun i hi => hval i
    (by simpa using (Finset.mem_filter.mp hi).2)]
  -- reindex the filtered sum over the explicit segments
  have hsplit : ∑ i ∈ Finset.univ.filter
      (fun i : Fin r => k.val ≤ i.val),
      (if i.val < j.val then c ^ 2 * s ^ (2 * i.val)
        else if i.val = j.val then s ^ (2 * j.val) else 0) =
      (∑ t ∈ Finset.range (j.val - k.val),
        c ^ 2 * s ^ (2 * (k.val + t))) + s ^ (2 * j.val) := by
    -- direct evaluation: sum over Fin r of the guarded values
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun v =>
      if k.val ≤ v then
        (if v < j.val then c ^ 2 * s ^ (2 * v)
          else if v = j.val then s ^ (2 * j.val) else 0) else 0) r]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k.val) (by omega :
        k.val ≤ r),
      ← Finset.sum_Ico_consecutive _ (hkj : k.val ≤ j.val) (by omega :
        j.val ≤ r)]
    have hzero1 : ∑ v ∈ Finset.Ico 0 k.val,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        0 :=
      Finset.sum_eq_zero fun v hv => by
        rw [if_neg (by
          simp only [Finset.mem_Ico] at hv
          omega)]
    have hmid : ∑ v ∈ Finset.Ico k.val j.val,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        ∑ t ∈ Finset.range (j.val - k.val),
          c ^ 2 * s ^ (2 * (k.val + t)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [Finset.mem_range] at ht
      rw [if_pos (by omega), if_pos (by omega)]
    have htail : ∑ v ∈ Finset.Ico j.val r,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        s ^ (2 * j.val) := by
      have hjmem : j.val ∈ Finset.Ico j.val r := by
        simp only [Finset.mem_Ico]
        omega
      rw [Finset.sum_eq_single_of_mem j.val hjmem]
      · rw [if_pos hkj, if_neg (lt_irrefl _), if_pos rfl]
      · intro v hv hvj
        simp only [Finset.mem_Ico] at hv
        rw [if_pos (by omega), if_neg (by omega), if_neg hvj]
    rw [hzero1, hmid, htail, Finset.range_eq_Ico]
    ring
  rw [hsplit, kahan_telescope c s hcs k.val (j.val - k.val)]
  have hexp : 2 * (k.val + (j.val - k.val)) = 2 * j.val := by omega
  rw [hexp, ← pow_mul]
  ring_nf

end NumStability
