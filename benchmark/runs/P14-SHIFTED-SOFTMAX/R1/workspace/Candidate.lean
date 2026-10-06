import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace HighamBenchCandidate

open NumStability

/-- The nonmaximal indices, in the input order used by Algorithm 4.1. -/
def nonmaxIndices {n : ℕ} (k : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun i => i ≠ k)

private theorem nonmaxIndices_length {n : ℕ} (k : Fin n) :
    (nonmaxIndices k).length = n - 1 := by
  have hfilter : nonmaxIndices k = (List.finRange n).erase k := by
    rw [nonmaxIndices, (List.nodup_finRange n).erase_eq_filter]
    apply List.filter_congr
    intro i hi
    by_cases h : i = k <;> simp [h]
  rw [hfilter, List.length_erase, List.length_finRange]
  simp [List.mem_finRange]

private theorem shifted_abs_le_range {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, x i ≤ x k) (i : Fin n) :
    |x i - x k| ≤ x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x := by
  have hmin : Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x ≤ x i :=
    Finset.inf'_le x (Finset.mem_univ i)
  rw [abs_of_nonpos (sub_nonpos.mpr (hk i))]
  linarith

/-- Exact shifted exponential, before any local rounding. -/
noncomputable def exactWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n) : ℝ :=
  Real.exp (x i - x k)

/-- Shifted exponentials after one rounded subtraction and one exponential evaluation. -/
noncomputable def computedWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n)
    (δsub δexp : Fin n → ℝ) : ℝ :=
  Real.exp ((x i - x k) * (1 + δsub i)) * (1 + δexp i)

private theorem computedWeight_bounds {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, x i ≤ x k) (i : Fin n) (u : ℝ) (δsub δexp : Fin n → ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hs : |δsub i| ≤ u) (he : |δexp i| ≤ u) :
    exactWeight x k i * (Real.exp (-(x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) * u) * (1 - u)) ≤
      computedWeight x k i δsub δexp ∧
    computedWeight x k i δsub δexp ≤
      exactWeight x k i * (Real.exp ((x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) * u) * (1 + u)) := by
  let D := x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x
  have hD : 0 ≤ D := by
    have h := Finset.inf'_le x (Finset.mem_univ k)
    dsimp [D]
    linarith
  have hzabs : |(x i - x k) * δsub i| ≤ D * u := by
    rw [abs_mul]
    exact mul_le_mul (shifted_abs_le_range x k hk i) hs (abs_nonneg _) hD
  have hzlo : -D * u ≤ (x i - x k) * δsub i := by
    have h := (abs_le.mp hzabs).1
    linarith
  have hzhi : (x i - x k) * δsub i ≤ D * u := (abs_le.mp hzabs).2
  have hexplo : Real.exp (-D * u) ≤ Real.exp ((x i - x k) * δsub i) :=
    Real.exp_le_exp.mpr hzlo
  have hexphi : Real.exp ((x i - x k) * δsub i) ≤ Real.exp (D * u) :=
    Real.exp_le_exp.mpr hzhi
  have hflo : 1 - u ≤ 1 + δexp i := by linarith [(abs_le.mp he).1]
  have hfhi : 1 + δexp i ≤ 1 + u := by linarith [(abs_le.mp he).2]
  have hfac : 0 ≤ 1 - u := by linarith
  have hweight :
      computedWeight x k i δsub δexp =
        exactWeight x k i * (Real.exp ((x i - x k) * δsub i) * (1 + δexp i)) := by
    unfold computedWeight exactWeight
    have heq : (x i - x k) * (1 + δsub i) =
        (x i - x k) + (x i - x k) * δsub i := by ring
    rw [heq, Real.exp_add]
    ring
  have hmullo :
      Real.exp (-D * u) * (1 - u) ≤
        Real.exp ((x i - x k) * δsub i) * (1 + δexp i) := by
    exact mul_le_mul hexplo hflo hfac (Real.exp_pos _).le
  have hmulhi :
      Real.exp ((x i - x k) * δsub i) * (1 + δexp i) ≤
        Real.exp (D * u) * (1 + u) := by
    exact mul_le_mul hexphi hfhi (by linarith) (Real.exp_pos _).le
  rw [hweight]
  exact ⟨mul_le_mul_of_nonneg_left hmullo (Real.exp_pos _).le,
    mul_le_mul_of_nonneg_left hmulhi (Real.exp_pos _).le⟩

private theorem foldl_round_bounds {α : Type*} (l : List α)
    (w δ : α → ℝ) (u a : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hw : ∀ j ∈ l, 0 ≤ w j)
    (hδ : ∀ j ∈ l, |δ j| ≤ u) :
    (1 - u) ^ l.length * (a + (l.map w).sum) ≤
      l.foldl (fun acc j => (acc + w j) * (1 + δ j)) a ∧
    l.foldl (fun acc j => (acc + w j) * (1 + δ j)) a ≤
      (1 + u) ^ l.length * (a + (l.map w).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons j rest ih =>
      have hwj : 0 ≤ w j := hw j (by simp)
      have hδj : -u ≤ δ j ∧ δ j ≤ u := abs_le.mp (hδ j (by simp))
      have hbase : 0 ≤ a + w j := add_nonneg ha hwj
      have hnext : 0 ≤ (a + w j) * (1 + δ j) := by
        apply mul_nonneg hbase
        linarith
      have hwrest : ∀ t ∈ rest, 0 ≤ w t := by
        intro t ht
        exact hw t (by simp [ht])
      have hδrest : ∀ t ∈ rest, |δ t| ≤ u := by
        intro t ht
        exact hδ t (by simp [ht])
      have hsum : 0 ≤ (rest.map w).sum :=
        List.sum_nonneg (by intro z hz; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz; exact hwrest t ht)
      have hpowlo : 0 ≤ (1 - u) ^ rest.length :=
        pow_nonneg (by linarith) _
      have hpowhi : 0 ≤ (1 + u) ^ rest.length :=
        pow_nonneg (by linarith) _
      obtain ⟨hlo, hhi⟩ := ih ((a + w j) * (1 + δ j)) hnext hwrest hδrest
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons, pow_succ]
      constructor
      · have hstep :
            (1 - u) * (a + w j + (rest.map w).sum) ≤
              (a + w j) * (1 + δ j) + (rest.map w).sum := by
          nlinarith [mul_nonneg hbase (show 0 ≤ δ j + u by linarith),
            mul_nonneg hu0 hsum]
        calc
          (1 - u) ^ rest.length * (1 - u) * (a + (w j + (rest.map w).sum))
              = (1 - u) ^ rest.length * ((1 - u) * (a + w j + (rest.map w).sum)) := by ring
          _ ≤ (1 - u) ^ rest.length * ((a + w j) * (1 + δ j) + (rest.map w).sum) :=
                mul_le_mul_of_nonneg_left hstep hpowlo
          _ ≤ rest.foldl (fun acc t => (acc + w t) * (1 + δ t))
                ((a + w j) * (1 + δ j)) := hlo
      · have hstep :
            (a + w j) * (1 + δ j) + (rest.map w).sum ≤
              (1 + u) * (a + w j + (rest.map w).sum) := by
          nlinarith [mul_nonneg hbase (show 0 ≤ u - δ j by linarith),
            mul_nonneg hu0 hsum]
        calc
          rest.foldl (fun acc t => (acc + w t) * (1 + δ t))
              ((a + w j) * (1 + δ j))
              ≤ (1 + u) ^ rest.length * ((a + w j) * (1 + δ j) + (rest.map w).sum) := hhi
          _ ≤ (1 + u) ^ rest.length * ((1 + u) * (a + w j + (rest.map w).sum)) :=
                mul_le_mul_of_nonneg_left hstep hpowhi
          _ = (1 + u) ^ rest.length * (1 + u) *
                (a + (w j + (rest.map w).sum)) := by ring

private theorem list_sum_bounds {α : Type*} (l : List α)
    (v w : α → ℝ) (L U : ℝ)
    (hb : ∀ i ∈ l, L * v i ≤ w i ∧ w i ≤ U * v i) :
    L * (l.map v).sum ≤ (l.map w).sum ∧
      (l.map w).sum ≤ U * (l.map v).sum := by
  have hlo : (l.map (fun i => L * v i)).sum ≤ (l.map w).sum :=
    List.sum_le_sum (by intro i hi; exact (hb i hi).1)
  have hhi : (l.map w).sum ≤ (l.map (fun i => U * v i)).sum :=
    List.sum_le_sum (by intro i hi; exact (hb i hi).2)
  simpa [List.sum_map_mul_left] using And.intro hlo hhi

/-- Sum the computed nonmaximal exponentials from the first term onward.
The first term is loaded without an addition; each later term has one rounded
addition, as in the summation analysis preceding (4.6). -/
noncomputable def computedNonmaxSum {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (δsub δexp δadd : Fin n → ℝ) : ℝ :=
  match nonmaxIndices k with
  | [] => 0
  | i :: rest =>
      rest.foldl
        (fun acc j => (acc + computedWeight x k j δsub δexp) * (1 + δadd j))
        (computedWeight x k i δsub δexp)

noncomputable def exactNonmaxSum {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ((nonmaxIndices k).map (exactWeight x k)).sum

private theorem exactNonmaxSum_nonneg {n : ℕ} (x : Fin n → ℝ) (k : Fin n) :
    0 ≤ exactNonmaxSum x k := by
  unfold exactNonmaxSum
  apply List.sum_nonneg
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  exact (Real.exp_pos _).le

private theorem computedNonmaxSum_bounds {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (k : Fin n) (hk : ∀ i, x i ≤ x k)
    (u : ℝ) (δsub δexp δadd : Fin n → ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hs : ∀ i, |δsub i| ≤ u) (he : ∀ i, |δexp i| ≤ u)
    (ha : ∀ i, |δadd i| ≤ u) :
    Real.exp (-(x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) * u) *
        (1 - u) ^ (n - 1) * exactNonmaxSum x k ≤
      computedNonmaxSum x k δsub δexp δadd ∧
    computedNonmaxSum x k δsub δexp δadd ≤
      Real.exp ((x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) * u) *
        (1 + u) ^ (n - 1) * exactNonmaxSum x k := by
  let D := x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x
  let L := Real.exp (-D * u) * (1 - u)
  let U := Real.exp (D * u) * (1 + u)
  have hL : 0 ≤ L := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hU : 0 ≤ U := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hwb : ∀ i, L * exactWeight x k i ≤ computedWeight x k i δsub δexp ∧
      computedWeight x k i δsub δexp ≤ U * exactWeight x k i := by
    intro i
    have h := computedWeight_bounds x k hk i u δsub δexp hu0 hu1 (hs i) (he i)
    simpa [L, U, D, mul_comm] using h
  have hwpos : ∀ i, 0 ≤ computedWeight x k i δsub δexp := by
    intro i
    exact le_trans (mul_nonneg hL (Real.exp_pos _).le) (hwb i).1
  have hlen := nonmaxIndices_length k
  cases hlist : nonmaxIndices k with
  | nil =>
      simp [hlist] at hlen
      omega
  | cons i rest =>
      have hrest : rest.length = n - 2 := by
        simp [hlist] at hlen
        omega
      have hpow : n - 1 = rest.length + 1 := by omega
      have hfold := foldl_round_bounds rest
        (fun j => computedWeight x k j δsub δexp) δadd u
        (computedWeight x k i δsub δexp) hu0 hu1 (hwpos i)
        (by intro j hj; exact hwpos j)
        (by intro j hj; exact ha j)
      have hsum := list_sum_bounds (i :: rest) (exactWeight x k)
        (fun j => computedWeight x k j δsub δexp) L U
        (by intro j hj; exact hwb j)
      have hpowlo : 0 ≤ (1-u)^rest.length := pow_nonneg (by linarith) _
      have hpowhi : 0 ≤ (1+u)^rest.length := pow_nonneg (by linarith) _
      have hslo :
          (1-u)^rest.length *
            (L * (exactWeight x k i + (rest.map (exactWeight x k)).sum)) ≤
            computedNonmaxSum x k δsub δexp δadd := by
        unfold computedNonmaxSum
        rw [hlist]
        exact le_trans (mul_le_mul_of_nonneg_left
          (by simpa using hsum.1) hpowlo) (by simpa using hfold.1)
      have hshi :
          computedNonmaxSum x k δsub δexp δadd ≤
            (1+u)^rest.length *
              (U * (exactWeight x k i + (rest.map (exactWeight x k)).sum)) := by
        unfold computedNonmaxSum
        rw [hlist]
        exact le_trans (by simpa using hfold.2)
          (mul_le_mul_of_nonneg_left (by simpa using hsum.2) hpowhi)
      unfold exactNonmaxSum
      rw [hlist]
      simp only [List.map_cons, List.sum_cons]
      constructor
      · simpa [D, L, hpow, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hslo
      · simpa [D, U, hpow, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hshi

/-- The full exact shifted softmax vector, including the maximal component. -/
noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n) :
    Fin n → ℝ :=
  fun i => exactWeight x k i / (1 + exactNonmaxSum x k)

/-- The full computed shifted softmax vector. The final denominator is exactly
`1 +` the computed nonmaximal sum; only the division is rounded. -/
noncomputable def computedSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (δsub δexp δadd δdiv : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    (computedWeight x k i δsub δexp /
      (1 + computedNonmaxSum x k δsub δexp δadd)) * (1 + δdiv i)

private theorem local_linear_bound {f : ℝ → ℝ} {a B : ℝ}
    (hf : HasDerivAt f a 0) (h0 : f 0 = 1) (hB : |a| < B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → |f t - 1| ≤ B * |t| := by
  let gap := (B - |a|) / 2
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hevent : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ),
      |t⁻¹ * (f t - 1) - a| < gap := by
    have hlim := HasDerivAt.tendsto_slope_zero hf
    simpa [h0, smul_eq_mul] using
      hlim.eventually (Metric.ball_mem_nhds a hgap)
  obtain ⟨r, hr, hsubset⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨r / 2, by positivity, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0, h0]
  have htball : t ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |t| < r := by linarith
    simpa using this
  have hts : t ∈ ({0}ᶜ : Set ℝ) := by simpa using ht0
  have hsl : |t⁻¹ * (f t - 1) - a| < gap := hsubset ⟨htball, hts⟩
  have habs : |t⁻¹ * (f t - 1)| ≤ B := by
    have htri : |t⁻¹ * (f t - 1)| ≤
        |t⁻¹ * (f t - 1) - a| + |a| := by
      calc
        |t⁻¹ * (f t - 1)| = |(t⁻¹ * (f t - 1) - a) + a| := by ring
        _ ≤ _ := abs_add_le _ _
    have hsmall : gap + |a| < B := by dsimp [gap]; linarith
    linarith
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have hmul : |t⁻¹ * (f t - 1)| * |t| = |f t - 1| := by
    rw [abs_mul, abs_inv]
    field_simp [htpos.ne']
  nlinarith [mul_le_mul_of_nonneg_right habs (abs_nonneg t)]

private noncomputable def envelope (D : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (2 * D * t) * (1 + t)^2 / (1-t)^m

private theorem envelope_deriv (D : ℝ) (m : ℕ) :
    HasDerivAt (envelope D m) (2*D+2+m) 0 := by
  have harg : HasDerivAt (fun t : ℝ => 2*D*t) (2*D) 0 := by
    convert (hasDerivAt_id (0:ℝ)).const_mul (2*D) using 1 <;> simp
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (2*D*t)) (2*D) 0 := by
    convert (Real.hasDerivAt_exp (2*D*(0:ℝ))).comp 0 harg using 1 <;> simp
  have hplus : HasDerivAt (fun t : ℝ => 1+t) 1 0 := by
    convert (hasDerivAt_id (0:ℝ)).const_add 1 using 1 <;> simp
  have hminus : HasDerivAt (fun t : ℝ => 1-t) (-1) 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ)) using 1 <;> simp
  unfold envelope
  convert (hexp.mul (hplus.pow 2)).div (hminus.pow m) (by simp) using 1 <;>
    simp <;> ring

private theorem envelope_local (D : ℝ) (m : ℕ) (hD : 0 ≤ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε →
      |envelope D m t - 1| ≤ (2*D+3+m) * |t| := by
  apply local_linear_bound (envelope_deriv D m) (by simp [envelope])
  have ha : 0 ≤ 2*D+2+(m:ℝ) := by positivity
  rw [abs_of_nonneg ha]
  linarith

private theorem quotient_bounds {Nlo N Nhi Dlo D Dhi : ℝ}
    (hNlo : 0 ≤ Nlo) (hNhi : 0 ≤ Nhi)
    (hNlower : Nlo ≤ N) (hNupper : N ≤ Nhi)
    (hDlo : 0 < Dlo) (hDlower : Dlo ≤ D) (hDupper : D ≤ Dhi) :
    Nlo / Dhi ≤ N / D ∧ N / D ≤ Nhi / Dlo := by
  have hD : 0 < D := lt_of_lt_of_le hDlo hDlower
  constructor
  · exact (div_le_div_of_nonneg_left hNlo hD hDupper).trans
      (div_le_div_of_nonneg_right hNlower hD.le)
  · exact (div_le_div_of_nonneg_right hNupper hD.le).trans
      (div_le_div_of_nonneg_left hNhi hDlo hDlower)

/-- The local relative-error model for the subtraction, exponential,
recursive additions, and final divisions. Errors are indexed separately, so
two calls with equal operands may have different admissible local errors. -/
def AdmissibleErrors {n : ℕ} (u : ℝ)
    (δsub δexp δadd δdiv : Fin n → ℝ) : Prop :=
  (∀ i, |δsub i| ≤ u) ∧
  (∀ i, |δexp i| ≤ u) ∧
  (∀ i, |δadd i| ≤ u) ∧
  (∀ i, |δdiv i| ≤ u)

private theorem computedSoftmax_envelope {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (k : Fin n) (hk : ∀ i, x i ≤ x k)
    (u : ℝ) (δsub δexp δadd δdiv : Fin n → ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (herr : AdmissibleErrors u δsub δexp δadd δdiv)
    (i : Fin n) :
    exactSoftmax x k i * envelope
      (x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) (n-1) (-u) ≤
      computedSoftmax x k δsub δexp δadd δdiv i ∧
    computedSoftmax x k δsub δexp δadd δdiv i ≤
      exactSoftmax x k i * envelope
        (x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x) (n-1) u := by
  let D := x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x
  let w := exactWeight x k i
  let wh := computedWeight x k i δsub δexp
  let s := exactNonmaxSum x k
  let sh := computedNonmaxSum x k δsub δexp δadd
  let A := Real.exp (-D*u) * (1-u)^(n-1)
  let B := Real.exp (D*u) * (1+u)^(n-1)
  let L := Real.exp (-D*u) * (1-u)
  let U := Real.exp (D*u) * (1+u)
  have hD : 0 ≤ D := by
    dsimp [D]
    have h := Finset.inf'_le x (Finset.mem_univ k)
    linarith
  have hu1' : u ≤ 1 := by linarith
  have hAle : A ≤ 1 := by
    have he : Real.exp (-D*u) ≤ 1 := by
      have hz : -D*u ≤ 0 := by nlinarith
      simpa using (Real.exp_le_exp.mpr hz : Real.exp (-D*u) ≤ Real.exp 0)
    exact mul_le_one₀ he (pow_nonneg (by linarith) _) (pow_le_one₀ (by linarith) (by linarith))
  have hBle : 1 ≤ B := by
    have he : 1 ≤ Real.exp (D*u) := by
      have hz : 0 ≤ D*u := mul_nonneg hD hu0
      simpa using (Real.exp_le_exp.mpr hz : Real.exp 0 ≤ Real.exp (D*u))
    exact one_le_mul_of_one_le_of_one_le he (one_le_pow₀ (by linarith))
  have hApos : 0 < A := mul_pos (Real.exp_pos _) (pow_pos (by linarith) _)
  have hBpos : 0 < B := mul_pos (Real.exp_pos _) (pow_pos (by linarith) _)
  have hLnonneg : 0 ≤ L := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hUnonneg : 0 ≤ U := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hwpos : 0 ≤ w := (Real.exp_pos _).le
  have hspos : 0 ≤ s := exactNonmaxSum_nonneg x k
  obtain ⟨hslo, hshi⟩ := computedNonmaxSum_bounds hn x k hk u δsub δexp δadd
      hu0 hu1' herr.1 herr.2.1 herr.2.2.1
  have hdenlo : A * (1+s) ≤ 1+sh := by
    dsimp [A, sh, s] at hslo ⊢
    nlinarith [hAle]
  have hdenhi : 1+sh ≤ B * (1+s) := by
    dsimp [B, sh, s] at hshi ⊢
    nlinarith [hBle]
  have hdenpos : 0 < 1+sh := lt_of_lt_of_le
    (mul_pos hApos (by linarith)) hdenlo
  have hwb := computedWeight_bounds x k hk i u δsub δexp hu0 hu1'
      (herr.1 i) (herr.2.1 i)
  have hwlo : L*w ≤ wh := by simpa [L, w, wh, D, mul_comm] using hwb.1
  have hwhi : wh ≤ U*w := by simpa [U, w, wh, D, mul_comm] using hwb.2
  have hwhnonneg : 0 ≤ wh := le_trans (mul_nonneg hLnonneg hwpos) hwlo
  have hdlo : 1-u ≤ 1+δdiv i := by linarith [(abs_le.mp (herr.2.2.2 i)).1]
  have hdhi : 1+δdiv i ≤ 1+u := by linarith [(abs_le.mp (herr.2.2.2 i)).2]
  have hnumlo : w*L*(1-u) ≤ wh*(1+δdiv i) := by
    have h := mul_le_mul hwlo hdlo (by linarith) hwhnonneg
    nlinarith [h]
  have hnumhi : wh*(1+δdiv i) ≤ w*U*(1+u) := by
    have h := mul_le_mul hwhi hdhi (by linarith) (mul_nonneg hUnonneg hwpos)
    nlinarith [h]
  have hquot := quotient_bounds
    (mul_nonneg (mul_nonneg hwpos hLnonneg) (by linarith))
    (mul_nonneg (mul_nonneg hwpos hUnonneg) (by linarith))
    hnumlo hnumhi (mul_pos hApos (by linarith)) hdenlo hdenhi
  have hExpLo : Real.exp (-D*u) = Real.exp (-2*D*u) * Real.exp (D*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpHi : Real.exp (D*u) = Real.exp (2*D*u) * Real.exp (-D*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hloeq :
      (w*L*(1-u))/(B*(1+s)) = exactSoftmax x k i * envelope D (n-1) (-u) := by
    unfold exactSoftmax envelope
    dsimp [w, L, B, s]
    have hExpLo' : Real.exp (-D*u) = Real.exp (2*D*(-u)) * Real.exp (D*u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExpLo']
    field_simp [ne_of_gt (Real.exp_pos (D*u)), ne_of_gt (by linarith : 0 < 1+s),
      ne_of_gt (by linarith : 0 < 1+u)]
    all_goals ring
  have hhieq :
      (w*U*(1+u))/(A*(1+s)) = exactSoftmax x k i * envelope D (n-1) u := by
    unfold exactSoftmax envelope
    dsimp [w, U, A, s]
    rw [hExpHi]
    field_simp [ne_of_gt (Real.exp_pos (-D*u)), ne_of_gt (by linarith : 0 < 1+s),
      ne_of_gt (by linarith : 0 < 1-u)]
    all_goals ring
  rw [← hloeq, ← hhieq]
  change (w*L*(1-u))/(B*(1+s)) ≤ wh/(1+sh)*(1+δdiv i) ∧
    wh/(1+sh)*(1+δdiv i) ≤ (w*U*(1+u))/(A*(1+s))
  simpa [div_mul_eq_mul_div] using hquot

/-- Theorem 4.3, equation (4.11). The quadratic constant and neighborhood
depend on the fixed input and order, and are uniform over every admissible
choice of local rounding errors. -/
theorem target {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, x i ≤ x k) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ (u : ℝ) (δsub δexp δadd δdiv : Fin n → ℝ),
        0 ≤ u → u ≤ ε →
        AdmissibleErrors u δsub δexp δadd δdiv →
        infNormVec (fun i =>
          computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i) /
            infNormVec (exactSoftmax x k) ≤
          ((n : ℝ) + 2 +
            2 * (x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x)) * u + C * u ^ 2 := by
  let D := x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x
  let b : ℝ := (n : ℝ) + 2 + 2*D
  have hD : 0 ≤ D := by
    dsimp [D]
    have h := Finset.inf'_le x (Finset.mem_univ k)
    linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hbeq : 2*D + 3 + ((n-1:ℕ):ℝ) = b := by
    dsimp [b]
    linarith
  obtain ⟨r, hr, henv⟩ := envelope_local D (n-1) hD
  let ε : ℝ := min r (1/2)
  have hε : 0 < ε := lt_min hr (by norm_num)
  refine ⟨0, ε, le_refl 0, hε, ?_⟩
  intro u δsub δexp δadd δdiv hu0 huε herr
  have hur : u ≤ r := le_trans huε (min_le_left _ _)
  have huHalf : u ≤ 1/2 := le_trans huε (min_le_right _ _)
  have henvhi : envelope D (n-1) u ≤ 1 + b*u := by
    have h := henv u (by simpa [abs_of_nonneg hu0] using hur)
    rw [hbeq, abs_of_nonneg hu0] at h
    have hh := (abs_le.mp h).2
    linarith
  have henvlo : 1 - b*u ≤ envelope D (n-1) (-u) := by
    have h := henv (-u) (by simpa [abs_neg, abs_of_nonneg hu0] using hur)
    rw [hbeq, abs_neg, abs_of_nonneg hu0] at h
    have hh := (abs_le.mp h).1
    linarith
  have hspos : 0 ≤ exactNonmaxSum x k := exactNonmaxSum_nonneg x k
  have hgpos : ∀ i, 0 ≤ exactSoftmax x k i := by
    intro i
    unfold exactSoftmax
    exact (div_pos (Real.exp_pos _) (by linarith)).le
  have hgk : 0 < exactSoftmax x k k := by
    unfold exactSoftmax
    exact div_pos (Real.exp_pos _) (by linarith)
  have hnormpos : 0 < infNormVec (exactSoftmax x k) := by
    have h := abs_le_infNormVec (exactSoftmax x k) k
    rw [abs_of_pos hgk] at h
    exact lt_of_lt_of_le hgk h
  have hpoint : ∀ i : Fin n,
      |computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i| ≤
        b*u*exactSoftmax x k i := by
    intro i
    obtain ⟨hlo, hhi⟩ := computedSoftmax_envelope hn x k hk u
      δsub δexp δadd δdiv hu0 huHalf herr i
    have hleft := mul_le_mul_of_nonneg_left henvlo (hgpos i)
    have hright := mul_le_mul_of_nonneg_left henvhi (hgpos i)
    rw [abs_le]
    constructor <;> nlinarith
  have hbound : infNormVec (fun i =>
      computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i) ≤
        b*u*infNormVec (exactSoftmax x k) := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i|
            ≤ b*u*exactSoftmax x k i := hpoint i
        _ ≤ b*u*infNormVec (exactSoftmax x k) := by
          have hg := abs_le_infNormVec (exactSoftmax x k) i
          rw [abs_of_nonneg (hgpos i)] at hg
          exact mul_le_mul_of_nonneg_left hg (mul_nonneg hb hu0)
    · exact mul_nonneg (mul_nonneg hb hu0) hnormpos.le
  have hquot :
      infNormVec (fun i =>
        computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i) /
          infNormVec (exactSoftmax x k) ≤ b*u := by
    apply (div_le_iff₀ hnormpos).mpr
    simpa [mul_comm] using hbound
  simpa [b, D] using hquot

end HighamBenchCandidate
