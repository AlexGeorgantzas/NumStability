-- Algorithms/Ch5NewtonForm.lean
--
-- Higham, 2nd ed., Chapter 5, Section 5.3: closing body claims for the
-- Newton form of a polynomial.
--
--   (i)  Rounding error analysis of the generalized Horner ("nested
--        multiplication") evaluator for the Newton form (5.8):
--          q_n = c_n;  q_i = (x - alpha_i) q_{i+1} + c_i;  p(x) = q_0.
--        We prove the <3n>-type backward result and the forward bound
--          |p(x) - q0hat| <= gamma_{3n} * sum_i |c_i| prod_{j<i} |x - alpha_j|
--        (Higham, closing displays of Section 5.3, "cf. (5.2)").
--
--   (ii) The monotone-node-ordering corollary of (5.11)/(5.12): for strictly
--        increasing nodes alpha_0 < alpha_1 < ... the bidiagonal factors satisfy
--          |L_{n-1}| ... |L_0| = |L_{n-1} ... L_0| = |L|   (no cancellation),
--        so the "very satisfactory" bounds
--          |c - chat|   <= ((1-3u)^{-n} - 1) |L|   |f|,
--          |f - L^{-1}chat| <= ((1-3u)^{-n} - 1) |L^{-1}| |chat|
--        hold with the exact divided-difference matrix in place of the product
--        of absolute factors.
--
-- IMPORT-ONLY: all divided-difference / Newton-form / rounding infrastructure
-- is reused from `Algorithms/Horner.lean` and `Analysis/Rounding.lean`.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.Horner

namespace NumStability

open scoped BigOperators

/-! ###########################################################################
    PART (i): Newton-form generalized-Horner evaluation error analysis.
    ###########################################################################

Coefficient list `[c_0, c_1, ..., c_n]` and node list `[alpha_0, ..., alpha_{n-1}]`
denote `p(x) = sum_i c_i prod_{j<i} (x - alpha_j)`; the exact nested evaluator
is `newtonFormNested` (see `Horner.lean`). -/

/-- Higham, 2nd ed., Section 5.3, closing display: the rounded generalized
Horner recurrence for the Newton form.  Each active step performs one rounded
subtraction `x - alpha_i`, one rounded multiplication, and one rounded
addition of `c_i` (the three roundings that give the `<3n>` counter). -/
noncomputable def ch5newton_fleval (fp : FPModel) (x : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], _ => 0
  | _c :: _cs, [] => _c
  | c :: cs, alpha :: alphas =>
      fp.fl_add (fp.fl_mul (fp.fl_sub x alpha)
        (ch5newton_fleval fp x cs alphas)) c

/-- Newton evaluation with each coefficient `c_i` carrying a multiplicative
backward-error factor `phi_i`; the coefficient/factor pairs travel together in
`cfs : List (R x R)` (first component the coefficient, second the factor). -/
noncomputable def ch5newton_pert (x : ℝ) :
    List (ℝ × ℝ) → List ℝ → ℝ
  | [], _ => 0
  | p :: _ps, [] => p.1 * p.2
  | p :: ps, alpha :: alphas =>
      p.1 * p.2 + (x - alpha) * ch5newton_pert x ps alphas

/-- Absolute-coefficient majorant `sum_i |c_i| prod_{j<i} |x - alpha_j|`, stored
in the nested (Horner-factored) form. -/
noncomputable def ch5newton_absMaj (x : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], _ => 0
  | c :: _cs, [] => |c|
  | c :: cs, alpha :: alphas =>
      |c| + |x - alpha| * ch5newton_absMaj x cs alphas

theorem ch5newton_absMaj_nonneg (x : ℝ) :
    ∀ (cs alphas : List ℝ), 0 ≤ ch5newton_absMaj x cs alphas := by
  intro cs
  induction cs with
  | nil => intro alphas; simp [ch5newton_absMaj]
  | cons c cs ih =>
      intro alphas
      cases alphas with
      | nil => simp [ch5newton_absMaj]
      | cons alpha alphas =>
          have := ih alphas
          have : 0 ≤ |x - alpha| * ch5newton_absMaj x cs alphas :=
            mul_nonneg (abs_nonneg _) (ih alphas)
          simp only [ch5newton_absMaj]
          positivity

/-- Scaling all backward-error factors by a common `rho` scales the perturbed
evaluation by `rho`. -/
theorem ch5newton_pert_scale (x rho : ℝ) :
    ∀ (cfs : List (ℝ × ℝ)) (alphas : List ℝ),
      ch5newton_pert x (cfs.map (fun p => (p.1, p.2 * rho))) alphas =
        rho * ch5newton_pert x cfs alphas := by
  intro cfs
  induction cfs with
  | nil => intro alphas; simp [ch5newton_pert]
  | cons p ps ih =>
      intro alphas
      cases alphas with
      | nil => simp [ch5newton_pert]; ring
      | cons alpha alphas =>
          simp only [List.map_cons, ch5newton_pert, ih alphas]
          ring

theorem ch5newton_pert_map_fst (rho : ℝ) :
    ∀ (cfs : List (ℝ × ℝ)),
      (cfs.map (fun p => (p.1, p.2 * rho))).map Prod.fst = cfs.map Prod.fst := by
  intro cfs
  induction cfs with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- Forward-error step for the Newton form ("cf. (5.2)"): if every coefficient
factor is within `eta` of `1`, the perturbed evaluation differs from the exact
one by at most `eta` times the absolute-coefficient majorant. -/
theorem ch5newton_pert_sub_exact_le (x eta : ℝ) (_heta : 0 ≤ eta) :
    ∀ (cfs : List (ℝ × ℝ)) (alphas : List ℝ),
      (∀ p ∈ cfs, |p.2 - 1| ≤ eta) →
      |ch5newton_pert x cfs alphas -
          newtonFormNested x (cfs.map Prod.fst) alphas| ≤
        eta * ch5newton_absMaj x (cfs.map Prod.fst) alphas := by
  intro cfs
  induction cfs with
  | nil =>
      intro alphas _
      simp [ch5newton_pert, newtonFormNested, ch5newton_absMaj]
  | cons p ps ih =>
      intro alphas hbound
      have hp : |p.2 - 1| ≤ eta := hbound p (by simp)
      have hrest : ∀ q ∈ ps, |q.2 - 1| ≤ eta := fun q hq => hbound q (by simp [hq])
      cases alphas with
      | nil =>
          -- last coefficient: only its own factor contributes
          have hval :
              ch5newton_pert x (p :: ps) [] -
                  newtonFormNested x ((p :: ps).map Prod.fst) [] =
                p.1 * (p.2 - 1) := by
            simp [ch5newton_pert, newtonFormNested]; ring
          rw [hval]
          calc
            |p.1 * (p.2 - 1)| = |p.1| * |p.2 - 1| := by rw [abs_mul]
            _ ≤ |p.1| * eta := by
                  exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
            _ = eta * ch5newton_absMaj x ((p :: ps).map Prod.fst) [] := by
                  simp [ch5newton_absMaj]; ring
      | cons alpha alphas =>
          have ihrest := ih alphas hrest
          have hsplit :
              ch5newton_pert x (p :: ps) (alpha :: alphas) -
                  newtonFormNested x ((p :: ps).map Prod.fst) (alpha :: alphas) =
                p.1 * (p.2 - 1) +
                  (x - alpha) *
                    (ch5newton_pert x ps alphas -
                      newtonFormNested x (ps.map Prod.fst) alphas) := by
            simp [ch5newton_pert, newtonFormNested]; ring
          have hfirst : |p.1 * (p.2 - 1)| ≤ eta * |p.1| := by
            calc
              |p.1 * (p.2 - 1)| = |p.1| * |p.2 - 1| := by rw [abs_mul]
              _ ≤ |p.1| * eta := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
              _ = eta * |p.1| := by ring
          have hsecond :
              |(x - alpha) *
                  (ch5newton_pert x ps alphas -
                    newtonFormNested x (ps.map Prod.fst) alphas)| ≤
                eta * (|x - alpha| * ch5newton_absMaj x (ps.map Prod.fst) alphas) := by
            rw [abs_mul]
            calc
              |x - alpha| *
                  |ch5newton_pert x ps alphas -
                    newtonFormNested x (ps.map Prod.fst) alphas|
                  ≤ |x - alpha| *
                      (eta * ch5newton_absMaj x (ps.map Prod.fst) alphas) :=
                    mul_le_mul_of_nonneg_left ihrest (abs_nonneg _)
              _ = eta * (|x - alpha| * ch5newton_absMaj x (ps.map Prod.fst) alphas) := by
                    ring
          calc
            |ch5newton_pert x (p :: ps) (alpha :: alphas) -
                newtonFormNested x ((p :: ps).map Prod.fst) (alpha :: alphas)|
                = |p.1 * (p.2 - 1) +
                    (x - alpha) *
                      (ch5newton_pert x ps alphas -
                        newtonFormNested x (ps.map Prod.fst) alphas)| := by
                  rw [hsplit]
            _ ≤ |p.1 * (p.2 - 1)| +
                  |(x - alpha) *
                    (ch5newton_pert x ps alphas -
                      newtonFormNested x (ps.map Prod.fst) alphas)| := abs_add_le _ _
            _ ≤ eta * |p.1| +
                  eta * (|x - alpha| * ch5newton_absMaj x (ps.map Prod.fst) alphas) :=
                  add_le_add hfirst hsecond
            _ = eta * ch5newton_absMaj x ((p :: ps).map Prod.fst) (alpha :: alphas) := by
                  simp [ch5newton_absMaj]; ring

/-- A Stewart relative-error counter of any length is realized by the exact
value `1` (take every local factor `1 + 0`). -/
theorem ch5newton_relErrorCounter_one_const (fp : FPModel) (m : ℕ) :
    relErrorCounter fp m (1 : ℝ) := by
  refine ⟨fun _ => 0, fun _ => false, ?_, ?_⟩
  · intro _; simpa using fp.u_nonneg
  · simp

/-- Higham, 2nd ed., Section 5.3, closing display (backward result, `<3n>`
type):  the rounded Newton evaluation equals the exact evaluation of a
polynomial whose divided differences `c_i` are each multiplied by a factor that
is a product of at most `3n` local relative-error factors (`n = alphas.length`).
Concretely we exhibit the coefficient/factor pairs. -/
theorem ch5newton_fleval_eq_pert (fp : FPModel) (x : ℝ) :
    ∀ (cs alphas : List ℝ), alphas.length + 1 = cs.length →
      ∃ cfs : List (ℝ × ℝ),
        cfs.map Prod.fst = cs ∧
        (∀ p ∈ cfs, relErrorCounter fp (3 * alphas.length) p.2) ∧
        ch5newton_fleval fp x cs alphas = ch5newton_pert x cfs alphas := by
  intro cs
  induction cs with
  | nil =>
      intro alphas hlen
      simp at hlen
  | cons c cs ih =>
      intro alphas hlen
      cases alphas with
      | nil =>
          -- cs must be empty
          have hcs : cs = [] := by
            have : cs.length = 0 := by simpa using hlen
            exact List.length_eq_zero_iff.mp this
          subst hcs
          refine ⟨[(c, 1)], ?_, ?_, ?_⟩
          · simp
          · intro p hp
            simp at hp
            subst hp
            simpa using ch5newton_relErrorCounter_one_const fp (3 * 0)
          · simp [ch5newton_fleval, ch5newton_pert]
      | cons alpha alphas =>
          have hlen' : alphas.length + 1 = cs.length := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨cfs', hmap', hcnt', heq'⟩ := ih alphas hlen'
          -- expand one rounded step
          obtain ⟨δs, hδs, hs⟩ := fp.model_sub x alpha
          obtain ⟨δm, hδm, hm⟩ :=
            fp.model_mul (fp.fl_sub x alpha) (ch5newton_fleval fp x cs alphas)
          obtain ⟨δa, hδa, ha⟩ :=
            fp.model_add
              (fp.fl_mul (fp.fl_sub x alpha) (ch5newton_fleval fp x cs alphas)) c
          set q := ch5newton_fleval fp x cs alphas with hq
          set rho := (1 + δs) * (1 + δm) * (1 + δa) with hrho
          -- the rounded step in closed form
          have hstepval :
              ch5newton_fleval fp x (c :: cs) (alpha :: alphas) =
                c * (1 + δa) + (x - alpha) * rho * q := by
            show fp.fl_add (fp.fl_mul (fp.fl_sub x alpha) q) c =
                c * (1 + δa) + (x - alpha) * rho * q
            rw [ha, hm, hs, hrho]; ring
          -- rescale the tail factors by rho
          set cfs'' := cfs'.map (fun p => (p.1, p.2 * rho)) with hcfs''
          have htailval :
              (x - alpha) * ch5newton_pert x cfs'' alphas =
                (x - alpha) * rho * q := by
            rw [hcfs'', ch5newton_pert_scale, ← heq', hq]; ring
          refine ⟨(c, 1 + δa) :: cfs'', ?_, ?_, ?_⟩
          · -- coefficients recovered
            have : (cfs''.map Prod.fst) = cs := by
              rw [hcfs'', ch5newton_pert_map_fst, hmap']
            simp [this]
          · -- every factor is a <3(n+1)> counter
            intro p hp
            have hcount : 3 * (alphas.length + 1) = 3 * alphas.length + 3 := by ring
            rw [List.length_cons, hcount]
            rcases List.mem_cons.mp hp with hhead | htail
            · -- head factor (1 + δa): pad count 1 up to 3*len+3
              subst hhead
              have h1 : relErrorCounter fp 1 (1 + δa) := relErrorCounter_one_add fp hδa
              have hpad : relErrorCounter fp (3 * alphas.length + 2) (1 : ℝ) :=
                ch5newton_relErrorCounter_one_const fp _
              have := relErrorCounter_mul fp 1 (3 * alphas.length + 2)
                (1 + δa) 1 h1 hpad
              simpa [show 1 + (3 * alphas.length + 2) = 3 * alphas.length + 3 from by ring]
                using this
            · -- a rescaled tail factor p'.2 * rho
              rw [hcfs''] at htail
              obtain ⟨p', hp'mem, hp'eq⟩ := List.mem_map.mp htail
              have hcRho : relErrorCounter fp 3 rho := by
                have ea : relErrorCounter fp 1 (1 + δs) := relErrorCounter_one_add fp hδs
                have eb : relErrorCounter fp 1 (1 + δm) := relErrorCounter_one_add fp hδm
                have ec : relErrorCounter fp 1 (1 + δa) := relErrorCounter_one_add fp hδa
                have eab := relErrorCounter_mul fp 1 1 _ _ ea eb
                have eabc := relErrorCounter_mul fp 2 1 _ _ eab ec
                simpa [hrho, show (2 + 1) = 3 from rfl] using eabc
              have hc' : relErrorCounter fp (3 * alphas.length) p'.2 := hcnt' p' hp'mem
              have hmul := relErrorCounter_mul fp (3 * alphas.length) 3 p'.2 rho hc' hcRho
              have : p.2 = p'.2 * rho := by rw [← hp'eq]
              rw [this]
              simpa [show 3 * alphas.length + 3 = 3 * alphas.length + 3 from rfl] using hmul
          · -- values agree
            rw [hstepval, ← htailval]
            show c * (1 + δa) + (x - alpha) * ch5newton_pert x cfs'' alphas =
              ch5newton_pert x ((c, 1 + δa) :: cfs'') (alpha :: alphas)
            simp [ch5newton_pert]

/-- **Higham, 2nd ed., Section 5.3, backward error of the Newton form
(`<3n>`-type).** The rounded generalized-Horner evaluation of the Newton form is
the exact value of a polynomial whose divided differences `c_i` are perturbed by
factors `phi_i` with `|phi_i - 1| <= gamma_{3n}` (`n = alphas.length`). -/
theorem ch5newton_backward_error (fp : FPModel) (x : ℝ)
    (cs alphas : List ℝ) (hlen : alphas.length + 1 = cs.length)
    (hγ : gammaValid fp (3 * alphas.length)) :
    ∃ cfs : List (ℝ × ℝ),
      cfs.map Prod.fst = cs ∧
      (∀ p ∈ cfs, |p.2 - 1| ≤ gamma fp (3 * alphas.length)) ∧
      ch5newton_fleval fp x cs alphas = ch5newton_pert x cfs alphas := by
  obtain ⟨cfs, hmap, hcnt, heq⟩ := ch5newton_fleval_eq_pert fp x cs alphas hlen
  refine ⟨cfs, hmap, ?_, heq⟩
  intro p hp
  exact relErrorCounter_abs_sub_one_le_gamma fp (3 * alphas.length) p.2 (hcnt p hp) hγ

/-- **Higham, 2nd ed., Section 5.3, closing forward bound ("cf. (5.2)").**
For the rounded generalized-Horner evaluation of the Newton form with `n` nodes,
`|p(x) - q0hat| <= gamma_{3n} * sum_i |c_i| prod_{j<i} |x - alpha_j|`. -/
theorem ch5newton_forward_error_bound (fp : FPModel) (x : ℝ)
    (cs alphas : List ℝ) (hlen : alphas.length + 1 = cs.length)
    (hγ : gammaValid fp (3 * alphas.length)) :
    |newtonFormNested x cs alphas - ch5newton_fleval fp x cs alphas| ≤
      gamma fp (3 * alphas.length) * ch5newton_absMaj x cs alphas := by
  obtain ⟨cfs, hmap, hbound, heq⟩ :=
    ch5newton_backward_error fp x cs alphas hlen hγ
  have hηnn : 0 ≤ gamma fp (3 * alphas.length) := gamma_nonneg fp hγ
  have hforward :=
    ch5newton_pert_sub_exact_le x (gamma fp (3 * alphas.length)) hηnn cfs alphas hbound
  rw [hmap] at hforward
  rw [heq, abs_sub_comm]
  exact hforward

/-! ###########################################################################
    PART (ii): sharpness of the data-rounding scale preceding (5.12).
    ########################################################################### -/

/-- **Higham, 2nd ed., Section 5.3, p. 100, data-rounding sharpness.**

For a fixed output coordinate `i`, componentwise relative perturbations
`f_j ↦ f_j * (1 + δ_j)`, `|δ_j| ≤ u`, can attain exactly the row majorant
`u * ∑ j, |L i j| * |f j|`.  The quantifier over `δ` is inside the quantifier
over `i`: the source's componentwise phrase "as large as" does not assert that
one common perturbation simultaneously attains every output coordinate.

This is a source-facing specialization of `matMul_forward_bound_sharp_B`; no
new sharpness argument is assumed. -/
theorem ch5newton_data_rounding_error_componentwise_sharp
    {n : ℕ} (u : ℝ) (hu : 0 ≤ u)
    (L : Fin n → Fin n → ℝ) (f : Fin n → ℝ) (i : Fin n) :
    ∃ delta : Fin n → ℝ,
      (∀ j, |delta j| ≤ u) ∧
      |(∑ j : Fin n, L i j * (f j * (1 + delta j))) -
          ∑ j : Fin n, L i j * f j| =
        u * ∑ j : Fin n, |L i j| * |f j| := by
  let fColumn : Fin n → Fin 1 → ℝ := fun j _ => f j
  obtain ⟨DeltaF, hDeltaF, hsharp⟩ :=
    matMul_forward_bound_sharp_B u hu L fColumn i (0 : Fin 1)
  let delta : Fin n → ℝ := fun j =>
    if f j = 0 then 0 else DeltaF j (0 : Fin 1) / f j
  have hdelta : ∀ j, |delta j| ≤ u := by
    intro j
    by_cases hfj : f j = 0
    · simp [delta, hfj, hu]
    · simp only [delta, if_neg hfj, abs_div]
      apply (div_le_iff₀ (abs_pos.mpr hfj)).2
      simpa [fColumn] using hDeltaF j (0 : Fin 1)
  have hrelative : ∀ j, f j * (1 + delta j) = f j + DeltaF j (0 : Fin 1) := by
    intro j
    by_cases hfj : f j = 0
    · have hDeltaZero : DeltaF j (0 : Fin 1) = 0 := by
        have hbound := hDeltaF j (0 : Fin 1)
        simp [fColumn, hfj] at hbound
        exact hbound
      simp [delta, hfj, hDeltaZero]
    · simp only [delta, if_neg hfj]
      field_simp [hfj]
  refine ⟨delta, hdelta, ?_⟩
  simpa only [fColumn, hrelative] using hsharp

/-! ###########################################################################
    PART (iii): monotone-node-ordering corollary of (5.11)/(5.12).
    ###########################################################################

We prove the no-cancellation identity `|L_{n-1}| ... |L_0| = |L|` for strictly
increasing nodes, in the divided-difference `L`-action framework of
`Horner.lean`, and derive the "very satisfactory" bounds. -/

/-- Sign-alternating scaling `(S v)_i = (-1)^i v_i`. -/
noncomputable def ch5newton_signFlip {n : ℕ} (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => (-1 : ℝ) ^ (i.val) * v i

theorem ch5newton_neg_one_sq (a : ℕ) : (-1 : ℝ) ^ a * (-1) ^ a = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨a, by ring⟩

/-- Sign conjugation by `(-1)^a` on both sides is the identity. -/
theorem ch5newton_conj_self (a : ℕ) (t : ℝ) :
    (-1 : ℝ) ^ a * t * (-1) ^ a = t := by
  calc (-1 : ℝ) ^ a * t * (-1) ^ a = ((-1 : ℝ) ^ a * (-1) ^ a) * t := by ring
    _ = t := by rw [ch5newton_neg_one_sq]; ring

/-- Sign conjugation by `(-1)^a` and `(-1)^(a-1)` flips the sign (`a >= 1`). -/
theorem ch5newton_conj_pred (a : ℕ) (ha : 1 ≤ a) (t : ℝ) :
    (-1 : ℝ) ^ a * t * (-1) ^ (a - 1) = -t := by
  have hodd : (-1 : ℝ) ^ a * (-1 : ℝ) ^ (a - 1) = -1 := by
    rw [← pow_add]
    have hsum : a + (a - 1) = 2 * a - 1 := by omega
    rw [hsum]
    exact Odd.neg_one_pow ⟨a - 1, by omega⟩
  calc (-1 : ℝ) ^ a * t * (-1) ^ (a - 1)
      = ((-1 : ℝ) ^ a * (-1) ^ (a - 1)) * t := by ring
    _ = -t := by rw [hodd]; ring

/-- Entrywise no-cancellation identity for one bidiagonal factor `L_k` with
strictly increasing nodes: `|(L_k)_{ij}| = (-1)^i (L_k)_{ij} (-1)^j`. -/
theorem ch5newton_abs_LMatrix_entry
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n k : ℕ) (i j : Fin (n + 1)) :
    |dividedDifferenceLMatrix nodes n k i j| =
      (-1 : ℝ) ^ (i.val) * dividedDifferenceLMatrix nodes n k i j *
        (-1 : ℝ) ^ (j.val) := by
  by_cases hi : i.val ≤ k
  · -- diagonal copy row
    simp only [dividedDifferenceLMatrix, hi, dif_pos]
    by_cases hji : j = i
    · subst hji
      simp [ch5newton_neg_one_sq]
    · simp [hji]
  · -- active row: two nonzero entries with opposite structural sign
    have hgt : k < i.val := Nat.lt_of_not_ge hi
    have hi1 : 1 ≤ i.val := Nat.one_le_of_lt hgt
    have hden_pos : 0 < nodes i.val - nodes (i.val - k - 1) := by
      have hlt : i.val - k - 1 < i.val := by omega
      have := hinc (i.val - k - 1) i.val hlt
      linarith
    have hden_inv_pos : 0 < 1 / (nodes i.val - nodes (i.val - k - 1)) :=
      one_div_pos.mpr hden_pos
    have hne : i ≠ dividedDifferenceFinPred i := by
      intro h
      have : i.val = i.val - 1 := congrArg Fin.val h
      omega
    have hjine : j = i → j ≠ dividedDifferenceFinPred i := by
      intro h; rw [h]; exact hne
    have hpredval : (dividedDifferenceFinPred i).val = i.val - 1 := rfl
    simp only [dividedDifferenceLMatrix, hi, dif_neg, not_false_iff]
    by_cases hji : j = i
    · rw [if_pos hji, if_neg (hjine hji), add_zero, hji,
        abs_of_pos hden_inv_pos, ch5newton_conj_self]
    · by_cases hjp : j = dividedDifferenceFinPred i
      · rw [if_neg hji, if_pos hjp, zero_add, abs_neg,
          abs_of_pos hden_inv_pos, hjp, hpredval,
          ch5newton_conj_pred i.val hi1]
        ring
      · rw [if_neg hji, if_neg hjp]
        simp

/-- No-cancellation identity for one factor, on vectors: applying `|L_k|`
equals the sign-flip conjugate of `L_k` (strictly increasing nodes). -/
theorem ch5newton_absLMatrixAction_eq_signFlip
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n k : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    dividedDifferenceAbsLMatrixAction nodes n k v i =
      (-1 : ℝ) ^ (i.val) *
        dividedDifferenceLMatrixAction nodes n k (ch5newton_signFlip v) i := by
  unfold dividedDifferenceAbsLMatrixAction dividedDifferenceLMatrixAction
    ch5newton_signFlip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ch5newton_abs_LMatrix_entry nodes hinc n k i j]
  ring

/-- **No cancellation in the factored form (vector version).**  For strictly
increasing nodes, `|L_{m-1}| ... |L_0| = S (L_{m-1} ... L_0) S` where
`S = diag((-1)^i)`; i.e. the product of absolute factors equals the sign-flip
conjugate of the exact product. -/
theorem ch5newton_absLProduct_eq_signFlip
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n m : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    dividedDifferenceAbsLProductAction nodes 0 n m v i =
      (-1 : ℝ) ^ (i.val) *
        dividedDifferenceLProductAction nodes n m (ch5newton_signFlip v) i := by
  induction m generalizing i with
  | zero =>
      simp only [dividedDifferenceAbsLProductAction, dividedDifferenceLProductAction,
        ch5newton_signFlip]
      rw [← mul_assoc, ch5newton_neg_one_sq, one_mul]
  | succ m ih =>
      -- unfold one abs factor
      have hstep :
          dividedDifferenceAbsLProductAction nodes 0 n (m + 1) v i =
            dividedDifferenceAbsLMatrixAction nodes n m
              (dividedDifferenceAbsLProductAction nodes 0 n m v) i := by
        simp [dividedDifferenceAbsLProductAction]
      rw [hstep,
        ch5newton_absLMatrixAction_eq_signFlip nodes hinc n m
          (dividedDifferenceAbsLProductAction nodes 0 n m v) i]
      -- signFlip of the abs product is the exact product on signFlip v
      have hpush :
          ch5newton_signFlip
              (dividedDifferenceAbsLProductAction nodes 0 n m v) =
            dividedDifferenceLProductAction nodes n m (ch5newton_signFlip v) := by
        funext j
        rw [ch5newton_signFlip, ih j]
        have : (-1 : ℝ) ^ (j.val) * ((-1 : ℝ) ^ (j.val) *
            dividedDifferenceLProductAction nodes n m (ch5newton_signFlip v) j) =
            ((-1 : ℝ) ^ (j.val) * (-1 : ℝ) ^ (j.val)) *
              dividedDifferenceLProductAction nodes n m (ch5newton_signFlip v) j := by
          ring
        rw [this, ch5newton_neg_one_sq, one_mul]
      rw [hpush]
      simp [dividedDifferenceLProductAction]

/-- Linearity (scalar multiple) of the exact single `L_k` action. -/
theorem ch5newton_LMatrixAction_smul
    (nodes : ℕ → ℝ) (n k : ℕ) (a : ℝ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    dividedDifferenceLMatrixAction nodes n k (fun j => a * v j) i =
      a * dividedDifferenceLMatrixAction nodes n k v i := by
  unfold dividedDifferenceLMatrixAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _; ring

/-- Linearity (scalar multiple) of the exact `L`-product action. -/
theorem ch5newton_LProduct_smul
    (nodes : ℕ → ℝ) (n m : ℕ) (a : ℝ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    dividedDifferenceLProductAction nodes n m (fun j => a * v j) i =
      a * dividedDifferenceLProductAction nodes n m v i := by
  induction m generalizing i with
  | zero => simp [dividedDifferenceLProductAction]
  | succ m ih =>
      simp only [dividedDifferenceLProductAction_succ]
      have hfun :
          dividedDifferenceLProductAction nodes n m (fun j => a * v j) =
            fun j => a * dividedDifferenceLProductAction nodes n m v j := by
        funext j; exact ih j
      rw [hfun, ch5newton_LMatrixAction_smul]

/-- Standard basis vector `e_j`. -/
noncomputable def ch5newton_basis {n : ℕ} (j : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun l => if l = j then 1 else 0

/-- **Higham (5.11), monotone corollary — the matrix identity
`|L_{n-1}| ... |L_0| = |L|`.**  For strictly increasing nodes, entry `(i,j)` of
the product of absolute factors equals the absolute value of entry `(i,j)` of the
exact product `L = L_{m-1} ... L_0`.  (Tested on the standard basis, so this is
the full entrywise statement.) -/
theorem ch5newton_absLProduct_entry_eq_abs
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n m : ℕ) (i j : Fin (n + 1)) :
    dividedDifferenceAbsLProductAction nodes 0 n m (ch5newton_basis j) i =
      |dividedDifferenceLProductAction nodes n m (ch5newton_basis j) i| := by
  -- the abs-product entry is nonnegative
  have hnonneg :
      0 ≤ dividedDifferenceAbsLProductAction nodes 0 n m (ch5newton_basis j) i :=
    dividedDifferenceAbsLProductAction_nonneg nodes (le_refl 0) n m
      (ch5newton_basis j)
      (fun l => by unfold ch5newton_basis; positivity) i
  -- signFlip of a basis vector is the basis vector rescaled by (-1)^j
  have hsf : ch5newton_signFlip (ch5newton_basis j) =
      fun l => ((-1 : ℝ) ^ (j.val)) * ch5newton_basis j l := by
    funext l
    unfold ch5newton_signFlip ch5newton_basis
    by_cases hlj : l = j
    · subst hlj; simp
    · simp [hlj]
  have hval :
      dividedDifferenceAbsLProductAction nodes 0 n m (ch5newton_basis j) i =
        (-1 : ℝ) ^ (i.val) * ((-1 : ℝ) ^ (j.val) *
          dividedDifferenceLProductAction nodes n m (ch5newton_basis j) i) := by
    rw [ch5newton_absLProduct_eq_signFlip nodes hinc n m (ch5newton_basis j) i,
      hsf, ch5newton_LProduct_smul]
  -- so the entry equals +/- (exact entry); nonnegativity forces the absolute value
  set L := dividedDifferenceLProductAction nodes n m (ch5newton_basis j) i with hL
  set P := dividedDifferenceAbsLProductAction nodes 0 n m (ch5newton_basis j) i with hP
  have hval' : P = (-1 : ℝ) ^ (i.val) * (-1 : ℝ) ^ (j.val) * L := by
    rw [hval]; ring
  rcases Int.even_or_odd (i.val + j.val) with hev | hodd
  · -- sign +1
    have hsign : (-1 : ℝ) ^ (i.val) * (-1 : ℝ) ^ (j.val) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow (by exact_mod_cast hev)
    rw [hsign, one_mul] at hval'
    rw [hval']
    rw [hval'] at hnonneg
    exact (abs_of_nonneg hnonneg).symm
  · -- sign -1
    have hsign : (-1 : ℝ) ^ (i.val) * (-1 : ℝ) ^ (j.val) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow (by exact_mod_cast hodd)
    rw [hsign] at hval'
    have hLval : L = -P := by rw [hval']; ring
    rw [hLval, abs_neg]
    exact (abs_of_nonneg hnonneg).symm

/-- `1 + gamma_3 = (1 - 3u)^{-1}` (the "very satisfactory" constant base). -/
theorem ch5newton_one_add_gamma3 (fp : FPModel) (hγ : gammaValid fp 3) :
    1 + gamma fp 3 = (1 - 3 * fp.u)⁻¹ := by
  have h3u : (3 : ℝ) * fp.u < 1 := by
    unfold gammaValid at hγ; push_cast at hγ; linarith
  have hden : 1 - 3 * fp.u ≠ 0 := by linarith
  unfold gamma
  push_cast
  field_simp
  ring

/-- **Higham (5.11), the "very satisfactory bound" for strictly increasing
nodes.**  The computed divided-difference column differs from the exact one by
at most `((1-3u)^{-m} - 1)` times the *exact* divided-difference matrix `|L|`
applied entrywise to `|f|` (`m = n` factors), with no product-of-absolute-factor
overestimate. -/
theorem ch5newton_dividedDifference_verySatisfactory
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
          dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        (((1 - 3 * fp.u) ^ m)⁻¹ - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
  intro i
  -- den ≠ 0 from strict monotonicity
  have hden : ∀ k j, k < j → j < n + 1 → nodes j - nodes (j - k - 1) ≠ 0 := by
    intro k j hkj hjn
    have hlt : j - k - 1 < j := by omega
    have := hinc (j - k - 1) j hlt
    intro hzero; linarith
  -- gap bound from the existing (5.10)-(5.11) analysis
  have hgap :=
    fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3
      fp nodes f m hden hdenHat hγ i
  -- pull the common (1 + gamma_3)^m factor out of the perturbed abs-product
  have hconst :=
    dividedDifferenceAbsLProductAction_const_gamma nodes (gamma fp 3) n m
      (fun i : Fin (n + 1) => |f i.val|) i
  rw [hconst] at hgap
  -- rewrite the geometric factor into (1 - 3u)^{-m}
  have hbase : 1 + gamma fp 3 = (1 - 3 * fp.u)⁻¹ :=
    ch5newton_one_add_gamma3 fp hγ
  have hpow : (1 + gamma fp 3) ^ m = ((1 - 3 * fp.u) ^ m)⁻¹ := by
    rw [hbase, inv_pow]
  have hgap' :
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
          dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
    calc
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
          dividedDifferenceFiniteCoeffs nodes f n m i|
          ≤ (1 + gamma fp 3) ^ m *
              dividedDifferenceAbsLProductAction nodes 0 n m
                (fun i : Fin (n + 1) => |f i.val|) i -
            dividedDifferenceAbsLProductAction nodes 0 n m
                (fun i : Fin (n + 1) => |f i.val|) i := hgap
      _ = ((1 + gamma fp 3) ^ m - 1) *
              dividedDifferenceAbsLProductAction nodes 0 n m
                (fun i : Fin (n + 1) => |f i.val|) i := by ring
  rw [hpow] at hgap'
  exact hgap'

/-! #### Residual bound (5.12) for strictly increasing nodes.

For increasing nodes each `L_k^{-1}` is entrywise nonnegative, so
`|L_0^{-1}| ... |L_{m-1}^{-1}| = L_0^{-1} ... L_{m-1}^{-1} = L^{-1}` and the
absolute majorant collapses to the exact inverse product. -/

/-- With strictly increasing nodes, the absolute inverse action `|L_k^{-1}|`
coincides with the exact inverse action `L_k^{-1}` (natural-index form). -/
theorem ch5newton_absLInvActionNat_eq
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (k : ℕ) (w : ℕ → ℝ) :
    ∀ j : ℕ, dividedDifferenceAbsLInvActionNat nodes k w j =
      dividedDifferenceLInvActionNat nodes k w j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      by_cases hle : j + 1 ≤ k
      · simp [dividedDifferenceAbsLInvActionNat, dividedDifferenceLInvActionNat, hle]
      · have hdennn : 0 ≤ nodes (j + 1) - nodes (j + 1 - k - 1) := by
          have hlt : j + 1 - k - 1 < j + 1 := by omega
          have := hinc (j + 1 - k - 1) (j + 1) hlt
          linarith
        simp only [dividedDifferenceAbsLInvActionNat, dividedDifferenceLInvActionNat,
          hle, if_false]
        rw [ih, abs_of_nonneg hdennn]

/-- Vector form: `|L_k^{-1}| = L_k^{-1}` under strictly increasing nodes. -/
theorem ch5newton_absLInvAction_eq
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n k : ℕ) (w : Fin (n + 1) → ℝ) :
    dividedDifferenceAbsLInvAction nodes n k w =
      dividedDifferenceLInvAction nodes n k w := by
  funext i
  unfold dividedDifferenceAbsLInvAction dividedDifferenceLInvAction
  exact ch5newton_absLInvActionNat_eq nodes hinc k _ i.val

/-- Product form: `|L_0^{-1}| ... |L_{m-1}^{-1}| = L_0^{-1} ... L_{m-1}^{-1}`. -/
theorem ch5newton_absLInvProduct_eq
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    (n m : ℕ) (v : Fin (n + 1) → ℝ) :
    dividedDifferenceAbsLInvProductAction nodes n m v =
      dividedDifferenceLInvProductAction nodes n m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
      simp only [dividedDifferenceAbsLInvProductAction,
        dividedDifferenceLInvProductAction]
      rw [ch5newton_absLInvAction_eq nodes hinc n m v, ih]

/-- **Higham (5.12), the "very satisfactory" residual bound for strictly
increasing nodes.**  If the data `f` is reconstructed from computed divided
differences `chat` by rounded inverse steps that are componentwise within
`gamma` of the exact `L_k^{-1}`, then the exact Newton reconstruction residual is
bounded by `((1+gamma)^m - 1)` times the *exact* inverse product `L^{-1}` applied
to `|chat|` — no product-of-absolute-factor overestimate. -/
theorem ch5newton_residual_verySatisfactory
    (nodes : ℕ → ℝ) (hinc : ∀ a b : ℕ, a < b → nodes a < nodes b)
    {n : ℕ} (m : ℕ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k (fun j => |v j|) i)
    (f chat : Fin (n + 1) → ℝ)
    (hf : f = dividedDifferencePerturbedLInvProductAction step m chat) :
    ∀ i : Fin (n + 1),
      |f i - dividedDifferenceLInvProductAction nodes n m chat i| ≤
        ((1 + gamma) ^ m - 1) *
          dividedDifferenceLInvProductAction nodes n m
            (fun j => |chat j|) i := by
  intro i
  have hbound :=
    dividedDifferenceResidual_error_bound nodes m hgamma step hstep f chat hf i
  rw [ch5newton_absLInvProduct_eq nodes hinc n m (fun j => |chat j|)] at hbound
  exact hbound

end NumStability
