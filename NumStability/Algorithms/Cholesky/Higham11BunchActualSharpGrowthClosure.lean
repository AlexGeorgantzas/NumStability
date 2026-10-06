import NumStability.Algorithms.Cholesky.Higham11BunchExactTrace
import NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix

/-!
# Algorithm 11.1 actual-trace adapter for Bunch's sharp growth comparison

`Higham11ExactBunchTrace.toSharpBlocks` extracts every analytic block field
from the literal complete-search, symmetric-permutation, and Schur recursion
of Algorithm 11.1.  In particular, neither determinant acceptance nor local
growth is supplied by a caller.

The one remaining imported mathematical fact is isolated in
`Higham11BunchCertifiedExecution.wholeBlockSegmentHadamard`: every nonempty
*contiguous list of complete pivot blocks* satisfies the determinant identity
followed by Hadamard's inequality.  This is a finite structural witness about
pivot-block determinants.  It is not a stage-ratio, element-growth, or sharp
comparison premise.
-/

namespace NumStability

open Higham11BunchSharpBlockCertificate

namespace Higham11ExactBunchTrace

/-- The analytic block produced by a literal one-by-one Algorithm 11.1 step. -/
noncomputable def oneSharpBlock {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (p q r : Fin (n + 1))
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.one) :
    Higham11BunchSharpBlock where
  width := 1
  stageMax := |A p q|
  detAbs := |A r r|
  width_one_or_two := Or.inl rfl
  stageMax_pos := hmaxPos
  detAbs_pos := by
    have hα : 0 < higham11_1_bunchParlettAlpha := by
      simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
    exact lt_of_lt_of_le (mul_pos hα hmaxPos)
      (one_pivot_lower A p q r hchoice)
  one_det_lower := by
    intro _
    exact one_pivot_lower A p q r hchoice
  two_det_lower := by omega

/-- The analytic block produced by a literal two-by-two Algorithm 11.1 step. -/
noncomputable def twoSharpBlock {n : ℕ}
    (A : Higham11BunchMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (p q r : Fin (n + 2))
    (hentry : ∀ i j, |A i j| ≤ |A p q|)
    (hdiag : ∀ i, |A i i| ≤ |A r r|)
    (hmaxPos : 0 < |A p q|)
    (hchoice : higham11_1_BunchParlettCompletePivotChoice
      higham11_1_bunchParlettAlpha |A p q| |A r r| PivotSize.two) :
    Higham11BunchSharpBlock where
  width := 2
  stageMax := |A p q|
  detAbs := |A p p * A q q - A p q ^ 2|
  width_one_or_two := Or.inr rfl
  stageMax_pos := hmaxPos
  detAbs_pos := two_pivot_pos A hA p q r hentry hdiag hmaxPos hchoice
  one_det_lower := by omega
  two_det_lower := by
    intro _
    exact two_pivot_lower A hA p q r hentry hdiag hchoice

/-- Elimination-order analytic blocks extracted from the actual dependent
trace.  Width-two pivots remain atomic. -/
noncomputable def toSharpBlocks :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      Higham11ExactBunchTrace A → List Higham11BunchSharpBlock
  | _, _, .nil _ => []
  | _, _, .one A _ p q r _ _ hmaxPos hchoice tail =>
      oneSharpBlock A p q r hmaxPos hchoice :: toSharpBlocks tail
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail =>
      twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice ::
        toSharpBlocks tail

@[simp] theorem toSharpBlocks_totalWidth :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      (trace : Higham11ExactBunchTrace A) →
        totalWidth trace.toSharpBlocks = n
  | _, _, .nil _ => by simp [toSharpBlocks, totalWidth]
  | _, _, .one A hA p q r hentry hdiag hmaxPos hchoice tail => by
      change 1 + totalWidth tail.toSharpBlocks = _
      rw [toSharpBlocks_totalWidth tail]
      omega
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail => by
      change 2 + totalWidth tail.toSharpBlocks = _
      rw [toSharpBlocks_totalWidth tail]
      omega

/-- The executor's stage history is exactly the stage-maximum projection of
the extracted sharp blocks. -/
@[simp] theorem stageMaxes_eq_map_stageMax :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      (trace : Higham11ExactBunchTrace A) →
        trace.stageMaxes = trace.toSharpBlocks.map (·.stageMax)
  | _, _, .nil _ => by simp [stageMaxes, toSharpBlocks]
  | _, _, .one A hA p q r hentry hdiag hmaxPos hchoice tail => by
      simp [stageMaxes, toSharpBlocks, oneSharpBlock,
        stageMaxes_eq_map_stageMax tail]
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail => by
      simp [stageMaxes, toSharpBlocks, twoSharpBlock,
        stageMaxes_eq_map_stageMax tail]

/-- Every positive-order actual trace has a positive original complete-search
maximum. -/
theorem firstMax_toSharpBlocks_pos {n : ℕ} {A : Higham11BunchMatrix n}
    (trace : Higham11ExactBunchTrace A) (hn : 0 < n) :
    0 < firstMax trace.toSharpBlocks := by
  cases trace with
  | nil A => omega
  | one A hA p q r hentry hdiag hmaxPos hchoice tail =>
      simpa [toSharpBlocks, oneSharpBlock, firstMax] using hmaxPos
  | two A hA p q r hentry hdiag hmaxPos hchoice tail =>
      simpa [toSharpBlocks, twoSharpBlock, firstMax] using hmaxPos

/-- The first complete-search maximum is exactly the source max-entry norm. -/
theorem firstMax_toSharpBlocks_eq_maxEntryNorm {n : ℕ}
    {A : Higham11BunchMatrix n} (trace : Higham11ExactBunchTrace A)
    (hn : 0 < n) :
    firstMax trace.toSharpBlocks =
      maxEntryNorm hn (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  cases trace with
  | nil A => omega
  | one A hA p q r hentry hdiag hmaxPos hchoice tail =>
      have hlo : |A p q| ≤
          maxEntryNorm hn (Matrix.of A : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ) := by
        simpa using entry_le_maxEntryNorm hn
          (Matrix.of A : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ) p q
      have hup : maxEntryNorm hn
          (Matrix.of A : Matrix (Fin (_ + 1)) (Fin (_ + 1)) ℝ) ≤ |A p q| := by
        apply maxEntryNorm_le_of_entry_le_bound hn _ _
        intro i j
        simpa using hentry i j
      simpa [toSharpBlocks, oneSharpBlock, firstMax] using le_antisymm hlo hup
  | two A hA p q r hentry hdiag hmaxPos hchoice tail =>
      have hlo : |A p q| ≤
          maxEntryNorm hn (Matrix.of A : Matrix (Fin (_ + 2)) (Fin (_ + 2)) ℝ) := by
        simpa using entry_le_maxEntryNorm hn
          (Matrix.of A : Matrix (Fin (_ + 2)) (Fin (_ + 2)) ℝ) p q
      have hup : maxEntryNorm hn
          (Matrix.of A : Matrix (Fin (_ + 2)) (Fin (_ + 2)) ℝ) ≤ |A p q| := by
        apply maxEntryNorm_le_of_entry_le_bound hn _ _
        intro i j
        simpa using hentry i j
      simpa [toSharpBlocks, twoSharpBlock, firstMax] using le_antisymm hlo hup

/-- The adjacent-boundary relation required by the analytic block
certificate. -/
def SharpAdjacent (b next : Higham11BunchSharpBlock) : Prop :=
  next.stageMax ≤
    higham11_1_bunchLocalGrowthFactor ^ b.width * b.stageMax

/-- All adjacent local-growth facts are consequences of the literal Schur
steps in the exact trace. -/
theorem toSharpBlocks_isChain {n : ℕ} {A : Higham11BunchMatrix n}
    (trace : Higham11ExactBunchTrace A) :
    List.IsChain SharpAdjacent trace.toSharpBlocks := by
  induction trace with
  | nil A => exact .nil
  | one A hA p q r hentry hdiag hmaxPos hchoice tail ih =>
      cases tail with
      | nil B => exact .singleton _
      | one B hB p' q' r' hentry' hdiag' hmaxPos' hchoice' tail' =>
          apply List.IsChain.cons_cons
          · unfold SharpAdjacent
            have hlocal := one_schur_entry_bound A p q r hentry hmaxPos hchoice p' q'
            simpa [toSharpBlocks, oneSharpBlock,
              higham11_1_bunchLocalGrowthFactor] using hlocal
          · simpa [toSharpBlocks] using ih
      | two B hB p' q' r' hentry' hdiag' hmaxPos' hchoice' tail' =>
          apply List.IsChain.cons_cons
          · unfold SharpAdjacent
            have hlocal := one_schur_entry_bound A p q r hentry hmaxPos hchoice p' q'
            simpa [toSharpBlocks, oneSharpBlock, twoSharpBlock,
              higham11_1_bunchLocalGrowthFactor] using hlocal
          · simpa [toSharpBlocks] using ih
  | two A hA p q r hentry hdiag hmaxPos hchoice tail ih =>
      cases tail with
      | nil B => exact .singleton _
      | one B hB p' q' r' hentry' hdiag' hmaxPos' hchoice' tail' =>
          apply List.IsChain.cons_cons
          · unfold SharpAdjacent
            have hlocal := two_schur_entry_bound A hA p q r hentry hdiag
              hmaxPos hchoice p' q'
            simpa [toSharpBlocks, oneSharpBlock, twoSharpBlock,
              higham11_1_bunchLocalGrowthFactor] using hlocal
          · simpa [toSharpBlocks] using ih
      | two B hB p' q' r' hentry' hdiag' hmaxPos' hchoice' tail' =>
          apply List.IsChain.cons_cons
          · unfold SharpAdjacent
            have hlocal := two_schur_entry_bound A hA p q r hentry hdiag
              hmaxPos hchoice p' q'
            simpa [toSharpBlocks, twoSharpBlock,
              higham11_1_bunchLocalGrowthFactor] using hlocal
          · simpa [toSharpBlocks] using ih

end Higham11ExactBunchTrace

open Higham11ExactBunchTrace

/-- The exact determinant-product/Hadamard statement for one nonempty list of
whole pivot blocks. -/
def Higham11WholeBlockHadamard
    (blocks : List Higham11BunchSharpBlock) : Prop :=
  detProduct blocks ≤
    Real.sqrt (((totalWidth blocks : ℕ) : ℝ) ^ totalWidth blocks) *
      firstMax blocks ^ totalWidth blocks

/-- An actual Algorithm 11.1 execution plus the one structural identity not
yet derived from the executor: determinant/Hadamard for every nonempty
contiguous whole-block segment.  There is deliberately no growth or ratio
field. -/
structure Higham11BunchCertifiedExecution {n : ℕ}
    (A : Higham11BunchMatrix n) where
  trace : Higham11ExactBunchTrace A
  wholeBlockSegmentHadamard :
    ∀ segment : List Higham11BunchSharpBlock,
      segment ≠ [] → segment <:+: trace.toSharpBlocks →
        Higham11WholeBlockHadamard segment

/-- A reached boundary is represented by the nonempty elimination prefix
ending at that boundary.  It adds no mathematical assumption to the certified
execution. -/
structure Higham11BunchCertifiedExecution.ReachedPrefix {n : ℕ}
    {A : Higham11BunchMatrix n} (exec : Higham11BunchCertifiedExecution A) where
  blocks : List Higham11BunchSharpBlock
  nonempty : blocks ≠ []
  isPrefix : blocks <+: exec.trace.toSharpBlocks

/-- Build the analytic certificate from trace-derived adjacency plus structural
Hadamard facts on whole-block infixes. -/
theorem higham11_1_bunchSharpBlockCertificate_of_chain_and_hadamard :
    ∀ {blocks : List Higham11BunchSharpBlock},
      blocks ≠ [] →
      List.IsChain Higham11ExactBunchTrace.SharpAdjacent blocks →
      (∀ segment : List Higham11BunchSharpBlock,
        segment ≠ [] → segment <:+: blocks →
          Higham11WholeBlockHadamard segment) →
      Higham11BunchSharpBlockCertificate blocks
  | [], hnonempty, _, _ => False.elim (hnonempty rfl)
  | [b], _, _, hhad => by
      apply Higham11BunchSharpBlockCertificate.singleton b
      have h := hhad [b] (by simp) (by rfl)
      simpa [Higham11WholeBlockHadamard, detProduct, totalWidth,
        firstMax] using h
  | b :: next :: rest, _, hchain, hhad => by
      rw [List.isChain_cons_cons] at hchain
      rcases hchain with ⟨hloc, htail⟩
      apply Higham11BunchSharpBlockCertificate.cons b next rest
      · apply higham11_1_bunchSharpBlockCertificate_of_chain_and_hadamard
          (blocks := next :: rest) (by simp) htail
        intro segment hsegment hinfix
        apply hhad segment hsegment
        exact hinfix.trans ⟨[b], [], by simp⟩
      · exact hloc
      · have h := hhad (b :: next :: rest) (by simp) (by rfl)
        simpa [Higham11WholeBlockHadamard, detProduct, totalWidth,
          firstMax] using h

namespace Higham11BunchCertifiedExecution

/-- A reached prefix inherits the exact trace's adjacent local-growth chain. -/
theorem ReachedPrefix.isChain {n : ℕ} {A : Higham11BunchMatrix n}
    {exec : Higham11BunchCertifiedExecution A}
    (pref : exec.ReachedPrefix) :
    List.IsChain Higham11ExactBunchTrace.SharpAdjacent pref.blocks := by
  apply (Higham11ExactBunchTrace.toSharpBlocks_isChain exec.trace).infix
  rcases pref.isPrefix with ⟨after, hafter⟩
  exact ⟨[], after, by simpa using hafter⟩

/-- Every reached prefix has the analytic block certificate; its determinant
facts and local growth come from the exact trace, while the execution's sole
extra field supplies only structural whole-block Hadamard. -/
theorem ReachedPrefix.toSharpBlockCertificate {n : ℕ}
    {A : Higham11BunchMatrix n} {exec : Higham11BunchCertifiedExecution A}
    (pref : exec.ReachedPrefix) :
    Higham11BunchSharpBlockCertificate pref.blocks := by
  apply higham11_1_bunchSharpBlockCertificate_of_chain_and_hadamard
    pref.nonempty pref.isChain
  intro segment hsegment hinfix
  apply exec.wholeBlockSegmentHadamard segment hsegment
  rcases pref.isPrefix with ⟨after, hafter⟩
  rcases hinfix with ⟨before, after', hinfix⟩
  refine ⟨before, after' ++ after, ?_⟩
  rw [← hafter, ← hinfix]
  simp [List.append_assoc]

/-- A reached prefix never contains more scalar dimensions than the original
matrix order. -/
theorem ReachedPrefix.totalWidth_le_order {n : ℕ}
    {A : Higham11BunchMatrix n} {exec : Higham11BunchCertifiedExecution A}
    (pref : exec.ReachedPrefix) : totalWidth pref.blocks ≤ n := by
  have hfull := Higham11ExactBunchTrace.toSharpBlocks_totalWidth exec.trace
  rcases pref.isPrefix with ⟨after, hafter⟩
  rw [← hafter] at hfull
  simp only [totalWidth, List.map_append, List.sum_append] at hfull ⊢
  omega

end Higham11BunchCertifiedExecution

/-- The printed sharp scalar bound is monotone once its literal source domain
`2 ≤ n` is respected. -/
theorem higham11_1_bunchSharpGrowthBound_le_of_le {k n : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    higham11_1_bunchSharpGrowthBound k ≤
      higham11_1_bunchSharpGrowthBound n := by
  have hsub : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hkn 1
  have hsubR : ((k - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hrpow :
      Real.rpow ((k - 1 : ℕ) : ℝ) ((223 : ℝ) / 500) ≤
        Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hsubR (by norm_num)
  have hmult : higham11_1_bunchSharpGrowthMultiplier k ≤
      higham11_1_bunchSharpGrowthMultiplier n := by
    unfold higham11_1_bunchSharpGrowthMultiplier
    exact mul_le_mul_of_nonneg_left hrpow (by norm_num)
  have hW := higham9_14_completePivotWilkinsonBound_le_of_le hkn
  have hmultN : 0 ≤ higham11_1_bunchSharpGrowthMultiplier n := by
    unfold higham11_1_bunchSharpGrowthMultiplier
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hW0 : 0 ≤ higham9_14_completePivotWilkinsonBound k :=
    le_of_lt (higham9_14_completePivotWilkinsonBound_pos (by omega))
  unfold higham11_1_bunchSharpGrowthBound
  exact mul_le_mul hmult hW hW0 hmultN

/-- On the source domain `2 ≤ n`, the printed bound dominates the unchanged
original stage (growth ratio one). -/
theorem higham11_1_one_le_bunchSharpGrowthBound {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) ≤ higham11_1_bunchSharpGrowthBound n := by
  have hmono := higham11_1_bunchSharpGrowthBound_le_of_le
    (k := 2) (n := n) (by omega) hn
  have htwo : (1 : ℝ) ≤ higham11_1_bunchSharpGrowthBound 2 := by
    unfold higham11_1_bunchSharpGrowthBound
    unfold higham11_1_bunchSharpGrowthMultiplier
    rw [show (2 - 1 : ℕ) = 1 by omega]
    norm_num [higham9_14_completePivotWilkinsonBound_two]
  exact htwo.trans hmono

/-- Every member of a block-stage history is the last boundary of some
nonempty prefix. -/
theorem higham11_1_exists_prefix_lastMax_eq_of_mem_stageMax :
    ∀ {blocks : List Higham11BunchSharpBlock} {mu : ℝ},
      mu ∈ blocks.map (·.stageMax) →
      ∃ reached : List Higham11BunchSharpBlock,
        reached ≠ [] ∧ reached <+: blocks ∧ lastMax reached = mu
  | [], _, h => by simp at h
  | b :: rest, mu, h => by
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with hhead | htail
      · refine ⟨[b], by simp, ?_, ?_⟩
        · exact ⟨rest, by simp⟩
        · simpa [lastMax] using hhead.symm
      · obtain ⟨reached, hnonempty, hprefix, hlast⟩ :=
          higham11_1_exists_prefix_lastMax_eq_of_mem_stageMax htail
        rcases reached with _ | ⟨c, cs⟩
        · exact False.elim (hnonempty rfl)
        · refine ⟨b :: c :: cs, by simp, ?_, ?_⟩
          · rcases hprefix with ⟨after, hafter⟩
            exact ⟨after, by simpa [List.append_assoc] using congrArg (b :: ·) hafter⟩
          · simpa [lastMax] using hlast

namespace Higham11BunchCertifiedExecution

/-- A nonempty prefix has the same first maximum as the full actual history. -/
theorem ReachedPrefix.firstMax_eq_full {n : ℕ}
    {A : Higham11BunchMatrix n} {exec : Higham11BunchCertifiedExecution A}
    (pref : exec.ReachedPrefix) :
    firstMax pref.blocks = firstMax exec.trace.toSharpBlocks := by
  obtain ⟨b, rest, hblocks⟩ := List.exists_cons_of_ne_nil pref.nonempty
  rcases pref.isPrefix with ⟨after, hafter⟩
  rw [hblocks, ← hafter]
  simp [hblocks, firstMax]

/-- Conditional adapter endpoint.  The name records exactly what remains
caller-supplied here: only structural whole-block Hadamard.  A downstream
trace-minor theorem can construct the certified execution internally and
thereby remove this condition. -/
theorem ReachedPrefix.stageMax_le_original_bound_of_structural_hadamard
    {n : ℕ} {A : Higham11BunchMatrix n}
    {exec : Higham11BunchCertifiedExecution A} (hn : 2 ≤ n)
    (pref : exec.ReachedPrefix) :
    lastMax pref.blocks ≤
      higham11_1_bunchSharpGrowthBound n * firstMax pref.blocks := by
  obtain ⟨b, rest, hblocks⟩ := List.exists_cons_of_ne_nil pref.nonempty
  cases rest with
  | nil =>
      rw [hblocks]
      simp only [lastMax, firstMax]
      exact le_mul_of_one_le_left (le_of_lt b.stageMax_pos)
        (higham11_1_one_le_bunchSharpGrowthBound hn)
  | cons next rest =>
      have cert := pref.toSharpBlockCertificate
      have hk : 2 ≤ totalWidth pref.blocks := by
        rw [hblocks]
        simp only [totalWidth, List.map_cons, List.sum_cons]
        have hb := b.width_pos
        have hnext := next.width_pos
        omega
      have hprefix := higham11_1_bunchSharpGrowth_stageMax_le_bound_mul
        hk cert rfl
      have hmono := higham11_1_bunchSharpGrowthBound_le_of_le hk
        pref.totalWidth_le_order
      exact hprefix.trans (mul_le_mul_of_nonneg_right hmono
        (le_of_lt (Higham11BunchSharpBlockCertificate.firstMax_pos cert)))

/-- All actual reduced-stage maxima, including the original stage, satisfy the
source comparison after monotone lifting from their reached prefix width to
the original order.  This theorem remains explicitly conditional only through
the certified execution's structural Hadamard field. -/
theorem all_stageMax_le_original_bound_of_structural_hadamard
    {n : ℕ} {A : Higham11BunchMatrix n}
    (exec : Higham11BunchCertifiedExecution A) (hn : 2 ≤ n) :
    ∀ mu ∈ exec.trace.stageMaxes,
      mu ≤ higham11_1_bunchSharpGrowthBound n *
        firstMax exec.trace.toSharpBlocks := by
  intro mu hmu
  have hmap : mu ∈ exec.trace.toSharpBlocks.map (·.stageMax) := by
    simpa [Higham11ExactBunchTrace.stageMaxes_eq_map_stageMax] using hmu
  obtain ⟨blocks, hnonempty, hprefix, hlast⟩ :=
    higham11_1_exists_prefix_lastMax_eq_of_mem_stageMax hmap
  let pref : exec.ReachedPrefix :=
    { blocks := blocks, nonempty := hnonempty, isPrefix := hprefix }
  have hbound := pref.stageMax_le_original_bound_of_structural_hadamard hn
  rw [hlast, pref.firstMax_eq_full] at hbound
  exact hbound

/-- Ratio form matching Higham's definition of element growth. -/
theorem all_stageRatio_le_original_bound_of_structural_hadamard
    {n : ℕ} {A : Higham11BunchMatrix n}
    (exec : Higham11BunchCertifiedExecution A) (hn : 2 ≤ n) :
    ∀ mu ∈ exec.trace.stageMaxes,
      mu / firstMax exec.trace.toSharpBlocks ≤
        higham11_1_bunchSharpGrowthBound n := by
  intro mu hmu
  have hfirst := Higham11ExactBunchTrace.firstMax_toSharpBlocks_pos
    exec.trace (by omega)
  rw [div_le_iff₀ hfirst]
  exact exec.all_stageMax_le_original_bound_of_structural_hadamard hn mu hmu

/-- Source-shaped ratio form with the original matrix max-entry norm in the
denominator. -/
theorem all_stageRatio_le_maxEntryNorm_of_structural_hadamard
    {n : ℕ} {A : Higham11BunchMatrix n}
    (exec : Higham11BunchCertifiedExecution A) (hn : 2 ≤ n) :
    ∀ mu ∈ exec.trace.stageMaxes,
      mu / maxEntryNorm (by omega : 0 < n)
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
        higham11_1_bunchSharpGrowthBound n := by
  rw [← Higham11ExactBunchTrace.firstMax_toSharpBlocks_eq_maxEntryNorm
    exec.trace (by omega)]
  exact exec.all_stageRatio_le_original_bound_of_structural_hadamard hn

end Higham11BunchCertifiedExecution

end NumStability
