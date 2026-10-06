-- Algorithms/Ch5LejaProducer.lean
--
-- Higham, 2nd ed., Chapter 5, Section 5.3, p. 101: a genuine finite
-- producer for the Leja reordering, complementing the certificate-only API
-- in Horner.lean.

import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
import NumStability.Algorithms.Horner

namespace NumStability

open scoped BigOperators

/-! ## A finite argmax-and-erase producer -/

/-- The score maximized at one Leja selection step.  At the first step it is
`|x|`; subsequently it is the product of distances from the already selected
prefix. -/
noncomputable def ch5LejaListScore (chosen : List ℝ) (x : ℝ) : ℝ :=
  match chosen with
  | [] => |x|
  | _ => (chosen.map fun y => |x - y|).prod

/-- List-native certificate for an actual greedy Leja trace.  Unlike
`IsLejaGreedyTrace`, this predicate records the remaining candidates at every
stage, which lets the producer prove that each selected head is a maximizer. -/
def Ch5LejaListTrace : List ℝ → List ℝ → Prop
  | _, [] => True
  | chosen, x :: remaining =>
      (∀ y ∈ x :: remaining,
        ch5LejaListScore chosen y ≤ ch5LejaListScore chosen x) ∧
      Ch5LejaListTrace (chosen ++ [x]) remaining

/-- The finite-list argmax used by the producer. -/
noncomputable def ch5LejaListArgmax
    (chosen remaining : List ℝ) (hne : remaining ≠ []) : ℝ :=
  (remaining.argmax (ch5LejaListScore chosen)).get (by
    rw [Option.isSome_iff_ne_none]
    intro hnone
    exact hne (List.argmax_eq_none.mp hnone))

theorem ch5LejaListArgmax_mem_argmax
    (chosen remaining : List ℝ) (hne : remaining ≠ []) :
    ch5LejaListArgmax chosen remaining hne ∈
      remaining.argmax (ch5LejaListScore chosen) := by
  unfold ch5LejaListArgmax
  exact Option.get_mem _

theorem ch5LejaListArgmax_mem
    (chosen remaining : List ℝ) (hne : remaining ≠ []) :
    ch5LejaListArgmax chosen remaining hne ∈ remaining :=
  List.argmax_mem (ch5LejaListArgmax_mem_argmax chosen remaining hne)

theorem ch5LejaListArgmax_is_max
    (chosen remaining : List ℝ) (hne : remaining ≠ [])
    {y : ℝ} (hy : y ∈ remaining) :
    ch5LejaListScore chosen y ≤
      ch5LejaListScore chosen (ch5LejaListArgmax chosen remaining hne) :=
  List.le_of_mem_argmax hy
    (ch5LejaListArgmax_mem_argmax chosen remaining hne)

/-- Repeatedly move a finite-list argmax to the front and erase that occurrence
from the remaining list.  The prefix parameter is the already selected part;
the recursion is finite because each step erases one member. -/
noncomputable def ch5LejaGreedyAux
    (chosen remaining : List ℝ) : List ℝ :=
  if hne : remaining = [] then []
  else
    let x := ch5LejaListArgmax chosen remaining hne
    x :: ch5LejaGreedyAux (chosen ++ [x]) (remaining.erase x)
termination_by remaining.length
decreasing_by
  have hx := ch5LejaListArgmax_mem chosen remaining hne
  have hlen := List.length_erase_add_one hx
  omega

/-- The producer only reorders its remaining list; it neither drops nor
duplicates an input occurrence. -/
theorem ch5LejaGreedyAux_perm
    (chosen remaining : List ℝ) :
    (ch5LejaGreedyAux chosen remaining).Perm remaining := by
  rw [ch5LejaGreedyAux]
  split_ifs with hne
  · subst remaining
    simp
  · let x := ch5LejaListArgmax chosen remaining hne
    have hx : x ∈ remaining :=
      ch5LejaListArgmax_mem chosen remaining hne
    have ih := ch5LejaGreedyAux_perm
      (chosen ++ [x]) (remaining.erase x)
    exact (List.Perm.cons x ih).trans (List.perm_cons_erase hx).symm
termination_by remaining.length
decreasing_by
  have hx := ch5LejaListArgmax_mem chosen remaining hne
  have hlen := List.length_erase_add_one hx
  omega

/-- Every head emitted by the producer is a genuine argmax over the candidates
remaining at that stage. -/
theorem ch5LejaGreedyAux_isTrace
    (chosen remaining : List ℝ) :
    Ch5LejaListTrace chosen (ch5LejaGreedyAux chosen remaining) := by
  rw [ch5LejaGreedyAux]
  split_ifs with hne
  · simp [Ch5LejaListTrace]
  · let x := ch5LejaListArgmax chosen remaining hne
    have hx : x ∈ remaining :=
      ch5LejaListArgmax_mem chosen remaining hne
    have hperm := ch5LejaGreedyAux_perm
      (chosen ++ [x]) (remaining.erase x)
    have ih := ch5LejaGreedyAux_isTrace
      (chosen ++ [x]) (remaining.erase x)
    constructor
    · intro y hy
      apply ch5LejaListArgmax_is_max chosen remaining hne
      have hy' : y ∈ x :: ch5LejaGreedyAux
          (chosen ++ [x]) (remaining.erase x) := hy
      obtain rfl | hyTail := List.mem_cons.mp hy'
      · exact hx
      · exact List.mem_of_mem_erase ((hperm.mem_iff).mp hyTail)
    · exact ih
termination_by remaining.length
decreasing_by
  have hx := ch5LejaListArgmax_mem chosen remaining hne
  have hlen := List.length_erase_add_one hx
  omega

/-- The produced Leja reordering of a finite input list. -/
noncomputable def ch5LejaGreedyList (input : List ℝ) : List ℝ :=
  ch5LejaGreedyAux [] input

theorem ch5LejaGreedyList_perm (input : List ℝ) :
    (ch5LejaGreedyList input).Perm input :=
  ch5LejaGreedyAux_perm [] input

theorem ch5LejaGreedyList_isTrace (input : List ℝ) :
    Ch5LejaListTrace [] (ch5LejaGreedyList input) :=
  ch5LejaGreedyAux_isTrace [] input

/-! ## Bridge from the finite producer to the Chapter 5 API -/

/-- Dropping `j` selected values from a list trace leaves the corresponding
trace with those values appended to the already selected list. -/
theorem Ch5LejaListTrace.drop
    {chosen output : List ℝ} (htrace : Ch5LejaListTrace chosen output)
    (j : ℕ) :
    Ch5LejaListTrace (chosen ++ output.take j) (output.drop j) := by
  induction j generalizing chosen output with
  | zero => simpa using htrace
  | succ j ih =>
      cases output with
      | nil => simp [Ch5LejaListTrace]
      | cons x remaining =>
          have htail :
              Ch5LejaListTrace (chosen ++ [x]) remaining := htrace.2
          simpa [List.take, List.drop, List.append_assoc] using
            (ih htail)

/-- The natural-indexed node sequence associated with a finite output list.
Indices outside the list are sent to zero; source-facing uses stay inside the
proved finite range. -/
def ch5LejaNodesOfList (output : List ℝ) : ℕ → ℝ :=
  fun i => output.getD i 0

/-- The Chapter 5 prefix product is exactly the product of distances from the
finite list prefix. -/
theorem ch5LejaPrefixProduct_nodesOfList
    (output : List ℝ) (j i : ℕ) (hj : j ≤ output.length) :
    lejaPrefixProduct (ch5LejaNodesOfList output) j i =
      ((output.take j).map
        fun y => |ch5LejaNodesOfList output i - y|).prod := by
  induction j with
  | zero => simp [lejaPrefixProduct, ch5LejaNodesOfList]
  | succ j ih =>
      have hjlt : j < output.length := by omega
      rw [lejaPrefixProduct_succ, ih (by omega)]
      simp only [List.map_take]
      rw [List.prod_take_succ _ j (by simpa using hjlt)]
      simp only [List.getElem_map]
      simp only [ch5LejaNodesOfList,
        List.getD_eq_getElem output 0 hjlt]

/-- A list trace supplies the exact greedy maximum inequality at any selected
stage `j` and any later candidate position `i`. -/
theorem Ch5LejaListTrace.score_getD_le
    {output : List ℝ} (htrace : Ch5LejaListTrace [] output)
    {j i : ℕ} (hj : j < output.length) (hji : j ≤ i)
    (hi : i < output.length) :
    ch5LejaListScore (output.take j) (output.getD i 0) ≤
      ch5LejaListScore (output.take j) (output.getD j 0) := by
  have hdrop := htrace.drop j
  rw [List.drop_eq_getElem_cons hj] at hdrop
  have hiDrop : i - j < (output.drop j).length := by
    simp
    omega
  have hcandidate : output[i] ∈ output.drop j := by
    have hget : (output.drop j)[i - j] = output[i] := by
      simp only [List.getElem_drop]
      congr 1
      omega
    rw [← hget]
    exact List.getElem_mem _
  rw [List.drop_eq_getElem_cons hj] at hcandidate
  rw [List.getD_eq_getElem output 0 hi,
    List.getD_eq_getElem output 0 hj]
  exact hdrop.1 output[i] hcandidate

/-- For a nonempty selected prefix, the list-native score is the Chapter 5
prefix product. -/
theorem ch5LejaListScore_take_eq_prefixProduct
    (output : List ℝ) (j i : ℕ) (hjpos : 1 ≤ j)
    (hj : j ≤ output.length) :
    ch5LejaListScore (output.take j) (ch5LejaNodesOfList output i) =
      lejaPrefixProduct (ch5LejaNodesOfList output) j i := by
  have htake : output.take j ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  rw [ch5LejaPrefixProduct_nodesOfList output j i hj]
  cases hprefix : output.take j with
  | nil => exact (htake hprefix).elim
  | cons x xs => simp [ch5LejaListScore]

/-! ## Source-facing finite-vector producer -/

/-- Run the finite Leja producer on the `n + 1` entries of a source vector. -/
noncomputable def ch5LejaGreedyVectorList {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) : List ℝ :=
  ch5LejaGreedyList (List.ofFn nodes)

/-- The natural-indexed sequence obtained from the produced finite list.
Only indices `0, ..., n` occur in the Chapter 5 correctness contract. -/
noncomputable def ch5LejaGreedyVectorNodes {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  ch5LejaNodesOfList (ch5LejaGreedyVectorList nodes)

/-- The producer is a reordering of all and only the supplied `n + 1`
entries, including multiplicities. -/
theorem ch5LejaGreedyVectorList_perm {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) :
    (ch5LejaGreedyVectorList nodes).Perm (List.ofFn nodes) := by
  exact ch5LejaGreedyList_perm (List.ofFn nodes)

theorem ch5LejaGreedyVectorList_length {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) :
    (ch5LejaGreedyVectorList nodes).length = n + 1 := by
  simpa using (ch5LejaGreedyVectorList_perm nodes).length_eq

/-- The actual finite producer satisfies the greedy trace contract used by
the Chapter 5 API.  Thus the previous certificate-only statement is now fed
by a construction from every finite input vector. -/
theorem ch5LejaGreedyVectorNodes_isTrace {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) :
    IsLejaGreedyTrace (ch5LejaGreedyVectorNodes nodes) n := by
  let output := ch5LejaGreedyVectorList nodes
  have hlen : output.length = n + 1 := by
    simpa [output] using ch5LejaGreedyVectorList_length nodes
  have htrace : Ch5LejaListTrace [] output := by
    simpa [output, ch5LejaGreedyVectorList] using
      ch5LejaGreedyList_isTrace (List.ofFn nodes)
  constructor
  · intro i hi
    have hzero : 0 < output.length := by omega
    have hi' : i < output.length := by omega
    have hscore := htrace.score_getD_le
      (j := 0) (i := i) hzero (Nat.zero_le i) hi'
    simpa [ch5LejaListScore, ch5LejaGreedyVectorNodes, output] using hscore
  · intro j hjpos hjn i hji hi
    have hj' : j < output.length := by omega
    have hi' : i < output.length := by omega
    have hscore := htrace.score_getD_le
      (j := j) (i := i) hj' hji hi'
    change ch5LejaListScore (output.take j)
        (ch5LejaNodesOfList output i) ≤
      ch5LejaListScore (output.take j)
        (ch5LejaNodesOfList output j) at hscore
    rw [ch5LejaListScore_take_eq_prefixProduct output j i hjpos (by omega),
      ch5LejaListScore_take_eq_prefixProduct output j j hjpos (by omega)]
      at hscore
    simpa [ch5LejaGreedyVectorNodes, output] using hscore

/-- Hence every output of the finite producer is a Leja ordering in the exact
sense of Higham's equations (5.13a,b). -/
theorem ch5LejaGreedyVectorNodes_isLejaOrdering {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) :
    IsLejaOrdering (ch5LejaGreedyVectorNodes nodes) n :=
  (ch5LejaGreedyVectorNodes_isTrace nodes).isLejaOrdering

/-- Source-facing producer theorem: every finite vector has an explicit
greedy Leja reordering, and that output preserves the input multiset. -/
theorem higham5_leja_greedy_producer_correct {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) :
    (ch5LejaGreedyVectorList nodes).Perm (List.ofFn nodes) ∧
      IsLejaGreedyTrace (ch5LejaGreedyVectorNodes nodes) n ∧
      IsLejaOrdering (ch5LejaGreedyVectorNodes nodes) n := by
  exact ⟨ch5LejaGreedyVectorList_perm nodes,
    ch5LejaGreedyVectorNodes_isTrace nodes,
    ch5LejaGreedyVectorNodes_isLejaOrdering nodes⟩

/-- The abstract arithmetic budget attached to the standard incremental Leja
selection scheme is exactly `n²`.  This theorem deliberately remains separate
from the functional list producer: it does not pretend that Lean's opaque
`List.argmax` implementation or evaluation strategy is a machine-cost model. -/
theorem higham5_leja_abstract_selection_budget_eq_square (n : ℕ) :
    lejaGreedyFlopCount n = n * n :=
  lejaGreedyFlopCount_eq_square n

end NumStability
