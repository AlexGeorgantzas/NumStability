/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.AlternatingDirections.ExactExecution
import NumStability.Source.Higham.Chapter26.CubicRoots.DepressedCubic
import NumStability.Source.Higham.Chapter26.CubicRoots.MonicCubic
import NumStability.Source.Higham.Chapter26.Equation01
import NumStability.Source.Higham.Chapter26.Equation02
import NumStability.Source.Higham.Chapter26.Equation03
import NumStability.Source.Higham.Chapter26.Equation04
import NumStability.Source.Higham.Chapter26.Equation05.CardanoRoots
import NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches
import NumStability.Source.Higham.Chapter26.Equation05.RealBranches
import NumStability.Source.Higham.Chapter26.Equation05.ZeroBranchDiscrepancy
import NumStability.Source.Higham.Chapter26.Equation06
import NumStability.Source.Higham.Chapter26.Equation07
import NumStability.Source.Higham.Chapter26.Equation08
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.DependencyExamples
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.DirectedRounding
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Execution
import NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Simplex

/-! # Compatibility import for Higham Chapter 26

Deprecated import path for the original Chapter 26 core. The canonical
declarations now live below `NumStability.Source.Higham.Chapter26`.

This wrapper deliberately excludes the crude-search and initial-simplex
producer leaves that were never exposed by this historical module.
-/
