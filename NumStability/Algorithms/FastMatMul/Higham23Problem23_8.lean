/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.FastMatMul.Internal.LegacyBounds
import NumStability.Source.Higham.Chapter23.BalancedScaling
import NumStability.Source.Higham.Chapter23.BilinearAlgorithm
import NumStability.Source.Higham.Chapter23.BlockAlgorithms
import NumStability.Source.Higham.Chapter23.ConventionalMultiplication
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.GammaAsymptotics
import NumStability.Source.Higham.Chapter23.Problem08
import NumStability.Source.Higham.Chapter23.Theorem02
import NumStability.Source.Higham.Chapter23.Theorem03.Execution
import NumStability.Source.Higham.Chapter23.ThreeM
import NumStability.Source.Higham.Chapter23.WinogradInnerProduct

/-!
# Historical Problem 23.8 import

Compatibility wrapper preserving the former recursive-inversion import surface.
-/
