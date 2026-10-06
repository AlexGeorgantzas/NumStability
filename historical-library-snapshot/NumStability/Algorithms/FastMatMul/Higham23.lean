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
import NumStability.Source.Higham.Chapter23.ThreeM
import NumStability.Source.Higham.Chapter23.WinogradInnerProduct

/-!
# Historical Higham Chapter 23 import

Compatibility wrapper for the former base Chapter 23 implementation. New code should import `NumStability.Source.Higham.Chapter23` or a specific canonical leaf.
-/
