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
import NumStability.Source.Higham.Chapter23.BiniLotti
import NumStability.Source.Higham.Chapter23.BlockAlgorithms
import NumStability.Source.Higham.Chapter23.ConventionalMultiplication
import NumStability.Source.Higham.Chapter23.Equation11
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.GammaAsymptotics
import NumStability.Source.Higham.Chapter23.Theorem02
import NumStability.Source.Higham.Chapter23.Theorem03
import NumStability.Source.Higham.Chapter23.ThreeM
import NumStability.Source.Higham.Chapter23.ThreeMStrassen
import NumStability.Source.Higham.Chapter23.WinogradInnerProduct

/-!
# Historical 3M--Strassen Chapter 23 import

Compatibility wrapper preserving the former combined 3M--Strassen import surface.
-/
