/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

/-!
# The sharp cyclic Hlawka constant for diagonal Schatten norms (Challenge)

For every real exponent `p ≥ 256`, the sharp constant is the maximum of
an explicit one-parameter cyclic ratio. The bound holds in every finite
dimension and is sharp in each dimension at least three. All three diagonal
matrices may have different norms and arbitrary complex entries.

The Schatten norm below is defined using singular values of the diagonal
linear operator, matching the existence boundary. This statement concerns
diagonal matrices; it does not assert the bound for arbitrary operators.
-/

namespace PalomarHlawkaSchatten.ConstructionDiagonal

/-- The Schatten norm of the operator with diagonal `d`. -/
noncomputable def diagonalSchattenNorm {n : ℕ} (p : ℝ) (d : Fin n → ℂ) : ℝ :=
  let T := Matrix.toEuclideanLin (Matrix.diagonal d)
  (∑ i ∈ T.singularValues.support, (T.singularValues i) ^ p) ^ (1 / p)

/-- The three-body triangle deficit. -/
def tripleGap {E : Type*} [Add E] (N : E → ℝ) (x y z : E) : ℝ :=
  N x + N y + N z - N (x + y + z)

/-- The sum of the three pair deficits. -/
def pairGapSum {E : Type*} [Add E] (N : E → ℝ) (x y z : E) : ℝ :=
  (N x + N y - N (x + y)) + (N x + N z - N (x + z)) +
    (N y + N z - N (y + z))

/-- A Hlawka constant for one size function. -/
def HasHlawkaConstant {E : Type*} [Add E] (N : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap N x y z ≤ C * pairGapSum N x y z

/-- The common singleton norm in the cyclic family. -/
noncomputable def cyclicA (p t : ℝ) : ℝ := (t ^ p + 2) ^ (1 / p)

/-- The common pair-sum norm in the cyclic family. -/
noncomputable def cyclicB (p t : ℝ) : ℝ :=
  (2 * |1 - t| ^ p + (2 : ℝ) ^ p) ^ (1 / p)

/-- The ratio of triple deficit to pair-deficit sum for the cyclic family. -/
noncomputable def cyclicRatio (p t : ℝ) : ℝ :=
  (3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t|) /
    (6 * cyclicA p t - 3 * cyclicB p t)

/-- The cyclic constant, specified by an explicit compact interval. -/
noncomputable def cyclicConstant (p : ℝ) : ℝ :=
  sSup (cyclicRatio p '' Set.Icc (1 / 2) 2)

/-- The explicit cyclic constant is admissible in every finite dimension. -/
theorem diagonal_hlawka_bound :
    ∀ p : ℝ, 256 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (diagonalSchattenNorm (n := n) p) (cyclicConstant p) := by
  sorry

/-- Every dimension at least three requires at least the cyclic constant. -/
theorem diagonal_hlawka_sharp :
    ∀ p : ℝ, 256 ≤ p → ∀ n : ℕ, 3 ≤ n → ∀ C : ℝ,
      HasHlawkaConstant (diagonalSchattenNorm (n := n) p) C → cyclicConstant p ≤ C := by
  sorry

/-- An actual cyclic parameter attains the constant on the stated interval. -/
theorem cyclic_maximum_attained :
    ∀ p : ℝ, 256 ≤ p →
      ∃ t ∈ Set.Icc (1 / 2 : ℝ) 2, cyclicRatio p t = cyclicConstant p := by
  sorry

end PalomarHlawkaSchatten.ConstructionDiagonal
