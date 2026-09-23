/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction

/-! # The sharp cyclic Hlawka constant for diagonal Schatten norms (Solution) -/

namespace PalomarHlawkaSchatten.ConstructionDiagonal

/-- The Schatten norm of the operator with diagonal `d`. -/
noncomputable def diagonalSchattenNorm {n : ℕ} (p : ℝ) (d : Fin n → ℂ) : ℝ :=
  let T := Matrix.toEuclideanLin (Matrix.diagonal d)
  (∑ i ∈ T.singularValues.support, (T.singularValues i) ^ p) ^ (1 / p)

/-- The pair deficit: `N(x) + N(y) - N(x + y)`. -/
def pairGap {E : Type*} [Add E] (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

/-- The triple deficit: `N(x) + N(y) + N(z) - N(x + y + z)`. -/
def tripleGap {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

/-- Sum of the three pair deficits. -/
def pairGapSum {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

/-- `C` is a Hlawka constant for `size` if the triple deficit never exceeds
`C` times the sum of pair deficits. -/
def HasHlawkaConstant {E : Type*} [Add E] (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z

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

private theorem diagonalSchattenNorm_eq_lpNorm {p : ℝ} (hp : 0 < p)
    {n : ℕ} (d : Fin n → ℂ) :
    diagonalSchattenNorm p d = HlawkaSchatten.DiagonalConstruction.lpNorm p d :=
  HlawkaSchatten.DiagonalConstruction.schattenPNorm_diagonal hp d

theorem diagonal_hlawka_bound :
    ∀ p : ℝ, 256 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (diagonalSchattenNorm (n := n) p) (cyclicConstant p) := by
  intro p hp n
  have he : diagonalSchattenNorm (n := n) p = HlawkaSchatten.DiagonalConstruction.lpNorm p :=
    funext (diagonalSchattenNorm_eq_lpNorm (by linarith : 0 < p))
  rw [he]
  exact HlawkaSchatten.DiagonalConstruction.complex_hlawka_bound hp

theorem diagonal_hlawka_sharp :
    ∀ p : ℝ, 256 ≤ p → ∀ n : ℕ, 3 ≤ n → ∀ C : ℝ,
      HasHlawkaConstant (diagonalSchattenNorm (n := n) p) C → cyclicConstant p ≤ C := by
  intro p hp n hn C hC
  have he : diagonalSchattenNorm (n := n) p = HlawkaSchatten.DiagonalConstruction.lpNorm p :=
    funext (diagonalSchattenNorm_eq_lpNorm (by linarith : 0 < p))
  rw [he] at hC
  exact HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_of_complex_constant
    (by linarith : 1 < p) hn hC

theorem cyclic_maximum_attained :
    ∀ p : ℝ, 256 ≤ p →
      ∃ t ∈ Set.Icc (1 / 2 : ℝ) 2, cyclicRatio p t = cyclicConstant p := by
  intro p hp
  exact HlawkaSchatten.DiagonalConstruction.cyclic_maximum_attained (by linarith : 1 < p)

end PalomarHlawkaSchatten.ConstructionDiagonal
