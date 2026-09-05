/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.HilbertHlawka

/-!
# Gap comparison through a nonlinear Mazur map

The Mazur map is not additive, so the Hilbert model for a family
`x, y, z` must use sums of the three *images*, rather than the image of
`x + y + z`.  This file records that distinction in the interface used by
the variational proof and carries out the final ordered-algebraic transfer.
-/

namespace HlawkaSchatten

variable {E H : Type*} [Add E]
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Two-body deficit of a family after applying a possibly nonlinear map
into a normed additive group. -/
def mappedPairGap (size : E → ℝ) (map : E → H) (x y : E) : ℝ :=
  size x + size y - ‖map x + map y‖

/-- Three-body deficit of a family after applying a possibly nonlinear map
into a normed additive group. -/
def mappedTripleGap (size : E → ℝ) (map : E → H) (x y z : E) : ℝ :=
  size x + size y + size z - ‖map x + map y + map z‖

/-- Sum of the three two-body mapped deficits. -/
def mappedPairGapSum (size : E → ℝ) (map : E → H) (x y z : E) : ℝ :=
  mappedPairGap size map x y + mappedPairGap size map x z +
    mappedPairGap size map y z

include 𝕜

/-- If a nonlinear map preserves the size of each individual input, its
mapped deficits satisfy the Hilbert-space Hlawka inequality. -/
theorem mappedTripleGap_le_mappedPairGapSum
    (size : E → ℝ) (map : E → H)
    (hnorm : ∀ x, ‖map x‖ = size x) (x y z : E) :
    mappedTripleGap size map x y z ≤ mappedPairGapSum size map x y z := by
  have h := norm_pair_sums_le (𝕜 := 𝕜) (map x) (map y) (map z)
  rw [hnorm x, hnorm y, hnorm z] at h
  dsimp only [mappedTripleGap, mappedPairGapSum, mappedPairGap]
  linarith

/-- The final pointwise comparison step for a nonlinear Mazur model.
The factors of two cancel exactly, leaving the ratio `M / m`. -/
theorem tripleGap_le_ratio_mul_mappedPairGapSum
    (size : E → ℝ) (modelSize : E → ℝ) (map : E → H)
    (m M : ℝ) (x y z : E)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : tripleGap size x y z ≤
      2 * M * mappedTripleGap modelSize map x y z)
    (hPairXY : 2 * m * mappedPairGap modelSize map x y ≤ pairGap size x y)
    (hPairXZ : 2 * m * mappedPairGap modelSize map x z ≤ pairGap size x z)
    (hPairYZ : 2 * m * mappedPairGap modelSize map y z ≤ pairGap size y z)
    (hModel : mappedTripleGap modelSize map x y z ≤
      mappedPairGapSum modelSize map x y z) :
    tripleGap size x y z ≤ (M / m) * pairGapSum size x y z := by
  have hPair : 2 * m * mappedPairGapSum modelSize map x y z ≤
      pairGapSum size x y z := by
    dsimp only [mappedPairGapSum, pairGapSum]
    nlinarith
  have hRatio : 0 ≤ M / m := div_nonneg hM hm.le
  have hScaled := mul_le_mul_of_nonneg_left hPair hRatio
  have hCancel :
      (M / m) * (2 * m * mappedPairGapSum modelSize map x y z) =
        2 * M * mappedPairGapSum modelSize map x y z := by
    field_simp [ne_of_gt hm]
  rw [hCancel] at hScaled
  calc
    tripleGap size x y z ≤
        2 * M * mappedTripleGap modelSize map x y z := hTriple
    _ ≤ 2 * M * mappedPairGapSum modelSize map x y z :=
      mul_le_mul_of_nonneg_left hModel (mul_nonneg (by positivity) hM)
    _ ≤ (M / m) * pairGapSum size x y z := hScaled

/-- Global nonlinear-map transfer theorem.  This is the ordered-algebraic
target for the Schatten variational estimates: once the original deficits
are compared with the mapped Hilbert deficits, the Hlawka constant is
`M / m`. -/
theorem hasHlawkaConstant_of_mappedGapComparison
    (size : E → ℝ) (modelSize : E → ℝ) (map : E → H)
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hnorm : ∀ x, ‖map x‖ = modelSize x)
    (hTriple : ∀ x y z, tripleGap size x y z ≤
      2 * M * mappedTripleGap modelSize map x y z)
    (hPair : ∀ x y,
      2 * m * mappedPairGap modelSize map x y ≤ pairGap size x y) :
    HasHlawkaConstant size (M / m) := by
  intro x y z
  exact tripleGap_le_ratio_mul_mappedPairGapSum (𝕜 := 𝕜)
    size modelSize map m M x y z
    hm hM (hTriple x y z) (hPair x y) (hPair x z) (hPair y z)
    (mappedTripleGap_le_mappedPairGapSum (𝕜 := 𝕜) modelSize map hnorm x y z)

end HlawkaSchatten
