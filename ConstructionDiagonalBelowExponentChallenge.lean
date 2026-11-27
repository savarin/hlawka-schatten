/-
The finite coordinate norm and Hlawka deficit definitions are adapted from
Ezzeri Esa's HlawkaSchatten sources. Copyright (c) 2026 Ezzeri Esa.
Released under the Apache License 2.0. See LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Hlawka’s inequality below the critical exponent (Challenge)

For `2 ≤ p ≤ log 3 / log (3 / 2)` and every `n : ℕ`, let `N` be the coordinate
ℓₚ norm on `Fin n → ℝ`. For any three vectors, Hlawka’s inequality reads

`N (x + y) + N (x + z) + N (y + z) ≤ N x + N y + N z + N (x + y + z)`.

The statement `HasHlawkaConstant (lpNorm p) 1` expresses this inequality in
terms of the triple deficit and the three pair deficits. It includes both
endpoint exponents and dimension zero.
-/

@[expose] public section

namespace HlawkaSchatten

variable {E : Type*} [Add E]

/-- The triangle-inequality deficit of a size functional at two vectors. -/
def pairGap (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

/-- The triangle-inequality deficit of a size functional at three vectors. -/
def tripleGap (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

/-- The sum of all three pair deficits associated to a triple. -/
def pairGapSum (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

/-- A size functional satisfies the three-vector Hlawka inequality with constant `C`. -/
def HasHlawkaConstant (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z

end HlawkaSchatten

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The finite coordinate `p`-norm, with a real exponent. -/
noncomputable def lpNorm (p : ℝ) (x : ι → E) : ℝ :=
  (∑ i, ‖x i‖ ^ p) ^ (1 / p)

end HlawkaSchatten.DiagonalConstruction

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.LpThreshold

/-- Constant one bounds the triple deficit by the sum of the three pair deficits
through the critical exponent, in every finite real dimension. -/
theorem hlawka_holds_below_exponent :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 := by
  sorry

end HlawkaSchatten.LpThreshold
