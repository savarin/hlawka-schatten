/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Transferring Hlawka inequalities through gap comparisons

This file isolates the last, purely ordered-algebraic step in the
Bregman--Mazur proof of the dimension-independent Schatten Hlawka bound.
If the three-body gap for one size functional is bounded above by the gap
for a model functional, while every two-body gap is bounded below by the
corresponding model gap, then a Hlawka inequality for the model transfers.
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
