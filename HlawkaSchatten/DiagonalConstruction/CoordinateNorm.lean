/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

@[expose] public section

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The finite coordinate `p`-norm, with a real exponent. -/
noncomputable def lpNorm (p : ℝ) (x : ι → E) : ℝ :=
  (∑ i, ‖x i‖ ^ p) ^ (1 / p)

end HlawkaSchatten.DiagonalConstruction
