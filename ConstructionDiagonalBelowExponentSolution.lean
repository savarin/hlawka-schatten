/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent

/-!
# Hlawka’s inequality below the critical exponent (Solution)

The selected theorem restates the Challenge. The definitions it uses are the library's own, from
`HlawkaSchatten.GapComparison.Defs` and `HlawkaSchatten.DiagonalConstruction.CoordinateNorm`, which
the Challenge copies word for word. Its proof is the library theorem
`HlawkaSchatten.BelowExponent.hlawka_holds_below_exponent`.
-/

@[expose] public section

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.LpThreshold

/-- Constant one bounds the triple deficit by the sum of the three pair deficits
through the critical exponent, in every finite real dimension. -/
theorem hlawka_holds_below_exponent :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 :=
  HlawkaSchatten.BelowExponent.hlawka_holds_below_exponent

end HlawkaSchatten.LpThreshold
