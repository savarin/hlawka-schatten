/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid3H0Neg_gap : SignedBoxGap CutMid3H0NegRestBox false :=
  ratioUnion_signedGap (B := CutMid3H0NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    CutMid3H0NegChart_ok CutMid3H0NegRest_ok

end HlawkaSchatten.BelowExponent.G3P
