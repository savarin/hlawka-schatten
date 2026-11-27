/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid4H0Neg_gap : SignedBoxGap CutMid4H0NegRestBox false :=
  ratioUnion_signedGap (B := CutMid4H0NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    CutMid4H0NegChart_ok CutMid4H0NegRest_ok

end HlawkaSchatten.BelowExponent.G3P
