/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop1H7Neg_gap : SignedBoxGap CutTop1H7NegRestBox false :=
  ratioUnion_signedGap (B := CutTop1H7NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop1H7NegChart_ok CutTop1H7NegRest_ok

end HlawkaSchatten.BelowExponent.G3P
