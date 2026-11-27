/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop2H3Neg_gap : SignedBoxGap CutTop2H3NegRestBox false :=
  ratioUnion_signedGap (B := CutTop2H3NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop2H3NegChart_ok CutTop2H3NegRest_ok

end HlawkaSchatten.BelowExponent.G3P
