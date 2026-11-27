/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid2H1Neg_gap : SignedBoxGap CutMid2H1NegRestBox false :=
  ratioUnion_signedGap (B := CutMid2H1NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    CutMid2H1NegChart_ok CutMid2H1NegRest_ok

end HlawkaSchatten.BelowExponent.G3P
