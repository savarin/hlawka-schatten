/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PGeometryCheckSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid0H3Neg_gap : SignedBoxGap CutMid0H3NegRestBox false :=
  ratioUnion_signedGap (B := CutMid0H3NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    (RatioChart.ok_of_geometryOK CutMid0H3NegPowerCache_valid CutMid0H3NegChart_ok)
    (RatioRemainder.ok_of_geometryOK CutMid0H3NegPowerCache_valid CutMid0H3NegRest_ok)

end HlawkaSchatten.BelowExponent.G3P
