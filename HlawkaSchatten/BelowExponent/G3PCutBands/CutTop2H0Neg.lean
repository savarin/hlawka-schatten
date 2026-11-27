/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PGeometryCheckSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop2H0Neg_gap : SignedBoxGap CutTop2H0NegRestBox false :=
  ratioUnion_signedGap (B := CutTop2H0NegRestBox) false
    (by norm_num : (0 : ℚ) ≤ 1)
    (RatioChart.ok_of_geometryOK CutTop2H0NegPowerCache_valid CutTop2H0NegChart_ok)
    (RatioRemainder.ok_of_geometryOK CutTop2H0NegPowerCache_valid CutTop2H0NegRest_ok)

end HlawkaSchatten.BelowExponent.G3P
