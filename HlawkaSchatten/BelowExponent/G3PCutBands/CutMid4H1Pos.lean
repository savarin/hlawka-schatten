/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PGeometryCheckSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid4H1Pos_gap : SignedBoxGap CutMid4H1PosRestBox true :=
  ratioUnion_signedGap (B := CutMid4H1PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    (RatioChart.ok_of_geometryOK CutMid4H1PosPowerCache_valid CutMid4H1PosChart_ok)
    (RatioRemainder.ok_of_geometryOK CutMid4H1PosPowerCache_valid CutMid4H1PosRest_ok)

end HlawkaSchatten.BelowExponent.G3P
