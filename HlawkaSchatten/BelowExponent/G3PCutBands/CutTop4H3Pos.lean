/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop4H3Pos_gap : SignedBoxGap CutTop4H3PosRestBox true :=
  ratioUnion_signedGap (B := CutTop4H3PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop4H3PosChart_ok CutTop4H3PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
