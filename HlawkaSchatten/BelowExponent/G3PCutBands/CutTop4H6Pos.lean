/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop4H6Pos_gap : SignedBoxGap CutTop4H6PosRestBox true :=
  ratioUnion_signedGap (B := CutTop4H6PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop4H6PosChart_ok CutTop4H6PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
