/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutMid3H2Pos_gap : SignedBoxGap CutMid3H2PosRestBox true :=
  ratioUnion_signedGap (B := CutMid3H2PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutMid3H2PosChart_ok CutMid3H2PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
