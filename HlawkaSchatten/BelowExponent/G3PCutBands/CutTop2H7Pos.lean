/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop2H7Pos_gap : SignedBoxGap CutTop2H7PosRestBox true :=
  ratioUnion_signedGap (B := CutTop2H7PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop2H7PosChart_ok CutTop2H7PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
