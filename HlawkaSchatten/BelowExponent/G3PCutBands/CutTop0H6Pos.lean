/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop0H6Pos_gap : SignedBoxGap CutTop0H6PosRestBox true :=
  ratioUnion_signedGap (B := CutTop0H6PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop0H6PosChart_ok CutTop0H6PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
