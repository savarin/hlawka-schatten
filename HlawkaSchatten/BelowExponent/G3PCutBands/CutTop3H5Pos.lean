/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioSound
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5PosChart
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5PosRest

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem CutTop3H5Pos_gap : SignedBoxGap CutTop3H5PosRestBox true :=
  ratioUnion_signedGap (B := CutTop3H5PosRestBox) true
    (by norm_num : (0 : ℚ) ≤ 1)
    CutTop3H5PosChart_ok CutTop3H5PosRest_ok

end HlawkaSchatten.BelowExponent.G3P
