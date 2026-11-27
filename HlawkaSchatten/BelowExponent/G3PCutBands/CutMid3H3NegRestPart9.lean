/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestPart9Box : Box := (((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H3NegRestPart9Tree : RatioRemainder :=
  .covered

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRestPart9_ok : CutMid3H3NegRestPart9Tree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
