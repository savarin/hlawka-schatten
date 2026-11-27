/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegChartPart1Box : Box := (((((⟨![63/136, 9/50, 0, -1], ![9/17, 19/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H7NegChartPart1Tree : RatioChart :=
  .row ⟨120689819474, 123862991200, (.direct 363332043 1750263650), 0, 10180665226, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutTop3H7NegChartPart1_ok : CutTop3H7NegChartPart1Tree.geometryOK CutTop3H7NegPowerCache CutTop3H7NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
