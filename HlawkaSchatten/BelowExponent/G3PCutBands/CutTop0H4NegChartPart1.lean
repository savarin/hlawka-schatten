/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegChartPart1Box : Box := (((((⟨![9/34, 3/20, 0, -1], ![45/136, 4/25, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop0H4NegChartPart1Tree : RatioChart :=
  .cut 1 (31/200)
    (.row ⟨110576703734, 112330851340, (.direct 185928075 1511580360), 0, 10180665226, 2, .leaf .universal⟩)
    (.row ⟨112330851339, 114055813620, (.direct 163330013 1524517039), 0, 10180665226, 2, .leaf .universal⟩)

set_option maxRecDepth 16000 in
theorem CutTop0H4NegChartPart1_ok : CutTop0H4NegChartPart1Tree.geometryOK CutTop0H4NegPowerCache CutTop0H4NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
