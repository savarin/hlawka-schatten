/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegChartPart1Box : Box := (((((⟨![9/136, 4/25, 0, -1], ![9/68, 17/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H1NegChartPart1Tree : RatioChart :=
  .row ⟨114055813619, 117423580140, (.direct 826817689 1518046096), 0, 10180665226, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutTop1H1NegChartPart1_ok : CutTop1H1NegChartPart1Tree.geometryOK CutTop1H1NegPowerCache CutTop1H1NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
