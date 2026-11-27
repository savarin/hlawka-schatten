/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegChartPart1Box : Box := (((((⟨![0, 17/100, 0, -1], ![9/136, 9/50, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H0NegChartPart1Tree : RatioChart :=
  .row ⟨117423580139, 120689819475, (.direct 1131165907 1515968947), 0, 10180665226, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutTop2H0NegChartPart1_ok : CutTop2H0NegChartPart1Tree.geometryOK CutTop2H0NegPowerCache CutTop2H0NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
