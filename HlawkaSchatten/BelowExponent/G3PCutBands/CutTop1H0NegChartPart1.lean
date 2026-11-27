/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegChartPart1Box : Box := (((((⟨![0, 4/25, 0, -1], ![9/136, 17/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H0NegChartPart1Tree : RatioChart :=
  .cut 3 (0)
    (.row ⟨114055813619, 117423580140, (.direct 1131165907 1491435954), 0, 10180665226, 537816322705/274877906944, .leaf (.secant 993888389401 30541785600 3715346965 0)⟩)
    (.row ⟨114055813619, 117423580140, (.direct 0 85963629), 0, 10180665226, 2, .leaf .universal⟩)

set_option maxRecDepth 16000 in
theorem CutTop1H0NegChartPart1_ok : CutTop1H0NegChartPart1Tree.geometryOK CutTop1H0NegPowerCache CutTop1H0NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
