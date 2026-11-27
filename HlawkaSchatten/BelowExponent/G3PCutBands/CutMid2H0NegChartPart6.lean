/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegChartPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegChartPart6Box : Box := ((((⟨![0, 9/100, 0, -1], ![9/68, 11/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H0NegChartPart6Tree : RatioChart :=
  .row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), 91625974997, 274877906944, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutMid2H0NegChartPart6_ok : CutMid2H0NegChartPart6Tree.ok CutMid2H0NegChartPart6Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
