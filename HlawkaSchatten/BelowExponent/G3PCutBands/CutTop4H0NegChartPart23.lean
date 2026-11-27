/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegChartPart23`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegChartPart23Box : Box := (((((⟨![0, 19/100, 0, -1], ![9/136, 1/5, 1, 1]⟩ : Box)).upperChild 3 (1/4)).lowerChild 3 (3/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H0NegChartPart23Tree : RatioChart :=
  .row ⟨123862991199, 126950446638, (.direct 0 114172333), 0, 10180665226, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutTop4H0NegChartPart23_ok : CutTop4H0NegChartPart23Tree.ok CutTop4H0NegChartPart23Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
