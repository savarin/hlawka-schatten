/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegChartPart1Box : Box := (((((⟨![9/68, 9/50, 0, -1], ![27/136, 19/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H2NegChartPart1Tree : RatioChart :=
  .row ⟨120689819474, 123862991200, (.direct 488619470 1597765324), 0, 10180665226, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutTop3H2NegChartPart1_ok : CutTop3H2NegChartPart1Tree.ok CutTop3H2NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
