/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegChartPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegChartPart3Box : Box := ((((⟨![9/34, 7/100, 0, -1], ![27/68, 9/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid1H2NegChartPart3Tree : RatioChart :=
  .row ⟨76698504228, 86531900009, (.direct 29146044007 31888375423), 91625974997, 274877906944, 2, .leaf .universal⟩

set_option maxRecDepth 16000 in
theorem CutMid1H2NegChartPart3_ok : CutMid1H2NegChartPart3Tree.ok CutMid1H2NegChartPart3Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
