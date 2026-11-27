/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegChartPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegChartPart4Box : Box := ((((⟨![9/68, 9/100, 0, -1], ![9/34, 11/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H1NegChartPart4Tree : RatioChart :=
  .cut 3 (0)
    (.row ⟨86531900008, 95281442641, (.direct 29635445272 31892807493), 91625974997, 274877906944, 2, .leaf .universal⟩)
    (.row ⟨86531900008, 95281442641, (.direct 88818297 163625445), 91625974997, 274877906944, 2, .leaf .universal⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegChartPart4_ok : CutMid2H1NegChartPart4Tree.geometryOK CutMid2H1NegPowerCache CutMid2H1NegChartPart4Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
