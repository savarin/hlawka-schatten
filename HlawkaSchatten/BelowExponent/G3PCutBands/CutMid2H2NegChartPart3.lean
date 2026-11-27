/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegChartPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegChartPart3Box : Box := ((((⟨![9/34, 9/100, 0, -1], ![27/68, 11/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H2NegChartPart3Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨86531900008, 95281442641, (.direct 28727966924 32120847313), 91625974997, 274877906944, 469664387077/274877906944, .leaf (.secant 815046710230 342509872 34922204517 10180561190)⟩)
      (.row ⟨86531900008, 95281442641, (.direct 8791281420 11423770202), 91625974997, 274877906944, 521673418371/274877906944, .leaf (.secant 735220963489 12143197460 63582830215 0)⟩))
    (.row ⟨86531900008, 95281442641, (.direct 269127805 209078691), 91625974997, 274877906944, 251730100063/137438953472, .leaf (.midpoint ⟨658473599885, 33437899883, 84214525667, 636287527261, 126320955114, 328044729802⟩)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H2NegChartPart3_ok : CutMid2H2NegChartPart3Tree.ok CutMid2H2NegChartPart3Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
