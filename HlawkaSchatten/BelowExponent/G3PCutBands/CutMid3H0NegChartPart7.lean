/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegChartPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegChartPart7Box : Box := ((((⟨![0, 11/100, 0, -1], ![9/68, 13/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H0NegChartPart7Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), 91625974997, 274877906944, 25351008853/17179869184, .leaf (.secant 993888389401 30541785600 114172333 10180561190)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 10180561190 11239342526), 91625974997, 274877906944, 133256811115/68719476736, .leaf (.secant 907805998772 10180561190 11146040162 0)⟩))
    (.cut 3 (1/8)
      (.row ⟨95281442640, 103236350716, (.direct 0 162890367), 91625974997, 274877906944, 2, .leaf .universal⟩)
      (.row ⟨95281442640, 103236350716, (.direct 3393509060 2591613356), 91625974997, 274877906944, 263796304309/137438953472, .leaf (.midpoint ⟨744454106434, 10180561190, 81445321801, 651562574406, 81444489524, 364190815654⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegChartPart7_ok : CutMid3H0NegChartPart7Tree.ok CutMid3H0NegChartPart7Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
