/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegChartPart24`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegChartPart24Box : Box := (((((⟨![9/136, 19/100, 0, -1], ![9/68, 1/5, 1, 1]⟩ : Box)).upperChild 3 (1/4)).lowerChild 3 (3/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H1NegChartPart24Tree : RatioChart :=
  .row ⟨123862991199, 126950446638, (.direct 105494030 125711707), 0, 10180665226, 543343016189/274877906944, .leaf (.midpoint ⟨627787276713, 44314362881, 131381647956, 464101405767, 140157054696, 293356865668⟩)⟩

set_option maxRecDepth 16000 in
theorem CutTop4H1NegChartPart24_ok : CutTop4H1NegChartPart24Tree.geometryOK CutTop4H1NegPowerCache CutTop4H1NegChartPart24Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
