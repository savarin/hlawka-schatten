/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegChartPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegChartPart3Box : Box := ((((⟨![27/68, 9/100, 0, -1], ![9/17, 11/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H3NegChartPart3Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨86531900008, 95281442641, (.direct 27819613156 32352396262), 91625974997, 274877906944, 115784861893/68719476736, .leaf (.secant 730620357551 13171657058 65459142127 10180561190)⟩)
      (.cut 0 (63/136)
        (.row ⟨86531900008, 95281442641, (.direct 8112700559 11146643386), 91625974997, 274877906944, 484812700997/274877906944, .leaf (.secant 654056799327 34921981117 81179804332 0)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 7777859674 11237464090), 91625974997, 274877906944, 472226872869/274877906944, .leaf (.secant 614802087393 49313657404 100314348286 0)⟩)))
    (.row ⟨86531900008, 95281442641, (.direct 516914045 259169283), 91625974997, 274877906944, 114867271037/68719476736, .leaf (.midpoint ⟨580667489242, 63582541603, 106756363911, 537735758958, 160133808481, 308872718761⟩)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H3NegChartPart3_ok : CutMid2H3NegChartPart3Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegChartPart3Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
