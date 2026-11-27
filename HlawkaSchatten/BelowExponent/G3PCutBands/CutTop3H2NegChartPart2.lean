/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegChartPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegChartPart2Box : Box := ((((((((⟨![9/68, 9/50, 0, -1], ![27/136, 19/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H2NegChartPart2Tree : RatioChart :=
  .cut 3 (-3/16)
    (.cut 2 (7/32)
      (.row ⟨120689819474, 123862991200, (.direct 1817518237 3360146759), 10180665226, 24716235638, 175188272623/137438953472, .leaf (.secant 902832344944 9247859247 217099539 19358451269)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 3690525515 5562304562), 24716235638, 43500686443, 175188272623/137438953472, .leaf (.secant 902832344944 9247859247 217099539 19358451269)⟩))
    (.cut 0 (45/272)
      (.cut 2 (7/32)
        (.row ⟨120689819474, 123862991200, (.direct 966448411 2028386746), 10180665226, 24716235638, 94461032865/68719476736, .leaf (.secant 860965232671 2782876251 1702189485 10180561190)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 2095369057 3408494692), 24716235638, 43500686443, 94461032865/68719476736, .leaf (.secant 860965232671 2782876251 1702189485 10180561190)⟩))
      (.cut 2 (7/32)
        (.row ⟨120689819474, 123862991200, (.direct 797389844 2043330137), 10180665226, 24716235638, 390059373239/274877906944, .leaf (.secant 839098591179 651286364 4390594002 10180561190)⟩)
        (.cut 3 (-5/32)
          (.row ⟨120689819474, 123862991200, (.direct 1871430078 3426254384), 24716235638, 43500686443, 355385979529/274877906944, .leaf (.secant 839098591179 651286364 1826441846 14500097491)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 1233545383 2625521644), 24716235638, 43500686443, 190036712715/137438953472, .leaf (.secant 818638020075 162610877 4390594002 10180561190)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H2NegChartPart2_ok : CutTop3H2NegChartPart2Tree.geometryOK CutTop3H2NegPowerCache CutTop3H2NegChartPart2Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
