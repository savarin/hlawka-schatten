/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegChartPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegChartPart9Box : Box := ((((((((⟨![9/68, 19/100, 0, -1], ![27/136, 1/5, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H2NegChartPart9Tree : RatioChart :=
  .cut 3 (-3/16)
    (.row ⟨123862991199, 126950446638, (.direct 8635731975 11131690197), 43500686443, 91625974997, 175188272623/137438953472, .leaf (.secant 902832344944 9247859247 217099539 19358451269)⟩)
    (.cut 0 (45/272)
      (.cut 3 (-5/32)
        (.row ⟨123862991199, 126950446638, (.direct 5116450815 6908687510), 43500686443, 91625974997, 171214529777/137438953472, .leaf (.secant 860965232671 2782876251 162614625 14500097491)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 3623189082 5251333624), 43500686443, 91625974997, 368537238561/274877906944, .leaf (.secant 840307952475 739381854 1702189485 10180561190)⟩))
      (.cut 3 (-5/32)
        (.row ⟨123862991199, 126950446638, (.direct 4794989340 6931290565), 43500686443, 91625974997, 355385979529/274877906944, .leaf (.secant 839098591179 651286364 1826441846 14500097491)⟩)
        (.cut 0 (99/544)
          (.row ⟨123862991199, 126950446638, (.direct 3336208443 5098567357), 43500686443, 91625974997, 92350941291/68719476736, .leaf (.secant 818638020075 162610877 2931370006 10180561190)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3195280529 5108590911), 43500686443, 91625974997, 374360748269/274877906944, .leaf (.secant 807881589732 831534857 4390594002 10180561190)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegChartPart9_ok : CutTop4H2NegChartPart9Tree.geometryOK CutTop4H2NegPowerCache CutTop4H2NegChartPart9Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
