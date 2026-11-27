/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegChartPart1Box : Box := (((((⟨![9/34, 13/100, 0, -1], ![27/68, 3/20, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H2NegChartPart1Tree : RatioChart :=
  .cut 1 (7/50)
    (.cut 0 (45/136)
      (.cut 1 (27/200)
        (.cut 0 (81/272)
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 284767307 1314910286), 0, 10180665226, 542684112623/274877906944, .leaf (.secant 815046710230 342509872 40301077235 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 503260664 30742751), 0, 10180665226, 500711893265/274877906944, .leaf (.midpoint ⟨658473599885, 33437899883, 84214525667, 636287527261, 126320955114, 341916639196⟩)⟩))
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 209079579 1321051163), 0, 10180665226, 539636869883/274877906944, .leaf (.secant 793621535036 2218152972 47625610649 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 608811714 32341298), 0, 10180665226, 244496158973/137438953472, .leaf (.midpoint ⟨638684598729, 40300837327, 90221347552, 605931025531, 135331206829, 337337703948⟩)⟩)))
        (.cut 0 (81/272)
          (.cut 3 (0)
            (.row ⟨105123556199, 106974752992, (.direct 258885485 1321019802), 0, 10180665226, 542684112623/274877906944, .leaf (.secant 815046710230 342509872 40301077235 0)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 537213190 32333065), 0, 10180665226, 500711893265/274877906944, .leaf (.midpoint ⟨658473599885, 33437899883, 84214525667, 636287527261, 126320955114, 341916639196⟩)⟩))
          (.row ⟨105123556199, 106974752992, (.direct 183148372 1327240651), 0, 10180665226, 2, .leaf .universal⟩)))
      (.cut 1 (27/200)
        (.cut 0 (99/272)
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 142100626 1327231585), 0, 10180665226, 267919257759/137438953472, .leaf (.secant 772407741571 5106505011 55391918480 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 722147418 33977291), 0, 10180665226, 477840225663/274877906944, .leaf (.midpoint ⟨619119350863, 47625351798, 95956792199, 580005499514, 143934396547, 332714238162⟩)⟩))
          (.cut 3 (0)
            (.row ⟨103236350715, 105123556200, (.direct 84945963 1333451894), 0, 10180665226, 531440945051/274877906944, .leaf (.secant 751406834970 8794015582 63582830215 0)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 843052201 35650820), 0, 10180665226, 233541654793/137438953472, .leaf (.midpoint ⟨599779686824, 55391643362, 101458604818, 557509909302, 152187141360, 328044729802⟩)⟩)))
        (.cut 0 (99/272)
          (.row ⟨105123556199, 106974752992, (.direct 117258410 1333502889), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨105123556199, 106974752992, (.direct 62670139 1339806890), 0, 10180665226, 2, .leaf .universal⟩))))
    (.cut 1 (29/200)
      (.cut 0 (45/136)
        (.cut 0 (81/272)
          (.row ⟨106974752991, 108791878640, (.direct 233755504 1327183008), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨106974752991, 108791878640, (.direct 158335800 1333485935), 0, 10180665226, 2, .leaf .universal⟩))
        (.cut 0 (99/272)
          (.row ⟨106974752991, 108791878640, (.direct 94061682 1339832159), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨106974752991, 108791878640, (.direct 42862210 1346222082), 0, 10180665226, 2, .leaf .universal⟩)))
      (.cut 0 (45/136)
        (.cut 1 (59/400)
          (.row ⟨108791878639, 109688224065, (.direct 209420601 1468493367), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨109688224064, 110576703735, (.direct 197565907 1474738215), 0, 10180665226, 2, .leaf .universal⟩))
        (.cut 1 (59/400)
          (.row ⟨108791878639, 109688224065, (.direct 72659693 1476426759), 0, 10180665226, 2, .leaf .universal⟩)
          (.row ⟨109688224064, 110576703735, (.direct 62687030 1482773326), 0, 10180665226, 2, .leaf .universal⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegChartPart1_ok : CutMid4H2NegChartPart1Tree.geometryOK CutMid4H2NegPowerCache CutMid4H2NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
