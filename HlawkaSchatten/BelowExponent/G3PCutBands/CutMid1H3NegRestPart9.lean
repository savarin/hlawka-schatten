/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart9Box : Box := (((((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (2/25)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart9Tree : RatioRemainder :=
  .cut 1 (17/200)
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨81775466252, 84190079492, (.direct 2150924658 3741727392), (.variance 975460107497)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨81775466252, 84190079492, (.direct 2150924658 3741727392), (.chord (.secant 1300899714158 144500975909 1743247626 92874576331) 3393555298 6452870597)⟩))
            (.covered)))
        (.cut 2 (1/16)
          (.original (.row ⟨81775466252, 84190079492, (.direct 3393509060 5196309429), (.variance 867922998893)⟩))
          (.original (.row ⟨81775466252, 84190079492, (.direct 3393509060 5196309429), (.chord (.secant 1495261158046 237274413746 1536679969 91959581205) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨81775466252, 84190079492, (.direct 2150924658 3994563597), (.variance 953460419397)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨81775466252, 84190079492, (.direct 2150924658 3994563597), (.chord (.secant 1284404750577 137222725814 33154784 101328035099) 3393555298 6452870597)⟩))
            (.covered)))
        (.original (.row ⟨81775466252, 84190079492, (.direct 3393509060 5476367862), (.variance 853244528250)⟩))))
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨84190079491, 86531900009, (.direct 2150924658 3849993624), (.variance 966639263189)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨84190079491, 86531900009, (.direct 2150924658 3849993624), (.chord (.secant 1315865851915 151193808385 2551914755 96152931714) 3393555298 6452870597)⟩))
            (.covered)))
        (.cut 2 (1/16)
          (.original (.row ⟨84190079491, 86531900009, (.direct 3393509060 5316395913), (.variance 862072203784)⟩))
          (.original (.row ⟨84190079491, 86531900009, (.direct 3393509060 5316395913), (.chord (.secant 1510755006418 245161262447 2098313452 94365896990) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨84190079491, 86531900009, (.direct 2150924658 4121383123), (.variance 943954679473)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨84190079491, 86531900009, (.direct 2150924658 4121383123), (.chord (.secant 1301434005122 144738465201 406695835 105280382507) 3393555298 6452870597)⟩))
            (.covered)))
        (.original (.row ⟨84190079491, 86531900009, (.direct 3393509060 5616356607), (.variance 846813049759)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart9_ok : CutMid1H3NegRestPart9Tree.geometryOK CutMid1H3NegPowerCache CutMid1H3NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
