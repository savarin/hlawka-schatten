/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegRestPart5Box : Box := (((((((((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid4H2NegRestPart5Tree : RatioRemainder :=
  .cut 1 (7/50)
    (.cut 3 (3/32)
      (.cut 0 (45/136)
        (.cut 3 (5/64)
          (.cut 2 (1/16)
            (.original (.row ⟨103236350715, 106974752992, (.direct 4833349683 7271126214), (.variance 785160821465)⟩))
            (.original (.row ⟨103236350715, 106974752992, (.direct 4833349683 7271126214), (.chord (.secant 1870087381231 443671076196 42322470747 134835198776) 3393555298 10180665226)⟩)))
          (.original (.row ⟨103236350715, 106974752992, (.direct 6452795533 9083197573), (.variance 729883440290)⟩)))
        (.cut 3 (5/64)
          (.original (.row ⟨103236350715, 106974752992, (.direct 4833349683 7801551412), (.variance 768183986886)⟩))
          (.original (.row ⟨103236350715, 106974752992, (.direct 6452795533 9648192902), (.variance 716784079926)⟩))))
      (.cut 0 (45/136)
        (.cut 1 (27/200)
          (.original (.row ⟨103236350715, 105123556200, (.direct 10180561190 13015758094), (.variance 685961683859)⟩))
          (.original (.row ⟨105123556199, 106974752992, (.direct 10180561190 13133919999), (.variance 684196071937)⟩)))
        (.original (.row ⟨103236350715, 106974752992, (.direct 10180561190 13757335641), (.variance 675491411072)⟩))))
    (.cut 3 (3/32)
      (.cut 1 (29/200)
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.original (.row ⟨106974752991, 108791878640, (.direct 4833349683 7372175541), (.variance 779402956674)⟩))
            (.original (.row ⟨106974752991, 108791878640, (.direct 6452795533 9190996427), (.variance 725459433115)⟩)))
          (.original (.row ⟨106974752991, 108791878640, (.direct 6452795533 9780509488), (.variance 761518982843)⟩)))
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.original (.row ⟨108791878639, 110576703735, (.direct 4833349683 7474289046), (.variance 776554739955)⟩))
            (.original (.row ⟨108791878639, 110576703735, (.direct 6452795533 9299850448), (.variance 723263895576)⟩)))
          (.original (.row ⟨108791878639, 110576703735, (.direct 6452795533 9914210671), (.variance 758233339748)⟩))))
      (.cut 0 (45/136)
        (.cut 1 (29/200)
          (.original (.row ⟨106974752991, 108791878640, (.direct 10180561190 13253115738), (.variance 682436490273)⟩))
          (.original (.row ⟨108791878639, 110576703735, (.direct 10180561190 13373355972), (.variance 680682880136)⟩)))
        (.original (.row ⟨106974752991, 110576703735, (.direct 10180561190 14049779742), (.variance 671317505848)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegRestPart5_ok : CutMid4H2NegRestPart5Tree.geometryOK CutMid4H2NegPowerCache CutMid4H2NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
