/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegRestPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegRestPart7Box : Box := ((((((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H0NegRestPart7Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.cut 1 (7/50)
          (.cut 0 (9/136)
            (.cut 3 (9/32)
              (.original (.row ⟨103236350715, 106974752992, (.direct 36810312175 37555970632), (.variance 488671898726)⟩))
              (.original (.row ⟨103236350715, 106974752992, (.direct 43500437793 44258642588), (.variance 465357958560)⟩)))
            (.original (.row ⟨103236350715, 106974752992, (.direct 43500437793 45021420028), (.variance 485899748400)⟩)))
          (.cut 3 (9/32)
            (.cut 0 (9/136)
              (.original (.row ⟨106974752991, 110576703735, (.direct 36810312175 37613761883), (.variance 488671898726)⟩))
              (.original (.row ⟨106974752991, 110576703735, (.direct 36810312175 38423363069), (.variance 485672847793)⟩)))
            (.cut 0 (9/136)
              (.original (.row ⟨106974752991, 110576703735, (.direct 43500437793 44317372822), (.variance 465357958560)⟩))
              (.original (.row ⟨106974752991, 110576703735, (.direct 43500437793 45139651910), (.variance 462921328805)⟩)))))
        (.cut 0 (9/136)
          (.cut 1 (7/50)
            (.original (.row ⟨103236350715, 106974752992, (.direct 58075547817 58841836690), (.variance 445447029174)⟩))
            (.cut 3 (11/32)
              (.original (.row ⟨106974752991, 110576703735, (.direct 50594077426 51418230692), (.variance 445447029174)⟩))
              (.original (.row ⟨106974752991, 110576703735, (.direct 58075547817 58901141935), (.variance 428170307078)⟩))))
          (.cut 1 (7/50)
            (.original (.row ⟨103236350715, 106974752992, (.direct 58075547817 59611543818), (.variance 443589157485)⟩))
            (.original (.row ⟨106974752991, 110576703735, (.direct 58075547817 59730746378), (.variance 443436667233)⟩)))))
      (.cut 3 (7/16)
        (.cut 0 (9/136)
          (.cut 1 (7/50)
            (.original (.row ⟨103236350715, 106974752992, (.direct 74148400816 74902747765), (.variance 412983663964)⟩))
            (.original (.row ⟨106974752991, 110576703735, (.direct 74148400816 74961092288), (.variance 412983663964)⟩)))
          (.cut 1 (7/50)
            (.original (.row ⟨103236350715, 106974752992, (.direct 74148400816 75659605561), (.variance 411676510697)⟩))
            (.original (.row ⟨106974752991, 110576703735, (.direct 74148400816 75776745007), (.variance 411569022512)⟩))))
        (.cut 0 (9/136)
          (.original (.row ⟨103236350715, 110576703735, (.direct 91625662891 92406418069), (.variance 387389137214)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 91625662891 93189301467), (.variance 386442089120)⟩)))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.original (.row ⟨103236350715, 110576703735, (.direct 110431305439 111896081870), (.variance 366503899985)⟩))
        (.original (.row ⟨103236350715, 110576703735, (.direct 130501749339 131836361741), (.variance 349018446009)⟩)))
      (.cut 3 (11/16)
        (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 152958163503), (.variance 334085249950)⟩))
        (.original (.row ⟨103236350715, 110576703735, (.direct 174227225485 175216301233), (.variance 321127709228)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegRestPart7_ok : CutMid4H0NegRestPart7Tree.geometryOK CutMid4H0NegPowerCache CutMid4H0NegRestPart7Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
