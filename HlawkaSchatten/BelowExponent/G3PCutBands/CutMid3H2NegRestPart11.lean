/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegRestPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegRestPart11Box : Box := ((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H2NegRestPart11Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (3/25)
      (.cut 3 (5/32)
        (.cut 0 (45/136)
          (.original (.row ⟨95281442640, 99345187400, (.direct 14500097491 17207441768), (.variance 624447563946)⟩))
          (.original (.row ⟨95281442640, 99345187400, (.direct 14500097491 17769184597), (.variance 618246864258)⟩)))
        (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 22834985134), (.variance 574553607047)⟩)))
      (.cut 3 (5/32)
        (.cut 0 (45/136)
          (.original (.row ⟨99345187399, 103236350716, (.direct 14500097491 17456950036), (.variance 622023765246)⟩))
          (.original (.row ⟨99345187399, 103236350716, (.direct 14500097491 18072306908), (.variance 615322721194)⟩)))
        (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 23155014824), (.variance 572791610773)⟩))))
    (.cut 1 (3/25)
      (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 34303580570), (.variance 536071707325)⟩))
      (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 34646615370), (.variance 534730842678)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegRestPart11_ok : CutMid3H2NegRestPart11Tree.geometryOK CutMid3H2NegPowerCache CutMid3H2NegRestPart11Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
