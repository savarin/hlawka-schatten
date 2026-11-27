/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestPart6Box : Box := (((((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid3H3NegRestPart6Tree : RatioRemainder :=
  .cut 1 (3/25)
    (.cut 3 (3/32)
      (.cut 0 (63/136)
        (.cut 1 (23/200)
          (.original (.row ⟨95281442640, 97336292160, (.direct 6452795533 9462475959), (.variance 767804829962)⟩))
          (.original (.row ⟨97336292159, 99345187400, (.direct 6452795533 9611754305), (.variance 763883198327)⟩)))
        (.original (.row ⟨95281442640, 99345187400, (.direct 6452795533 10100002756), (.variance 754534583933)⟩)))
      (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 14253640534), (.variance 675254927208)⟩)))
    (.cut 3 (3/32)
      (.cut 0 (63/136)
        (.cut 1 (1/8)
          (.original (.row ⟨99345187399, 101311009181, (.direct 6452795533 9762696302), (.variance 760008703889)⟩))
          (.original (.row ⟨101311009180, 103236350716, (.direct 6452795533 9915318700), (.variance 756180265424)⟩)))
        (.original (.row ⟨99345187399, 103236350716, (.direct 6452795533 10453554146), (.variance 745981477652)⟩)))
      (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 14640730591), (.variance 670366727319)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRestPart6_ok : CutMid3H3NegRestPart6Tree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
