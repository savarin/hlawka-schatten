/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart18`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart18Box : Box := ((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart18Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.original (.row ⟨86531900008, 95281442641, (.direct 43500437793 47057735572), (.variance 481277708202)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 61660821574), (.variance 440470233563)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 91625662891 95004596872), (.variance 409471997561)⟩)))
        (.cut 3 (5/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 130501749339 133381620611), (.variance 364623165179)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 176359418818), (.variance 333053018981)⟩))))
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 0 (45/136)
            (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 61057828913), (.variance 481277708202)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 61660821574), (.variance 479487912960)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 91625662891 95004596872), (.variance 409471997561)⟩)))
        (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 176359418818), (.variance 364623165179)⟩))))
    (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 176359418818), (.variance 481277708202)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart18_ok : CutMid2H2NegRestPart18Tree.ok CutMid2H2NegRestPart18Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
