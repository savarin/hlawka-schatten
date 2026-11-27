/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegRestPart0Box : Box := (((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid4H2NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3310278903968), (.variance 143266922294)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 762416712322), (.variance 210437923150)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5029492291575), (.variance 128403642971)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3310278903968), (.variance 143266922294)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1872282600059), (.variance 166323427138)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 762416712322), (.variance 210437923150)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5029492291575), (.variance 128403642971)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3310278903968), (.variance 143266922294)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1872282600059), (.variance 166323427138)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 762416712322), (.variance 210437923150)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 23125319349), (.variance 525596577284)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 299936584436), (.variance 268669413318)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 133217091856), (.variance 332288715552)⟩))
            (.cut 0 (45/136)
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 71970297746), (.variance 390425869843)⟩))
                (.cut 2 (5/16)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 24308217553), (.variance 518775242613)⟩))
                  (.cut 3 (-23/64)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 54287234842 45818661791), (.variance 439432430014)⟩))
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 24308217553), (.chord (.midpoint ⟨417818215486, 155344496618, 196890314360, 348304468925, 222672983046, 203710007941⟩) 43500686443 91625974997)⟩)))))
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 69887763794), (.variance 393439410338)⟩))
                (.cut 2 (5/16)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 23125319349), (.variance 525596577284)⟩))
                  (.cut 3 (-23/64)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 54287234842 44189137826), (.variance 443619202651)⟩))
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 23125319349), (.chord (.midpoint ⟨391309268976, 174373588631, 200870325584, 343393741579, 232374972986, 194376348873⟩) 43500686443 91625974997)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 299936584436), (.variance 268669413318)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 133217091856), (.variance 332288715552)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 69887763794), (.variance 393439410338)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegRestPart0_ok : CutMid4H2NegRestPart0Tree.ok CutMid4H2NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
