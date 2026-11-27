/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRestPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestPart8Box : Box := ((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid2H0NegRestPart8Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.cut 1 (1/10)
              (.original (.row ⟨86531900008, 91020629598, (.direct 43500437793 44562029915), (.variance 488671898726)⟩))
              (.original (.row ⟨91020629597, 95281442641, (.direct 43500437793 44674893146), (.variance 488671898726)⟩)))
            (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 59262012820), (.variance 445447029174)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 91625662891 92747162846), (.variance 412983663964)⟩)))
        (.cut 3 (5/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 130501749339 131459329340), (.variance 366503899985)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 174937057313), (.variance 334085249950)⟩))))
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 0 (9/136)
            (.cut 3 (5/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 43500437793 44086346988), (.variance 488671898726)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 58667813846), (.variance 445447029174)⟩)))
            (.cut 3 (5/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 43500437793 44674893146), (.variance 486787050422)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 58075547817 59262012820), (.variance 444184860237)⟩))))
          (.original (.row ⟨86531900008, 95281442641, (.direct 91625662891 92747162846), (.variance 412983663964)⟩)))
        (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 174937057313), (.variance 366503899985)⟩))))
    (.original (.row ⟨86531900008, 95281442641, (.direct 174227225485 174937057313), (.chord .universal 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRestPart8_ok : CutMid2H0NegRestPart8Tree.ok CutMid2H0NegRestPart8Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
