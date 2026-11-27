/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegRestPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegRestPart8Box : Box := (((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H7NegRestPart8Tree : RatioRemainder :=
  .cut 2 (3/4)
    (.cut 3 (1/2)
      (.cut 3 (3/8)
        (.covered)
        (.cut 2 (5/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.chord (.secant 1246493552310 120902915877 9444084759 138406980499) 91625974997 130502050762)⟩))
          (.covered)))
      (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.variance 359352036895)⟩)))
    (.cut 3 (1/2)
      (.covered)
      (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.chord (.secant 1216776418985 108530744392 63899376 98787214060) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegRestPart8_ok : CutTop4H7NegRestPart8Tree.ok CutTop4H7NegRestPart8Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
