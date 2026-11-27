/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart44`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart44Box : Box := ((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart44Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.row ⟨123862991199, 126950446638, (.direct 58075547817 67355517179), (.variance 461819519235)⟩)
      (.cut 3 (7/16)
        (.row ⟨123862991199, 126950446638, (.direct 74148400816 83231597623), (.variance 399840203943)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.variance 377760455415)⟩)))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.row ⟨123862991199, 126950446638, (.direct 110431305439 118546014691), (.variance 359352036895)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 130501749339 137877312067), (.variance 343682143340)⟩))
      (.cut 3 (11/16)
        (.row ⟨123862991199, 126950446638, (.direct 151782739331 158265500893), (.variance 330121341985)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.variance 318227065763)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart44_checked : CutTop4H7NegPart44Tree.commonOK CutTop4H7NegPart44Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
