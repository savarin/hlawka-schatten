/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart50`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart50Box : Box := ((((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart50Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.row ⟨123862991199, 126950446638, (.direct 43500437793 49207765699), (.variance 472699647540)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 58075547817 63816266796), (.variance 434611253018)⟩))
      (.cut 3 (7/16)
        (.row ⟨123862991199, 126950446638, (.direct 74148400816 79780189194), (.variance 405296493694)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 91625662891 97022205632), (.variance 381786229092)⟩)))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.row ⟨123862991199, 126950446638, (.direct 110431305439 115478253977), (.variance 362358449034)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 130501749339 135094064671), (.variance 345934880911)⟩))
      (.cut 3 (11/16)
        (.row ⟨123862991199, 126950446638, (.direct 151782739331 155822850315), (.variance 331800440998)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 174227225485 177623698670), (.variance 319459224834)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart50_checked : CutTop4H4NegPart50Tree.commonOK CutTop4H4NegPart50Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
