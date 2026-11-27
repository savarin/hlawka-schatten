/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegRestPart5Box : Box := (((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H4NegRestPart5Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 2 (3/4)
      (.cut 3 (3/8)
        (.covered)
        (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 97022205632), (.chord (.secant 1383462000445 182418708244 20145516394 98441691225) 91625974997 174227471798)⟩)))
      (.covered))
    (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 177623698670), (.variance 362358449034)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegRestPart5_ok : CutTop4H4NegRestPart5Tree.ok CutTop4H4NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
