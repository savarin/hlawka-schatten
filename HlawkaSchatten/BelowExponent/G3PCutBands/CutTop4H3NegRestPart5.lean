/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegRestPart5Box : Box := (((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H3NegRestPart5Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.covered)
      (.cut 2 (3/4)
        (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 95933856336), (.chord (.secant 1430280287265 204933344518 31058824065 96720790547) 91625974997 174227471798)⟩))
        (.covered)))
    (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 176942518418), (.variance 363379822555)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegRestPart5_ok : CutTop4H3NegRestPart5Tree.geometryOK CutTop4H3NegPowerCache CutTop4H3NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
