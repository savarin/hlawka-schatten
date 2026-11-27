/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegRestPart5Box : Box := (((((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H1NegRestPart5Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.covered)
      (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 93770785246), (.chord (.secant 1525629751961 252793618386 29960977394 59144865737) 91625974997 274877906944)⟩)))
    (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 175583058274), (.variance 365452381764)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegRestPart5_ok : CutTop4H1NegRestPart5Tree.geometryOK CutTop4H1NegPowerCache CutTop4H1NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
