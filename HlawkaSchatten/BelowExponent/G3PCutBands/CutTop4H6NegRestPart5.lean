/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegRestPart5Box : Box := (((((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H6NegRestPart5Tree : RatioRemainder :=
  .cut 2 (3/4)
    (.cut 3 (1/2)
      (.cut 3 (3/8)
        (.covered)
        (.cut 2 (5/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 99212464793), (.chord (.secant 1291563387274 140368559773 17897900525 136064923840) 91625974997 130502050762)⟩))
          (.covered)))
      (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178988954677), (.variance 360344711309)⟩)))
    (.cut 3 (1/2)
      (.covered)
      (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178988954677), (.chord (.secant 1265200832422 128883192472 2982040583 97751987017) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegRestPart5_ok : CutTop4H6NegRestPart5Tree.ok CutTop4H6NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
