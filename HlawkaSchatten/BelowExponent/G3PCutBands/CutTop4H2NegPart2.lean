/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart2Box : Box := (((((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨123862991199, 126950446638, (.direct 10180561190 7168719696), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 15250780141), (.chord (.midpoint ⟨443061506049, 138374007533, 200346902647, 344030034848, 213365816605, 230122246536⟩) 24716235638 43500686443)⟩)
      (.cut 0 (45/272)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 7643431541), (.chord (.midpoint ⟨541486665599, 81997945470, 160827344188, 402068360469, 175894646434, 283282882015⟩) 24716235638 43500686443)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 7168719696), (.chord (.midpoint ⟨530420241170, 87601232912, 161604231817, 400695998670, 180238542755, 281036389476⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart2_checked : CutTop4H2NegPart2Tree.commonOK CutTop4H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
