/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart49`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart49Box : Box := ((((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 0 (135/272)).upperChild 3 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart49Tree : CertTree :=
  .cut 3 (5/8)
    (.row ⟨123862991199, 126950446638, (.direct 130501749339 137877312067), (.variance 358859182165)⟩)
    (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.variance 329844297459)⟩)

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart49_checked : CutTop4H7NegPart49Tree.commonOK CutTop4H7NegPart49Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
