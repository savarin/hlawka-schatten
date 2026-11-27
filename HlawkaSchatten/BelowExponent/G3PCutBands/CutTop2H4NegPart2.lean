/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart2Box : Box := (((((((((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 13396882232), (.variance 606366563799)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 5856369868), (.chord (.midpoint ⟨433071415786, 144959811641, 190750840988, 356221747282, 217058877248, 161466438794⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 13396882232), (.chord (.midpoint ⟨396306670546, 170688400422, 205461891967, 337931102647, 230550241593, 216857156882⟩) 24716235638 43500686443)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 5856369868), (.chord (.midpoint ⟨497020406309, 105615816396, 164222706041, 396152387721, 193118217559, 266006973456⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart2_checked : CutTop2H4NegPart2Tree.commonOK CutTop2H4NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
