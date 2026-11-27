/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegPart2Box : Box := (((((((((⟨![9/68, 17/100, 0, -8], ![27/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H2NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨117423580139, 120689819475, (.direct 10180561190 7480456141), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 15684383583), (.chord (.midpoint ⟨438284730592, 141502006772, 202194603031, 341796482422, 215133391786, 228452011362⟩) 24716235638 43500686443)⟩)
      (.cut 0 (45/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 7909016041), (.chord (.midpoint ⟨537423244484, 84034555690, 162531316074, 399073003677, 177494566205, 281914896503⟩) 24716235638 43500686443)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 7480456141), (.chord (.midpoint ⟨525582606775, 90107229986, 163640578425, 397151754358, 182124590210, 279315929311⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H2NegPart2_checked : CutTop2H2NegPart2Tree.commonOK CutTop2H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
