/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart2Box : Box := (((((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨123862991199, 126950446638, (.direct 10180561190 6253483483), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 13963202999), (.chord (.midpoint ⟨423359104159, 151525524982, 201380828683, 342775878610, 220636738732, 225255445429⟩) 24716235638 43500686443)⟩)
      (.cut 0 (63/272)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 6705336986), (.chord (.midpoint ⟨519438381711, 93340046230, 162378478569, 399339477130, 184509393711, 278777082844⟩) 24716235638 43500686443)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 6253483483), (.chord (.midpoint ⟨508541551792, 99212151316, 163150114802, 397998486332, 188711224881, 276504709439⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart2_checked : CutTop4H3NegPart2Tree.commonOK CutTop4H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
