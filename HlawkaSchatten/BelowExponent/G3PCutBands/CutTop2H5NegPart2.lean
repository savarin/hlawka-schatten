/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart2Box : Box := (((((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 12303721675), (.variance 620033952681)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 5100505224), (.chord (.midpoint ⟨416436964899, 156304880629, 190631752043, 356379623503, 223180070520, 159635602627⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 12303721675), (.chord (.midpoint ⟨375907692005, 186026564312, 207081778880, 336053406686, 237989700006, 210891959844⟩) 24716235638 43500686443)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 5100505224), (.chord (.midpoint ⟨474116932836, 118953749907, 166419907695, 392434269693, 201783438259, 260568520909⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart2_checked : CutTop2H5NegPart2Tree.commonOK CutTop2H5NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
