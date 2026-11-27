/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegPart2Box : Box := (((((((((⟨![9/34, 3/20, 0, -8], ![45/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H4NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 14073497262), (.variance 598593363122)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 6331229389), (.chord (.midpoint ⟨422645252300, 152014529778, 194953489853, 350756089878, 220899266261, 154387509233⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 14073497262), (.chord (.midpoint ⟨388843713735, 176208868375, 208415669987, 334525972762, 233274648839, 213437929007⟩) 24716235638 43500686443)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 6331229389), (.chord (.midpoint ⟨489329140060, 110003859638, 167496732578, 390642543620, 196041518315, 263202217979⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H4NegPart2_checked : CutTop0H4NegPart2Tree.commonOK CutTop0H4NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
