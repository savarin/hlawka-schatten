/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart16Box : Box := ((((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart16Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨99345187399, 103236350716, (.direct 19358451269 14276039075), (.variance 596357762465)⟩)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 6474331913), (.chord (.midpoint ⟨419578453331, 154125461122, 196184648739, 349192904348, 222026469419, 125971232681⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨99345187399, 103236350716, (.direct 19358451269 14276039075), (.chord (.midpoint ⟨386645687812, 177854623403, 209283926462, 333540683924, 234076403072, 195121946050⟩) 24716235638 43500686443)⟩)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 6474331913), (.chord (.midpoint ⟨487062008459, 111314759616, 168456743303, 389061707261, 196900523492, 247796159266⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart16_checked : CutMid3H2NegPart16Tree.commonOK CutMid3H2NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
