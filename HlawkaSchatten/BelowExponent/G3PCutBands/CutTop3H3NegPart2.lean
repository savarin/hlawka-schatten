/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegPart2Box : Box := (((((((((⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨120689819474, 123862991200, (.direct 10180561190 6451762675), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 14244135311), (.chord (.midpoint ⟨420208348644, 153690552569, 202616266001, 341291647259, 221795035706, 223977359223⟩) 24716235638 43500686443)⟩)
      (.cut 0 (63/272)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 6883189797), (.chord (.midpoint ⟨516620731840, 94841366768, 163571076278, 397271478264, 185599189459, 277734057126⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 6451762675), (.chord (.midpoint ⟨505346987026, 100967534748, 164508037250, 395664754384, 189936711274, 275280460478⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H3NegPart2_checked : CutTop3H3NegPart2Tree.commonOK CutTop3H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
