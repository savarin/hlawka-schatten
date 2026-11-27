/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart4Box : Box := ((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)).lowerChild 1 (1/10)).upperChild 1 (19/200)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart4Tree : RatioRemainder :=
  .original (.row ⟨88806993132, 91020629598, (.direct 10180561190 6442319029), (.variance 734507972838)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart4_ok : CutMid2H3NegRestPart4Tree.ok CutMid2H3NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
