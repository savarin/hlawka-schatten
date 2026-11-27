/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegRestPart4Box : Box := (((((⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid0H3NegRestPart4Tree : RatioRemainder :=
  .covered

set_option maxRecDepth 16000 in
theorem CutMid0H3NegRestPart4_ok : CutMid0H3NegRestPart4Tree.ok CutMid0H3NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
