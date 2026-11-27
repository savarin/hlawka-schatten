/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestPart9Box : Box := (((((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid4H1NegRestPart9Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.covered)
      (.original (.row ⟨103236350715, 110576703735, (.direct 91625662891 94762367741), (.chord (.secant 1477187991336 228158014520 9049120965 59493420343) 91625974997 274877906944)⟩)))
    (.original (.row ⟨103236350715, 110576703735, (.direct 174227225485 176207194545), (.variance 365113352438)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRestPart9_ok : CutMid4H1NegRestPart9Tree.ok CutMid4H1NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
