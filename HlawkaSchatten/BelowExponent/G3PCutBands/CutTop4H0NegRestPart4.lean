/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegRestPart4Box : Box := (((((⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H0NegRestPart4Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.covered)
      (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 92696090634), (.chord (.secant 1574151333884 278088253644 42692341484 58075547817) 91625974997 274877906944)⟩)))
    (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 174904780337), (.variance 366503899985)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegRestPart4_ok : CutTop4H0NegRestPart4Tree.ok CutTop4H0NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
