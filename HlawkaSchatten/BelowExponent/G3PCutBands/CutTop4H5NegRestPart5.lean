/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegRestPart5Box : Box := (((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H5NegRestPart5Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 2 (3/4)
      (.cut 3 (3/8)
        (.covered)
        (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.chord (.secant 1337221312045 160886150531 11083747410 100173767391) 91625974997 174227471798)⟩)))
      (.covered))
    (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 361346797580)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegRestPart5_ok : CutTop4H5NegRestPart5Tree.ok CutTop4H5NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
