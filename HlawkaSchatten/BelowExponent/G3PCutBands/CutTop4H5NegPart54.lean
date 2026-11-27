/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegPart54`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegPart54Box : Box := (((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H5NegPart54Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 2 (3/4)
      (.cut 3 (3/8)
        (.cut 2 (5/8)
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 64988177306), (.chord (.secant 1155418032935 84264257964 1989373481 75274436963) 91625974997 130502050762)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 64988177306), (.chord (.secant 1038523507228 43662777100 1004403373 56382954368) 130502050762 174227471798)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.chord (.secant 1337221312045 160886150531 11083747410 100173767391) 91625974997 174227471798)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.chord (.secant 1075739338397 55687536841 9670269613 35737487284) 174227471798 274877906944)⟩))
    (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 361346797580)⟩)

set_option maxRecDepth 16000 in
theorem CutTop4H5NegPart54_checked : CutTop4H5NegPart54Tree.commonOK CutTop4H5NegPart54Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
