/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart44`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart44Box : Box := ((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart44Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 6253483483), (.chord (.midpoint ⟨643062881299, 38735093547, 104425363607, 546224978863, 133366398036, 339775510290⟩) 174227471798 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 1131185174), (.chord (.midpoint ⟨679602767631, 26720145704, 83528341587, 639991800329, 116286074106, 361846607425⟩) 174227471798 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 4228606), (.chord (.midpoint ⟨698150849095, 21349838569, 71555660810, 714243660188, 107044351904, 372530335036⟩) 174227471798 274877906944)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 0 1027550858), (.chord (.secant 722976394163 14953305879 36080426793 282105521) 174227471798 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 6056415565), (.chord (.secant 773971851728 4863426089 29362767612 595183778) 174227471798 274877906944)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 826238792157 20013764 18573924961 5222588696) 174227471798 274877906944)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 934501998252 15689087280 9728864461 12632978562) 174227471798 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart44_checked : CutTop4H3NegPart44Tree.commonOK CutTop4H3NegPart44Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
