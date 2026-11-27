/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart49`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart49Box : Box := ((((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart49Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 5385228726), (.chord (.midpoint ⟨608884076779, 51670319961, 112153195457, 519245432581, 148330628280, 332161537037⟩) 174227471798 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 716985716), (.chord (.midpoint ⟨644433357457, 38250507795, 92641710061, 594655932424, 132748173786, 354415735704⟩) 174227471798 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 97678863), (.chord (.secant 663825190180 31676578042 58039269395 1943420165) 174227471798 274877906944)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 0 1463531430), (.chord (.secant 688198140661 24169645611 48417313740 34563518) 174227471798 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 3776874053), (.chord (.secant 712893922733 17439965273 41444119967 939020125) 174227471798 274877906944)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3393509060 6807321803), (.chord (.secant 737909569402 11557622919 35055570686 3028378036) 174227471798 274877906944)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.chord (.secant 788889038729 2782876251 29070645558 5894800717) 174227471798 274877906944)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 30541785600 36050804961), (.chord (.secant 894565355609 7768244982 18397059051 13493159417) 174227471798 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart49_checked : CutTop4H4NegPart49Tree.commonOK CutTop4H4NegPart49Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
