/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegChartPart27`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegChartPart27Box : Box := (((((⟨![45/136, 19/100, 0, -1], ![27/68, 1/5, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H5NegChartPart27Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨123862991199, 126950446638, (.direct 25483725706 31965827039), 174227471798, 274877906944, 222981452589/137438953472, .leaf (.secant 772407741571 5106505011 34922204517 10180561190)⟩)
      (.cut 3 (-1/16)
        (.row ⟨123862991199, 126950446638, (.direct 6427132021 11300417200), 174227471798, 274877906944, 449393227521/274877906944, .leaf (.secant 694201015171 22451666156 48467052168 3393509060)⟩)
        (.cut 3 (-1/32)
          (.row ⟨123862991199, 126950446638, (.direct 991985168 4210721544), 174227471798, 274877906944, 224409255861/137438953472, .leaf (.secant 656263828223 34176967371 55835977598 1131165907)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 36953040 1717346538), 174227471798, 274877906944, 458582491307/274877906944, .leaf (.secant 637591753773 40695841872 63582830215 0)⟩))))
    (.cut 3 (1/8)
      (.row ⟨123862991199, 126950446638, (.direct 1414515598 177743980), 174227471798, 274877906944, 228288188923/137438953472, .leaf (.midpoint ⟨619119350863, 47625351798, 95956792199, 580005499514, 143934396547, 345448164409⟩)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 11246715106 5331960776), 174227471798, 274877906944, 224480704377/137438953472, .leaf (.midpoint ⟨547257952928, 79146669043, 133367208341, 459188362893, 173612048224, 328044729802⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegChartPart27_ok : CutTop4H5NegChartPart27Tree.ok CutTop4H5NegChartPart27Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
