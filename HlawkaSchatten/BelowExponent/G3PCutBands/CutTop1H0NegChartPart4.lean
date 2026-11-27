/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegChartPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegChartPart4Box : Box := ((((⟨![0, 4/25, 0, -1], ![9/136, 17/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop1H0NegChartPart4Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 30541785600 31439566031), 91625974997, 274877906944, 374416013081/274877906944, .leaf (.secant 993888389401 30541785600 3082652371 10180561190)⟩)
      (.cut 3 (-1/16)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 10883729410), 91625974997, 274877906944, 398108116639/274877906944, .leaf (.secant 907805998772 10180561190 38057447 3393509060)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 3902749698), 91625974997, 274877906944, 121843145985/68719476736, .leaf (.secant 865852635331 3393509060 3715346965 0)⟩)))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨114055813619, 117423580140, (.direct 0 85963629), 91625974997, 274877906944, 498865027569/274877906944, .leaf (.secant 824636475650 0 6858526993 1131165907)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 377054043 167981157), 91625974997, 274877906944, 7728790089/4294967296, .leaf (.midpoint ⟨804307792578, 1131165907, 36197925553, 1158333617689, 36197309053, 396585378034⟩)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 1131165907 789699943), 91625974997, 274877906944, 254128076013/137438953472, .leaf (.midpoint ⟨784166997248, 3393509060, 54296884765, 868750156237, 54296144964, 388782703074⟩)⟩))
      (.cut 3 (3/16)
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 2848881548), 91625974997, 274877906944, 499104287/268435456, .leaf (.midpoint ⟨744454106434, 10180561190, 81445321801, 651562574406, 81444489524, 380867298586⟩)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 5734880906), 91625974997, 274877906944, 257522182057/137438953472, .leaf (.midpoint ⟨705508172521, 19358451269, 103245922769, 550644921433, 103245073436, 372833410511⟩)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H0NegChartPart4_ok : CutTop1H0NegChartPart4Tree.ok CutTop1H0NegChartPart4Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
