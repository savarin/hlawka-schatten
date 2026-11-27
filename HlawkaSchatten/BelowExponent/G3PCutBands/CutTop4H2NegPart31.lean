/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart31`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart31Box : Box := (((((((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart31Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 0 (45/272)
      (.cut 3 (3/64)
        (.cut 2 (23/64)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3558135964), (.chord (.secant 873325563390 4407947549 1741831285 10104286682) 43500686443 54287507865)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3558135964), (.chord (.secant 855452647831 2148019036 2802185811 8319807220) 54287507865 65931360876)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 4992079111), (.chord (.secant 906312843835 9897284119 449640885 13302763993) 43500686443 65931360876)⟩))
      (.cut 3 (3/64)
        (.cut 2 (23/64)
          (.cut 0 (99/544)
            (.row ⟨123862991199, 126950446638, (.direct 2150924658 3712791436), (.chord (.secant 855052964341 2104320673 2249155390 11335831725) 43500686443 54287507865)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2150924658 3869862004), (.chord (.secant 847820328466 1371814810 3187386765 11971009242) 43500686443 54287507865)⟩))
          (.cut 0 (99/544)
            (.row ⟨123862991199, 126950446638, (.direct 2150924658 3712791436), (.chord (.secant 836839336225 497957902 3492983405 9333853798) 54287507865 65931360876)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2150924658 3869862004), (.chord (.secant 829185167928 104492589 4631720107 9856855041) 54287507865 65931360876)⟩)))
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 5338406430), (.chord (.secant 891431264005 7231282699 1834686205 14482405640) 43500686443 65931360876)⟩)))
    (.cut 0 (45/272)
      (.cut 3 (3/64)
        (.cut 2 (29/64)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3558135964), (.chord (.secant 841797279423 853363899 3768525945 6997561804) 65931360876 78389578142)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3558135964), (.chord (.secant 831024930121 178896068 4628892545 5986682843) 78389578142 91625974997)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 4992079111), (.chord (.secant 866793690653 3515999606 2030904693 9572268547) 65931360876 91625974997)⟩))
      (.cut 3 (3/64)
        (.cut 0 (99/544)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3712791436), (.chord (.secant 822927577706 22190492 5611199813 6716360237) 65931360876 91625974997)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 2150924658 3869862004), (.chord (.secant 814954702004 347744407 7036784010 7092696189) 65931360876 91625974997)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 5338406430), (.chord (.secant 850473244708 1627317514 4216299346 10421103167) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart31_checked : CutTop4H2NegPart31Tree.commonOK CutTop4H2NegPart31Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
