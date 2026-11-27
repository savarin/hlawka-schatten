/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart3Box : Box := ((((((((((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart3Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/32)
      (.row ⟨114055813619, 117423580140, (.direct 6452795533 3191924161), (.chord (.midpoint ⟨500988304250, 103387566371, 162522843239, 399087764918, 191604364267, 254441208702⟩) 10180665226 24716235638)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 3393509060 1051430855), (.chord (.midpoint ⟨578335893882, 64617075897, 127452648248, 474207469825, 161090531103, 293798399010⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/32)
      (.cut 0 (81/272)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 3479370453), (.chord (.midpoint ⟨540532598144, 82473965142, 145114189564, 432493512466, 176270823465, 313081046031⟩) 24716235638 43500686443)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 3191924161), (.chord (.midpoint ⟨528099469146, 88799129159, 146572787846, 429435414513, 181144284327, 310391165856⟩) 24716235638 43500686443)⟩))
      (.cut 0 (81/272)
        (.cut 1 (33/200)
          (.row ⟨114055813619, 115752966124, (.direct 3393509060 1295944888), (.chord (.midpoint ⟨594157205878, 57747867695, 119665883845, 495899603501, 154545051415, 333092453415⟩) 24716235638 43500686443)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 3393509060 1239566569), (.chord (.midpoint ⟨595904051623, 57011056945, 118788961992, 498494222612, 153814344669, 333642123870⟩) 24716235638 43500686443)⟩))
        (.cut 1 (33/200)
          (.row ⟨114055813619, 115752966124, (.direct 3393509060 1110493306), (.chord (.midpoint ⟨580910229169, 63475279688, 121520444950, 490517983875, 160034053806, 330461060455⟩) 24716235638 43500686443)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 3393509060 1051430855), (.chord (.midpoint ⟨582835216374, 62627617921, 120556453663, 493297659419, 159241952455, 331082878331⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart3_checked : CutTop1H4NegPart3Tree.commonOK CutTop1H4NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
