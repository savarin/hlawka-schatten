/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart3Box : Box := ((((((((((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 2 (5/16)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart3Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/32)
      (.row ⟨120689819474, 123862991200, (.direct 6452795533 2245328589), (.chord (.midpoint ⟨494769485905, 106890587303, 157417558772, 408228313235, 193975239112, 258021565719⟩) 10180665226 24716235638)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 3393509060 480814023), (.chord (.midpoint ⟨570885177166, 67974669360, 121798464681, 489723303801, 164130589057, 296665406093⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/32)
      (.cut 0 (99/272)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 2532446420), (.chord (.midpoint ⟨524253707706, 90801686843, 144147497660, 434549393781, 182641378596, 310691226775⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 2245328589), (.chord (.midpoint ⟨512727859921, 96935139624, 145259708504, 432186060945, 187101016757, 308287958397⟩) 24716235638 43500686443)⟩))
      (.cut 0 (99/272)
        (.cut 1 (37/200)
          (.row ⟨120689819474, 122287555846, (.direct 3393509060 699844068), (.chord (.midpoint ⟨576260048444, 65544615542, 119083001156, 497620585833, 161940123618, 330610487859⟩) 24716235638 43500686443)⟩)
          (.cut 3 (-5/64)
            (.row ⟨122287555845, 123862991200, (.direct 4833349683 1474178706), (.chord (.midpoint ⟨551090364433, 77279971946, 131527995797, 463734959167, 172089421461, 331316396103⟩) 24716235638 43500686443)⟩)
            (.row ⟨122287555845, 123862991200, (.direct 3393509060 644124787), (.chord (.midpoint ⟨578418283431, 64580388223, 117982873071, 500908313815, 161056768806, 340938216160⟩) 24716235638 43500686443)⟩)))
        (.cut 1 (37/200)
          (.row ⟨120689819474, 122287555846, (.direct 3393509060 535639396), (.chord (.midpoint ⟨563930069255, 71180227224, 120554470153, 493303418043, 166945800380, 328245244262⟩) 24716235638 43500686443)⟩)
          (.row ⟨122287555845, 123862991200, (.direct 3393509060 480814023), (.chord (.midpoint ⟨566265958343, 70095934050, 119364473907, 496787733588, 166002666132, 329025642066⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart3_checked : CutTop3H5NegPart3Tree.commonOK CutTop3H5NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
