/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart5Box : Box := (((((((((((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 2 (5/16)).upperChild 1 (37/200)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart5Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨122287555845, 123862991200, (.direct 3393509060 211031955), (.chord (.midpoint ⟨552489648885, 76603697388, 121611330750, 490257857993, 171532075897, 258617425983⟩) 10180665226 24716235638)⟩)
    (.cut 3 (-3/32)
      (.row ⟨122287555845, 123862991200, (.direct 6452795533 1710411795), (.chord (.midpoint ⟨507924244690, 99550152370, 143285995897, 436401528647, 188948250928, 301841915506⟩) 24716235638 43500686443)⟩)
      (.cut 0 (117/272)
        (.row ⟨122287555845, 123862991200, (.direct 3393509060 335839613), (.chord (.midpoint ⟨554209132562, 75776538891, 120734820414, 492780477739, 170846143684, 326723515802⟩) 24716235638 43500686443)⟩)
        (.row ⟨122287555845, 123862991200, (.direct 3393509060 211031955), (.chord (.midpoint ⟨542248345826, 81618866991, 122094219151, 488881328411, 175594091004, 324409822495⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart5_checked : CutTop3H6NegPart5Tree.commonOK CutTop3H6NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
